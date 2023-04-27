use rustc_middle::ty::TyCtxt;
use rustc_span::def_id::StableCrateId;
use rustc_span::source_map::SourceMap;
use rustc_span::{BytePos, ExternalSource, Span, SpanData};
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::sync::Arc;
use vir::ast::{SpannedTyped, Typ};
use vir::def::Spanned;

pub(crate) fn to_raw_span(span: Span) -> air::ast::RawSpan {
    Arc::new(span.data())
}

// Note: this only returns Some for Spans in the local crate
pub(crate) fn from_raw_span(raw_span: &air::ast::RawSpan) -> Option<Span> {
    (**raw_span).downcast_ref::<SpanData>().map(|data| data.span())
}

// Note: this produces a span suitable for reporting immediate errors;
// It should not be used to construct VIR AST node spans,
// and cannot be serialized an deserialized.
pub(crate) fn err_air_span(span: Span) -> air::ast::Span {
    let raw_span = to_raw_span(span);
    let as_string = format!("{:?}", span);
    air::ast::Span { raw_span, id: 0, data: vec![], as_string }
}

#[derive(Debug, Clone)]
struct ExternSourceFile {
    original_start_pos: BytePos,
    original_end_pos: BytePos,
    start_pos: BytePos,
    end_pos: BytePos,
}

#[derive(Debug)]
struct CrateInfo {
    files: Vec<ExternSourceFile>,
}

#[derive(Clone, Copy, Debug)]
pub(crate) struct FileStartEndPos {
    start_pos: BytePos,
    end_pos: BytePos,
}

impl Serialize for FileStartEndPos {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        use serde::ser::SerializeSeq;
        let mut seq = serializer.serialize_seq(Some(2))?;
        seq.serialize_element(&self.start_pos.0)?;
        seq.serialize_element(&self.end_pos.0)?;
        seq.end()
    }
}

impl<'a> Deserialize<'a> for FileStartEndPos {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'a>,
    {
        use serde::de::Error;
        struct FileStartEndPosVisitor;
        impl<'de> serde::de::Visitor<'de> for FileStartEndPosVisitor {
            type Value = FileStartEndPos;
            fn expecting(&self, formatter: &mut std::fmt::Formatter) -> std::fmt::Result {
                formatter.write_str("a sequence of two u32s")
            }
            fn visit_seq<A>(self, mut seq: A) -> Result<Self::Value, A::Error>
            where
                A: serde::de::SeqAccess<'de>,
            {
                let start_pos =
                    BytePos(seq.next_element()?.ok_or_else(|| A::Error::invalid_length(0, &self))?);
                let end_pos =
                    BytePos(seq.next_element()?.ok_or_else(|| A::Error::invalid_length(1, &self))?);
                Ok(FileStartEndPos { start_pos, end_pos })
            }
        }
        deserializer.deserialize_seq(FileStartEndPosVisitor)
    }
}

pub(crate) type SpanContext = Arc<SpanContextX>;
pub(crate) struct SpanContextX {
    pub(crate) local_crate: StableCrateId,
    // Map StableCrateId.to_u64() to CrateInfo
    imported_crates: HashMap<u64, CrateInfo>,
    next_span_id: std::cell::Cell<u64>,
    pub(crate) local_files: HashMap<Vec<u8>, FileStartEndPos>,
}

impl SpanContextX {
    pub(crate) fn new(
        tcx: TyCtxt,
        local_crate: StableCrateId,
        source_map: &SourceMap,
        original_crate_files: HashMap<u64, HashMap<Vec<u8>, FileStartEndPos>>,
    ) -> SpanContext {
        let mut imported_crates = HashMap::new();
        let mut local_files = HashMap::new();

        for source_file in source_map.files().iter() {
            match *source_file.external_src.borrow() {
                ExternalSource::Unneeded => {
                    let pos = FileStartEndPos {
                        start_pos: source_file.start_pos,
                        end_pos: source_file.end_pos,
                    };
                    local_files.insert(source_file.src_hash.hash_bytes().to_vec(), pos);
                }
                ExternalSource::Foreign { .. } => {
                    let imported_crate = tcx.stable_crate_id(source_file.cnum).to_u64();
                    let start_pos = source_file.start_pos;
                    let end_pos = source_file.end_pos;
                    if let Some(original) = original_crate_files
                        .get(&imported_crate)
                        .and_then(|x| x.get(&source_file.src_hash.hash_bytes().to_vec()))
                    {
                        let extern_source_file = ExternSourceFile {
                            original_start_pos: original.start_pos,
                            original_end_pos: original.end_pos,
                            start_pos,
                            end_pos,
                        };
                        if !imported_crates.contains_key(&imported_crate) {
                            imported_crates.insert(imported_crate, CrateInfo { files: Vec::new() });
                        }
                        imported_crates
                            .get_mut(&imported_crate)
                            .unwrap()
                            .files
                            .push(extern_source_file);
                    }
                }
            }
        }

        for (_, info) in imported_crates.iter_mut() {
            info.files.sort_by_key(|f| f.original_start_pos);
        }

        let next_span_id = std::cell::Cell::new(1);
        Arc::new(SpanContextX { local_crate, imported_crates, next_span_id, local_files })
    }

    fn pos_to_extern_source_file(
        &self,
        imported_crate: u64,
        pos: BytePos,
    ) -> Option<ExternSourceFile> {
        if let Some(crate_info) = self.imported_crates.get(&imported_crate) {
            let i = crate_info.files.binary_search_by_key(&pos.0, |f| f.original_start_pos.0);
            let i = match i {
                Ok(i) => i,
                Err(i) if i == 0 => return None,
                Err(i) => i - 1,
            };
            let f = crate_info.files[i].clone();
            if pos.0 <= f.end_pos.0 {
                return Some(f);
            }
        }
        None
    }

    fn pack_span(&self, span: Span) -> Vec<u64> {
        // Encode as [StableCrateId, lo_hi]
        let span_data = span.data();
        let lo_hi = ((span_data.lo.0 as u64) << 32) | (span_data.hi.0 as u64);
        return vec![self.local_crate.to_u64(), lo_hi];
    }

    fn unpack_span(&self, packed: &Vec<u64>) -> Span {
        // Encode as [StableCrateId, lo_hi]
        let crate_id = packed[0];
        let original_lo = BytePos((packed[1] >> 32) as u32);
        let original_hi = BytePos(packed[1] as u32);
        let ExternSourceFile { original_start_pos, original_end_pos, start_pos, end_pos } = self
            .pos_to_extern_source_file(crate_id, original_lo)
            .expect("span source file not found");

        assert!(original_start_pos <= original_lo);
        assert!(original_hi <= original_end_pos);
        let lo = original_lo - original_start_pos + start_pos;
        let hi = original_hi - original_start_pos + start_pos;
        assert!(lo <= hi);
        assert!(hi <= end_pos);
        SpanData { lo, hi, ctxt: rustc_span::SyntaxContext::root(), parent: None }.span()
    }

    pub(crate) fn to_air_span(&self, span: Span) -> air::ast::Span {
        let raw_span = to_raw_span(span);
        let id = self.next_span_id.get();
        self.next_span_id.set(id + 1);
        let data = self.pack_span(span);
        let as_string = format!("{:?}", span);
        air::ast::Span { raw_span, id, data, as_string }
    }

    // TODO(main_new) this does not need to return Option
    pub(crate) fn from_air_span(&self, air_span: &air::ast::Span) -> Option<Span> {
        if let Some(span) = from_raw_span(&air_span.raw_span) {
            Some(span)
        } else {
            Some(self.unpack_span(&air_span.data))
        }
    }

    pub(crate) fn spanned_new<X>(&self, span: Span, x: X) -> Arc<Spanned<X>> {
        Spanned::new(self.to_air_span(span), x)
    }

    pub(crate) fn spanned_typed_new<X>(&self, span: Span, typ: &Typ, x: X) -> Arc<SpannedTyped<X>> {
        SpannedTyped::new(&self.to_air_span(span), typ, x)
    }
}

impl<'tcx> crate::context::ContextX<'tcx> {
    pub(crate) fn spanned_new<X>(&self, span: Span, x: X) -> Arc<Spanned<X>> {
        self.spans.spanned_new(span, x)
    }

    pub(crate) fn spanned_typed_new<X>(&self, span: Span, typ: &Typ, x: X) -> Arc<SpannedTyped<X>> {
        self.spans.spanned_typed_new(span, typ, x)
    }
}

impl<'tcx> crate::context::BodyCtxt<'tcx> {
    pub(crate) fn spanned_new<X>(&self, span: Span, x: X) -> Arc<Spanned<X>> {
        self.ctxt.spanned_new(span, x)
    }

    pub(crate) fn spanned_typed_new<X>(&self, span: Span, typ: &Typ, x: X) -> Arc<SpannedTyped<X>> {
        self.ctxt.spanned_typed_new(span, typ, x)
    }
}
