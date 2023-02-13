use rustc_middle::ty::TyCtxt;
use rustc_span::def_id::StableCrateId;
use rustc_span::source_map::SourceMap;
use rustc_span::{BytePos, ExternalSource, Span, SpanData};
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
}

struct CrateInfo {
    files: Vec<ExternSourceFile>,
}

pub(crate) type SpanContext = Arc<SpanContextX>;
pub(crate) struct SpanContextX {
    local_crate: StableCrateId,
    // Map StableCrateId.to_u64() to CrateInfo
    imported_crates: HashMap<u64, CrateInfo>,
    next_span_id: std::cell::Cell<u64>,
}

impl SpanContextX {
    pub(crate) fn new(
        tcx: TyCtxt,
        local_crate: StableCrateId,
        source_map: &SourceMap,
    ) -> SpanContext {
        let mut imported_crates = HashMap::new();
        for source_file in source_map.files().iter() {
            if let ExternalSource::Foreign { original_start_pos, original_end_pos, .. } =
                *source_file.external_src.borrow()
            {
                let imported_crate = tcx.stable_crate_id(source_file.cnum).to_u64();
                let start_pos = source_file.start_pos;
                let end_pos = source_file.end_pos;
                assert!(original_end_pos - original_start_pos == end_pos - start_pos);
                let extern_source_file =
                    ExternSourceFile { original_start_pos, original_end_pos, start_pos };
                if !imported_crates.contains_key(&imported_crate) {
                    imported_crates.insert(imported_crate, CrateInfo { files: Vec::new() });
                }
                imported_crates.get_mut(&imported_crate).unwrap().files.push(extern_source_file);
            }
        }
        for (_, info) in imported_crates.iter_mut() {
            info.files.sort_by_key(|f| f.original_start_pos);
        }
        let next_span_id = std::cell::Cell::new(1);
        Arc::new(SpanContextX { local_crate, imported_crates, next_span_id })
    }

    fn pos_to_extern_source_file(
        &self,
        imported_crate: u64,
        pos: BytePos,
    ) -> Option<ExternSourceFile> {
        if let Some(crate_info) = self.imported_crates.get(&imported_crate) {
            let i = crate_info.files.binary_search_by_key(&pos, |f| f.original_start_pos);
            let i = match i {
                Ok(i) => i,
                Err(i) if i == 0 => return None,
                Err(i) => i - 1,
            };
            let f = crate_info.files[i].clone();
            assert!(f.original_start_pos <= pos);
            if pos <= f.original_end_pos {
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

    fn unpack_span(&self, packed: &Vec<u64>) -> Option<Span> {
        // Encode as [StableCrateId, lo_hi]
        if packed.len() >= 2 {
            let crate_id = packed[0];
            let original_lo = BytePos((packed[1] >> 32) as u32);
            let original_hi = BytePos(packed[1] as u32);
            if let Some(f) = self.pos_to_extern_source_file(crate_id, original_lo) {
                assert!(f.original_start_pos <= original_lo);
                if original_lo <= original_hi && original_hi <= f.original_end_pos {
                    let lo = original_lo - f.original_start_pos + f.start_pos;
                    let hi = original_hi - f.original_start_pos + f.start_pos;
                    let ctxt = rustc_span::SyntaxContext::root();
                    return Some(SpanData { lo, hi, ctxt, parent: None }.span());
                }
            }
        }
        None
    }

    pub(crate) fn to_air_span(&self, span: Span) -> air::ast::Span {
        let raw_span = to_raw_span(span);
        let id = self.next_span_id.get();
        self.next_span_id.set(id + 1);
        let data = self.pack_span(span);
        let as_string = format!("{:?}", span);
        air::ast::Span { raw_span, id, data, as_string }
    }

    pub(crate) fn from_air_span(&self, air_span: &air::ast::Span) -> Option<Span> {
        if let Some(span) = from_raw_span(&air_span.raw_span) {
            Some(span)
        } else if let Some(span) = self.unpack_span(&air_span.data) {
            Some(span)
        } else {
            // We could panic here, but it's not actually fatal to be missing the span,
            // so try to carry on.
            dbg!("internal failure: failed to generate span for {:?}", &air_span.as_string);
            None
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
