use rustc_middle::ty::TyCtxt;
use rustc_span::def_id::StableCrateId;
use rustc_span::source_map::SourceMap;
use rustc_span::{BytePos, ExternalSource, FileName, RealFileName, Span, SpanData};
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::sync::{Arc, Mutex};
use vir::ast::{SpannedTyped, Typ};
use vir::def::Spanned;

use crate::externs::VerusExterns;

pub(crate) fn to_raw_span(span: Span) -> vir::messages::RawSpan {
    Arc::new(span.data())
}

// Note: this only returns Some for Spans in the local crate
// WARNING: this should only be called from rustc's thread, not from a Verus worker thread,
// because rustc may use its thread-local storage in .span().
pub(crate) fn from_raw_span(raw_span: &vir::messages::RawSpan) -> Option<Span> {
    if std::thread::current().name() != Some("rustc") {
        eprintln!(
            "warning: from_raw_span called from wrong thread; please report this as a Verus issue: {}",
            std::backtrace::Backtrace::force_capture(),
        );
    }
    let x = (&(**raw_span)) as &(dyn std::any::Any + Sync + Send); // rust subtyping limitaiton
    x.downcast_ref::<SpanData>().map(|data| data.span())
}

// Note: this produces a span suitable for reporting immediate errors;
// It should not be used to construct VIR AST node spans,
// and cannot be serialized an deserialized.
pub(crate) fn err_air_span(span: Span) -> vir::messages::Span {
    let raw_span = to_raw_span(span);
    let as_string = format!("{:?}", span);
    vir::messages::Span { raw_span, id: 0, data: vec![], as_string }
}

#[derive(Debug, Clone)]
enum ExternSourceInfo {
    Loaded { start_pos: BytePos, end_pos: BytePos },
    Delayed { filename: std::path::PathBuf, hash: Vec<u8> },
    None,
}

#[derive(Debug, Clone)]
struct ExternSourceFile {
    original_start_pos: BytePos,
    original_end_pos: BytePos,
    info: Arc<Mutex<ExternSourceInfo>>,
}

#[derive(Debug)]
struct CrateInfo {
    files: Vec<ExternSourceFile>,
}

#[derive(Clone, Debug, Deserialize, Serialize)]
pub(crate) struct FileStartEndPos {
    // In case SourceMap doesn't load the file itself,
    // as a backup we can try to ask SourceMap to load from filename
    // (this is optional; it's ok if the filename is None):
    filename: Option<std::path::PathBuf>,
    // positions taken from BytePos:
    start_pos: u32,
    end_pos: u32,
}

pub(crate) type SpanContext = Arc<SpanContextX>;
pub(crate) struct SpanContextX {
    pub(crate) local_crate: StableCrateId,
    // Map StableCrateId.to_u64() to CrateInfo
    imported_crates: HashMap<u64, CrateInfo>,
    next_span_id: std::sync::atomic::AtomicU64,
    pub(crate) local_files: HashMap<Vec<u8>, FileStartEndPos>,
}

impl SpanContextX {
    pub(crate) fn new(
        tcx: TyCtxt,
        local_crate: StableCrateId,
        source_map: &SourceMap,
        original_crate_files: HashMap<u64, HashMap<Vec<u8>, FileStartEndPos>>,
        verus_externs: Option<&VerusExterns>,
    ) -> SpanContext {
        let mut imported_crates = HashMap::new();
        let mut local_files = HashMap::new();
        let mut remaining_crate_files = original_crate_files.clone();
        let path_mappings = verus_externs.map(|x| x.to_path_mappings());

        for source_file in source_map.files().iter() {
            match *source_file.external_src.borrow() {
                ExternalSource::Unneeded => {
                    let filename = match &source_file.name {
                        FileName::Real(RealFileName::LocalPath(path)) => path.canonicalize().ok(),
                        _ => None,
                    };
                    let pos = FileStartEndPos {
                        filename,
                        start_pos: source_file.start_pos.0,
                        end_pos: source_file.start_pos.0 + source_file.normalized_source_len.0,
                    };
                    local_files.insert(source_file.src_hash.hash_bytes().to_vec(), pos);
                }
                ExternalSource::Foreign { .. } => {
                    let imported_crate = tcx.stable_crate_id(source_file.cnum).as_u64();
                    let start_pos = source_file.start_pos;
                    let end_pos =
                        BytePos(source_file.start_pos.0 + source_file.normalized_source_len.0);
                    let hash = source_file.src_hash.hash_bytes().to_vec();
                    if let Some(original) =
                        original_crate_files.get(&imported_crate).and_then(|x| x.get(&hash))
                    {
                        remaining_crate_files.get_mut(&imported_crate).unwrap().remove(&hash);
                        let info = if let FileName::Real(real_file_name) = &source_file.name {
                            // Ideally we'd change this into Remapped, but I don't know how to do that
                            if let (Some(path_mappings), RealFileName::LocalPath(local_file_name)) =
                                (&path_mappings, real_file_name)
                            {
                                let mut found_match = None;
                                for (name, epath) in path_mappings.iter() {
                                    // search for source/<name> in local_file_path.components()
                                    let mut found = 0;
                                    let mut components = local_file_name.components();
                                    while let Some(c) = components.next() {
                                        if found == 0 {
                                            if c.as_os_str().to_str().unwrap() == "source" {
                                                found += 1;
                                            }
                                        } else if found == 1 {
                                            if c.as_os_str().to_str().unwrap() == name {
                                                found += 1;
                                                break;
                                            }
                                        }
                                    }
                                    let rest = components.as_path().to_path_buf();
                                    if found == 2 {
                                        found_match = Some((name, epath, rest));
                                        break;
                                    }
                                }
                                if let Some((_, base_path, file)) = found_match {
                                    let filename = base_path.join(file);
                                    ExternSourceInfo::Delayed { filename, hash }
                                } else {
                                    ExternSourceInfo::Loaded { start_pos, end_pos }
                                }
                            } else {
                                ExternSourceInfo::Loaded { start_pos, end_pos }
                            }
                        } else {
                            ExternSourceInfo::Loaded { start_pos, end_pos }
                        };
                        let file = ExternSourceFile {
                            original_start_pos: BytePos(original.start_pos),
                            original_end_pos: BytePos(original.end_pos),
                            info: Arc::new(Mutex::new(info)),
                        };

                        imported_crates
                            .entry(imported_crate)
                            .or_insert(CrateInfo { files: Vec::new() })
                            .files
                            .push(file);
                    }
                }
            }
        }
        for (imported_crate, files) in remaining_crate_files.iter() {
            if !imported_crates.contains_key(imported_crate) {
                imported_crates.insert(*imported_crate, CrateInfo { files: Vec::new() });
            }
            for (hash, original) in files.iter() {
                let info = if let Some(filename) = original.filename.clone() {
                    ExternSourceInfo::Delayed { filename, hash: hash.clone() }
                } else {
                    ExternSourceInfo::None
                };
                let file = ExternSourceFile {
                    original_start_pos: BytePos(original.start_pos),
                    original_end_pos: BytePos(original.end_pos),
                    info: Arc::new(Mutex::new(info)),
                };
                imported_crates.get_mut(&imported_crate).unwrap().files.push(file);
            }
        }

        for (_, info) in imported_crates.iter_mut() {
            info.files.sort_by_key(|f| f.original_start_pos);
        }

        let next_span_id = std::sync::atomic::AtomicU64::new(1);
        Arc::new(SpanContextX { local_crate, imported_crates, next_span_id, local_files })
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

    fn pos_to_extern_source_file_resolve(
        &self,
        imported_crate: u64,
        pos: BytePos,
        source_map: Option<&SourceMap>,
    ) -> Option<(BytePos, BytePos, BytePos, BytePos)> {
        let ExternSourceFile { original_start_pos, original_end_pos, info } =
            self.pos_to_extern_source_file(imported_crate, pos)?;
        if let Some(source_map) = source_map {
            // If rustc didn't originally load the file into the source_map,
            // we can try to request that it load the file on demand.
            let mut info = info.lock().unwrap();
            let filename = if let ExternSourceInfo::Delayed { filename, hash } = &*info {
                Some((filename.clone(), hash.clone()))
            } else {
                None
            };
            if let Some((filename, hash)) = filename {
                *info = ExternSourceInfo::None;
                if let Ok(source_file) = source_map.load_file(&filename) {
                    if hash == source_file.src_hash.hash_bytes().to_vec() {
                        let start_pos = source_file.start_pos;
                        let end_pos =
                            BytePos(source_file.start_pos.0 + source_file.normalized_source_len.0);
                        *info = ExternSourceInfo::Loaded { start_pos, end_pos };
                    }
                }
            }
        }
        let locs = match &*info.lock().unwrap() {
            ExternSourceInfo::Loaded { start_pos, end_pos } => {
                Some((original_start_pos, original_end_pos, *start_pos, *end_pos))
            }
            _ => None,
        };
        locs
    }

    fn pack_span(&self, span: Span) -> Vec<u64> {
        // Encode as [StableCrateId, lo_hi]
        let span_data = span.data();
        let lo_hi = ((span_data.lo.0 as u64) << 32) | (span_data.hi.0 as u64);
        return vec![self.local_crate.as_u64(), lo_hi];
    }

    fn unpack_span(&self, packed: &Vec<u64>, source_map: Option<&SourceMap>) -> Option<Span> {
        // Encode as [StableCrateId, lo_hi]
        let crate_id = packed[0];
        let original_lo = BytePos((packed[1] >> 32) as u32);
        let original_hi = BytePos(packed[1] as u32);
        let locs = self.pos_to_extern_source_file_resolve(crate_id, original_lo, source_map);
        let (original_start_pos, original_end_pos, start_pos, end_pos) = if let Some(locs) = locs {
            locs
        } else {
            return None;
        };
        assert!(original_start_pos <= original_lo);
        assert!(original_hi <= original_end_pos);
        let lo = original_lo - original_start_pos + start_pos;
        let hi = original_hi - original_start_pos + start_pos;
        assert!(lo <= hi);
        assert!(hi <= end_pos);
        Some(SpanData { lo, hi, ctxt: rustc_span::SyntaxContext::root(), parent: None }.span())
    }

    pub(crate) fn get_next_span_id(&self) -> u64 {
        self.next_span_id.fetch_add(1, std::sync::atomic::Ordering::SeqCst)
    }

    pub(crate) fn to_air_span(&self, span: Span) -> vir::messages::Span {
        let raw_span = to_raw_span(span);

        let id = self.get_next_span_id();
        let data = self.pack_span(span);
        let as_string = format!("{:?}", span);
        vir::messages::Span { raw_span, id, data, as_string }
    }

    pub(crate) fn from_air_span(
        &self,
        air_span: &vir::messages::Span,
        source_map: Option<&SourceMap>,
    ) -> Option<Span> {
        if let Some(span) = from_raw_span(&air_span.raw_span) {
            Some(span)
        } else {
            self.unpack_span(&air_span.data, source_map)
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

    pub(crate) fn spanned_typed_new_vir<X>(
        &self,
        span: &vir::messages::Span,
        typ: &Typ,
        x: X,
    ) -> Arc<SpannedTyped<X>> {
        let mut span = span.clone();
        span.id = self.spans.get_next_span_id();
        SpannedTyped::new(&span, typ, x)
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
