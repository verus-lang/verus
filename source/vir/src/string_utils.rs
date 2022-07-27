use crate::ast::*;
use std::sync::Arc;
#[macro_export]
macro_rules! segments {
    ($($name:expr),*) => {
        {
            let mut v = Vec::new();
            $(
                v.push(Arc::new($name.to_string()));
            )*
            Arc::new(v)
        }
    }
}

pub use segments;

pub fn get_strslice_path() -> Path {
    let path = PathX { krate: None, segments: segments!("pervasive", "string", "StrSlice") };
    Arc::new(path)
}

// get the type of strslice
pub fn get_strslice_vir_ty() -> Typ {
    let path = get_strslice_path();
    Arc::new(TypX::Datatype(path, Arc::new(vec![])))
}

// gets the return type of is_ascii
pub fn get_is_ascii_vir_ty() -> Typ {
    Arc::new(TypX::Bool)
}

// gets the function for is_ascii
pub fn get_is_ascii_vir_fun() -> Fun {
    let path =
        PathX { krate: None, segments: segments!("pervasive", "string", "StrSlice", "is_ascii") };
    let funx = FunX { path: Arc::new(path), trait_path: None };
    Arc::new(funx)
}

// gets the return value of view
pub fn get_view_vir_ty() -> Typ {
    let pathx = PathX { krate: None, segments: segments!("pervasive", "seq", "Seq") };
    let path = Arc::new(pathx);
    let u8tyx = TypX::Int(IntRange::U(8));
    let u8ty = Arc::new(u8tyx);
    Arc::new(TypX::Datatype(path, Arc::new(vec![u8ty])))
}

pub fn get_view_vir_fun() -> Fun {
    let pathx =
        PathX { krate: None, segments: segments!("pervasive", "string", "StrSlice", "view") };
    let path = Arc::new(pathx);
    let funx = FunX { path, trait_path: None };
    Arc::new(funx)
}

pub fn get_index_vir_ty() -> Typ {
    let u8tyx = TypX::Int(IntRange::U(8));
    Arc::new(u8tyx)
}

pub fn get_index_vir_fun() -> Fun {
    let pathx = PathX { krate: None, segments: segments!("pervasive", "seq", "Seq", "index") };
    let path = Arc::new(pathx);
    let funx = FunX { path, trait_path: None };
    Arc::new(funx)
}

pub fn get_len_vir_ty() -> Typ {
    let usizety = TypX::Int(IntRange::USize);
    Arc::new(usizety)
}


pub fn get_len_vir_fun() -> Fun {
    let pathx = PathX {krate: None, segments: segments!("pervasive", "seq", "Seq", "len") };
    let path = Arc::new(pathx);
    let funx = FunX{ path, trait_path: None };
    Arc::new(funx)
}
