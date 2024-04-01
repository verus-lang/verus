pub use rustc_span::source_map::RealFileLoader;

pub trait FileLoaderClone {
    fn clone(&self) -> Self;
}

impl FileLoaderClone for RealFileLoader {
    fn clone(&self) -> Self {
        rustc_span::source_map::RealFileLoader
    }
}
