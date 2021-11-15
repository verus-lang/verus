/// A rustc file loader that remaps "pervasive" to a user-provided path
pub struct PervasiveFileLoader {
    pervasive_path: Option<String>,
    real_file_loader: rustc_span::source_map::RealFileLoader,
}

impl PervasiveFileLoader {
    pub fn new(pervasive_path: Option<String>) -> Self {
        Self { pervasive_path, real_file_loader: rustc_span::source_map::RealFileLoader }
    }

    pub fn set_for_compiler(
        compiler: &mut rustc_driver::RunCompiler,
        pervasive_path: Option<String>,
    ) {
        let file_loader = Self::new(pervasive_path);
        compiler.set_file_loader(Some(Box::new(file_loader)));
    }

    fn remap_pervasive_path(&self, path: &std::path::Path) -> std::path::PathBuf {
        if let Some(pervasive_path) = &self.pervasive_path {
            if path.parent().and_then(|x| x.file_name()) == Some(std::ffi::OsStr::new("pervasive"))
            {
                if let Some(file_name) = path.file_name() {
                    return std::path::Path::new(pervasive_path).join(file_name).into();
                }
            }
        }
        return path.into();
    }
}

impl rustc_span::source_map::FileLoader for PervasiveFileLoader {
    fn file_exists(&self, path: &std::path::Path) -> bool {
        let path = self.remap_pervasive_path(path);
        self.real_file_loader.file_exists(&path)
    }

    fn read_file(&self, path: &std::path::Path) -> Result<String, std::io::Error> {
        let path = self.remap_pervasive_path(path);
        self.real_file_loader.read_file(&path)
    }
}
