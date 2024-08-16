use rustc_driver::{Callbacks, Compilation, RunCompiler};
use rustc_interface::interface::Compiler;
use rustc_interface::{Config, Queries};
use rustc_span::ErrorGuaranteed;

pub(crate) struct DefaultCallbacks;

impl Callbacks for DefaultCallbacks {}

pub(crate) trait ConfigCallback {
    fn config(&mut self, _config: &mut Config) {}
}

pub(crate) struct ConfigCallbackWrapper<'a, 'b, T, U: ?Sized> {
    config_callback: &'a mut T,
    wrapped: &'b mut U,
}

impl<'a, 'b, T, U: ?Sized> ConfigCallbackWrapper<'a, 'b, T, U> {
    pub(crate) fn new(config_callback: &'a mut T, wrapped: &'b mut U) -> Self {
        Self { config_callback, wrapped }
    }
}

impl<'a, 'b, T: ConfigCallback, U: Callbacks + ?Sized> Callbacks
    for ConfigCallbackWrapper<'a, 'b, T, U>
{
    fn config(&mut self, config: &mut Config) {
        self.config_callback.config(config);
        self.wrapped.config(config);
    }

    fn after_crate_root_parsing<'tcx>(
        &mut self,
        compiler: &Compiler,
        queries: &'tcx Queries<'tcx>,
    ) -> Compilation {
        self.wrapped.after_crate_root_parsing(compiler, queries)
    }

    fn after_expansion<'tcx>(
        &mut self,
        compiler: &Compiler,
        queries: &'tcx Queries<'tcx>,
    ) -> Compilation {
        self.wrapped.after_expansion(compiler, queries)
    }

    fn after_analysis<'tcx>(
        &mut self,
        compiler: &Compiler,
        queries: &'tcx Queries<'tcx>,
    ) -> Compilation {
        self.wrapped.after_analysis(compiler, queries)
    }
}

pub(crate) fn probe_config<T: Send, F: Send + FnOnce(&mut Config) -> T>(
    rustc_args: &[String],
    probe: F,
) -> Result<T, ErrorGuaranteed> {
    let mut callbacks = ProbeConfigCallbacks::new(probe);
    let status = RunCompiler::new(rustc_args, &mut callbacks).run();
    status.map(|()| callbacks.output.unwrap())
}

struct ProbeConfigCallbacks<T, F> {
    probe: Option<F>,
    output: Option<T>,
}

impl<T, F> ProbeConfigCallbacks<T, F> {
    fn new(probe: F) -> Self {
        Self { probe: Some(probe), output: None }
    }
}

impl<T: Send, F: Send + FnOnce(&mut Config) -> T> Callbacks for ProbeConfigCallbacks<T, F> {
    fn config(&mut self, config: &mut Config) {
        let probe = self.probe.take().unwrap();
        let output = probe(config);
        self.output.replace(output);
    }

    fn after_crate_root_parsing<'tcx>(
        &mut self,
        _compiler: &Compiler,
        _queries: &'tcx Queries<'tcx>,
    ) -> Compilation {
        Compilation::Stop
    }
}

pub(crate) fn probe_after_crate_root_parsing<
    T: Send,
    F: Send + for<'tcx> FnOnce(&Compiler, &'tcx Queries<'tcx>) -> T,
>(
    rustc_args: &[String],
    probe: F,
) -> Result<T, ErrorGuaranteed> {
    let mut callbacks = ProbeAfterRootCrateParsingCallbacks::new(probe);
    let status = RunCompiler::new(rustc_args, &mut callbacks).run();
    status.map(|()| callbacks.output.unwrap())
}

struct ProbeAfterRootCrateParsingCallbacks<T, F> {
    probe: Option<F>,
    output: Option<T>,
}

impl<T, F> ProbeAfterRootCrateParsingCallbacks<T, F> {
    fn new(probe: F) -> Self {
        Self { probe: Some(probe), output: None }
    }
}

impl<T: Send, F: Send + for<'tcx> FnOnce(&Compiler, &'tcx Queries<'tcx>) -> T> Callbacks
    for ProbeAfterRootCrateParsingCallbacks<T, F>
{
    fn after_crate_root_parsing<'tcx>(
        &mut self,
        compiler: &Compiler,
        queries: &'tcx Queries<'tcx>,
    ) -> Compilation {
        let probe = self.probe.take().unwrap();
        let output = probe(compiler, queries);
        self.output.replace(output);
        Compilation::Stop
    }
}
