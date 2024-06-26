# IDE Support for Verus

Verus currently has IDE support for VS Code and Emacs.

For VS Code, we require `verus-analyzer`, our Verus-specific fork of `rust-analyzer`. To use Verus with VS Code, follow the instructions in the [README for verus-analyzer](https://github.com/verus-lang/verus-analyzer).
 
For Emacs, we have stand-alone support for Verus. The steps to get started with [Emacs](#quickstart-emacs) are below.

## Quickstart Emacs
We support for Verus programming in Emacs through [verus-mode.el](https://github.com/verus-lang/verus-mode.el), a major mode that supports syntax highlighting, verification-on-save, jump-to-definition, and more.

To use verus-mode, the setup can be as simple as configuring `.emacs` to (i) set `verus-home` to the path to Verus, and then (ii) load up `verus-mode`.

For example, if you use `use-package`, you can clone [verus-mode.el](https://github.com/verus-lang/verus-mode.el) into a location that Emacs can load from, and add the following snippet:
```
(use-package verus-mode
  :init
  (setq verus-home "PATH_TO_VERUS_DIR"))   ; Path to where you've cloned https://github.com/verus-lang/verus
```

Depending on your specific Emacs setup, your exact installation process for verus-mode.el could vary. Detailed installation steps for various Emacs setups are documented in the [Install section on verus-mode.el's README](https://github.com/verus-lang/verus-mode.el#install).

For more details on latest features, key-bindings, and troubleshooting tips, do check out the [README for verus-mode.el](https://github.com/verus-lang/verus-mode.el/blob/main/README.md).
