# IDE Support for Verus

Verus currently has IDE support for VS Code, and Emacs. Here, we describe the steps for using Verus with both these editors.

For VS Code, we require verus-analyzer, our Verus-specific fork of rust-analyzer. For Emacs, we have stand-alone support for Verus.

We describe the steps to get started with [VS Code](#quickstart-vs-code) and [Emacs](#quickstart-emacs) below.

## Quickstart VS Code
The steps below walk you through compiling verus-analyzer, our Verus-specific fork of rust-analyzer, and installing it in VS Code. After following these steps, when you save a file, the editor will run Verus for that file and display Verus results. It also provides Verus syntax support, IDE functionalities, and Verus-specific code actions.  For more details on latest features, troubleshooting tips, and limitations, do check out the [README for verus-analyzer](https://github.com/verus-lang/verus-analyzer/blob/main/README.md).

#### 1. Compile custom rust-analyzer

1. Clone the repository: `git clone https://github.com/verus-lang/verus-analyzer.git`  
2. `cd verus-analyzer`
3. Compile the verus-analyzer binary: `cargo xtask dist`
4. Unzip the generated file (e.g. `gunzip ./dist/verus-analyzer-x86_64-apple-darwin.gz`)
5. Make it executable (e.g. `chmod +x ./dist/verus-analyzer-x86_64-apple-darwin`)

#### 2. Install the VS Code Extension

1. Install the rust-analyzer extension in VS Code's extensions tab.
2. We need to change the configuration inside `settings.json`. Specifically, we need to set two variables:
- `rust-analyzer.server.path` should be set to the path of the custom verus-analyzer binary produced in step 1 above (e.g., the full path to `./dist/verus-analyzer-x86_64-apple-darwin`)
- `"rust-analyzer.checkOnSave.overrideCommand"` to the command to run Verus. 

For `rust-analyzer.checkOnSave.overrideCommand`, the first argument needs to be the absolute path to the `verus/source/tools/rust-verify.sh` script. The second argument needs to be `${file}`, which will be replaced with the filename when the user hits the save button. After these two, you could add additional Verus flags. For example, setting a low `rlimit` prevents long waits from Verus. Most importantly, one must include `-- --error-format=json` as the last argument to make Verus output readable by verus-analyzer.

For example:
```
"rust-analyzer.server.path": "/Users/verususer/rust-analyzer/dist/rust-analyzer-x86_64-apple-darwin", 

"rust-analyzer.checkOnSave.overrideCommand": [
    "/Users/verususer/Works/secure-foundations/verus/source/tools/rust-verify.sh", 
    "${file}",   
    // add additional flags of choice here, e.g. "--expand-errors",
    "--rlimit",        // low rlimit is recommended to avoid long wait
    "3",
    "--", 
    "--error-format=json",
],
```

For VS Code running in WSL, the `rust-analyzer-server.path` and
`rust-analyzer.checkOnSave.overrideCommand` settings described above have to be
set in two different files. The `rust-analyzer-server.path` setting needs to be
in `~/.vscode-server/data/Machine/settings.json`, which you can open in VS Code
by pressing F1 and running the command `Preferences: Open Remote Settings
(JSON)`. The `rust-analyzer.checkOnSave.overrideCommand` setting needs to be in
your local settings file, named something like
`/C:/Users/verususer/AppData/Roaming/Code/User/settings.json`. You can open this
file in VS Code by pressing F1 and running the command `Preferences: Open User
Settings (JSON)`.

#### 3. Connecting other editors to verus-analyzer

[Rust-analyzer's manual](https://rust-analyzer.github.io/manual.html) might be helpful. When you connect Verus' rust-analyzer with another IDE, please make a PR to this doc to share how to do so :)


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
