# IDE Support for Verus

Verus currently has IDE support for VS Code, and Emacs. Here, we describe the steps for using Verus with both these editors.

For VS Code, we require verus-analyzer, our Verus-specific fork of rust-analyzer. For Emacs, we have stand-alone support for Verus.

We describe the steps to get started with [VS Code](#quickstart-vs-code) and [Emacs](#quickstart-emacs) below.

## Quickstart VS Code
The steps below walk you through compiling a Verus-specific version of rust-analyzer and using it in VS Code. It provides Verus syntax support and several IDE functionalities.

For more details and latest updates, please check out the [README for verus-analyzer](https://github.com/verus-lang/verus-analyzer)
### 1. Compile binary

1. Clone the repository: `git clone https://github.com/verus-lang/verus-analyzer.git`  
2. `cd verus-analyzer`
3. Compile the rust-analyzer binary: `cargo xtask dist`
4. Unzip the generated file (e.g., `gunzip ./dist/verus-analyzer-x86_64-apple-darwin.gz`)
5. Make it executable (e.g., `chmod +x ./dist/verus-analyzer-x86_64-apple-darwin`)



### 2. VS Code
Before starting, please install the original rust-analyzer extension in VS Code's extensions tab.

#### 2.1. Adding a separate [VS Code Workspace](https://code.visualstudio.com/docs/editor/workspaces)
Suppose you have a new project with `cargo new`. After you open this project in VS Code, use `File > Save Workspace As...` to generate `{project_name}.code-workspace` file. The file will look similar to this. 

```json
{
	"folders": [
		{
			"path": "."
		}
	],
	"settings": {}
}
```


#### 2.2. Adding settings variables
We will modify the "settings" section of the `.code-workspace` file. To be specific, we will add two entries in the "settings" section of the file. These are `rust-analyzer.server.path` and `rust-analyzer.checkOnSave`.

- `rust-analyzer.server.path` should be set to the path of the verus-analyzer binary produced in step 1 above (e.g., the full path to `./dist/rust-analyzer-x86_64-apple-darwin`)
- `rust-analyzer.checkOnSave` to disable `cargo check`.

For example, the "settings" in the `.code-workspace` file could look the following:
```json
"settings": {
        "rust-analyzer.server.path": "ABSOLUTE-PATH-TO-THE-VERUS-ANALYZER-BINARY",
        "rust-analyzer.checkOnSave": false,
}
```

When you modify and save this file, VS Code will ask you if you want to reload the rust-analyzer server. It will replace the rust-analyzer binary with this custom one.

By opening this workspace, the rust-analyzer plugin will use the custom binary. If you open your project without that workspace setting(e.g., open this project by "open folder"), it will use the original rust-analyzer binary.



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
