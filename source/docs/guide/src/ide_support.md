# Using Verus with rust-analyzer


After following the below steps, when you save a file, rust-analyzer will run Verus for that file and display generated error messages. By default, rust-analyzer uses `cargo check` to get diagnostics, but we intercept that and make the rust-analyzer use Verus. 

### 1. Compile custom rust-analyzer

1. Clone the repository: `git clone https://github.com/channy412/rust-analyzer/tree/connect-verus`
2. `cd rust-analyzer`
3. Compile the rust-analyzer binary: `cargo xtask dist`
4. Unzip the generated file (e.g. `gunzip ./dist/rust-analyzer-x86_64-apple-darwin.gz`)
5. Make it executable (e.g. `chmod +x ./dist/rust-analyzer-x86_64-apple-darwin`)



### 2. VS Code
We need to change the configuration inside `settings.json`. Specifically, we need to set below two variables.
1. `rust-analyzer.server.path` to the above rust-analyzer binary's path.
2. `"rust-analyzer.checkOnSave.overrideCommand"` to the command to run Verus. When doing this, please include `-- --error-format=json`.

For example:
```
"rust-analyzer.server.path": "/Users/chanhee/Works/secure-foundations/rust-analyzer/dist/rust-analyzer-x86_64-apple-darwin", 

"rust-analyzer.checkOnSave.overrideCommand": [
    "/Users/chanhee/Works/secure-foundations/verus/source/tools/rust-verify.sh",
    "${file}",
    "--", 
    "--error-format=json",
],
```

Verus will be triggered when the user saves a file, and `${file}` will be replaced with that file's name.





### 3. Other IDEs

Rust-analyzer's manual might be helpful (`https://rust-analyzer.github.io/manual.html`)

When you connect Verus with another IDE, please share how to do so on this document :)

  

### Current limitations
(We are still improving this IDE support.)
Currently, it does not provide Verus syntax errors. We are currently extending rust-analyzer's grammar for Verus' syntax.