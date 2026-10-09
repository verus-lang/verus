@echo off

rem Get the script's directory
for %%i in (%0) do set SCRIPT_DIR=%%~dpi

pushd "%SCRIPT_DIR%\vargo"
cargo build --release
popd

set PATH=%SCRIPT_DIR%vargo\target\release;%PATH%

echo WARNING: Vargo is being deprecated. Use Cargo instead. Refer to `BUILD.md`.
echo See also: https://github.com/verus-lang/verus/pull/2686
