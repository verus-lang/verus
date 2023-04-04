$ScriptDir = Split-Path -Parent -Path $MyInvocation.MyCommand.Definition

Push-Location -Path (Join-Path -Path $ScriptDir -ChildPath "vargo")
cargo build --release
Pop-Location

$env:PATH = "$ScriptDir\vargo\target\release;$env:PATH"
