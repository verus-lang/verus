$z3_version = "4.12.5"
$filename = "z3-$z3_version-x64-win"

$download_url = "https://github.com/Z3Prover/z3/releases/download/z3-$z3_version/$filename.zip"
Invoke-WebRequest -Uri $download_url -OutFile "$filename.zip"
Expand-Archive -Path "$filename.zip" -DestinationPath "."
Copy-Item "$filename/bin/z3.exe" -Destination "."
Remove-Item -Recurse -Force "$filename"
Remove-Item "$filename.zip"
