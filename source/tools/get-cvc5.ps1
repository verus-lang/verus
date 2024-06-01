$cvc5_version = "1.1.2"
$filename = "cvc5-Win64-static"

$download_url = "https://github.com/cvc5/cvc5/releases/download/cvc5-$cvc5_version/$filename.zip"
Invoke-WebRequest -Uri $download_url -OutFile "$filename.zip"
Expand-Archive -Path "$filename.zip" -DestinationPath "."
Copy-Item "$filename/bin/cvc5.exe" -Destination "."
Remove-Item -Recurse -Force "$filename"
Remove-Item "$filename.zip"
