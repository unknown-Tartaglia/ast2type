ts-node ast2type.ts -i output/ast
$dotDir = "output\dotfile"
if (-Not (Test-Path $dotDir)) {
    Write-Error "Directory $dotDir does not exist."
    exit 1
}

Get-ChildItem "$dotDir\*.dot" | ForEach-Object {
    $svgPath = Join-Path $dotDir ($_.BaseName + ".svg")
    Write-Host "Processing $($_.FullName) → $svgPath"
    dot -Tsvg $_.FullName -o $svgPath
}
Write-Host "All done."
