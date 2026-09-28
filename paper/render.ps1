$ErrorActionPreference = "Stop"

$PaperRoot = $PSScriptRoot
$RepoRoot = (Resolve-Path (Join-Path $PaperRoot "..")).Path
$BuildDir = Join-Path $PaperRoot "build"
$DistDir = Join-Path $PaperRoot "dist"

New-Item -ItemType Directory -Force -Path $BuildDir, $DistDir | Out-Null

$Commit = (& git -C $RepoRoot rev-parse --short HEAD).Trim()
if ($env:PAPER_VERSION) {
    $Version = $env:PAPER_VERSION
} else {
    $Version = (& git -C $RepoRoot describe --tags --always --dirty).Trim()
}
$SafeVersion = $Version -replace '[^A-Za-z0-9._-]', '-'
$BuildDate = Get-Date -Format "yyyy-MM-dd"

@"
\newcommand{\PaperVersion}{$SafeVersion}
\newcommand{\PaperCommit}{$Commit}
\newcommand{\PaperBuildDate}{$BuildDate}
"@ | Set-Content -Encoding UTF8 (Join-Path $BuildDir "version.tex")

Push-Location $PaperRoot
try {
    latexmk -pdf -interaction=nonstopmode -halt-on-error -outdir=build main.tex
} finally {
    Pop-Location
}

$ExportName = "ellipse-smoothing-paper-$SafeVersion.pdf"
$ExportPath = Join-Path $DistDir $ExportName
Copy-Item -Force (Join-Path $BuildDir "main.pdf") $ExportPath

Write-Host "Exported: $ExportPath"
