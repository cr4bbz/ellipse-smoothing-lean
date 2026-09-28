# Paper build

The paper is assembled by `main.tex` from separate files in `sections/`,
`appendices/`, and `backmatter/`.

## Windows / PowerShell

```powershell
.\paper\render.ps1
```

## Linux or macOS

```bash
./paper/render.sh
```

The generated PDF is copied to `paper/dist/` with a version derived from the
current Git tag or commit. Set `PAPER_VERSION` to override it explicitly:

```powershell
$env:PAPER_VERSION = "v0.1.0"
.\paper\render.ps1
```

Build products are ignored by Git. The CI workflow uploads the PDF as a
versioned artifact on every push and pull request.
