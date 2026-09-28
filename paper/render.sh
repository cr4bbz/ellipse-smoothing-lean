#!/usr/bin/env sh
set -eu

paper_root=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
repo_root=$(CDPATH= cd -- "$paper_root/.." && pwd)
build_dir="$paper_root/build"
dist_dir="$paper_root/dist"

mkdir -p "$build_dir" "$dist_dir"

commit=$(git -C "$repo_root" rev-parse --short HEAD)
version=${PAPER_VERSION:-$(git -C "$repo_root" describe --tags --always --dirty)}
safe_version=$(printf '%s' "$version" | tr -c 'A-Za-z0-9._-' '-')
build_date=$(date +%Y-%m-%d)

sed \
  -e "s/@VERSION@/$safe_version/g" \
  -e "s/@COMMIT@/$commit/g" \
  -e "s/@DATE@/$build_date/g" \
  "$paper_root/version.template.tex" > "$build_dir/version.tex"

cd "$paper_root"
latexmk -pdf -interaction=nonstopmode -halt-on-error -outdir=build main.tex >&2

export_path="$dist_dir/ellipse-smoothing-paper-$safe_version.pdf"
cp "$build_dir/main.pdf" "$export_path"
printf '%s\n' "$export_path"
