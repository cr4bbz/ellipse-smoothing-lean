.PHONY: paper clean

paper:
	./render.sh

clean:
	latexmk -C -outdir=build main.tex
	rm -rf build dist
