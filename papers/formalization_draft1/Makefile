.PHONY: all clean distclean check

all: paper.pdf

paper.pdf: paper.tex
	latexmk -pdf paper.tex

check:
	@grep -n "TODO" paper.tex claims_to_files.md venue_notes.md || true

clean:
	latexmk -c paper.tex

# Remove the generated PDF and build directory as well.
distclean:
	latexmk -C paper.tex
	rm -rf build
