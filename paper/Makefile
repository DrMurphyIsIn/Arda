# Build the whitepaper PDF.
# Prefers latexmk; falls back to two pdflatex passes (for refs + bibtex).

main.pdf: pdf

pdf:
	@if command -v latexmk >/dev/null 2>&1; then \
		latexmk -pdf main.tex; \
	else \
		pdflatex -interaction=nonstopmode main.tex && \
		bibtex main || true; \
		pdflatex -interaction=nonstopmode main.tex && \
		pdflatex -interaction=nonstopmode main.tex; \
	fi

clean:
	@if command -v latexmk >/dev/null 2>&1; then latexmk -C; else \
		rm -f main.aux main.bbl main.blg main.log main.out main.pdf main.toc; fi

.PHONY: pdf clean
