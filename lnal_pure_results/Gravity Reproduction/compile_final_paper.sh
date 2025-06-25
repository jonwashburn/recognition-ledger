#!/bin/bash

# Compile the Final LNAL Gravity Paper (Narrative Version)

echo "Compiling Final LNAL Gravity Paper (Narrative Version)..."

# First compilation
pdflatex -interaction=nonstopmode LNAL_Gravity_Paper_Final.tex

# Run BibTeX if needed (currently no bibliography)
# bibtex LNAL_Gravity_Paper_Final

# Second compilation to resolve references
pdflatex -interaction=nonstopmode LNAL_Gravity_Paper_Final.tex

# Third compilation to finalize
pdflatex -interaction=nonstopmode LNAL_Gravity_Paper_Final.tex

# Clean up auxiliary files
rm -f *.aux *.log *.toc *.out

echo "Compilation complete! Output: LNAL_Gravity_Paper_Final.pdf" 