#!/bin/bash

# Compile the LNAL Gravity Paper

echo "Compiling LNAL Gravity Paper..."

# First compilation
pdflatex -interaction=nonstopmode LNAL_Gravity_Paper_Complete.tex

# Run BibTeX if needed (currently no bibliography)
# bibtex LNAL_Gravity_Paper_Complete

# Second compilation to resolve references
pdflatex -interaction=nonstopmode LNAL_Gravity_Paper_Complete.tex

# Third compilation to finalize
pdflatex -interaction=nonstopmode LNAL_Gravity_Paper_Complete.tex

# Clean up auxiliary files
rm -f *.aux *.log *.toc *.out

echo "Compilation complete! Output: LNAL_Gravity_Paper_Complete.pdf" 