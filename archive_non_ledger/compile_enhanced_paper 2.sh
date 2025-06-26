#!/bin/bash

# Compile the Enhanced LNAL Gravity Paper

echo "Compiling Enhanced LNAL Gravity Paper..."

# First compilation
pdflatex -interaction=nonstopmode LNAL_Gravity_Paper_Enhanced.tex

# Run BibTeX if needed (currently no bibliography)
# bibtex LNAL_Gravity_Paper_Enhanced

# Second compilation to resolve references
pdflatex -interaction=nonstopmode LNAL_Gravity_Paper_Enhanced.tex

# Third compilation to finalize
pdflatex -interaction=nonstopmode LNAL_Gravity_Paper_Enhanced.tex

# Clean up auxiliary files
rm -f *.aux *.log *.toc *.out

echo "Compilation complete! Output: LNAL_Gravity_Paper_Enhanced.pdf" 