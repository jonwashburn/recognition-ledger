#!/bin/bash

# Compile the Recognition Principle refined paper

echo "Compiling Recognition Principle refined paper..."

# Run pdflatex twice to resolve references
pdflatex -interaction=nonstopmode recognition_principle_refined.tex
pdflatex -interaction=nonstopmode recognition_principle_refined.tex

# Check if compilation was successful
if [ -f "recognition_principle_refined.pdf" ]; then
    echo "✓ Compilation successful!"
    echo "PDF created: recognition_principle_refined.pdf"
    
    # Clean up auxiliary files
    rm -f *.aux *.log *.out *.toc *.lof *.lot
    echo "✓ Cleaned up auxiliary files"
else
    echo "✗ Compilation failed. Check the log file for errors."
    if [ -f "recognition_principle_refined.log" ]; then
        echo "Last 50 lines of log file:"
        tail -50 recognition_principle_refined.log
    fi
fi 