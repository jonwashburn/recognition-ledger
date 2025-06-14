#!/bin/bash

# Pattern Theory Solver Runner
# Attempts to prove lemmas in the Pattern module

# Set your API key here or export it before running
if [ -z "$ANTHROPIC_API_KEY" ]; then
    echo "Error: ANTHROPIC_API_KEY not set"
    echo "Please run: export ANTHROPIC_API_KEY='your-api-key'"
    exit 1
fi

echo "Starting Pattern Theory Solver..."
echo "================================"

# Run the solver and capture output
python3 pattern_solver.py 2>&1 | tee pattern_solver_output.log

echo ""
echo "Solver completed. Checking results..."
echo ""

# Count solved lemmas
echo "Files created:"
ls -la Pattern/*_SOLVED.lean 2>/dev/null || echo "No solved files found"

echo ""
echo "Sorry count comparison:"
for file in Pattern/*.lean; do
    if [[ -f "$file" && ! "$file" =~ "_SOLVED" && ! "$file" =~ "_FIXED" && ! "$file" =~ "_COMPLETED" ]]; then
        original=$(grep -c "sorry" "$file" 2>/dev/null || echo 0)
        solved_file="${file%.lean}_SOLVED.lean"
        if [[ -f "$solved_file" ]]; then
            solved=$(grep -c "sorry" "$solved_file" 2>/dev/null || echo 0)
            echo "$file: $original → $solved sorries"
        fi
    fi
done 