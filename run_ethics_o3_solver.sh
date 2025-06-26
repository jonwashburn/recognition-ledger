#!/bin/bash
# Run the Ethics Module O3 Solver

echo "Ethics Module O3 Proof Completion System"
echo "========================================"
echo ""

# Check for API key
if [ -z "$OPENAI_API_KEY" ]; then
    echo "Error: OPENAI_API_KEY not set"
    echo "Please run: export OPENAI_API_KEY='sk-proj-...'"
    exit 1
fi

# Create backup directory if it doesn't exist
mkdir -p backups

echo "Starting Ethics Module proof completion with o3..."
echo "Features:"
echo "  ✓ Pattern-based sorry classification"
echo "  ✓ Ethics-specific context extraction"
echo "  ✓ Floor arithmetic handling"
echo "  ✓ Philosophical sorry detection"
echo "  ✓ Iterative error correction"
echo ""

# Check current sorry count
echo "Current sorry count in ethics module:"
grep -r "sorry" ethics/*.lean | grep -v "^--" | wc -l

echo ""
echo "Running solver..."
python3 ethics_o3_solver.py

echo ""
echo "Ethics module completion finished!"
echo ""

# Check final sorry count
echo "Final sorry count in ethics module:"
grep -r "sorry" ethics/*.lean | grep -v "^--" | wc -l

# Run build to verify
echo ""
echo "Running lake build to verify..."
lake build 