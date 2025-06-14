#!/bin/bash
# Run the O3 Pattern Lemma Solver

echo "O3 Pattern Lemma Solver"
echo "======================"
echo ""

# Check for API key
if [ -z "$OPENAI_API_KEY" ]; then
    echo "Error: OPENAI_API_KEY environment variable not set!"
    echo ""
    echo "Please set it with:"
    echo "  export OPENAI_API_KEY='your-api-key'"
    echo ""
    echo "Or create a .env file from env.example"
    exit 1
fi

# Check if we're in the right directory
if [ ! -d "Lemmas" ]; then
    echo "Error: Lemmas directory not found!"
    echo "Please run this script from the Pattern directory"
    exit 1
fi

# Install requirements if needed
if ! python3 -c "import openai" 2>/dev/null; then
    echo "Installing required packages..."
    pip3 install -r requirements.txt
fi

# Run the solver
echo "Starting O3 solver..."
python3 o3_pattern_solver.py

echo ""
echo "Done! Check the .solved.lean files for results." 