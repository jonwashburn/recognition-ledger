#!/bin/bash
# Recognition Science Lean Solver Runner
# =====================================
# **IMPORTANT: USES ONLY CLAUDE SONNET 4**
# **USER REQUEST: CLAUDE SONNET 4 EXCLUSIVELY**
# **MODEL: claude-sonnet-4-20250514**

echo "======================================"
echo "Recognition Science Lean Solver"
echo "**CONFIGURED FOR CLAUDE SONNET 4 ONLY**"
echo "**MODEL: claude-sonnet-4-20250514**"
echo "======================================"

# Check if we're in the right directory
if [ ! -f "lakefile.toml" ]; then
    echo "❌ Error: Not in a Lean project directory"
    echo "Please run from: Last Hope/Unifying Math and Physics/recognition-ledger"
    exit 1
fi

# Check Python 3
if ! command -v python3 &> /dev/null; then
    echo "❌ Error: Python 3 not found"
    echo "Please install Python 3.8 or higher"
    exit 1
fi

# Function to set API key
set_api_key() {
    echo ""
    echo "**IMPORTANT: This solver uses CLAUDE SONNET 4 ONLY**"
    echo "**MODEL: claude-sonnet-4-20250514**"
    echo ""
    echo "Please enter your Anthropic API key:"
    read -s api_key
    export ANTHROPIC_API_KEY="$api_key"
    echo "✅ API key set for this session"
}

# Menu
while true; do
    echo ""
    echo "========================================="
    echo "RECOGNITION SCIENCE SOLVER MENU"
    echo "**ALL OPTIONS USE CLAUDE SONNET 4 ONLY**"
    echo "**MODEL: claude-sonnet-4-20250514**"
    echo "========================================="
    echo "1) Set Anthropic API key"
    echo "2) Run Claude Sonnet 4 Solver (Biology focus) **RECOMMENDED**"
    echo "3) Run Ultimate Autonomous Solver (20 agents) **ALL USE CLAUDE SONNET 4**"
    echo "4) Run standard o3 solver (basic) **USES CLAUDE SONNET 4**"
    echo "5) Check implementation status"
    echo "6) Build Lean project"
    echo "7) Exit"
    echo ""
    echo "**REMINDER: ALL SOLVERS USE CLAUDE SONNET 4 EXCLUSIVELY**"
    echo ""
    read -p "Select option (1-7): " choice

    case $choice in
        1)
            set_api_key
            ;;
        2)
            echo ""
            echo "**RUNNING CLAUDE SONNET 4 SOLVER**"
            echo "**MODEL: claude-sonnet-4-20250514**"
            echo "**FOCUSING ON PROTEIN FOLDING**"
            echo ""
            if [ -z "$ANTHROPIC_API_KEY" ]; then
                echo "⚠️ API key not set. Please set it first (option 1)"
            else
                cd formal
                python3 claude_sonnet_4_solver.py
                cd ..
            fi
            ;;
        3)
            echo ""
            echo "**RUNNING ULTIMATE AUTONOMOUS SOLVER**"
            echo "**20 AGENTS - ALL USE CLAUDE SONNET 4**"
            echo "**MODEL: claude-sonnet-4-20250514**"
            echo ""
            if [ -z "$ANTHROPIC_API_KEY" ]; then
                echo "⚠️ API key not set. Please set it first (option 1)"
            else
                cd formal
                python3 ultimate_autonomous_solver.py
                cd ..
            fi
            ;;
        4)
            echo ""
            echo "**RUNNING STANDARD SOLVER**"
            echo "**USES CLAUDE SONNET 4 ONLY**"
            echo "**MODEL: claude-sonnet-4-20250514**"
            echo ""
            if [ -z "$ANTHROPIC_API_KEY" ]; then
                echo "⚠️ API key not set. Please set it first (option 1)"
            else
                cd formal
                python3 o3_enhanced_solver.py
                cd ..
            fi
            ;;
        5)
            echo ""
            echo "Checking implementation status..."
            if [ -f "IMPLEMENTATION_STATUS.md" ]; then
                # Show summary
                echo ""
                echo "=== CURRENT STATUS ==="
                grep -A 5 "## Summary" IMPLEMENTATION_STATUS.md
                echo ""
                echo "For full details, see IMPLEMENTATION_STATUS.md"
            else
                echo "❌ Status file not found"
            fi
            ;;
        6)
            echo ""
            echo "Building Lean project..."
            lake build
            ;;
        7)
            echo ""
            echo "**REMINDER: All solvers use CLAUDE SONNET 4 ONLY**"
            echo "**MODEL: claude-sonnet-4-20250514**"
            echo "Goodbye!"
            exit 0
            ;;
        *)
            echo "❌ Invalid option. Please select 1-7"
            ;;
    esac
done 