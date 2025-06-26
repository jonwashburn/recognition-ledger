# Recognition Ledger Repository Structure

## Overview
This repository contains the core Lean ledger project with a clean, organized structure focused on formal verification and the Recognition Science framework.

## Core Directories

### Lean Project Foundations
- **`foundation/`** - Zero-axiom Lean foundation (PROTECTED by CODEOWNERS)
- **`formal/`** - Formal Lean proofs and verification
- **`ledger/`** - LedgerState.lean and predictions
- **`ethics/`** - Lean implementations of ethical framework
- **`physics/`** - Lean physics implementations
- **`helpers/`** - Lean helper files
- **`Numerics/`** - Numerical bounds in Lean

### Active Lean Projects
- **`gravity/`** - Gravity theory with its own lakefile.toml
- **`working/`** - Work in progress (NavierStokes)

### Supporting Infrastructure
- **`docs/`** - Documentation for the ledger project
- **`web/`** - Contains widget.js for web integration
- **`scripts/`** - Core utility scripts:
  - `generate_constants.py` - Generates constants for Lean
  - `fix_imports.py` - Fixes Lean imports
  - `verify_rs_*.py` - Verification scripts for the framework

### Configuration Files
- `lakefile.lean` - Main Lean project file
- `lean-toolchain` - Lean version specification
- `CODEOWNERS` - GitHub code ownership rules
- `README.md` - Project documentation

### Version Control
- `.git/` - Git repository
- `.gitignore` - Git ignore rules
- `.github/` - GitHub workflows

### Archived Content
- **`archive_non_ledger/`** - Contains all non-core content that was moved during cleanup (see ARCHIVE_CONTENTS_SUMMARY.md within)

## Protected Files
The `foundation/` directory is protected by CODEOWNERS and requires explicit approval for any changes, maintaining the zero-axiom integrity of the framework. 