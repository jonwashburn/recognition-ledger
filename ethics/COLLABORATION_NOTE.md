# Collaboration Constraints for Ethics Module Work

## Important: Multiple Teams Working in Parallel

**Date**: Current session
**My Scope**: Ethics folder ONLY

### Key Constraints:
1. **I am authorized to work ONLY in the `/ethics/` folder**
2. **Other teams are actively working on**:
   - `/foundation/` - DO NOT MODIFY (marked as complete)
   - `/formal/` - Other team working
   - `/physics/` - Other team working  
   - `/gravity/` - Other team working
   - `/ledger/` - Other team working
   - All other folders - DO NOT TOUCH

### What This Means:
- I should NOT create new folders outside `/ethics/`
- I should NOT modify `lakefile.lean` at root level
- I should NOT create new infrastructure like `/Recognition/` folder
- Any shared utilities I need should be created within `/ethics/` subfolder
- Import paths from other modules should remain unchanged

### Current Ethics Status:
- ~~49 sorries remaining (per README)~~ **ACTUAL: 18 sorries**
- Files in ethics folder:
  - Main.lean
  - Curvature.lean
  - Virtue.lean
  - Measurement.lean
  - Applications.lean
  - Helpers.lean
  - EmpiricalData.lean
  - Tests.lean
  - ethics.lean

### Repository Reality Check:
The README claims 0 sorries in non-ethics files, but actual counts are:
- foundation: 49 sorries
- formal: 208 sorries  
- physics: 5 sorries
- gravity: 14 sorries
- ethics: 18 sorries (not 49 as claimed)
- bio: 1 sorry
- pattern: 6 sorries

### My Task:
Complete the ethics framework by resolving the 18 remaining sorries WITHOUT:
- Creating any files outside `/ethics/`
- Modifying any root-level configuration files
- Creating conflicts with other teams' work

### Cleanup Done:
- Removed `/Recognition/` folder I mistakenly created
- Removed `Justfile` I created at root
- Reverted `lakefile.lean` to original state 