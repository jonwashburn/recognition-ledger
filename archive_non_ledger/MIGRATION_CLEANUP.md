# Migration Cleanup Plan

## Issue
We have duplicate implementations:
- `foundation/` - Clean, zero-axiom implementation (what we want)
- `formal/` - Older implementation with Mathlib dependencies and sorries

## Duplicated Files to Remove from formal/
1. `formal/RecognitionScience/axioms.lean` - Use foundation version instead
2. `formal/MetaPrincipleProof.lean` - Has 2 sorries, foundation version is complete
3. `formal/RecognitionScience.lean` - Check if needed

## Import Updates Needed
All files importing `RecognitionScience.axioms` should import from foundation:
- `formal/Cosmology/DarkEnergy.lean`
- `formal/Helpers/InfoTheory.lean`
- `formal/RecognitionScience/AxiomProofs.lean`
- `formal/RecognitionScience/AxiomProofs 2.lean`
- `formal/ParticlePhysics/Neutrinos.lean`
- And 53 other files...

## New Import Structure
Replace:
```lean
import RecognitionScience.axioms
```

With:
```lean
import foundation.RecognitionScience
```

## Steps
1. Delete duplicate files from formal/
2. Update lakefile.lean to include foundation as dependency
3. Update all imports in formal/ files
4. Verify build works
5. Update documentation 