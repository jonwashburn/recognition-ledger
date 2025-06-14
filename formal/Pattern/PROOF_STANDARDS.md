# Proof Standards for the Pattern Module

> **Purpose**  Ensure every Lean file in `formal/Pattern/` conforms to
> accepted mathematical practice and is publishable in a peer-reviewed
> journal without additional justification.

-------------------------------------------------------------------------------
## 1 Axiomatic Discipline

1. **No New Axioms**  Every declaration in the Pattern module must be
   provable from:
   * Lean's kernel axioms (dependent type theory with UIP + Quot)
   * `Mathlib4` foundational axioms (classical choice, propext, etc.)
   * The eight Recognition Science axioms already stated in
     `Core/Axioms.lean`

2. **Prefer Derivations Over Assumptions**  Whenever possible, derive a
   concept instead of postulating it.  Extra axioms require a formal
   justification in the file header and a cross-reference to this
   document.

3. **Prohibited:** `axiom`, `constant`, or `noncomputable irreducible`
   declarations that introduce new logical principles or bypass
   definitional equality.

-------------------------------------------------------------------------------
## 2 Proof Completeness

1. **No `sorry` Allowed**  Every theorem, lemma, and definition must
   compile without the `-- sorry` placeholder.  CI should fail if any
   `sorry` is present.

2. **Partial Proofs**  If a result is work-in-progress, comment it out or
   move it to a dedicated `*.todo` file excluded from the default
   `lake` target.

-------------------------------------------------------------------------------
## 3 Library Usage

1. **Standard Library First**  Reuse results from `Mathlib4` instead of
   re-proving folklore lemmas.

2. **Qualified Imports**  Use `import Mathlib.{…}` rather than deep local
   paths when the lemma already exists upstream.

3. **Naming Conventions**  Follow the `Mathlib4` style guide: lowercase
   snake-case for lemmas, UpperCamelCase for structures.

-------------------------------------------------------------------------------
## 4 File Hygiene

1. **Module Docstrings**  Every `.lean` file begins with a Markdown
   comment explaining its purpose, main results, and dependencies.

2. **Local Docstrings**  Each definition and theorem has a `docstring`
   (triple-dash `---`).

3. **Namespace Discipline**  All Pattern code lives under
   `namespace RecognitionScience.Pattern` (or a sub-namespace).

4. **Compile Targets**  `lake build Pattern` must succeed with
   `-Dpp.unicode` and `-DautoImplicit=false` flags.

-------------------------------------------------------------------------------
## 5 Academic Citations

Where a proof mirrors a classical reference, include a short citation,
for example:
```lean
/-- Euler product for ζ(s) (`[Apostol 1976]`, Thm 2.3). -/
```
Bibliographic data go in `docs/REFERENCES.bib`.

-------------------------------------------------------------------------------
## 6 Continuous Integration (CI) Checklist

- [ ] `git grep -n "sorry" formal/Pattern | wc -l → 0`
- [ ] `lake build Pattern` passes
- [ ] No file imports a non-standard axiom
- [ ] All linting goals (`lake env lean --run Scripts/lint.lean`) pass

-------------------------------------------------------------------------------
## 7 Versioning & Review

1. **Pull Requests**  Every change to `formal/Pattern/` must go through a
   PR with at least one approving review.
2. **Semantic Versioning**  Increment minor version when proofs are
   added; increment major version only when foundations change.

-------------------------------------------------------------------------------

Following these standards guarantees that the Pattern module maintains
rigorous academic quality and can be trusted by external reviewers. 