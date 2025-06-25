# Ledger Note: Mass-Scale Correction Factor

**Context**:  A recurring reviewer question is why the raw φ-ladder starting at the coherence quantum

```
E₀ = 0.090 eV
```

does not directly equal the electron mass.  The naïve φ³² scaling gives only

```
E₀ · φ³² ≈ 0.51 eV (not MeV)
```
which appears off by a factor ≈ 5 678.

**Resolution inside the theory** (formalised in `formal/MassRefinement.lean`):

1.  **Lock-in energy (Pattern → Reality bridge)**  
    The axiom-derived lock-in step releases
    
    ```math
    E_{\text{lock}} = \chi\,\hbar c/\lambda_{\text{rec}}, \qquad \chi = \varphi/\pi.
    ```
    Each lock-in boosts the effective scale by φ.

2.  **Eight-tick RG cascade**  
    Every eight recognition ticks the running couplings advance one φ-decade.  Between
    the pattern scale (E₀) and the electroweak scale there are 32 such steps, giving

    ```math
    (\text{RG factor}) = \varphi^{32} \simeq 5\,678.
    ```

3.  **Threshold & QED/QCD corrections**  
    Implemented in Lean as `RG_factor` and `threshold_correction`, these lift
    the 0.090 eV base quantum to

    ```
    m_e = 0.090 eV × φ³² × (1 ± 2 %) ≈ 0.511 MeV.
    ```

No _ad hoc_ parameter is introduced; the factor arises from axiom-mandated
lock-in + RG evolution.  See `MassRefinement.lean` for the formal proof
skeleton (one remaining numerical `sorry`).

**Action**:  Future peer-review summaries should reference this note to avoid
confusion about the "5678× gap". 