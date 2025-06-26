# Implementation Review: Path to χ²/N ≈ 1.0

## Step-by-Step Analysis

### ✅ IMMEDIATELY IMPLEMENTABLE

**Step 2: Vertical Disk Physics**
- Add ζ(r) = 1 + 0.5(h_z/R_d)×sech²(z/2h_z) correction
- Use typical h_z/R_d ≈ 0.1-0.2 for thin disks
- Modifies: g_eff → g_eff × ζ(r)

**Step 3: Galaxy-Specific Radial Profiles**  
- Replace global n(r) with per-galaxy cubic splines
- Control points at r = [0.5, 2, 10, 30] kpc
- Shared hyperparameters for smoothness

**Step 6: Full Error Model**
- Include asymmetric errors, beam smearing
- Proper likelihood: -ln L = Σ[(v_obs-v_model)²/σ²_tot]
- σ²_tot = σ²_obs + σ²_beam + σ²_asym

**Step 8: Better Optimizer**
- Switch from differential_evolution to CMA-ES
- Parallelize objective function evaluation

**Step 9: Cross-Validation**
- 5-fold CV on 175 galaxies
- L2 penalty: λ_reg × Σ(n_i - n_prior)²

### ⚠️ PARTIALLY IMPLEMENTABLE

**Step 1: Clean Data Pipeline**
- Can improve H2 estimation: M_H2/M_HI = 0.4×(Σ_star/Σ_crit)^0.5
- Add Monte Carlo error propagation
- Cannot access external SPARC v2 without downloads

**Step 5: Time-Domain Variation**
- Model: n_eff = n × (1 + σ_t×sin(2πt/T_orb))
- Average over orbital phase → <n_eff>

### ❌ BLOCKED (Need External Data)

**Step 4: Environmental Complexity**
- Requires group/cluster membership catalogs
- Could use placeholder: Θ = (ρ_local/ρ_cosmic)^1/3

**Step 7: Hierarchical Bayesian**
- Requires PyMC3 installation
- Major refactor of fitting code

**Steps 10-12: Infrastructure**
- Not critical for improving χ²/N immediately

## Recommended Execution Order

1. **First**: Step 2 (vertical disk) - Quick win, ~20% improvement expected
2. **Second**: Step 3 (galaxy-specific profiles) - Major improvement path
3. **Third**: Step 6 (error model) - Proper statistics
4. **Fourth**: Steps 8+9 (optimizer + regularization)
5. **Later**: Steps 1,5,7 (data cleanup, time-domain, Bayesian)

## Expected Impact
- Current: χ²/N ≈ 3-4
- After Step 2: χ²/N ≈ 2.5-3
- After Step 3: χ²/N ≈ 1.5-2
- After Step 6: χ²/N ≈ 1.2-1.5
- After Steps 8+9: χ²/N ≈ 1.0-1.2 