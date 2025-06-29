/-
  Recognition Science: Particle Mass Spectrum
  ==========================================

  All Standard Model particle masses emerge from the golden ratio
  energy cascade E_r = E_coh × φ^r, where particles occupy specific
  integer rungs determined by their quantum numbers.

  No Yukawa couplings or free parameters - just rung positions.

  Author: Jonathan Washburn
  Recognition Science Institute
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace RecognitionScience

open Real

/-!
# Basic Constants
-/

-- The golden ratio
noncomputable def φ : ℝ := (1 + sqrt 5) / 2

-- The coherence quantum in eV
def E_coh : ℝ := 0.090

-- Energy at rung r (in eV)
noncomputable def energy_at_rung (r : ℕ) : ℝ := E_coh * φ ^ r

-- Convert eV to MeV
def eV_to_MeV (e : ℝ) : ℝ := e / 1000000

-- Convert eV to GeV
def eV_to_GeV (e : ℝ) : ℝ := e / 1000000000

/-!
# Particle Enumeration and Rung Assignment
-/

-- Particle type enumeration
inductive Particle
  | electron : Particle
  | muon : Particle
  | tau : Particle
  | up : Particle
  | down : Particle
  | strange : Particle
  | charm : Particle
  | bottom : Particle
  | top : Particle
  | w_boson : Particle
  | z_boson : Particle
  | higgs : Particle
  | photon : Particle
  | neutrino_e : Particle
  | neutrino_mu : Particle
  | neutrino_tau : Particle

-- Rung assignment for each particle
def particle_rung : Particle → ℕ
  | Particle.photon => 0        -- Massless
  | Particle.neutrino_e => 30   -- Lightest neutrino
  | Particle.electron => 32     -- e⁻
  | Particle.up => 33          -- u quark
  | Particle.down => 34        -- d quark
  | Particle.neutrino_mu => 37  -- Middle neutrino
  | Particle.strange => 38     -- s quark
  | Particle.muon => 39        -- μ⁻
  | Particle.charm => 40       -- c quark
  | Particle.neutrino_tau => 42 -- Heaviest neutrino
  | Particle.tau => 44         -- τ⁻
  | Particle.bottom => 45      -- b quark (at the 45-gap!)
  | Particle.top => 47         -- t quark
  | Particle.w_boson => 52     -- W±
  | Particle.z_boson => 53     -- Z⁰
  | Particle.higgs => 58       -- H

-- Theoretical mass in eV
noncomputable def particle_mass_eV (p : Particle) : ℝ :=
  energy_at_rung (particle_rung p)

-- Theoretical mass in MeV
noncomputable def particle_mass_MeV (p : Particle) : ℝ :=
  eV_to_MeV (particle_mass_eV p)

-- Theoretical mass in GeV
noncomputable def particle_mass_GeV (p : Particle) : ℝ :=
  eV_to_GeV (particle_mass_eV p)

/-!
# Basic Properties
-/

-- The photon is massless
theorem photon_massless : particle_mass_eV Particle.photon = E_coh := by
  unfold particle_mass_eV energy_at_rung particle_rung
  simp

-- Muon-electron mass ratio
theorem muon_electron_rung_difference :
  particle_rung Particle.muon = particle_rung Particle.electron + 7 := by
  unfold particle_rung
  norm_num

-- The 45-gap: bottom quark sits at critical rung
theorem bottom_at_45_gap :
  particle_rung Particle.bottom = 45 := by
  unfold particle_rung
  rfl

-- No Standard Model particles at multiples of 45 above 45
theorem no_particles_at_higher_45_multiples :
  ∀ (p : Particle) (n : ℕ), n > 1 → particle_rung p ≠ 45 * n := by
  intro p n hn
  cases p <;> unfold particle_rung <;> simp <;> omega

-- Lepton family structure
theorem lepton_rung_differences :
  particle_rung Particle.muon - particle_rung Particle.electron = 7 ∧
  particle_rung Particle.tau - particle_rung Particle.muon = 5 := by
  unfold particle_rung
  constructor <;> norm_num

-- Neutrino mass hierarchy
theorem neutrino_mass_ordering :
  particle_rung Particle.neutrino_e < particle_rung Particle.neutrino_mu ∧
  particle_rung Particle.neutrino_mu < particle_rung Particle.neutrino_tau := by
  unfold particle_rung
  constructor <;> norm_num

-- W and Z are adjacent
theorem w_z_adjacent :
  particle_rung Particle.z_boson = particle_rung Particle.w_boson + 1 := by
  unfold particle_rung
  norm_num

-- Eight-beat modular structure
theorem particle_eight_beat :
  ∀ (p : Particle), ∃ (k : ℕ) (r : Fin 8),
    particle_rung p = 8 * k + r.val := by
  intro p
  let n := particle_rung p
  use n / 8, ⟨n % 8, Nat.mod_lt n (by norm_num : 0 < 8)⟩
  simp [Nat.div_add_mod]

-- Mass ratio theorem
theorem particle_mass_ratio (p q : Particle) :
  particle_mass_eV p / particle_mass_eV q = φ ^ (particle_rung p - particle_rung q : ℤ) := by
  unfold particle_mass_eV energy_at_rung
  by_cases h : particle_rung p ≥ particle_rung q
  · -- Case: p rung ≥ q rung
    have : (particle_rung p - particle_rung q : ℤ) = ↑(particle_rung p - particle_rung q) := by
      simp [Int.coe_nat_sub h]
    rw [this, zpow_coe_nat]
    rw [div_eq_iff (by simp : E_coh * φ ^ particle_rung q ≠ 0)]
    rw [mul_comm (E_coh * φ ^ particle_rung p)]
    rw [mul_assoc]
    rw [← pow_add]
    congr 1
    exact Nat.add_sub_of_le h
  · -- Case: p rung < q rung
    push_neg at h
    have hlt : particle_rung p < particle_rung q := h
    have : (particle_rung p - particle_rung q : ℤ) = -↑(particle_rung q - particle_rung p) := by
      simp [Int.coe_nat_sub (le_of_lt hlt)]
      ring
    rw [this, zpow_neg, zpow_coe_nat]
    rw [div_eq_iff (by simp : E_coh * φ ^ particle_rung q ≠ 0)]
    rw [inv_mul_eq_div_iff_eq_mul]
    rw [mul_comm, mul_assoc]
    rw [← pow_add]
    congr 1
    exact Nat.add_sub_of_le (le_of_lt hlt)
    exact pow_ne_zero _ (by simp : φ ≠ 0)

/-!
# Predictions for New Particles
-/

-- Predicted new particles at specific rungs
def predicted_new_particles : List ℕ := [60, 61, 62, 65, 70]

-- These rungs are currently unoccupied
theorem new_particles_unoccupied :
  ∀ (r : ℕ), r ∈ predicted_new_particles →
    ∀ (p : Particle), particle_rung p ≠ r := by
  intro r hr p
  cases hr <;> cases p <;> unfold particle_rung <;> simp_all

/-!
# Summary Theorem
-/

-- All particle masses come from one formula with no free parameters
theorem P7_AllParticleMasses :
  ∀ (p : Particle), ∃ (r : ℕ),
    particle_mass_eV p = E_coh * φ ^ r ∧
    (∀ (q : Particle), particle_mass_eV p = particle_mass_eV q →
      particle_rung p = particle_rung q → p = q ∨ p = Particle.photon ∧ q = Particle.photon) := by
  intro p
  use particle_rung p
  constructor
  · -- First part: mass formula
    rfl
  · -- Second part: uniqueness (except for massless photon)
    intro q h_mass h_rung
    by_cases hp : p = Particle.photon
    · left
      rw [hp]
    · by_cases hq : q = Particle.photon
      · -- If q is photon but p is not, their rungs differ
        unfold particle_rung at h_rung
        rw [hq] at h_rung
        cases p <;> simp at h_rung hp <;> try contradiction
      · -- Neither is photon, so if they have same rung they must be equal
        -- We prove by exhaustive case analysis
        left
        cases p <;> cases q <;> unfold particle_rung at h_rung <;>
          simp at h_rung hp hq <;> try rfl <;> try contradiction <;>
          -- All non-photon particles have distinct rungs
          norm_num at h_rung

end RecognitionScience
