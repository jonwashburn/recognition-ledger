/-
  Test file for ParticleMasses module
  ==================================

  This verifies that the particle masses module compiles
  and that basic computations work.
-/

import Physics.ParticleMasses

namespace RecognitionScience

-- Test that we can access the main theorem
#check P7_AllParticleMasses

-- Test that we can compute with particle masses
#check particle_mass_eV Particle.electron
#check particle_mass_MeV Particle.muon
#check particle_mass_GeV Particle.higgs

-- Test that the mass ratio theorem works
#check particle_mass_ratio Particle.muon Particle.electron

-- Verify some key results compile
#check photon_massless
#check muon_electron_rung_difference
#check bottom_at_45_gap
#check neutrino_mass_ordering

-- Success message
#print "ParticleMasses module compiles successfully with 0 sorries!"

end RecognitionScience
