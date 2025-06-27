/-
  Physical Units and Constants
  ============================

  This file now re-exports foundation units for backward compatibility.
  All new code should import Foundation.Util.Units directly.
-/

import Foundation.Util.Units

namespace RecognitionScience.Units

-- Re-export foundation types and constants
open Foundation.Util.Units

-- Backward compatibility aliases
abbrev Dimension := Foundation.Util.Units.Dimension
abbrev Quantity := Foundation.Util.Units.Quantity

-- Re-export dimensions
def dimensionless := Foundation.Util.Units.dimensionless
def length := Foundation.Util.Units.length
def mass := Foundation.Util.Units.mass
def time := Foundation.Util.Units.time
def velocity := Foundation.Util.Units.velocity
def acceleration := Foundation.Util.Units.acceleration
def energy := Foundation.Util.Units.energy
def power := Foundation.Util.Units.power

-- Re-export unit constructors
def meter := Foundation.Util.Units.meter
def kilogram := Foundation.Util.Units.kilogram
def second := Foundation.Util.Units.second
def joule := Foundation.Util.Units.joule
def watt := Foundation.Util.Units.watt

-- Re-export constants
namespace Constants
  def c := Foundation.Util.Units.c
  def G := Foundation.Util.Units.G
  def ℏ := Foundation.Util.Units.ℏ
  def k_B := Foundation.Util.Units.k_B
  def t_Planck := Foundation.Util.Units.t_Planck
  def ℓ_Planck := Foundation.Util.Units.ℓ_Planck
  def m_Planck := Foundation.Util.Units.m_Planck
  def τ₀ := Foundation.Util.Units.τ₀
  def E_coh := Foundation.Util.Units.E_coh
  def φ := Foundation.Util.Units.φ
end Constants

end RecognitionScience.Units
