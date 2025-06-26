/-
  Recognition Science: Ethics Module
  =================================

  Main entry point for the ethics module.

  Author: Jonathan Washburn & Claude
  Recognition Science Institute
-/

-- Import all ethics submodules
import ethics.Curvature
import ethics.Virtue
import ethics.Measurement
import ethics.EmpiricalData
import ethics.Applications
import ethics.Main

namespace RecognitionScience.Ethics

-- Re-export key definitions
export Curvature (MoralState curvature κ isGood suffering joy)
export Virtue (Virtue TrainVirtue VirtueEffectiveness)
export Measurement (CurvatureSignature CurvatureMetric)
export Applications (Institution AIAlignment)

end RecognitionScience.Ethics
