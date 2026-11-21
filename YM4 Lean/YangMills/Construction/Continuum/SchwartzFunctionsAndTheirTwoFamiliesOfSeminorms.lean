import YangMills.Construction.Continuum.TestFunctionsOfConfigurationSpace
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.SchwartzSeminorms
abbrev schwartzSpace (n : ℕ) : Set (ConfigurationSpace.Config n → ℂ) :=
  ConfigurationSpace.schwartzSet n
abbrev weightNorm {n : ℕ} (p : ℕ) (φ : schwartzSpace n) : ℝ≥0∞ :=
  ConfigurationSpace.sobolevWeightNorm p φ.1
end YangMills.Construction.SchwartzSeminorms
end
