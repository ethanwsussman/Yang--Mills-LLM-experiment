import YangMills.Construction.Geometry.TorusMetric
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction
namespace Tower
def oddHarmonicWeight (a : ℤ) : ℝ := (max 1 (2 * |(a : ℝ)| - 1))⁻¹
def oddHarmonicWeightTerm (m : Fin 4 → ℤ) : ℝ :=
  (TorusMetric.supNormVec fun ν => (m ν : ℝ))⁻¹ * ∏ ν, oddHarmonicWeight (m ν)
def oddHarmonicWeightSum : ℝ≥0∞ :=
  ⨆ s : Finset {m : Fin 4 → ℤ // m ≠ 0}, ∑ m ∈ s, ENNReal.ofReal (oddHarmonicWeightTerm m)
end Tower
end YangMills.Construction
end
