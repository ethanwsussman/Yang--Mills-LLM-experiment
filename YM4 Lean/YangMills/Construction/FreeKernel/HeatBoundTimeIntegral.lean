import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.FreeKernel
open MeasureTheory
def TimeIntegralOfHeatBound : Prop :=
  ∀ k : ℕ, 3 ≤ k → ∃ c : ℝ, 0 ≤ c ∧ ∀ R : ℝ, 0 ≤ R →
    IntegrableOn
        (fun T : ℝ => (max T 1) ^ (-(k : ℝ) / 2) * Real.exp (-R / Real.sqrt (max T 1)))
        (Set.Ioi 0) ∧
      ∫ T in Set.Ioi (0 : ℝ), (max T 1) ^ (-(k : ℝ) / 2) * Real.exp (-R / Real.sqrt (max T 1)) ≤
        c * (R + 1) ^ (2 - (k : ℝ))
end YangMills.Construction.FreeKernel
