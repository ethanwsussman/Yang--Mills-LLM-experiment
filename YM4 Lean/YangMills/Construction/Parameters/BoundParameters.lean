import YangMills.Construction.Parameters.ConstructionParameters
import Mathlib
set_option autoImplicit false
universe u
namespace YangMills.Construction.ParameterChoice
def ExponentLowerBound (r : ℝ) : Prop := 2 ≤ r
def GapLowerBound (L : ℕ) (R₁ : ℝ) : Prop := (L : ℝ) ≤ R₁
theorem IsAdmissible.exponentLowerBound {T : DerivedConstants} {c : FullChoice}
    (h : IsAdmissible T c) : ExponentLowerBound c.r := by
  unfold ExponentLowerBound
  exact_mod_cast h.r_floor
theorem IsAdmissible.gapLowerBound {T : DerivedConstants} {c : FullChoice}
    (h : IsAdmissible T c) : GapLowerBound c.L c.gapNumber := by
  unfold GapLowerBound
  exact_mod_cast h.gapNumber_floor
end YangMills.Construction.ParameterChoice
