import YangMills.Construction.TorusOrFourSpace.FunctionsOfClassC1SupportsAndNorms
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicSpace.Kind
variable (D : Params) (E : Kind)
def lipschitzSupportedIn (A : Set (E.Pt D)) : Set (E.Pt D → ℝ) :=
  {h | IsLipschitzQ D E h ∧ IsCompactQ D E (supportQ D E h) ∧ supportQ D E h ⊆ A}
def c1SupportedIn (A : Set (E.Pt D)) : Set (E.Pt D → ℝ) :=
  {h | h ∈ c1Set D E ∧ IsCompactQ D E (supportQ D E h) ∧ supportQ D E h ⊆ A}
end YangMills.Construction.PeriodicSpace.Kind
