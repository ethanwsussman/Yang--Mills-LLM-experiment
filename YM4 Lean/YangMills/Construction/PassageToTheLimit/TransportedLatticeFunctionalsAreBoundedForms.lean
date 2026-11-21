import YangMills.Construction.PassageToTheLimit.FormsOnProductsOfSpacesOfFunctionsOfClassC1
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace LimitSpaces
open Ambient ReflectionPositivity.CutoffMirrors
def periodizedFormsBounded : Prop :=
  ∀ (q : ℕ), 1 ≤ q → ∀ (s : Conventions.StandingParameters) (D : MirrorData)
    (W : Fin q → Set (Ambient.euclidean.Carrier s)),
    D.L = s.L → (∀ l, Ambient.euclidean.IsCompactSubset s (W l)) →
    Pairwise (Function.onFun Disjoint W) → TorusSideAdmissible D W →
    PeriodizedFormBound D W
end LimitSpaces
end YangMills.Construction
end
