import YangMills.Construction.PassageToTheLimit.FormsOnProductsOfSpacesOfFunctionsOfClassC1
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace LimitSpaces
open Ambient ReflectionPositivity.CutoffMirrors
def torusFormsBounded : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    (∀ D : MirrorData, LatticeFunctionalBound D n) ∧
    ∀ (D : MirrorData) (K : Fin n → Set (Ambient.periodic.Carrier D.toStandingParameters)),
      (∀ i, Ambient.periodic.IsCompactSubset D.toStandingParameters (K i)) →
      Pairwise (Function.onFun Disjoint K) →
      IsRealFormBoundedBy (torusForm D (W := K)) ((4 * (D.faceCount : ℝ)) ^ n)
end LimitSpaces
end YangMills.Construction
end
