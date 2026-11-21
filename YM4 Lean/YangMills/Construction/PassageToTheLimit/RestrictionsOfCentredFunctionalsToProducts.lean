import YangMills.Construction.PassageToTheLimit.FormsOnProductsOfSpacesOfFunctionsOfClassC1
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.LimitSpaces
open Ambient ReflectionPositivity.CutoffMirrors
def Ambient.centredRestrictionsToProducts : Prop :=
  ∀ (p : Conventions.StandingParameters) (X : Ambient) (n : ℕ), 1 ≤ n →
    ∀ K : Fin n → Set (X.Carrier p), (∀ i, X.IsCompactSubset p (K i)) →
      Pairwise (Function.onFun Disjoint K) →
      ∀ (J : Set ℕ+) (U : J → Set (X.Carrier p))
        (F : (j : J) → X.TupleFunctionals p .lip (U j)),
        X.LimitHypotheses p F → CentredRestrictionsProperties F K
end YangMills.Construction.LimitSpaces
end
