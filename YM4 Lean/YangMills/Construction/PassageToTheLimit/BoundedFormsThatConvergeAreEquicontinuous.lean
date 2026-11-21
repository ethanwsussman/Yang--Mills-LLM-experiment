import YangMills.Construction.PassageToTheLimit.FormsOnProductsOfSpacesOfFunctionsOfClassC1
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.LimitSpaces
open Ambient ReflectionPositivity.CutoffMirrors
def Ambient.pointwiseConvergentFormsEquicontinuous : Prop :=
  ∀ (p : Conventions.StandingParameters) (X : Ambient) (n : ℕ), 1 ≤ n →
    ∀ K : Fin n → Set (X.Carrier p), (∀ i, X.IsCompactSubset p (K i)) →
      Pairwise (Function.onFun Disjoint K) →
      X.ProductElementsAreSepTuples p K ∧ X.ConvergentBoundedFormsEquicontinuous p K
end YangMills.Construction.LimitSpaces
end
