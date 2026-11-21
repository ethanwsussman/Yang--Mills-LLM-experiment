import YangMills.Construction.PassageToTheLimit.FormsOnProductsOfSpacesOfFunctionsOfClassC1
import Mathlib
set_option autoImplicit false
open Filter Set Topology
open scoped ENNReal NNReal
noncomputable section
namespace YangMills.Construction
namespace LimitSpaces
open Ambient ReflectionPositivity.CutoffMirrors
def Ambient.uniformBoundednessEquicontinuity : Prop :=
  ∀ (M : SharpParameter) (q : ℕ), 1 ≤ q →
    (∀ (s : Conventions.StandingParameters) (E : Ambient),
      E.C1WithinIsBanach s ∧ E.TranslationContinuityC1 s M ∧
      ∀ W : Fin q → Set (E.Carrier s), (∀ l, E.IsCompactSubset s (W l)) →
        Pairwise (Function.onFun Disjoint W) →
        E.ProductElementsAreSepTuples s W ∧ E.ConvergentBoundedFormsEquicontinuous s W ∧
        ∀ (𝒥 : Set ℕ+) (Dom : 𝒥 → Set (E.Carrier s))
          (Φ : (j : 𝒥) → E.TupleFunctionals s .lip (Dom j)),
          E.LimitHypotheses s Φ → CentredRestrictionsProperties Φ W) ∧
    (∀ D : MirrorData, LatticeFunctionalBound D q) ∧
    (∀ (D : MirrorData) (W : Fin q → Set (Ambient.periodic.Carrier D.toStandingParameters)),
      (∀ l, Ambient.periodic.IsCompactSubset D.toStandingParameters (W l)) →
      Pairwise (Function.onFun Disjoint W) →
      IsRealFormBoundedBy (torusForm D (W := W)) ((4 * (D.faceCount : ℝ)) ^ q)) ∧
    (∀ (s : Conventions.StandingParameters) (D : MirrorData) (W : Fin q → Set (Ambient.euclidean.Carrier s)),
      D.L = s.L → (∀ l, Ambient.euclidean.IsCompactSubset s (W l)) →
      Pairwise (Function.onFun Disjoint W) → TorusSideAdmissible D W →
      PeriodizedFormBound D W) ∧
    (∀ (s : Conventions.StandingParameters) (W : Fin q → Set (Ambient.periodic.Carrier s)),
      (∀ l, Ambient.periodic.IsCompactSubset s (W l)) → Pairwise (Function.onFun Disjoint W) →
      TorusSequencesEquicontinuous s W) ∧
    ∀ (s : Conventions.StandingParameters) (W : Fin q → Set (Ambient.euclidean.Carrier s)),
      (∀ l, Ambient.euclidean.IsCompactSubset s (W l)) → Pairwise (Function.onFun Disjoint W) →
      EuclideanSequencesEquicontinuous s W
end LimitSpaces
end YangMills.Construction
end
