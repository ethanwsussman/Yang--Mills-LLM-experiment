import YangMills.Construction.Continuum.OperationsOnFunctionsOfSeveralPoints
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ConfigSpace
def CompactSupportTensorFacts : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    (∀ V : Set (Config n), IsOpen V → ∀ φ ∈ smoothCompactSupportIn V,
      IsSchwartz φ ∧ FlatOff φ V) ∧
    smoothCompactSupportIn (distinctArgs n) ⊆ schwartzFlatOffDiagonal n ∧
    smoothCompactSupportIn (posTimeSet n) ⊆ schwartzFlatOffPosTime n ∧
    smoothCompactSupportIn (negTimeSet n) ⊆ schwartzFlatOffNegTime n ∧
    (∀ f ∈ separatedFamilies Set.univ n, AllSmoothCompact f →
      tensorRealFamily f ∈ smoothCompactSupportIn (distinctArgs n) ∧
      ((∀ i, tsupport (f i) ⊆ upperHalfSpace) →
        tensorRealFamily f ∈ smoothCompactSupportIn (posTimeSet n))) ∧
    (∀ f ∈ separatedFamilies Set.univ n,
      (∀ r : EuclidMotion, motionAct r (tensorRealFamily f) =
        tensorRealFamily fun i => f i ∘ r.invMap) ∧
      (∀ ς : Equiv.Perm (Fin n), permAct ς (tensorRealFamily f) =
        tensorRealFamily fun j => f (ς.symm j)) ∧
      flipConj (tensorRealFamily f) =
        tensorRealFamily fun i => f i ∘ timeFlip)
end YangMills.Construction.ConfigSpace
end
