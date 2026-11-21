import YangMills.Construction.PassageToTheLimit.SpaceTestFunctionsTranslationsReflectionsPositions
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction
namespace LimitSpaces
structure IsFinePartitionOfUnity (s : Conventions.StandingParameters) (E : Ambient) (ε : ℝ)
    {I : Type} (ψ : I → E.Carrier s → ℝ) : Prop where
  mem_c1Compact : ∀ ν, ψ ν ∈ E.c1Compact s
  mem_Icc : ∀ ν x, ψ ν x ∈ Set.Icc (0 : ℝ) 1
  closedSupport_nonempty : ∀ ν, (E.closedSupport s (ψ ν)).Nonempty
  setDiam_closedSupport_le : ∀ ν, E.setDiam s (E.closedSupport s (ψ ν)) ≤ ENNReal.ofReal ε
  locallyFinite_compact : ∀ C : Set (E.Carrier s), E.IsCompactSubset s C →
    {ν | (C ∩ E.closedSupport s (ψ ν)).Nonempty}.Finite
  finite_ne_zero : ∀ x, {ν | ψ ν x ≠ 0}.Finite
  finsum_eq_one : ∀ x, ∑ᶠ ν, ψ ν x = 1
def FinePartitionOfUnity.Claim : Prop :=
  ∀ (s : Conventions.StandingParameters) (E : Ambient) (ε : ℝ), 0 < ε →
    ∃ (I : Type) (ψ : I → E.Carrier s → ℝ), IsFinePartitionOfUnity s E ε ψ
end LimitSpaces
end YangMills.Construction
