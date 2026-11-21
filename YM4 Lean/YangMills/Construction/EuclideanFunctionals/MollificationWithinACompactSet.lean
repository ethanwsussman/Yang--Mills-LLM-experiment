import YangMills.Construction.EuclideanFunctionals.StandingDataOfTheStudyFromOneInsertionToPlates
import Mathlib
noncomputable section
namespace YangMills.Construction.EuclideanFunctionals
def MollificationInCompact : Prop :=
  ∀ O : Set R4, IsOpen O → ∀ h ∈ C1c ℂ, supp h ⊆ O →
    ∃ Q : Set R4, IsCompact Q ∧ Q ⊆ O ∧ supp h ⊆ Q ∧
      ∃ hs : ℕ → R4 → ℂ,
        (∀ j, 1 ≤ j → hs j ∈ smoothCompactSupp R4 ℂ ∧ supp (hs j) ⊆ Q ∧
          l1Norm (hs j) ≤ l1Norm h) ∧
        TendstoC1 hs h ∧
        (IsRealValued h → ∀ j, 1 ≤ j → IsRealValued (hs j))
end YangMills.Construction.EuclideanFunctionals
