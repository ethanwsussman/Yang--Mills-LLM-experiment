import YangMills.Construction.Towers.CompositionWithAStepOfTheCriticalBranch
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.PeriodicOperators.Tempered
variable {L : ℕ}
structure IsDefinedOn (L : ℕ) (F : FieldFamily L) (S : Set ℕ)
    (D : ∀ n : ℕ, Set (UnitEdge L n → Matrices.ComplexMatrix2)) : Prop where
  eventually : EventuallyForSides L (· ∈ S)
  admissible : ∀ n ∈ S, 0 < n → IsAdmissibleMember (F n)
  nhdsIdentity : ∀ n ∈ S, 0 < n → Tower.EventuallyNearIdentity (Tower.fieldSpace L n 0 0) (· ∈ D n)
theorem isDefinedOn_of_isLatticeFunctional {F : FieldFamily L} (h : IsLatticeFunctional L F) :
    IsDefinedOn L F {n | IsAdmissibleMember (F n)} fun _ => univ where
  eventually := by
    obtain ⟨s₀, hs₀, hlarge⟩ := h
    exact ⟨s₀, hs₀, fun s hs hle n hn e => hlarge s hs hle n hn e⟩
  admissible := fun _ hn _ => hn
  nhdsIdentity := fun _ _ _ => Filter.Eventually.of_forall fun _ => mem_univ _
def CompStepEventuallyDefined : Prop :=
  ∀ (L : ℕ) (hL : Conventions.IsAdmissibleBlockingFactor L) (F : FieldFamily L) (S : Set ℕ)
    (D : ∀ n : ℕ, Set (UnitEdge L n → Matrices.ComplexMatrix2)), IsDefinedOn L F S D → ∀ i : ℕ,
    (∀ s ∈ Tower.sideSet L, (L : ℝ) * s ∈ Tower.sideSet L ∧ s ≤ (L : ℝ) * s) ∧
    EventuallyForSides L (fun n => n + 1 ∈ S) ∧
    EventuallyForSides L (· ∈ stepIndexSet S) ∧
    ∀ n ∈ stepIndexSet S, ∀ P : Set (Tower.Edge L n (i + 1) (i + 1) → Matrices.ComplexMatrix2),
      Tower.EventuallyNearIdentity (Tower.fieldSpace L n (i + 1) (i + 1)) (· ∈ P) →
      Tower.EventuallyNearIdentity (Tower.fieldSpace L n (i + 1) (i + 1))
        (· ∈ stepCompDomain (Nat.lt_of_lt_of_le (by norm_num) hL.2) n i P (D (n + 1)))
end YangMills.Construction.PeriodicOperators.Tempered
end
