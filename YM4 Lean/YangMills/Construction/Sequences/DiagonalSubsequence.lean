import YangMills.Construction.Sequences.PNatIndexSetConvergence
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.DiagonalSubsequence
open YangMills.Construction.Sequences
def restrictAlong {j₀ : ℤ} (w : {j : ℤ // j₀ ≤ j} → ℂ) (J : PNatIndexSet) :
    (J.filterGe j₀).carrier → ℂ :=
  fun k => w ⟨(((k : ℕ+) : ℕ) : ℤ), k.property.2⟩
def CountableBoundedFamilyConverges : Prop :=
  ∀ (I : Type) [Countable I] (start : I → ℤ) (v : ∀ ι : I, {j : ℤ // start ι ≤ j} → ℂ),
    (∀ ι : I, ∃ C : ℝ, ∀ j : {j : ℤ // start ι ≤ j}, ‖v ι j‖ ≤ C) →
    ∀ J₀ : PNatIndexSet, ∃ J : PNatIndexSet, J.carrier ⊆ J₀.carrier ∧
      ∀ ι : I, (J.filterGe (start ι)).HasLimit (restrictAlong (v ι) J)
end YangMills.Construction.DiagonalSubsequence
