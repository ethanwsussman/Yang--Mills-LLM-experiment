import YangMills.Construction.Continuum.FlatSchwartzAndTuples
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ConfigSpace
def tensorSpan (n : ℕ) : Submodule ℂ (Config n → ℂ) :=
  Submodule.span ℂ (tensorProd '' smoothRealTupleSet n)
def TensorSpanDenseInFlatSchwartz : Prop :=
  ∀ n : ℕ, 2 ≤ n →
    IsSchwartzDenseIn (testFnOffDiag n) (flatSchwartzSet n) ∧
    IsSchwartzDenseIn (tensorSpan n : Set (Config n → ℂ)) (flatSchwartzSet n) ∧
    ∀ S₁ ∈ flatDualSet n, ∀ S₂ ∈ flatDualSet n,
      (∀ φ : flatSchwartzSet n, (∃ f ∈ smoothRealTupleSet n, φ.1 = tensorProd f) → S₁ φ = S₂ φ) →
        S₁ = S₂
end YangMills.Construction.ConfigSpace
end
