import YangMills.Construction.Lattice.HolomorphicFieldFamilies
import Mathlib
set_option autoImplicit false
open Set
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.Matrices.GroupLieProduct
variable {ι κ : Type}
def cartanDirection : ComplexMatrix2 := Matrix.diagonal ![1, -1]
def withParameter (p : ι ⊕ κ → ComplexMatrix2) (t : ℂ) : ι ⊕ (κ ⊕ Unit) → ComplexMatrix2
  | .inl i => p (.inl i)
  | .inr (.inl k) => p (.inr k)
  | .inr (.inr _) => t • cartanDirection
def ParameterDerivativesHolomorphic : Prop :=
  ∀ (ι κ : Type) [Fintype ι] [Fintype κ] (b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless)
    (W : Set (ι ⊕ κ → ComplexMatrix2)) (W' : Set (ι ⊕ (κ ⊕ Unit) → ComplexMatrix2))
    (Φ : (ι ⊕ (κ ⊕ Unit) → ComplexMatrix2) → ComplexMatrix2),
    ComplexMatrix2.IsRelativelyOpen (GroupLieProduct ι κ) W →
    IsHolomorphicToMatrixEntries b W' Φ → (∀ p ∈ W, withParameter p 0 ∈ W') →
    ∀ n : ℕ, IsHolomorphicToMatrixEntries b W fun p =>
      iteratedDeriv n (fun t : ℂ => Φ (withParameter p t)) 0
end YangMills.Construction.Matrices.GroupLieProduct
