import YangMills.Construction.Matrices.GroupLieProducts
import Mathlib
open Set
noncomputable section
namespace YangMills.Construction.Matrices.UnimodularArguments
def unimodularPart {P : Type} (D : Set (P → ComplexMatrix2)) : Set (P → ComplexMatrix2) :=
  D ∩ GroupLieProduct.unimodularPi P
def HolomorphicAtUnimodular : Prop :=
  ∀ (P : Type) [Fintype P] (k : ℕ) (ν : P ≃ Fin k) (D : Set (P → ComplexMatrix2))
    (F : (P → ComplexMatrix2) → ComplexMatrix2), IsOpen D →
    Coordinates.ComplexCoordinates.IsHolomorphicVia (GroupLieProduct.matrixPiEquiv ν)
      Coordinates.ComplexCoordinates.matrixEquiv D F →
    (∀ U ∈ unimodularPart D, F U ∈ ComplexMatrix2.unitDeterminant) →
    ComplexMatrix2.IsRelativelyOpen (GroupLieProduct.unimodularPi P) (unimodularPart D) ∧
    ComplexMatrix2.IsHolomorphicBetween (fun _ : P => ComplexMatrix2.FactorKind.group)
      (fun _ : Unit => ComplexMatrix2.FactorKind.group)
      (unimodularPart D) (fun U _ => F U) ∧
    (∀ (N : ℕ) (μ : P ≃ Fin N) (b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless), 1 ≤ N →
      Coordinates.ComplexCoordinates.IsHolomorphicOnSL2Power b
        ((fun U => U ∘ μ.symm) '' unimodularPart D)
        fun X => F (X ∘ μ)) ∧
    ∀ b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless,
      GroupLieProduct.IsHolomorphicToUnimodular (κ := Empty) b
        ((fun x : P ⊕ Empty → ComplexMatrix2 => x ∘ Sum.inl) ⁻¹' unimodularPart D)
        fun x => F (x ∘ Sum.inl)
end YangMills.Construction.Matrices.UnimodularArguments
end
