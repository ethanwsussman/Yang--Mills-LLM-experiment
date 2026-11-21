import YangMills.Construction.Matrices.GroupLieProducts
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
namespace Matrices
namespace GroupLieProduct
abbrev IsHolomorphicToMatrixEntries {ι κ : Type} [Fintype ι] [Fintype κ]
    (b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless) (W : Set (ι ⊕ κ → ComplexMatrix2))
    (Φ : (ι ⊕ κ → ComplexMatrix2) → ComplexMatrix2) : Prop :=
  IsHolomorphicToCoords b Coordinates.ComplexCoordinates.matrixEquiv W Φ
end GroupLieProduct
end Matrices
namespace PeriodicLattice
open Matrices
variable {L m : ℕ} {j : ℤ} {ι κ : Type} [Fintype ι] [Fintype κ]
structure IsHolomorphicGaugeFieldFamily (b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless)
    (W : Set (ι ⊕ κ → ComplexMatrix2)) (U : (ι ⊕ κ → ComplexMatrix2) → Bond L m j → ComplexMatrix2) :
    Prop where
  isOpen : ComplexMatrix2.IsRelativelyOpen (GroupLieProduct ι κ) W
  isGaugeField : ∀ p ∈ W, IsGaugeField complexGaugeGroup univ (U p)
  holomorphic : ∀ e : Bond L m j,
    GroupLieProduct.IsHolomorphicToMatrixEntries b W fun p => U p e
structure IsHolomorphicBondFormFamily (b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless)
    (W : Set (ι ⊕ κ → ComplexMatrix2)) (A : (ι ⊕ κ → ComplexMatrix2) → Bond L m j → ComplexMatrix2) :
    Prop where
  isOpen : ComplexMatrix2.IsRelativelyOpen (GroupLieProduct ι κ) W
  isBondForm : ∀ p ∈ W, IsBondForm complexLieAlgebra (A p)
  holomorphic : ∀ e : Bond L m j,
    GroupLieProduct.IsHolomorphicToMatrixEntries b W fun p => A p e
end PeriodicLattice
end YangMills.Construction
