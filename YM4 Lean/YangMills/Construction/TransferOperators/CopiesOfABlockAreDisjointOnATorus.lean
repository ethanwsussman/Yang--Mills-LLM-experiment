import YangMills.Construction.TransferOperators.ObjectsOfAnInsertionOfContractionsBetweenLayers
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open InfiniteLattice
namespace TransferOperators.BlockCopies
def DisjointStatement : Prop :=
  ∀ (μ : Fin 4) (B : Block μ) (n : ℤ) (Q : AddSubgroup (LatticePoint 1)), Q.FiniteIndex →
    B.PairwiseDisjointShifts n Q →
    ∀ Γ : CubicPeriodSublattice, Γ.lattice.periods ≤ Q → Γ.BlockCopiesDisjoint B n Q
end TransferOperators.BlockCopies
end YangMills.Construction
end
