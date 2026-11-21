import YangMills.Construction.TransferOperators.ObjectsOfAnInsertionOfContractionsBetweenLayers
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TransferOperators.LevelProductOps
def ContractionStatement : Prop :=
  ∀ (μ : Fin 4) (B : Block μ) (Ξ : B.L2Operator), ‖Ξ‖ ≤ 1 →
    ∀ (n : ℤ) (Q : AddSubgroup (InfiniteLattice.LatticePoint 1)), B.PairwiseDisjointShifts n Q →
      ∀ Γ : CubicPeriodSublattice, Γ.lattice.periods ≤ Q →
        Γ.LevelProductOpsContract B Ξ n Q
end YangMills.Construction.TransferOperators.LevelProductOps
end
