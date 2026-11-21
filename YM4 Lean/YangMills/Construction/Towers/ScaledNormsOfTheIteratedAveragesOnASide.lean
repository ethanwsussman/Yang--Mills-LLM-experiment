import YangMills.Construction.Towers.AveragesAreContractions
import YangMills.Construction.Towers.TheConstantOfTheStepsOfTheIteratedAverages
import YangMills.Construction.Towers.TheSettingOfTheRemainder
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.Tower
open SmoothingContraction (TorusOpNormLE)
namespace RescaledNormBounds
variable {L n k : ℕ}
structure IteratesControlled (a : Edge L n k 0 → Matrices.ComplexMatrix2) : Prop where
  mem_fields : ∀ i < k, PeriodicLattice.complexBlockFieldAtLevel i (remainderGaugeField a) ∈
    fieldsIn L n k i PeriodicLattice.complexGaugeGroup
  norm_sub_one_le : ∀ i < k, ∀ e : Edge L n k i,
    Matrices.ComplexMatrix2.operatorNorm
        (PeriodicLattice.complexBlockFieldAtLevel i (remainderGaugeField a) e - 1) ≤
      20 * meshAt L k i * (maxOperatorNorm a).toReal
  norm_sub_one_lt : ∀ i < k, ∀ e : Edge L n k i,
    Matrices.ComplexMatrix2.operatorNorm
        (PeriodicLattice.complexBlockFieldAtLevel i (remainderGaugeField a) e - 1) <
      polydiscRadius L / 2
def OperatorNormsBounded : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ n k : ℕ, 0 < n → 1 ≤ k →
    ∀ a ∈ complexEdgeForms L n k 0, maxOperatorNorm a ≤ ENNReal.ofReal (1 / 41) →
      IteratesControlled a →
      TorusOpNormLE (finestMesh L k) (meshAt L k k)
          (rescaledOperators L n k (remainderGaugeField a)).Q
          (Real.exp (30 * smoothingStepConstant L)) ∧
        TorusOpNormLE (finestMesh L k) (meshAt L k k)
          (rescaledOperators L n k (remainderGaugeField a)).R
          (Real.exp (30 * smoothingStepConstant L))
end RescaledNormBounds
end YangMills.Construction.Tower
end
