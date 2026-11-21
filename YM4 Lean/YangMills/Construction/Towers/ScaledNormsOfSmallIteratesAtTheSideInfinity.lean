import YangMills.Construction.Towers.AveragesAreContractions
import YangMills.Construction.Towers.TheSettingOfTheRemainder
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.RescaledNormBounds
structure SmallIterates (L k : ℕ) (a : Tower.FullSpace.Edge L k 0 → Matrices.ComplexMatrix2) : Prop where
  mem_fields : ∀ j < k,
    Tower.FullSpace.complexIter L k j (Tower.FullSpace.remainderGaugeField a) ∈
      Tower.FullSpace.fieldsValuedIn L k j PeriodicLattice.complexGaugeGroup
  norm_sub_one_le : ∀ j < k, ∀ e : Tower.FullSpace.Edge L k j,
    Matrices.ComplexMatrix2.operatorNorm
        (Tower.FullSpace.complexIter L k j (Tower.FullSpace.remainderGaugeField a) e - 1) ≤
      20 * Tower.meshAt L k j * (Tower.maxOperatorNorm a).toReal
  norm_sub_one_lt_half : ∀ j < k, ∀ e : Tower.FullSpace.Edge L k j,
    Matrices.ComplexMatrix2.operatorNorm
        (Tower.FullSpace.complexIter L k j (Tower.FullSpace.remainderGaugeField a) e - 1) <
      Tower.polydiscRadius L / 2
def RescaledNormsBounded : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ, 1 ≤ k →
    ∀ a ∈ Tower.FullSpace.complexEdgeForms (Tower.meshAt L k 0),
      Tower.maxOperatorNorm a ≤ ENNReal.ofReal (1 / 41) →
      SmallIterates L k a →
        Tower.SmoothingContraction.OpNormLE (PeriodicOperators.colourEdges L k 0)
            (PeriodicOperators.colourEdges L k k)
            (Tower.FullSpace.rescaledOperators L k (Tower.FullSpace.remainderGaugeField a)).Q
            (Real.exp (30 * ((12 * (L : ℝ) ^ 3 + 2) * (2560 * (Tower.polydiscRadius L ^ 2)⁻¹)))) ∧
          Tower.SmoothingContraction.OpNormLE (PeriodicOperators.colourVertices L k 0)
            (PeriodicOperators.colourVertices L k k)
            (Tower.FullSpace.rescaledOperators L k (Tower.FullSpace.remainderGaugeField a)).R
            (Real.exp (30 * ((12 * (L : ℝ) ^ 3 + 2) * (2560 * (Tower.polydiscRadius L ^ 2)⁻¹))))
end YangMills.Construction.Tower.FullSpace.RescaledNormBounds
end
