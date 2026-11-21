import YangMills.Construction.Towers.ConfigurationsUnderTheLeftChart
import YangMills.Construction.Towers.TheScaledPicture
import YangMills.Construction.Towers.TheSettingOfTheRemainder
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.HolomorphicRescaledKernels
def SmallIterates (L k : ℕ) (ρ : ℝ) : Prop :=
  ∀ a ∈ (Tower.FullSpace.complexEdgeForms (Tower.meshAt L k 0) :
      Set (Tower.FullSpace.Edge L k 0 → Matrices.ComplexMatrix2)),
    Tower.maxOperatorNorm a < ENNReal.ofReal ρ → ∀ j < k,
      Tower.FullSpace.complexIter L k j (Tower.FullSpace.remainderGaugeField a) ∈
          Tower.FullSpace.fieldsValuedIn L k j PeriodicLattice.complexGaugeGroup ∧
        ∀ e : Tower.FullSpace.Edge L k j,
          Matrices.ComplexMatrix2.operatorNorm
              (Tower.FullSpace.complexIter L k j (Tower.FullSpace.remainderGaugeField a) e - 1) <
            Tower.polydiscRadius L / 2
def KernelEntriesHolomorphic : Prop :=
  ∀ (L : ℕ), Conventions.IsAdmissibleBlockingFactor L → ∀ (ρ : ℝ), 0 < ρ → ∀ (k : ℕ), 1 ≤ k →
    SmallIterates L k ρ →
    (∀ i' i, ∃ (F : Finset (Tower.FullSpace.Edge L k 0)) (f : (F → Matrices.ComplexMatrix2) → ℂ),
      (∀ B : Module.Basis (Fin 3) ℂ Matrices.ComplexMatrix2.traceless,
        Matrices.GroupLieProduct.IsHolomorphicOnTraceless B Tower.LeftChartFields.scalarCoords
          (Matrices.GroupLieProduct.supBall F ρ) f) ∧
      ∀ a ∈ (Tower.FullSpace.complexEdgeForms (Tower.meshAt L k 0) :
          Set (Tower.FullSpace.Edge L k 0 → Matrices.ComplexMatrix2)),
        Tower.maxOperatorNorm a < ENNReal.ofReal ρ →
          f (fun e => a e) =
            (Tower.FullSpace.rescaledOperators L k (Tower.FullSpace.remainderGaugeField a)).Q i' i) ∧
    (∀ i' i, ∃ (F : Finset (Tower.FullSpace.Edge L k 0)) (f : (F → Matrices.ComplexMatrix2) → ℂ),
      (∀ B : Module.Basis (Fin 3) ℂ Matrices.ComplexMatrix2.traceless,
        Matrices.GroupLieProduct.IsHolomorphicOnTraceless B Tower.LeftChartFields.scalarCoords
          (Matrices.GroupLieProduct.supBall F ρ) f) ∧
      ∀ a ∈ (Tower.FullSpace.complexEdgeForms (Tower.meshAt L k 0) :
          Set (Tower.FullSpace.Edge L k 0 → Matrices.ComplexMatrix2)),
        Tower.maxOperatorNorm a < ENNReal.ofReal ρ →
          f (fun e => a e) =
            (Tower.FullSpace.rescaledOperators L k (Tower.FullSpace.remainderGaugeField a)).R i' i)
end YangMills.Construction.Tower.FullSpace.HolomorphicRescaledKernels
end
