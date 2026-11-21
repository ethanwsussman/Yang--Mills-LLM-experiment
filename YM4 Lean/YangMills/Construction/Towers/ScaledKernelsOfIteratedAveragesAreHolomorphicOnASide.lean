import YangMills.Construction.Towers.ConfigurationsUnderTheLeftChart
import YangMills.Construction.Towers.TheScaledPicture
import YangMills.Construction.Towers.TheSettingOfTheRemainder
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.Tower
def RescaledKernelsHolomorphicOnTorus : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ ρ : ℝ, 0 < ρ → ∀ k : ℕ, 1 ≤ k →
    ∀ m : ℕ, 0 < m →
    (∀ a ∈ (Tower.complexEdgeForms L m k 0 : Set (Tower.Edge L m k 0 → Matrices.ComplexMatrix2)),
      Tower.maxOperatorNorm a < ENNReal.ofReal ρ →
      ∀ j < k,
        PeriodicLattice.complexBlockFieldAtLevel j (Tower.remainderGaugeField a) ∈
            Tower.fieldsIn L m k j PeriodicLattice.complexGaugeGroup ∧
          ∀ e : Tower.Edge L m k j,
            Matrices.ComplexMatrix2.operatorNorm
                (PeriodicLattice.complexBlockFieldAtLevel j (Tower.remainderGaugeField a) e - 1) <
              Tower.polydiscRadius L / 2) →
    (∀ i' i, ∃ (F : Finset (Tower.Edge L m k 0)) (f : (F → Matrices.ComplexMatrix2) → ℂ),
      (∀ B : Module.Basis (Fin 3) ℂ Matrices.ComplexMatrix2.traceless,
        Matrices.GroupLieProduct.IsHolomorphicOnTraceless B Tower.LeftChartFields.scalarCoords
          (Matrices.GroupLieProduct.supBall F ρ) f) ∧
      ∀ a ∈ (Tower.complexEdgeForms L m k 0 : Set (Tower.Edge L m k 0 → Matrices.ComplexMatrix2)),
        Tower.maxOperatorNorm a < ENNReal.ofReal ρ →
        f (fun e => a e) = (Tower.rescaledOperators L m k (Tower.remainderGaugeField a)).Q i' i) ∧
    ∀ i' i, ∃ (F : Finset (Tower.Edge L m k 0)) (f : (F → Matrices.ComplexMatrix2) → ℂ),
      (∀ B : Module.Basis (Fin 3) ℂ Matrices.ComplexMatrix2.traceless,
        Matrices.GroupLieProduct.IsHolomorphicOnTraceless B Tower.LeftChartFields.scalarCoords
          (Matrices.GroupLieProduct.supBall F ρ) f) ∧
      ∀ a ∈ (Tower.complexEdgeForms L m k 0 : Set (Tower.Edge L m k 0 → Matrices.ComplexMatrix2)),
        Tower.maxOperatorNorm a < ENNReal.ofReal ρ →
        f (fun e => a e) = (Tower.rescaledOperators L m k (Tower.remainderGaugeField a)).R i' i
end YangMills.Construction.Tower
end
