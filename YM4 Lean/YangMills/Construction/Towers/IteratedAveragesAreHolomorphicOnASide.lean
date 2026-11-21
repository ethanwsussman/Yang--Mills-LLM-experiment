import YangMills.Construction.Towers.TheSettingOfTheRemainder
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.Tower.IteratedMeansHolomorphic
def IteratedMeansHolomorphicOnSide : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ ρ : ℝ, 0 < ρ → ∀ n k : ℕ, 0 < n → 1 ≤ k →
    (∀ a ∈ complexEdgeForms L n k 0, maxOperatorNorm a < ENNReal.ofReal ρ → ∀ j < k,
      PeriodicLattice.complexBlockFieldAtLevel j (remainderGaugeField a) ∈
          fieldsIn L n k j PeriodicLattice.complexGaugeGroup ∧
        ∀ b : Edge L n k j,
          Matrices.ComplexMatrix2.operatorNorm
              (PeriodicLattice.complexBlockFieldAtLevel j (remainderGaugeField a) b - 1) <
            polydiscRadius L / 2) →
    ∀ j ≤ k, ∀ c : Edge L n k j,
      ∃ (F : Finset (Edge L n k 0)) (f : (F → Matrices.ComplexMatrix2) → Matrices.ComplexMatrix2),
        (∀ e : Module.Basis (Fin 3) ℂ Matrices.ComplexMatrix2.traceless,
          Matrices.GroupLieProduct.IsHolomorphicOnTraceless e
            Coordinates.ComplexCoordinates.matrixEquiv
            (Matrices.GroupLieProduct.supBall F ρ) f) ∧
        ∀ a ∈ complexEdgeForms L n k 0, maxOperatorNorm a < ENNReal.ofReal ρ →
          f (fun b => a b) = PeriodicLattice.complexBlockFieldAtLevel j (remainderGaugeField a) c
end YangMills.Construction.Tower.IteratedMeansHolomorphic
end
