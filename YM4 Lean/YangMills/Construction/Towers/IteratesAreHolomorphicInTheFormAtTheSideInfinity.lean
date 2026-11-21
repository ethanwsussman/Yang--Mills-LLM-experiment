import YangMills.Construction.Towers.TheSettingOfTheRemainder
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.IterHolomorphy
def IteratesHolomorphicInForm : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ ρ : ℝ, 0 < ρ → ∀ k : ℕ, 1 ≤ k →
    (∀ a ∈ complexEdgeForms (meshAt L k 0), maxOperatorNorm a < ENNReal.ofReal ρ → ∀ j < k,
      complexIter L k j (remainderGaugeField a) ∈
          fieldsValuedIn L k j PeriodicLattice.complexGaugeGroup ∧
        ∀ b : Edge L k j,
          Matrices.ComplexMatrix2.operatorNorm (complexIter L k j (remainderGaugeField a) b - 1) <
            polydiscRadius L / 2) →
    ∀ j ≤ k, ∀ b : Edge L k j,
      ∃ (F : Finset (Edge L k 0)) (f : (F → Matrices.ComplexMatrix2) → Matrices.ComplexMatrix2),
        (∀ β : Module.Basis (Fin 3) ℂ Matrices.ComplexMatrix2.traceless,
          Matrices.GroupLieProduct.IsHolomorphicOnTraceless β
            Coordinates.ComplexCoordinates.matrixEquiv
            (Matrices.GroupLieProduct.supBall F ρ) f) ∧
        ∀ a ∈ complexEdgeForms (meshAt L k 0), maxOperatorNorm a < ENNReal.ofReal ρ →
          f (fun c => a c) = complexIter L k j (remainderGaugeField a) b
end YangMills.Construction.Tower.FullSpace.IterHolomorphy
end
