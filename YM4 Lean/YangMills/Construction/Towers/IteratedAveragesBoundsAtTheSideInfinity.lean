import YangMills.Construction.Towers.TheSettingOfTheRemainder
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.IterBounds
structure BoundsAtForm (L k : ℕ) (a : Edge L k 0 → Matrices.ComplexMatrix2) : Prop where
  mem_complexGroup : ∀ j ≤ k, complexIter L k j (remainderGaugeField a) ∈
    fieldsValuedIn L k j PeriodicLattice.complexGaugeGroup
  mem_polydisc : ∀ j < k, ∀ c : Edge L k (j + 1), c.IsPositivelyOriented →
    complexIter L k j (remainderGaugeField a) ∈
      nearIdentityPolydisc L k j (polydiscRadius L) c
  norm_sub_one_le : ∀ j ≤ k, ∀ b : Edge L k j,
    Matrices.ComplexMatrix2.operatorNorm (complexIter L k j (remainderGaugeField a) b - 1) ≤
      20 * meshAt L k j * (maxOperatorNorm a).toReal
  norm_sub_one_lt_half : ∀ j ≤ k, ∀ b : Edge L k j,
    Matrices.ComplexMatrix2.operatorNorm (complexIter L k j (remainderGaugeField a) b - 1) <
      polydiscRadius L / 2
def UniformIterBounds : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ 1 / 41 ∧
    ∀ k : ℕ, 1 ≤ k → ∀ a ∈ complexEdgeForms (meshAt L k 0),
      maxOperatorNorm a ≤ ENNReal.ofReal ρ → BoundsAtForm L k a
end YangMills.Construction.Tower.FullSpace.IterBounds
end
