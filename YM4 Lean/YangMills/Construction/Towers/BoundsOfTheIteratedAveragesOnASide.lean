import YangMills.Construction.Towers.TheSettingOfTheRemainder
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.IteratedMeanBounds
structure FormConditions (L n k : ℕ) (a : Edge L n k 0 → Matrices.ComplexMatrix2) : Prop where
  mem_fields : ∀ j ≤ k, PeriodicLattice.complexBlockFieldAtLevel j (remainderGaugeField a) ∈
    fieldsIn L n k j PeriodicLattice.complexGaugeGroup
  mem_polydisc : ∀ j < k, ∀ c : Edge L n k (j + 1), c.IsPositivelyOriented →
    PeriodicLattice.complexBlockFieldAtLevel j (remainderGaugeField a) ∈
      nearIdentityPolydisc (polydiscRadius L) c
  norm_sub_one_le : ∀ j ≤ k, ∀ e : Edge L n k j,
    Matrices.ComplexMatrix2.operatorNorm
        (PeriodicLattice.complexBlockFieldAtLevel j (remainderGaugeField a) e - 1) ≤
      20 * meshAt L k j * (maxOperatorNorm a).toReal
  norm_sub_one_lt_half : ∀ j ≤ k, ∀ e : Edge L n k j,
    Matrices.ComplexMatrix2.operatorNorm
        (PeriodicLattice.complexBlockFieldAtLevel j (remainderGaugeField a) e - 1) <
      polydiscRadius L / 2
def RadiusIsAdmissible (L : ℕ) (ρ : ℝ) : Prop :=
  0 < ρ ∧ ρ ≤ 1 / 41 ∧ ∀ n : ℕ, 0 < n → ∀ k : ℕ, 1 ≤ k →
    ∀ a ∈ complexEdgeForms L n k 0, maxOperatorNorm a ≤ ENNReal.ofReal ρ → FormConditions L n k a
def smallRadius (L : ℕ) : ℝ := Classical.epsilon (RadiusIsAdmissible L)
def SmallRadiusAdmissible : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → RadiusIsAdmissible L (smallRadius L)
end YangMills.Construction.Tower.IteratedMeanBounds
end
