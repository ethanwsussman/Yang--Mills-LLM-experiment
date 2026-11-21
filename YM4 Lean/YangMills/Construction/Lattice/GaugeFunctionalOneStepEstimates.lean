import YangMills.Construction.Lattice.GaugeSizeAnglesAndBlockMean
import YangMills.Construction.Lattice.SiteLogarithm
import YangMills.Construction.Lattice.StraightenedIterates
import Mathlib
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.PeriodicLattice
variable {L m K n : ℕ}
structure RecursionStepBounds (κ : ℝ) (W₀ : BondAtLevel L m K n → Matrices.ComplexMatrix2)
    (a : LieBondFunction L m (levelDepth K n)) (r : SiteAtLevel L m K n → Matrices.ComplexMatrix2) :
    Prop where
  defined : GaugeRecursionStepDefined W₀ a r
  compact_valued : LieBondFunction.IsCompactValued (transformedBondFunction W₀ a r)
  gauge_map : IsGaugeMap compactGaugeGroup (gaugeRecursionStep W₀ a r)
  sup_le : supOperatorNorm (transformedBondFunction W₀ a r) ≤ supOperatorNorm a + gaugeMaxAngle W₀ r
  sup_lt : supOperatorNorm a + gaugeMaxAngle W₀ r < stepBondRadius L
  dist_le : gaugeDistFromOne (gaugeRecursionStep W₀ a r) ≤
    (1 + κ * maxCurvature W₀) * gaugeDistFromOne r + κ * gaugeMaxAngle W₀ r
  angle_le : gaugeMaxAngle (levelAverage .centred n W₀) (gaugeRecursionStep W₀ a r) ≤
    L * gaugeMaxAngle W₀ r + κ * (maxCurvature W₀ * gaugeDistFromOne r + gaugeMaxAngle W₀ r ^ 2 +
      supOperatorNorm a * gaugeMaxAngle W₀ r)
  log_le : supOfOperatorNorms (fun y : SiteAtLevel L m K (n + 1) =>
      siteLog (gaugeRecursionStep W₀ a r) y -
        covariantBlockAverage W₀ (siteLog r) y) ≤
    κ * (gaugeDistFromOne r + supOperatorNorm a) *
      (gaugeMaxAngle W₀ r + maxCurvature W₀ * gaugeDistFromOne r)
structure IsRecursionStepConstants (L : ℕ) (g κ s₀ : ℝ) : Prop where
  angle_pos : 0 < g
  one_le : 1 ≤ κ
  holds : ∀ m K n : ℕ, 0 < m → n < K →
    ∀ W₀ ∈ gaugeFieldsAtLevel L m K n, maxCurvature W₀ ≤ stepCurvatureBound L →
      ∀ a : LieBondFunction L m (levelDepth K n), LieBondFunction.IsCompactValued a →
        supOperatorNorm a ≤ stepBondRadius L / 16 →
        ∀ r : SiteAtLevel L m K n → Matrices.ComplexMatrix2, IsGaugeMap compactGaugeGroup r →
          gaugeMaxAngle W₀ r ≤ g → gaugeDistFromOne r ≤ s₀ → RecursionStepBounds κ W₀ a r
def IsRecursionStepRadius (s₀ : ℝ) : Prop :=
  0 < s₀ ∧ s₀ ≤ 1 / 64 ∧
    ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L →
      ∃ g κ : ℝ, IsRecursionStepConstants L g κ s₀
def recursionStepRadius : ℝ := Classical.epsilon IsRecursionStepRadius
def recursionStepConstants (L : ℕ) : ℝ × ℝ :=
  Classical.epsilon fun t => IsRecursionStepConstants L t.1 t.2 recursionStepRadius
def recursionStepAngle (L : ℕ) : ℝ := (recursionStepConstants L).1
def recursionStepConstant (L : ℕ) : ℝ := (recursionStepConstants L).2
end YangMills.Construction.PeriodicLattice
