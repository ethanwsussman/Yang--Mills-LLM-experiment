import YangMills.Construction.LawOnABoxOfTheFlow.DensityInTheChart
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Quaternion
namespace YangMills.Construction.BoxGaussian
open TorusFields TorusLumps WeightedResponses ResponseInTheExpansion RenormalizationStepParameters BlockAverages
variable {n : ℕ} [NeZero n]
abbrev ChartPoint (o : TorusSite n) (R : ℕ) : Type :=
  (TorusBond n → imaginaryQuaternions) × (TorusSite n → UnitQuaternion) × OuterField o R × InnerField o R
def chartPointSet (a : ℝ) (L k : ℕ) (o : TorusSite n) (R : ℕ) (c₀ δ : ℝ) : Set (ChartPoint o R) :=
  {p | IsAxialSmall o R δ p.1 ∧ p.2.2.2 ∈ gaugeOrbitsOverEllipsoid a L k o R c₀ p.2.1 p.1 p.2.2.1}
def measurableChartStatement : Prop :=
  ∀ Tb : ParameterAssignment, Tb.Admissible → ∀ κ₀ : ℝ, 1 / 27 ≤ κ₀ → κ₀ ≤ 1 / 21 → ∀ C₀ : ℝ, 0 < C₀ → ∃ xs : ℝ,
    ∀ (x : ℝ) (R k n : ℕ) [NeZero n] (o : TorusSite n),
      xs ≤ x → R = boxRadius κ₀ x → 16 * R < n →
      MeasurableSet (chartPointSet Tb.coupling Tb.side k o R (C₀ * (R : ℝ) ^ 4 * boxScale x ^ 2) (boxScale x)) ∧
      ∃ coord : ChartPoint o R → TorusBond n → imaginaryQuaternions, Measurable coord ∧
        ∀ p ∈ chartPointSet Tb.coupling Tb.side k o R (C₀ * (R : ℝ) ^ 4 * boxScale x ^ 2) (boxScale x),
          ∃ γ : TorusSite n → UnitQuaternion, IsSupportedGauge o R γ ∧
            coord p ∈ sliceEllipsoid Tb.coupling Tb.side k o R p.1 (C₀ * (R : ℝ) ^ 4 * boxScale x ^ 2) ∧
            IsInChart (supBall o (2 * R)) p.1 (coord p)
              (gaugeTransform (p.2.1 * γ) (glueField p.2.2.1 p.2.2.2))
end YangMills.Construction.BoxGaussian
end
