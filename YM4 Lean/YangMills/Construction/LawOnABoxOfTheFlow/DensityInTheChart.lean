import YangMills.Construction.LawOnABoxOfTheFlow.EventsOfABox
import YangMills.Construction.LawOnABoxOfTheFlow.HaarMeasureInTheChart
import YangMills.Construction.ResponseInTheExpansion.PairsAtALevel
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Quaternion
namespace YangMills.Construction.BoxGaussian
open TorusFields TorusLumps RenormalizationStepParameters StepSettings WeightedResponses ResponseInTheExpansion BlockAverages BoxEvents
variable {n : ℕ} [NeZero n]
def gaugeOrbitsOverEllipsoid (a : ℝ) (L k : ℕ) (o : TorusSite n) (R : ℕ) (c₀ : ℝ)
    (g : TorusSite n → UnitQuaternion) (A : TorusBond n → imaginaryQuaternions) (u : OuterField o R) :
    Set (InnerField o R) :=
  {w | ∃ (γ : TorusSite n → UnitQuaternion) (ζ : TorusBond n → imaginaryQuaternions),
    IsSupportedGauge o R γ ∧ ζ ∈ sliceEllipsoid a L k o R A c₀ ∧
    IsInChart (supBall o (2 * R)) A ζ (gaugeTransform (g * γ) (glueField u w))}
def chartDensityStatement : Prop :=
  HoldsAtAdmissibleParameters fun Tb y => ∀ κ₀ : ℝ, 1 / 27 ≤ κ₀ → κ₀ ≤ 1 / 21 → ∀ C₀ : ℝ, 0 < C₀ → ∃ K xs : ℝ,
    ∀ (T : StageTower (Tb.stepParameters y)) (β : ℝ) (k n : ℕ) [NeZero n] (o : TorusSite n) (x : ℝ) (R : ℕ)
      (g : TorusSite n → UnitQuaternion) (A : TorusBond n → imaginaryQuaternions) (u : OuterField o R)
      (Y : Finset (TorusSite n)) (ω : Y → (T.stage k).labels.Ω),
      IsBoxDatum Tb y T β κ₀ xs k n → x = flowCoupling (Tb.stepParameters y) β k → R = boxRadius κ₀ x →
      IsAxialSmall o R (boxScale x) A → Disjoint Y (supBall o (3 * R)) →
      (∃ w ∈ gaugeOrbitsOverEllipsoid Tb.coupling Tb.side k o R (C₀ * (R : ℝ) ^ 4 * boxScale x ^ 2) g A u,
        IsHullState (Tb.stepParameters y) (clusterRange x) (glueField u w) Y ∧
          0 < (T.stage k).labelWeight n (glueField u w) Y ω) →
      ∃ (c : ℝ) (wt : (TorusBond n → imaginaryQuaternions) → ℝ), 0 < c ∧ Measurable wt ∧
        (∀ ζ ∈ sliceEllipsoid Tb.coupling Tb.side k o R A (C₀ * (R : ℝ) ^ 4 * boxScale x ^ 2), 0 < wt ζ ∧
          |Real.log (wt ζ)| ≤ K * (R : ℝ) ^ 9 * x ^ (-(1 / 2 : ℝ)) * Real.log x ^ 3) ∧
        ∀ coord : InnerField o R → TorusBond n → imaginaryQuaternions,
          (∀ w ∈ gaugeOrbitsOverEllipsoid Tb.coupling Tb.side k o R (C₀ * (R : ℝ) ^ 4 * boxScale x ^ 2) g A u,
            ∃ γ : TorusSite n → UnitQuaternion,
            IsSupportedGauge o R γ ∧
              coord w ∈ sliceEllipsoid Tb.coupling Tb.side k o R A (C₀ * (R : ℝ) ^ 4 * boxScale x ^ 2) ∧
            IsInChart (supBall o (2 * R)) A (coord w) (gaugeTransform (g * γ) (glueField u w))) →
          ∀ Φ : (TorusBond n → imaginaryQuaternions) → ENNReal, Measurable Φ →
            ∫⁻ w in gaugeOrbitsOverEllipsoid Tb.coupling Tb.side k o R (C₀ * (R : ℝ) ^ 4 * boxScale x ^ 2) g A u,
                Φ (coord w) * ENNReal.ofReal ((T.stage k).labelWeight n (glueField u w) Y ω) ∂(innerHaar o R) =
              ENNReal.ofReal c * ∫⁻ ζ in sliceEllipsoid Tb.coupling Tb.side k o R A (C₀ * (R : ℝ) ^ 4 * boxScale x ^ 2),
                Φ ζ * ENNReal.ofReal (wt ζ) ∂(sliceGaussian Tb.coupling Tb.side k o R x A)
end YangMills.Construction.BoxGaussian
end
