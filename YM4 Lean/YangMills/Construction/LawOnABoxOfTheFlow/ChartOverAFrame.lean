import YangMills.Construction.LawOnABoxOfTheFlow.ChartOfABox
import YangMills.Construction.LawOnABoxOfTheFlow.DensityInTheChart
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Quaternion
namespace YangMills.Construction.BoxGaussian
open TorusFields TorusLumps WeightedResponses ResponseInTheExpansion RenormalizationStepParameters BlockAverages BoxEvents
def chartOverFrameStatement : Prop :=
  HoldsAtAdmissibleParameters fun Tb y => ∀ κ₀ : ℝ, 1 / 27 ≤ κ₀ → κ₀ ≤ 1 / 21 → ∃ C₁ : ℝ, ∀ C₀ : ℝ, C₁ ≤ C₀ →
    ∃ C xs : ℝ,
    ∀ (T : StageTower (Tb.stepParameters y)) (β : ℝ) (k n : ℕ) [NeZero n] (o : TorusSite n) (x : ℝ) (R : ℕ)
      (G₀ : Set (OuterData T k o R)) (g : OuterData T k o R → TorusSite n → UnitQuaternion)
      (A : OuterData T k o R → TorusBond n → imaginaryQuaternions)
      (M : OuterData T k o R → TorusPlaquette n → imaginaryQuaternions),
      IsBoxDatum Tb y T β κ₀ xs k n → x = flowCoupling (Tb.stepParameters y) β k → R = boxRadius κ₀ x →
      16 * R < n → IsBlockTorusSide (Tb.stepParameters y) n →
      MeasurableSet G₀ → Measurable g → Measurable A → Measurable M →
      (∀ q ∈ G₀, IsAxialSmall o R (boxScale x) (A q)) →
      (∀ q ∈ G₀, Disjoint q.2.1 (supBall o (3 * R))) →
      ∃ c : BoxChart T k o R, c.axialGauge = g ∧ c.background = A ∧ c.meanCurl = M ∧ c.goodOuter ⊆ G₀ ∧
        (∀ p, p ∈ c.orbitSet ↔ p.1 ∈ c.goodOuter ∧
          p.2 ∈ gaugeOrbitsOverEllipsoid Tb.coupling Tb.side k o R (C₀ * (R : ℝ) ^ 4 * boxScale x ^ 2)
            (g p.1) (A p.1) p.1.1) ∧
        c.IsMeasurable ∧ c.IsInGauge C (boxScale x) (C₀ * (R : ℝ) ^ 4 * boxScale x ^ 2) ∧
        c.HasLaw (markedSampleLaw T β k n) x (C₀ * (R : ℝ) ^ 4 * boxScale x ^ 2)
          (C * (R : ℝ) ^ 9 * x ^ (-(1 / 2 : ℝ)) * Real.log x ^ 3) ∧
        (∀ q, MeasurableSet (sliceEllipsoid Tb.coupling Tb.side k o R (A q) (C₀ * (R : ℝ) ^ 4 * boxScale x ^ 2))) ∧
        (Measurable fun p : OuterData T k o R × InnerField o R => c.coord p.1 p.2) ∧
        (∀ q ∈ c.goodOuter, IsProbabilityMeasure (c.coordLaw x (C₀ * (R : ℝ) ^ 4 * boxScale x ^ 2) q)) ∧
        (∀ E : Set (OuterData T k o R × (TorusBond n → imaginaryQuaternions)), MeasurableSet E →
          Measurable fun q : c.goodOuter =>
            c.coordLaw x (C₀ * (R : ℝ) ^ 4 * boxScale x ^ 2) q (Prod.mk q.1 ⁻¹' E)) ∧
        markedSampleLaw T β k n {u | outerData T k o R (stageState T k n u) ∈ G₀ \ c.goodOuter ∧
          restrictInner o R (stageState T k n u).1 ∈
            gaugeOrbitsOverEllipsoid Tb.coupling Tb.side k o R (C₀ * (R : ℝ) ^ 4 * boxScale x ^ 2)
              (g (outerData T k o R (stageState T k n u))) (A (outerData T k o R (stageState T k n u)))
              (outerData T k o R (stageState T k n u)).1} = 0
end YangMills.Construction.BoxGaussian
end
