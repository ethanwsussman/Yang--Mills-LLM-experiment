import YangMills.Construction.FourPointCondition.CumulantOfAnObservable
import YangMills.Construction.ResponseInTheExpansion.ConnectedFunctionsOfTheExpansion
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.FourPointCondition
def fineLevelQuadraticApproxAt (Tb : RenormalizationStepParameters.ParameterAssignment) (y : ℝ) : Prop :=
  (Tb.stepParameters y).Admissible ∧ ∀ vt : ℝ, 0 < vt → vt ≤ 1 → ∃ (Cr : ℕ → ℝ) (C x₀ : ℝ),
    ∀ (q : ℕ) (β : ℝ) (m : ℕ) (n : ℝ), (q = 1 ∨ q = 3) → x₀ ≤ β →
      Real.exp (Real.log β ^ 3) ≤ 2 * ((Tb.stepParameters y).side : ℝ) ^ m → 1 ≤ n → n ≤ β ^ ((1 : ℝ) / 90) →
      ∀ f : Fin (q + 1) → PeriodicLattice.FourTorus (Tb.stepParameters y).side m → ℝ,
        ResponseInTheExpansion.IsSeparatedTestTuple (Tb.stepParameters y) m n vt f →
        ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (_ : IsProbabilityMeasure μ)
          (Φ : Ω → TorusFields.TorusField
            (WeightedResponses.fineSide (Tb.stepParameters y).side 0 (2 * (Tb.stepParameters y).side ^ m)))
          (I : Type) (_ : Fintype I)
          (G : Ω → I → BlockAverages.imaginaryQuaternions) (A B : Set Ω) (κ : Fin (q + 1) → Matrix I I ℝ)
          (Tc : Matrix I I ℝ) (Bg : ℝ),
          Measurable Φ ∧ Measure.map Φ μ = WeightedResponses.wilsonLaw β
            (WeightedResponses.fineSide (Tb.stepParameters y).side 0 (2 * (Tb.stepParameters y).side ^ m)) ∧
          QuadraticFormApproximation μ
            (fun i ω => WeightedResponses.curvatureObservable
              (WeightedResponses.testWeight (Tb.stepParameters y).side 0 m (f i)) (Φ ω))
            G A B κ Tc 0 β n C 40 Bg Cr ∧
          (∀ i ω, |WeightedResponses.curvatureObservable
            (WeightedResponses.testWeight (Tb.stepParameters y).side 0 m (f i)) (Φ ω)| ≤ C * n ^ 4) ∧
          |ResponseInTheExpansion.cyclicTraceSum κ Tc - ResponseInTheExpansion.gaussianCumulantLimit
            (PeriodicLattice.torusSide (Tb.stepParameters y).side m) f| ≤
            C * (β ^ (-(1 / 100 : ℝ)) + 1 / n)
def fineLevelQuadraticApproxStatement : Prop :=
  ResponseInTheExpansion.HoldsOnParameterFamilies fineLevelQuadraticApproxAt
end YangMills.Construction.FourPointCondition
end
