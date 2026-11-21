import YangMills.Construction.RunningCouplingSlope.FamiliesThroughOne
import YangMills.Construction.RunningCouplingSlope.GaussianNumbersOfTheSoftChain
import Mathlib
set_option autoImplicit false
open Filter
open scoped Topology Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction
namespace RunningCouplingSlope
open Tower
def AnalyticFamilyTransportAndGauge : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k n : ℕ, 1 ≤ k → 0 < n →
    ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (X : E → ChainPoint L n k) (p₀ : E),
      IsAnalyticFamilyThroughUnit X p₀ →
      (∀ (ξ : LevelForms L n k) (j : ℕ), j ≤ k →
        (∀ e : Edge L n k j, AnalyticAt ℝ (fun p => tangentTransport (X p) ξ j e) p₀) ∧
        ∀ v : Vertex L n k j, AnalyticAt ℝ (fun p => chainDrift (X p) ξ j v) p₀) ∧
      ∀ᶠ p in 𝓝 p₀,
        IsShiftedGaugeMap (X p) (shiftedGaugeMap (X p)) ∧
        IsGaugeTransform (X p) (gaugeTransform (X p)) ∧
        ∃ T : LevelForms L n k →ₗ[ℝ] vertexFunctionSpace L n k 0, ∀ ξ,
          (T ξ : Vertex L n k 0 → Matrices.ComplexMatrix2) = gaugeCorrection (X p) ξ
end RunningCouplingSlope
end YangMills.Construction
end
