import YangMills.Construction.Towers.DataOfAChangeOfTheGaugeFixing
import YangMills.Construction.Towers.TheFunctionalInTheBackgroundGauge
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower
def GaussianLogViaTwoSaddleDets : Prop :=
  ∀ L n k : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < n → 1 ≤ k →
    ∃ C : ℝ, ∀ (Q Q' : edgeFormSpace L n k 0 →ₗ[ℝ] edgeFormSpace L n k k)
      (T : QuadraticForm ℝ (LinearMap.ker Q)) (X : edgeFormSpace L n k 0 →ₗ[ℝ] edgeFormSpace L n k 0)
      (r' : vertexFunctionSpace L n k 0 →ₗ[ℝ] vertexFunctionSpace L n k k)
      (Y : vertexFunctionSpace L n k 0 →ₗ[ℝ] vertexFunctionSpace L n k 0),
      Nonempty (GaugeFixingTransferData L n k Q Q' T X r' Y) →
        saddleDetOnEdgeForms X Q' ≠ 0 ∧ saddleDetOnVertexFunctions Y r' ≠ 0 ∧
          Real.log (constrainedGaussianOnEdgeForms Q T) =
            C - (1 / 2) * Real.log |saddleDetOnEdgeForms X Q'| +
              Real.log |saddleDetOnVertexFunctions Y r'|
end YangMills.Construction.Tower
end
