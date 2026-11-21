import YangMills.Construction.ColdStepAtMirrorFrames.OtherTermsOfTheExponentForm
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ColdStepAtMirrorFrames
open YangMills.Construction.BlockAverages
def ConvexAboveChartPointAt (T : StepParameters) : Prop :=
  ∀ (t : ℕ) (x : ℝ) (f : LocalFamily) (F : BlockFrame) (V : F.GaugeField F.top)
    (w : F.Site F.depth → Fin 4 → imaginaryQuaternions) (ν : ℝ), T.coupling ≤ x →
    HasDecayingDerivs T.L t T.n₀ T.σ T.decayRate T.E T.energyRatio f → IsCubicTopTorus T.L t T.n₀ F →
    IsSmallCurvature (5 / 4 * T.σ) V → IsChartBasePoint T w V →
    (∀ (b : ↥(chordBonds (finiteCells F))) (e : BondVector), ‖e‖ = 1 →
      x * |bondPartialDeriv (chartedEnergyAt T.a w V) b 0 e| ≤ 1) → 0 ≤ ν → ν ≤ 1 →
    IsConvexClassMember T.ballRadius (x * T.chainParams.lam / 4) T.κ (chordBondDist F)
      (exponentInChart T.a x w f ν V) ∧
    ∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ < T.ballRadius) →
      ∀ (b : ↥(chordBonds (finiteCells F))) (e : BondVector),
        |bondPartialDeriv (exponentInChart T.a x w f ν V) b η e| ≤
          (T.Ct * T.ballRadius + T.chainParams.lam + 1) * x * ‖e‖
def ConvexAboveChartPoint : Prop := EventuallyInParameters ConvexAboveChartPointAt
end YangMills.Construction.ColdStepAtMirrorFrames
end
