import YangMills.Construction.ColdStepAtMirrorFrames.OtherTermsOfTheExponentForm
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ResponseInTheExpansion
open BlockAverages ColdStepAtMirrorFrames
def RemainderSlopeAt (T : StepParameters) : Prop :=
  ∃ M : ℝ, 0 ≤ M ∧ ∀ (t : ℕ) (x : ℝ) (f : LocalFamily) (F : BlockFrame) (V : F.GaugeField F.top)
    (w : F.Site F.depth → Fin 4 → imaginaryQuaternions) (ν : ℝ), T.coupling ≤ x →
    HasDecayingDerivs T.L t T.n₀ T.σ T.decayRate T.E T.energyRatio f →
    IsCubicTopTorus T.L t T.n₀ F → IsChartBasePoint T w V → 0 ≤ ν → ν ≤ 1 →
    ∀ η : StepVariable (finiteCells F), (∀ b, ‖η b‖ ≤ T.ballRadius) →
      DifferentiableAt ℝ (exponentMinusEnergy T.a x w f ν V) η ∧
      ∀ (b : ↥(chordBonds (finiteCells F))) (e : BondVector),
        |bondPartialDeriv (exponentMinusEnergy T.a x w f ν V) b η e| ≤ M * ‖e‖
def RemainderSlopeBound : Prop := EventuallyInParameters RemainderSlopeAt
end YangMills.Construction.ResponseInTheExpansion
end
