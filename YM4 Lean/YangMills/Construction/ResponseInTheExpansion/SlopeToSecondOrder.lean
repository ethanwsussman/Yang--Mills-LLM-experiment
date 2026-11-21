import YangMills.Construction.ColdStepAtMirrorFrames.ChartPointsNearABox
import YangMills.Construction.ColdStepAtMirrorFrames.FormsOfTheTermsOfTheStep
import YangMills.Construction.ColdStepAtMirrorFrames.KernelsOfTheChartEnergy
import YangMills.Construction.ColdStepAtMirrorFrames.ParametersOfTheColdStep
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames
namespace WeightedResponses
def EnergySlopeSecondOrderAt (T : StepParameters) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (F : BlockFrame) (V : F.GaugeField F.top) (w : F.Site F.depth → Fin 4 → imaginaryQuaternions)
    (η : StepVariable (finiteCells F)), IsBlockTorus T.L F →
    (∀ s : ℝ, 0 ≤ s → s ≤ 1 → IsAdmissibleChartPoint T.L T.chainParams.σA (shiftCoordinates w (s • η)) V) →
    ∀ (b : ↥(chordBonds (finiteCells F))) (e : BondVector), ‖e‖ = 1 →
      |fderiv ℝ (chartedEnergyAt T.a w V) η (bondVariation b e) - fderiv ℝ (chartedEnergyAt T.a w V) 0 (bondVariation b e) -
          secondDerivAlong (chartedEnergyAt T.a w V) 0 (bondVariation b e) η| ≤
        C * (∑ b', Real.exp (-(T.chainParams.δ₁ / 2 * chordBondDist F b b')) * ‖η b'‖) ^ 2
def EnergySlopeSecondOrder : Prop := EventuallyInParameters EnergySlopeSecondOrderAt
end WeightedResponses
end YangMills.Construction
end
