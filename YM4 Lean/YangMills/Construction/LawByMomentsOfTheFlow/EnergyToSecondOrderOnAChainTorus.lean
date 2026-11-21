import YangMills.Construction.ColdStepAtMirrorFrames.ChartPointsNearABox
import YangMills.Construction.ColdStepAtMirrorFrames.FormsOfTheTermsOfTheStep
import YangMills.Construction.ColdStepAtMirrorFrames.KernelsOfTheChartEnergy
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages YangMills.Construction.ColdStepAtMirrorFrames
namespace YangMills.Construction.MomentLaw
def chartEnergySecondOrderStatement : Prop :=
  ∀ (a : ℝ) (L : ℕ) (c : ColdChainParameters), 1 ≤ a → Odd L → 2 ^ 40 ≤ L → c.Admissible a L → ∃ C : ℝ, 0 < C ∧
    ∀ (F : BlockFrame) (V : F.GaugeField F.top) (w : F.Site F.depth → Fin 4 → imaginaryQuaternions), IsBlockTorus L F →
      (∀ ζ : StepVariable (finiteCells F), IsAdmissibleChartPoint L c.σA (shiftCoordinates w ζ) V →
        ContDiffAt ℝ 3 (chartedEnergyAt a w V) ζ) ∧
      ∀ η : StepVariable (finiteCells F),
        (∀ s : ℝ, 0 ≤ s → s ≤ 1 → IsAdmissibleChartPoint L c.σA (shiftCoordinates w (s • η)) V) →
        ∀ (b : ↥(chordBonds (finiteCells F))) (e : BondVector), ‖e‖ = 1 →
          |fderiv ℝ (chartedEnergyAt a w V) η (bondVariation b e) - fderiv ℝ (chartedEnergyAt a w V) 0 (bondVariation b e) -
              secondDerivAlong (chartedEnergyAt a w V) 0 (bondVariation b e) η| ≤
            C * (∑ b', Real.exp (-(c.δ₁ / 2 * chordBondDist F b b')) * ‖η b'‖) ^ 2
end YangMills.Construction.MomentLaw
end
