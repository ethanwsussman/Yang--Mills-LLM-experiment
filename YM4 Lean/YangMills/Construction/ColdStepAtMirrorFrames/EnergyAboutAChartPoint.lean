import YangMills.Construction.ColdStepAtMirrorFrames.ChartPointsNearABox
import YangMills.Construction.ColdStepAtMirrorFrames.FormsOfTheTermsOfTheStep
import YangMills.Construction.ColdStepAtMirrorFrames.KernelsOfTheChartEnergy
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
open YangMills.Construction.BlockAverages
namespace YangMills.Construction
namespace ColdStepAtMirrorFrames
def ChartEnergyDerivBounds : Prop :=
  ∀ (a : ℝ) (L : ℕ) (c : ColdChainParameters), 1 ≤ a → Odd L → 2 ^ 40 ≤ L → c.Admissible a L →
    ∃ C : ℝ, 0 < C ∧ ∀ (F : BlockFrame) (w : F.Site F.depth → Fin 4 → imaginaryQuaternions)
      (η : StepVariable (finiteCells F)) (V : F.GaugeField F.top),
      IsBlockTorus L F → IsAdmissibleChartPoint L c.σA (shiftCoordinates w η) V →
      ContDiffAt ℝ 3 (chartedEnergyAt a w V) η ∧
      (∀ (b : ↥(chordBonds (finiteCells F))) (e : BondVector),
        chartedSlope a (shiftCoordinates w η) V b.1 (toImaginary e) =
          fderiv ℝ (chartedEnergyAt a w V) η (bondVariation b e)) ∧
      (∀ (b b' : ↥(chordBonds (finiteCells F))) (e e' : BondVector),
        |secondDerivAlong (chartedEnergyAt a w V) η (bondVariation b e) (bondVariation b' e')| ≤
          C * Real.exp (-(c.δ₁ * chordBondDist F b b')) * ‖e‖ * ‖e'‖) ∧
      ∀ (b b' b'' : ↥(chordBonds (finiteCells F))) (e e' e'' : BondVector),
        |thirdDerivAlong (chartedEnergyAt a w V) η (bondVariation b e) (bondVariation b' e')
          (bondVariation b'' e'')| ≤ C * ‖e‖ * ‖e'‖ * ‖e''‖
end ColdStepAtMirrorFrames
end YangMills.Construction
end
