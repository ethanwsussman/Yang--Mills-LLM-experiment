import YangMills.Construction.ColdStepAtMirrorFrames.FormsOfTheTermsOfTheStep
import YangMills.Construction.ColdStepAtMirrorFrames.KernelsOfTheChartEnergy
import YangMills.Construction.ColdStepAtMirrorFrames.ParametersOfTheColdStep
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages
namespace YangMills.Construction.ColdStepAtMirrorFrames
variable {F : BlockFrame}
def ChartEnergyHessianRows (a lam κ s M : ℝ) (L : ℕ) (V : F.GaugeField F.top) : Prop :=
  ∃ K : ↥(chordBonds (finiteCells F)) → ↥(chordBonds (finiteCells F)) → ℝ,
    (∀ b b', K b b' = K b' b) ∧
    (∀ w, IsAdmissibleChartPoint L s w V → ContDiffAt ℝ 3 (chartedEnergyAt a w V) 0 ∧
      ∀ (b b' : ↥(chordBonds (finiteCells F))) (e e' : BondVector),
        |secondDerivAlong (chartedEnergyAt a w V) 0 (bondVariation b e) (bondVariation b' e')| ≤
          K b b' * ‖e‖ * ‖e'‖) ∧
    (∀ b, ∑ b', K b b' * (Real.exp (2 * κ * chordBondDist F b b') - 1) ≤ lam / 16) ∧
    ∀ b, ∑ b', K b b' ≤ M
def ChartEnergyHessianRowsForParameters (T : StepParameters) : Prop :=
  ∀ (F : BlockFrame) (V : F.GaugeField F.top), IsBlockTorus T.L F →
    ChartEnergyHessianRows T.a T.chainParams.lam T.κ T.chainParams.σA T.Ct T.L V
def ChartEnergyHessianRowsEventually : Prop :=
  EventuallyInParameters ChartEnergyHessianRowsForParameters
end YangMills.Construction.ColdStepAtMirrorFrames
end
