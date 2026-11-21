import YangMills.Construction.ClusterExpansionOfAStep.ColdSettingOfAStep
import YangMills.Construction.ColdStepAtMirrorFrames.DensityHypothesesAtParameters
import YangMills.Construction.ColdStepAtMirrorFrames.FamiliesOnFramesAndTori
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.StepSettings
open BlockAverages ColdStepAtMirrorFrames TorusFields TorusLumps StepCosts
variable (R : StepSetup)
def chartBondCount (L : ℕ) : ℕ := 3 * L ^ 4 + 1
def StepSetup.coldBlockConstant (lam : ℝ) : ℝ :=
  (R.gaussianLogMass lam + Real.log (haarRadialDensity 0)) * chartBondCount R.params.side +
    4 * logPartitionGap (R.params.coupling * R.coupling)
def coldLocalDensity (lam : ℝ) : LocalDensity := fun n Y V =>
  if h : n = 0 then 0 else
    haveI : NeZero n := ⟨h⟩
    (coldChartSetting R V).blockActivity lam Y +
      R.coupling * levelShare R.params.coupling R.params.side (R.depth + 1) Finset.univ Y V -
      R.coldBlockConstant lam
def coldInteractionDensity (lam : ℝ) : LocalDensity :=
  densityOfTopFamily R.params.side R.depth
    (interactionFamily R.params.coupling R.anchorRadius R.ballRadius lam R.coupling R.frameReach R.barrierFn
      (localFamilyOfDensity R.density))
def coldExpansionDensity : LocalDensity :=
  densityOfTopFamily R.params.side R.depth
    (expansionFamily R.params.coupling R.anchorRadius R.ballRadius R.coupling R.frameReach R.barrierFn
      (localFamilyOfDensity R.density))
def coldFrameDensity : LocalDensity :=
  densityOfTopFamily R.params.side R.depth (frameFamily R.params.coupling R.anchorRadius R.coupling R.frameReach)
def coldStepIntegral (n : ℕ) (V : TorusField n) : ℝ :=
  stepIntegral R.params.coupling R.anchorRadius R.ballRadius R.coupling R.frameReach R.barrierFn
    (localFamilyOfDensity R.density) (finiteCells (torusFrame R.params.side R.depth n))
    (readAtLevel (torusFrame R.params.side R.depth n) (torusFrame R.params.side R.depth n).top V)
end YangMills.Construction.StepSettings
end
