import YangMills.Construction.ClusterExpansionOfAStep.SettingsOfAStep
import YangMills.Construction.RunningCouplingSlope.FamiliesOfExponents
import YangMills.Construction.SummableBoundsOfTheFlow.ReferenceTrajectoryOfTheFlow
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames TorusFields TorusLumps StepSettings ReferenceDensity LaplaceAsymptotics
namespace RunningCouplingSlope
variable {k : ℕ} (R : StepSetup) (n : ℕ) (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions)
def perturbedTop (τ : Fin k → ℝ) :
    (torusFrame R.params.side R.depth n).GaugeField (torusFrame R.params.side R.depth n).top :=
  readAtLevel (torusFrame R.params.side R.depth n) (torusFrame R.params.side R.depth n).top
    (perturb c X τ (trivialField n))
def chartEnergyAlongCurve
    (q : (Fin k → ℝ) × StepVariable (finiteCells (torusFrame R.params.side R.depth n))) : ℝ :=
  chartedEnergyAtMinimizer R.params.coupling R.anchorRadius (perturbedTop R n c X q.1) q.2 -
    chartedEnergyAtMinimizer R.params.coupling R.anchorRadius (perturbedTop R n c X q.1) 0
def exponentRemainderAlongCurve
    (q : (Fin k → ℝ) × StepVariable (finiteCells (torusFrame R.params.side R.depth n))) : ℝ :=
  stepExponent true R.params.coupling R.anchorRadius R.coupling 0 (localFamilyOfDensity R.density) 1
      (perturbedTop R n c X q.1) q.2 -
    R.coupling * chartEnergyAlongCurve R n c X q
def contourAverageNorm
    (b : (torusFrame R.params.side R.depth n).Site (torusFrame R.params.side R.depth n).top × Fin 4)
    (τ : Fin k → ℝ) : ℝ :=
  ‖contourAverage (fieldAboveFrame true R.params.coupling R.anchorRadius 0 (perturbedTop R n c X τ) 0) b‖
def haarGapSumAlongCurve (τ : Fin k → ℝ) : ℝ :=
  ∑ b ∈ innerBonds (finiteCells (torusFrame R.params.side R.depth n)) (torusFrame R.params.side R.depth n).top,
    haarGapSubLog (R.params.coupling * R.coupling * contourAverageNorm R n c X b τ)
end RunningCouplingSlope
end YangMills.Construction
end
