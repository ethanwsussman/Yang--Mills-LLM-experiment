import YangMills.Construction.ClusterExpansionOfAStep.ColdSettingOfAStep
import YangMills.Construction.RunningCouplingSlope.LogarithmOfTheChain
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
def minimalActionTotal (a : ℝ) (L t : ℕ) : SlopeCoefficient.GaugeTotal := fun n V =>
  if h : n = 0 then 0 else
    haveI : NeZero n := ⟨h⟩
    TorusFields.actionAtLevel a L t Finset.univ V
def centeredDensityTotal (f : TorusLumps.LocalDensity) : SlopeCoefficient.GaugeTotal := fun n V =>
  if h : n = 0 then 0 else
    haveI : NeZero n := ⟨h⟩
    ∑ y, TorusLumps.centered f n y V
def atMinimizer (a ρ : ℝ) (L t : ℕ) (H : SlopeCoefficient.GaugeTotal) : SlopeCoefficient.GaugeTotal :=
  fun n V => H (n * L) (SlopeCoefficient.minimizerOnFinerTorus a ρ L t n V)
def goodFieldLogIntegral (S : StepSettings.StepSetup) : SlopeCoefficient.GaugeTotal := fun n V =>
  if h : n = 0 then 0 else
    haveI : NeZero n := ⟨h⟩
    Real.log (StepSettings.coldImageIntegral S V) -
      Real.log (StepSettings.coldImageIntegral S (TorusFields.trivialField n))
end YangMills.Construction.RunningCouplingSlope
end
