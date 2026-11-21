import YangMills.Construction.LawByMomentsOfTheFlow.GaussianChainOfTheLaw
import YangMills.Construction.LawByMomentsOfTheFlow.WindowOfTheLaw
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.MomentLaw
variable {n : ℕ} [NeZero n]
open Classical in
def chartFreeCoords (R : StepSettings.StepSetup) (u : ℕ) (V : TorusFields.TorusField n)
    (k : ColdStepAtMirrorFrames.BondField (ChartBondIndex R.params.side u n)) :
    StepSettings.FreeCoords (coldSettingOver R V).free :=
  fun b => ∑ c : ChartBondIndex R.params.side u n,
    if (StepCosts.torusSiteInFrame (TorusFields.torusFrame R.params.side u n)
        (TorusFields.torusFrame R.params.side u n).depth b.1.1, b.1.2) = c.1 then k c else 0
def chartPotential (R : StepSettings.StepSetup) (u : ℕ) (V : TorusFields.TorusField n)
    (k : ColdStepAtMirrorFrames.BondField (ChartBondIndex R.params.side u n)) : ℝ :=
  (coldSettingOver R V).potential (chartFreeCoords R u V k)
end YangMills.Construction.MomentLaw
end
