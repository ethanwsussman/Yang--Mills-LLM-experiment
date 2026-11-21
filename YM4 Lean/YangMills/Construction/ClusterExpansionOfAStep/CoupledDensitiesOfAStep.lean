import YangMills.Construction.ClusterExpansionOfAStep.ColdExpansionOfFourDensities
import YangMills.Construction.ClusterExpansionOfAStep.ColdIntegralOfAStep
import YangMills.Construction.ClusterExpansionOfAStep.MarkedIntegralsOfAStep
import YangMills.Construction.ClusterExpansionOfAStep.SharesAreACurvatureFamily
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace StepSettings
open TorusLumps ShareFamilies
variable (S : StepSetup)
def StepSetup.imageDensity (lam : ℝ) : LocalDensity :=
  sumOfFour (coldInteractionDensity S lam) (coldExpansionDensity S) (coldFrameDensity S) S.blockDensity
def StepSetup.couplingShift (lam : ℝ) : ℝ := curvatureCoefficient (S.imageDensity lam)
def StepSetup.shiftedCoupling (lam : ℝ) : ℝ := S.coupling - S.couplingShift lam
def StepSetup.renormalizedDensity (lam : ℝ) : LocalDensity :=
  densitiesLessMultiple (coldInteractionDensity S lam) (coldExpansionDensity S) (coldFrameDensity S) S.blockDensity
    (levelShareFamily S.params.coupling S.params.side (S.depth + 1)) (S.couplingShift lam)
end StepSettings
end YangMills.Construction
end
