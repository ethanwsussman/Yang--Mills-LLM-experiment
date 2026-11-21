import YangMills.Construction.Parameters.AbsoluteNumberOfTheAgeAnalysis
import YangMills.Construction.Parameters.CeilingsOfTheExpansionOnTheCutoffRadius
import YangMills.Construction.Parameters.TiesCeilingsOnGamma
import YangMills.Construction.Parameters.TiesConstantsBehindM
import YangMills.Construction.Parameters.TiesCubeFloors
import YangMills.Construction.Parameters.TiesKernelsAndRates
import YangMills.Construction.Parameters.TiesOfTheFloorsTheWalksTheRoomAndTheMembers
import YangMills.Construction.Parameters.TiesToTheAverageAndToCriticalConfigurations
import YangMills.Construction.Parameters.TiesToTheCountTheExtractionAndThePropagators
import YangMills.Construction.Parameters.TiesToTheNumbersOfTheConstruction
import YangMills.Construction.Parameters.TiesToTheOneLoopLawAndToTheFourShapes
import YangMills.Construction.Parameters.TiesToThePublishedTheorems
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ParameterChoice
structure AdmissibleConstants (T : DerivedConstants) (N : ExternalConstants) : Prop where
  ranges : AdmissibleConstantFamily T N
  averageAndCritical : ∀ L 𝔐 R₁ : ℕ, BlockingFactorAdmissible L →
    IsPositivePowerOf L 𝔐 → IsPositivePowerOf L R₁ →
    N.productFloor L ≤ (R₁ : ℝ) * (𝔐 : ℝ) → AverageAndCriticalTies T N L 𝔐 R₁
  published : MatchesPublishedConstants T N
  oneLoopAndShapes : TiedToOneLoopLawAndShapes T
  combined : MatchesCombinedConstants N
  propagatorCounting : PropagatorCountingTies N
  anchorPrecision : AnchorPrecisionIsAgingPrecision N
  cutoffBounds : CutoffBoundsIncluded T N
  thresholds : MatchesThresholds N
  couplingCeiling : CouplingCeilingTie N
  potentialConstant : PotentialConstantTie N
  coreLowerBound : CoreLowerBoundTie T N
  compatibility : CompatibilityConditions T N
  cubeConst_pos : 0 < T.o
  flowConstB_pos : 0 < T.flowConstB
end YangMills.Construction.ParameterChoice
end
