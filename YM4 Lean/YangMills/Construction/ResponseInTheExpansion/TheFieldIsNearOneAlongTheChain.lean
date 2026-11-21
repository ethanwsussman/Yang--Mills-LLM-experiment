import YangMills.Construction.ResponseInTheExpansion.LocalSizesOfTheChain
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ResponseInTheExpansion
open YangMills.Construction.BlockAverages YangMills.Construction.TorusLumps YangMills.Construction.TorusFields
open YangMills.Construction.RenormalizationStepParameters YangMills.Construction.WeightedResponses
open Classical
open MeasureTheory
variable (Tb : ParameterAssignment) (y : ℝ)
def nearIdentityAlongChainAt : Prop :=
  ∀ p : ℝ, ∃ C x₀ : ℝ, ∀ (T : StageTower (ParameterAssignment.stepParameters Tb y)) (β : ℝ) (k N : ℕ) [NeZero N] (nn : ℝ)
    (o : TorusSite (fineSide (ParameterAssignment.stepParameters Tb y).side (localChainDepth (ParameterAssignment.stepParameters Tb y) β k)
      (fineSide (ParameterAssignment.stepParameters Tb y).side (localChainDepth (ParameterAssignment.stepParameters Tb y) β k) N))),
    IsLocalChainAbove Tb y T β k N nn x₀ → (ParameterAssignment.stepParameters Tb y).side ∣ N →
    Measure.real (markedSampleLaw T β (k + localChainDepth (ParameterAssignment.stepParameters Tb y) β k +
        localChainDepth (ParameterAssignment.stepParameters Tb y) β k) N)
      {u | IsLocalEvent T k (localChainDepth (ParameterAssignment.stepParameters Tb y) β k)
          (localBlockSide (ParameterAssignment.stepParameters Tb y) β k) N u o ∧
        ¬ IsGaugeSmallAlong T k nn (localLogScale (ParameterAssignment.stepParameters Tb y) β k)
          (flowCouplings (ParameterAssignment.stepParameters Tb y) β k ^ (-(1 / 4 : ℝ)))
          (localChainDepth (ParameterAssignment.stepParameters Tb y) β k)
          (fineSide (ParameterAssignment.stepParameters Tb y).side (localChainDepth (ParameterAssignment.stepParameters Tb y) β k) N)
          (sampleBelow (ParameterAssignment.stepParameters Tb y) (k + localChainDepth (ParameterAssignment.stepParameters Tb y) β k)
            (localChainDepth (ParameterAssignment.stepParameters Tb y) β k) N u) o
          (axialGaugeAt (ParameterAssignment.stepParameters Tb y)
            (topField (ParameterAssignment.stepParameters Tb y) (k + localChainDepth (ParameterAssignment.stepParameters Tb y) β k)
              (fineSide (ParameterAssignment.stepParameters Tb y).side (localChainDepth (ParameterAssignment.stepParameters Tb y) β k) N)
              (sampleBelow (ParameterAssignment.stepParameters Tb y) (k + localChainDepth (ParameterAssignment.stepParameters Tb y) β k)
                (localChainDepth (ParameterAssignment.stepParameters Tb y) β k) N u))
            (siteAbove (ParameterAssignment.stepParameters Tb y).side (localChainDepth (ParameterAssignment.stepParameters Tb y) β k)
              (fineSide (ParameterAssignment.stepParameters Tb y).side (localChainDepth (ParameterAssignment.stepParameters Tb y) β k) N) o))} ≤
      C * flowCouplings (ParameterAssignment.stepParameters Tb y) β k ^ (-p)
def nearIdentityAlongChainStatement : Prop := HoldsOnParameterFamilies nearIdentityAlongChainAt
end YangMills.Construction.ResponseInTheExpansion
end
