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
def curvatureNearDescendedFormAt : Prop :=
  ∃ C c x₀ : ℝ, 0 < c ∧ ∀ (T : StageTower (ParameterAssignment.stepParameters Tb y)) (β : ℝ) (k N : ℕ) [NeZero N] (nn s : ℝ)
    (o : TorusSite (fineSide (ParameterAssignment.stepParameters Tb y).side (localChainDepth (ParameterAssignment.stepParameters Tb y) β k)
      (fineSide (ParameterAssignment.stepParameters Tb y).side (localChainDepth (ParameterAssignment.stepParameters Tb y) β k) N))),
    IsLocalChainAbove Tb y T β k N nn x₀ → (ParameterAssignment.stepParameters Tb y).side ∣ N → 0 ≤ s →
    s ≤ flowCouplings (ParameterAssignment.stepParameters Tb y) β k ^ (-(1 / 4 : ℝ)) →
    ∀ᵐ u ∂(markedSampleLaw T β (k + localChainDepth (ParameterAssignment.stepParameters Tb y) β k +
        localChainDepth (ParameterAssignment.stepParameters Tb y) β k) N),
      IsLocalEvent T k (localChainDepth (ParameterAssignment.stepParameters Tb y) β k)
        (localBlockSide (ParameterAssignment.stepParameters Tb y) β k) N u o →
      IsGaugeSmallAlong T k nn (localLogScale (ParameterAssignment.stepParameters Tb y) β k) s
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
            (fineSide (ParameterAssignment.stepParameters Tb y).side (localChainDepth (ParameterAssignment.stepParameters Tb y) β k) N) o)) →
      ∀ p ∈ plaquettesIn (supBall o (ballRadius (ParameterAssignment.stepParameters Tb y).side nn
          (localLogScale (ParameterAssignment.stepParameters Tb y) β k) 0)),
        ‖((lieFormCurl (ballLog
            (gaugeDescent k (localChainDepth (ParameterAssignment.stepParameters Tb y) β k)
              (fineSide (ParameterAssignment.stepParameters Tb y).side (localChainDepth (ParameterAssignment.stepParameters Tb y) β k) N)
              (sampleBelow (ParameterAssignment.stepParameters Tb y) (k + localChainDepth (ParameterAssignment.stepParameters Tb y) β k)
                (localChainDepth (ParameterAssignment.stepParameters Tb y) β k) N u)
              (axialGaugeAt (ParameterAssignment.stepParameters Tb y)
                (topField (ParameterAssignment.stepParameters Tb y) (k + localChainDepth (ParameterAssignment.stepParameters Tb y) β k)
                  (fineSide (ParameterAssignment.stepParameters Tb y).side (localChainDepth (ParameterAssignment.stepParameters Tb y) β k) N)
                  (sampleBelow (ParameterAssignment.stepParameters Tb y) (k + localChainDepth (ParameterAssignment.stepParameters Tb y) β k)
                    (localChainDepth (ParameterAssignment.stepParameters Tb y) β k) N u))
                (siteAbove (ParameterAssignment.stepParameters Tb y).side (localChainDepth (ParameterAssignment.stepParameters Tb y) β k)
                  (fineSide (ParameterAssignment.stepParameters Tb y).side (localChainDepth (ParameterAssignment.stepParameters Tb y) β k) N) o)))
            (topField (ParameterAssignment.stepParameters Tb y) k _
              (sampleBelow (ParameterAssignment.stepParameters Tb y) k (localChainDepth (ParameterAssignment.stepParameters Tb y) β k) _
                (sampleBelow (ParameterAssignment.stepParameters Tb y) (k + localChainDepth (ParameterAssignment.stepParameters Tb y) β k)
                  (localChainDepth (ParameterAssignment.stepParameters Tb y) β k) N u)))
            o (ballRadius (ParameterAssignment.stepParameters Tb y).side nn (localLogScale (ParameterAssignment.stepParameters Tb y) β k) 0)) p -
          sampledCurvature T k (localChainDepth (ParameterAssignment.stepParameters Tb y) β k) nn
            (flowCouplings (ParameterAssignment.stepParameters Tb y) β k) N u o p : imaginaryQuaternions) : Quaternion ℝ)‖ ≤
        C * (s ^ 2 + Real.exp (-(c * localLogScale (ParameterAssignment.stepParameters Tb y) β k)))
def curvatureNearDescendedFormStatement : Prop := HoldsOnParameterFamilies curvatureNearDescendedFormAt
end YangMills.Construction.ResponseInTheExpansion
end
