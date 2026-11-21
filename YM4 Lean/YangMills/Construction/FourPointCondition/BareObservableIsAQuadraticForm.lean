import YangMills.Construction.ColdChainAtEveryLevel.CriticalChainsOfTurnedTops
import YangMills.Construction.ResponseInTheExpansion.LocalChainAboveALevel
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
open Classical
namespace YangMills.Construction
open ResponseInTheExpansion WeightedResponses TorusLumps TorusFields RenormalizationStepParameters BlockAverages
namespace FourPointCondition
def bareObservableQuadraticFormStatement : Prop :=
  HoldsOnParameterFamilies fun tbl y => ∃ (C : ℕ → ℝ) (x₀ : ℝ),
    ∀ (T : StageTower (tbl.stepParameters y)) (β : ℝ) (N : ℕ) [NeZero N] (r : ℝ)
      (o : TorusSite (fineSide (tbl.stepParameters y).side (chainDepth (couplingFlow (tbl.stepParameters y) β 0).1)
        (fineSide (tbl.stepParameters y).side (chainDepth (couplingFlow (tbl.stepParameters y) β 0).1) N)))
      (w : PlaquetteWeight (fineSide (tbl.stepParameters y).side 0 (fineSide (tbl.stepParameters y).side (chainDepth (couplingFlow (tbl.stepParameters y) β 0).1)
        (fineSide (tbl.stepParameters y).side (chainDepth (couplingFlow (tbl.stepParameters y) β 0).1) N)))),
      IsLocalChainAbove tbl y T β 0 N r x₀ → (tbl.stepParameters y).side ∣ N → weightSup w ≤ 1 →
      (∀ (z : TorusSite (fineSide (tbl.stepParameters y).side (chainDepth (couplingFlow (tbl.stepParameters y) β 0).1)
          (fineSide (tbl.stepParameters y).side (chainDepth (couplingFlow (tbl.stepParameters y) β 0).1) N))) (p), z ∉ supBall o (12 * r) →
        IsPlaquetteAt (tbl.stepParameters y).side 0 z p → w p = 0) →
      ∀ q : ℕ, 1 ≤ q →
        ∫⁻ u, ENNReal.ofReal (Set.indicator {u | IsLocalEvent T 0 (chainDepth (couplingFlow (tbl.stepParameters y) β 0).1)
              (localBoxRadius (couplingFlow (tbl.stepParameters y) β 0).1) N u o ∧
            IsGaugeSmallAlong T 0 r (logCubeScale (couplingFlow (tbl.stepParameters y) β 0).1)
              ((couplingFlow (tbl.stepParameters y) β 0).1 ^ (-(1 / 4 : ℝ))) (chainDepth (couplingFlow (tbl.stepParameters y) β 0).1)
              (fineSide (tbl.stepParameters y).side (chainDepth (couplingFlow (tbl.stepParameters y) β 0).1) N)
              (sampleBelow (tbl.stepParameters y) (0 + chainDepth (couplingFlow (tbl.stepParameters y) β 0).1)
                (chainDepth (couplingFlow (tbl.stepParameters y) β 0).1) N u) o
              (axialGaugeAt (tbl.stepParameters y) (topField (tbl.stepParameters y) (0 + chainDepth (couplingFlow (tbl.stepParameters y) β 0).1)
                (fineSide (tbl.stepParameters y).side (chainDepth (couplingFlow (tbl.stepParameters y) β 0).1) N)
                (sampleBelow (tbl.stepParameters y) (0 + chainDepth (couplingFlow (tbl.stepParameters y) β 0).1)
                  (chainDepth (couplingFlow (tbl.stepParameters y) β 0).1) N u))
                (siteAbove (tbl.stepParameters y).side (chainDepth (couplingFlow (tbl.stepParameters y) β 0).1)
                  (fineSide (tbl.stepParameters y).side (chainDepth (couplingFlow (tbl.stepParameters y) β 0).1) N) o))}
          (fun u => |response T β (fun _ => 1) 0 _ w (sampleBelow (tbl.stepParameters y) 0
              (chainDepth (couplingFlow (tbl.stepParameters y) β 0).1) _ (sampleBelow (tbl.stepParameters y)
                (0 + chainDepth (couplingFlow (tbl.stepParameters y) β 0).1) (chainDepth (couplingFlow (tbl.stepParameters y) β 0).1) N u)) -
            (1 / 2) * ∑ p ∈ plaquettesIn Finset.univ, w p * ∑ e : Fin 3,
              imaginaryComponent e (sampledCurvature T 0 (chainDepth (couplingFlow (tbl.stepParameters y) β 0).1) r
                (couplingFlow (tbl.stepParameters y) β 0).1 N u o p) ^ 2| ^ (2 * q)) u)
          ∂(markedSampleLaw T β (0 + chainDepth (couplingFlow (tbl.stepParameters y) β 0).1 + chainDepth (couplingFlow (tbl.stepParameters y) β 0).1) N) ≤
        ENNReal.ofReal ((C q * r ^ 4 * (couplingFlow (tbl.stepParameters y) β 0).1 ^ (-(3 / 2 : ℝ) + 6 / 1000)) ^ (2 * q))
end FourPointCondition
end YangMills.Construction
end
