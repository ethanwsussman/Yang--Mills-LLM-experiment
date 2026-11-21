import YangMills.Construction.ColdChainAtEveryLevel.CriticalChainsOfTurnedTops
import YangMills.Construction.ResponseInTheExpansion.LocalChainAboveALevel
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ResponseInTheExpansion
open TorusFields WeightedResponses RenormalizationStepParameters TorusLumps BlockAverages MeasureTheory
open Classical
def levelCurvatureMomentsStatement : Prop :=
  HoldsOnParameterFamilies fun tbl y => ∀ q : ℕ, ∃ C x₀ : ℝ, ∀ (T : WeightedResponses.StageTower (tbl.stepParameters y))
    (β : ℝ) (k N : ℕ) [NeZero N] (r : ℝ)
    (o : TorusSite (fineSide (tbl.stepParameters y).side (chainDepth (couplingFlow (tbl.stepParameters y) β k).1)
      (fineSide (tbl.stepParameters y).side (chainDepth (couplingFlow (tbl.stepParameters y) β k).1) N)))
    (p : Fin q → TorusPlaquette (fineSide (tbl.stepParameters y).side (chainDepth (couplingFlow (tbl.stepParameters y) β k).1)
      (fineSide (tbl.stepParameters y).side (chainDepth (couplingFlow (tbl.stepParameters y) β k).1) N)))
    (e : Fin q → Fin 3) (w : ℕ),
    N = 2 * (tbl.stepParameters y).side ^ (w + 1) → IsLocalChainAbove tbl y T β k N r x₀ →
    (∀ j, p j ∈ plaquettesIn Finset.univ ∧ (p j).1 ∈ supBall o (19 * r)) →
    MeasurableSet {u | IsLocalEvent T k (chainDepth (couplingFlow (tbl.stepParameters y) β k).1)
        (localBoxRadius (couplingFlow (tbl.stepParameters y) β k).1) N u o} ∧
    (∀ i, AEStronglyMeasurable (Set.indicator {u | IsLocalEvent T k (chainDepth (couplingFlow (tbl.stepParameters y) β k).1)
          (localBoxRadius (couplingFlow (tbl.stepParameters y) β k).1) N u o}
        (fun u => imaginaryComponent (e i) (sampledCurvature T k (chainDepth (couplingFlow (tbl.stepParameters y) β k).1) r
          (couplingFlow (tbl.stepParameters y) β k).1 N u o (p i))))
      (markedSampleLaw T β (k + chainDepth (couplingFlow (tbl.stepParameters y) β k).1 +
        chainDepth (couplingFlow (tbl.stepParameters y) β k).1) N)) ∧
    (∀ᵐ u ∂(markedSampleLaw T β (k + chainDepth (couplingFlow (tbl.stepParameters y) β k).1 +
        chainDepth (couplingFlow (tbl.stepParameters y) β k).1) N),
      IsLocalEvent T k (chainDepth (couplingFlow (tbl.stepParameters y) β k).1)
        (localBoxRadius (couplingFlow (tbl.stepParameters y) β k).1) N u o →
      ∀ i, |imaginaryComponent (e i) (sampledCurvature T k (chainDepth (couplingFlow (tbl.stepParameters y) β k).1) r
        (couplingFlow (tbl.stepParameters y) β k).1 N u o (p i))| ≤ C) ∧
    (∀ i i', e i = e i' → |accumulatedCovariance tbl.coupling tbl.ρA (tbl.stepParameters y).side k
      (chainDepth (couplingFlow (tbl.stepParameters y) β k).1)
      (fineSide (tbl.stepParameters y).side (chainDepth (couplingFlow (tbl.stepParameters y) β k).1) N)
      (curlFunctional (p i)) (curlFunctional (p i'))| ≤ C) ∧
    Integrable (Set.indicator {u | IsLocalEvent T k (chainDepth (couplingFlow (tbl.stepParameters y) β k).1)
          (localBoxRadius (couplingFlow (tbl.stepParameters y) β k).1) N u o}
        (fun u => ∏ j, imaginaryComponent (e j) (sampledCurvature T k (chainDepth (couplingFlow (tbl.stepParameters y) β k).1) r
          (couplingFlow (tbl.stepParameters y) β k).1 N u o (p j))))
      (markedSampleLaw T β (k + chainDepth (couplingFlow (tbl.stepParameters y) β k).1 +
        chainDepth (couplingFlow (tbl.stepParameters y) β k).1) N) ∧
    |∫ u, Set.indicator {u | IsLocalEvent T k (chainDepth (couplingFlow (tbl.stepParameters y) β k).1)
          (localBoxRadius (couplingFlow (tbl.stepParameters y) β k).1) N u o}
        (fun u => ∏ j, imaginaryComponent (e j) (sampledCurvature T k (chainDepth (couplingFlow (tbl.stepParameters y) β k).1) r
          (couplingFlow (tbl.stepParameters y) β k).1 N u o (p j))) u
        ∂(markedSampleLaw T β (k + chainDepth (couplingFlow (tbl.stepParameters y) β k).1 +
          chainDepth (couplingFlow (tbl.stepParameters y) β k).1) N) -
      (couplingFlow (tbl.stepParameters y) β k).1 ^ (-(q : ℝ) / 2) * wickPairingSum fun i j =>
        if e i = e j then accumulatedCovariance tbl.coupling tbl.ρA (tbl.stepParameters y).side k
          (chainDepth (couplingFlow (tbl.stepParameters y) β k).1)
          (fineSide (tbl.stepParameters y).side (chainDepth (couplingFlow (tbl.stepParameters y) β k).1) N)
          (curlFunctional (p i)) (curlFunctional (p j)) else 0| ≤
      C * (couplingFlow (tbl.stepParameters y) β k).1 ^ (-((q : ℝ) + 1) / 2 + 2 / 1000)
end YangMills.Construction.ResponseInTheExpansion
end
