import YangMills.Construction.ColdChainAtEveryLevel.CriticalChainsOfTurnedTops
import YangMills.Construction.ResponseInTheExpansion.GaussianMomentsAlongAChain
import YangMills.Construction.ResponseInTheExpansion.LocalChainAboveALevel
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ResponseInTheExpansion
open TorusFields WeightedResponses RenormalizationStepParameters TorusLumps BlockAverages
open Classical
def curvatureGaussianChainStatement : Prop :=
  HoldsOnParameterFamilies fun tbl y => ∀ q : ℕ, ∃ K x₀ : ℝ, ∀ (T : WeightedResponses.StageTower (tbl.stepParameters y))
    (β : ℝ) (k N : ℕ) [NeZero N] (r : ℝ)
    (o : TorusSite (fineSide (tbl.stepParameters y).side (chainDepth (couplingFlow (tbl.stepParameters y) β k).1)
      (fineSide (tbl.stepParameters y).side (chainDepth (couplingFlow (tbl.stepParameters y) β k).1) N)))
    (p : Fin q → TorusPlaquette (fineSide (tbl.stepParameters y).side (chainDepth (couplingFlow (tbl.stepParameters y) β k).1)
      (fineSide (tbl.stepParameters y).side (chainDepth (couplingFlow (tbl.stepParameters y) β k).1) N)))
    (e : Fin q → Fin 3) (w : ℕ),
    N = 2 * (tbl.stepParameters y).side ^ (w + 1) → IsLocalChainAbove tbl y T β k N r x₀ →
    (∀ j, p j ∈ plaquettesIn Finset.univ ∧ (p j).1 ∈ supBall o (19 * r)) →
    ∃ (ε : ℝ) (A : ℕ → Set (MarkedSample (tbl.stepParameters y) (k + chainDepth (couplingFlow (tbl.stepParameters y) β k).1 +
        chainDepth (couplingFlow (tbl.stepParameters y) β k).1) N)) (Xs : ℕ → ℝ) (Γ Γc : ℕ → Fin q → Fin q → ℝ)
      (ζ : ℕ → Fin q → MarkedSample (tbl.stepParameters y) (k + chainDepth (couplingFlow (tbl.stepParameters y) β k).1 +
        chainDepth (couplingFlow (tbl.stepParameters y) β k).1) N → ℝ)
      (top : Fin q → MarkedSample (tbl.stepParameters y) (k + chainDepth (couplingFlow (tbl.stepParameters y) β k).1 +
        chainDepth (couplingFlow (tbl.stepParameters y) β k).1) N → ℝ)
      (s : ℕ → MarkedSample (tbl.stepParameters y) (k + chainDepth (couplingFlow (tbl.stepParameters y) β k).1 +
        chainDepth (couplingFlow (tbl.stepParameters y) β k).1) N → ℝ),
      IsGaussianChain (markedSampleLaw T β (k + chainDepth (couplingFlow (tbl.stepParameters y) β k).1 +
          chainDepth (couplingFlow (tbl.stepParameters y) β k).1) N)
        K ((couplingFlow (tbl.stepParameters y) β k).1 ^ (-(1 / 2 : ℝ)))
        ((couplingFlow (tbl.stepParameters y) β k).1 ^ (2 / 1000 : ℝ)) ε
        (chainDepth (couplingFlow (tbl.stepParameters y) β k).1) A Xs Γ Γc ζ top s ∧
      A 0 = {u | IsLocalEvent T k (chainDepth (couplingFlow (tbl.stepParameters y) β k).1)
        (localBoxRadius (couplingFlow (tbl.stepParameters y) β k).1) N u o} ∧
      (∀ u i, tailSum (chainDepth (couplingFlow (tbl.stepParameters y) β k).1) ζ top 0 i u =
        imaginaryComponent (e i) (sampledCurvature T k (chainDepth (couplingFlow (tbl.stepParameters y) β k).1) r
          (couplingFlow (tbl.stepParameters y) β k).1 N u o (p i))) ∧
      ∀ i i', ∑ u ∈ Finset.range (chainDepth (couplingFlow (tbl.stepParameters y) β k).1), Γ u i i' =
        if e i = e i' then accumulatedCovariance tbl.coupling tbl.ρA (tbl.stepParameters y).side k
          (chainDepth (couplingFlow (tbl.stepParameters y) β k).1)
          (fineSide (tbl.stepParameters y).side (chainDepth (couplingFlow (tbl.stepParameters y) β k).1) N)
          (curlFunctional (p i)) (curlFunctional (p i')) else 0
end YangMills.Construction.ResponseInTheExpansion
end
