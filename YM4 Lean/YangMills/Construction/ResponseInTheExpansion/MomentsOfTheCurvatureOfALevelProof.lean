import YangMills.Construction.ResponseInTheExpansion.MomentsOfTheCurvatureOfALevel
import YangMills.Construction.ResponseInTheExpansion.TheCurvatureIsAGaussianChain
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.ResponseInTheExpansion
open Classical
theorem levelCurvatureMoments (hG : gaussianMomentsAlongChainStatement)
    (hC : curvatureGaussianChainStatement) : levelCurvatureMomentsStatement := by
  intro a ha
  obtain ⟨L₀, rt₀, C₀, hrt, hT⟩ := hC a ha
  refine ⟨L₀, rt₀, C₀, hrt, fun L hL hL₀ Tb h1 h2 h3 h4 h5 h6 h7 => ?_⟩
  obtain ⟨y₀, hy⟩ := hT L hL hL₀ Tb h1 h2 h3 h4 h5 h6 h7
  refine ⟨y₀, fun y hy₀ hR hW q => ?_⟩
  obtain ⟨K, x₀, hK⟩ := hy y hy₀ hR hW q
  obtain ⟨C, hCm⟩ := hG q K
  refine ⟨|C|, max x₀ 1, ?_⟩
  intro T β k N _ nn o p e w hw hL' hp
  have hx₁ : 1 ≤ (TorusLumps.couplingFlow (Tb.stepParameters y) β k).1 := (le_max_right _ _).trans hL'.floor_le
  have hx₀ : 0 < (TorusLumps.couplingFlow (Tb.stepParameters y) β k).1 := by linarith
  have hL'' : IsLocalChainAbove Tb y T β k N nn x₀ :=
    { hL' with floor_le := (le_max_left _ _).trans hL'.floor_le }
  obtain ⟨ε, A, Xs, Gam, Gamc, ζ, top, s, hch, hA0, hsum, hcov⟩ := hK T β k N nn o p e w hw hL'' hp
  obtain ⟨m1, m2, m3, m4, m5⟩ := hCm _ _ _ _ _ _ _ _ _ _ _ _ _ hch
  have hprod : (fun u => ∏ i, tailSum (WeightedResponses.chainDepth (TorusLumps.couplingFlow (Tb.stepParameters y) β k).1) ζ top 0 i u) =
      fun u => ∏ j, BlockAverages.imaginaryComponent (e j) (sampledCurvature T k
        (WeightedResponses.chainDepth (TorusLumps.couplingFlow (Tb.stepParameters y) β k).1) nn
        (TorusLumps.couplingFlow (Tb.stepParameters y) β k).1 N u o (p j)) := by
    funext u
    exact Finset.prod_congr rfl fun i _ => hsum u i
  have hfun : ∀ i, tailSum (WeightedResponses.chainDepth (TorusLumps.couplingFlow (Tb.stepParameters y) β k).1) ζ top 0 i =
      fun u => BlockAverages.imaginaryComponent (e i) (sampledCurvature T k
        (WeightedResponses.chainDepth (TorusLumps.couplingFlow (Tb.stepParameters y) β k).1) nn
        (TorusLumps.couplingFlow (Tb.stepParameters y) β k).1 N u o (p i)) :=
    fun i => funext fun u => hsum u i
  rw [hprod, hA0] at m3 m5
  rw [hA0] at m1 m2
  have hXq : ((TorusLumps.couplingFlow (Tb.stepParameters y) β k).1 ^ (-(1 / 2 : ℝ))) ^ q =
      (TorusLumps.couplingFlow (Tb.stepParameters y) β k).1 ^ (-(q : ℝ) / 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx₀.le]
    congr 1
    ring
  have hXq1 : ((TorusLumps.couplingFlow (Tb.stepParameters y) β k).1 ^ (-(1 / 2 : ℝ))) ^ (q + 1) *
      (TorusLumps.couplingFlow (Tb.stepParameters y) β k).1 ^ (2 / 1000 : ℝ) =
      (TorusLumps.couplingFlow (Tb.stepParameters y) β k).1 ^ (-((q : ℝ) + 1) / 2 + 2 / 1000) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx₀.le, ← Real.rpow_add hx₀]
    congr 1
    push_cast
    ring
  have hpair : (fun i i' => ∑ u ∈ Finset.range (WeightedResponses.chainDepth (TorusLumps.couplingFlow (Tb.stepParameters y) β k).1),
      Gam u i i') = fun i j =>
      if e i = e j then WeightedResponses.accumulatedCovariance Tb.coupling Tb.ρA (Tb.stepParameters y).side k
        (WeightedResponses.chainDepth (TorusLumps.couplingFlow (Tb.stepParameters y) β k).1)
        (WeightedResponses.fineSide (Tb.stepParameters y).side
          (WeightedResponses.chainDepth (TorusLumps.couplingFlow (Tb.stepParameters y) β k).1) N)
        (WeightedResponses.curlFunctional (p i)) (WeightedResponses.curlFunctional (p j)) else 0 :=
    funext fun i => funext fun i' => hcov i i'
  rw [hpair, hXq, mul_assoc, hXq1] at m5
  refine ⟨hA0 ▸ hch.event_measurable 0, ?_, ?_, ?_, m3, ?_⟩
  · intro i
    have := m1 i
    rwa [hfun i] at this
  · filter_upwards [m2] with u hu hloc i
    have := hu hloc i
    rw [hsum u i] at this
    exact this.trans (le_abs_self _)
  · intro i i' hee
    have := m4 i i'
    rw [hcov i i', if_pos hee] at this
    exact this.trans (le_abs_self _)
  · refine m5.trans ?_
    apply mul_le_mul_of_nonneg_right (le_abs_self _)
    exact Real.rpow_nonneg hx₀.le _
end YangMills.Construction.ResponseInTheExpansion
end
