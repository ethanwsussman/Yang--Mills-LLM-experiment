import Formulation.ReferenceCoupling
import YangMills.Construction.TheStatementsProvedTogether.FromHeatSumOnALatticeProof
import YangMills.Construction.LawByMomentsOfTheFlow.LawAtLimitPointsProof
import YangMills.Construction.GrowingTori.TransportThroughABallToTheTorusOfAnExponentProof
import YangMills.Construction.FourPointCondition.LawsAtTheDataOfTheFlowProof
noncomputable section
open Filter Set MeasureTheory ProbabilityTheory
open scoped ENNReal Topology
namespace YangMills.StoppedReference
open Construction PeriodicLattice TestFunctions TorusMetric FourPointBounds WeightedResponses
open ResponseInTheExpansion FreeEnergies TorusLumps
open TopAux.NonemptyTestClasses QuadrupleClasses.Collinear

def stoppedTests (L M r : ℕ) : Fin 2 → FourTorus L (M+r) → ℝ :=
  fun i => dilateToSide L M (M+r) (fixedReferenceTests L M i)

def fineSource (L k m : ℕ) (f : FourTorus L m → ℝ) : FinePlaquetteFunction :=
  fun x => f (torusProj (torusSide L m) fun i => x i / (L:ℝ)^k)

theorem reference_eq_covariance {L M k r : ℕ} [NeZero L] (hL : 3 ≤ L) (hm : 1 ≤ M) (β : ℝ) :
    let N := 2 * L^(M+r)
    let h (i : Fin 2) := fineWeight (fineSource L k (M+r) (stoppedTests L M r i)) (fineSide L k N)
    referenceResponse L M (k+r) β =
      cov[curvatureObservable (h 0), curvatureObservable (h 1); wilsonLaw β (fineSide L k N)] := by
  classical
  intro N h
  let m := fineSide L k N
  let μ := WeightedResponses.wilsonLaw β m
  let O (i : Fin 2) := curvatureObservable (h i)
  have hr := TheStatementsProvedTogether.four_point_cutoff_rescaling_invariant L M (k+r) (M+r) k
    2 β hL (by omega) (fixedReferenceTests L M)
  have hw := TheStatementsProvedTogether.torus_ursell_eq_weighted_curvature L (M+r) k 2 β hL
    (by omega) (stoppedTests L M r)
  have hcov : referenceResponse L M (k+r) β = (Cumulants.mixedCumulant μ O).re :=
    congrArg Complex.re (hr.trans hw)
  letI : IsProbabilityMeasure μ := YangMills.SharedProofs.p2076 β
  have hO (i : Fin 2) : Probability.IsBoundedRealRV (O i) := YangMills.SharedProofs.p42321 _
  have hL2 (i : Fin 2) : MemLp (O i) 2 μ := by
    obtain ⟨B,hB⟩ := (hO i).bounded
    exact MemLp.of_bound (hO i).measurable.aestronglyMeasurable B (Eventually.of_forall hB)
  change _ = cov[O 0,O 1; μ]
  have hv : O = ![O 0, O 1] := by funext i; fin_cases i <;> rfl
  rw [hcov,hv,(TheStatementsProvedTogether.moment_generating_function_regular _ μ).2
    (O 0) (O 1) (hO 0).measurable (hO 1).measurable (hO 0).bounded (hO 1).bounded,
    Complex.ofReal_re]
  exact (covariance_eq_sub (hL2 0) (hL2 1)).symm

theorem scaled_periodized_norm {S : ℝ} (hS : 8 ≤ S) (c : Fin 4 → ℝ) :
    uniformNorm (periodize S (scaledBump (6/5) c)) = 1 := by
  let B := closedBallR4 c ((6/5)/16)
  have hdiam : ∀ x ∈ B, ∀ y ∈ B, euclidNormVec (x-y) < S/2 := by
    intro x hx y hy
    change euclidNormVec (x-c) ≤ (6/5)/16 at hx
    change euclidNormVec (y-c) ≤ (6/5)/16 at hy
    have hdiff := QuadrupleClasses.Collinear.euclidNormVec_sub_le (x-c) (y-c)
    rw [show x - c - (y - c) = x-y by abel] at hdiff
    linarith
  rw [ToriLimits.ExponentTorusPeriodization.uniformNorm_periodize (by linarith : 0<S) hdiam
    (fun x hx => image_eq_zero_of_notMem_tsupport (fun h => hx (tsupport_scaledBump_subset
      (by norm_num : 0<(6/5:ℝ)) c h)))
    (fun x => by simpa [Real.norm_eq_abs,abs_of_nonneg (scaledBump_nonneg _ _ _)] using scaledBump_le_one (6/5) c x)]
  exact uniformNorm_scaledBump c
private theorem setEuclidDist_le_comm {S : ℝ} (A B : Set (Torus4 S)) :
    setEuclidDist A B ≤ setEuclidDist B A := by
  unfold setEuclidDist
  refine le_iInf₂ fun b hb => le_iInf₂ fun a ha => ?_
  rw [AmbientPoints.torusEuclidNorm_sub_comm b a]
  exact (iInf₂_le a ha).trans (iInf₂_le b hb)
private theorem euclidDistTorus_le_of_mem_closedBall {S d : ℝ} {c u v : Torus4 S} (hu : u ∈ closedBallTorus c d)
    (hv : v ∈ closedBallTorus c d) : euclidDistTorus u v ≤ 2 * d := by
  have h1 : torusEuclidNorm (u - c) ≤ d := hu
  have h2 : torusEuclidNorm (v - c) ≤ d := hv
  have h3 := AmbientPoints.torusEuclidNorm_sub_le u c v
  rw [AmbientPoints.torusEuclidNorm_sub_comm c v] at h3
  show torusEuclidNorm (u - v) ≤ 2 * d
  linarith
private theorem euclidDistTorus_le_of_setEuclidDist_le {S d : ℝ} {x₁ x₂ : Torus4 S} {A B : Set (Torus4 S)} (hd : 0 < d)
    (hA : A ⊆ closedBallTorus x₁ d) (hB : B ⊆ closedBallTorus x₂ d) (h : setEuclidDist A B ≤ ENNReal.ofReal (6 * d)) :
    ∀ u ∈ A, ∀ v ∈ B, euclidDistTorus u v ≤ 10 * d := by
  intro u hu v hv
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hlt : setEuclidDist A B < ENNReal.ofReal (6 * d + ε) :=
    h.trans_lt ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 (by linarith))
  simp only [setEuclidDist, iInf_lt_iff] at hlt
  obtain ⟨p, hp, q, hq, hpq⟩ := hlt
  have hpq' : torusEuclidNorm (p - q) < 6 * d + ε := (ENNReal.ofReal_lt_ofReal_iff (by positivity)).1 hpq
  have h1 : euclidDistTorus u p ≤ 2 * d := euclidDistTorus_le_of_mem_closedBall (hA hu) (hA hp)
  have h2 : euclidDistTorus q v ≤ 2 * d := euclidDistTorus_le_of_mem_closedBall (hB hq) (hB hv)
  have h3 := AmbientPoints.torusEuclidNorm_sub_le u p v
  have h4 := AmbientPoints.torusEuclidNorm_sub_le p q v
  have h1' : torusEuclidNorm (u - p) ≤ 2 * d := h1
  have h2' : torusEuclidNorm (q - v) ≤ 2 * d := h2
  show torusEuclidNorm (u - v) ≤ 10 * d + ε
  linarith
private theorem pairTuple {p : StepParameters} {m : ℕ} {d θ : ℝ} (hd : 0 < d)
    {f : Fin 2 → FourTorus p.side m → ℝ}
    (hnorm : ∀ i, uniformNorm (f i) = 1) (hpair : (f 0,f 1) ∈ separatedPairsFourTorus p.side m d θ) :
    IsSeparatedTestTuple p m d θ f := by
  obtain ⟨a,b,h0,h1,hsep,hnear⟩ := hpair
  have B0 := h0.2.2.2.1
  have B1 := h1.2.2.2.1
  have near := euclidDistTorus_le_of_setEuclidDist_le hd B0 B1 hnear
  refine ⟨hnorm, ?_, ?_, ⟨hd, ?_⟩, ?_⟩
  · intro i
    fin_cases i
    · exact h0.1
    · exact h1.1
  · intro i
    fin_cases i
    · simpa [lipConstTorus,hnorm] using h0.2.2.2.2.2
    · simpa [lipConstTorus,hnorm] using h1.2.2.2.2.2
  · intro i j hij
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · exact hsep
    · exact hsep.trans (setEuclidDist_le_comm _ _)
    · exact (hij rfl).elim
  · intro i j u hu v hv
    fin_cases i <;> fin_cases j
    · exact (euclidDistTorus_le_of_mem_closedBall (B0 hu) (B0 hv)).trans (by linarith)
    · exact near u hu v hv
    · have e := near v hv u hu
      change torusEuclidNorm (u-v) ≤ _
      rwa [AmbientPoints.torusEuclidNorm_sub_comm]
    · exact (euclidDistTorus_le_of_mem_closedBall (B1 hu) (B1 hv)).trans (by linarith)

theorem stoppedTests_shaped (p : StepParameters) (hfit : p.Admissible)
    (hL : Conventions.IsAdmissibleBlockingFactor p.side) (M : ℕ+) (hside : 48 ≤ torusSide p.side M) :
    ∃ θ : ℝ, θ ∈ Ioc 0 1 ∧ ∀ r : ℕ,
      IsSeparatedTestTuple p ((M:ℕ)+r) ((6/5) * (p.side:ℝ)^r) θ (stoppedTests p.side M r) := by
  classical
  obtain ⟨C, hC, hlip⟩ := exists_unitBump_lipschitz
  let θ := min (1 / 32 ^ 4) (1 / (32 * C))
  have hθ : 0 < θ := lt_min (by norm_num) (by positivity)
  have hθ1 : θ ≤ 1 / 32 ^ 4 := min_le_left _ _
  have hθ2 : 32 * C * θ ≤ 1 := by
    have := (le_div_iff₀ (by positivity : 0 < 32*C)).1 (min_le_right (1/32^4) (1/(32*C)))
    exact (mul_comm _ _).le.trans this
  have hI : θ ∈ Ioc (0:ℝ) 1 := ⟨hθ,hθ1.trans (by norm_num)⟩
  let s : Conventions.StandingParameters := ⟨p.side,hL,1,M⟩
  let d : ℝ := 6/5
  obtain ⟨X,hX,hpair,_⟩ := referenceBumpTests_shaped hC hlip hI hθ1 hθ2 (by norm_num : 0<d) s (by
    change 40*(6/5:ℝ) ≤ torusSide p.side M
    linarith)
  have eqRef : referenceBumpTests s d = fixedReferenceTests p.side M := by
    funext i
    fin_cases i <;> apply congrArg (periodize _) <;> funext x <;>
      norm_num [d,bumpQuadruple,fixedReferenceBump,scaledBump,lineCentre]
  have hnorm i : uniformNorm (referenceBumpTests s d i) = 1 := by
    change uniformNorm (periodize (torusSide p.side M) (scaledBump (6/5) _)) = 1
    exact scaled_periodized_norm (by linarith) _
  have hbase : IsSeparatedTestTuple p M d θ (fixedReferenceTests p.side M) := by
    rw [← eqRef]
    exact pairTuple (by norm_num : 0<d) hnorm (hX ▸ hpair)
  refine ⟨θ,hI,fun r => (TheStatementsProvedTogether.dilated_tuple_to_side p M ((M:ℕ)+r) 2 d
    (6/5*(p.side:ℝ)^r) θ hfit ?_ _ hbase).1⟩
  simp [torusSide,pow_add,d]
  ring
end YangMills.StoppedReference
