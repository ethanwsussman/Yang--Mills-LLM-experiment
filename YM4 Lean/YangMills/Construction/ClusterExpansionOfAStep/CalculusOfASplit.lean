import YangMills.Construction.ClusterExpansionOfAStep.TreesOfABlock
import YangMills.Construction.ClusterExpansionOfAStep.DensitiesOfASplit
import YangMills.Construction.ClusterExpansionOfAStep.FactorOfAClassIsOneRuleProof
import YangMills.Construction.ClusterExpansionOfAStep.LogOfAnIntegralAlongASegment
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open MeasureTheory Set
namespace YangMills.Construction.ClusterExpansionOfAStep
open BlockAverages LumpContours ColdStepAtMirrorFrames StepSettings TorusFields TorusLumps Interpolation
section Cutoff
theorem coordNorm_eq_norm (v : EuclideanSpace ℝ (Fin 3)) : coordNorm v = ‖v‖ := by apply _root_.YangMills.Construction.BlockTrees.norm_toImaginary <;> assumption
variable {ρ : ℝ} {p : ℝ → ℝ}
theorem cutoffFactor_le_one (hρ : 0 < ρ) (hp : IsCutoff ρ p) {u : ℝ} (h0 : 0 ≤ u) : cutoffFactor ρ p u ≤ 1 := by apply _root_.YangMills.Construction.CoarseFactorLocality.cutoffFactor_le_one <;> assumption
theorem cutoffFactor_nonneg (u : ℝ) : 0 ≤ cutoffFactor ρ p u := by apply _root_.YangMills.Construction.CoarseFactorLocality.cutoffFactor_nonneg <;> assumption
theorem measurable_cutoffFactor_coordNorm (hp : IsCutoff ρ p) :
    Measurable fun v : EuclideanSpace ℝ (Fin 3) => cutoffFactor ρ p (coordNorm v) := by
  classical
  have hc : ContinuousOn (fun u => Real.exp (-p u)) (Ico 0 ρ) :=
    Real.continuous_exp.comp_continuousOn hp.smooth.continuousOn.neg
  have hg : Measurable ((Ico 0 ρ).piecewise (fun u => Real.exp (-p u)) fun _ => (0 : ℝ)) :=
    hc.measurable_piecewise continuousOn_const measurableSet_Ico
  have e : (fun v : EuclideanSpace ℝ (Fin 3) => cutoffFactor ρ p (coordNorm v)) =
      fun v => ((Ico 0 ρ).piecewise (fun u => Real.exp (-p u)) fun _ => (0 : ℝ)) ‖v‖ := by
    funext v
    rw [coordNorm_eq_norm]
    unfold cutoffFactor
    by_cases h : ‖v‖ < ρ
    · rw [if_pos h, Set.piecewise_eq_of_mem _ _ _ (show ‖v‖ ∈ Ico 0 ρ from ⟨norm_nonneg _, h⟩)]
    · rw [if_neg h, Set.piecewise_eq_of_notMem _ _ _ (fun hm => h hm.2)]
  rw [e]
  exact hg.comp measurable_norm
end Cutoff
section Calculus
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {C : E → ℝ} {U : Set E}
theorem deriv_comp_add_smul_eq_fderiv (hUo : IsOpen U) (hC : ContDiffOn ℝ 1 C U) {ζ : E} (a : E) (hζ : ζ ∈ U) :
    deriv (fun τ : ℝ => C (ζ + τ • a)) 0 = fderiv ℝ C ζ a := by
  have hd : DifferentiableAt ℝ C ζ :=
    (hC.differentiableOn (by simp)).differentiableAt (hUo.mem_nhds hζ)
  have h1 : HasDerivAt (fun τ : ℝ => ζ + τ • a) a 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const a).const_add ζ
  have h2 : HasFDerivAt C (fderiv ℝ C ζ) (ζ + (0 : ℝ) • a) := by simpa using hd.hasFDerivAt
  exact (h2.comp_hasDerivAt (0 : ℝ) h1).deriv
theorem integral_fderiv_smul_segment (hUo : IsOpen U) (hC : ContDiffOn ℝ 1 C U) {η : E}
    (hseg : ∀ v ∈ Icc (0 : ℝ) 1, v • η ∈ U) :
    ∫ v in (0 : ℝ)..1, fderiv ℝ C (v • η) η = C η - C 0 := by
  have hfd : ContinuousOn (fderiv ℝ C) U := hC.continuousOn_fderiv_of_isOpen hUo le_rfl
  have hu : uIcc (0 : ℝ) 1 = Icc 0 1 := uIcc_of_le zero_le_one
  have hder : ∀ v ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun v : ℝ => C (v • η)) (fderiv ℝ C (v • η) η) v := by
    intro v hv
    rw [hu] at hv
    have hd : DifferentiableAt ℝ C (v • η) :=
      (hC.differentiableOn (by simp)).differentiableAt (hUo.mem_nhds (hseg v hv))
    have h1 : HasDerivAt (fun v : ℝ => v • η) η v := by
      simpa using (hasDerivAt_id v).smul_const η
    exact hd.hasFDerivAt.comp_hasDerivAt v h1
  have hc : ContinuousOn (fun v : ℝ => fderiv ℝ C (v • η) η) (uIcc (0 : ℝ) 1) := by
    rw [hu]
    have h2 : ContinuousOn (fun v : ℝ => fderiv ℝ C (v • η)) (Icc 0 1) :=
      hfd.comp (by fun_prop) (fun v hv => hseg v hv)
    exact h2.clm_apply continuousOn_const
  have := intervalIntegral.integral_eq_sub_of_hasDerivAt hder hc.intervalIntegrable
  simpa using this
theorem intervalIntegrable_fderiv_smul_segment (hUo : IsOpen U) (hC : ContDiffOn ℝ 1 C U) {η : E}
    (hseg : ∀ v ∈ Icc (0 : ℝ) 1, v • η ∈ U) (a : E) :
    IntervalIntegrable (fun v : ℝ => fderiv ℝ C (v • η) a) volume 0 1 := by
  have hfd : ContinuousOn (fderiv ℝ C) U := hC.continuousOn_fderiv_of_isOpen hUo le_rfl
  have hu : uIcc (0 : ℝ) 1 = Icc 0 1 := uIcc_of_le zero_le_one
  have hc : ContinuousOn (fun v : ℝ => fderiv ℝ C (v • η) a) (uIcc (0 : ℝ) 1) := by
    rw [hu]
    have h2 : ContinuousOn (fun v : ℝ => fderiv ℝ C (v • η)) (Icc 0 1) :=
      hfd.comp (by fun_prop) (fun v hv => hseg v hv)
    exact h2.clm_apply continuousOn_const
  exact hc.intervalIntegrable
theorem continuousOn_integral_fderiv_segment {K : Set E} (hK : IsCompact K) (hUo : IsOpen U)
    (hC : ContDiffOn ℝ 1 C U) (hKU : K ⊆ U) (hseg : ∀ η ∈ K, ∀ v ∈ Icc (0 : ℝ) 1, v • η ∈ K) {A : E → E}
    (hA : Continuous A) :
    ContinuousOn (fun η => ∫ v in (0 : ℝ)..1, fderiv ℝ C (v • η) (A η)) K := by
  have hfd : ContinuousOn (fderiv ℝ C) U := hC.continuousOn_fderiv_of_isOpen hUo le_rfl
  have hG : ContinuousOn (fun p : ℝ × E => fderiv ℝ C (p.1 • p.2) (A p.2)) (Icc 0 1 ×ˢ K) := by
    have h1 : ContinuousOn (fun p : ℝ × E => fderiv ℝ C (p.1 • p.2)) (Icc 0 1 ×ˢ K) :=
      hfd.comp (by fun_prop) (fun p hp => hKU (hseg p.2 hp.2 p.1 hp.1))
    exact h1.clm_apply (by fun_prop)
  obtain ⟨M, hM⟩ := (isCompact_Icc.prod hK).exists_bound_of_continuousOn hG
  simp only [intervalIntegral.integral_of_le (zero_le_one' ℝ)]
  refine continuousOn_of_dominated (bound := fun _ => M) ?_ ?_ ?_ ?_
  · intro η hη
    have hc1 : ContinuousOn (fun v : ℝ => ((v, η) : ℝ × E)) (Icc 0 1) :=
      (by fun_prop : Continuous fun v : ℝ => ((v, η) : ℝ × E)).continuousOn
    have : ContinuousOn (fun v : ℝ => fderiv ℝ C (v • η) (A η)) (Icc 0 1) :=
      hG.comp hc1 (fun v hv => ⟨hv, hη⟩)
    exact (this.mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
  · intro η hη
    refine (ae_restrict_iff' measurableSet_Ioc).mpr (Filter.Eventually.of_forall fun v hv => ?_)
    exact hM (v, η) ⟨Ioc_subset_Icc_self hv, hη⟩
  · exact integrable_const _
  · refine (ae_restrict_iff' measurableSet_Ioc).mpr (Filter.Eventually.of_forall fun v hv => ?_)
    have hc1 : ContinuousOn (fun η : E => ((v, η) : ℝ × E)) K :=
      (by fun_prop : Continuous fun η : E => ((v, η) : ℝ × E)).continuousOn
    exact hG.comp hc1 (fun η hη => ⟨Ioc_subset_Icc_self hv, hη⟩)
end Calculus
section Means
variable {α : Type} [MeasurableSpace α] {μ : Measure α} {w f g : α → ℝ} {M : ℝ}
theorem integrable_mul_weight_exp (hw : Integrable w μ) (hf : AEStronglyMeasurable f μ)
    (hg : AEStronglyMeasurable g μ) (hfM : ∀ᵐ a ∂μ, |f a| ≤ M) (hgM : ∀ᵐ a ∂μ, |g a| ≤ M)
    {G : α → ℝ} (hG : AEStronglyMeasurable G μ) {K : ℝ} (hK : ∀ᵐ a ∂μ, |G a| ≤ K) (τ : ℝ) :
    Integrable (fun a => G a * (w a * Real.exp (f a + τ * g a))) μ := by
  have hdom : Integrable (fun a => K * (|w a| * Real.exp (M + |τ| * M))) μ :=
    (hw.abs.mul_const _).const_mul _
  refine hdom.mono' (hG.mul (hw.aestronglyMeasurable.mul
    (Real.continuous_exp.comp_aestronglyMeasurable (hf.add (hg.const_mul τ))))) ?_
  filter_upwards [hfM, hgM, hK] with a h1 h2 hk
  have hexp : Real.exp (f a + τ * g a) ≤ Real.exp (M + |τ| * M) := by
    apply Real.exp_le_exp.mpr
    have e1 : f a ≤ M := (abs_le.mp h1).2
    have e2 : τ * g a ≤ |τ| * M := by
      calc τ * g a ≤ |τ * g a| := le_abs_self _
        _ = |τ| * |g a| := abs_mul _ _
        _ ≤ |τ| * M := mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
    linarith
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _)]
  have : |w a| * Real.exp (f a + τ * g a) ≤ |w a| * Real.exp (M + |τ| * M) :=
    mul_le_mul_of_nonneg_left hexp (abs_nonneg _)
  exact mul_le_mul hk this (mul_nonneg (abs_nonneg _) (Real.exp_pos _).le) ((abs_nonneg _).trans hk)
theorem tiltedMean_finset_sum {ι : Type} (s : Finset ι) (G : ι → α → ℝ) (hw : Integrable w μ)
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) (hfM : ∀ᵐ a ∂μ, |f a| ≤ M)
    (hgM : ∀ᵐ a ∂μ, |g a| ≤ M) (hG : ∀ i ∈ s, AEStronglyMeasurable (G i) μ)
    (hK : ∀ i ∈ s, ∃ K : ℝ, ∀ᵐ a ∂μ, |G i a| ≤ K) (τ : ℝ) :
    tiltedMean μ w f g (fun a => ∑ i ∈ s, G i a) τ = ∑ i ∈ s, tiltedMean μ w f g (G i) τ := by
  unfold tiltedMean
  rw [← Finset.sum_div]
  congr 1
  rw [← integral_finsetSum]
  · refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
    simp only [Finset.sum_mul]
  · intro i hi
    obtain ⟨K, hk⟩ := hK i hi
    exact integrable_mul_weight_exp hw hf hg hfM hgM (hG i hi) hk τ
theorem tiltedMean_neg (G : α → ℝ) (τ : ℝ) :
    tiltedMean μ w f g (fun a => - G a) τ = - tiltedMean μ w f g G τ := by
  unfold tiltedMean
  rw [← neg_div]
  congr 1
  rw [← integral_neg]
  refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
  simp only [neg_mul]
end Means
section Balls
variable {R : StepSetup} {n : ℕ} {free : Finset (TorusBond (n * R.params.side))}
def closedBallsIn (R : StepSetup) {n : ℕ} (free : Finset (TorusBond (n * R.params.side))) : Set (FreeCoords free) :=
  {η | ∀ b, coordNorm (η b) ≤ R.ballRadius}
theorem isOpen_openBallsIn : IsOpen (openBallsIn R free) := by
  have e : openBallsIn R free = Set.pi univ fun _ => Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R.ballRadius := by
    ext η
    simp [openBallsIn, coordNorm_eq_norm]
  rw [e]
  exact isOpen_set_pi finite_univ fun _ _ => Metric.isOpen_ball
theorem isCompact_closedBallsIn : IsCompact (closedBallsIn R free) := by
  have e : closedBallsIn R free =
      Set.pi univ fun _ => Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) R.ballRadius := by
    ext η
    simp [closedBallsIn, coordNorm_eq_norm]
  rw [e]
  exact isCompact_univ_pi fun _ => isCompact_closedBall _ _
theorem measurableSet_openBallsIn : MeasurableSet (openBallsIn R free) := isOpen_openBallsIn.measurableSet
theorem openBallsIn_subset_closedBallsIn : openBallsIn R free ⊆ closedBallsIn R free := fun _ h b => (h b).le
theorem smul_mem_closedBallsIn {η : FreeCoords free} (hη : η ∈ closedBallsIn R free) {v : ℝ}
    (hv : v ∈ Icc (0 : ℝ) 1) : v • η ∈ closedBallsIn R free := by
  intro b
  have h := hη b
  rw [coordNorm_eq_norm] at h ⊢
  simp only [Pi.smul_apply, norm_smul, Real.norm_eq_abs, abs_of_nonneg hv.1]
  calc v * ‖η b‖ ≤ 1 * ‖η b‖ := mul_le_mul_of_nonneg_right hv.2 (norm_nonneg _)
    _ ≤ R.ballRadius := by simpa using h
theorem cutoffProd_pos {η : FreeCoords free} (h : η ∈ openBallsIn R free) : 0 < cutoffProd (R := R) η := by
  refine Finset.prod_pos fun b _ => ?_
  unfold cutoffFactor
  rw [if_pos (h b)]
  exact Real.exp_pos _
theorem cutoffProd_eq_zero {η : FreeCoords free} (h : η ∉ openBallsIn R free) : cutoffProd (R := R) η = 0 := by
  simp only [openBallsIn, mem_setOf_eq, not_forall, not_lt] at h
  obtain ⟨b, hb⟩ := h
  refine Finset.prod_eq_zero (Finset.mem_univ b) ?_
  unfold cutoffFactor
  rw [if_neg (not_lt.mpr hb)]
theorem cutoffProd_le_one (hρ : 0 < R.ballRadius) (hp : IsCutoff R.ballRadius R.barrierFn) (η : FreeCoords free) :
    cutoffProd (R := R) η ≤ 1 :=
  Finset.prod_le_one (fun _ _ => cutoffFactor_nonneg _) fun b _ =>
    cutoffFactor_le_one hρ hp (by rw [coordNorm_eq_norm]; positivity)
theorem cutoffProd_nonneg (η : FreeCoords free) : 0 ≤ cutoffProd (R := R) η :=
  Finset.prod_nonneg fun _ _ => cutoffFactor_nonneg _
theorem measurable_cutoffProd (hp : IsCutoff R.ballRadius R.barrierFn) :
    Measurable (cutoffProd (R := R) (free := free)) :=
  Finset.measurable_prod _ fun b _ => (measurable_cutoffFactor_coordNorm hp).comp (measurable_pi_apply b)
end Balls
section Bounded
variable {α : Type} [MeasurableSpace α] {μ : Measure α}
def AEBounded (μ : Measure α) (h : α → ℝ) : Prop := AEStronglyMeasurable h μ ∧ ∃ K : ℝ, ∀ᵐ a ∂μ, |h a| ≤ K
theorem AEBounded.add {h k : α → ℝ} (h1 : AEBounded μ h) (h2 : AEBounded μ k) : AEBounded μ fun a => h a + k a := by
  obtain ⟨m1, K1, b1⟩ := h1
  obtain ⟨m2, K2, b2⟩ := h2
  refine ⟨m1.add m2, K1 + K2, ?_⟩
  filter_upwards [b1, b2] with a x y
  exact (abs_add_le _ _).trans (add_le_add x y)
theorem AEBounded.neg {h : α → ℝ} (h1 : AEBounded μ h) : AEBounded μ fun a => - h a := by
  obtain ⟨m1, K1, b1⟩ := h1
  refine ⟨m1.neg, K1, ?_⟩
  filter_upwards [b1] with a x
  simpa using x
theorem AEBounded.sub {h k : α → ℝ} (h1 : AEBounded μ h) (h2 : AEBounded μ k) : AEBounded μ fun a => h a - k a := by
  simpa [sub_eq_add_neg] using h1.add h2.neg
theorem AEBounded.sum {ι : Type} (s : Finset ι) {h : ι → α → ℝ} (h1 : ∀ i ∈ s, AEBounded μ (h i)) :
    AEBounded μ fun a => ∑ i ∈ s, h i a := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨by simpa using aestronglyMeasurable_const, 0, by simp⟩
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (h1 i (Finset.mem_insert_self _ _)).add (ih fun j hj => h1 j (Finset.mem_insert_of_mem hj))
theorem AEBounded.congr {h k : α → ℝ} (h1 : AEBounded μ h) (e : h =ᵐ[μ] k) : AEBounded μ k := by
  obtain ⟨m1, K1, b1⟩ := h1
  refine ⟨m1.congr e, K1, ?_⟩
  filter_upwards [b1, e] with a x y
  rwa [← y]
theorem AEBounded.const (c : ℝ) : AEBounded μ fun _ => c := ⟨aestronglyMeasurable_const, |c|, by simp⟩
theorem AEBounded.exists_common_bound {h k : α → ℝ} (h1 : AEBounded μ h) (h2 : AEBounded μ k) :
    ∃ M : ℝ, (∀ᵐ a ∂μ, |h a| ≤ M) ∧ ∀ᵐ a ∂μ, |k a| ≤ M := by
  obtain ⟨_, K1, b1⟩ := h1
  obtain ⟨_, K2, b2⟩ := h2
  exact ⟨max K1 K2, b1.mono fun a x => x.trans (le_max_left _ _), b2.mono fun a x => x.trans (le_max_right _ _)⟩
end Bounded
section Split
variable {R : StepSetup} {n : ℕ} [NeZero n] {free : Finset (TorusBond (n * R.params.side))}
theorem sum_singleBond (η : FreeCoords free) : ∑ b : free, singleBond b η = η := by
  classical
  funext b'
  rw [Finset.sum_apply]
  simp [singleBond]
theorem continuous_singleBond (b : free) : Continuous (singleBond b : FreeCoords free → FreeCoords free) := by
  classical
  refine continuous_pi fun b' => ?_
  unfold singleBond
  by_cases h : b' = b
  · simp only [h, if_true]
    exact continuous_apply b
  · simp only [h, if_false]
    exact continuous_const
theorem sum_freeBondsAt {M : Type} [AddCommMonoid M] (g : free → M) :
    ∑ Y : TorusSite n, ∑ b ∈ freeBondsAt free Y, g b = ∑ b : free, g b := by
  classical
  have := Finset.sum_fiberwise (s := (Finset.univ : Finset free)) (g := fun b : free => bondBlock (R := R) b.1) g
  rw [← this]
  refine Finset.sum_congr rfl fun Y _ => Finset.sum_congr ?_ fun _ _ => rfl
  ext b
  simp [freeBondsAt]
theorem sum_card_freeBondsAt : ∑ Y : TorusSite n, ((freeBondsAt free Y).card : ℝ) = (Fintype.card free : ℝ) := by
  have := sum_freeBondsAt (R := R) (n := n) (free := free) (fun _ => (1 : ℝ))
  simpa using this
end Split
section Regular
variable {R : StepSetup} {n : ℕ} [NeZero n] {free : Finset (TorusBond (n * R.params.side))}
def gaussianCutoffFactor (R : StepSetup) (lam : ℝ) (z : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  cutoffFactor R.ballRadius R.barrierFn (coordNorm z) * Real.exp (-(R.coupling * lam / 2 * ‖z‖ ^ 2))
theorem aeBounded_of_continuousOn_closedBallsIn {h : FreeCoords free → ℝ}
    (hc : ContinuousOn h (closedBallsIn R free)) :
    AEBounded (volume.restrict (openBallsIn R free)) h := by
  have hBm : MeasurableSet (openBallsIn R free) := isOpen_openBallsIn.measurableSet
  obtain ⟨K, hK⟩ := (isCompact_closedBallsIn (R := R) (free := free)).exists_bound_of_continuousOn hc
  refine ⟨(hc.mono openBallsIn_subset_closedBallsIn).aestronglyMeasurable hBm, K, ?_⟩
  exact ae_restrict_of_forall_mem hBm fun η hη => by simpa using hK η (openBallsIn_subset_closedBallsIn hη)
def BlockDensitySplit.segmentIntegral (D : BlockDensitySplit R n free) (b : free) (η : FreeCoords free) : ℝ :=
  ∫ v in (0 : ℝ)..1, fderiv ℝ D.totalCost (v • η) (singleBond b η)
variable {D : BlockDensitySplit R n free}
theorem interaction_eq (hreg : D.IsRegular) {η : FreeCoords free} (hη : η ∈ closedBallsIn R free)
    (Y : TorusSite n) :
    D.interaction Y η = R.coupling * ∑ b ∈ freeBondsAt free Y, D.segmentIntegral b η
      - D.logJacobian Y η + D.logJacobian Y 0 := by
  obtain ⟨U, hUo, hUb, hC⟩ := hreg.cost_smooth
  have hs : ∑ b ∈ freeBondsAt free Y, ∫ v in (0 : ℝ)..1,
      deriv (fun τ : ℝ => D.totalCost (v • η + τ • singleBond b η)) 0 =
        ∑ b ∈ freeBondsAt free Y, D.segmentIntegral b η := by
    refine Finset.sum_congr rfl fun b _ => ?_
    refine intervalIntegral.integral_congr fun v hv => ?_
    rw [uIcc_of_le zero_le_one] at hv
    exact deriv_comp_add_smul_eq_fderiv hUo hC _ (hUb _ (smul_mem_closedBallsIn hη hv))
  exact congrArg (fun z => R.coupling * z - D.logJacobian Y η + D.logJacobian Y 0) hs
theorem continuousOn_segmentIntegral (hreg : D.IsRegular) (b : free) :
    ContinuousOn (D.segmentIntegral b) (closedBallsIn R free) := by
  obtain ⟨U, hUo, hUb, hC⟩ := hreg.cost_smooth
  exact continuousOn_integral_fderiv_segment isCompact_closedBallsIn hUo hC (fun η hη => hUb η hη)
    (fun η hη v hv => smul_mem_closedBallsIn hη hv) (continuous_singleBond b)
theorem sum_segmentIntegral (hreg : D.IsRegular) {η : FreeCoords free} (hη : η ∈ closedBallsIn R free) :
    ∑ b : free, D.segmentIntegral b η = D.totalCost η - D.totalCost 0 := by
  obtain ⟨U, hUo, hUb, hC⟩ := hreg.cost_smooth
  have hstar : ∀ v ∈ Icc (0 : ℝ) 1, v • η ∈ U := fun v hv => hUb _ (smul_mem_closedBallsIn hη hv)
  unfold BlockDensitySplit.segmentIntegral
  rw [← intervalIntegral.integral_finsetSum fun b _ =>
    intervalIntegrable_fderiv_smul_segment hUo hC hstar (singleBond b η), ← integral_fderiv_smul_segment hUo hC hstar]
  refine intervalIntegral.integral_congr fun v _ => ?_
  show ∑ b : free, fderiv ℝ D.totalCost (v • η) (singleBond b η) = fderiv ℝ D.totalCost (v • η) η
  rw [← map_sum, sum_singleBond]
theorem totalInteraction_eq (hreg : D.IsRegular) {η : FreeCoords free} (hη : η ∈ closedBallsIn R free) :
    D.totalInteraction η = R.coupling * (D.totalCost η - D.totalCost 0)
      - ∑ Y : TorusSite n, D.logJacobian Y η + ∑ Y : TorusSite n, D.logJacobian Y 0 := by
  unfold BlockDensitySplit.totalInteraction
  simp only [interaction_eq hreg hη, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [sum_freeBondsAt (fun b => D.segmentIntegral b η), sum_segmentIntegral hreg hη]
theorem potential_eq (hreg : D.IsRegular) {η : FreeCoords free} (hη : η ∈ closedBallsIn R free) :
    D.potential η = D.totalInteraction η + (R.coupling * D.totalCost 0 - ∑ Y : TorusSite n, D.logJacobian Y 0)
      - ∑ Y : TorusSite n, D.density Y η := by
  rw [totalInteraction_eq hreg hη]
  unfold BlockDensitySplit.potential
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, BlockDensitySplit.totalCost]
  ring
theorem aeBounded_logJacobian (hreg : D.IsRegular) (Y : TorusSite n) :
    AEBounded (volume.restrict (openBallsIn R free)) (D.logJacobian Y) := by
  have hBm : MeasurableSet (openBallsIn R free) := isOpen_openBallsIn.measurableSet
  obtain ⟨M, hM⟩ := hreg.bounded
  exact ⟨(aestronglyMeasurable_indicator_iff hBm).mp (hreg.measurable_logJacobian Y).aestronglyMeasurable, M,
    ae_restrict_of_forall_mem hBm fun η h => (hM η h Y).1⟩
theorem aeBounded_density (hreg : D.IsRegular) (Y : TorusSite n) :
    AEBounded (volume.restrict (openBallsIn R free)) (D.density Y) := by
  have hBm : MeasurableSet (openBallsIn R free) := isOpen_openBallsIn.measurableSet
  obtain ⟨M, hM⟩ := hreg.bounded
  exact ⟨(aestronglyMeasurable_indicator_iff hBm).mp (hreg.measurable_density Y).aestronglyMeasurable, M,
    ae_restrict_of_forall_mem hBm fun η h => (hM η h Y).2⟩
theorem continuous_gaussianPart (lam : ℝ) (Y : TorusSite n) :
    Continuous (gaussianPart (R := R) (free := free) lam Y) := by
  unfold gaussianPart
  fun_prop
theorem aeBounded_gaussianPart (lam : ℝ) (Y : TorusSite n) :
    AEBounded (volume.restrict (openBallsIn R free)) (gaussianPart (R := R) (free := free) lam Y) :=
  aeBounded_of_continuousOn_closedBallsIn (continuous_gaussianPart lam Y).continuousOn
theorem aeBounded_interaction (hreg : D.IsRegular) (Y : TorusSite n) :
    AEBounded (volume.restrict (openBallsIn R free)) (D.interaction Y) := by
  have hBm : MeasurableSet (openBallsIn R free) := isOpen_openBallsIn.measurableSet
  have h1 : AEBounded (volume.restrict (openBallsIn R free))
      fun η => R.coupling * ∑ b ∈ freeBondsAt free Y, D.segmentIntegral b η :=
    aeBounded_of_continuousOn_closedBallsIn
      (continuousOn_const.mul (continuousOn_finsetSum _ fun b _ => continuousOn_segmentIntegral hreg b))
  refine ((h1.sub (aeBounded_logJacobian hreg Y)).add (AEBounded.const (D.logJacobian Y 0))).congr ?_
  exact ae_restrict_of_forall_mem hBm fun η h => (interaction_eq hreg (openBallsIn_subset_closedBallsIn h) Y).symm
end Regular
section Close
variable {R : StepSetup} {n n' : ℕ} [NeZero n] [NeZero n'] {free : Finset (TorusBond (n * R.params.side))}
  {free' : Finset (TorusBond (n' * R.params.side))}
theorem cutoffProd_setup (hρ : 0 < R.ballRadius) (hp : IsCutoff R.ballRadius R.barrierFn) :
    volume.restrict (openBallsIn R free) ≠ 0 ∧ Integrable (cutoffProd (R := R) (free := free))
      (volume.restrict (openBallsIn R free)) ∧
      ∀ᵐ η ∂(volume.restrict (openBallsIn R free)), 0 < cutoffProd (R := R) (free := free) η := by
  have hBm : MeasurableSet (openBallsIn R free) := isOpen_openBallsIn.measurableSet
  have hfin : volume (openBallsIn R free) < ⊤ :=
    (measure_mono openBallsIn_subset_closedBallsIn).trans_lt
      (isCompact_closedBallsIn (R := R) (free := free)).measure_lt_top
  have hfm : IsFiniteMeasure (volume.restrict (openBallsIn R free)) := ⟨by simpa using hfin⟩
  refine ⟨fun h0 => ?_, ?_, ae_restrict_of_forall_mem hBm fun η h => cutoffProd_pos h⟩
  · have h1 : volume (openBallsIn R free) = 0 := Measure.restrict_eq_zero.mp h0
    have h2 : 0 < volume (openBallsIn R free) := isOpen_openBallsIn.measure_pos _ ⟨0, fun b => by
      rw [coordNorm_eq_norm]; simpa using hρ⟩
    exact h2.ne' h1
  · refine Integrable.of_bound (measurable_cutoffProd hp).aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun η => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (cutoffProd_nonneg η)]
    exact cutoffProd_le_one hρ hp η
theorem integral_eq_setIntegral_openBallsIn {h : FreeCoords free → ℝ}
    (hz : ∀ η, η ∉ openBallsIn R free → h η = 0) :
    ∫ η, h η = ∫ η, h η ∂(volume.restrict (openBallsIn R free)) :=
  (setIntegral_eq_integral_of_forall_compl_eq_zero hz).symm
theorem weightedMean_interpolatedDensity_eq (D : BlockDensitySplit R n free) (lam τ : ℝ)
    (G : FreeCoords free → ℝ) :
    weightedMean (D.interpolatedDensity lam τ) G = tiltedMean (volume.restrict (openBallsIn R free)) cutoffProd
      (fun η => -∑ Y : TorusSite n, gaussianPart (R := R) lam Y η)
      (fun η => ∑ Y : TorusSite n, gaussianPart (R := R) lam Y η - D.totalInteraction η) G τ := by
  unfold weightedMean tiltedMean BlockDensitySplit.interpolatedDensity
  have hE : ∀ η, -(τ * D.totalInteraction η) - (1 - τ) * ∑ Y : TorusSite n, gaussianPart (R := R) lam Y η =
      -∑ Y : TorusSite n, gaussianPart (R := R) lam Y η
        + τ * (∑ Y : TorusSite n, gaussianPart (R := R) lam Y η - D.totalInteraction η) := by
    intro η
    ring
  simp only [hE]
  congr 1 <;> exact integral_eq_setIntegral_openBallsIn fun η h => by rw [cutoffProd_eq_zero h]; simp
theorem weightedMean_perturbedDensity_eq (D : BlockDensitySplit R n free) (ν : ℝ) (G : FreeCoords free → ℝ) :
    weightedMean (D.perturbedDensity ν) G = tiltedMean (volume.restrict (openBallsIn R free)) cutoffProd
      (fun η => -D.totalInteraction η) (fun η => ∑ Y : TorusSite n, D.density Y η) G ν := by
  unfold weightedMean tiltedMean BlockDensitySplit.perturbedDensity
  congr 1 <;> exact integral_eq_setIntegral_openBallsIn fun η h => by rw [cutoffProd_eq_zero h]; simp
theorem continuous_weightedMean_interpolatedDensity (hcore : LogIntegralExpInterpolationStatement)
    (hρ : 0 < R.ballRadius) (hp : IsCutoff R.ballRadius R.barrierFn) {D : BlockDensitySplit R n free}
    (hreg : D.IsRegular) (lam : ℝ) {G : FreeCoords free → ℝ}
    (hG : AEBounded (volume.restrict (openBallsIn R free)) G) :
    Continuous fun τ => weightedMean (D.interpolatedDensity lam τ) G := by
  obtain ⟨hμ, hw, hw0⟩ := cutoffProd_setup (R := R) (free := free) hρ hp
  have hPsi : AEBounded (volume.restrict (openBallsIn R free)) D.totalInteraction :=
    AEBounded.sum _ fun Y _ => aeBounded_interaction hreg Y
  have hQ : AEBounded (volume.restrict (openBallsIn R free))
      fun η => ∑ Y : TorusSite n, gaussianPart (R := R) lam Y η :=
    AEBounded.sum _ fun Y _ => aeBounded_gaussianPart lam Y
  have hf := hQ.neg
  have hg := hQ.sub hPsi
  obtain ⟨M, a, b⟩ := hf.exists_common_bound hg
  have := (hcore _ cutoffProd _ _ M hμ hw hw0 hf.1 hg.1 a b).2.1 G hG.1 hG.2
  simp only [weightedMean_interpolatedDensity_eq]
  exact this
theorem continuous_weightedMean_perturbedDensity (hcore : LogIntegralExpInterpolationStatement)
    (hρ : 0 < R.ballRadius) (hp : IsCutoff R.ballRadius R.barrierFn) {D : BlockDensitySplit R n free}
    (hreg : D.IsRegular) {G : FreeCoords free → ℝ}
    (hG : AEBounded (volume.restrict (openBallsIn R free)) G) :
    Continuous fun ν => weightedMean (D.perturbedDensity ν) G := by
  obtain ⟨hμ, hw, hw0⟩ := cutoffProd_setup (R := R) (free := free) hρ hp
  have hPsi : AEBounded (volume.restrict (openBallsIn R free)) D.totalInteraction :=
    AEBounded.sum _ fun Y _ => aeBounded_interaction hreg Y
  have hΦ : AEBounded (volume.restrict (openBallsIn R free)) fun η => ∑ Y : TorusSite n, D.density Y η :=
    AEBounded.sum _ fun Y _ => aeBounded_density hreg Y
  have hf := hPsi.neg
  obtain ⟨M, a, b⟩ := hf.exists_common_bound hΦ
  have := (hcore _ cutoffProd _ _ M hμ hw hw0 hf.1 hΦ.1 a b).2.1 G hG.1 hG.2
  simp only [weightedMean_perturbedDensity_eq]
  exact this
theorem abs_sub_integral_div_le {α : Type} [MeasurableSpace α] {μ : Measure α} {d G H : α → ℝ} {ε : ℝ}
    (hd0 : ∀ a, 0 ≤ d a) (hint : Integrable d μ) (hpos : 0 < ∫ a, d a ∂μ)
    (hG : Integrable (fun a => G a * d a) μ) (hH : Integrable (fun a => H a * d a) μ)
    (hclose : ∀ a, d a ≠ 0 → |G a - H a| ≤ ε) :
    |(∫ a, G a * d a ∂μ) / (∫ a, d a ∂μ) - (∫ a, H a * d a ∂μ) / ∫ a, d a ∂μ| ≤ ε := by
  rw [← sub_div, abs_div, abs_of_pos hpos, div_le_iff₀ hpos, ← integral_sub hG hH]
  calc |∫ a, (G a * d a - H a * d a) ∂μ| ≤ ∫ a, |G a * d a - H a * d a| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ a, ε * d a ∂μ := by
        refine integral_mono (hG.sub hH).abs (hint.const_mul _) fun a => ?_
        by_cases h : d a = 0
        · simp [h]
        · have : G a * d a - H a * d a = (G a - H a) * d a := by ring
          simp only [this, abs_mul, abs_of_nonneg (hd0 a)]
          exact mul_le_mul_of_nonneg_right (hclose a h) (hd0 a)
    _ = ε * ∫ a, d a ∂μ := integral_const_mul _ _
theorem abs_activity_sub_le {D : BlockDensitySplit R n free} {D' : BlockDensitySplit R n' free'}
    {lam e₀ e₁ e₂ : ℝ} {Y : TorusSite n} {Y' : TorusSite n'}
    (h0 : |R.coupling * D.cost Y 0 - R.coupling * D'.cost Y' 0| ≤ e₀) (hj : D.logJacobian Y 0 = D'.logJacobian Y' 0)
    (hc : (freeBondsAt free Y).card = (freeBondsAt free' Y').card)
    (hτ : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      |weightedMean (D.interpolatedDensity lam τ) (fun η => D.interaction Y η - gaussianPart lam Y η) -
        weightedMean (D'.interpolatedDensity lam τ) (fun η => D'.interaction Y' η - gaussianPart lam Y' η)| ≤ e₁)
    (hν : ∀ ν ∈ Set.Icc (0 : ℝ) 1,
      |weightedMean (D.perturbedDensity ν) (D.density Y) - weightedMean (D'.perturbedDensity ν) (D'.density Y')| ≤ e₂)
    (c₁ : Continuous fun τ =>
      weightedMean (D.interpolatedDensity lam τ) (fun η => D.interaction Y η - gaussianPart lam Y η))
    (c₂ : Continuous fun τ =>
      weightedMean (D'.interpolatedDensity lam τ) (fun η => D'.interaction Y' η - gaussianPart lam Y' η))
    (c₃ : Continuous fun ν => weightedMean (D.perturbedDensity ν) (D.density Y))
    (c₄ : Continuous fun ν => weightedMean (D'.perturbedDensity ν) (D'.density Y')) :
    |D.activity lam Y - D'.activity lam Y'| ≤ e₀ + e₁ + e₂ := by
  have hI₁ : |(∫ τ in (0 : ℝ)..1,
        weightedMean (D.interpolatedDensity lam τ) fun η => D.interaction Y η - gaussianPart lam Y η) -
      ∫ τ in (0 : ℝ)..1,
        weightedMean (D'.interpolatedDensity lam τ) fun η => D'.interaction Y' η - gaussianPart lam Y' η| ≤ e₁ := by
    rw [← intervalIntegral.integral_sub (c₁.intervalIntegrable _ _) (c₂.intervalIntegrable _ _)]
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1) (C := e₁)
      (f := fun τ => weightedMean (D.interpolatedDensity lam τ) (fun η => D.interaction Y η - gaussianPart lam Y η) -
        weightedMean (D'.interpolatedDensity lam τ) (fun η => D'.interaction Y' η - gaussianPart lam Y' η))
      (fun τ hτ' => by
        rw [uIoc_of_le zero_le_one] at hτ'
        exact hτ τ (Ioc_subset_Icc_self hτ'))
    simpa using this
  have hI₂ : |(∫ ν in (0 : ℝ)..1, weightedMean (D.perturbedDensity ν) (D.density Y)) -
      ∫ ν in (0 : ℝ)..1, weightedMean (D'.perturbedDensity ν) (D'.density Y')| ≤ e₂ := by
    rw [← intervalIntegral.integral_sub (c₃.intervalIntegrable _ _) (c₄.intervalIntegrable _ _)]
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1) (C := e₂)
      (f := fun ν => weightedMean (D.perturbedDensity ν) (D.density Y) -
        weightedMean (D'.perturbedDensity ν) (D'.density Y'))
      (fun ν hν' => by
        rw [uIoc_of_le zero_le_one] at hν'
        exact hν ν (Ioc_subset_Icc_self hν'))
    simpa using this
  unfold BlockDensitySplit.activity
  rw [hj, hc]
  rw [abs_le] at h0 hI₁ hI₂ ⊢
  constructor <;> linarith [h0.1, h0.2, hI₁.1, hI₁.2, hI₂.1, hI₂.2]
end Close
end YangMills.Construction.ClusterExpansionOfAStep
end
