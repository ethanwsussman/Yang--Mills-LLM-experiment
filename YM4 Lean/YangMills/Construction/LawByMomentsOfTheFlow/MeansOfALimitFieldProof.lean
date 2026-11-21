import YangMills.Construction.LawByMomentsOfTheFlow.ScoresInALimitFieldProof
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped Topology ENNReal
namespace YangMills.Construction.MomentMethod
section MeanErgodic
variable {Ω : Type} [m0 : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {T : Ω → Ω}
private def invariantSigma (T : Ω → Ω) : MeasurableSpace Ω := MeasurableSpace.invariants T ⊓ m0
private theorem invariantSigma_le : invariantSigma T ≤ m0 := inf_le_right
private def koopmanOp (hT : MeasurePreserving T P P) : Lp ℝ 2 P →L[ℝ] Lp ℝ 2 P :=
  (Lp.compMeasurePreservingₗᵢ ℝ T hT).toContinuousLinearMap
private theorem koopmanOp_coeFn (hT : MeasurePreserving T P P) (x : Lp ℝ 2 P) : koopmanOp hT x =ᵐ[P] x ∘ T :=
  Lp.coeFn_compMeasurePreserving x hT
private theorem koopmanOp_iterate_coeFn (hT : MeasurePreserving T P P) (x : Lp ℝ 2 P) (k : ℕ) :
    ((koopmanOp hT)^[k] x : Lp ℝ 2 P) =ᵐ[P] x ∘ T^[k] := by
  induction k with
  | zero => exact Filter.EventuallyEq.rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    have h1 := koopmanOp_coeFn hT ((koopmanOp hT)^[k] x)
    have h2 : (((koopmanOp hT)^[k] x : Lp ℝ 2 P) ∘ T) =ᵐ[P] (x ∘ T^[k]) ∘ T := hT.quasiMeasurePreserving.ae_eq_comp ih
    refine h1.trans (h2.trans (Filter.Eventually.of_forall fun ω => ?_))
    simp [Function.comp, Function.iterate_succ_apply]
private theorem birkhoffAverage_koopmanOp_coeFn (hT : MeasurePreserving T P P) (x : Lp ℝ 2 P) (M : ℕ) :
    (birkhoffAverage ℝ (koopmanOp hT) _root_.id M x : Lp ℝ 2 P) =ᵐ[P]
      fun ω => (M : ℝ)⁻¹ * ∑ k ∈ Finset.range M, x (T^[k] ω) := by
  have hsum : ∀ M : ℕ, (birkhoffSum (koopmanOp hT) _root_.id M x : Lp ℝ 2 P) =ᵐ[P]
      fun ω => ∑ k ∈ Finset.range M, x (T^[k] ω) := by
    intro M
    induction M with
    | zero =>
      simp only [birkhoffSum, Finset.range_zero, Finset.sum_empty]
      exact Lp.coeFn_zero _ _ _
    | succ M ih =>
      rw [birkhoffSum_succ]
      refine (Lp.coeFn_add _ _).trans ?_
      filter_upwards [ih, koopmanOp_iterate_coeFn hT x M] with ω h1 h2
      simp only [Pi.add_apply, id, h1, h2, Finset.sum_range_succ, Function.comp]
  unfold birkhoffAverage
  refine (Lp.coeFn_smul _ _).trans ?_
  filter_upwards [hsum M] with ω h1
  simp [h1]
private theorem aestronglyMeasurable_invariantSigma_of_fixed (hT : MeasurePreserving T P P) (g : Lp ℝ 2 P)
    (hg : koopmanOp hT g = g) : AEStronglyMeasurable[invariantSigma T] g P := by
  obtain ⟨g', hg'm, hg'⟩ := (Lp.aestronglyMeasurable g).aemeasurable
  obtain ⟨G, hG⟩ : ∃ G : Ω → ℝ, G = fun ω => limsup (fun n => g' (T^[n] ω)) atTop := ⟨_, rfl⟩
  have hGm : Measurable G := by
    rw [hG]
    exact Measurable.limsup fun n => hg'm.comp (hT.measurable.iterate n)
  have hGT : ∀ ω, G (T ω) = G ω := by
    intro ω
    rw [hG]
    have := Filter.limsup_nat_add (fun n => g' (T^[n] ω)) 1
    simp only [Function.iterate_succ_apply] at this
    exact this
  have hfix : ∀ n, g' ∘ T^[n] =ᵐ[P] g' := by
    intro n
    have h1 : ((koopmanOp hT)^[n] g : Lp ℝ 2 P) = g := by
      have : Function.IsFixedPt (koopmanOp hT) g := hg
      exact (this.iterate n)
    have h2 := koopmanOp_iterate_coeFn hT g n
    rw [h1] at h2
    have h3 : g ∘ T^[n] =ᵐ[P] g' ∘ T^[n] := (hT.iterate n).quasiMeasurePreserving.ae_eq_comp hg'
    exact (h3.symm.trans h2.symm).trans hg'
  have hall : ∀ᵐ ω ∂P, ∀ n, g' (T^[n] ω) = g' ω := ae_all_iff.mpr hfix
  have hae : g =ᵐ[P] G := by
    filter_upwards [hg', hall] with ω h1 h2
    rw [h1, hG]
    simp only [h2, limsup_const]
  have hinv : Measurable[invariantSigma T] G := by
    intro B hB
    refine ⟨?_, hGm hB⟩
    show MeasurableSet[MeasurableSpace.invariants T] _
    rw [MeasurableSpace.measurableSet_invariants]
    refine ⟨hGm hB, ?_⟩
    ext ω
    simp [hGT]
  exact ⟨G, hinv.stronglyMeasurable, hae⟩
private abbrev fixedSubspace (hT : MeasurePreserving T P P) : Submodule ℝ (Lp ℝ 2 P) :=
  ((koopmanOp hT).eqLocus (1 : Lp ℝ 2 P →L[ℝ] Lp ℝ 2 P) : Submodule ℝ (Lp ℝ 2 P))
private theorem exists_fixed_eq_condExp (hT : MeasurePreserving T P P) {f : Ω → ℝ} (hf : MemLp f 2 P) :
    ∃ g : Lp ℝ 2 P, g =ᵐ[P] P[f | invariantSigma T] ∧ koopmanOp hT g = g ∧ inner ℝ g (hf.toLp f) = inner ℝ g g ∧
      Tendsto (fun M : ℕ => birkhoffAverage ℝ (koopmanOp hT) _root_.id M (hf.toLp f)) atTop (𝓝 g) := by
  obtain ⟨x, hx⟩ : ∃ x : Lp ℝ 2 P, x = hf.toLp f := ⟨_, rfl⟩
  have hxf : x =ᵐ[P] f := hx ▸ hf.coeFn_toLp
  have hnorm : ‖koopmanOp hT‖ ≤ 1 := LinearIsometry.norm_toContinuousLinearMap_le _
  have hlim := ContinuousLinearMap.tendsto_birkhoffAverage_orthogonalProjection (koopmanOp hT) hnorm x
  obtain ⟨g, hg⟩ : ∃ g : Lp ℝ 2 P, g = ((fixedSubspace hT).orthogonalProjectionOnto x : Lp ℝ 2 P) := ⟨_, rfl⟩
  have hgK : g ∈ fixedSubspace hT := hg ▸ ((fixedSubspace hT).orthogonalProjectionOnto x).2
  have hmemK : ∀ u : Lp ℝ 2 P, u ∈ fixedSubspace hT ↔ koopmanOp hT u = u := fun u => by
    simp [fixedSubspace, LinearMap.mem_eqLocus]
  have hfix : koopmanOp hT g = g := (hmemK g).mp hgK
  have horth : ∀ u ∈ fixedSubspace hT, inner ℝ u (x - g) = 0 := by
    intro u hu
    have := (fixedSubspace hT).sub_starProjection_mem_orthogonal x
    rw [Submodule.mem_orthogonal] at this
    rw [hg]
    exact this u hu
  refine ⟨g, ?_, hfix, ?_, ?_⟩
  · refine ae_eq_condExp_of_forall_setIntegral_eq invariantSigma_le (hf.integrable one_le_two)
      (fun s _ _ => (Lp.memLp g).integrable one_le_two |>.integrableOn) (fun s hs _ => ?_)
      (aestronglyMeasurable_invariantSigma_of_fixed hT g hfix)
    obtain ⟨hs1, hs2⟩ := hs
    have hs1' : T ⁻¹' s = s := ((MeasurableSpace.measurableSet_invariants).mp hs1).2
    obtain ⟨u, hu⟩ : ∃ u : Lp ℝ 2 P, u = indicatorConstLp 2 hs2 (measure_ne_top P s) (1 : ℝ) := ⟨_, rfl⟩
    have huK : u ∈ fixedSubspace hT := by
      rw [hmemK]
      apply Lp.ext
      have h1 := koopmanOp_coeFn hT u
      have h2 : (u : Ω → ℝ) =ᵐ[P] s.indicator fun _ => (1 : ℝ) := hu ▸ indicatorConstLp_coeFn
      have h3 : (u : Ω → ℝ) ∘ T =ᵐ[P] (s.indicator fun _ => (1 : ℝ)) ∘ T := hT.quasiMeasurePreserving.ae_eq_comp h2
      have h4 : (s.indicator fun _ => (1 : ℝ)) ∘ T = s.indicator fun _ => (1 : ℝ) := by
        funext ω
        have : T ω ∈ s ↔ ω ∈ s := by
          conv_rhs => rw [← hs1']
          rfl
        simp only [Function.comp, Set.indicator]
        by_cases h : ω ∈ s
        · rw [if_pos h, if_pos (this.mpr h)]
        · rw [if_neg h, if_neg fun h' => h (this.mp h')]
      rw [h4] at h3
      exact h1.trans (h3.trans h2.symm)
    have h0 := horth u huK
    rw [inner_sub_right, hu, L2.inner_indicatorConstLp_one, L2.inner_indicatorConstLp_one] at h0
    have hxs : ∫ ω in s, x ω ∂P = ∫ ω in s, f ω ∂P := setIntegral_congr_ae hs2 (hxf.mono fun ω h _ => h)
    linarith
  · have h0 := horth g hgK
    rw [inner_sub_right] at h0
    rw [← hx]
    linarith
  · rw [← hx, hg]
    exact hlim
private theorem tendsto_eLpNorm_birkhoff_sub_condExp (hT : MeasurePreserving T P P) {f : Ω → ℝ} (hf : MemLp f 2 P) :
    Tendsto (fun M : ℕ => eLpNorm (fun ω => (M : ℝ)⁻¹ * ∑ k ∈ Finset.range M, f (T^[k] ω) - (P[f | invariantSigma T]) ω) 2 P)
      atTop (𝓝 0) := by
  obtain ⟨g, hg, -, -, hlim⟩ := exists_fixed_eq_condExp hT hf
  have h1 := (Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ _).mp hlim
  refine h1.congr fun M => eLpNorm_congr_ae ?_
  have hxf : (hf.toLp f : Ω → ℝ) =ᵐ[P] f := hf.coeFn_toLp
  have hall : ∀ᵐ ω ∂P, ∀ k, (hf.toLp f : Ω → ℝ) (T^[k] ω) = f (T^[k] ω) :=
    ae_all_iff.mpr fun k => (hT.iterate k).quasiMeasurePreserving.ae hxf
  filter_upwards [birkhoffAverage_koopmanOp_coeFn hT (hf.toLp f) M, hg, hall] with ω h2 h3 h4
  simp only [Pi.sub_apply, h2, h3, h4]
end MeanErgodic
section Truncation
private def truncate (R y : ℝ) : ℝ := max (-R) (min y R)
private theorem continuous_truncate (R : ℝ) : Continuous (truncate R) := by
  unfold truncate
  fun_prop
private theorem abs_truncate_le {R : ℝ} (hR : 0 ≤ R) (y : ℝ) : |truncate R y| ≤ R := by
  unfold truncate
  rw [abs_le]
  constructor
  · exact le_max_left _ _
  · exact max_le (by linarith) (min_le_right _ _)
private theorem abs_sub_truncate_le {R : ℝ} (hR : 0 < R) (y : ℝ) : |y - truncate R y| ≤ y ^ 2 / R := by
  rw [le_div_iff₀ hR]
  unfold truncate
  rcases le_total y (-R) with h | h
  · have h1 : min y R = y := min_eq_left (by linarith)
    have h2 : max (-R) y = -R := max_eq_left h
    rw [h1, h2, abs_of_nonpos (by linarith)]
    nlinarith
  · rcases le_total y R with h' | h'
    · have h1 : min y R = y := min_eq_left h'
      have h2 : max (-R) y = y := max_eq_right h
      rw [h1, h2, sub_self, abs_zero, zero_mul]
      positivity
    · have h1 : min y R = R := min_eq_right h'
      have h2 : max (-R) R = R := max_eq_right (by linarith)
      rw [h1, h2, abs_of_nonneg (by linarith)]
      nlinarith
private theorem prod_le_one_add_sum_pow {l : ℕ} (t : Fin l → ℝ) (ht : ∀ c, 0 ≤ t c) : ∏ c, t c ≤ 1 + ∑ c, t c ^ l := by
  have hs : 0 ≤ ∑ c, t c ^ l := Finset.sum_nonneg fun c _ => pow_nonneg (ht c) _
  rcases Nat.eq_zero_or_pos l with rfl | hl
  · simp
  · haveI : Nonempty (Fin l) := ⟨⟨0, hl⟩⟩
    obtain ⟨c₀, -, hc₀⟩ := Finset.exists_max_image Finset.univ t Finset.univ_nonempty
    have h1 : ∏ c, t c ≤ t c₀ ^ l := by
      calc ∏ c, t c ≤ ∏ _c : Fin l, t c₀ := Finset.prod_le_prod (fun c _ => ht c) fun c _ => hc₀ c (Finset.mem_univ c)
        _ = t c₀ ^ l := by simp
    have h2 : t c₀ ^ l ≤ ∑ c, t c ^ l :=
      Finset.single_le_sum (f := fun c => t c ^ l) (fun c _ => pow_nonneg (ht c) _) (Finset.mem_univ c₀)
    linarith
variable {Ω : Type} [MeasurableSpace Ω] {ν : Measure Ω} [IsProbabilityMeasure ν]
private theorem memLp_two_of_lintegral_sq_le {Y : Ω → ℝ} {M : ℝ} (hY : AEStronglyMeasurable Y ν) (hM : 0 ≤ M)
    (hb : ∫⁻ ω, ENNReal.ofReal (Y ω ^ 2) ∂ν ≤ ENNReal.ofReal M) : MemLp Y 2 ν ∧ ∫ ω, Y ω ^ 2 ∂ν ≤ M := by
  have hsq : Integrable (fun ω => Y ω ^ 2) ν := by
    refine ⟨hY.pow 2, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun ω => sq_nonneg _)]
    exact hb.trans_lt ENNReal.ofReal_lt_top
  refine ⟨(memLp_two_iff_integrable_sq hY).2 hsq, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun ω => sq_nonneg _) (hY.pow 2)]
  exact ENNReal.toReal_le_of_le_ofReal hM hb
private theorem abs_integral_sub_truncate_le {Y : Ω → ℝ} {M R : ℝ} (hY : AEStronglyMeasurable Y ν) (hM : 0 ≤ M) (hR : 0 < R)
    (hb : ∫⁻ ω, ENNReal.ofReal (Y ω ^ 2) ∂ν ≤ ENNReal.ofReal M) :
    |∫ ω, Y ω ∂ν - ∫ ω, truncate R (Y ω) ∂ν| ≤ M / R := by
  obtain ⟨h2, hM2⟩ := memLp_two_of_lintegral_sq_le hY hM hb
  have hI : Integrable Y ν := h2.integrable one_le_two
  have hC : Integrable (fun ω => truncate R (Y ω)) ν := by
    refine Integrable.of_bound ((continuous_truncate R).comp_aestronglyMeasurable hY) R
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs]
    exact abs_truncate_le hR.le _
  have hsq : Integrable (fun ω => Y ω ^ 2 / R) ν := ((memLp_two_iff_integrable_sq hY).1 h2).div_const R
  rw [← integral_sub hI hC]
  refine (abs_integral_le_integral_abs).trans ?_
  calc ∫ ω, |Y ω - truncate R (Y ω)| ∂ν ≤ ∫ ω, Y ω ^ 2 / R ∂ν :=
        integral_mono (hI.sub hC).abs hsq fun ω => abs_sub_truncate_le hR _
    _ = (∫ ω, Y ω ^ 2 ∂ν) / R := integral_div _ _
    _ ≤ M / R := div_le_div_of_nonneg_right hM2 hR.le
end Truncation
section LimitLaw
variable {T : TranslatedLaws} {J : Type} [Countable J] {X : J → T.Family} {P : Measure (TranslateValues J)}
private theorem translate_succ (Y : T.Family) (k i : ℕ) (ω : T.Ω i) :
    TranslatedLaws.translate Y (k + 1) i ω = TranslatedLaws.translate Y k i (T.τ i ω) := by
  simp only [TranslatedLaws.translate, Function.iterate_succ_apply]
private theorem aemeasurable_translate (hT : T.IsPreserving) {Y : T.Family} (hY : TranslatedLaws.HasBoundedMoments Y)
    (k i : ℕ) : AEMeasurable (TranslatedLaws.translate Y k i) (T.μ i) :=
  (hY.aemeasurable i).comp_quasiMeasurePreserving ((hT.measurePreserving i).iterate k).quasiMeasurePreserving
private theorem lintegral_abs_pow_translate (hT : T.IsPreserving) {Y : T.Family} (hY : TranslatedLaws.HasBoundedMoments Y)
    (q k i : ℕ) :
    ∫⁻ ω, ENNReal.ofReal (|TranslatedLaws.translate Y k i ω| ^ q) ∂(T.μ i) = ∫⁻ ω, ENNReal.ofReal (|Y i ω| ^ q) ∂(T.μ i) := by
  have hp := (hT.measurePreserving i).iterate k
  have hm : AEMeasurable (fun ω => ENNReal.ofReal (|Y i ω| ^ q)) (T.μ i) :=
    ENNReal.measurable_ofReal.comp_aemeasurable ((continuous_abs.measurable.comp_aemeasurable (hY.aemeasurable i)).pow_const q)
  have := lintegral_map' (μ := T.μ i) (f := fun ω => ENNReal.ofReal (|Y i ω| ^ q)) (g := (T.τ i)^[k])
    (by rw [hp.map_eq]; exact hm) hp.measurable.aemeasurable
  rw [hp.map_eq] at this
  exact this.symm
private def translateTuple (X : J → T.Family) {l : ℕ} (a : Fin l → J × ℕ) (i : ℕ) (ω : T.Ω i) : Fin l → ℝ :=
  fun c => TranslatedLaws.translate (X (a c).1) (a c).2 i ω
private theorem aemeasurable_translateTuple (hT : T.IsPreserving) (hX : ∀ j, TranslatedLaws.HasBoundedMoments (X j))
    {l : ℕ} (a : Fin l → J × ℕ) (i : ℕ) : AEMeasurable (translateTuple X a i) (T.μ i) :=
  aemeasurable_pi_lambda _ fun c => aemeasurable_translate hT (hX _) _ i
private theorem measurePreserving_translateShift (hT : T.IsPreserving) (hX : ∀ j, TranslatedLaws.HasBoundedMoments (X j))
    (hP : IsJointLimitLaw T X P) : MeasurePreserving (translateShift (J := J)) P P := by
  haveI := hP.isProbability
  have hm : Measurable (translateShift (J := J)) := measurable_pi_lambda _ fun a => measurable_pi_apply _
  refine ⟨hm, ?_⟩
  refine IsProjectiveLimit.unique (P := fun I : Finset (J × ℕ) => P.map I.restrict) (fun I => ?_) (fun I => rfl)
  have hr : Measurable (I.restrict : TranslateValues J → (I → ℝ)) := Finset.measurable_restrict I
  rw [Measure.map_map hr hm]
  haveI : IsProbabilityMeasure (P.map (I.restrict ∘ translateShift (J := J))) :=
    Measure.isProbabilityMeasure_map (hr.comp hm).aemeasurable
  haveI : IsProbabilityMeasure (P.map (I.restrict : TranslateValues J → (I → ℝ))) :=
    Measure.isProbabilityMeasure_map hr.aemeasurable
  refine ext_of_forall_integral_eq_of_IsFiniteMeasure fun f => ?_
  rw [integral_map (hr.comp hm).aemeasurable f.continuous.aestronglyMeasurable,
    integral_map hr.aemeasurable f.continuous.aestronglyMeasurable]
  obtain ⟨e⟩ : Nonempty (I ≃ Fin I.card) := ⟨I.equivFin⟩
  obtain ⟨a, ha⟩ : ∃ a : Fin I.card → J × ℕ, ∀ c, a c = ((e.symm c : I) : J × ℕ) := ⟨_, fun _ => rfl⟩
  obtain ⟨a', ha'⟩ : ∃ a' : Fin I.card → J × ℕ, ∀ c, a' c = ((a c).1, (a c).2 + 1) := ⟨_, fun _ => rfl⟩
  obtain ⟨G, hGd⟩ : ∃ G : (Fin I.card → ℝ) → ℝ, G = fun w => f fun j => w (e j) := ⟨_, rfl⟩
  have hG : Continuous G := by
    rw [hGd]
    exact f.continuous.comp (continuous_pi fun j => continuous_apply _)
  have hGb : ∃ C : ℝ, ∀ w, |G w| ≤ C := ⟨‖f‖, fun w => by
    rw [hGd]
    exact f.norm_coe_le_norm _⟩
  have lim1 := hP.tendsto I.card a G hG hGb
  have lim2 := hP.tendsto I.card a' G hG hGb
  have hseq : ∀ i, ∫ ω, G (fun c => TranslatedLaws.translate (X (a' c).1) (a' c).2 i ω) ∂(T.μ i) =
      ∫ ω, G (fun c => TranslatedLaws.translate (X (a c).1) (a c).2 i ω) ∂(T.μ i) := by
    intro i
    have hp := hT.measurePreserving i
    have hH : AEStronglyMeasurable (fun ω => G (translateTuple X a i ω)) (T.μ i) :=
      hG.comp_aestronglyMeasurable (aemeasurable_translateTuple hT hX a i).aestronglyMeasurable
    have h1 := integral_map (μ := T.μ i) hp.aemeasurable (f := fun ω => G (translateTuple X a i ω))
      (by rw [hp.map_eq]; exact hH)
    rw [hp.map_eq] at h1
    refine Eq.trans ?_ h1.symm
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    show G _ = G _
    congr 1
    funext c
    rw [ha', translateTuple]
    exact translate_succ _ _ _ _
  have heq : ∫ v, G (fun c => v (a' c)) ∂P = ∫ v, G (fun c => v (a c)) ∂P :=
    tendsto_nhds_unique (lim2.congr hseq) lim1
  have e1 : ∀ v : TranslateValues J, f ((I.restrict ∘ translateShift (J := J)) v) = G fun c => v (a' c) := by
    intro v
    rw [hGd]
    congr 1
    funext j
    simp [ha', ha, translateShift, Finset.restrict]
  have e2 : ∀ v : TranslateValues J, f (I.restrict v) = G fun c => v (a c) := by
    intro v
    rw [hGd]
    congr 1
    funext j
    simp [ha, Finset.restrict]
  simp_rw [e1, e2]
  exact heq
private theorem ae_eq_zero_of_eventually_eq_zero (hP : IsJointLimitLaw T X P) {l : ℕ} (a : Fin l → J × ℕ)
    (G : (Fin l → ℝ) → ℝ) (hG : Continuous G)
    (h : ∀ᶠ i in atTop, ∀ ω, G (fun c => TranslatedLaws.translate (X (a c).1) (a c).2 i ω) = 0) :
    ∀ᵐ v ∂P, G (fun c => v (a c)) = 0 := by
  haveI := hP.isProbability
  obtain ⟨G', hG'⟩ : ∃ G' : (Fin l → ℝ) → ℝ, G' = fun w => min |G w| 1 := ⟨_, rfl⟩
  have hc : Continuous G' := by
    rw [hG']
    exact (continuous_abs.comp hG).min continuous_const
  have hb : ∃ C : ℝ, ∀ w, |G' w| ≤ C := ⟨1, fun w => by
    rw [hG', abs_of_nonneg (le_min (abs_nonneg _) zero_le_one)]
    exact min_le_right _ _⟩
  have lim := hP.tendsto l a G' hc hb
  have hz : Tendsto (fun i => ∫ ω, G' (fun c => TranslatedLaws.translate (X (a c).1) (a c).2 i ω) ∂(T.μ i)) atTop (𝓝 0) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [h] with i hi
    simp [hG', hi]
  have h0 := tendsto_nhds_unique lim hz
  have hm : Measurable fun v : TranslateValues J => G' fun c => v (a c) :=
    (hc.comp (continuous_pi fun c => continuous_apply (a c))).measurable
  have hnn : ∀ v : TranslateValues J, 0 ≤ G' fun c => v (a c) := fun v => by
    rw [hG']
    exact le_min (abs_nonneg _) zero_le_one
  have hint : Integrable (fun v : TranslateValues J => G' fun c => v (a c)) P := by
    obtain ⟨C, hC⟩ := hb
    exact Integrable.of_bound hm.aestronglyMeasurable C (Filter.Eventually.of_forall fun v => by
      rw [Real.norm_eq_abs]
      exact hC _)
  have := (integral_eq_zero_iff_of_nonneg hnn hint).mp h0
  filter_upwards [this] with v hv
  have hv' : min |G fun c => v (a c)| 1 = 0 := by
    have : G' (fun c => v (a c)) = 0 := hv
    rwa [hG'] at this
  rcases min_choice |G fun c => v (a c)| 1 with h1 | h1
  · rw [h1] at hv'
    exact abs_eq_zero.mp hv'
  · rw [h1] at hv'
    exact absurd hv' one_ne_zero
end LimitLaw
section LimitLawMoments
variable {T : TranslatedLaws} {J : Type} [Countable J] {X : J → T.Family} {P : Measure (TranslateValues J)}
private theorem exists_lintegral_sq_prod_le (hT : T.IsPreserving) (hX : ∀ j, TranslatedLaws.HasBoundedMoments (X j))
    {l : ℕ} (a : Fin l → J × ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ i, ∫⁻ ω, ENNReal.ofReal ((∏ c, translateTuple X a i ω c) ^ 2) ∂(T.μ i) ≤ ENNReal.ofReal M := by
  choose C hC using fun c => (hX (a c).1).moment_bound (2 * l)
  refine ⟨1 + ∑ c, |C c|, by positivity, fun i => ?_⟩
  haveI := hT.isProbability i
  have hpt : ∀ ω, ENNReal.ofReal ((∏ c, translateTuple X a i ω c) ^ 2) ≤
      1 + ∑ c, ENNReal.ofReal (|translateTuple X a i ω c| ^ (2 * l)) := by
    intro ω
    have h1 : (∏ c, translateTuple X a i ω c) ^ 2 ≤ 1 + ∑ c, |translateTuple X a i ω c| ^ (2 * l) := by
      rw [← Finset.prod_pow]
      refine (prod_le_one_add_sum_pow _ fun c => sq_nonneg _).trans (le_of_eq ?_)
      congr 1
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [pow_mul, sq_abs]
    refine (ENNReal.ofReal_le_ofReal h1).trans (le_of_eq ?_)
    rw [ENNReal.ofReal_add zero_le_one (Finset.sum_nonneg fun c _ => by positivity), ENNReal.ofReal_one,
      ENNReal.ofReal_sum_of_nonneg fun c _ => by positivity]
  have hmeas : ∀ c ∈ (Finset.univ : Finset (Fin l)),
      AEMeasurable (fun ω => ENNReal.ofReal (|translateTuple X a i ω c| ^ (2 * l))) (T.μ i) :=
    fun c _ => ENNReal.measurable_ofReal.comp_aemeasurable
      ((continuous_abs.measurable.comp_aemeasurable (aemeasurable_translate hT (hX (a c).1) (a c).2 i)).pow_const _)
  calc ∫⁻ ω, ENNReal.ofReal ((∏ c, translateTuple X a i ω c) ^ 2) ∂(T.μ i)
      ≤ ∫⁻ ω, (1 + ∑ c, ENNReal.ofReal (|translateTuple X a i ω c| ^ (2 * l))) ∂(T.μ i) := lintegral_mono hpt
    _ = 1 + ∑ c, ∫⁻ ω, ENNReal.ofReal (|translateTuple X a i ω c| ^ (2 * l)) ∂(T.μ i) := by
        rw [lintegral_add_left measurable_const, lintegral_const, lintegral_finset_sum' _ hmeas]
        simp
    _ ≤ 1 + ∑ c, ENNReal.ofReal |C c| := by
        gcongr with c
        have h2 := lintegral_abs_pow_translate hT (hX (a c).1) (2 * l) (a c).2 i
        have h3 : ∫⁻ ω, ENNReal.ofReal (|translateTuple X a i ω c| ^ (2 * l)) ∂(T.μ i) =
            ∫⁻ ω, ENNReal.ofReal (|TranslatedLaws.translate (X (a c).1) (a c).2 i ω| ^ (2 * l)) ∂(T.μ i) := rfl
        rw [h3, h2]
        exact (hC c i).trans (ENNReal.ofReal_le_ofReal (le_abs_self _))
    _ = ENNReal.ofReal (1 + ∑ c, |C c|) := by
        rw [ENNReal.ofReal_add zero_le_one (Finset.sum_nonneg fun c _ => abs_nonneg _), ENNReal.ofReal_one,
          ENNReal.ofReal_sum_of_nonneg fun c _ => abs_nonneg _]
private theorem measurable_prod_coords {l : ℕ} (a : Fin l → J × ℕ) :
    Measurable fun v : TranslateValues J => ∏ c, v (a c) :=
  Finset.measurable_prod _ fun c _ => measurable_pi_apply _
private theorem lintegral_sq_prod_le_of_limit (hT : T.IsPreserving) (hX : ∀ j, TranslatedLaws.HasBoundedMoments (X j))
    (hP : IsJointLimitLaw T X P) {l : ℕ} (a : Fin l → J × ℕ) {M : ℝ} (hM : 0 ≤ M)
    (hb : ∀ i, ∫⁻ ω, ENNReal.ofReal ((∏ c, translateTuple X a i ω c) ^ 2) ∂(T.μ i) ≤ ENNReal.ofReal M) :
    ∫⁻ v, ENNReal.ofReal ((∏ c, v (a c)) ^ 2) ∂P ≤ ENNReal.ofReal M := by
  haveI := hP.isProbability
  obtain ⟨Gn, hGn⟩ : ∃ Gn : ℕ → (Fin l → ℝ) → ℝ, ∀ n w, Gn n w = min ((∏ c, w c) ^ 2) n := ⟨_, fun _ _ => rfl⟩
  have hc : ∀ n, Continuous (Gn n) := fun n => by
    have : Gn n = fun w : Fin l → ℝ => min ((∏ c, w c) ^ 2) (n : ℝ) := funext (hGn n)
    rw [this]
    exact ((continuous_finset_prod _ fun c _ => continuous_apply c).pow 2).min continuous_const
  have hnn : ∀ n w, 0 ≤ Gn n w := fun n w => by
    rw [hGn]
    exact le_min (sq_nonneg _) (Nat.cast_nonneg _)
  have hle : ∀ n w, Gn n w ≤ n := fun n w => by
    rw [hGn]
    exact min_le_right _ _
  have hstep : ∀ n, ∫⁻ v, ENNReal.ofReal (Gn n fun c => v (a c)) ∂P ≤ ENNReal.ofReal M := by
    intro n
    have lim := hP.tendsto l a (Gn n) (hc n) ⟨n, fun w => by
      rw [abs_of_nonneg (hnn n w)]
      exact hle n w⟩
    have hmeas : Measurable fun v : TranslateValues J => Gn n fun c => v (a c) :=
      ((hc n).comp (continuous_pi fun c => continuous_apply (a c))).measurable
    have hI : Integrable (fun v : TranslateValues J => Gn n fun c => v (a c)) P :=
      Integrable.of_bound hmeas.aestronglyMeasurable n (Filter.Eventually.of_forall fun v => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hnn n _)]
        exact hle n _)
    have hterm : ∀ i, ∫ ω, Gn n (fun c => TranslatedLaws.translate (X (a c).1) (a c).2 i ω) ∂(T.μ i) ≤ M := by
      intro i
      haveI := hT.isProbability i
      have hae : AEStronglyMeasurable (fun ω => Gn n (translateTuple X a i ω)) (T.μ i) :=
        (hc n).comp_aestronglyMeasurable (aemeasurable_translateTuple hT hX a i).aestronglyMeasurable
      refine (integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun ω => hnn n _) hae).le.trans ?_
      refine ENNReal.toReal_le_of_le_ofReal hM (le_trans (lintegral_mono fun ω => ?_) (hb i))
      refine ENNReal.ofReal_le_ofReal ?_
      rw [hGn]
      exact min_le_left _ _
    have hlim : ∫ v, Gn n (fun c => v (a c)) ∂P ≤ M := le_of_tendsto' lim hterm
    rw [← ofReal_integral_eq_lintegral_ofReal hI (Filter.Eventually.of_forall fun v => hnn n _)]
    exact ENNReal.ofReal_le_ofReal hlim
  have hmono : Monotone fun n : ℕ => fun v : TranslateValues J => ENNReal.ofReal (Gn n fun c => v (a c)) := by
    intro n n' hnn' v
    refine ENNReal.ofReal_le_ofReal ?_
    rw [hGn, hGn]
    exact min_le_min_left _ (by exact_mod_cast hnn')
  have hmeas : ∀ n, Measurable fun v : TranslateValues J => ENNReal.ofReal (Gn n fun c => v (a c)) := fun n =>
    ENNReal.measurable_ofReal.comp ((hc n).comp (continuous_pi fun c => continuous_apply (a c))).measurable
  calc ∫⁻ v, ENNReal.ofReal ((∏ c, v (a c)) ^ 2) ∂P ≤ ∫⁻ v, ⨆ n : ℕ, ENNReal.ofReal (Gn n fun c => v (a c)) ∂P := by
        refine lintegral_mono fun v => ?_
        obtain ⟨n, hn⟩ := exists_nat_ge ((∏ c, v (a c)) ^ 2)
        refine le_trans (le_of_eq ?_) (le_iSup _ n)
        rw [hGn, min_eq_left hn]
    _ = ⨆ n : ℕ, ∫⁻ v, ENNReal.ofReal (Gn n fun c => v (a c)) ∂P := lintegral_iSup hmeas hmono
    _ ≤ ENNReal.ofReal M := iSup_le hstep
private theorem memLp_prod_coords (hT : T.IsPreserving) (hX : ∀ j, TranslatedLaws.HasBoundedMoments (X j))
    (hP : IsJointLimitLaw T X P) {l : ℕ} (a : Fin l → J × ℕ) :
    MemLp (fun v : TranslateValues J => ∏ c, v (a c)) 2 P := by
  haveI := hP.isProbability
  obtain ⟨M, hM, hb⟩ := exists_lintegral_sq_prod_le hT hX a
  exact (memLp_two_of_lintegral_sq_le (measurable_prod_coords a).aestronglyMeasurable hM
    (lintegral_sq_prod_le_of_limit hT hX hP a hM hb)).1
private theorem tendsto_integral_prod (hT : T.IsPreserving) (hX : ∀ j, TranslatedLaws.HasBoundedMoments (X j))
    (hP : IsJointLimitLaw T X P) {l : ℕ} (a : Fin l → J × ℕ) :
    Tendsto (fun i => ∫ ω, ∏ c, TranslatedLaws.translate (X (a c).1) (a c).2 i ω ∂(T.μ i)) atTop
      (𝓝 (∫ v, ∏ c, v (a c) ∂P)) := by
  haveI := hP.isProbability
  obtain ⟨M, hM, hb⟩ := exists_lintegral_sq_prod_le hT hX a
  have hbP := lintegral_sq_prod_le_of_limit hT hX hP a hM hb
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨R, hR⟩ : ∃ R : ℝ, R = 4 * (M + 1) / ε := ⟨_, rfl⟩
  have hR0 : 0 < R := by
    rw [hR]
    positivity
  have hMR : M / R < ε / 4 := by
    rw [hR, div_div_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith
  have hcl : Continuous fun w : Fin l → ℝ => truncate R (∏ c, w c) :=
    (continuous_truncate R).comp (continuous_finset_prod _ fun c _ => continuous_apply c)
  have lim := hP.tendsto l a (fun w => truncate R (∏ c, w c)) hcl ⟨R, fun w => abs_truncate_le hR0.le _⟩
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp lim (ε / 4) (by positivity)
  refine ⟨N, fun i hi => ?_⟩
  haveI := hT.isProbability i
  have h1 := hN i hi
  rw [Real.dist_eq] at h1 ⊢
  have hY : AEStronglyMeasurable (fun ω => ∏ c, translateTuple X a i ω c) (T.μ i) :=
    ((continuous_finset_prod _ fun c _ => continuous_apply c).comp_aestronglyMeasurable
      (aemeasurable_translateTuple hT hX a i).aestronglyMeasurable)
  have h2 := abs_integral_sub_truncate_le hY hM hR0 (hb i)
  have h3 := abs_integral_sub_truncate_le (measurable_prod_coords a).aestronglyMeasurable hM hR0 hbP
  have h4 : ∫ ω, ∏ c, TranslatedLaws.translate (X (a c).1) (a c).2 i ω ∂(T.μ i) =
      ∫ ω, ∏ c, translateTuple X a i ω c ∂(T.μ i) := rfl
  rw [h4]
  have h5 : ∫ ω, truncate R (∏ c, TranslatedLaws.translate (X (a c).1) (a c).2 i ω) ∂(T.μ i) =
      ∫ ω, truncate R (∏ c, translateTuple X a i ω c) ∂(T.μ i) := rfl
  rw [h5] at h1
  have a1 := abs_lt.mp h1
  have a2 := abs_le.mp h2
  have a3 := abs_le.mp h3
  rw [abs_lt]
  constructor <;> linarith [a1.1, a1.2, a2.1, a2.2, a3.1, a3.2]
end LimitLawMoments
section Translates
variable {J : Type} {P : Measure (TranslateValues J)}
private theorem translateShift_iterate_apply (k : ℕ) (v : TranslateValues J) (j : J) (m : ℕ) :
    ((translateShift (J := J))^[k] v) (j, m) = v (j, m + k) := by apply _root_.YangMills.SharedProofs.p49195 <;> assumption
variable [IsProbabilityMeasure P]
private theorem tendsto_average_integral_mul (hS : MeasurePreserving (translateShift (J := J)) P P) {j : J}
    (hc : ∀ k, MemLp (fun v : TranslateValues J => v (j, k)) 2 P) {g : Lp ℝ 2 P} (hfix : koopmanOp hS g = g)
    (hlim : Tendsto (fun M : ℕ => birkhoffAverage ℝ (koopmanOp hS) _root_.id M ((hc 0).toLp _)) atTop (𝓝 g))
    {W : TranslateValues J → ℝ} (hW : MemLp W 2 P) (o : ℕ) :
    Tendsto (fun M : ℕ => (M : ℝ)⁻¹ * ∑ k ∈ Finset.range M, ∫ v, W v * v (j, o + k) ∂P) atTop
      (𝓝 (∫ v, W v * g v ∂P)) := by
  obtain ⟨U, hU⟩ : ∃ U, U = koopmanOp hS := ⟨_, rfl⟩
  obtain ⟨x, hx⟩ : ∃ x, x = (hc 0).toLp _ := ⟨_, rfl⟩
  rw [← hU, ← hx] at hlim
  have hcont : Continuous (U^[o]) := U.continuous.iterate o
  have h1 : Tendsto (fun M : ℕ => U^[o] (birkhoffAverage ℝ U _root_.id M x)) atTop (𝓝 (U^[o] g)) :=
    (hcont.tendsto g).comp hlim
  have hUg : U^[o] g = g := by
    have : Function.IsFixedPt U g := by
      rw [hU]
      exact hfix
    exact this.iterate o
  rw [hUg] at h1
  obtain ⟨w, hw⟩ : ∃ w, w = hW.toLp W := ⟨_, rfl⟩
  have hwW : w =ᵐ[P] W := hw ▸ hW.coeFn_toLp
  have h2 := (tendsto_const_nhds (x := w)).inner (𝕜 := ℝ) h1
  have hinner : ∀ y : Lp ℝ 2 P, inner ℝ w y = ∫ v, W v * y v ∂P := by
    intro y
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hwW] with v hv
    rw [hv]
    simp [mul_comm]
  rw [hinner g] at h2
  refine h2.congr fun M => ?_
  rw [hinner]
  have hxc : (x : TranslateValues J → ℝ) =ᵐ[P] fun v => v (j, 0) := hx ▸ (hc 0).coeFn_toLp
  have hall : ∀ᵐ v ∂P, ∀ k, (x : TranslateValues J → ℝ) ((translateShift (J := J))^[k] v) = v (j, k) := by
    refine ae_all_iff.mpr fun k => ?_
    filter_upwards [(hS.iterate k).quasiMeasurePreserving.ae hxc] with v hv
    rw [hv, translateShift_iterate_apply]
    simp
  have e1 : (U^[o] (birkhoffAverage ℝ U _root_.id M x) : Lp ℝ 2 P) =ᵐ[P]
      fun v => (M : ℝ)⁻¹ * ∑ k ∈ Finset.range M, v (j, o + k) := by
    rw [hU]
    have a1 := koopmanOp_iterate_coeFn hS (birkhoffAverage ℝ (koopmanOp hS) _root_.id M x) o
    have a2 := (hS.iterate o).quasiMeasurePreserving.ae_eq_comp (birkhoffAverage_koopmanOp_coeFn hS x M)
    have a3 := (hS.iterate o).quasiMeasurePreserving.ae hall
    refine a1.trans (a2.trans ?_)
    filter_upwards [a3] with v hv
    simp only [Function.comp]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hv k, translateShift_iterate_apply, add_comm]
  have hint : ∀ k, Integrable (fun v : TranslateValues J => W v * v (j, o + k)) P :=
    fun k => hW.integrable_mul (hc (o + k))
  calc ∫ v, W v * (U^[o] (birkhoffAverage ℝ U _root_.id M x) : Lp ℝ 2 P) v ∂P
      = ∫ v, (M : ℝ)⁻¹ * ∑ k ∈ Finset.range M, W v * v (j, o + k) ∂P := by
        refine integral_congr_ae ?_
        filter_upwards [e1] with v hv
        rw [hv, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        ring
    _ = (M : ℝ)⁻¹ * ∑ k ∈ Finset.range M, ∫ v, W v * v (j, o + k) ∂P := by
        rw [integral_const_mul, integral_finset_sum _ fun k _ => hint k]
end Translates
section FixedVector
variable {J : Type} {P : Measure (TranslateValues J)} [IsProbabilityMeasure P]
private theorem invariantCondExp_ae_eq_zero (hS : MeasurePreserving (translateShift (J := J)) P P) {j : J}
    (hc : ∀ k, MemLp (fun v : TranslateValues J => v (j, k)) 2 P)
    (hcor : Tendsto (fun k : ℕ => ∫ v, v (j, 0) * v (j, k) ∂P) atTop (𝓝 0)) :
    invariantCondExp P (evalAtZero j) =ᵐ[P] 0 := by
  obtain ⟨g, hg, hfix, hin, hlim⟩ := exists_fixed_eq_condExp hS (hc 0)
  have h1 := tendsto_average_integral_mul hS hc hfix hlim (hc 0) 0
  simp only [zero_add] at h1
  have h2 : Tendsto (fun M : ℕ => (M : ℝ)⁻¹ * ∑ k ∈ Finset.range M, ∫ v, v (j, 0) * v (j, k) ∂P) atTop (𝓝 0) :=
    Filter.Tendsto.cesaro hcor
  have h3 : ∫ v : TranslateValues J, v (j, 0) * g v ∂P = 0 := tendsto_nhds_unique h1 h2
  have hxc : ((hc 0).toLp _ : TranslateValues J → ℝ) =ᵐ[P] fun v => v (j, 0) := (hc 0).coeFn_toLp
  have h4 : inner ℝ g ((hc 0).toLp _) = ∫ v : TranslateValues J, v (j, 0) * g v ∂P := by
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hxc] with v hv
    rw [hv]
    simp
  rw [h4, h3] at hin
  have h5 : g = 0 := inner_self_eq_zero.mp hin.symm
  have h6 : (g : TranslateValues J → ℝ) =ᵐ[P] 0 := by
    rw [h5]
    exact Lp.coeFn_zero _ _ _
  exact hg.symm.trans h6
private theorem integral_pow_fixed_le (hS : MeasurePreserving (translateShift (J := J)) P P) {j : J}
    (hc : ∀ k, MemLp (fun v : TranslateValues J => v (j, k)) 2 P) {g : Lp ℝ 2 P} (hfix : koopmanOp hS g = g)
    (hlim : Tendsto (fun M : ℕ => birkhoffAverage ℝ (koopmanOp hS) _root_.id M ((hc 0).toLp _)) atTop (𝓝 g))
    {Cb Cq : ℝ} (hall : ∀ᵐ v ∂P, ∀ k, |v (j, k)| ≤ Cb) (hgb : ∀ᵐ v ∂P, |g v| ≤ Cb) {q gap : ℕ}
    (hgap : ∀ k : Fin q → ℕ, (∀ c e, c ≠ e → gap ≤ k c - k e ∨ gap ≤ k e - k c) → ∫ v, ∏ c, v (j, k c) ∂P ≤ Cq) :
    ∫ v, g v ^ q ∂P ≤ Cq := by
  have claim : ∀ m : ℕ, ∀ S : Finset ℕ, S.card + m = q → (∀ x ∈ S, ∀ y ∈ S, x ≠ y → gap ≤ x - y ∨ gap ≤ y - x) →
      ∫ v, g v ^ m * ∏ k ∈ S, v (j, k) ∂P ≤ Cq := by
    intro m
    induction m with
    | zero =>
      intro S hS' hgaps
      have hcard : S.card = q := by omega
      obtain ⟨e⟩ : Nonempty (Fin q ≃ S) := ⟨(S.orderIsoOfFin hcard).toEquiv⟩
      have h1 := hgap (fun c => (e c : ℕ))
        (fun c c' hne => hgaps _ (e c).2 _ (e c').2 (fun h => hne (e.injective (Subtype.ext h))))
      refine le_trans (le_of_eq ?_) h1
      refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
      simp only [pow_zero, one_mul]
      rw [← Finset.prod_coe_sort S fun k => v (j, k)]
      exact (Equiv.prod_comp e fun s : S => v (j, (s : ℕ))).symm
    | succ m ih =>
      intro S hS' hgaps
      obtain ⟨W, hW⟩ : ∃ W : TranslateValues J → ℝ, W = fun v => g v ^ m * ∏ k ∈ S, v (j, k) := ⟨_, rfl⟩
      have hWm : MemLp W 2 P := by
        refine MemLp.of_bound ?_ (|Cb| ^ m * |Cb| ^ S.card) ?_
        · rw [hW]
          exact ((Lp.aestronglyMeasurable g).pow m).mul
            (Finset.measurable_prod (f := fun (k : ℕ) (v : TranslateValues J) => v (j, k)) S
              fun k _ => measurable_pi_apply (j, k)).aestronglyMeasurable
        · filter_upwards [hall, hgb] with v h1 h2
          rw [hW, Real.norm_eq_abs, abs_mul, abs_pow, Finset.abs_prod]
          refine mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) (h2.trans (le_abs_self _)) m) ?_
            (Finset.prod_nonneg fun _ _ => abs_nonneg _) (by positivity)
          calc ∏ k ∈ S, |v (j, k)| ≤ ∏ _k ∈ S, |Cb| :=
                Finset.prod_le_prod (fun _ _ => abs_nonneg _) fun k _ => (h1 k).trans (le_abs_self _)
            _ = |Cb| ^ S.card := by rw [Finset.prod_const]
      obtain ⟨o, ho⟩ : ∃ o, o = S.sup id + gap + 1 := ⟨_, rfl⟩
      have lim := tendsto_average_integral_mul hS hc hfix hlim hWm o
      have hterm : ∀ k, ∫ v, W v * v (j, o + k) ∂P ≤ Cq := by
        intro k
        have hnot : o + k ∉ S := by
          intro hmem
          have : o + k ≤ S.sup id := Finset.le_sup (f := id) hmem
          omega
        have h1 := ih (insert (o + k) S) (by rw [Finset.card_insert_of_notMem hnot]; omega) (by
          intro x hx y hy hxy
          rw [Finset.mem_insert] at hx hy
          rcases hx with rfl | hx
          · rcases hy with rfl | hy
            · exact absurd rfl hxy
            · have : y ≤ S.sup id := Finset.le_sup (f := id) hy
              left
              omega
          · rcases hy with rfl | hy
            · have : x ≤ S.sup id := Finset.le_sup (f := id) hx
              right
              omega
            · exact hgaps x hx y hy hxy)
        refine le_trans (le_of_eq ?_) h1
        refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
        simp only [hW]
        rw [Finset.prod_insert hnot]
        ring
      have hle : ∀ᶠ M : ℕ in atTop, (M : ℝ)⁻¹ * ∑ k ∈ Finset.range M, ∫ v, W v * v (j, o + k) ∂P ≤ Cq := by
        filter_upwards [eventually_gt_atTop 0] with M hM
        have hM' : (0 : ℝ) < M := by exact_mod_cast hM
        rw [inv_mul_le_iff₀ hM']
        calc ∑ k ∈ Finset.range M, ∫ v, W v * v (j, o + k) ∂P ≤ ∑ _k ∈ Finset.range M, Cq :=
              Finset.sum_le_sum fun k _ => hterm k
          _ = M * Cq := by simp
      have h2 := le_of_tendsto lim hle
      refine le_trans (le_of_eq ?_) h2
      refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
      simp only [hW]
      ring
  have := claim q ∅ (by simp) (by simp)
  simpa using this
private theorem ae_le_of_moment_bound {Y : TranslateValues J → ℝ} {b C₀ Cb : ℝ} (hb : 0 ≤ b)
    (hY : AEStronglyMeasurable Y P) (h0 : ∀ᵐ v ∂P, 0 ≤ Y v ∧ Y v ≤ Cb)
    (hm : ∀ q : ℕ, 1 ≤ q → ∫ v, Y v ^ q ∂P ≤ C₀ * b ^ q) : ∀ᵐ v ∂P, Y v ≤ b := by
  have key : ∀ n : ℕ, ∀ᵐ v ∂P, Y v ≤ b + 1 / ((n : ℝ) + 1) := by
    intro n
    obtain ⟨ε, hε⟩ : ∃ ε : ℝ, ε = 1 / ((n : ℝ) + 1) := ⟨_, rfl⟩
    have hε0 : 0 < ε := by
      rw [hε]
      positivity
    rw [← hε]
    have hbε : 0 < b + ε := by linarith
    have hp : ∀ q : ℕ, 1 ≤ q → P.real {v | b + ε < Y v} ≤ C₀ * (b / (b + ε)) ^ q := by
      intro q hq
      have hint : Integrable (fun v => Y v ^ q) P := by
        refine Integrable.of_bound (hY.pow q) (|Cb| ^ q) ?_
        filter_upwards [h0] with v hv
        rw [Real.norm_eq_abs, abs_pow]
        exact pow_le_pow_left₀ (abs_nonneg _)
          (abs_le.mpr ⟨by linarith [abs_nonneg Cb, neg_abs_le Cb, hv.1], hv.2.trans (le_abs_self _)⟩) q
      have h1 := mul_meas_ge_le_integral_of_nonneg (μ := P) (f := fun v => Y v ^ q)
        (by filter_upwards [h0] with v hv using pow_nonneg hv.1 q) hint ((b + ε) ^ q)
      have h2 : P.real {v | b + ε < Y v} ≤ P.real {v | (b + ε) ^ q ≤ Y v ^ q} := by
        refine measureReal_mono (fun v hv => ?_) (measure_ne_top _ _)
        exact pow_le_pow_left₀ hbε.le (le_of_lt hv) q
      have hpos : 0 < (b + ε) ^ q := pow_pos hbε q
      have h3 : (b + ε) ^ q * P.real {v | b + ε < Y v} ≤ C₀ * b ^ q :=
        (mul_le_mul_of_nonneg_left h2 hpos.le).trans (h1.trans (hm q hq))
      rw [div_pow, mul_div_assoc', le_div_iff₀ hpos]
      linarith
    have hρ0 : 0 ≤ b / (b + ε) := div_nonneg hb hbε.le
    have hρ1 : b / (b + ε) < 1 := by
      rw [div_lt_one hbε]
      linarith
    have hlim : Tendsto (fun q : ℕ => C₀ * (b / (b + ε)) ^ q) atTop (𝓝 0) := by
      have := (tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1).const_mul C₀
      simpa using this
    have hz : P.real {v | b + ε < Y v} ≤ 0 := ge_of_tendsto hlim (by
      filter_upwards [eventually_ge_atTop 1] with q hq using hp q hq)
    have hz' : P {v | b + ε < Y v} = 0 := by
      have := le_antisymm hz measureReal_nonneg
      exact (measureReal_eq_zero_iff (measure_ne_top _ _)).mp this
    rw [ae_iff]
    simpa using hz'
  filter_upwards [ae_all_iff.mpr key] with v hv
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
  exact (hv n).trans (by linarith)
end FixedVector
theorem jointLimitProperties : jointLimitPropertiesStatement := by
  intro T J _ X P hT hX hP
  haveI := hP.isProbability
  have hS := measurePreserving_translateShift hT hX hP
  have hone : ∀ a : J × ℕ, MemLp (fun v : TranslateValues J => v a) 2 P := by
    intro a
    simpa using memLp_prod_coords hT hX hP (fun _ : Fin 1 => a)
  have hc : ∀ j k, MemLp (fun v : TranslateValues J => v (j, k)) 2 P := fun j k => hone (j, k)
  refine ⟨hS, fun l a => ⟨(memLp_prod_coords hT hX hP a).integrable one_le_two, tendsto_integral_prod hT hX hP a⟩,
    fun l a G hG h => ae_eq_zero_of_eventually_eq_zero hP a G hG h, ?_, ?_, ?_⟩
  · intro j
    refine (tendsto_eLpNorm_birkhoff_sub_condExp hS (hc j 0)).congr fun M =>
      eLpNorm_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    have h1 : ∀ k, ((translateShift (J := J))^[k] v) (j, 0) = v (j, k) := fun k => by
      rw [translateShift_iterate_apply, zero_add]
    simp only [Pi.sub_apply, h1]
    rfl
  · intro j hcor
    exact invariantCondExp_ae_eq_zero hS (hc j) hcor
  · intro j b C₀ Cb hb hbd hq
    have hbk : ∀ k, ∀ᵐ v ∂P, 0 ≤ v (j, k) ∧ v (j, k) ≤ Cb := by
      intro k
      have h1 := (hS.iterate k).quasiMeasurePreserving.ae hbd
      filter_upwards [h1] with v hv
      rw [translateShift_iterate_apply, zero_add] at hv
      exact hv
    obtain ⟨g, hg, hfix, -, hlim⟩ := exists_fixed_eq_condExp hS (hc j 0)
    have hm : (invariantSigma (translateShift (J := J))) ≤ MeasurableSpace.pi := invariantSigma_le
    have hI : Integrable (fun v : TranslateValues J => v (j, 0)) P := (hc j 0).integrable one_le_two
    have hY0 : 0 ≤ᵐ[P] P[fun v : TranslateValues J => v (j, 0) | invariantSigma (translateShift (J := J))] :=
      condExp_nonneg (by filter_upwards [hbd] with v hv using hv.1)
    have hY1 : P[fun v : TranslateValues J => v (j, 0) | invariantSigma (translateShift (J := J))] ≤ᵐ[P] fun _ => Cb := by
      have h1 := condExp_mono (m := invariantSigma (translateShift (J := J))) hI (integrable_const Cb)
        (by filter_upwards [hbd] with v hv using hv.2)
      rwa [condExp_const hm] at h1
    have hgb0 : ∀ᵐ v ∂P, 0 ≤ g v ∧ g v ≤ Cb := by
      filter_upwards [hg, hY0, hY1] with v h1 h2 h3
      rw [h1]
      exact ⟨h2, h3⟩
    have hall : ∀ᵐ v ∂P, ∀ k, |v (j, k)| ≤ |Cb| := by
      refine ae_all_iff.mpr fun k => ?_
      filter_upwards [hbk k] with v hv
      exact abs_le.mpr ⟨by linarith [neg_abs_le Cb, abs_nonneg Cb, hv.1], hv.2.trans (le_abs_self _)⟩
    have hgb : ∀ᵐ v ∂P, |g v| ≤ |Cb| := by
      filter_upwards [hgb0] with v hv
      exact abs_le.mpr ⟨by linarith [neg_abs_le Cb, abs_nonneg Cb, hv.1], hv.2.trans (le_abs_self _)⟩
    have hmom : ∀ q : ℕ, 1 ≤ q → ∫ v, g v ^ q ∂P ≤ C₀ * b ^ q := by
      intro q hq1
      obtain ⟨gap, hgap⟩ := hq q hq1
      exact integral_pow_fixed_le hS (hc j) hfix hlim hall hgb hgap
    have hle := ae_le_of_moment_bound hb (Lp.aestronglyMeasurable g) hgb0 hmom
    filter_upwards [hle, hg] with v h1 h2
    have : invariantCondExp P (evalAtZero j) v = g v := by
      rw [h2]
      rfl
    rw [this]
    exact h1
end YangMills.Construction.MomentMethod
end
