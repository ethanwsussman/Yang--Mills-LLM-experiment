import YangMills.Construction.EuclideanFunctionals.ExpansionTranslationsContinuityAndSmearingOfTheInsertionValueProof
import Mathlib
set_option autoImplicit false
open Filter Topology MeasureTheory
open scoped Pointwise ENNReal
namespace YangMills.Construction
noncomputable section
namespace EuclideanFunctionals.Smearing
theorem supp_eq_tsupport {𝕜 : Type*} [RCLike 𝕜] (f : R4 → 𝕜) : supp f = tsupport f :=
  SeparatedTuplesR4.closureWrt_euclid_eq_closure (fun _ _ => rfl) _
theorem mem_C1c_iff {𝕜 : Type*} [RCLike 𝕜] (f : R4 → 𝕜) :
    f ∈ C1c 𝕜 ↔ ContDiff ℝ 1 f ∧ HasCompactSupport f := by apply _root_.YangMills.Construction.EuclideanFunctionals.Moments.mem_C1c_iff_contDiff <;> assumption
theorem actFn_transl_eq_comp (y : R4) (h : R4 → ℂ) :
    (EuclidMotion.transl y).actFn h = h ∘ Homeomorph.subRight y := by
  funext x
  simpa using EuclidMotion.actFn_transl y h x
theorem actFn_transl_mem {h : R4 → ℂ} (hh : h ∈ C1c ℂ) (y : R4) :
    (EuclidMotion.transl y).actFn h ∈ C1c ℂ := by apply _root_.YangMills.Construction.EuclideanFunctionals.InsertionForm.shiftFn_mem_C1c <;> assumption
theorem mem_supp_actFn_transl (y : R4) (h : R4 → ℂ) (x : R4) :
    x ∈ supp ((EuclidMotion.transl y).actFn h) ↔ x - y ∈ supp h := by
  rw [supp_eq_tsupport, supp_eq_tsupport, actFn_transl_eq_comp, tsupport_comp_eq_preimage]
  rfl
section Measure
variable {E : Submodule ℝ R4}
theorem injective_of_preserves {T : (Fin (Module.finrank ℝ E) → ℝ) →ₗ[ℝ] E}
    (hT : PreservesEuclidNorm E T) : Function.Injective T := by
  refine (injective_iff_map_eq_zero T).2 fun y hy => ?_
  have h := hT.2 y
  rw [hy] at h
  have h0 : EuclideanFunctions.euclideanNorm y = 0 := by
    rw [← h]
    simp [EuclideanFunctions.euclideanNorm]
  simp only [EuclideanFunctions.euclideanNorm] at h0
  have h1 : ∑ i, y i ^ 2 = 0 :=
    (Real.sqrt_eq_zero (Finset.sum_nonneg fun i _ => sq_nonneg _)).1 h0
  funext i
  have := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => sq_nonneg (y i)).1 h1 i (Finset.mem_univ i)
  simpa using this
def equivOfPreserves {T : (Fin (Module.finrank ℝ E) → ℝ) →ₗ[ℝ] E}
    (hT : PreservesEuclidNorm E T) : (Fin (Module.finrank ℝ E) → ℝ) ≃L[ℝ] E :=
  (LinearEquiv.ofBijective T ⟨injective_of_preserves hT, hT.1⟩).toContinuousLinearEquiv
theorem equivOfPreserves_apply {T : (Fin (Module.finrank ℝ E) → ℝ) →ₗ[ℝ] E}
    (hT : PreservesEuclidNorm E T) (y : Fin (Module.finrank ℝ E) → ℝ) :
    equivOfPreserves hT y = T y := rfl
theorem measurePreserving_of_norm_eq {κ : ℕ} (U : (Fin κ → ℝ) ≃L[ℝ] (Fin κ → ℝ))
    (hU : ∀ y, EuclideanFunctions.euclideanNorm (U y) =
      EuclideanFunctions.euclideanNorm y) :
    MeasurePreserving U volume volume := by
  let L : EuclideanSpace ℝ (Fin κ) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin κ) :=
    (WithLp.linearEquiv 2 ℝ (Fin κ → ℝ)).trans
      (U.toLinearEquiv.trans (WithLp.linearEquiv 2 ℝ (Fin κ → ℝ)).symm)
  have hnorm : ∀ w : EuclideanSpace ℝ (Fin κ),
      ‖w‖ = EuclideanFunctions.euclideanNorm (WithLp.ofLp w) := by
    intro w
    simp [EuclideanSpace.norm_eq, EuclideanFunctions.euclideanNorm]
  let f : EuclideanSpace ℝ (Fin κ) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin κ) :=
    ⟨L, fun w => by
      rw [hnorm, hnorm]
      exact hU _⟩
  have h := ((PiLp.volume_preserving_ofLp (Fin κ)).comp f.measurePreserving).comp
    (PiLp.volume_preserving_toLp (Fin κ))
  have hfun : ⇑U = (WithLp.ofLp ∘ ⇑f) ∘ WithLp.toLp 2 := by
    funext y
    rfl
  rw [hfun]
  exact h
theorem map_volume_eq_of_preserves {T T' : (Fin (Module.finrank ℝ E) → ℝ) →ₗ[ℝ] E}
    (hT : PreservesEuclidNorm E T) (hT' : PreservesEuclidNorm E T') :
    Measure.map T volume = Measure.map T' volume := by
  let e := equivOfPreserves hT
  let e' := equivOfPreserves hT'
  let U : (Fin (Module.finrank ℝ E) → ℝ) ≃L[ℝ] (Fin (Module.finrank ℝ E) → ℝ) := e.trans e'.symm
  have hTU : ∀ y, T' (U y) = T y := by
    intro y
    have : e' (U y) = e y := by simp [U]
    simpa [e, e', equivOfPreserves_apply] using this
  have hU : ∀ y, EuclideanFunctions.euclideanNorm (U y) =
      EuclideanFunctions.euclideanNorm y := by
    intro y
    rw [← hT'.2 (U y), hTU, hT.2]
  have hmp := measurePreserving_of_norm_eq U hU
  have hT'm : Measurable T' := (equivOfPreserves hT').continuous.measurable
  have hcomp : (T : _ → E) = T' ∘ U := by
    funext y
    exact (hTU y).symm
  rw [hcomp, ← Measure.map_map hT'm hmp.measurable, hmp.map_eq]
theorem isLebesgueOn_unique (μ μ' : Measure E) (h : IsLebesgueOn E μ)
    (h' : IsLebesgueOn E μ') : μ = μ' := by
  rcases h with ⟨h0, rfl⟩ | ⟨h0, T, hT, rfl⟩
  · rcases h' with ⟨-, rfl⟩ | ⟨h0', -⟩
    · rfl
    · exact absurd h0 h0'
  · rcases h' with ⟨h0', -⟩ | ⟨-, T', hT', rfl⟩
    · exact absurd h0' h0
    · exact map_volume_eq_of_preserves hT hT'
theorem isFiniteMeasureOnCompacts_of_isLebesgueOn {μ : Measure E} (h : IsLebesgueOn E μ) :
    IsFiniteMeasureOnCompacts μ := by
  rcases h with ⟨-, rfl⟩ | ⟨-, T, hT, rfl⟩
  · infer_instance
  · have : Measure.IsAddHaarMeasure
        (Measure.map (equivOfPreserves hT) (volume : Measure (Fin _ → ℝ))) :=
      (equivOfPreserves hT).isAddHaarMeasure_map volume
    exact (inferInstance :
      IsFiniteMeasureOnCompacts (Measure.map (equivOfPreserves hT) (volume : Measure (Fin _ → ℝ))))
end Measure
section Pieces
variable {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
open Classical in
theorem exists_partition_of_cover {δ : ℝ} (t : Finset X) : ∀ K : Set X, MeasurableSet K →
    K ⊆ ⋃ y ∈ t, Metric.ball y δ →
    ∃ B : X → Set X, (∀ y ∈ t, MeasurableSet (B y)) ∧
      Set.Pairwise (↑t) (Function.onFun Disjoint B) ∧ (⋃ y ∈ t, B y) = K ∧
      ∀ y ∈ t, B y ⊆ Metric.ball y δ := by
  induction t using Finset.induction_on with
  | empty =>
    intro K _ hK
    refine ⟨fun _ => ∅, by simp, by simp, ?_, by simp⟩
    simpa using (Set.subset_empty_iff.1 (by simpa using hK)).symm
  | insert a t ha IH =>
    intro K hKm hK
    obtain ⟨B, hBm, hBd, hBU, hBb⟩ := IH (K \ Metric.ball a δ)
      (hKm.diff Metric.isOpen_ball.measurableSet) (by
        intro z hz
        have h := hK hz.1
        rw [Finset.set_biUnion_insert] at h
        rcases h with h | h
        · exact absurd h hz.2
        · exact h)
    have hsub : ∀ y ∈ t, B y ⊆ K \ Metric.ball a δ := fun y hy z hz =>
      hBU ▸ Set.mem_biUnion hy hz
    have hne : ∀ y ∈ t, y ≠ a := fun y hy => ne_of_mem_of_not_mem hy ha
    refine ⟨Function.update B a (K ∩ Metric.ball a δ), ?_, ?_, ?_, ?_⟩
    · intro y hy
      rcases Finset.mem_insert.1 hy with rfl | hy'
      · rw [Function.update_self]
        exact hKm.inter Metric.isOpen_ball.measurableSet
      · rw [Function.update_of_ne (hne y hy')]
        exact hBm y hy'
    · intro y hy y' hy' hyy
      rcases Finset.mem_insert.1 (Finset.mem_coe.1 hy) with rfl | hy₁ <;>
        rcases Finset.mem_insert.1 (Finset.mem_coe.1 hy') with rfl | hy₂
      · exact absurd rfl hyy
      · simp only [Function.onFun]
        rw [Function.update_self, Function.update_of_ne (hne y' hy₂)]
        exact Set.disjoint_left.2 fun z hz hz' => (hsub y' hy₂ hz').2 hz.2
      · simp only [Function.onFun]
        rw [Function.update_self, Function.update_of_ne (hne y hy₁)]
        exact Set.disjoint_right.2 fun z hz hz' => (hsub y hy₁ hz').2 hz.2
      · simp only [Function.onFun]
        rw [Function.update_of_ne (hne y hy₁), Function.update_of_ne (hne y' hy₂)]
        exact hBd hy₁ hy₂ hyy
    · rw [Finset.set_biUnion_insert, Function.update_self]
      have h : (⋃ y ∈ t, Function.update B a (K ∩ Metric.ball a δ) y) = ⋃ y ∈ t, B y :=
        Set.iUnion₂_congr fun y hy => by rw [Function.update_of_ne (hne y hy)]
      rw [h, hBU, Set.inter_union_sdiff]
    · intro y hy
      rcases Finset.mem_insert.1 hy with rfl | hy'
      · rw [Function.update_self]
        exact Set.inter_subset_right
      · rw [Function.update_of_ne (hne y hy')]
        exact hBb y hy'
structure FineCover (K : Set X) (t : ℕ → Finset X) (B : ℕ → X → Set X) : Prop where
  mem : ∀ n, ∀ y ∈ t n, y ∈ K
  measurableSet : ∀ n, ∀ y ∈ t n, MeasurableSet (B n y)
  pairwiseDisjoint : ∀ n, Set.Pairwise (↑(t n)) (Function.onFun Disjoint (B n))
  iUnion_eq : ∀ n, (⋃ y ∈ t n, B n y) = K
  dist_lt : ∀ n, ∀ y ∈ t n, ∀ z ∈ B n y, dist z y < 1 / ((n : ℝ) + 1)
theorem exists_fineCover {K : Set X} (hK : IsCompact K) (hKm : MeasurableSet K) :
    ∃ (t : ℕ → Finset X) (B : ℕ → X → Set X), FineCover K t B := by
  have h : ∀ n : ℕ, ∃ (t : Finset X) (B : X → Set X), (∀ y ∈ t, y ∈ K) ∧
      (∀ y ∈ t, MeasurableSet (B y)) ∧ Set.Pairwise (↑t) (Function.onFun Disjoint B) ∧
      (⋃ y ∈ t, B y) = K ∧ ∀ y ∈ t, ∀ z ∈ B y, dist z y < 1 / ((n : ℝ) + 1) := by
    intro n
    obtain ⟨t, htK, htf, hcov⟩ :=
      hK.finite_cover_balls (e := 1 / ((n : ℝ) + 1)) (by positivity)
    obtain ⟨B, hBm, hBd, hBU, hBb⟩ :=
      exists_partition_of_cover (δ := 1 / ((n : ℝ) + 1)) htf.toFinset K hKm
        (by simpa using hcov)
    refine ⟨htf.toFinset, B, fun y hy => htK (htf.mem_toFinset.1 hy), hBm, hBd, hBU,
      fun y hy z hz => ?_⟩
    exact Metric.mem_ball.1 (hBb y hy hz)
  choose t B h₁ h₂ h₃ h₄ h₅ using h
  exact ⟨t, B, ⟨h₁, h₂, h₃, h₄, h₅⟩⟩
omit [PseudoMetricSpace X] [OpensMeasurableSpace X] in
theorem norm_setIntegral_sub_riemannSum_le (μ : Measure X) (t : Finset X) (B : X → Set X)
    (hBm : ∀ y ∈ t, MeasurableSet (B y)) (hBd : Set.Pairwise (↑t) (Function.onFun Disjoint B))
    {b G : X → ℂ} (hb : IntegrableOn b (⋃ y ∈ t, B y) μ)
    (hbG : IntegrableOn (fun z => b z * G z) (⋃ y ∈ t, B y) μ) {ε : ℝ}
    (hG : ∀ y ∈ t, ∀ z ∈ B y, ‖G z - G y‖ ≤ ε) :
    ‖(∫ z in ⋃ y ∈ t, B y, b z * G z ∂μ) - ∑ y ∈ t, (∫ z in B y, b z ∂μ) * G y‖ ≤
      ε * ∫ z in ⋃ y ∈ t, B y, ‖b z‖ ∂μ := by
  have hsub : ∀ y ∈ t, B y ⊆ ⋃ y ∈ t, B y := fun y hy z hz => Set.mem_biUnion hy hz
  have hb' : ∀ y ∈ t, IntegrableOn b (B y) μ := fun y hy => hb.mono_set (hsub y hy)
  have hbG' : ∀ y ∈ t, IntegrableOn (fun z => b z * G z) (B y) μ :=
    fun y hy => hbG.mono_set (hsub y hy)
  rw [integral_biUnion_finset t hBm hBd hbG',
    integral_biUnion_finset t hBm hBd (f := fun z => ‖b z‖) (fun y hy => (hb' y hy).norm),
    ← Finset.sum_sub_distrib, Finset.mul_sum]
  refine norm_sum_le_of_le t fun y hy => ?_
  have e : (∫ z in B y, b z * G z ∂μ) - (∫ z in B y, b z ∂μ) * G y =
      ∫ z in B y, b z * (G z - G y) ∂μ := by
    rw [← integral_mul_const, ← integral_sub (hbG' y hy) ((hb' y hy).mul_const _)]
    congr 1
    funext z
    ring
  rw [e, ← integral_const_mul]
  refine norm_integral_le_of_norm_le ((hb' y hy).norm.const_mul ε) ?_
  refine (ae_restrict_iff' (hBm y hy)).2 (ae_of_all _ fun z hz => ?_)
  rw [norm_mul, mul_comm]
  exact mul_le_mul_of_nonneg_right (hG y hy z hz) (norm_nonneg _)
omit [OpensMeasurableSpace X] in
theorem tendstoUniformly_riemannSum {ι : Type*} (μ : Measure X) {K : Set X} {t : ℕ → Finset X}
    {B : ℕ → X → Set X} (hc : FineCover K t B) {b : X → ℂ} (hb : IntegrableOn b K μ)
    (G : ι → X → ℂ) (hbG : ∀ i, IntegrableOn (fun z => b z * G i z) K μ)
    (hG : ∀ ε > 0, ∃ δ > 0, ∀ i, ∀ z ∈ K, ∀ y ∈ K, dist z y < δ → ‖G i z - G i y‖ ≤ ε) :
    TendstoUniformly (fun n i => ∑ y ∈ t n, (∫ z in B n y, b z ∂μ) * G i y)
      (fun i => ∫ z in K, b z * G i z ∂μ) atTop := by
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  have hC : 0 ≤ ∫ z in K, ‖b z‖ ∂μ := integral_nonneg fun _ => norm_nonneg _
  set C := ∫ z in K, ‖b z‖ ∂μ with hCdef
  obtain ⟨δ, hδ, hd⟩ := hG (ε / (2 * (C + 1))) (by positivity)
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hδ
  filter_upwards [eventually_ge_atTop N] with n hn i
  have hsmall : (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) :=
    one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.succ_le_succ hn)
  have key := norm_setIntegral_sub_riemannSum_le μ (t n) (B n) (hc.measurableSet n)
    (hc.pairwiseDisjoint n) (b := b)
    (G := G i) (by rw [hc.iUnion_eq n]; exact hb) (by rw [hc.iUnion_eq n]; exact hbG i)
    (ε := ε / (2 * (C + 1))) (fun y hy z hz =>
      hd i z (hc.iUnion_eq n ▸ Set.mem_biUnion hy hz) y (hc.mem n y hy)
        (((hc.dist_lt n y hy z hz).trans_le hsmall).trans hN))
  rw [hc.iUnion_eq n, ← hCdef] at key
  rw [dist_eq_norm]
  refine key.trans_lt ?_
  rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
  nlinarith
end Pieces
section Convolved
variable {E : Submodule ℝ R4} (μ : Measure E) [IsFiniteMeasureOnCompacts μ]
theorem integrable_smul_comp_sub {b : E → ℂ} (hb : Continuous b) (hbc : HasCompactSupport b)
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W] {u : R4 → W} (hu : Continuous u)
    (x : R4) : Integrable (fun z : E => b z • u (x - z)) μ := by
  refine Continuous.integrable_of_hasCompactSupport
    (hb.smul (hu.comp (continuous_const.sub continuous_subtype_val))) ?_
  exact hbc.smul_right
omit [IsFiniteMeasureOnCompacts μ] in
theorem conv_eq_setIntegral (b : E → ℂ) (u : R4 → ℂ) (x : R4) :
    Smearing.conv μ b u x = ∫ z in tsupport b, b z * u (x - z) ∂μ :=
  (setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz => by
    rw [image_eq_zero_of_notMem_tsupport hz, zero_mul]).symm
variable {b : E → ℂ} {h : R4 → ℂ}
theorem hasFDerivAt_conv (hb : Continuous b) (hbc : HasCompactSupport b) (hh : ContDiff ℝ 1 h)
    (hc : HasCompactSupport h) (x : R4) :
    HasFDerivAt (Smearing.conv μ b h) (∫ z : E, b z • fderiv ℝ h (x - z) ∂μ) x := by
  have hd : Continuous (fderiv ℝ h) := hh.continuous_fderiv one_ne_zero
  obtain ⟨C, hC⟩ := hd.bounded_above_of_compact_support (hc.fderiv ℝ)
  have hbi : Integrable (fun z : E => ‖b z‖ * C) μ :=
    (hb.integrable_of_hasCompactSupport hbc).norm.mul_const C
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (s := Set.univ)
    (F := fun x (z : E) => b z * h (x - z)) (F' := fun x (z : E) => b z • fderiv ℝ h (x - z))
    (bound := fun z => ‖b z‖ * C) univ_mem ?_ ?_ ?_ ?_ hbi ?_
  · exact Eventually.of_forall fun y =>
      (hb.mul (hh.continuous.comp (continuous_const.sub continuous_subtype_val))).aestronglyMeasurable
  · exact integrable_smul_comp_sub μ hb hbc hh.continuous x
  · exact (integrable_smul_comp_sub μ hb hbc hd x).aestronglyMeasurable
  · refine ae_of_all _ fun z y _ => ?_
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (hC _) (norm_nonneg _)
  · refine ae_of_all _ fun z y _ => ?_
    have h₁ : HasFDerivAt h (fderiv ℝ h (y - z)) (y - z) :=
      (hh.differentiable one_ne_zero _).hasFDerivAt
    have h₂ : HasFDerivAt (fun y => h (y - z)) (fderiv ℝ h (y - z)) y := by
      simpa [Function.comp_def] using
        HasFDerivAt.comp y h₁ ((hasFDerivAt_id y).sub_const (z : R4))
    exact h₂.const_mul (b z)
theorem contDiff_conv (hb : Continuous b) (hbc : HasCompactSupport b) (hh : ContDiff ℝ 1 h)
    (hc : HasCompactSupport h) : ContDiff ℝ 1 (Smearing.conv μ b h) := by
  have hd : Continuous (fderiv ℝ h) := hh.continuous_fderiv one_ne_zero
  obtain ⟨C, hC⟩ := hd.bounded_above_of_compact_support (hc.fderiv ℝ)
  have hbi : Integrable (fun z : E => ‖b z‖ * C) μ :=
    (hb.integrable_of_hasCompactSupport hbc).norm.mul_const C
  refine contDiff_one_iff_fderiv.2
    ⟨fun x => (hasFDerivAt_conv μ hb hbc hh hc x).differentiableAt, ?_⟩
  have e : fderiv ℝ (Smearing.conv μ b h) = fun x => ∫ z : E, b z • fderiv ℝ h (x - z) ∂μ := by
    funext x
    exact (hasFDerivAt_conv μ hb hbc hh hc x).fderiv
  rw [e]
  refine continuous_of_dominated (bound := fun z => ‖b z‖ * C)
    (fun x => (integrable_smul_comp_sub μ hb hbc hd x).aestronglyMeasurable)
    (fun x => ae_of_all _ fun z => ?_) hbi (ae_of_all _ fun z => ?_)
  · rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (hC _) (norm_nonneg _)
  · exact Continuous.const_smul (hd.comp (continuous_id.sub continuous_const)) (b z)
theorem fderiv_conv_apply (hb : Continuous b) (hbc : HasCompactSupport b)
    (hh : ContDiff ℝ 1 h) (hc : HasCompactSupport h) (x v : R4) :
    fderiv ℝ (Smearing.conv μ b h) x v = Smearing.conv μ b (fun y => fderiv ℝ h y v) x := by
  have hd : Continuous (fderiv ℝ h) := hh.continuous_fderiv one_ne_zero
  rw [(hasFDerivAt_conv μ hb hbc hh hc x).fderiv,
    ContinuousLinearMap.integral_apply (integrable_smul_comp_sub μ hb hbc hd x)]
  rfl
omit [IsFiniteMeasureOnCompacts μ] in
theorem supp_conv_subset (hbc : HasCompactSupport b) (hc : HasCompactSupport h) :
    IsCompact (supp h + suppIn b) ∧
      supp (Smearing.conv μ b h) ⊆ supp h + suppIn b := by
  have hK : IsCompact (supp h + suppIn b) := by
    rw [supp_eq_tsupport]
    exact hc.isCompact.add (hbc.isCompact.image continuous_subtype_val)
  refine ⟨hK, ?_⟩
  rw [supp_eq_tsupport]
  refine closure_minimal (fun x hx => ?_) hK.isClosed
  by_contra hxS
  refine hx ?_
  have : ∀ z : E, b z * h (x - z) = 0 := by
    intro z
    by_contra hne
    have h₁ : b z ≠ 0 := left_ne_zero_of_mul hne
    have h₂ : h (x - z) ≠ 0 := right_ne_zero_of_mul hne
    refine hxS (Set.mem_add.2 ⟨x - z, ?_, z, ⟨z, subset_tsupport _ h₁, rfl⟩, by simp⟩)
    rw [supp_eq_tsupport]
    exact subset_tsupport _ h₂
  simp [Smearing.conv, this]
end Convolved
section Convergence
theorem tendstoUniformly_comp_sub {u : R4 → ℂ} (hu : UniformContinuous u) {ys : ℕ → R4}
    {y : R4} (hy : Tendsto ys atTop (𝓝 y)) :
    TendstoUniformly (fun j x => u (x - ys j)) (fun x => u (x - y)) atTop := by
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  obtain ⟨δ, hδ, hd⟩ := Metric.uniformContinuous_iff.1 hu ε hε
  filter_upwards [Metric.tendsto_nhds.1 hy δ hδ] with j hj x
  refine hd ?_
  rw [dist_sub_left, dist_comm]
  exact hj
variable {h : R4 → ℂ}
theorem partialDeriv_continuous (hh : ContDiff ℝ 1 h) (v : R4) :
    Continuous fun y => fderiv ℝ h y v :=
  (hh.continuous_fderiv one_ne_zero).clm_apply continuous_const
theorem partialDeriv_hasCompactSupport (hc : HasCompactSupport h) (v : R4) :
    HasCompactSupport fun y => fderiv ℝ h y v :=
  (hc.fderiv ℝ).comp_left (g := fun L : R4 →L[ℝ] ℂ => L v) rfl
theorem tendstoC1_actFn_transl (hh : ContDiff ℝ 1 h) (hc : HasCompactSupport h) {ys : ℕ → R4}
    {y : R4} (hy : Tendsto ys atTop (𝓝 y)) :
    TendstoC1 (fun j => (EuclidMotion.transl (ys j)).actFn h)
      ((EuclidMotion.transl y).actFn h) := by
  have e : ∀ w : R4, (EuclidMotion.transl w).actFn h = fun x => h (x - w) :=
    fun w => funext (EuclidMotion.actFn_transl w h)
  simp only [e]
  refine ⟨tendstoUniformly_comp_sub (hc.uniformContinuous_of_continuous hh.continuous) hy,
    fun m => ?_⟩
  simp only [fderiv_comp_sub]
  exact tendstoUniformly_comp_sub
    ((partialDeriv_hasCompactSupport hc _).uniformContinuous_of_continuous
      (partialDeriv_continuous hh _)) hy
variable {E : Submodule ℝ R4} (μ : Measure E) [IsFiniteMeasureOnCompacts μ]
theorem tendstoUniformly_riemannSum_conv {t : ℕ → Finset E} {B : ℕ → E → Set E} {b : E → ℂ}
    (hcut : FineCover (tsupport b) t B) (hb : Continuous b) (hbc : HasCompactSupport b)
    {u : R4 → ℂ} (hu : Continuous u) (huc : HasCompactSupport u) :
    TendstoUniformly (fun n x => ∑ y ∈ t n, (∫ z in B n y, b z ∂μ) * u (x - y))
      (Smearing.conv μ b u) atTop := by
  have e : Smearing.conv μ b u = fun x => ∫ z in tsupport b, b z * u (x - z) ∂μ :=
    funext (conv_eq_setIntegral μ b u)
  rw [e]
  refine tendstoUniformly_riemannSum μ hcut (hb.integrable_of_hasCompactSupport hbc).integrableOn
    (fun (x : R4) (z : E) => u (x - z))
    (fun x => (integrable_smul_comp_sub μ hb hbc hu x).integrableOn) fun ε hε => ?_
  obtain ⟨δ, hδ, hd⟩ :=
    Metric.uniformContinuous_iff.1 (huc.uniformContinuous_of_continuous hu) ε hε
  refine ⟨δ, hδ, fun x z _ y _ hzy => ?_⟩
  rw [← dist_eq_norm]
  refine (hd ?_).le
  rw [dist_sub_left]
  exact hzy
theorem fderiv_sum_actFn_transl (hh : ContDiff ℝ 1 h) (t : Finset E) (w : E → ℂ) (x v : R4) :
    fderiv ℝ (∑ y ∈ t, w y • (EuclidMotion.transl (y : R4)).actFn h) x v =
      ∑ y ∈ t, w y * fderiv ℝ h (x - y) v := by
  have hd : HasFDerivAt (∑ y ∈ t, w y • (EuclidMotion.transl (y : R4)).actFn h)
      (∑ y ∈ t, w y • fderiv ℝ h (x - y)) x := by
    refine HasFDerivAt.sum fun y _ => ?_
    have e : w y • (EuclidMotion.transl (y : R4)).actFn h =
        fun x => w y * h (x - y) := by
      funext x
      simp [EuclidMotion.actFn_transl]
    rw [e]
    have h₁ : HasFDerivAt h (fderiv ℝ h (x - y)) (x - y) :=
      (hh.differentiable one_ne_zero _).hasFDerivAt
    have h₂ : HasFDerivAt (fun x => h (x - y)) (fderiv ℝ h (x - y)) x := by
      simpa [Function.comp_def] using
        HasFDerivAt.comp x h₁ ((hasFDerivAt_id x).sub_const (y : R4))
    exact h₂.const_mul (w y)
  rw [hd.fderiv]
  simp
end Convergence
section OneSlot
def testsIn (A : Set R4) : Set (R4 → ℂ) :=
  {u | u ∈ C1c ℂ ∧ supp u ⊆ A}
theorem zero_mem_testsIn (A : Set R4) : (0 : R4 → ℂ) ∈ testsIn A := by
  refine ⟨(mem_C1c_iff _).2 ⟨contDiff_const, HasCompactSupport.zero⟩, ?_⟩
  rw [supp_eq_tsupport, tsupport, Function.support_zero, closure_empty]
  exact Set.empty_subset _
theorem linComb_mem_testsIn {A : Set R4} {u v : R4 → ℂ} (hu : u ∈ testsIn A)
    (hv : v ∈ testsIn A) (a a' : ℂ) : a • u + a' • v ∈ testsIn A := by
  have hu' := (mem_C1c_iff u).1 hu.1
  have hv' := (mem_C1c_iff v).1 hv.1
  refine ⟨(mem_C1c_iff _).2 ⟨(hu'.1.const_smul a).add (hv'.1.const_smul a'), ?_⟩, ?_⟩
  · exact (hu'.2.comp_left (g := fun z : ℂ => a • z) (smul_zero a)).add
      (hv'.2.comp_left (g := fun z : ℂ => a' • z) (smul_zero a'))
  · have hsub : Function.support (a • u + a' • v) ⊆ Function.support u ∪ Function.support v := by
      intro x hx
      by_contra hn
      simp only [Set.mem_union, Function.mem_support, not_or, not_not] at hn
      simp [hn.1, hn.2] at hx
    have h₁ := hu.2
    have h₂ := hv.2
    rw [supp_eq_tsupport] at h₁ h₂ ⊢
    refine (closure_mono hsub).trans ?_
    rw [closure_union]
    exact Set.union_subset h₁ h₂
theorem sum_smul_mem_testsIn {A : Set R4} {ι : Type*} (t : Finset ι) (a : ι → ℂ)
    (u : ι → R4 → ℂ) (h : ∀ y ∈ t, u y ∈ testsIn A) :
    ∑ y ∈ t, a y • u y ∈ testsIn A := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using zero_mem_testsIn A
  | insert y t hy IH =>
    rw [Finset.sum_insert hy]
    have h₁ := linComb_mem_testsIn (h y (Finset.mem_insert_self y t))
      (IH fun y' hy' => h y' (Finset.mem_insert_of_mem hy')) (a y) 1
    simpa using h₁
variable {E : Submodule ℝ R4} (μ : Measure E) [IsFiniteMeasureOnCompacts μ]
variable {A : Set R4} {L : (R4 → ℂ) → ℂ} {b : E → ℂ} {h : R4 → ℂ}
omit [IsFiniteMeasureOnCompacts μ] in
theorem actFn_transl_mem_testsIn (hh : h ∈ C1c ℂ)
    (hA : supp h + suppIn b ⊆ A) {z : E} (hz : z ∈ tsupport b) :
    (EuclidMotion.transl (z : R4)).actFn h ∈ testsIn A :=
  ⟨actFn_transl_mem hh z, fun x hx =>
    hA (Set.mem_add.2 ⟨x - z, (mem_supp_actFn_transl _ _ _).1 hx, z, ⟨z, hz, rfl⟩, by simp⟩)⟩
omit [IsFiniteMeasureOnCompacts μ] in
theorem continuousOn_apply_actFn_transl
    (hL₂ : ∀ (g : R4 → ℂ) (gs : ℕ → R4 → ℂ), g ∈ testsIn A →
      (∀ j, gs j ∈ testsIn A) → TendstoC1 gs g →
      Tendsto (fun j => L (gs j)) atTop (𝓝 (L g)))
    (hh : h ∈ C1c ℂ) (hA : supp h + suppIn b ⊆ A) :
    ContinuousOn (fun z : E => L ((EuclidMotion.transl (z : R4)).actFn h))
      (tsupport b) := by
  have hh' := (mem_C1c_iff h).1 hh
  rw [continuousOn_iff_continuous_domRestrict, continuous_iff_seqContinuous]
  intro zs z hz
  have hy : Tendsto (fun j => ((zs j : E) : R4)) atTop (𝓝 ((z : E) : R4)) :=
    ((continuous_subtype_val.comp continuous_subtype_val).tendsto z).comp hz
  exact hL₂ _ _ (actFn_transl_mem_testsIn hh hA z.2)
    (fun j => actFn_transl_mem_testsIn hh hA (zs j).2) (tendstoC1_actFn_transl hh'.1 hh'.2 hy)
theorem conv_mem_testsIn (hb : Continuous b) (hbc : HasCompactSupport b)
    (hh : h ∈ C1c ℂ) (hA : supp h + suppIn b ⊆ A) :
    Smearing.conv μ b h ∈ testsIn A := by
  have hh' := (mem_C1c_iff h).1 hh
  obtain ⟨hK, hs⟩ := supp_conv_subset μ hbc hh'.2
  refine ⟨(mem_C1c_iff _).2 ⟨contDiff_conv μ hb hbc hh'.1 hh'.2, ?_⟩, hs.trans hA⟩
  rw [supp_eq_tsupport] at hs
  exact hK.of_isClosed_subset (isClosed_tsupport _) hs
theorem apply_conv_eq_integral
    (hL₁ : ∀ (t : Finset E) (a : E → ℂ) (u : E → R4 → ℂ), (∀ y ∈ t, u y ∈ testsIn A) →
      L (∑ y ∈ t, a y • u y) = ∑ y ∈ t, a y * L (u y))
    (hL₂ : ∀ (g : R4 → ℂ) (gs : ℕ → R4 → ℂ), g ∈ testsIn A →
      (∀ j, gs j ∈ testsIn A) → TendstoC1 gs g →
      Tendsto (fun j => L (gs j)) atTop (𝓝 (L g)))
    (hb : Continuous b) (hbc : HasCompactSupport b)
    (hh : h ∈ C1c ℂ) (hA : supp h + suppIn b ⊆ A) :
    L (Smearing.conv μ b h) =
      ∫ z : E, b z * L ((EuclidMotion.transl (z : R4)).actFn h) ∂μ := by
  have hh' := (mem_C1c_iff h).1 hh
  have hK : IsCompact (tsupport b) := hbc
  obtain ⟨t, B, hcut⟩ := exists_fineCover hK (isClosed_tsupport b).measurableSet
  have hcont := continuousOn_apply_actFn_transl hL₂ hh hA
  let w : ℕ → E → ℂ := fun n y => ∫ z in B n y, b z ∂μ
  let s : ℕ → R4 → ℂ := fun n =>
    ∑ y ∈ t n, w n y • (EuclidMotion.transl (y : R4)).actFn h
  have hs : ∀ n, s n ∈ testsIn A := fun n =>
    sum_smul_mem_testsIn (t n) (w n) _ fun y hy =>
      actFn_transl_mem_testsIn hh hA (hcut.mem n y hy)
  have hsapply : ∀ n, s n = fun x => ∑ y ∈ t n, w n y * h (x - y) := by
    intro n
    funext x
    simp [s, Finset.sum_apply, EuclidMotion.actFn_transl]
  have hconv : TendstoC1 s (Smearing.conv μ b h) := by
    refine ⟨?_, fun m => ?_⟩
    · rw [show s = fun n x => ∑ y ∈ t n, w n y * h (x - y) from funext hsapply]
      exact tendstoUniformly_riemannSum_conv μ hcut hb hbc hh'.1.continuous hh'.2
    · have e₁ : ∀ n x, fderiv ℝ (s n) x (Pi.single m 1) =
          ∑ y ∈ t n, w n y * fderiv ℝ h (x - y) (Pi.single m 1) :=
        fun n x => fderiv_sum_actFn_transl hh'.1 (t n) (w n) x _
      have e₂ : (fun x => fderiv ℝ (Smearing.conv μ b h) x (Pi.single m 1)) =
          Smearing.conv μ b (fun y => fderiv ℝ h y (Pi.single m 1)) :=
        funext fun x => fderiv_conv_apply μ hb hbc hh'.1 hh'.2 x _
      simp only [e₁]
      rw [e₂]
      exact tendstoUniformly_riemannSum_conv μ hcut hb hbc (partialDeriv_continuous hh'.1 _)
        (partialDeriv_hasCompactSupport hh'.2 _)
  have lim₁ := hL₂ _ s (conv_mem_testsIn μ hb hbc hh hA) hs hconv
  have hLs : ∀ n, L (s n) =
      ∑ y ∈ t n, w n y * L ((EuclidMotion.transl (y : R4)).actFn h) := fun n =>
    hL₁ (t n) (w n) (fun y => (EuclidMotion.transl (y : R4)).actFn h) fun y hy =>
      actFn_transl_mem_testsIn hh hA (hcut.mem n y hy)
  simp only [hLs] at lim₁
  have lim₂ := (tendstoUniformly_riemannSum μ hcut
    (hb.integrable_of_hasCompactSupport hbc).integrableOn
    (fun (_ : Unit) (z : E) => L ((EuclidMotion.transl (z : R4)).actFn h))
    (fun _ => (hb.continuousOn.mul hcont).integrableOn_compact hK) (fun ε hε => by
      obtain ⟨δ, hδ, hd⟩ := Metric.uniformContinuousOn_iff.1
        (hK.uniformContinuousOn_of_continuous hcont) ε hε
      refine ⟨δ, hδ, fun _ z hz y hy hzy => ?_⟩
      rw [← dist_eq_norm]
      exact (hd z hz y hy hzy).le)).tendsto_at ()
  rw [tendsto_nhds_unique lim₁ lim₂]
  exact setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz => by
    rw [image_eq_zero_of_notMem_tsupport hz, zero_mul]
end OneSlot
section Containers
theorem exists_separatedInBalls {q : ℕ} (hq : 2 ≤ q) {A : Fin q → Set R4}
    (hc : ∀ l, IsCompact (A l)) (hd : Pairwise fun k l => Disjoint (A k) (A l)) :
    ∃ R d : ℝ, 0 < R ∧ 0 < d ∧ Moments.SeparatedInBalls A R d := by apply _root_.YangMills.Construction.EuclideanFunctionals.InsertionForm.exists_separatedInBalls <;> assumption
end Containers
section Slots
open Moments (EntriesSupportedIn MomentContinuous)
open TensorComponents (IsComplexMultilinear)
theorem tendstoC1_const (f : R4 → ℂ) : TendstoC1 (fun _ => f) f := by
  have h : ∀ {Z : Type} (g : R4 → Z) [PseudoMetricSpace Z],
      TendstoUniformly (fun (_ : ℕ) => g) g atTop := by
    intro Z g _
    rw [Metric.tendstoUniformly_iff]
    intro ε hε
    exact Eventually.of_forall fun _ x => by simpa using hε
  exact ⟨h f, fun m => h _⟩
theorem continuous_mul_of_continuousOn_of_eq_zero {X : Type*} [TopologicalSpace X]
    {f u : X → ℂ} {K : Set X}
    (hf : Continuous f) (hK : IsClosed K) (hu : ContinuousOn u K) (h0 : ∀ x, x ∉ K → f x = 0) :
    Continuous fun x => f x * u x := by
  have h₁ : ContinuousOn (fun x => f x * u x) K := hf.continuousOn.mul hu
  have hcl : closure Kᶜ ⊆ f ⁻¹' {0} :=
    closure_minimal (fun x hx => h0 x hx) (isClosed_singleton.preimage hf)
  have h₂ : ContinuousOn (fun x => f x * u x) (closure Kᶜ) :=
    (continuousOn_const (c := (0 : ℂ))).congr fun x hx => by
      have : f x = 0 := hcl hx
      simp [this]
  have h₃ := h₁.union_of_isClosed h₂ hK isClosed_closure
  have e : K ∪ closure Kᶜ = Set.univ :=
    Set.eq_univ_of_univ_subset fun x _ => by
      by_cases hx : x ∈ K
      · exact Or.inl hx
      · exact Or.inr (subset_closure hx)
  rw [e] at h₃
  exact continuousOn_univ.1 h₃
variable {S : ConnFamily} {q : ℕ} {A : Fin q → Set R4}
theorem complexFamily_of_componentsSupportedIn (hq : 1 ≤ q)
    (hd : Pairwise fun k l => Disjoint (A k) (A l))
    {f : Fin q → R4 → ℂ} (hf : EntriesSupportedIn A f) : ComplexComponents f :=
  ⟨hq, fun l => (hf l).1, fun _ _ hkl => (hd hkl).mono (hf _).2 (hf _).2⟩
theorem componentsSupportedIn_update {g : Fin q → R4 → ℂ} {l : Fin q}
    (hg : ∀ k, k ≠ l → g k ∈ testsIn (A k)) {u : R4 → ℂ} (hu : u ∈ testsIn (A l)) :
    EntriesSupportedIn A (Function.update g l u) := by
  intro k
  by_cases hk : k = l
  · subst hk
    rw [Function.update_self]
    exact hu
  · rw [Function.update_of_ne hk]
    exact hg k hk
variable (hq : 1 ≤ q) (hd : Pairwise fun k l => Disjoint (A k) (A l))
  (hlin : IsComplexMultilinear S)
  (hcont : ∀ f, EntriesSupportedIn A f → MomentContinuous S A f)
  {g : Fin q → R4 → ℂ} {l : Fin q} (hg : ∀ k, k ≠ l → g k ∈ testsIn (A k))
include hq hd hlin hg
theorem valueAt_update_linComb {u v : R4 → ℂ} (hu : u ∈ testsIn (A l))
    (hv : v ∈ testsIn (A l)) (a a' : ℂ) :
    valueAt S (Function.update g l (a • u + a' • v)) =
      a * valueAt S (Function.update g l u) +
        a' * valueAt S (Function.update g l v) := by
  have h := (hlin q l a a' (Function.update g l u) v
    (complexFamily_of_componentsSupportedIn hq hd (componentsSupportedIn_update hg hu))
    (by
      rw [Function.update_idem]
      exact complexFamily_of_componentsSupportedIn hq hd (componentsSupportedIn_update hg hv))).2
  simp only [Function.update_self, Function.update_idem] at h
  exact h
theorem valueAt_update_sum {E : Type*} (t : Finset E) (a : E → ℂ) (u : E → R4 → ℂ)
    (hu : ∀ y ∈ t, u y ∈ testsIn (A l)) :
    valueAt S (Function.update g l (∑ y ∈ t, a y • u y)) =
      ∑ y ∈ t, a y * valueAt S (Function.update g l (u y)) := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    have h := valueAt_update_linComb hq hd hlin hg (zero_mem_testsIn (A l))
      (zero_mem_testsIn (A l)) 0 0
    simpa using h
  | insert y t hy IH =>
    have h := valueAt_update_linComb hq hd hlin hg (hu y (Finset.mem_insert_self y t))
      (sum_smul_mem_testsIn t a u fun y' hy' => hu y' (Finset.mem_insert_of_mem hy')) (a y) 1
    rw [Finset.sum_insert hy, Finset.sum_insert hy,
      ← IH fun y' hy' => hu y' (Finset.mem_insert_of_mem hy')]
    simpa using h
omit hq hd hlin in
include hcont in
theorem tendsto_valueAt_update (g₀ : R4 → ℂ) (gs : ℕ → R4 → ℂ) (h₀ : g₀ ∈ testsIn (A l))
    (hs : ∀ j, gs j ∈ testsIn (A l)) (hc : TendstoC1 gs g₀) :
    Tendsto (fun j => valueAt S (Function.update g l (gs j))) atTop
      (𝓝 (valueAt S (Function.update g l g₀))) := by
  refine hcont _ (componentsSupportedIn_update hg h₀) (fun j => Function.update g l (gs j))
    (fun j _ => componentsSupportedIn_update hg (hs j)) fun k => ?_
  by_cases hk : k = l
  · subst hk
    simpa only [Function.update_self] using hc
  · simp only [Function.update_of_ne hk]
    exact tendstoC1_const _
include hcont in
theorem valueAt_update_conv {E : Submodule ℝ R4} (μ : Measure E) [IsFiniteMeasureOnCompacts μ]
    {b : E → ℂ} {h : R4 → ℂ} (hb : Continuous b) (hbc : HasCompactSupport b)
    (hh : h ∈ C1c ℂ) (hA : supp h + suppIn b ⊆ A l) :
    valueAt S (Function.update g l (Smearing.conv μ b h)) =
      ∫ z : E, b z * valueAt S
        (Function.update g l ((EuclidMotion.transl (z : R4)).actFn h)) ∂μ :=
  apply_conv_eq_integral μ (L := fun u => valueAt S (Function.update g l u))
    (fun t a u hu => valueAt_update_sum hq hd hlin hg t a u hu)
    (fun g₀ gs h₀ hs hc => tendsto_valueAt_update hcont hg g₀ gs h₀ hs hc) hb hbc hh hA
end Slots
section Main
open Moments (EntriesSupportedIn MomentContinuous)
open TensorComponents (IsComplexMultilinear)
variable {S : ConnFamily} {E : Submodule ℝ R4} {p q : ℕ} {A : Fin q → Set R4}
  {h : Fin q → R4 → ℂ} {b : Fin p → E → ℂ}
theorem convInSets_of_data (μ : Measure E) [IsFiniteMeasureOnCompacts μ]
    (d : Data A h b) : ConvInSets μ A h b := fun l hl =>
  conv_mem_testsIn μ (d.cont _) (d.compactSupport _) (d.mem_C1c l)
    (d.conv_supp l hl)
theorem componentsSupportedIn_shiftComponents (d : Data A h b) {z : Fin p → E}
    (hz : z ∈ Set.pi Set.univ fun l => tsupport (b l)) :
    EntriesSupportedIn A (shiftSmearingTuple z h) := by
  intro l
  simp only [shiftSmearingTuple]
  split_ifs with hl
  · exact actFn_transl_mem_testsIn (d.mem_C1c l) (d.conv_supp l hl)
      (hz ⟨l, hl⟩ (Set.mem_univ _))
  · exact ⟨d.mem_C1c l, d.rest_supp l hl⟩
theorem continuousOn_valueAt_shiftEntries
    (hcont : ∀ f, EntriesSupportedIn A f → MomentContinuous S A f)
    (d : Data A h b) :
    ContinuousOn (fun z : Fin p → E => valueAt S (shiftSmearingTuple z h))
      (Set.pi Set.univ fun l => tsupport (b l)) := by
  rw [continuousOn_iff_continuous_domRestrict, continuous_iff_seqContinuous]
  intro zs z hz
  refine hcont _ (componentsSupportedIn_shiftComponents d z.2)
    (fun j => shiftSmearingTuple (zs j : Fin p → E) h)
    (fun j _ => componentsSupportedIn_shiftComponents d (zs j).2) fun l => ?_
  by_cases hl : (l : ℕ) < p
  · simp only [shiftSmearingTuple, dif_pos hl]
    have hh := (mem_C1c_iff _).1 (d.mem_C1c l)
    refine tendstoC1_actFn_transl hh.1 hh.2 ?_
    have hc : Continuous fun w : (Set.pi Set.univ fun l => tsupport (b l) : Set (Fin p → E)) =>
        (((w : Fin p → E) ⟨l, hl⟩ : E) : R4) :=
      continuous_subtype_val.comp ((continuous_apply _).comp continuous_subtype_val)
    exact (hc.tendsto z).comp hz
  · simp only [shiftSmearingTuple, dif_neg hl]
    exact tendstoC1_const _
theorem prod_eq_zero_of_not_mem_pi {z : Fin p → E}
    (hz : z ∉ Set.pi Set.univ fun l => tsupport (b l)) :
    ∏ l, b l (z l) = 0 := by
  simp only [Set.mem_pi, Set.mem_univ, true_implies, not_forall] at hz
  obtain ⟨l, hl⟩ := hz
  exact Finset.prod_eq_zero (Finset.mem_univ l) (image_eq_zero_of_notMem_tsupport hl)
theorem continuous_integrand (hcont : ∀ f, EntriesSupportedIn A f → MomentContinuous S A f)
    (d : Data A h b) : Continuous (integrand S b h) :=
  continuous_mul_of_continuousOn_of_eq_zero
    (continuous_finsetProd _ fun l _ => (d.cont l).comp (continuous_apply l))
    (isClosed_set_pi fun _ _ => isClosed_tsupport _) (continuousOn_valueAt_shiftEntries hcont d)
    fun _ hz => prod_eq_zero_of_not_mem_pi hz
theorem hasCompactSupport_integrand (d : Data A h b) : HasCompactSupport (integrand S b h) :=
  HasCompactSupport.intro (isCompact_univ_pi fun l => d.compactSupport l) fun z hz => by
    simp only [integrand]
    rw [prod_eq_zero_of_not_mem_pi hz, zero_mul]
theorem valueAt_convComponents_eq_integral (μ : Measure E) [IsFiniteMeasureOnCompacts μ]
    (hq : 1 ≤ q)
    (hd : Pairwise fun k l => Disjoint (A k) (A l)) (hlin : IsComplexMultilinear S)
    (hcont : ∀ f, EntriesSupportedIn A f → MomentContinuous S A f) (p : ℕ) :
    p ≤ q → ∀ (h : Fin q → R4 → ℂ) (b : Fin p → E → ℂ), Data A h b →
      valueAt S (convEntries μ b h) =
        ∫ z, integrand S b h z ∂(Measure.pi fun _ : Fin p => μ) := by
  have hσ : SigmaFinite μ := inferInstance
  induction p with
  | zero =>
    intro _ h b _
    have e : convEntries μ b h = h := by
      funext l
      simp [convEntries]
    have e₂ : ∀ z : Fin 0 → E, shiftSmearingTuple z h = h := by
      intro z
      funext l
      simp [shiftSmearingTuple]
    rw [e, Measure.pi_of_empty (fun _ : Fin 0 => μ), integral_dirac]
    simp [integrand, e₂]
  | succ p IH =>
    intro hp h b d
    have hpq : p < q := hp
    let i : Fin q := ⟨p, hpq⟩
    let bl : Fin p → E → ℂ := fun l => b (Fin.castSucc l)
    let bz : E → ℂ := b (Fin.last p)
    let g := convEntries μ bl h
    let h' : E → Fin q → R4 → ℂ := fun w =>
      Function.update h i ((EuclidMotion.transl (w : R4)).actFn (h i))
    have hi_lt : (i : ℕ) < p + 1 := Nat.lt_succ_self p
    have hi_not : ¬ (i : ℕ) < p := lt_irrefl p
    have hsupp : supp (h i) + suppIn bz ⊆ A i := d.conv_supp i hi_lt
    have hkp : ∀ k : Fin q, k ≠ i → (k : ℕ) ≠ p := fun k hk e => hk (Fin.ext e)
    have hh'k : ∀ w k, k ≠ i → h' w k = h k := fun w k hk => Function.update_of_ne hk _ _
    have hh'i : ∀ w, h' w i = (EuclidMotion.transl (w : R4)).actFn (h i) :=
      fun w => Function.update_self _ _ _
    have hg : ∀ k, k ≠ i → g k ∈ testsIn (A k) := by
      intro k hk
      have := hkp k hk
      simp only [g, convEntries]
      split_ifs with hl
      · exact conv_mem_testsIn μ (d.cont _) (d.compactSupport _) (d.mem_C1c k)
          (d.conv_supp k (Nat.lt_succ_of_lt hl))
      · exact ⟨d.mem_C1c k, d.rest_supp k (by omega)⟩
    have e₁ : convEntries μ b h = Function.update g i (Smearing.conv μ bz (h i)) := by
      funext k
      by_cases hk : k = i
      · rw [hk, Function.update_self]
        exact dif_pos hi_lt
      · rw [Function.update_of_ne hk]
        have := hkp k hk
        simp only [g, convEntries]
        by_cases hl : (k : ℕ) < p
        · rw [dif_pos hl, dif_pos (Nat.lt_succ_of_lt hl)]
          rfl
        · rw [dif_neg hl, dif_neg (by omega)]
    have e₂ : ∀ w, convEntries μ bl (h' w) =
        Function.update g i ((EuclidMotion.transl (w : R4)).actFn (h i)) := by
      intro w
      funext k
      by_cases hk : k = i
      · rw [hk, Function.update_self, ← hh'i w]
        exact dif_neg hi_not
      · rw [Function.update_of_ne hk]
        simp only [g, convEntries]
        rw [hh'k w k hk]
    have e₃ : ∀ z : Fin (p + 1) → E, shiftSmearingTuple z h =
        shiftSmearingTuple (fun j => z (Fin.castSucc j)) (h' (z (Fin.last p))) := by
      intro z
      funext k
      by_cases hk : k = i
      · rw [hk]
        have r₁ : shiftSmearingTuple z h i =
            (EuclidMotion.transl (z ⟨i, hi_lt⟩ : R4)).actFn (h i) := dif_pos hi_lt
        have r₂ : shiftSmearingTuple (fun j => z (Fin.castSucc j)) (h' (z (Fin.last p))) i =
            h' (z (Fin.last p)) i := dif_neg hi_not
        rw [r₁, r₂, hh'i]
        rfl
      · have := hkp k hk
        simp only [shiftSmearingTuple]
        rw [hh'k _ k hk]
        by_cases hl : (k : ℕ) < p
        · rw [dif_pos hl, dif_pos (Nat.lt_succ_of_lt hl)]
          rfl
        · rw [dif_neg hl, dif_neg (by omega)]
    have dIH : ∀ w ∈ tsupport bz, Data A (h' w) bl := fun w hw =>
      { compact := d.compact
        pairwise_disjoint := d.pairwise_disjoint
        mem_C1c := fun k => by
          by_cases hk : k = i
          · rw [hk, hh'i]
            exact actFn_transl_mem (d.mem_C1c i) _
          · rw [hh'k w k hk]
            exact d.mem_C1c k
        cont := fun _ => d.cont _
        compactSupport := fun _ => d.compactSupport _
        conv_supp := fun l hl => by
          have hk : l ≠ i := fun e => by
            rw [e] at hl
            exact hi_not hl
          rw [hh'k w l hk]
          exact d.conv_supp l (Nat.lt_succ_of_lt hl)
        rest_supp := fun l hl => by
          by_cases hk : l = i
          · rw [hk, hh'i]
            exact (actFn_transl_mem_testsIn (d.mem_C1c i) hsupp hw).2
          · rw [hh'k w l hk]
            have := hkp l hk
            exact d.rest_supp l (by omega) }
    have hm := measurePreserving_piFinSuccAbove (fun _ : Fin (p + 1) => μ) (Fin.last p)
    let G : E × (Fin p → E) → ℂ := fun w => bz w.1 * integrand S bl (h' w.1) w.2
    have hGf : ∀ z, G (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (p + 1) => E) (Fin.last p) z) =
        integrand S b h z := by
      intro z
      have e : MeasurableEquiv.piFinSuccAbove (fun _ : Fin (p + 1) => E) (Fin.last p) z =
          (z (Fin.last p), fun j => z (Fin.castSucc j)) := by
        refine Prod.ext rfl (funext fun j => ?_)
        simp [MeasurableEquiv.piFinSuccAbove, Fin.init]
      rw [e]
      simp only [G, integrand]
      rw [e₃ z, Fin.prod_univ_castSucc]
      simp only [bl, bz]
      ring
    have hint : Integrable (integrand S b h) (Measure.pi fun _ : Fin (p + 1) => μ) :=
      (continuous_integrand hcont d).integrable_of_hasCompactSupport
        (hasCompactSupport_integrand d)
    have hGint : Integrable G (μ.prod (Measure.pi fun _ : Fin p => μ)) := by
      refine (hm.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _)).1 ?_
      have e : G ∘ MeasurableEquiv.piFinSuccAbove (fun _ : Fin (p + 1) => E) (Fin.last p) =
          integrand S b h := funext hGf
      rw [e]
      exact hint
    have e₄ : ∀ w : E, bz w * valueAt S
        (Function.update g i ((EuclidMotion.transl (w : R4)).actFn (h i))) =
        ∫ z', G (w, z') ∂(Measure.pi fun _ : Fin p => μ) := by
      intro w
      by_cases hw : w ∈ tsupport bz
      · simp only [G]
        rw [integral_const_mul, ← IH hpq.le (h' w) bl (dIH w hw), e₂ w]
      · have h0 : bz w = 0 := image_eq_zero_of_notMem_tsupport hw
        simp [G, h0]
    rw [e₁, valueAt_update_conv hq hd hlin hcont hg μ (d.cont _) (d.compactSupport _)
      (d.mem_C1c i) hsupp]
    refine (integral_congr_ae (ae_of_all _ e₄)).trans ?_
    rw [← integral_prod G hGint, ← hm.integral_comp' G]
    exact integral_congr_ae (ae_of_all _ hGf)
end Main
theorem holds (hmoments : Moments.MomentBoundsTheorem)
    (htensor : TensorComponents.CenteredSeesTensorComps) : Holds := by
  refine ⟨fun E μ μ' h h' => isLebesgueOn_unique μ μ' h h', ?_⟩
  intro c S σ q p hq hp₁ hpq E μ hμ A h b d
  have hfin := isFiniteMeasureOnCompacts_of_isLebesgueOn hμ
  have hlin := (htensor S).2.2.2.1
  obtain ⟨R, r, hR, hr, hsep⟩ := exists_separatedInBalls hq d.compact d.pairwise_disjoint
  have hcont : ∀ f, Moments.EntriesSupportedIn A f →
      Moments.MomentContinuous S A f := fun f hf =>
    (hmoments c S σ q hq R r hR hr A hsep f f hf hf).2.2.1
  have hq₁ : 1 ≤ q := by omega
  refine ⟨convInSets_of_data μ d, ⟨isCompact_univ_pi fun l => d.compactSupport l,
    fun z hz => complexFamily_of_componentsSupportedIn hq₁ d.pairwise_disjoint
      (componentsSupportedIn_shiftComponents d hz),
    continuousOn_valueAt_shiftEntries hcont d⟩,
    valueAt_convComponents_eq_integral μ hq₁ d.pairwise_disjoint hlin hcont p hpq h b d,
    continuous_integrand hcont d, hasCompactSupport_integrand d⟩
end EuclideanFunctionals.Smearing
end
end YangMills.Construction
