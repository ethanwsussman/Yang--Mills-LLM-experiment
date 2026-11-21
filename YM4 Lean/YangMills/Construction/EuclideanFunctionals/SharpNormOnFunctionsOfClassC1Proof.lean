import YangMills.Construction.EuclideanFunctionals.ExpansionTranslationsContinuityAndSmearingOfTheInsertionValueProof
import Mathlib
set_option autoImplicit false
open Filter Topology YangMills.Construction.ReflectionPositivity.AxisMirror YangMills.Construction.MetricNotions YangMills.Construction.TorusMetric
noncomputable section
namespace YangMills.Construction.EuclideanFunctionals.SharpNormC1
theorem norm_le_euclidNormVec (v : R4) : ‖v‖ ≤ euclidNormVec v := by apply _root_.YangMills.Construction.EuclideanFunctionals.Moments.norm_le_euclidNormVec <;> assumption
theorem euclidNormVec_le_two_mul_norm (v : R4) : euclidNormVec v ≤ 2 * ‖v‖ := by apply _root_.YangMills.Construction.EuclideanFunctionals.Moments.euclidNormVec_le_two_mul_norm <;> assumption
abbrev r4Metric : R4 → R4 → ℝ := Ambient.metric defaultMirrorData Ambient.euclidean
theorem isOpenWrt_of_isOpen {U : Set R4} (hU : IsOpen U) : IsOpenWrt r4Metric U := by
  intro x hx
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU x hx
  refine ⟨ε, hε, fun y hy => hball ?_⟩
  rw [Metric.mem_ball, dist_comm, dist_eq_norm]
  exact (norm_le_euclidNormVec _).trans_lt hy
theorem closureWrt_subset_closure (S : Set R4) : closureWrt r4Metric S ⊆ closure S := by
  intro x hx
  refine Metric.mem_closure_iff.2 fun ε hε => ?_
  obtain ⟨y, hy, hdist⟩ := hx ε hε
  exact ⟨y, hy, by rw [dist_eq_norm]; exact (norm_le_euclidNormVec _).trans_lt hdist⟩
theorem closure_subset_closureWrt (S : Set R4) : closure S ⊆ closureWrt r4Metric S := by
  intro x hx r hr
  obtain ⟨y, hy, hdist⟩ := Metric.mem_closure_iff.1 hx (r / 2) (half_pos hr)
  refine ⟨y, hy, ?_⟩
  rw [dist_eq_norm] at hdist
  have htwo := euclidNormVec_le_two_mul_norm (x - y)
  change euclidNormVec (x - y) < r
  linarith
theorem isCompact_of_isCompactWrt {S : Set R4} (hS : IsCompactWrt r4Metric S) :
    IsCompact S := by
  refine isCompact_of_finite_subcover fun {ι} U hU hcover => ?_
  obtain ⟨V, hsub, hfin, hcov⟩ := hS (Set.range U)
    (by rintro _ ⟨i, rfl⟩; exact isOpenWrt_of_isOpen (hU i))
    (by rwa [Set.sUnion_range])
  choose idx hidx using fun W : V => hsub W.2
  have : Finite V := hfin
  have : Fintype V := Fintype.ofFinite V
  classical
  refine ⟨Finset.univ.image idx, fun x hx => ?_⟩
  obtain ⟨W, hW, hxW⟩ := hcov hx
  refine Set.mem_iUnion₂.2 ⟨idx ⟨W, hW⟩, Finset.mem_image_of_mem _ (Finset.mem_univ _), ?_⟩
  rw [hidx ⟨W, hW⟩]
  exact hxW
theorem contDiff_hasCompactSupport_of_mem {f : R4 → ℂ} (hf : f ∈ C1c ℂ) :
    ContDiff ℝ 1 f ∧ HasCompactSupport f := by
  refine ⟨hf.1, ?_⟩
  have hsupp : supp f = tsupport f :=
    Set.Subset.antisymm (closureWrt_subset_closure _) (closure_subset_closureWrt _)
  have hcpt : IsCompact (supp f) := isCompact_of_isCompactWrt hf.2
  rw [hsupp] at hcpt
  exact hcpt
theorem hasDerivAt_comp_line {f : R4 → ℂ} (hf : ContDiff ℝ 1 f) (x v : R4) (t : ℝ) :
    HasDerivAt (fun s : ℝ => f (x + s • v)) (fderiv ℝ f (x + t • v) v) t := by
  have hfd : HasFDerivAt f (fderiv ℝ f (x + t • v)) (x + t • v) :=
    ((hf.differentiable (by norm_num)) _).hasFDerivAt
  have hline : HasDerivAt (fun s : ℝ => x + s • v) v t := by
    simpa using ((hasDerivAt_id t).smul_const v).const_add x
  exact hfd.comp_hasDerivAt t hline
theorem partialDerivR4_eq_fderiv {f : R4 → ℂ} (hf : ContDiff ℝ 1 f) (i : Fin 4) (x : R4) :
    TestFunctions.partialDerivR4 i f x = fderiv ℝ f x (Pi.single i (1 : ℝ)) := (hf.differentiable (by decide) x).lineDeriv_eq_fderiv
theorem partialDerivR4_sub {f g : R4 → ℂ} (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g)
    (i : Fin 4) (x : R4) :
    TestFunctions.partialDerivR4 i (f - g) x =
      fderiv ℝ f x (Pi.single i (1 : ℝ)) - fderiv ℝ g x (Pi.single i (1 : ℝ)) := by
  rw [partialDerivR4_eq_fderiv (f := f - g) (hf.sub hg), fderiv_sub
    ((hf.differentiable (by norm_num)) x) ((hg.differentiable (by norm_num)) x)]
  rfl
theorem partialDerivR4_transl (b : R4) (i : Fin 4) (f : R4 → ℂ) (x : R4) :
    TestFunctions.partialDerivR4 i ((EuclidMotion.transl b).actFn f) x =
      TestFunctions.partialDerivR4 i f (x - b) := by
  simp only [TestFunctions.partialDerivR4, EuclidMotion.actFn_transl]
  congr 1
  funext t
  congr 1
  abel
theorem partialDerivR4_continuous_hasCompactSupport {f : R4 → ℂ} (hf : ContDiff ℝ 1 f)
    (hc : HasCompactSupport f) (i : Fin 4) :
    Continuous (TestFunctions.partialDerivR4 i f) ∧
      HasCompactSupport (TestFunctions.partialDerivR4 i f) := by
  have heq : TestFunctions.partialDerivR4 i f = fun x => fderiv ℝ f x (Pi.single i (1 : ℝ)) :=
    funext (partialDerivR4_eq_fderiv hf i)
  rw [heq]
  exact ⟨(hf.continuous_fderiv one_ne_zero).clm_apply continuous_const,
    hc.fderiv_apply (𝕜 := ℝ) _⟩
theorem bddAbove_gradNorm {f : R4 → ℂ} (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) :
    BddAbove (Set.range fun x => Real.sqrt (∑ i, ‖TestFunctions.partialDerivR4 i f x‖ ^ 2)) := by
  choose C hC using fun i =>
    (partialDerivR4_continuous_hasCompactSupport hf hc i).1.bounded_above_of_compact_support
      (partialDerivR4_continuous_hasCompactSupport hf hc i).2
  refine ⟨Real.sqrt (∑ i, C i ^ 2), ?_⟩
  rintro _ ⟨x, rfl⟩
  exact Real.sqrt_le_sqrt (Finset.sum_le_sum fun i _ =>
    pow_le_pow_left₀ (norm_nonneg _) (hC i x) 2)
theorem gradSup_nonneg (f : R4 → ℂ) : 0 ≤ gradSup f :=
  Real.iSup_nonneg fun _ => Real.sqrt_nonneg _
theorem norm_fderiv_apply_le_gradSup {f : R4 → ℂ} (hf : ContDiff ℝ 1 f)
    (hc : HasCompactSupport f) (x v : R4) :
    ‖fderiv ℝ f x v‖ ≤ gradSup f * euclidNormVec v := by
  have hdecomp : v = ∑ i, v i • (Pi.single i (1 : ℝ) : R4) := by
    funext j
    simp [Finset.sum_apply, Pi.single_apply]
  have hval : fderiv ℝ f x v = ∑ i, v i • TestFunctions.partialDerivR4 i f x := by
    conv_lhs => rw [hdecomp]
    simp only [map_sum, map_smul, partialDerivR4_eq_fderiv hf]
  have hcs : ∑ i, |v i| * ‖TestFunctions.partialDerivR4 i f x‖ ≤
      Real.sqrt (∑ i, |v i| ^ 2) *
        Real.sqrt (∑ i, ‖TestFunctions.partialDerivR4 i f x‖ ^ 2) :=
    Real.sum_mul_le_sqrt_mul_sqrt _ _ _
  have hv : Real.sqrt (∑ i, |v i| ^ 2) = euclidNormVec v := by
    simp only [sq_abs, euclidNormVec]
  rw [hv] at hcs
  have hgrad : Real.sqrt (∑ i, ‖TestFunctions.partialDerivR4 i f x‖ ^ 2) ≤ gradSup f :=
    le_ciSup (bddAbove_gradNorm hf hc) x
  calc ‖fderiv ℝ f x v‖ ≤ ∑ i, ‖v i • TestFunctions.partialDerivR4 i f x‖ := by
        rw [hval]
        exact norm_sum_le _ _
    _ = ∑ i, |v i| * ‖TestFunctions.partialDerivR4 i f x‖ := by
        simp only [norm_smul, Real.norm_eq_abs]
    _ ≤ euclidNormVec v * Real.sqrt (∑ i, ‖TestFunctions.partialDerivR4 i f x‖ ^ 2) := hcs
    _ ≤ euclidNormVec v * gradSup f :=
        mul_le_mul_of_nonneg_left hgrad (Real.sqrt_nonneg _)
    _ = gradSup f * euclidNormVec v := mul_comm _ _
theorem norm_sub_le_gradSup_mul {f : R4 → ℂ} (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f)
    (x y : R4) : ‖f x - f y‖ ≤ gradSup f * euclidNormVec (x - y) := by
  have hmv := norm_image_sub_le_of_norm_deriv_le_segment_01'
    (f := fun s : ℝ => f (y + s • (x - y)))
    (f' := fun s : ℝ => fderiv ℝ f (y + s • (x - y)) (x - y))
    (C := gradSup f * euclidNormVec (x - y))
    (fun t _ => (hasDerivAt_comp_line hf y (x - y) t).hasDerivWithinAt)
    (fun t _ => norm_fderiv_apply_le_gradSup hf hc _ _)
  simpa using hmv
theorem lipConstR4_le_gradSup {f : R4 → ℂ} (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) :
    TestFunctions.lipConstR4 f ≤ gradSup f :=
  csInf_le ⟨0, fun _ hK => hK.1⟩ ⟨gradSup_nonneg f, norm_sub_le_gradSup_mul hf hc⟩
theorem sharpNorm_le_max {f : R4 → ℂ} (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f)
    (s : SharpScale) :
    s.sharpNorm f ≤ max (TestFunctions.uniformNorm f) (40 * s.M * gradSup f) := by
  have hM : 0 ≤ 40 * s.M := by linarith [s.one_le]
  exact max_le_max le_rfl (mul_le_mul_of_nonneg_left (lipConstR4_le_gradSup hf hc) hM)
theorem sharpNorm_comp_le {f : R4 → ℂ} (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f)
    (s : SharpScale) (p : ℂ → ℝ) (hp : ∀ a, ‖p a‖ ≤ ‖a‖)
    (hlip : ∀ a b, ‖p a - p b‖ ≤ ‖a - b‖) : s.sharpNorm (fun x => p (f x)) ≤ s.sharpNorm f := by
  obtain ⟨C, hC⟩ := hf.continuous.bounded_above_of_compact_support hc
  have hbdd : BddAbove (Set.range fun x => ‖f x‖) := ⟨C, by rintro _ ⟨x, rfl⟩; exact hC x⟩
  have hsup : TestFunctions.uniformNorm (fun x => p (f x)) ≤ TestFunctions.uniformNorm f :=
    ciSup_le fun x => (hp _).trans (le_ciSup hbdd x)
  have hL : TestFunctions.lipConstR4 (fun x => p (f x)) ≤ TestFunctions.lipConstR4 f := by
    refine csInf_le_csInf ⟨0, fun _ hK => hK.1⟩
      ⟨gradSup f, gradSup_nonneg f, norm_sub_le_gradSup_mul hf hc⟩ ?_
    exact fun D hD => ⟨hD.1, fun x y => (hlip _ _).trans (hD.2 x y)⟩
  have hM : 0 ≤ 40 * s.M := by linarith [s.one_le]
  exact max_le_max hsup (mul_le_mul_of_nonneg_left hL hM)
theorem sharpNorm_nonneg (s : SharpScale) (f : R4 → ℂ) : 0 ≤ s.sharpNorm f := by apply _root_.YangMills.Construction.EuclideanFunctionals.InsertionForm.zero_le_sharpNorm <;> assumption
theorem gradSup_le_two_mul {f : R4 → ℂ} {δ : ℝ} (hδ : 0 ≤ δ)
    (hpd : ∀ i x, ‖TestFunctions.partialDerivR4 i f x‖ ≤ δ) : gradSup f ≤ 2 * δ := by
  refine ciSup_le fun x => Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
  calc ∑ i, ‖TestFunctions.partialDerivR4 i f x‖ ^ 2 ≤ ∑ _i : Fin 4, δ ^ 2 :=
        Finset.sum_le_sum fun i _ => pow_le_pow_left₀ (norm_nonneg _) (hpd i x) 2
    _ = (2 * δ) ^ 2 := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        ring
theorem tendsto_sharpNorm_zero {ι : Type*} {l : Filter ι} (s : SharpScale) (g : ι → R4 → ℂ)
    (hg : ∀ᶠ k in l, ContDiff ℝ 1 (g k) ∧ HasCompactSupport (g k))
    (h₀ : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in l, ∀ x, ‖g k x‖ ≤ ε)
    (h₁ : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in l, ∀ i x, ‖TestFunctions.partialDerivR4 i (g k) x‖ ≤ ε) :
    Tendsto (fun k => s.sharpNorm (g k)) l (𝓝 0) := by
  refine tendsto_order.2 ⟨fun a ha => Eventually.of_forall fun k =>
    ha.trans_le (sharpNorm_nonneg s _), fun a ha => ?_⟩
  have hM := s.one_le
  set δ := a / (2 * (80 * s.M + 1)) with hδdef
  have hδ : 0 < δ := by positivity
  have hδa : δ * (80 * s.M + 1) = a / 2 := by
    rw [hδdef]
    field_simp
  filter_upwards [hg, h₀ δ hδ, h₁ δ hδ] with k hk hk₀ hk₁
  have hs₀ : TestFunctions.uniformNorm (g k) ≤ δ := ciSup_le hk₀
  have hs₁ : 40 * s.M * gradSup (g k) ≤ 40 * s.M * (2 * δ) :=
    mul_le_mul_of_nonneg_left (gradSup_le_two_mul hδ.le hk₁) (by linarith)
  refine (sharpNorm_le_max hk.1 hk.2 s).trans_lt (max_lt ?_ ?_)
  · nlinarith
  · nlinarith
theorem boundedAndLipschitz_holds : BoundedAndLipschitz := by
  intro h hh
  obtain ⟨hC, hc⟩ := contDiff_hasCompactSupport_of_mem hh
  exact ⟨hC.continuous.bounded_above_of_compact_support hc,
    fun i => (partialDerivR4_continuous_hasCompactSupport hC hc i).1.bounded_above_of_compact_support
      (partialDerivR4_continuous_hasCompactSupport hC hc i).2,
    norm_sub_le_gradSup_mul hC hc⟩
theorem sharpLeGrad_holds (s : SharpScale) : SharpLeGrad s := by
  intro h hh
  obtain ⟨hC, hc⟩ := contDiff_hasCompactSupport_of_mem hh
  exact ⟨lipConstR4_le_gradSup hC hc, sharpNorm_le_max hC hc s⟩
theorem reImParts_holds (hP : TupleRules.ReImAndMotionOfFns) (s : SharpScale) :
    ReImParts s := by
  intro h hh
  obtain ⟨hC, hc⟩ := contDiff_hasCompactSupport_of_mem hh
  obtain ⟨hre, him, hsupp, -⟩ := hP s 1 1 h hh
  refine ⟨hre, him, hsupp, ?_, ?_⟩
  · refine sharpNorm_comp_le hC hc s Complex.re (fun a => Complex.abs_re_le_norm a) fun a b => ?_
    rw [← Complex.sub_re]
    exact Complex.abs_re_le_norm _
  · refine sharpNorm_comp_le hC hc s Complex.im (fun a => Complex.abs_im_le_norm a) fun a b => ?_
    rw [← Complex.sub_im]
    exact Complex.abs_im_le_norm _
theorem sharpTendstoOfC1_holds (s : SharpScale) : SharpTendstoOfC1 s := by
  intro hs h hmem hh hconv
  obtain ⟨hC, hc⟩ := contDiff_hasCompactSupport_of_mem hh
  have hmem' : ∀ j, 1 ≤ j → ContDiff ℝ 1 (hs j) ∧ HasCompactSupport (hs j) := fun j hj =>
    contDiff_hasCompactSupport_of_mem (hmem j hj)
  refine tendsto_sharpNorm_zero s _ ?_ (fun ε hε => ?_) (fun ε hε => ?_)
  · filter_upwards [eventually_ge_atTop 1] with j hj
    refine ⟨(hmem' j hj).1.sub hC, ?_⟩
    rw [sub_eq_add_neg]
    exact (hmem' j hj).2.add hc.neg
  · filter_upwards [Metric.tendstoUniformly_iff.1 hconv.1 ε hε] with j hj x
    have hx := (hj x).le
    rwa [dist_comm, dist_eq_norm] at hx
  · filter_upwards [eventually_ge_atTop 1,
      eventually_all.2 fun i => Metric.tendstoUniformly_iff.1 (hconv.2 i) ε hε] with j hj hd i x
    rw [partialDerivR4_sub (hmem' j hj).1 hC]
    have hx := (hd i x).le
    rwa [dist_comm, dist_eq_norm] at hx
theorem eventually_norm_shift_sub_le {u : R4 → ℂ} (hu : UniformContinuous u) (z' : R4) {ε : ℝ}
    (hε : 0 < ε) : ∀ᶠ z in 𝓝 z', ∀ x, ‖u (x - z) - u (x - z')‖ ≤ ε := by
  obtain ⟨δ, hδ, hunif⟩ := Metric.uniformContinuous_iff.1 hu ε hε
  filter_upwards [Metric.ball_mem_nhds z' hδ] with z hz x
  have hd : dist (x - z) (x - z') < δ := by rwa [dist_sub_left]
  have hclose := hunif hd
  rw [dist_eq_norm] at hclose
  exact hclose.le
theorem translContinuous_holds (hP : TupleRules.ReImAndMotionOfFns) (s : SharpScale) :
    TranslContinuous s := by
  intro h hh z'
  obtain ⟨hC, hc⟩ := contDiff_hasCompactSupport_of_mem hh
  have hT : ∀ v, ContDiff ℝ 1 ((EuclidMotion.transl v).actFn h) ∧
      HasCompactSupport ((EuclidMotion.transl v).actFn h) := fun v =>
    contDiff_hasCompactSupport_of_mem (hP s (EuclidMotion.transl v) 1 h hh).2.2.2.1
  refine tendsto_sharpNorm_zero s _ (Eventually.of_forall fun z => ?_) (fun ε hε => ?_)
    (fun ε hε => ?_)
  · refine ⟨(hT z).1.sub (hT z').1, ?_⟩
    rw [sub_eq_add_neg]
    exact (hT z).2.add (hT z').2.neg
  · filter_upwards [eventually_norm_shift_sub_le
      (hc.uniformContinuous_of_continuous hC.continuous) z' hε] with z hz x
    simpa only [Pi.sub_apply, EuclidMotion.actFn_transl] using hz x
  · have hU : ∀ i, UniformContinuous (TestFunctions.partialDerivR4 i h) := fun i =>
      (partialDerivR4_continuous_hasCompactSupport hC hc i).2.uniformContinuous_of_continuous
        (partialDerivR4_continuous_hasCompactSupport hC hc i).1
    filter_upwards [eventually_all.2 fun i => eventually_norm_shift_sub_le (hU i) z' hε]
      with z hz i x
    rw [partialDerivR4_sub (hT z).1 (hT z').1, ← partialDerivR4_eq_fderiv (hT z).1,
      ← partialDerivR4_eq_fderiv (hT z').1, partialDerivR4_transl, partialDerivR4_transl]
    exact hz i x
theorem main_holds (hT : TupleRules.TupleSpanActionRules) : Main :=
  ⟨boundedAndLipschitz_holds, fun s => ⟨sharpLeGrad_holds s, reImParts_holds hT.1 s,
    sharpTendstoOfC1_holds s, translContinuous_holds hT.1 s⟩⟩
end YangMills.Construction.EuclideanFunctionals.SharpNormC1
