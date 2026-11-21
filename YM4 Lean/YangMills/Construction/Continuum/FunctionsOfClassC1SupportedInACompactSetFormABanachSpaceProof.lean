import YangMills.Construction.PassageToTheLimit.MovingAMirrorIsTranslatingTheImageProof
import YangMills.Construction.Continuum.FunctionsOfClassC1SupportedInACompactSetFormABanachSpace
import YangMills.Construction.PassageToTheLimit.SpacesOfFunctionsOfClassC1AreBanachSpacesProof
import YangMills.Construction.ReflectionPositivity.FunctionsOfClassC1OnOneTorusProof
import Mathlib
set_option autoImplicit false
open Filter Set Topology TopologicalSpace
noncomputable section
namespace YangMills.Construction.C1Banach
open TestFunctions TorusMetric
section Calculus
theorem partialDerivR4_eq_fderiv_apply {f : (Fin 4 → ℝ) → ℝ} {L : (Fin 4 → ℝ) →L[ℝ] ℝ}
    {y : Fin 4 → ℝ} (hL : HasFDerivAt f L y) (i : Fin 4) :
    partialDerivR4 i f y = L (Pi.single i 1) := by
  have hline : HasDerivAt (fun t : ℝ => y + t • (Pi.single i (1 : ℝ) : Fin 4 → ℝ))
      (Pi.single i 1) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (Pi.single i (1 : ℝ) : Fin 4 → ℝ)).const_add y
  have hf : HasFDerivAt f L (y + (0 : ℝ) • (Pi.single i (1 : ℝ) : Fin 4 → ℝ)) := by
    simpa using hL
  exact (hf.comp_hasDerivAt (0 : ℝ) hline).deriv
theorem norm_single_one_le (i : Fin 4) : ‖(Pi.single i (1 : ℝ) : Fin 4 → ℝ)‖ ≤ 1 := by apply _root_.YangMills.Construction.LimitSpaces.Ambient.C1Banach.norm_single_one_le <;> assumption
theorem clm_apply_eq_sum_single (L : (Fin 4 → ℝ) →L[ℝ] ℝ) (v : Fin 4 → ℝ) :
    L v = ∑ i, v i * L (Pi.single i 1) := by apply _root_.YangMills.Construction.ReflectionPositivity.TorusC1Facts.clm_apply_eq_sum_basis <;> assumption
theorem opNorm_le_sum_abs_single (L : (Fin 4 → ℝ) →L[ℝ] ℝ) :
    ‖L‖ ≤ ∑ i, |L (Pi.single i 1)| := by apply _root_.YangMills.Construction.LimitSpaces.Ambient.C1Banach.opNorm_le_sum_abs_single <;> assumption
theorem abs_sum_mul_le_two_mul_euclid (v p : Fin 4 → ℝ) {B : ℝ} (hp : ∀ i, |p i| ≤ B)
    (hB : 0 ≤ B) :
    |∑ i, v i * p i| ≤ 2 * B * euclidNormVec v := by
  have hnn : 0 ≤ ∑ i, v i ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hpsq : ∑ i, p i ^ 2 ≤ 4 * B ^ 2 := by
    calc ∑ i, p i ^ 2 ≤ ∑ _i : Fin 4, B ^ 2 :=
          Finset.sum_le_sum fun i _ => by
            rw [← sq_abs (p i)]
            exact (sq_le_sq₀ (abs_nonneg _) hB).mpr (hp i)
      _ = 4 * B ^ 2 := by simp
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ v p
  refine abs_le_of_sq_le_sq ?_ (by
    unfold euclidNormVec
    positivity)
  calc (∑ i, v i * p i) ^ 2 ≤ (∑ i, v i ^ 2) * ∑ i, p i ^ 2 := hcs
    _ ≤ (∑ i, v i ^ 2) * (4 * B ^ 2) := mul_le_mul_of_nonneg_left hpsq hnn
    _ = (2 * B * euclidNormVec v) ^ 2 := by
        unfold euclidNormVec
        rw [mul_pow, Real.sq_sqrt hnn]
        ring
theorem euclidNormVec_smul_single (t : ℝ) (i : Fin 4) :
    euclidNormVec (t • (Pi.single i (1 : ℝ) : Fin 4 → ℝ)) = |t| := by apply _root_.YangMills.Construction.LimitSpaces.MirrorTranslation.euclidNormVec_smul_stdBasisVec <;> assumption
theorem exists_uniform_limit_of_uniformCauchy {α β : Type*} [NormedAddCommGroup β]
    [CompleteSpace β] (g : ℕ → α → β)
    (hg : ∀ δ > 0, ∃ M : ℕ, ∀ m ≥ M, ∀ n ≥ M, ∀ z, ‖g m z - g n z‖ ≤ δ) :
    ∃ l : α → β, ∀ δ > 0, ∃ M : ℕ, ∀ m ≥ M, ∀ z, ‖g m z - l z‖ ≤ δ := by
  have key : ∀ x, ∃ y, Tendsto (g · x) atTop (𝓝 y) := fun x =>
    cauchySeq_tendsto_of_complete <| Metric.cauchySeq_iff'.2 fun δ hδ => by
      obtain ⟨M, hM⟩ := hg (δ / 2) (half_pos hδ)
      exact ⟨M, fun n hn =>
        (dist_eq_norm _ _).trans_lt ((hM n hn M le_rfl x).trans_lt (half_lt_self hδ))⟩
  choose lim hlim using key
  refine ⟨lim, fun δ hδ => ?_⟩
  obtain ⟨M, hM⟩ := hg δ hδ
  exact ⟨M, fun n hn x => le_of_tendsto ((hlim x).const_sub (g n x)).norm
    (eventually_atTop.2 ⟨M, fun m hm => hM n hn m hm x⟩)⟩
theorem tendstoUniformly_of_eventually_norm_le {α β : Type*} [NormedAddCommGroup β]
    (g : ℕ → α → β) (l : α → β)
    (hgl : ∀ ε : ℝ, 0 < ε → ∃ N, ∀ a ≥ N, ∀ x, ‖g a x - l x‖ ≤ ε) :
    TendstoUniformly g l atTop := by apply _root_.YangMills.Construction.LimitSpaces.Ambient.C1Banach.tendstoUniformly_of_norm_bound <;> assumption
theorem abs_le_uniformNorm {g : (Fin 4 → ℝ) → ℝ} (hg : IsBoundedFun g) (x : Fin 4 → ℝ) :
    |g x| ≤ uniformNorm g := by
  obtain ⟨C, hC⟩ := hg
  exact le_ciSup (f := fun x => ‖g x‖) ⟨C, by
    rintro _ ⟨x, rfl⟩
    exact hC x⟩ x
theorem uniformNorm_le {g : (Fin 4 → ℝ) → ℝ} {ε : ℝ} (hg : ∀ x, |g x| ≤ ε) :
    uniformNorm g ≤ ε :=
  ciSup_le hg
end Calculus
section Members
variable {W : Compacts (Fin 4 → ℝ)}
theorem contDiff_of_mem (h : c1Supported W) : ContDiff ℝ 1 (h : (Fin 4 → ℝ) → ℝ) :=
  (mem_c1Supported.mp h.2).1
theorem hasCompactSupport_of_mem (h : c1Supported W) :
    HasCompactSupport (h : (Fin 4 → ℝ) → ℝ) :=
  W.isCompact.of_isClosed_subset (isClosed_tsupport _) (mem_c1Supported.mp h.2).2
theorem differentiable_of_mem (h : c1Supported W) :
    Differentiable ℝ (h : (Fin 4 → ℝ) → ℝ) :=
  (contDiff_of_mem h).differentiable (by norm_num)
theorem hasFDerivAt_of_mem (h : c1Supported W) (y : Fin 4 → ℝ) :
    HasFDerivAt (h : (Fin 4 → ℝ) → ℝ) (fderiv ℝ (h : (Fin 4 → ℝ) → ℝ) y) y :=
  (differentiable_of_mem h y).hasFDerivAt
theorem isBoundedFun_of_mem (h : c1Supported W) : IsBoundedFun (h : (Fin 4 → ℝ) → ℝ) :=
  (contDiff_of_mem h).continuous.bounded_above_of_compact_support (hasCompactSupport_of_mem h)
theorem isBoundedFun_partialDeriv (h : c1Supported W) (i : Fin 4) :
    IsBoundedFun (partialDerivR4 i (h : (Fin 4 → ℝ) → ℝ)) := by
  obtain ⟨C, hC⟩ := ((contDiff_of_mem h).continuous_fderiv
    (by norm_num)).bounded_above_of_compact_support ((hasCompactSupport_of_mem h).fderiv (𝕜 := ℝ))
  refine ⟨C, fun x => ?_⟩
  rw [partialDerivR4_eq_fderiv_apply (hasFDerivAt_of_mem h x)]
  calc _ ≤ ‖fderiv ℝ (h : (Fin 4 → ℝ) → ℝ) x‖ * ‖(Pi.single i (1 : ℝ) : Fin 4 → ℝ)‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ ≤ ‖fderiv ℝ (h : (Fin 4 → ℝ) → ℝ) x‖ * 1 :=
        mul_le_mul_of_nonneg_left (norm_single_one_le i) (norm_nonneg _)
    _ ≤ C := by simpa using hC x
theorem abs_apply_le_norm (h : c1Supported W) (x : Fin 4 → ℝ) :
    |(h : (Fin 4 → ℝ) → ℝ) x| ≤ ‖h‖ :=
  (abs_le_uniformNorm (isBoundedFun_of_mem h) x).trans (le_max_left _ _)
theorem abs_partialDeriv_le_norm (h : c1Supported W) (i : Fin 4) (x : Fin 4 → ℝ) :
    |partialDerivR4 i (h : (Fin 4 → ℝ) → ℝ) x| ≤ ‖h‖ :=
  (abs_le_uniformNorm (isBoundedFun_partialDeriv h i) x).trans
    ((le_ciSup (f := fun j : Fin 4 => uniformNorm (partialDerivR4 j (h : (Fin 4 → ℝ) → ℝ)))
      (Set.finite_range _).bddAbove i).trans (le_max_right _ _))
theorem norm_le_of_pointwise (h : c1Supported W) {ε : ℝ}
    (h0 : ∀ x, |(h : (Fin 4 → ℝ) → ℝ) x| ≤ ε)
    (h1 : ∀ i x, |partialDerivR4 i (h : (Fin 4 → ℝ) → ℝ) x| ≤ ε) : ‖h‖ ≤ ε :=
  max_le (uniformNorm_le h0) (ciSup_le fun i => uniformNorm_le (h1 i))
theorem c1_norm_nonneg (h : c1Supported W) : 0 ≤ ‖h‖ :=
  (abs_nonneg _).trans (abs_apply_le_norm h 0)
theorem c1_norm_smul_le (c : ℝ) (h : c1Supported W) : ‖c • h‖ ≤ |c| * ‖h‖ := by
  refine norm_le_of_pointwise _ (fun x => ?_) (fun i x => ?_)
  · show |c * (h : (Fin 4 → ℝ) → ℝ) x| ≤ _
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (abs_apply_le_norm h x) (abs_nonneg c)
  · have hd : HasFDerivAt ((c • h : c1Supported W) : (Fin 4 → ℝ) → ℝ)
        (c • fderiv ℝ (h : (Fin 4 → ℝ) → ℝ) x) x := (hasFDerivAt_of_mem h x).const_smul c
    rw [partialDerivR4_eq_fderiv_apply hd, smul_apply,
      ← partialDerivR4_eq_fderiv_apply (hasFDerivAt_of_mem h x), smul_eq_mul, abs_mul]
    exact mul_le_mul_of_nonneg_left (abs_partialDeriv_le_norm h i x) (abs_nonneg c)
theorem c1_norm_smul (c : ℝ) (h : c1Supported W) : ‖c • h‖ = ‖c‖ * ‖h‖ := by
  rw [Real.norm_eq_abs]
  refine le_antisymm (c1_norm_smul_le c h) ?_
  by_cases hc : c = 0
  · subst hc
    simpa using c1_norm_nonneg ((0 : ℝ) • h)
  · have h1 := c1_norm_smul_le c⁻¹ (c • h)
    rw [smul_smul, inv_mul_cancel₀ hc, one_smul, abs_inv] at h1
    have hpos : 0 < |c| := abs_pos.mpr hc
    calc |c| * ‖h‖ ≤ |c| * (|c|⁻¹ * ‖c • h‖) := mul_le_mul_of_nonneg_left h1 hpos.le
      _ = ‖c • h‖ := by field_simp
theorem c1_norm_add_le (f g : c1Supported W) : ‖f + g‖ ≤ ‖f‖ + ‖g‖ := by
  refine norm_le_of_pointwise _ (fun x => ?_) (fun i x => ?_)
  · show |(f : (Fin 4 → ℝ) → ℝ) x + (g : (Fin 4 → ℝ) → ℝ) x| ≤ _
    exact (abs_add_le _ _).trans (add_le_add (abs_apply_le_norm f x) (abs_apply_le_norm g x))
  · have hd : HasFDerivAt ((f + g : c1Supported W) : (Fin 4 → ℝ) → ℝ)
        (fderiv ℝ (f : (Fin 4 → ℝ) → ℝ) x + fderiv ℝ (g : (Fin 4 → ℝ) → ℝ) x) x :=
      (hasFDerivAt_of_mem f x).add (hasFDerivAt_of_mem g x)
    rw [partialDerivR4_eq_fderiv_apply hd, add_apply,
      ← partialDerivR4_eq_fderiv_apply (hasFDerivAt_of_mem f x),
      ← partialDerivR4_eq_fderiv_apply (hasFDerivAt_of_mem g x)]
    exact (abs_add_le _ _).trans
      (add_le_add (abs_partialDeriv_le_norm f i x) (abs_partialDeriv_le_norm g i x))
theorem c1_norm_eq_zero_iff (h : c1Supported W) : ‖h‖ = 0 ↔ h = 0 := by
  constructor
  · intro h0
    refine Subtype.ext (funext fun x => ?_)
    have := abs_apply_le_norm h x
    rw [h0] at this
    exact abs_nonpos_iff.mp this
  · rintro rfl
    have h1 := c1_norm_smul (0 : ℝ) (0 : c1Supported W)
    simpa using h1
end Members
section Completeness
theorem cauchyConverges_holds (W : Compacts (Fin 4 → ℝ)) : CauchyConverges W := by
  intro u hC
  let F : ℕ → (Fin 4 → ℝ) → ℝ := fun k => (u k : (Fin 4 → ℝ) → ℝ)
  have hFd : ∀ k y, HasFDerivAt (F k) (fderiv ℝ (F k) y) y := fun k y => hasFDerivAt_of_mem (u k) y
  have hD : ∀ a b y, ‖fderiv ℝ (F a) y - fderiv ℝ (F b) y‖ ≤ 4 * ‖u a - u b‖ := by
    intro a b y
    refine (opNorm_le_sum_abs_single _).trans ?_
    have hi : ∀ i : Fin 4, |(fderiv ℝ (F a) y - fderiv ℝ (F b) y) (Pi.single i 1)| ≤
        ‖u a - u b‖ := by
      intro i
      have hder : HasFDerivAt ((u a - u b : c1Supported W) : (Fin 4 → ℝ) → ℝ)
          (fderiv ℝ (F a) y - fderiv ℝ (F b) y) y := (hFd a y).sub (hFd b y)
      rw [← partialDerivR4_eq_fderiv_apply hder]
      exact abs_partialDeriv_le_norm _ i y
    calc _ ≤ ∑ _i : Fin 4, ‖u a - u b‖ := Finset.sum_le_sum fun i _ => hi i
      _ = _ := by simp
  obtain ⟨f, hf⟩ := exists_uniform_limit_of_uniformCauchy F (fun ε hε => by
    obtain ⟨N, hN⟩ := hC ε hε
    exact ⟨N, fun a ha b hb x => (abs_apply_le_norm (u a - u b) x).trans (hN a ha b hb).le⟩)
  obtain ⟨L, hL⟩ := exists_uniform_limit_of_uniformCauchy (fun k y => fderiv ℝ (F k) y) <| by
    intro δ hδ
    obtain ⟨M, hM⟩ := hC (δ / 4) (div_pos hδ four_pos)
    exact ⟨M, fun m hm n hn z => (hD m n z).trans (by linarith [(hM m hm n hn).le])⟩
  have tf := tendstoUniformly_of_eventually_norm_le F f hf
  have tL := tendstoUniformly_of_eventually_norm_le _ L hL
  have hpt : ∀ x, Tendsto (fun k => F k x) atTop (𝓝 (f x)) := tf.tendsto_at
  have hφ : ∀ y, HasFDerivAt f (L y) y := hasFDerivAt_of_tendstoUniformly tL hFd hpt
  have hLc : Continuous L := tL.continuous <| Frequently.of_forall fun k =>
    (contDiff_of_mem (u k)).continuous_fderiv (by norm_num)
  have hC1 : IsC1R4 f := by
    have hfd : fderiv ℝ f = L := funext fun y => (hφ y).fderiv
    exact contDiff_one_iff_fderiv.mpr ⟨fun y => (hφ y).differentiableAt, hfd ▸ hLc⟩
  have hsupp : tsupport f ⊆ W := by
    refine closure_minimal (fun x hx => ?_) W.isCompact.isClosed
    by_contra hxW
    have h0 : ∀ k, F k x = 0 := fun k =>
      image_eq_zero_of_notMem_tsupport fun hk => hxW ((mem_c1Supported.mp (u k).2).2 hk)
    have hlim : Tendsto (fun k => F k x) atTop (𝓝 0) := by
      simp [h0]
    exact hx (tendsto_nhds_unique (hpt x) hlim)
  have hfV : f ∈ c1Supported W := mem_c1Supported.mpr ⟨hC1, hsupp⟩
  refine ⟨⟨f, hfV⟩, fun ε hε => ?_⟩
  have hε2 : 0 < ε / 2 := half_pos hε
  obtain ⟨P, hP⟩ := hf _ hε2
  obtain ⟨Q, hQ⟩ := hL _ hε2
  refine ⟨P + Q, fun a ha => ?_⟩
  have hPa : P ≤ a := le_trans (Nat.le_add_right P Q) ha
  have hQa : Q ≤ a := le_trans (Nat.le_add_left Q P) ha
  have hle : ‖u a - ⟨f, hfV⟩‖ ≤ ε / 2 := by
    refine norm_le_of_pointwise _ (hP a hPa) (fun i x => ?_)
    have hdiff : HasFDerivAt ((u a - ⟨f, hfV⟩ : c1Supported W) : (Fin 4 → ℝ) → ℝ)
        (fderiv ℝ (F a) x - L x) x := (hFd a x).sub (hφ x)
    rw [partialDerivR4_eq_fderiv_apply hdiff]
    calc _ ≤ ‖fderiv ℝ (F a) x - L x‖ * ‖(Pi.single i (1 : ℝ) : Fin 4 → ℝ)‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ ε / 2 * 1 := mul_le_mul (hQ a hQa x) (norm_single_one_le i)
          (norm_nonneg _) (by positivity)
      _ = ε / 2 := mul_one _
  linarith
end Completeness
section TwoNorms
variable {W : Compacts (Fin 4 → ℝ)}
theorem norm_sub_le_two_mul_dist (h : c1Supported W) (x y : Fin 4 → ℝ) :
    ‖(h : (Fin 4 → ℝ) → ℝ) x - (h : (Fin 4 → ℝ) → ℝ) y‖ ≤ 2 * ‖h‖ * euclidDistR4 x y := by
  have hmove : ∀ s : ℝ, HasDerivAt (fun r : ℝ => y + r • (x - y)) (x - y) s := fun s => by
    have hs := (hasDerivAt_id' (x := s)).smul_const (x - y) |>.const_add y
    rwa [one_smul] at hs
  have hchain : ∀ s : ℝ, HasDerivAt (fun r : ℝ => (h : (Fin 4 → ℝ) → ℝ) (y + r • (x - y)))
      (fderiv ℝ (h : (Fin 4 → ℝ) → ℝ) (y + s • (x - y)) (x - y)) s := fun s =>
    (hasFDerivAt_of_mem h _).comp_hasDerivAt s (hmove s)
  have hbound : ∀ s ∈ (univ : Set ℝ),
      ‖deriv (fun r : ℝ => (h : (Fin 4 → ℝ) → ℝ) (y + r • (x - y))) s‖ ≤
        2 * ‖h‖ * euclidDistR4 x y := by
    intro s _
    rw [(hchain s).deriv, clm_apply_eq_sum_single, Real.norm_eq_abs]
    refine abs_sum_mul_le_two_mul_euclid (x - y) _ (fun i => ?_) (c1_norm_nonneg h)
    rw [← partialDerivR4_eq_fderiv_apply (hasFDerivAt_of_mem h _)]
    exact abs_partialDeriv_le_norm h i _
  have hmv := convex_univ.norm_image_sub_le_of_norm_deriv_le
    (fun s _ => (hchain s).differentiableAt) hbound (mem_univ (0 : ℝ)) (mem_univ (1 : ℝ))
  simpa using hmv
theorem isLipschitzFor_of_mem (h : c1Supported W) :
    IsLipschitzFor euclidDistR4 (h : (Fin 4 → ℝ) → ℝ) :=
  ⟨2 * ‖h‖, by have := c1_norm_nonneg h; positivity, norm_sub_le_two_mul_dist h⟩
theorem lipConstR4_le (h : c1Supported W) : lipConstR4 (h : (Fin 4 → ℝ) → ℝ) ≤ 2 * ‖h‖ :=
  csInf_le ⟨0, fun _ hC => hC.1⟩
    ⟨by have := c1_norm_nonneg h; positivity, norm_sub_le_two_mul_dist h⟩
theorem lipConstR4_nonneg (h : c1Supported W) : 0 ≤ lipConstR4 (h : (Fin 4 → ℝ) → ℝ) :=
  le_csInf ⟨_, by have := c1_norm_nonneg h; positivity, norm_sub_le_two_mul_dist h⟩
    fun _ hC => hC.1
theorem abs_partialDeriv_le_lipConstR4 (h : c1Supported W) (i : Fin 4) (x : Fin 4 → ℝ) :
    |partialDerivR4 i (h : (Fin 4 → ℝ) → ℝ) x| ≤ lipConstR4 (h : (Fin 4 → ℝ) → ℝ) := by
  refine le_csInf ⟨_, by have := c1_norm_nonneg h; positivity, norm_sub_le_two_mul_dist h⟩ ?_
  rintro C ⟨hC0, hC⟩
  refine norm_deriv_le_of_lip' (𝕜 := ℝ) (F := ℝ) (x₀ := 0)
    (f := fun t : ℝ => (h : (Fin 4 → ℝ) → ℝ) (x + t • (Pi.single i (1 : ℝ) : Fin 4 → ℝ))) hC0
    (Eventually.of_forall fun t => ?_)
  have h1 := hC (x + t • (Pi.single i (1 : ℝ) : Fin 4 → ℝ))
    (x + (0 : ℝ) • (Pi.single i (1 : ℝ) : Fin 4 → ℝ))
  have hd : euclidDistR4 (x + t • (Pi.single i (1 : ℝ) : Fin 4 → ℝ))
      (x + (0 : ℝ) • (Pi.single i (1 : ℝ) : Fin 4 → ℝ)) = ‖t - 0‖ := by
    unfold euclidDistR4
    simp only [zero_smul, add_zero, add_sub_cancel_left, sub_zero, Real.norm_eq_abs]
    exact euclidNormVec_smul_single t i
  rw [hd] at h1
  exact h1
theorem norm_le_sharpNormR4 (M : ℝ) (hM : 1 ≤ M) (h : c1Supported W) :
    ‖h‖ ≤ sharpNormR4 M (h : (Fin 4 → ℝ) → ℝ) := by
  refine norm_le_of_pointwise h
    (fun x => (abs_le_uniformNorm (isBoundedFun_of_mem h) x).trans (le_max_left _ _))
    (fun i x => ((abs_partialDeriv_le_lipConstR4 h i x).trans ?_).trans (le_max_right _ _))
  have hL := lipConstR4_nonneg h
  nlinarith
theorem sharpNormR4_le (M : ℝ) (hM : 1 ≤ M) (h : c1Supported W) :
    sharpNormR4 M (h : (Fin 4 → ℝ) → ℝ) ≤ 80 * M * ‖h‖ := by
  have hn := c1_norm_nonneg h
  have hL := lipConstR4_le h
  refine max_le ?_ ?_
  · refine (uniformNorm_le (abs_apply_le_norm h)).trans ?_
    nlinarith
  · have hM0 : 0 ≤ 40 * M := by linarith
    calc 40 * M * lipConstR4 (h : (Fin 4 → ℝ) → ℝ) ≤ 40 * M * (2 * ‖h‖) :=
          mul_le_mul_of_nonneg_left hL hM0
      _ = 80 * M * ‖h‖ := by ring
end TwoNorms
theorem banachAndComparable_holds : BanachAndComparable := fun W =>
  ⟨⟨fun h => ⟨isBoundedFun_of_mem h, isBoundedFun_partialDeriv h⟩,
    { norm_nonneg := c1_norm_nonneg
      norm_smul := c1_norm_smul
      norm_triangle := c1_norm_add_le
      norm_eq_zero_iff := c1_norm_eq_zero_iff },
    cauchyConverges_holds W⟩,
   fun M hM h => ⟨isLipschitzFor_of_mem h, norm_le_sharpNormR4 M hM h, sharpNormR4_le M hM h⟩⟩
end YangMills.Construction.C1Banach
