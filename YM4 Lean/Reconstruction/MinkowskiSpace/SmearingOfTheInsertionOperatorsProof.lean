import YangMills.Construction.TwoPoints.LocalKernelOfAFormProof
import Reconstruction.MinkowskiSpace.InsertionOperatorsOfOneField
import Reconstruction.MinkowskiSpace.SmearingOfTheInsertionOperators
import Mathlib
set_option autoImplicit false
open scoped InnerProductSpace ContDiff
open MeasureTheory Function
noncomputable section
namespace YangMills.Construction.InsertionSmearing
theorem hasDerivAt_along_coord {f : (Fin 4 → ℝ) → ℂ} (hf : ContDiff ℝ 1 f) (i : Fin 4)
    (y : Fin 4 → ℝ) :
    HasDerivAt (fun t : ℝ => f (y + t • (Pi.single i 1 : Fin 4 → ℝ)))
      (TestFunctions.partialDerivR4 i f y) 0 := by
  have hcd : ContDiff ℝ 1 (fun t : ℝ => f (y + t • (Pi.single i 1 : Fin 4 → ℝ))) :=
    hf.comp (contDiff_const.add (contDiff_id.smul contDiff_const))
  exact ((hcd.differentiable (by norm_num)) 0).hasDerivAt
theorem partialDerivR4_eq_fderiv {f : (Fin 4 → ℝ) → ℂ} (hf : ContDiff ℝ 1 f) (i : Fin 4)
    (y : Fin 4 → ℝ) :
    TestFunctions.partialDerivR4 i f y = fderiv ℝ f y (Pi.single i 1 : Fin 4 → ℝ) := by
  have hfd : HasFDerivAt f (fderiv ℝ f y) (y + (0 : ℝ) • (Pi.single i 1 : Fin 4 → ℝ)) := by
    simpa using ((hf.differentiable (by norm_num)) y).hasFDerivAt
  have hline : HasDerivAt (fun t : ℝ => y + t • (Pi.single i 1 : Fin 4 → ℝ))
      (Pi.single i 1 : Fin 4 → ℝ) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (Pi.single i 1 : Fin 4 → ℝ)).const_add y
  exact (hfd.comp_hasDerivAt (0 : ℝ) hline).deriv
theorem partialDerivR4_comp_sub (g : (Fin 4 → ℝ) → ℂ) (a y : Fin 4 → ℝ) (i : Fin 4) :
    TestFunctions.partialDerivR4 i (fun u => g (u - a)) y =
      TestFunctions.partialDerivR4 i g (y - a) := by apply _root_.YangMills.Construction.TwoPoints.LocalFormKernel.partialDerivR4_comp_sub_right <;> assumption
theorem partialDerivR4_sub {f g : (Fin 4 → ℝ) → ℂ} (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g)
    (i : Fin 4) (y : Fin 4 → ℝ) :
    TestFunctions.partialDerivR4 i (f - g) y =
      TestFunctions.partialDerivR4 i f y - TestFunctions.partialDerivR4 i g y :=
  ((hasDerivAt_along_coord hf i y).sub (hasDerivAt_along_coord hg i y)).deriv
theorem partialDerivR4_finset_sum {ι : Type} (s : Finset ι) (c : ι → ℂ)
    (f : ι → (Fin 4 → ℝ) → ℂ) (hf : ∀ j ∈ s, ContDiff ℝ 1 (f j)) (i : Fin 4)
    (y : Fin 4 → ℝ) :
    TestFunctions.partialDerivR4 i (∑ j ∈ s, c j • f j) y =
      ∑ j ∈ s, c j * TestFunctions.partialDerivR4 i (f j) y := by
  have hsum := HasDerivAt.fun_sum (u := s)
    (A := fun j (t : ℝ) => c j * f j (y + t • (Pi.single i 1 : Fin 4 → ℝ)))
    (A' := fun j => c j * TestFunctions.partialDerivR4 i (f j) y) (x := (0 : ℝ))
    (fun j hj => (hasDerivAt_along_coord (hf j hj) i y).const_mul (c j))
  have hfun : (fun t : ℝ => (∑ j ∈ s, c j • f j) (y + t • (Pi.single i 1 : Fin 4 → ℝ))) =
      fun t : ℝ => ∑ j ∈ s, c j * f j (y + t • (Pi.single i 1 : Fin 4 → ℝ)) := by
    funext t
    simp [Finset.sum_apply]
  simp only [TestFunctions.partialDerivR4] at hsum ⊢
  rw [hfun]
  exact hsum.deriv
theorem supC1Norm_le {f : (Fin 4 → ℝ) → ℂ} {M M' : ℝ} (hM : ∀ x, ‖f x‖ ≤ M)
    (hM' : ∀ x i, ‖TestFunctions.partialDerivR4 i f x‖ ≤ M') (hM'0 : 0 ≤ M') :
    WightmanReconstruction.supC1Norm f ≤ M + 2 * M' := by
  unfold WightmanReconstruction.supC1Norm TestFunctions.uniformNorm
  refine add_le_add (ciSup_le hM) (ciSup_le fun x => ?_)
  refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
  calc ∑ i, ‖TestFunctions.partialDerivR4 i f x‖ ^ 2 ≤ ∑ _i : Fin 4, M' ^ 2 :=
        Finset.sum_le_sum fun i _ => pow_le_pow_left₀ (norm_nonneg _) (hM' x i) 2
    _ = (2 * M') ^ 2 := by simp; ring
theorem exists_uniform_modulus_of_contDiff {g : (Fin 4 → ℝ) → ℂ} (hg : ContDiff ℝ 1 g)
    (hgc : HasCompactSupport g) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ u v : Fin 4 → ℝ, dist u v < δ →
      ‖g u - g v‖ ≤ ε ∧
        ∀ i, ‖TestFunctions.partialDerivR4 i g u - TestFunctions.partialDerivR4 i g v‖ ≤ ε := by
  have hu1 : UniformContinuous g := hgc.uniformContinuous_of_continuous hg.continuous
  have hu2 : UniformContinuous (fderiv ℝ g) :=
    (hgc.fderiv ℝ).uniformContinuous_of_continuous (hg.continuous_fderiv (by norm_num))
  obtain ⟨δ₁, hδ₁, h₁⟩ := Metric.uniformContinuous_iff.1 hu1 ε hε
  obtain ⟨δ₂, hδ₂, h₂⟩ := Metric.uniformContinuous_iff.1 hu2 ε hε
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun u v huv => ⟨?_, fun i => ?_⟩⟩
  · have hd := h₁ (lt_of_lt_of_le huv (min_le_left _ _))
    rw [dist_eq_norm] at hd
    exact hd.le
  · have hd := h₂ (lt_of_lt_of_le huv (min_le_right _ _))
    rw [dist_eq_norm] at hd
    rw [partialDerivR4_eq_fderiv hg, partialDerivR4_eq_fderiv hg, ← _root_.sub_apply]
    calc ‖(fderiv ℝ g u - fderiv ℝ g v) (Pi.single i 1 : Fin 4 → ℝ)‖
        ≤ ‖fderiv ℝ g u - fderiv ℝ g v‖ * ‖(Pi.single i 1 : Fin 4 → ℝ)‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ = ‖fderiv ℝ g u - fderiv ℝ g v‖ := by simp [Pi.norm_single]
      _ ≤ ε := hd.le
theorem exists_simpleFunc_near_id {K : Set (Fin 4 → ℝ)} (hK : IsCompact K) (hKne : K.Nonempty)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ r : SimpleFunc (Fin 4 → ℝ) (Fin 4 → ℝ), (∀ x, r x ∈ K) ∧ ∀ x ∈ K, dist (r x) x < δ := by
  have : Nonempty K := hKne.to_subtype
  let e : ℕ → (Fin 4 → ℝ) := fun n => (TopologicalSpace.denseSeq K n : Fin 4 → ℝ)
  have hcover : K ⊆ ⋃ n, Metric.ball (e n) δ := by
    intro x hx
    obtain ⟨n, hn⟩ := (TopologicalSpace.denseRange_denseSeq K).exists_dist_lt ⟨x, hx⟩ hδ
    exact Set.mem_iUnion.2 ⟨n, by
      rw [Metric.mem_ball]
      exact hn⟩
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover _ (fun _ => Metric.isOpen_ball) hcover
  refine ⟨SimpleFunc.nearestPt e (t.sup id), fun x => ?_, fun x hx => ?_⟩
  · change e _ ∈ K
    exact Subtype.coe_prop _
  · obtain ⟨n, hn, hxn⟩ : ∃ n ∈ t, x ∈ Metric.ball (e n) δ := by
      simpa using ht hx
    have hle : n ≤ t.sup id := Finset.le_sup (f := id) hn
    have hed := SimpleFunc.edist_nearestPt_le e x hle
    rw [edist_dist, edist_dist, ENNReal.ofReal_le_ofReal_iff dist_nonneg] at hed
    exact lt_of_le_of_lt hed (by simpa [dist_comm] using hxn)
theorem integral_mul_comp_simpleFunc (r : SimpleFunc (Fin 4 → ℝ) (Fin 4 → ℝ))
    {φ : (Fin 4 → ℝ) → ℂ} (hφ : Integrable φ) (w : (Fin 4 → ℝ) → ℂ) :
    Integrable (fun x => φ x * w (r x)) ∧
      ∫ x, φ x * w (r x) = ∑ z ∈ r.range, (∫ x in r ⁻¹' {z}, φ x) * w z := by
  have hint : Integrable (fun x => φ x * w (r x)) := by
    refine Integrable.mono' (g := fun x => ‖φ x‖ * ∑ z ∈ r.range, ‖w z‖) (hφ.norm.mul_const _)
      (hφ.aestronglyMeasurable.mul ((r.map w).measurable.aestronglyMeasurable))
      (Filter.Eventually.of_forall fun x => ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left
      (Finset.single_le_sum (f := fun z => ‖w z‖) (fun _ _ => norm_nonneg _) (r.mem_range_self x))
      (norm_nonneg _)
  refine ⟨hint, ?_⟩
  have hunion : (⋃ z ∈ r.range, r ⁻¹' {z}) = Set.univ := by
    ext x
    simp
  have hparts := integral_biUnion_finset (μ := (volume : Measure (Fin 4 → ℝ)))
    (f := fun x => φ x * w (r x)) r.range (s := fun z => r ⁻¹' {z})
    (fun z _ => r.measurableSet_fiber z)
    (fun z _ z' _ hzz => Set.disjoint_left.2 fun x hx hx' => hzz (hx.symm.trans hx'))
    (fun z _ => hint.integrableOn)
  rw [hunion, setIntegral_univ] at hparts
  rw [hparts]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [← integral_mul_const]
  refine setIntegral_congr_fun (r.measurableSet_fiber z) fun x hx => ?_
  have hrz : r x = z := hx
  simp [hrz]
theorem norm_integral_sub_integral_le {φ u v : (Fin 4 → ℝ) → ℂ} {K : Set (Fin 4 → ℝ)} {ε : ℝ}
    (hφ : Integrable φ) (hφK : ∀ x, x ∉ K → φ x = 0) (hu : Integrable fun x => φ x * u x)
    (hv : Integrable fun x => φ x * v x) (hε : ∀ x ∈ K, ‖u x - v x‖ ≤ ε) :
    ‖(∫ x, φ x * u x) - ∫ x, φ x * v x‖ ≤ ε * ∫ x, ‖φ x‖ := by
  rw [← integral_sub hu hv, ← integral_const_mul]
  refine norm_integral_le_of_norm_le (hφ.norm.const_mul ε)
    (Filter.Eventually.of_forall fun x => ?_)
  by_cases hx : x ∈ K
  · rw [← mul_sub, norm_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right (hε x hx) (norm_nonneg _)
  · simp [hφK x hx]
theorem norm_inner_apply_le {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (T : H →L[ℂ] H) (ξ ξ' : H) : ‖⟪ξ, T ξ'⟫_ℂ‖ ≤ ‖ξ‖ * ‖ξ'‖ * ‖T‖ := by
  calc ‖⟪ξ, T ξ'⟫_ℂ‖ ≤ ‖ξ‖ * ‖T ξ'‖ := norm_inner_le_norm _ _
    _ ≤ ‖ξ‖ * (‖T‖ * ‖ξ'‖) := mul_le_mul_of_nonneg_left (T.le_opNorm _) (norm_nonneg _)
    _ = ‖ξ‖ * ‖ξ'‖ * ‖T‖ := by ring
theorem conv_eq_integral (g φ : (Fin 4 → ℝ) → ℂ) (y : Fin 4 → ℝ) :
    EuclideanFunctionals.conv g φ y = ∫ x, φ x * g (y - x) := by
  have hsub := integral_sub_left_eq_self (fun x => φ x * g (y - x))
    (volume : Measure (Fin 4 → ℝ)) y
  simp only [sub_sub_cancel] at hsub
  rw [← hsub]
  change (∫ x, g x * φ (y - x)) = _
  exact integral_congr_ae (Filter.Eventually.of_forall fun x => mul_comm _ _)
theorem conv_eq_convolution (g φ : (Fin 4 → ℝ) → ℂ) :
    EuclideanFunctionals.conv g φ =
      MeasureTheory.convolution φ g (ContinuousLinearMap.mul ℝ ℂ) volume := by
  funext y
  rw [conv_eq_integral]
  rfl
theorem contDiff_conv_and_partial {g φ : (Fin 4 → ℝ) → ℂ} (hg : ContDiff ℝ 1 g)
    (hgc : HasCompactSupport g) (hφ : Continuous φ) :
    ContDiff ℝ 1 (EuclideanFunctionals.conv g φ) ∧
      ∀ i y, TestFunctions.partialDerivR4 i (EuclideanFunctionals.conv g φ) y =
        ∫ x, φ x * TestFunctions.partialDerivR4 i g (y - x) := by
  have hloc : LocallyIntegrable φ (volume : Measure (Fin 4 → ℝ)) := hφ.locallyIntegrable
  have hcd : ContDiff ℝ 1 (EuclideanFunctionals.conv g φ) := by
    rw [conv_eq_convolution]
    exact hgc.contDiff_convolution_right (n := 1) (ContinuousLinearMap.mul ℝ ℂ) hloc hg
  refine ⟨hcd, fun i y => ?_⟩
  rw [partialDerivR4_eq_fderiv hcd, conv_eq_convolution,
    (hgc.hasFDerivAt_convolution_right (ContinuousLinearMap.mul ℝ ℂ) hloc hg y).fderiv,
    convolution_precompR_apply (ContinuousLinearMap.mul ℝ ℂ) hloc (hgc.fderiv ℝ)
      (hg.continuous_fderiv one_ne_zero)]
  simp only [MeasureTheory.convolution]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [partialDerivR4_eq_fderiv hg]
  rfl
theorem inner_apply_conv_eq_integral {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (a : ((Fin 4 → ℝ) → ℂ) → H →L[ℂ] H) (B : ℝ) (hB : 0 ≤ B) (D : Set (Fin 4 → ℝ))
    (hbound : ∀ f, ContDiff ℝ 1 f → support f ⊆ D → ‖a f‖ ≤ B * WightmanReconstruction.supC1Norm f)
    (hlin : ∀ {ι : Type} (s : Finset ι) (c : ι → ℂ) (f : ι → (Fin 4 → ℝ) → ℂ),
      (∀ j ∈ s, ContDiff ℝ 1 (f j)) → (∀ j ∈ s, support (f j) ⊆ D) →
        a (∑ j ∈ s, c j • f j) = ∑ j ∈ s, c j • a (f j))
    {g φ : (Fin 4 → ℝ) → ℂ} (hg : ContDiff ℝ 1 g) (hgc : HasCompactSupport g)
    (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (hsum : ∀ x ∈ tsupport φ, ∀ y ∈ tsupport g, x + y ∈ D) :
    ContinuousOn (fun x => a (fun u => g (u - x))) (tsupport φ) ∧
      ∀ ξ ξ' : H, ⟪ξ, a (EuclideanFunctionals.conv g φ) ξ'⟫_ℂ =
        ∫ x, φ x * ⟪ξ, a (fun u => g (u - x)) ξ'⟫_ℂ := by
  have hK : IsCompact (tsupport φ) := hφc
  have hφi : Integrable φ := hφ.integrable_of_hasCompactSupport hφc
  have hφ0 : ∀ x, x ∉ tsupport φ → φ x = 0 := fun x hx => image_eq_zero_of_notMem_tsupport hx
  have hsh : ∀ x, ContDiff ℝ 1 (fun u => g (u - x)) :=
    fun x => hg.comp (contDiff_id.sub contDiff_const)
  have hshs : ∀ x ∈ tsupport φ, support (fun u => g (u - x)) ⊆ D := by
    intro x hx u hu
    have hxu := hsum x hx (u - x) (subset_tsupport g hu)
    simpa using hxu
  have hdiff : ∀ f f', ContDiff ℝ 1 f → support f ⊆ D → ContDiff ℝ 1 f' → support f' ⊆ D →
      ‖a f - a f'‖ ≤ B * WightmanReconstruction.supC1Norm (f - f') := by
    intro f f' hf hfs hf' hf's
    have hff : a (f - f') = a f - a f' := by
      have hl := hlin (Finset.univ : Finset Bool) (fun b => if b then 1 else -1)
        (fun b => if b then f else f') (by intro b _; cases b <;> simpa)
        (by intro b _; cases b <;> simpa)
      simpa [sub_eq_add_neg] using hl
    have hs : support (f - f') ⊆ D := (support_sub f f').trans (Set.union_subset hfs hf's)
    rw [← hff]
    exact hbound _ (hf.sub hf') hs
  have hnear : ∀ ε > 0, ∃ δ > 0, ∀ x z : Fin 4 → ℝ, dist x z < δ →
      WightmanReconstruction.supC1Norm ((fun u => g (u - x)) - fun u => g (u - z)) ≤ 3 * ε := by
    intro ε hε
    obtain ⟨δ, hδ, hmod⟩ := exists_uniform_modulus_of_contDiff hg hgc hε
    refine ⟨δ, hδ, fun x z hxz => ?_⟩
    have hd : ∀ y : Fin 4 → ℝ, dist (y - x) (y - z) < δ := fun y => by
      rw [dist_sub_left]
      exact hxz
    have hle := supC1Norm_le (f := (fun u => g (u - x)) - fun u => g (u - z)) (M := ε) (M' := ε)
      (fun y => (hmod _ _ (hd y)).1)
      (fun y i => by
        rw [partialDerivR4_sub (hsh x) (hsh z), partialDerivR4_comp_sub, partialDerivR4_comp_sub]
        exact (hmod _ _ (hd y)).2 i) hε.le
    linarith
  have hcont : ContinuousOn (fun x => a (fun u => g (u - x))) (tsupport φ) := by
    rw [Metric.continuousOn_iff]
    intro x hx ε hε
    have hB1 : 0 < B + 1 := by linarith
    obtain ⟨δ, hδ, hn⟩ := hnear (ε / (6 * (B + 1))) (by positivity)
    refine ⟨δ, hδ, fun x' hx' hd => ?_⟩
    rw [dist_eq_norm]
    calc ‖a (fun u => g (u - x')) - a (fun u => g (u - x))‖
        ≤ B * WightmanReconstruction.supC1Norm ((fun u => g (u - x')) - fun u => g (u - x)) :=
          hdiff _ _ (hsh x') (hshs x' hx') (hsh x) (hshs x hx)
      _ ≤ B * (3 * (ε / (6 * (B + 1)))) := mul_le_mul_of_nonneg_left (hn _ _ hd) hB
      _ < ε := by
          rw [show B * (3 * (ε / (6 * (B + 1)))) = (B * ε) / (2 * (B + 1)) by
            field_simp; ring, div_lt_iff₀ (by positivity)]
          nlinarith
  refine ⟨hcont, fun ξ ξ' => ?_⟩
  rcases (tsupport φ).eq_empty_or_nonempty with hemp | hne
  · have hφz : φ = 0 := funext fun x => hφ0 x (by simp [hemp])
    have hcv : EuclideanFunctionals.conv g φ = 0 := by
      funext y
      simp [conv_eq_integral, hφz]
    have ha0 : a 0 = 0 := by
      simpa using hlin (∅ : Finset Bool) (fun _ => 0) (fun _ => 0) (by simp) (by simp)
    rw [hcv, ha0]
    simp [hφz]
  have hcv := contDiff_conv_and_partial hg hgc hφ (φ := φ)
  have hcvs : support (EuclideanFunctionals.conv g φ) ⊆ D := by
    intro y hy
    rw [conv_eq_convolution] at hy
    obtain ⟨u, hu, v, hv, rfl⟩ := support_convolution_subset (ContinuousLinearMap.mul ℝ ℂ) hy
    exact hsum u (subset_tsupport φ hu) v (subset_tsupport g hv)
  set w : (Fin 4 → ℝ) → ℂ := fun x => ⟪ξ, a (fun u => g (u - x)) ξ'⟫_ℂ with hwdef
  have hw : ContinuousOn w (tsupport φ) :=
    (Continuous.inner continuous_const
      (continuous_id.clm_apply continuous_const)).comp_continuousOn hcont
  have hφw : Integrable fun x => φ x * w x := by
    have hon : IntegrableOn (fun x => φ x * w x) (tsupport φ) :=
      (hφ.continuousOn.mul hw).integrableOn_compact hK
    refine (integrableOn_iff_integrable_of_support_subset fun x hx => ?_).1 hon
    by_contra hxK
    exact hx (by simp [hφ0 x hxK])
  set I : ℝ := ∫ x, ‖φ x‖ with hI
  have hI0 : 0 ≤ I := integral_nonneg fun _ => norm_nonneg _
  set X : ℂ := ⟪ξ, a (EuclideanFunctionals.conv g φ) ξ'⟫_ℂ - ∫ x, φ x * w x with hX
  have key : ∀ ε > 0, ‖X‖ ≤ ε * (6 * ‖ξ‖ * ‖ξ'‖ * B * I) := by
    intro ε hε
    obtain ⟨δ₁, hδ₁, hm⟩ := exists_uniform_modulus_of_contDiff hg hgc hε
    obtain ⟨δ₂, hδ₂, hn⟩ := hnear ε hε
    obtain ⟨r, hrK, hrδ⟩ := exists_simpleFunc_near_id hK hne (lt_min hδ₁ hδ₂)
    have hrange : ∀ z ∈ r.range, z ∈ tsupport φ := by
      intro z hz
      obtain ⟨x, rfl⟩ := SimpleFunc.mem_range.1 hz
      exact hrK x
    set c : (Fin 4 → ℝ) → ℂ := fun z => ∫ x in r ⁻¹' {z}, φ x with hc
    set S : (Fin 4 → ℝ) → ℂ := ∑ z ∈ r.range, c z • (fun u => g (u - z)) with hS
    have hSe : S = fun y => ∑ z ∈ r.range, c z * g (y - z) := by
      funext y
      simp [hS, Finset.sum_apply]
    have hS1 : ContDiff ℝ 1 S := by
      rw [hSe]
      exact ContDiff.sum fun z _ => contDiff_const.mul (hsh z)
    have hSs : support S ⊆ D := by
      intro y hy
      have hy' : ∑ z ∈ r.range, c z * g (y - z) ≠ 0 := by
        rw [hSe] at hy
        exact hy
      obtain ⟨z, hz, hzy⟩ := Finset.exists_ne_zero_of_sum_ne_zero hy'
      exact hshs z (hrange z hz) (right_ne_zero_of_mul hzy)
    have hSv : ∀ y, S y = ∫ x, φ x * g (y - r x) := fun y => by
      rw [(integral_mul_comp_simpleFunc r hφi (fun z => g (y - z))).2, hSe]
    have hSp : ∀ i y, TestFunctions.partialDerivR4 i S y =
        ∫ x, φ x * TestFunctions.partialDerivR4 i g (y - r x) := fun i y => by
      rw [hS, partialDerivR4_finset_sum _ _ _ (fun z _ => hsh z) i y,
        (integral_mul_comp_simpleFunc r hφi
          (fun z => TestFunctions.partialDerivR4 i g (y - z))).2]
      exact Finset.sum_congr rfl fun z _ => by rw [partialDerivR4_comp_sub]
    have hnearby : ∀ (y x : Fin 4 → ℝ), x ∈ tsupport φ → dist (y - r x) (y - x) < δ₁ :=
      fun y x hx => by
        rw [dist_sub_left]
        exact lt_of_lt_of_le (hrδ x hx) (min_le_left _ _)
    have hpc : ∀ i : Fin 4, Continuous (TestFunctions.partialDerivR4 i g) := fun i => by
      have hpe : TestFunctions.partialDerivR4 i g =
          fun u => fderiv ℝ g u (Pi.single i 1 : Fin 4 → ℝ) :=
        funext fun u => partialDerivR4_eq_fderiv hg i u
      rw [hpe]
      exact (hg.continuous_fderiv one_ne_zero).clm_apply continuous_const
    have hint : ∀ (h : (Fin 4 → ℝ) → ℂ), Continuous h → ∀ y : Fin 4 → ℝ,
        Integrable fun x => φ x * h (y - x) := fun h hh y =>
      (hφ.mul (hh.comp (continuous_const.sub continuous_id))).integrable_of_hasCompactSupport
        hφc.mul_right
    have hN : WightmanReconstruction.supC1Norm (EuclideanFunctionals.conv g φ - S) ≤
        ε * I + 2 * (ε * I) := by
      refine supC1Norm_le (fun y => ?_) (fun y i => ?_) (by positivity)
      · rw [Pi.sub_apply, conv_eq_integral, hSv]
        exact norm_integral_sub_integral_le hφi hφ0 (hint g hg.continuous y)
          (integral_mul_comp_simpleFunc r hφi (fun z => g (y - z))).1
          (fun x hx => by
            rw [norm_sub_rev]
            exact (hm _ _ (hnearby y x hx)).1)
      · rw [partialDerivR4_sub hcv.1 hS1, hcv.2, hSp]
        exact norm_integral_sub_integral_le hφi hφ0 (hint _ (hpc i) y)
          (integral_mul_comp_simpleFunc r hφi
            (fun z => TestFunctions.partialDerivR4 i g (y - z))).1
          (fun x hx => by
            rw [norm_sub_rev]
            exact (hm _ _ (hnearby y x hx)).2 i)
    have hA : ‖a (EuclideanFunctionals.conv g φ) - a S‖ ≤ B * (3 * (ε * I)) := by
      refine (hdiff _ _ hcv.1 hcvs hS1 hSs).trans (mul_le_mul_of_nonneg_left ?_ hB)
      linarith
    have hAS : ⟪ξ, a S ξ'⟫_ℂ = ∫ x, φ x * w (r x) := by
      rw [(integral_mul_comp_simpleFunc r hφi w).2, hS,
        hlin r.range c (fun z u => g (u - z)) (fun z _ => hsh z)
          (fun z hz => hshs z (hrange z hz))]
      simp [hwdef]
      rfl
    have hsecond : ‖(∫ x, φ x * w (r x)) - ∫ x, φ x * w x‖ ≤
        (‖ξ‖ * ‖ξ'‖ * (B * (3 * ε))) * I := by
      refine norm_integral_sub_integral_le hφi hφ0 (integral_mul_comp_simpleFunc r hφi w).1 hφw
        (fun x hx => ?_)
      have he : w (r x) - w x =
          ⟪ξ, (a (fun u => g (u - r x)) - a (fun u => g (u - x))) ξ'⟫_ℂ := by
        simp [hwdef]
      rw [he]
      refine (norm_inner_apply_le _ ξ ξ').trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
      refine (hdiff _ _ (hsh _) (hshs _ (hrK x)) (hsh _) (hshs _ hx)).trans
        (mul_le_mul_of_nonneg_left (hn _ _ ?_) hB)
      exact lt_of_lt_of_le (hrδ x hx) (min_le_right _ _)
    have hfirst : ‖⟪ξ, (a (EuclideanFunctionals.conv g φ) - a S) ξ'⟫_ℂ‖ ≤
        ‖ξ‖ * ‖ξ'‖ * (B * (3 * (ε * I))) :=
      (norm_inner_apply_le _ ξ ξ').trans (mul_le_mul_of_nonneg_left hA (by positivity))
    have hsplit : X = ⟪ξ, (a (EuclideanFunctionals.conv g φ) - a S) ξ'⟫_ℂ +
        ((∫ x, φ x * w (r x)) - ∫ x, φ x * w x) := by
      rw [hX, ← hAS]
      simp
    rw [hsplit]
    refine (norm_add_le _ _).trans ((add_le_add hfirst hsecond).trans (le_of_eq ?_))
    ring
  have hX0 : X = 0 := by
    by_contra hne0
    have hpos : 0 < ‖X‖ := norm_pos_iff.2 hne0
    set Q : ℝ := 6 * ‖ξ‖ * ‖ξ'‖ * B * I with hQ
    have hQ0 : 0 ≤ Q := by positivity
    have hk := key (‖X‖ / (2 * (Q + 1))) (by positivity)
    have hlt : ‖X‖ / (2 * (Q + 1)) * Q < ‖X‖ := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      nlinarith
    linarith
  exact sub_eq_zero.1 hX0
theorem claim_of_insertionOperatorBounds (hIns : InsertionOperators.InsertionOperatorBounds) :
    Claim := by
  intro sigma E p C hc η g φ h0 h1 hg hφ hφc hsupp hdiam
  obtain ⟨hA, hL, -⟩ := hIns sigma E p C hc η h0 h1
  obtain ⟨hg1, hgc, -⟩ := hg
  have hC : 0 ≤ C := le_trans zero_le_one hc.one_le_const
  set D : Set (Fin 4 → ℝ) := (fun q : (Fin 4 → ℝ) × (Fin 4 → ℝ) => q.1 + q.2) ''
    (tsupport φ ×ˢ tsupport g) with hD
  have hDc : IsCompact D :=
    (IsCompact.prod hφc hgc).image (continuous_fst.add continuous_snd)
  have hDm : ∀ x ∈ tsupport φ, ∀ y ∈ tsupport g, x + y ∈ D :=
    fun x hx y hy => ⟨(x, y), ⟨hx, hy⟩, rfl⟩
  have hts : ∀ f : (Fin 4 → ℝ) → ℂ, support f ⊆ D → tsupport f ⊆ D :=
    fun f hf => closure_minimal hf hDc.isClosed
  have hDd : ∀ x ∈ D, ∀ y ∈ D, TorusMetric.euclidNormVec (x - y) ≤ 1 := by
    rintro _ ⟨⟨x, y⟩, ⟨hx, hy⟩, rfl⟩ _ ⟨⟨x', y'⟩, ⟨hx', hy'⟩, rfl⟩
    exact hdiam x hx y hy x' hx' y' hy'
  have hadm : ∀ f : (Fin 4 → ℝ) → ℂ, ContDiff ℝ 1 f → support f ⊆ D →
      InsertedFieldForm.IsAdmissible η f := by
    intro f hf hs
    refine ⟨⟨hf, hDc.of_isClosed_subset (isClosed_tsupport f) (hts f hs), Set.subset_univ _⟩,
      fun x hx => ?_, fun x hx y hy => hDd x (hts f hs hx) y (hts f hs hy)⟩
    obtain ⟨⟨u, v⟩, ⟨hu, hv⟩, rfl⟩ := hts f hs hx
    exact hsupp u hu v hv
  have main := inner_apply_conv_eq_integral (InsertedFieldForm.insertionOp sigma η)
    (C * η ^ (-p)) (mul_nonneg hC (Real.rpow_nonneg h0.le _)) D
    (fun f hf hs => (hA f (hadm f hf hs)).2)
    (fun s c f hf hs => hL s c f D
      (fun j hj => hadm _ (hf j hj) (hs j hj)) (fun j hj => hts _ (hs j hj)) hDd)
    hg1 hgc hφ hφc hDm
  exact main
end YangMills.Construction.InsertionSmearing
end
