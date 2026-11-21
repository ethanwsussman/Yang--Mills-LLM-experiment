import YangMills.Construction.RotationInvariance.RadialBumpsExistAndMollifyInC1
import Mathlib
set_option autoImplicit false
open MeasureTheory Set Metric Filter Topology
open scoped Pointwise ContDiff Convolution
noncomputable section
namespace YangMills.Construction
open RealPlane
namespace EuclideanFunctionals.RadialMollifiers
def bumpProfile (y : RealPlane) : ℝ := expNegInvGlue (1 / 4 - ‖y‖ ^ 2)
theorem bumpProfile_contDiff : ContDiff ℝ ∞ bumpProfile :=
  (expNegInvGlue.contDiff (n := ⊤)).comp (contDiff_const.sub (contDiff_norm_sq ℝ))
theorem bumpProfile_nonneg (y : RealPlane) : 0 ≤ bumpProfile y := expNegInvGlue.nonneg _
theorem bumpProfile_eq_zero {y : RealPlane} (hy : 1 / 2 ≤ ‖y‖) : bumpProfile y = 0 := by
  apply expNegInvGlue.zero_of_nonpos
  nlinarith [norm_nonneg y]
theorem bumpProfile_hasCompactSupport : HasCompactSupport bumpProfile :=
  HasCompactSupport.intro (isCompact_closedBall (0 : RealPlane) (1 / 2)) fun y hy => by
    apply bumpProfile_eq_zero
    have : ¬ ‖y‖ ≤ 1 / 2 := by simpa using hy
    linarith
theorem bumpProfile_integral_pos : 0 < ∫ y, bumpProfile y := by
  refine bumpProfile_contDiff.continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
    bumpProfile_hasCompactSupport bumpProfile_nonneg (x := 0) ?_
  apply ne_of_gt
  apply expNegInvGlue.pos_of_pos
  norm_num
def normalizedBump (r : ℝ) (y : RealPlane) : ℝ :=
  (∫ y, bumpProfile y)⁻¹ * (r ^ 2)⁻¹ * bumpProfile (r⁻¹ • y)
theorem normalizedBump_contDiff (r : ℝ) : ContDiff ℝ ∞ (normalizedBump r) :=
  contDiff_const.mul (bumpProfile_contDiff.comp (contDiff_id.const_smul r⁻¹))
theorem normalizedBump_nonneg {r : ℝ} (y : RealPlane) : 0 ≤ normalizedBump r y :=
  mul_nonneg (mul_nonneg (inv_nonneg.2 bumpProfile_integral_pos.le) (inv_nonneg.2 (sq_nonneg r)))
    (bumpProfile_nonneg _)
theorem normalizedBump_eq_zero {r : ℝ} (hr : 0 < r) {y : RealPlane} (hy : r / 2 ≤ ‖y‖) :
    normalizedBump r y = 0 := by
  have : bumpProfile (r⁻¹ • y) = 0 := by
    apply bumpProfile_eq_zero
    rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hr, inv_mul_eq_div, le_div_iff₀ hr]
    linarith
  simp [normalizedBump, this]
theorem normalizedBump_support_subset {r : ℝ} (hr : 0 < r) :
    Function.support (normalizedBump r) ⊆ closedBall 0 (r / 2) := by
  intro y hy
  by_contra hn
  have hn' : ¬ ‖y‖ ≤ r / 2 := by simpa using hn
  exact hy (normalizedBump_eq_zero hr (not_le.1 hn').le)
theorem normalizedBump_tsupport_subset {r : ℝ} (hr : 0 < r) :
    tsupport (normalizedBump r) ⊆ closedBall 0 (r / 2) :=
  closure_minimal (normalizedBump_support_subset hr) isClosed_closedBall
theorem normalizedBump_integral {r : ℝ} (hr : 0 < r) : ∫ y, normalizedBump r y = 1 := by
  have hZ := bumpProfile_integral_pos
  have hs : ∫ y : RealPlane, bumpProfile (r⁻¹ • y) = r ^ 2 * ∫ y, bumpProfile y := by
    have := Measure.integral_comp_inv_smul_of_nonneg (volume : Measure RealPlane) bumpProfile
      hr.le
    simpa using this
  simp only [normalizedBump]
  rw [integral_const_mul, hs]
  field_simp
theorem convolve_ofRealFun_eq (b : RealPlane → ℂ) (δ : RealPlane → ℝ) :
    convolve b (ofRealFun δ) =
      δ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] b := by
  funext y'
  rw [convolution_lsmul_swap]
  simp [convolve, ofRealFun, Complex.real_smul, mul_comm]
def planeComponentCLM : (Fin 4 → ℝ) →L[ℝ] RealPlane :=
  LinearMap.toContinuousLinearMap
    { toFun := planeComponent
      map_add' := fun x x' => by
        ext i
        fin_cases i <;> simp [planeComponent]
      map_smul' := fun c x => by
        ext i
        fin_cases i <;> simp [planeComponent] }
def orthogonalComponentCLM : (Fin 4 → ℝ) →L[ℝ] RealPlane :=
  LinearMap.toContinuousLinearMap
    { toFun := orthogonalComponent
      map_add' := fun x x' => by
        ext i
        fin_cases i <;> simp [orthogonalComponent]
      map_smul' := fun c x => by
        ext i
        fin_cases i <;> simp [orthogonalComponent] }
theorem planeComponentCLM_apply (x : Fin 4 → ℝ) : planeComponentCLM x = planeComponent x := rfl
theorem orthogonalComponentCLM_apply (x : Fin 4 → ℝ) :
    orthogonalComponentCLM x = orthogonalComponent x := rfl
theorem fderiv_productFunction_apply {α : RealPlane → ℂ} {φ : RealPlane → ℝ}
    (hα : Differentiable ℝ α) (hφ : Differentiable ℝ φ) (x v : Fin 4 → ℝ) :
    fderiv ℝ (productFunction α φ) x v =
      α (planeComponent x) *
          ((fderiv ℝ φ (orthogonalComponent x) (orthogonalComponentCLM v) : ℝ) : ℂ) +
        (φ (orthogonalComponent x) : ℂ) * fderiv ℝ α (planeComponent x) (planeComponentCLM v) := by
  have h1 : HasFDerivAt (fun x => α (planeComponentCLM x))
      ((fderiv ℝ α (planeComponentCLM x)).comp planeComponentCLM) x :=
    (hα _).hasFDerivAt.comp x planeComponentCLM.hasFDerivAt
  have h2 : HasFDerivAt (fun x => φ (orthogonalComponentCLM x))
      ((fderiv ℝ φ (orthogonalComponentCLM x)).comp orthogonalComponentCLM) x :=
    (hφ _).hasFDerivAt.comp x orthogonalComponentCLM.hasFDerivAt
  have h3 : HasFDerivAt (fun x => ((φ (orthogonalComponentCLM x) : ℝ) : ℂ))
      (Complex.ofRealCLM.comp ((fderiv ℝ φ (orthogonalComponentCLM x)).comp
        orthogonalComponentCLM)) x :=
    Complex.ofRealCLM.hasFDerivAt.comp x h2
  have h4 : HasFDerivAt
      (fun x => α (planeComponentCLM x) * ((φ (orthogonalComponentCLM x) : ℝ) : ℂ)) _ x :=
    h1.mul h3
  have h5 : productFunction α φ =
      fun x => α (planeComponentCLM x) * ((φ (orthogonalComponentCLM x) : ℝ) : ℂ) := rfl
  rw [h5, h4.fderiv]
  simp [planeComponentCLM_apply, orthogonalComponentCLM_apply]
theorem norm_mul_lt_of_norm_lt_div {a c : ℂ} {C ε : ℝ} (hε : 0 < ε) (ha : ‖a‖ < ε / (C + 1))
    (hc : ‖c‖ ≤ C) : ‖a * c‖ < ε := by
  have hC : 0 ≤ C := (norm_nonneg c).trans hc
  have hpos : 0 < C + 1 := by linarith
  rw [norm_mul]
  calc ‖a‖ * ‖c‖ ≤ ε / (C + 1) * C :=
        mul_le_mul ha.le hc (norm_nonneg c) (div_pos hε hpos).le
    _ < ε := by
        rw [div_mul_eq_mul_div, div_lt_iff₀ hpos]
        nlinarith
theorem tendstoC1_productFunction {αs : ℕ → RealPlane → ℂ} {b : RealPlane → ℂ}
    {φ : RealPlane → ℝ} (hαs : ∀ k, Differentiable ℝ (αs k)) (hb : Differentiable ℝ b)
    (hφ : φ ∈ realLabels) (H0 : TendstoUniformly αs b atTop)
    (H1 : ∀ w, TendstoUniformly (fun k y => fderiv ℝ (αs k) y w) (fun y => fderiv ℝ b y w) atTop) :
    TendstoC1 (fun k => productFunction (αs k) φ) (productFunction b φ) := by
  have hφd : Differentiable ℝ φ := hφ.1.differentiable one_ne_zero
  obtain ⟨C, hC⟩ := hφ.2.exists_bound_of_continuous hφ.1.continuous
  rw [Metric.tendstoUniformly_iff] at H0
  refine ⟨?_, fun μ => ?_⟩
  · rw [Metric.tendstoUniformly_iff]
    intro ε hε
    have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
    filter_upwards [H0 (ε / (C + 1)) (div_pos hε (by linarith))] with k hk x
    have hm := norm_mul_lt_of_norm_lt_div (c := (φ (orthogonalComponent x) : ℂ)) hε
      (by simpa [dist_eq_norm] using hk (planeComponent x))
      (by simpa using hC (orthogonalComponent x))
    rw [dist_eq_norm]
    simpa [productFunction, sub_mul] using hm
  · set v : Fin 4 → ℝ := Pi.single μ 1 with hv
    have hdφ : HasCompactSupport fun z => fderiv ℝ φ z (orthogonalComponentCLM v) :=
      (hφ.2.fderiv (𝕜 := ℝ)).comp_left
        (g := fun L : RealPlane →L[ℝ] ℝ => L (orthogonalComponentCLM v)) (by simp)
    have hcφ : Continuous fun z => fderiv ℝ φ z (orthogonalComponentCLM v) :=
      (hφ.1.continuous_fderiv one_ne_zero).clm_apply continuous_const
    obtain ⟨D, hD⟩ := hdφ.exists_bound_of_continuous hcφ
    have H1' := H1 (planeComponentCLM v)
    rw [Metric.tendstoUniformly_iff] at H1' ⊢
    intro ε hε
    have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
    have hD0 : 0 ≤ D := (norm_nonneg _).trans (hD 0)
    have hε2 : 0 < ε / 2 := by linarith
    filter_upwards [H0 (ε / 2 / (D + 1)) (div_pos hε2 (by linarith)),
      H1' (ε / 2 / (C + 1)) (div_pos hε2 (by linarith))] with k hk0 hk1 x
    have ha := norm_mul_lt_of_norm_lt_div
      (c := ((fderiv ℝ φ (orthogonalComponent x) (orthogonalComponentCLM v) : ℝ) : ℂ)) hε2
      (by simpa [dist_eq_norm] using hk0 (planeComponent x))
      (by simpa using hD (orthogonalComponent x))
    have hc := norm_mul_lt_of_norm_lt_div (c := (φ (orthogonalComponent x) : ℂ)) hε2
      (by simpa [dist_eq_norm] using hk1 (planeComponent x))
      (by simpa using hC (orthogonalComponent x))
    rw [fderiv_productFunction_apply hb hφd, fderiv_productFunction_apply (hαs k) hφd,
      dist_eq_norm]
    have hsplit :
        b (planeComponent x) *
              ((fderiv ℝ φ (orthogonalComponent x) (orthogonalComponentCLM v) : ℝ) : ℂ) +
            (φ (orthogonalComponent x) : ℂ) * fderiv ℝ b (planeComponent x) (planeComponentCLM v) -
          (αs k (planeComponent x) *
              ((fderiv ℝ φ (orthogonalComponent x) (orthogonalComponentCLM v) : ℝ) : ℂ) +
            (φ (orthogonalComponent x) : ℂ) *
              fderiv ℝ (αs k) (planeComponent x) (planeComponentCLM v)) =
        (b (planeComponent x) - αs k (planeComponent x)) *
            ((fderiv ℝ φ (orthogonalComponent x) (orthogonalComponentCLM v) : ℝ) : ℂ) +
          (fderiv ℝ b (planeComponent x) (planeComponentCLM v) -
              fderiv ℝ (αs k) (planeComponent x) (planeComponentCLM v)) *
            (φ (orthogonalComponent x) : ℂ) := by
      ring
    rw [hsplit]
    calc _ ≤ _ := norm_add_le _ _
      _ < ε / 2 + ε / 2 := add_lt_add ha hc
      _ = ε := by ring
theorem tendstoUniformly_convolution_of_shrinking {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [CompleteSpace F] {δs : ℕ → RealPlane → ℝ} {r : ℕ → ℝ}
    (hr : Tendsto r atTop (𝓝 0)) (hsupp : ∀ k, Function.support (δs k) ⊆ ball 0 (r k))
    (hnn : ∀ k y, 0 ≤ δs k y) (hint : ∀ k, ∫ y, δs k y = 1) {g : RealPlane → F}
    (hg : UniformContinuous g) :
    TendstoUniformly (fun k => δs k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) g atTop := by
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  obtain ⟨s, hs, hgs⟩ := Metric.uniformContinuous_iff.1 hg (ε / 2) (by linarith)
  filter_upwards [hr.eventually (gt_mem_nhds hs)] with k hk y
  have hd : dist ((δs k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) y) (g y) ≤ ε / 2 :=
    dist_convolution_le (by linarith) (hsupp k) (hnn k) (hint k)
      hg.continuous.aestronglyMeasurable fun x hx =>
        (hgs ((mem_ball.1 hx).trans hk)).le
  rw [dist_comm]
  linarith
theorem fderiv_convolution_lsmul_apply {δ : RealPlane → ℝ} (hδ : Continuous δ)
    {b : RealPlane → ℂ} (hb : b ∈ complexProfiles) (y w : RealPlane) :
    fderiv ℝ (δ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] b) y w =
      (δ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] fun a => fderiv ℝ b a w) y := by
  have hloc : LocallyIntegrable δ volume := hδ.locallyIntegrable
  rw [(hb.2.hasFDerivAt_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ) hloc hb.1 y).fderiv]
  exact convolution_precompR_apply _ hloc (hb.2.fderiv (𝕜 := ℝ))
    (hb.1.continuous_fderiv one_ne_zero) y w
theorem existAndConvergeC1_holds : ExistAndConvergeC1 := by
  intro m S d η hη
  have hc : 0 < d.base.frac := d.base.frac_mem.1
  have hcη : 0 < d.base.frac * η := mul_pos hc hη.1
  have hjpos : ∀ j : ℕ+, (0 : ℝ) < ((j : ℕ) : ℝ) := fun j => Nat.cast_pos.2 j.pos
  refine ⟨⟨fun j => normalizedBump (d.base.frac * η / ((j : ℕ) : ℝ)), ?_⟩, ?_⟩
  · have hr : ∀ j : ℕ+, 0 < d.base.frac * η / ((j : ℕ) : ℝ) :=
      fun j => div_pos hcη (hjpos j)
    have hts : ∀ j : ℕ+, tsupport (normalizedBump (d.base.frac * η / ((j : ℕ) : ℝ))) ⊆
        closedBall 0 (d.base.frac * η / ((j : ℕ) : ℝ) / 2) :=
      fun j => normalizedBump_tsupport_subset (hr j)
    refine ⟨fun j => normalizedBump_contDiff _, fun j y => normalizedBump_nonneg y, fun j => ?_,
      fun j => ?_, fun j y y' hyy => ?_, fun j => normalizedBump_integral (hr j)⟩
    · exact HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall _ _)
        (subset_tsupport _ |>.trans (hts j))
    · intro y hy
      have hy' : ‖y‖ ≤ d.base.frac * η / ((j : ℕ) : ℝ) / 2 := by
        simpa using hts j hy
      have : ‖y - 0‖ < d.base.frac * η / ((j : ℕ) : ℝ) := by
        rw [sub_zero]
        linarith [hr j]
      exact this
    · simp [normalizedBump, bumpProfile, norm_smul, hyy]
  · intro δ hδ b hb φ hφ
    have hcont : ∀ j, Continuous (δ j) := fun j => (hδ.contDiff j).continuous
    have hsupp : ∀ j : ℕ+, Function.support (δ j) ⊆
        ball 0 (d.base.frac * η / ((j : ℕ) : ℝ)) := fun j y hy => by
      have := hδ.tsupport_subset j (subset_tsupport _ hy)
      have h' : ‖y - 0‖ < d.base.frac * η / ((j : ℕ) : ℝ) := this
      simpa using h'
    have hconv : ∀ j, convolve b (ofRealFun (δ j)) =
        δ j ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] b := fun j => convolve_ofRealFun_eq b _
    have hbig : ∀ j : ℕ+, d.base.frac * η / ((j : ℕ) : ℝ) ≤ d.base.frac * η :=
      fun j => div_le_self hcη.le (Nat.one_le_cast.mpr j.pos)
    have hC1 : ∀ j, ContDiff ℝ 1 (δ j ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] b) := fun j =>
      hb.2.contDiff_convolution_right _ (hcont j).locallyIntegrable hb.1
    have hK : IsCompact (tsupport b + closedDiscAt 0 (d.base.frac * η)) := by
      have : closedDiscAt (0 : RealPlane) (d.base.frac * η) =
          closedBall 0 (d.base.frac * η) := by
        ext y
        simp [closedDiscAt]
      rw [this]
      exact hb.2.isCompact.add (isCompact_closedBall _ _)
    have hts : ∀ j, tsupport (δ j ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] b) ⊆
        tsupport b + closedDiscAt 0 (d.base.frac * η) := fun j => by
      refine closure_minimal ?_ hK.isClosed
      refine (support_convolution_subset_swap _).trans ?_
      refine Set.add_subset_add (subset_tsupport _) fun y hy => ?_
      have := hsupp j hy
      have h' : ‖y‖ < d.base.frac * η / ((j : ℕ) : ℝ) := by simpa using this
      exact show ‖y - 0‖ ≤ d.base.frac * η from by
        rw [sub_zero]
        exact h'.le.trans (hbig j)
    refine ⟨fun j => ?_, ?_⟩
    · rw [hconv j]
      exact ⟨⟨hC1 j, hK.of_isClosed_subset (isClosed_tsupport _) (hts j)⟩, hts j⟩
    · have hr : Tendsto (fun k : ℕ => d.base.frac * η / (((k.succPNat : ℕ+) : ℕ) : ℝ))
          atTop (𝓝 0) := by
        have h := tendsto_const_div_atTop_nhds_zero_nat (d.base.frac * η)
        have h' := h.comp (tendsto_add_atTop_nat 1)
        refine h'.congr fun k => ?_
        simp [Nat.succPNat]
      have hU0 : UniformContinuous b :=
        hb.2.uniformContinuous_of_continuous hb.1.continuous
      have hUw : ∀ w, UniformContinuous fun a => fderiv ℝ b a w := fun w => by
        have hd : HasCompactSupport fun a => fderiv ℝ b a w :=
          (hb.2.fderiv (𝕜 := ℝ)).comp_left (g := fun L : RealPlane →L[ℝ] ℂ => L w) (by simp)
        exact hd.uniformContinuous_of_continuous
          ((hb.1.continuous_fderiv one_ne_zero).clm_apply continuous_const)
      have hb' : Differentiable ℝ b := hb.1.differentiable one_ne_zero
      simp only [hconv]
      refine tendstoC1_productFunction (fun k => (hC1 _).differentiable one_ne_zero) hb' hφ
        (tendstoUniformly_convolution_of_shrinking hr (fun k => hsupp _) (fun k => hδ.nonneg _)
          (fun k => hδ.integral_eq_one _) hU0) fun w => ?_
      have h := tendstoUniformly_convolution_of_shrinking (g := fun a => fderiv ℝ b a w) hr
        (fun k => hsupp k.succPNat) (fun k => hδ.nonneg k.succPNat)
        (fun k => hδ.integral_eq_one k.succPNat) (hUw w)
      have heq : (fun (k : ℕ) y =>
          fderiv ℝ (δ k.succPNat ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] b) y w) =
          fun k => δ k.succPNat ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
            fun a => fderiv ℝ b a w := by
        funext k y
        exact fderiv_convolution_lsmul_apply (hcont _) hb y w
      beta_reduce
      rw [heq]
      exact h
end EuclideanFunctionals.RadialMollifiers
end YangMills.Construction
end
