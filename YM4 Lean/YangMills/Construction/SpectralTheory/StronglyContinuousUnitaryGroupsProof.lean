import YangMills.Construction.BorelCalculus.BoundedCalculusConstruction
import YangMills.Construction.EuclideanSpectral.FunctionalCalculusTransport
import YangMills.Construction.SpectralTheory.JointMeasureOfASemigroupAndARepresentationProof
import YangMills.Construction.SpectralTheory.SpectralTheoremForSelfAdjointOperators
import Mathlib
set_option autoImplicit false
open MeasureTheory Set Filter Topology
open scoped InnerProductSpace ComplexConjugate ComplexOrder
noncomputable section
namespace YangMills.Construction.UnitaryGroups.Stone
open YangMills.Construction.BorelSpectral YangMills.Construction.HilbertSpaceBasics YangMills.Construction.SpectralTheorem YangMills.Construction.SelfAdjointFunctions YangMills.Construction.BorelCalculus YangMills.Construction.JointSpectral
section Group
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {U W : ℝ → H →L[ℂ] H} {C : H →L[ℂ] H}
theorem group_apply_add (hU : IsContinuousUnitaryGroup U) (s t : ℝ) (ψ : H) :
    U (s + t) ψ = U s (U t ψ) := by
  rw [← hU.1.2.2 s t]
  rfl
theorem group_apply_zero (hU : IsContinuousUnitaryGroup U) (ψ : H) : U 0 ψ = ψ := by
  rw [hU.1.2.1]
  rfl
theorem group_star (hU : IsContinuousUnitaryGroup U) (s : ℝ) : star (U s) = U (-s) := by
  have h1 : star (U s) * U s = 1 := (hU.1.1 s).1
  have h2 : U s * U (-s) = 1 := by rw [hU.1.2.2, add_neg_cancel, hU.1.2.1]
  calc star (U s) = star (U s) * (U s * U (-s)) := by rw [h2, mul_one]
    _ = U (-s) := by rw [← mul_assoc, h1, one_mul]
theorem inner_star_apply_eq (A : H →L[ℂ] H) (φ ψ : H) : ⟪φ, star A ψ⟫_ℂ = ⟪A φ, ψ⟫_ℂ := by
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]
theorem group_inner_apply (hU : IsContinuousUnitaryGroup U) (s : ℝ) (φ ψ : H) :
    ⟪U s φ, U s ψ⟫_ℂ = ⟪φ, ψ⟫_ℂ := by
  have h1 : star (U s) * U s = 1 := (hU.1.1 s).1
  have h2 : ⟪φ, star (U s) (U s ψ)⟫_ℂ = ⟪U s φ, U s ψ⟫_ℂ := inner_star_apply_eq _ _ _
  rw [← h2]
  have h3 : star (U s) (U s ψ) = ψ := by
    have := congrArg (fun T : H →L[ℂ] H => T ψ) h1
    simpa using this
  rw [h3]
theorem group_norm_apply (hU : IsContinuousUnitaryGroup U) (s : ℝ) (ψ : H) : ‖U s ψ‖ = ‖ψ‖ := by
  have h := group_inner_apply hU s ψ ψ
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h
  have h2 : ‖U s ψ‖ ^ 2 = ‖ψ‖ ^ 2 := by exact_mod_cast h
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h2
theorem group_continuous_apply (hU : IsContinuousUnitaryGroup U) (ψ : H) :
    Continuous fun t => U t ψ := by
  rw [continuous_iff_continuousAt]
  intro s₀
  have hc : Tendsto (fun t : ℝ => t - s₀) (𝓝 s₀) (𝓝 0) := by
    have : Continuous fun t : ℝ => t - s₀ := by fun_prop
    simpa using this.tendsto s₀
  have h0 : Tendsto (fun t => U (t - s₀) ψ) (𝓝 s₀) (𝓝 ψ) := by
    have h : Tendsto (fun t => U t ψ) (𝓝 0) (𝓝 ψ) := hU.2 ψ
    exact h.comp hc
  have h1 : Tendsto (fun t => U s₀ (U (t - s₀) ψ)) (𝓝 s₀) (𝓝 (U s₀ ψ)) :=
    ((U s₀).continuous.tendsto ψ).comp h0
  refine h1.congr fun t => ?_
  rw [← group_apply_add hU]
  simp
def expDampedOrbit (U : ℝ → H →L[ℂ] H) (ψ : H) (s : ℝ) : H := ((Real.exp (-s) : ℝ) : ℂ) • U s ψ
theorem continuous_expDampedOrbit (hU : IsContinuousUnitaryGroup U) (ψ : H) :
    Continuous (expDampedOrbit U ψ) := by
  unfold expDampedOrbit
  have h1 : Continuous fun s : ℝ => ((Real.exp (-s) : ℝ) : ℂ) := by fun_prop
  exact h1.smul (group_continuous_apply hU ψ)
theorem norm_expDampedOrbit (hU : IsContinuousUnitaryGroup U) (ψ : H) (s : ℝ) :
    ‖expDampedOrbit U ψ s‖ = Real.exp (-s) * ‖ψ‖ := by
  rw [expDampedOrbit, norm_smul, group_norm_apply hU, Complex.norm_real,
    Real.norm_of_nonneg (Real.exp_pos _).le]
theorem integrableOn_expDampedOrbit (hU : IsContinuousUnitaryGroup U) (ψ : H) (c : ℝ) :
    IntegrableOn (expDampedOrbit U ψ) (Ioi c) := by
  refine Integrable.mono' ((integrableOn_exp_neg_Ioi c).mul_const ‖ψ‖)
    (continuous_expDampedOrbit hU ψ).aestronglyMeasurable (ae_of_all _ fun s => ?_)
  exact (norm_expDampedOrbit hU ψ s).le
def resolventVec (U : ℝ → H →L[ℂ] H) (ψ : H) : H := ∫ s in Ioi (0 : ℝ), expDampedOrbit U ψ s
omit [CompleteSpace H] in
theorem expDampedInner_eq (U : ℝ → H →L[ℂ] H) (φ ψ : H) (s : ℝ) :
    expDampedInner U φ ψ s = ⟪φ, expDampedOrbit U ψ s⟫_ℂ := by
  simp [expDampedInner, expDampedOrbit]
theorem integrableOn_expDampedInner (hU : IsContinuousUnitaryGroup U) (φ ψ : H) :
    IntegrableOn (expDampedInner U φ ψ) (Ioi 0) := by
  have h := (integrableOn_expDampedOrbit hU ψ 0).const_inner (𝕜 := ℂ) φ
  exact h.congr (ae_of_all _ fun s => (expDampedInner_eq U φ ψ s).symm)
theorem resolventForm_eq (hU : IsContinuousUnitaryGroup U) (φ ψ : H) :
    resolventForm U φ ψ = ⟪φ, resolventVec U ψ⟫_ℂ := by
  unfold resolventForm resolventVec
  simp_rw [expDampedInner_eq]
  exact integral_inner (integrableOn_expDampedOrbit hU ψ 0) φ
theorem resolventVec_add (hU : IsContinuousUnitaryGroup U) (ψ ψ' : H) :
    resolventVec U (ψ + ψ') = resolventVec U ψ + resolventVec U ψ' := by
  unfold resolventVec
  rw [← integral_add (integrableOn_expDampedOrbit hU ψ 0) (integrableOn_expDampedOrbit hU ψ' 0)]
  simp [expDampedOrbit, smul_add]
omit [CompleteSpace H] in
theorem resolventVec_smul (z : ℂ) (ψ : H) :
    resolventVec U (z • ψ) = z • resolventVec U ψ := by
  unfold resolventVec
  rw [← integral_smul]
  simp only [expDampedOrbit, map_smul]
  simp_rw [smul_comm z]
theorem norm_resolventVec_le (hU : IsContinuousUnitaryGroup U) (ψ : H) :
    ‖resolventVec U ψ‖ ≤ ‖ψ‖ := by
  have h := norm_integral_le_of_norm_le (μ := volume.restrict (Ioi (0 : ℝ)))
    (f := expDampedOrbit U ψ) (g := fun s => Real.exp (-s) * ‖ψ‖)
    ((integrableOn_exp_neg_Ioi 0).mul_const ‖ψ‖)
    (ae_of_all _ fun s => (norm_expDampedOrbit hU ψ s).le)
  rw [integral_mul_const, integral_exp_neg_Ioi_zero, one_mul] at h
  exact h
def resolventMap (hU : IsContinuousUnitaryGroup U) : H →L[ℂ] H :=
  LinearMap.mkContinuous
    { toFun := resolventVec U
      map_add' := resolventVec_add hU
      map_smul' := fun z ψ => resolventVec_smul z ψ } 1
    fun ψ => by simpa using norm_resolventVec_le hU ψ
theorem isResolventOp_resolventMap (hU : IsContinuousUnitaryGroup U) :
    IsResolventOp U (resolventMap hU) := fun φ ψ => (resolventForm_eq hU φ ψ).symm
theorem apply_eq_resolventVec (hU : IsContinuousUnitaryGroup U)
    (hC : IsResolventOp U C) (ψ : H) : C ψ = resolventVec U ψ :=
  ext_inner_left ℂ fun φ => by rw [hC φ ψ, resolventForm_eq hU]
theorem resolventOp_unique (hU : IsContinuousUnitaryGroup U) {C' : H →L[ℂ] H}
    (hC : IsResolventOp U C) (hC' : IsResolventOp U C') : C = C' := by
  ext ψ
  rw [apply_eq_resolventVec hU hC, apply_eq_resolventVec hU hC']
theorem isResolventOp_resolventOp (hU : IsContinuousUnitaryGroup U) :
    IsResolventOp U (resolventOp U) :=
  Classical.epsilon_spec ⟨_, isResolventOp_resolventMap hU⟩
theorem group_apply_resolventVec (hU : IsContinuousUnitaryGroup U) (t : ℝ) (χ : H) :
    U t (resolventVec U χ) = ((Real.exp t : ℝ) : ℂ) • ∫ s in Ioi t, expDampedOrbit U χ s := by
  have h1 : U t (resolventVec U χ) = ∫ s in Ioi (0 : ℝ), U t (expDampedOrbit U χ s) :=
    ((U t).integral_comp_comm (integrableOn_expDampedOrbit hU χ 0)).symm
  have h2 : ∀ s, U t (expDampedOrbit U χ s) =
      ((Real.exp t : ℝ) : ℂ) • expDampedOrbit U χ (s + t) := by
    intro s
    simp only [expDampedOrbit, map_smul, smul_smul]
    rw [add_comm s t, group_apply_add hU t s, ← Complex.ofReal_mul, ← Real.exp_add]
    congr 3
    ring
  have h3 : ∫ s in Ioi (0 : ℝ), expDampedOrbit U χ (s + t) = ∫ s in Ioi t, expDampedOrbit U χ s := by
    have h := (measurePreserving_add_right volume t).setIntegral_preimage_emb
      (measurableEmbedding_addRight t) (expDampedOrbit U χ) (Ioi t)
    have hp : (fun x => x + t) ⁻¹' Ioi t = Ioi (0 : ℝ) := by
      ext x
      simp
    rwa [hp] at h
  rw [h1]
  simp_rw [h2]
  rw [integral_smul, h3]
theorem hasDerivAt_group_resolventVec (hU : IsContinuousUnitaryGroup U) (t : ℝ) (χ : H) :
    HasDerivAt (fun u => U u (resolventVec U χ)) (U t (resolventVec U χ) - U t χ) t := by
  have hG : ∀ u : ℝ, ∫ s in Ioi u, expDampedOrbit U χ s =
      resolventVec U χ - ∫ s in (0 : ℝ)..u, expDampedOrbit U χ s := fun u => by
    rw [← intervalIntegral.integral_Ioi_sub_Ioi' (integrableOn_expDampedOrbit hU χ 0)
      (integrableOn_expDampedOrbit hU χ u)]
    simp [resolventVec]
  have hGd : HasDerivAt (fun u => ∫ s in Ioi u, expDampedOrbit U χ s) (-expDampedOrbit U χ t) t := by
    have h := (((continuous_expDampedOrbit hU χ).integral_hasStrictDerivAt 0 t).hasDerivAt).const_sub
      (resolventVec U χ)
    exact h.congr_of_eventuallyEq (Eventually.of_forall hG)
  have hexp : HasDerivAt (fun u : ℝ => ((Real.exp u : ℝ) : ℂ)) ((Real.exp t : ℝ) : ℂ) t :=
    (Real.hasDerivAt_exp t).ofReal_comp
  have hd := hexp.smul hGd
  refine (hd.congr_of_eventuallyEq
    (Eventually.of_forall fun u => group_apply_resolventVec hU u χ)).congr_deriv ?_
  rw [← group_apply_resolventVec hU t χ, smul_neg]
  have : ((Real.exp t : ℝ) : ℂ) • expDampedOrbit U χ t = U t χ := by
    simp only [expDampedOrbit, smul_smul]
    rw [← Complex.ofReal_mul, ← Real.exp_add]
    simp
  rw [this]
  abel
theorem hasDerivAt_group_resolvent (hU : IsContinuousUnitaryGroup U)
    (hC : IsResolventOp U C) (t : ℝ) (χ : H) :
    HasDerivAt (fun u => U u (C χ)) (U t (C χ - χ)) t := by
  rw [map_sub, apply_eq_resolventVec hU hC]
  exact hasDerivAt_group_resolventVec hU t χ
theorem commute_resolvent (hU : IsContinuousUnitaryGroup U) (hC : IsResolventOp U C)
    {B : H →L[ℂ] H} (hB : ∀ s, Commute B (U s)) : Commute B C := by
  ext χ
  change B (C χ) = C (B χ)
  rw [apply_eq_resolventVec hU hC, apply_eq_resolventVec hU hC]
  unfold resolventVec
  rw [← B.integral_comp_comm (integrableOn_expDampedOrbit hU χ 0)]
  congr 1
  funext s
  have : B (U s χ) = U s (B χ) := congrArg (fun T : H →L[ℂ] H => T χ) (hB s).eq
  simp only [expDampedOrbit, map_smul, this]
theorem group_commute (hU : IsContinuousUnitaryGroup U) (s t : ℝ) :
    Commute (U s) (U t) := by
  change U s * U t = U t * U s
  rw [hU.1.2.2, hU.1.2.2, add_comm]
theorem isContinuousUnitaryGroup_neg (hU : IsContinuousUnitaryGroup U) :
    IsContinuousUnitaryGroup fun s => U (-s) := by
  refine ⟨⟨fun a => hU.1.1 _, by simpa using hU.1.2.1, fun a a' => ?_⟩, fun ψ => ?_⟩
  · change U (-a) * U (-a') = U (-(a + a'))
    rw [hU.1.2.2, neg_add]
  · have h := hU.2 ψ
    have hc : Tendsto (fun t : ℝ => -t) (𝓝 0) (𝓝 0) := by
      have : Continuous fun t : ℝ => -t := by fun_prop
      simpa using this.tendsto 0
    exact h.comp hc
theorem isResolventOp_star (hU : IsContinuousUnitaryGroup U)
    (hC : IsResolventOp U C) : IsResolventOp (fun s => U (-s)) (star C) := by
  intro φ ψ
  rw [inner_star_apply_eq, ← inner_conj_symm, hC ψ φ]
  unfold resolventForm
  rw [← integral_conj]
  congr 1
  funext s
  simp only [expDampedInner, map_mul, Complex.conj_ofReal, inner_conj_symm]
  congr 1
  rw [← group_star hU, inner_star_apply_eq]
theorem inner_resolvent_add_eq_zero (hU : IsContinuousUnitaryGroup U) (hC : IsResolventOp U C)
    (a b : H) : ⟪C a, C b - b⟫_ℂ + ⟪C a - a, C b⟫_ℂ = 0 := by
  have h := (hasDerivAt_group_resolvent hU hC 0 a).inner ℂ (hasDerivAt_group_resolvent hU hC 0 b)
  have hconst : (fun t => ⟪U t (C a), U t (C b)⟫_ℂ) = fun _ => ⟪C a, C b⟫_ℂ :=
    funext fun t => group_inner_apply hU t _ _
  rw [hconst] at h
  have h0 := h.unique (hasDerivAt_const (0 : ℝ) ⟪C a, C b⟫_ℂ)
  simpa only [group_apply_zero hU] using h0
theorem resolvent_star_mul_self (hU : IsContinuousUnitaryGroup U) (hC : IsResolventOp U C) :
    star C * C = (1 / 2 : ℂ) • (C + star C) := by
  ext ψ
  refine ext_inner_left ℂ fun φ => ?_
  have h := inner_resolvent_add_eq_zero hU hC φ ψ
  simp only [inner_sub_left, inner_sub_right] at h
  simp only [mul_apply_eq_comp, smul_apply, add_apply,
    inner_smul_right, inner_add_right, inner_star_apply_eq]
  linear_combination (1 / 2 : ℂ) * h
theorem resolvent_commute_star (hU : IsContinuousUnitaryGroup U) (hC : IsResolventOp U C) :
    Commute C (star C) := by
  refine commute_resolvent (isContinuousUnitaryGroup_neg hU) (isResolventOp_star hU hC) fun s => ?_
  exact (commute_resolvent hU hC fun t => group_commute hU _ _).symm
theorem eq_zero_of_resolvent_eq_zero (hU : IsContinuousUnitaryGroup U)
    (hC : IsResolventOp U C) (ψ : H) (h : C ψ = 0) : ψ = 0 := by
  have hd := hasDerivAt_group_resolvent hU hC 0 ψ
  have hconst : (fun u => U u (C ψ)) = fun _ => (0 : H) := by
    funext u
    rw [h, map_zero]
  rw [hconst] at hd
  have h0 := hd.unique (hasDerivAt_const (0 : ℝ) (0 : H))
  rw [group_apply_zero hU, h, zero_sub, neg_eq_zero] at h0
  exact h0
theorem group_eq_of_resolvent_eq (hU : IsContinuousUnitaryGroup U)
    (hW : IsContinuousUnitaryGroup W) (hC : IsResolventOp U C)
    (hC' : IsResolventOp W C) (hd : DenseRange C) (s : ℝ) : U s = W s := by
  have hstep : ∀ ψ, U s (C ψ) = W s (C ψ) := by
    intro ψ
    have hder : ∀ t, HasDerivAt (fun u => ⟪U u (C ψ), W u (C ψ)⟫_ℂ) 0 t := by
      intro t
      have h := (hasDerivAt_group_resolvent hU hC t ψ).inner ℂ
        (hasDerivAt_group_resolvent hW hC' t ψ)
      have hcu : ∀ χ, U t (C χ) = C (U t χ) := fun χ => congrArg (fun T : H →L[ℂ] H => T χ)
        (commute_resolvent hU hC fun r => group_commute hU t r).eq
      have hcw : ∀ χ, W t (C χ) = C (W t χ) := fun χ => congrArg (fun T : H →L[ℂ] H => T χ)
        (commute_resolvent hW hC' fun r => group_commute hW t r).eq
      have h0 := inner_resolvent_add_eq_zero hU hC (U t ψ) (W t ψ)
      have e : ⟪U t (C ψ), W t (C ψ - ψ)⟫_ℂ + ⟪U t (C ψ - ψ), W t (C ψ)⟫_ℂ = 0 := by
        rw [map_sub, map_sub, hcu, hcw]
        exact h0
      exact h.congr_deriv e
    have hconst : ⟪U s (C ψ), W s (C ψ)⟫_ℂ = ⟪U 0 (C ψ), W 0 (C ψ)⟫_ℂ :=
      is_const_of_deriv_eq_zero (fun t => (hder t).differentiableAt)
        (fun t => (hder t).deriv) s 0
    rw [group_apply_zero hU, group_apply_zero hW, inner_self_eq_norm_sq_to_K] at hconst
    have hre : RCLike.re ⟪U s (C ψ), W s (C ψ)⟫_ℂ = ‖C ψ‖ ^ 2 := by
      rw [hconst]
      simp [← Complex.ofReal_pow]
    have hn := norm_sub_sq (𝕜 := ℂ) (U s (C ψ)) (W s (C ψ))
    rw [hre, group_norm_apply hU, group_norm_apply hW] at hn
    have hz : ‖U s (C ψ) - W s (C ψ)‖ ^ 2 = 0 := by
      rw [hn]
      ring
    exact sub_eq_zero.mp (norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp hz))
  have he : (⇑(U s) : H → H) = ⇑(W s) :=
    hd.equalizer (U s).continuous (W s).continuous (funext hstep)
  exact ContinuousLinearMap.coeFn_injective he
end Group
section Calculus
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
def phaseFn {X : Type*} (q : X → ℝ) (s : ℝ) (y : X) : ℂ :=
  Complex.exp (Complex.I * s * (q y : ℝ))
theorem norm_phaseFn {X : Type*} (q : X → ℝ) (s : ℝ) (y : X) : ‖phaseFn q s y‖ = 1 := by
  have : Complex.I * s * (q y : ℝ) = ((s * q y : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [phaseFn, this, Complex.norm_exp_ofReal_mul_I]
theorem measurable_phaseFn {X : Type*} [MeasurableSpace X] {q : X → ℝ} (hq : Measurable q)
    (s : ℝ) : Measurable (phaseFn q s) :=
  Complex.measurable_exp.comp (measurable_const.mul (Complex.measurable_ofReal.comp hq))
theorem isBoundedFn_phaseFn {X : Type*} (q : X → ℝ) (s : ℝ) :
    IsBoundedFn (phaseFn q s) := ⟨1, fun y => (norm_phaseFn q s y).le⟩
theorem phaseFn_add {X : Type*} (q : X → ℝ) (a b : ℝ) :
    phaseFn q (a + b) = phaseFn q a * phaseFn q b := by
  funext y
  simp only [phaseFn, Pi.mul_apply, ← Complex.exp_add]
  congr 1
  push_cast
  ring
theorem phaseFn_zero {X : Type*} (q : X → ℝ) : phaseFn q 0 = fun _ => 1 := by
  funext y
  simp [phaseFn]
theorem continuous_phaseFn_time {X : Type*} (q : X → ℝ) (y : X) :
    Continuous fun s : ℝ => phaseFn q s y := by
  unfold phaseFn
  fun_prop
theorem norm_inv_one_sub_I_mul_le (x : ℝ) : ‖(1 - Complex.I * (x : ℝ))⁻¹‖ ≤ 1 := by
  rw [norm_inv]
  refine inv_le_one_of_one_le₀ ?_
  have h := Complex.abs_re_le_norm (1 - Complex.I * (x : ℝ))
  simpa using h
variable {n : ℕ} {Y : Set (Fin n → ℝ)} {E : SpectralMeasure Y H}
theorem measurable_inv_one_sub_I_mul {q : Y → ℝ} (hq : Measurable q) :
    Measurable fun y => (1 - Complex.I * (q y : ℝ))⁻¹ :=
  (measurable_const.sub (measurable_const.mul (Complex.measurable_ofReal.comp hq))).inv
theorem isBoundedFn_inv_one_sub_I_mul (q : Y → ℝ) :
    IsBoundedFn fun y => (1 - Complex.I * (q y : ℝ))⁻¹ :=
  ⟨1, fun y => norm_inv_one_sub_I_mul_le (q y)⟩
theorem isDiagonalIntegral_integralOp (hc : BoundedFunctionalCalculus E) {g : Y → ℂ}
    (hg : Measurable g) (hb : IsBoundedFn g) : E.IsDiagonalIntegral g (E.integralOp g) :=
  Classical.epsilon_spec (hc.existsUnique_op g hg hb).exists
theorem integralOp_one (hc : BoundedFunctionalCalculus E) : E.integralOp (fun _ => 1) = 1 := by
  have h := hc.indicator ⟨univ, MeasurableSet.univ⟩
  rw [E.map_univ, indicator_univ] at h
  exact h
theorem isCarriedBy_univ (hc : BoundedFunctionalCalculus E) :
    E.IsCarriedBy ⟨univ, MeasurableSet.univ⟩ := by apply _root_.YangMills.Construction.EuclideanSpectral.FunctionalCalculus.isCarriedBy_univ <;> assumption
omit [CompleteSpace H] in
theorem ext_of_inner_self_apply {A B : H →L[ℂ] H} (h : ∀ ψ, ⟪ψ, A ψ⟫_ℂ = ⟪ψ, B ψ⟫_ℂ) : A = B := by apply _root_.YangMills.Construction.BorelCalculus.OfSpectralMeasure.ext_of_inner_self <;> assumption
theorem integralOp_congr (hu : UnboundedFunctionalCalculus E) {g h : Y → ℂ} (hg : Measurable g)
    (hgb : IsBoundedFn g) (hh : Measurable h) (hhb : IsBoundedFn h) (Δ₀ : BorelSubsets Y)
    (hΔ : E.IsCarriedBy Δ₀) (he : ∀ y ∈ Δ₀.1, g y = h y) :
    E.integralOp g = E.integralOp h := by
  obtain ⟨cg, hcg⟩ := hgb
  obtain ⟨ch, hch⟩ := hhb
  ext ψ
  have hv := (hu.congr g h hg hh Δ₀ hΔ he).2 ψ (by rw [E.integralDom_eq_univ hcg]; trivial)
  rwa [E.integralApply_eq_integralOp hcg, E.integralApply_eq_integralOp hch] at hv
theorem isContinuousUnitaryGroup_phases (hc : BoundedFunctionalCalculus E)
    (hs : StrongConvergence E) {q : Y → ℝ} (hq : Measurable q) :
    IsContinuousUnitaryGroup fun s => E.integralOp (phaseFn q s) := by
  refine ⟨⟨fun a => hc.isUnitary _ (measurable_phaseFn hq a) (norm_phaseFn q a), ?_, fun a a' => ?_⟩,
    fun ψ => ?_⟩
  · change E.integralOp (phaseFn q 0) = 1
    rw [phaseFn_zero, integralOp_one hc]
  · change E.integralOp (phaseFn q a) * E.integralOp (phaseFn q a') =
      E.integralOp (phaseFn q (a + a'))
    rw [phaseFn_add, hc.mul _ _ (measurable_phaseFn hq a) (isBoundedFn_phaseFn q a)
      (measurable_phaseFn hq a') (isBoundedFn_phaseFn q a')]
  · refine tendsto_of_seq_tendsto fun u hu => ?_
    have h := (hs (fun r => phaseFn q (u r)) (fun _ => 1) 1 ⟨univ, MeasurableSet.univ⟩
      (fun r => measurable_phaseFn hq _) measurable_const (fun r y => (norm_phaseFn q _ y).le)
      (isCarriedBy_univ hc) (fun y _ => ?_)).2 ψ
    · rw [E.integralApply_eq_integralOp (c := 1) (fun _ => by simp), integralOp_one hc] at h
      exact h
    · have h0 := ((continuous_phaseFn_time q y).tendsto 0).comp hu
      rw [phaseFn_zero] at h0
      exact h0
theorem resolvent_eq_of_phases {U : ℝ → H →L[ℂ] H} {C : H →L[ℂ] H}
    (hc : BoundedFunctionalCalculus E) (hC : IsResolventOp U C) {q : Y → ℝ} (hq : Measurable q)
    (h : ∀ s : ℝ, 0 ≤ s → U s = E.integralOp (phaseFn q s)) :
    C = E.integralOp fun y => (1 - Complex.I * (q y : ℝ))⁻¹ := by
  refine ext_of_inner_self_apply fun ψ => ?_
  rw [isDiagonalIntegral_integralOp hc (measurable_inv_one_sub_I_mul hq)
    (isBoundedFn_inv_one_sub_I_mul q) ψ, hC ψ ψ]
  set μ := E.diagMeasure ψ
  let f : ℝ → Y → ℂ := fun s y => ((Real.exp (-s) : ℝ) : ℂ) * phaseFn q s y
  have h1 : resolventForm U ψ ψ = ∫ s in Ioi (0 : ℝ), ∫ y, f s y ∂μ := by
    refine setIntegral_congr_fun measurableSet_Ioi fun s hs => ?_
    have hd := isDiagonalIntegral_integralOp hc (measurable_phaseFn hq s)
      (isBoundedFn_phaseFn q s) ψ
    simp only [expDampedInner, f]
    rw [h s (le_of_lt hs), hd, integral_const_mul]
  have hmeas : Measurable (Function.uncurry f) := by
    have h1 : Measurable fun p : ℝ × Y => ((Real.exp (-p.1) : ℝ) : ℂ) :=
      Complex.measurable_ofReal.comp (Real.measurable_exp.comp measurable_fst.neg)
    have h2 : Measurable fun p : ℝ × Y => phaseFn q p.1 p.2 :=
      Complex.measurable_exp.comp ((measurable_const.mul
        (Complex.measurable_ofReal.comp measurable_fst)).mul
        (Complex.measurable_ofReal.comp (hq.comp measurable_snd)))
    exact h1.mul h2
  have hint : Integrable (Function.uncurry f) ((volume.restrict (Ioi (0 : ℝ))).prod μ) := by
    refine Integrable.mono' ((integrableOn_exp_neg_Ioi 0).comp_fst μ)
      hmeas.aestronglyMeasurable (ae_of_all _ fun p => ?_)
    simp only [Function.uncurry, f, norm_mul, norm_phaseFn, mul_one, Complex.norm_real]
    exact (Real.norm_of_nonneg (Real.exp_pos _).le).le
  rw [h1, integral_integral_swap hint]
  refine integral_congr_ae (ae_of_all _ fun y => ?_)
  have hre : (-1 + Complex.I * (q y : ℝ)).re < 0 := by simp
  have he : ∀ s : ℝ, f s y = Complex.exp ((-1 + Complex.I * (q y : ℝ)) * s) := fun s => by
    simp only [f, phaseFn]
    rw [Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  simp only [he]
  rw [integral_exp_mul_complex_Ioi hre 0]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
  rw [show -1 + Complex.I * (q y : ℝ) = -(1 - Complex.I * (q y : ℝ)) by ring, neg_div_neg_eq,
    one_div]
theorem isBoundedFn_add {X : Type*} {g h : X → ℂ} (hg : IsBoundedFn g)
    (hh : IsBoundedFn h) : IsBoundedFn (g + h) := by apply _root_.YangMills.Construction.SpectralTheorem.isBoundedFn_add <;> assumption
theorem isBoundedFn_mul {X : Type*} {g h : X → ℂ} (hg : IsBoundedFn g)
    (hh : IsBoundedFn h) : IsBoundedFn (g * h) := by apply _root_.YangMills.Construction.SpectralTheorem.isBoundedFn_mul <;> assumption
theorem isBoundedFn_smul {X : Type*} (z : ℂ) {g : X → ℂ} (hg : IsBoundedFn g) :
    IsBoundedFn (z • g) := by
  obtain ⟨a, ha⟩ := hg
  refine ⟨‖z‖ * a, fun x => ?_⟩
  rw [Pi.smul_apply, norm_smul]
  exact mul_le_mul_of_nonneg_left (ha x) (norm_nonneg _)
theorem isBoundedFn_conjFn {X : Type*} {g : X → ℂ} (hg : IsBoundedFn g) :
    IsBoundedFn (conjFn g) := by apply _root_.YangMills.Construction.SpectralTheorem.isBoundedFn_conjFn <;> assumption
theorem measurable_conjFn {X : Type*} [MeasurableSpace X] {g : X → ℂ} (hg : Measurable g) :
    Measurable (conjFn g) :=
  Complex.continuous_conj.measurable.comp hg
def circleDeviation {X : Type*} (ζ : X → ℂ) : X → ℂ :=
  conjFn ζ * ζ + (-(1 / 2) : ℂ) • (ζ + conjFn ζ)
theorem circleDeviation_apply {X : Type*} (ζ : X → ℂ) (y : X) :
    circleDeviation ζ y = ((‖ζ y‖ ^ 2 - (ζ y).re : ℝ) : ℂ) := by
  simp only [circleDeviation, conjFn, Pi.add_apply, Pi.mul_apply, Pi.smul_apply,
    smul_eq_mul, Complex.conj_mul', Complex.add_conj]
  push_cast
  ring
theorem inv_one_sub_I_mul_ratio {z : ℂ} (h0 : z ≠ 0) (h1 : ‖z‖ ^ 2 = z.re) :
    (1 - Complex.I * ((z.im / z.re : ℝ) : ℂ))⁻¹ = z := by
  have hn : z.re * z.re + z.im * z.im = z.re := by
    rw [← Complex.normSq_apply, Complex.normSq_eq_norm_sq, h1]
  have hr : z.re ≠ 0 := fun hr => h0 (by
    rw [hr] at h1
    exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h1))
  symm
  apply eq_inv_of_mul_eq_one_left
  apply Complex.ext
  · simp only [Complex.mul_re, Complex.sub_re, Complex.one_re, Complex.mul_im, Complex.I_re,
      Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, Complex.sub_im, Complex.one_im]
    field_simp
    nlinarith
  · simp only [Complex.mul_re, Complex.sub_re, Complex.one_re, Complex.mul_im, Complex.I_re,
      Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, Complex.sub_im, Complex.one_im]
    field_simp
    ring
theorem isCarriedBy_circleSupport {U : ℝ → H →L[ℂ] H} {C : H →L[ℂ] H}
    (hU : IsContinuousUnitaryGroup U) (hC : IsResolventOp U C)
    (hc : BoundedFunctionalCalculus E) (hk : KernelAndPositivity E) {ζ : Y → ℂ}
    (hζ : Measurable ζ) (hb : IsBoundedFn ζ) (hCE : C = E.integralOp ζ) :
    E.IsCarriedBy (circleSupport ζ hζ) := by
  have hζc := measurable_conjFn hζ
  have hbc := isBoundedFn_conjFn hb
  have hgm : Measurable (circleDeviation ζ) :=
    (hζc.mul hζ).add (((hζ.add hζc).const_smul _))
  have hgb : IsBoundedFn (circleDeviation ζ) :=
    isBoundedFn_add (isBoundedFn_mul hbc hb)
      (isBoundedFn_smul _ (isBoundedFn_add hb hbc))
  have hzero : E.integralOp (circleDeviation ζ) = 0 := by
    have h1 : E.integralOp (circleDeviation ζ) =
        E.integralOp (conjFn ζ) * E.integralOp ζ +
          (-(1 / 2) : ℂ) • (E.integralOp ζ + E.integralOp (conjFn ζ)) := by
      unfold circleDeviation
      rw [hc.add _ _ (hζc.mul hζ) (isBoundedFn_mul hbc hb) ((hζ.add hζc).const_smul _)
        (isBoundedFn_smul _ (isBoundedFn_add hb hbc)),
        hc.mul _ _ hζc hbc hζ hb, hc.smul _ _ (hζ.add hζc) (isBoundedFn_add hb hbc),
        hc.add _ _ hζ hb hζc hbc]
    rw [h1, hc.star_eq ζ hζ hb, ← hCE, resolvent_star_mul_self hU hC]
    simp only [smul_add, neg_smul]
    abel
  obtain ⟨cg, hcg⟩ := hgb
  have hN : E (nonzeroLocus hgm) = 0 := (hk.eq_zero_iff _ hgm).mp fun ψ _ => by
    rw [E.integralApply_eq_integralOp hcg, hzero]
    rfl
  obtain ⟨cz, hcz⟩ := hb
  have hZ : E (zeroLocus hζ) = 0 := by
    ext ψ
    have hmem : E (zeroLocus hζ) ψ ∈ Set.range (E (zeroLocus hζ)) := ⟨ψ, rfl⟩
    rw [← hk.kernel_eq ζ hζ] at hmem
    have h0 := hmem.2
    rw [E.integralApply_eq_integralOp hcz, ← hCE] at h0
    simpa using eq_zero_of_resolvent_eq_zero hU hC _ h0
  have hU' := hc.apply_iUnion Bool (fun b => cond b (zeroLocus hζ) (nonzeroLocus hgm)) (fun b => by
    cases b
    · exact hN
    · exact hZ)
  refine hc.apply_subset _ _ hU' fun y hy => ?_
  simp only [mem_iUnion]
  by_cases hy0 : ζ y = 0
  · exact ⟨true, hy0⟩
  · refine ⟨false, fun hg => hy ⟨hy0, ?_⟩⟩
    have h1 := circleDeviation_apply ζ y
    rw [show circleDeviation ζ y = 0 from hg] at h1
    have h2 : ‖ζ y‖ ^ 2 - (ζ y).re = 0 := by exact_mod_cast h1.symm
    linarith
theorem group_eq_integralOp_phases {U : ℝ → H →L[ℂ] H} {C : H →L[ℂ] H}
    (hU : IsContinuousUnitaryGroup U) (hC : IsResolventOp U C) (hd : DenseRange C)
    (hc : BoundedFunctionalCalculus E) (hs : StrongConvergence E)
    (hu : UnboundedFunctionalCalculus E) (hk : KernelAndPositivity E)
    {ζ : Y → ℂ} (hζ : Measurable ζ) (hb : IsBoundedFn ζ) (hCE : C = E.integralOp ζ)
    (s : ℝ) : U s = E.integralOp (phaseFn (fun y => (ζ y).im / (ζ y).re) s) := by
  have hq : Measurable fun y => (ζ y).im / (ζ y).re :=
    (Complex.measurable_im.comp hζ).div (Complex.measurable_re.comp hζ)
  have hW := isContinuousUnitaryGroup_phases hc hs hq
  have hcar := isCarriedBy_circleSupport hU hC hc hk hζ hb hCE
  have hCW : IsResolventOp (fun s => E.integralOp (phaseFn (fun y => (ζ y).im / (ζ y).re) s))
      C := by
    have h1 := resolvent_eq_of_phases hc (isResolventOp_resolventMap hW) hq fun _ _ => rfl
    have h2 := integralOp_congr hu (measurable_inv_one_sub_I_mul hq)
      (isBoundedFn_inv_one_sub_I_mul _) hζ hb _ hcar fun y hy => inv_one_sub_I_mul_ratio hy.1 hy.2
    rw [h2, ← hCE] at h1
    rw [← h1]
    exact isResolventOp_resolventMap hW
  exact group_eq_of_resolvent_eq hU hW hC hCW hd s
end Calculus
section Measures
theorem inv_one_sub_I_mul_eq (x : ℝ) :
    (1 - Complex.I * (x : ℝ))⁻¹ =
      (((1 + x ^ 2)⁻¹ : ℝ) : ℂ) + Complex.I * ((x * (1 + x ^ 2)⁻¹ : ℝ) : ℂ) := by
  have hD : ((1 : ℂ) + (x : ℂ) ^ 2) ≠ 0 := by
    have : (1 : ℝ) + x ^ 2 ≠ 0 := by positivity
    exact_mod_cast this
  symm
  apply eq_inv_of_mul_eq_one_right
  push_cast
  field_simp
  linear_combination (-(x : ℂ) ^ 2) * Complex.I_sq
def cayleyCoords {n : ℕ} (y : Fin n → ℝ) : Fin (n + n) → ℝ :=
  Fin.addCases (fun i => (1 + y i ^ 2)⁻¹) (fun i => y i * (1 + y i ^ 2)⁻¹)
open scoped Classical in
def invCayleyCoords {n : ℕ} (u : Fin (n + n) → ℝ) (i : Fin n) : ℝ :=
  if u (Fin.castAdd n i) = 0 then 0 else u (Fin.natAdd n i) / u (Fin.castAdd n i)
theorem invCayleyCoords_cayleyCoords {n : ℕ} (y : Fin n → ℝ) :
    invCayleyCoords (cayleyCoords y) = y := by
  funext i
  have h : (1 + y i ^ 2)⁻¹ ≠ 0 := by positivity
  simp only [invCayleyCoords, cayleyCoords, Fin.addCases_left, Fin.addCases_right,
    h, if_false]
  field_simp
theorem measurable_invCayleyCoords {n : ℕ} :
    Measurable (invCayleyCoords (n := n)) := by
  refine measurable_pi_iff.mpr fun i => ?_
  unfold invCayleyCoords
  exact Measurable.ite (measurableSet_eq_fun (measurable_pi_apply _) measurable_const)
    measurable_const ((measurable_pi_apply _).div (measurable_pi_apply _))
theorem measurable_cayleyCoords {n : ℕ} :
    Measurable (cayleyCoords (n := n)) := by
  refine measurable_pi_iff.mpr fun j => ?_
  induction j using Fin.addCases with
  | left i =>
    simp only [cayleyCoords, Fin.addCases_left]
    exact (measurable_const.add ((measurable_pi_apply i).pow_const 2)).inv
  | right i =>
    simp only [cayleyCoords, Fin.addCases_right]
    exact (measurable_pi_apply i).mul
      (measurable_const.add ((measurable_pi_apply i).pow_const 2)).inv
theorem norm_cayleyCoords_le {n : ℕ} (y : Fin n → ℝ) : ‖cayleyCoords y‖ ≤ 1 := by
  refine (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun j => ?_
  induction j using Fin.addCases with
  | left i =>
    simp only [cayleyCoords, Fin.addCases_left]
    rw [Real.norm_of_nonneg (by positivity)]
    exact inv_le_one_of_one_le₀ (by nlinarith [sq_nonneg (y i)])
  | right i =>
    simp only [cayleyCoords, Fin.addCases_right]
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (show (0 : ℝ) < (1 + y i ^ 2)⁻¹ by positivity),
      ← div_eq_mul_inv, div_le_one (by positivity)]
    nlinarith [sq_nonneg (|y i| - 1), sq_abs (y i)]
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
theorem spectralMeasure_eq_of_phases (h₂ : BorelCalculusTheorem)
    (h₃ : JointSpectralTheorem) {n : ℕ}
    (E E' : SpectralMeasure (FullSpace n) H)
    (h : ∀ (s : ℝ) (i : Fin n), 0 ≤ s →
      E.integralOp (fun y => Complex.exp (Complex.I * s * (y.1 i : ℝ))) =
        E'.integralOp fun y => Complex.exp (Complex.I * s * (y.1 i : ℝ))) : E = E' := by
  obtain ⟨hc, hs, -, -, -, -, -⟩ := (h₂ H n).1 _ E
  obtain ⟨hc', hs', -, -, -, -, -⟩ := (h₂ H n).1 _ E'
  have hn : 1 ≤ n + n := by
    have := E.one_le_dimension
    omega
  have hr : ∀ i : Fin n, E.integralOp (fun y => (1 - Complex.I * (y.1 i : ℝ))⁻¹) =
      E'.integralOp fun y => (1 - Complex.I * (y.1 i : ℝ))⁻¹ := by
    intro i
    have hq : Measurable fun y : FullSpace n => y.1 i :=
      (measurable_pi_apply i).comp measurable_subtype_coe
    have hW := isContinuousUnitaryGroup_phases hc hs hq
    have hW' := isContinuousUnitaryGroup_phases hc' hs' hq
    have h1 := resolvent_eq_of_phases hc (isResolventOp_resolventMap hW) hq fun _ _ => rfl
    have hL : IsResolventOp (fun s => E'.integralOp (phaseFn (fun y : FullSpace n => y.1 i) s))
        (resolventMap hW) := by
      intro φ ψ
      rw [isResolventOp_resolventMap hW φ ψ]
      refine setIntegral_congr_fun measurableSet_Ioi fun s hs₀ => ?_
      have := h s i (le_of_lt hs₀)
      simp only [expDampedInner]
      congr 3
    have h2 := resolvent_eq_of_phases hc' hL hq fun _ _ => rfl
    exact h1.symm.trans h2
  have hmr : ∀ i : Fin n, Measurable fun y : FullSpace n => (1 - Complex.I * (y.1 i : ℝ))⁻¹ :=
    fun i => measurable_inv_one_sub_I_mul ((measurable_pi_apply i).comp measurable_subtype_coe)
  have hbr : ∀ i : Fin n, IsBoundedFn fun y : FullSpace n => (1 - Complex.I * (y.1 i : ℝ))⁻¹ :=
    fun i => isBoundedFn_inv_one_sub_I_mul _
  have hcomb : ∀ (i : Fin n) (a b : ℂ),
      E.integralOp (a • (fun y : FullSpace n => (1 - Complex.I * (y.1 i : ℝ))⁻¹) +
        b • conjFn fun y : FullSpace n => (1 - Complex.I * (y.1 i : ℝ))⁻¹) =
      E'.integralOp (a • (fun y : FullSpace n => (1 - Complex.I * (y.1 i : ℝ))⁻¹) +
        b • conjFn fun y : FullSpace n => (1 - Complex.I * (y.1 i : ℝ))⁻¹) := by
    intro i a b
    have hm := hmr i
    have hb := hbr i
    have hmc := measurable_conjFn hm
    have hbc := isBoundedFn_conjFn hb
    rw [hc.add _ _ (hm.const_smul a) (isBoundedFn_smul a hb) (hmc.const_smul b)
        (isBoundedFn_smul b hbc),
      hc'.add _ _ (hm.const_smul a) (isBoundedFn_smul a hb) (hmc.const_smul b)
        (isBoundedFn_smul b hbc),
      hc.smul a _ hm hb, hc'.smul a _ hm hb, hc.smul b _ hmc hbc, hc'.smul b _ hmc hbc,
      hc.star_eq _ hm hb, hc'.star_eq _ hm hb, hr i]
  refine (h₃ H (n + n) hn).2 n _ E E' (fun y => cayleyCoords y.1)
    (fun u => ⟨invCayleyCoords u, mem_univ _⟩)
    (measurable_cayleyCoords.comp measurable_subtype_coe) ⟨1, fun y =>
      norm_cayleyCoords_le y.1⟩
    (measurable_invCayleyCoords.subtype_mk)
    (fun y => Subtype.ext (invCayleyCoords_cayleyCoords y.1)) fun j => ?_
  induction j using Fin.addCases with
  | left i =>
    have hf : (fun y : FullSpace n => ((cayleyCoords y.1 (Fin.castAdd n i) : ℝ) : ℂ)) =
        (1 / 2 : ℂ) • (fun y : FullSpace n => (1 - Complex.I * (y.1 i : ℝ))⁻¹) +
          (1 / 2 : ℂ) • conjFn fun y : FullSpace n => (1 - Complex.I * (y.1 i : ℝ))⁻¹ := by
      funext y
      simp only [cayleyCoords, Fin.addCases_left, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
        conjFn, inv_one_sub_I_mul_eq]
      simp only [map_add, map_mul, Complex.conj_I, Complex.conj_ofReal]
      ring
    rw [hf]
    exact hcomb i _ _
  | right i =>
    have hf : (fun y : FullSpace n => ((cayleyCoords y.1 (Fin.natAdd n i) : ℝ) : ℂ)) =
        (1 / (2 * Complex.I) : ℂ) • (fun y : FullSpace n => (1 - Complex.I * (y.1 i : ℝ))⁻¹) +
          (-(1 / (2 * Complex.I)) : ℂ) •
            conjFn fun y : FullSpace n => (1 - Complex.I * (y.1 i : ℝ))⁻¹ := by
      funext y
      simp only [cayleyCoords, Fin.addCases_right, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
        conjFn, inv_one_sub_I_mul_eq]
      simp only [map_add, map_mul, Complex.conj_I, Complex.conj_ofReal]
      field_simp
      ring
    rw [hf]
    exact hcomb i _ _
end Measures
section Generator
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
theorem denseRange_resolvent (h₁ : HilbertSpaceFacts.Facts) {U : ℝ → H →L[ℂ] H}
    {C : H →L[ℂ] H} (hU : IsContinuousUnitaryGroup U) (hC : IsResolventOp U C) :
    DenseRange C := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hN, -, -⟩ := h₁
  have hd := (hN H C (resolvent_commute_star hU hC).eq.symm).2 (by
    refine (Submodule.eq_bot_iff _).mpr fun ψ hψ => ?_
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hψ
    exact eq_zero_of_resolvent_eq_zero hU hC _ hx)
  have he : HilbertSpaceBasics.opRange (ofBounded C) = Set.range C := by
    ext χ
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x.1, rfl⟩
    · rintro ⟨x, rfl⟩
      exact ⟨⟨x, Submodule.mem_top⟩, rfl⟩
  rw [he] at hd
  exact hd
theorem le_of_isGE {A B : H →L[ℂ] H} (h : IsGE A B) : B ≤ A := by apply _root_.YangMills.Construction.SemigroupRepresentation.le_of_isGE <;> assumption
theorem isSelfAdjoint_realPartOp (C : H →L[ℂ] H) : IsSelfAdjoint (realPartOp C) := by apply _root_.YangMills.Construction.SemigroupRepresentation.isSelfAdjoint_realPartOp <;> assumption
theorem isSelfAdjoint_imagPartOp (C : H →L[ℂ] H) : IsSelfAdjoint (imagPartOp C) := by apply _root_.YangMills.Construction.SemigroupRepresentation.isSelfAdjoint_imagPartOp <;> assumption
theorem norm_realPartOp_le {C : H →L[ℂ] H} (h : ‖C‖ ≤ 1) : ‖realPartOp C‖ ≤ 1 := by apply _root_.YangMills.Construction.SemigroupRepresentation.norm_realPartOp_le_one <;> assumption
theorem norm_imagPartOp_le {C : H →L[ℂ] H} (h : ‖C‖ ≤ 1) : ‖imagPartOp C‖ ≤ 1 := by apply _root_.YangMills.Construction.SemigroupRepresentation.norm_imagPartOp_le_one <;> assumption
theorem realPartOp_add_I_smul_imagPartOp (C : H →L[ℂ] H) :
    realPartOp C + Complex.I • imagPartOp C = C := by apply _root_.YangMills.Construction.SemigroupRepresentation.realPartOp_add_I_smul_imagPartOp <;> assumption
theorem commute_realPartOp_imagPartOp {C : H →L[ℂ] H} (h : Commute C (star C)) :
    Commute (realPartOp C) (imagPartOp C) := by
  unfold realPartOp imagPartOp
  refine Commute.smul_left (Commute.smul_right ?_ _) _
  exact Commute.add_left ((Commute.refl C).sub_right h) (h.symm.sub_right (Commute.refl _))
theorem commute_realPartOp {B C : H →L[ℂ] H} (h : Commute B C) (h' : Commute B (star C)) :
    Commute B (realPartOp C) :=
  (h.add_right h').smul_right _
theorem commute_imagPartOp {B C : H →L[ℂ] H} (h : Commute B C) (h' : Commute B (star C)) :
    Commute B (imagPartOp C) :=
  (h.sub_right h').smul_right _
theorem isCommutingInBox_parts (h₁ : HilbertSpaceFacts.Facts) {C : H →L[ℂ] H}
    (hcomm : Commute C (star C)) (hn : ‖C‖ ≤ 1) :
    IsCommutingInBox (![realPartOp C, imagPartOp C] : Fin 2 → H →L[ℂ] H)
      (fun _ => -1) (fun _ => 1) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hB, -, -, -, -, -⟩ := h₁
  have hp := commute_realPartOp_imagPartOp hcomm
  have hsa : ∀ i, IsSelfAdjoint ((![realPartOp C, imagPartOp C] : Fin 2 → H →L[ℂ] H) i) :=
    Fin.forall_fin_two.mpr ⟨isSelfAdjoint_realPartOp C, isSelfAdjoint_imagPartOp C⟩
  have hnorm : ∀ i, ‖(![realPartOp C, imagPartOp C] : Fin 2 → H →L[ℂ] H) i‖ ≤ 1 :=
    Fin.forall_fin_two.mpr ⟨norm_realPartOp_le hn, norm_imagPartOp_le hn⟩
  refine ⟨hsa, Fin.forall_fin_two.mpr ⟨Fin.forall_fin_two.mpr ⟨Commute.refl _, hp⟩,
    Fin.forall_fin_two.mpr ⟨hp.symm, Commute.refl _⟩⟩, fun _ => by norm_num, fun i => ?_,
    fun i => ?_⟩
  · have := (hB H _ 1 (hsa i) (hnorm i)).1
    exact le_of_isGE (by simpa using this)
  · have := (hB H _ 1 (hsa i) (hnorm i)).2
    exact le_of_isGE (by simpa using this)
theorem norm_resolventMap_le {U : ℝ → H →L[ℂ] H} (hU : IsContinuousUnitaryGroup U) :
    ‖resolventMap hU‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun ψ => by
    rw [one_mul]
    exact norm_resolventVec_le hU ψ
variable {n : ℕ} {Y : Set (Fin n → ℝ)} {E : SpectralMeasure Y H}
theorem isSpectralIntegralOf_spectralIntegralOp (hu : UnboundedFunctionalCalculus E)
    {g : Y → ℂ} (hg : Measurable g) : IsSpectralIntegralOf (spectralIntegralOp E g) E g := by
  obtain ⟨A, -, hA⟩ := hu.exists_op g hg
  refine Classical.epsilon_spec (p := fun A => IsSpectralIntegralOf A E g) ⟨A, fun ψ => ?_, hA.2⟩
  rw [← hA.1]
  exact Iff.rfl
theorem hasDomainAndAction_of_isSpectralIntegralOf {A : UnboundedOp H} {g : Y → ℂ}
    (h : IsSpectralIntegralOf A E g) :
    HasDomainAndAction A (E.integralDom g) (E.integralApply g) :=
  ⟨Set.ext h.1, h.2⟩
theorem expI_eq_integralOp_phaseFn (h₄ : SpectralTheoremHolds)
    {P : UnboundedOp H}
    (hP : IsSelfAdjointOp P) {q : Y → ℝ} (hq : Measurable q)
    (hI : IsSpectralIntegralOf P E fun y => ((q y : ℝ) : ℂ)) (s : ℝ) :
    expI P s = E.integralOp (phaseFn q s) := by
  obtain ⟨-, -, -, -, -, -, hcc, -, -⟩ := h₄ H P hP
  have hm : Measurable fun x : ℝ => Complex.exp (Complex.I * s * (x : ℝ)) := by fun_prop
  have h := ((hcc n Y E q hq hI).2 _ hm).2
  ext ψ
  have hb₁ : ∀ y : RealLineSet, ‖Complex.exp (Complex.I * s * ((y.1 0 : ℝ) : ℂ))‖ ≤ 1 :=
    fun y => (norm_phaseFn (fun y : RealLineSet => y.1 0) s y).le
  have hb₂ : ∀ y, ‖phaseFn q s y‖ ≤ 1 := fun y => (norm_phaseFn q s y).le
  have hv := h ψ (by rw [(spectralMeasure P).integralDom_eq_univ hb₁]; trivial)
  rw [(spectralMeasure P).integralApply_eq_integralOp hb₁] at hv
  exact hv.trans (E.integralApply_eq_integralOp hb₂ ψ)
theorem exists_stoneGenerator (h₁ : HilbertSpaceFacts.Facts)
    (h₂ : BorelCalculusTheorem)
    (h₃ : JointSpectralTheorem)
    (h₄ : SpectralTheoremHolds) {U : ℝ → H →L[ℂ] H}
    (hU : IsContinuousUnitaryGroup U) :
    ∃ P : UnboundedOp H, IsStoneGenerator P U ∧ ∀ B : H →L[ℂ] H, (∀ s, Commute B (U s)) →
      ∀ Δ : BorelSubsets ℝ, Commute B (spectralMeasure P (realLineSet Δ)) := by
  have hC := isResolventOp_resolventMap hU
  set C := resolventMap hU with hCdef
  have hcomm := resolvent_commute_star hU hC
  have hbox := isCommutingInBox_parts h₁ hcomm (norm_resolventMap_le hU)
  have hn2 : 1 ≤ 2 := by norm_num
  obtain ⟨-, hRep, -, hFc⟩ := (h₃ H 2 hn2).1 _ _ _ hbox
  set F := jointMeasure hn2 (![realPartOp C, imagPartOp C] : Fin 2 → H →L[ℂ] H) (fun _ => -1)
    (fun _ => 1) hbox.lt with hF
  obtain ⟨hc, hs, -, hu, hk, -, -⟩ := (h₂ H 2).1 _ F
  have hcm : ∀ i : Fin 2, Measurable (coordFn (Y := closedBox (fun _ => -1) (fun _ => 1)) i) :=
    fun i => Complex.measurable_ofReal.comp ((measurable_pi_apply i).comp measurable_subtype_coe)
  have hcb : ∀ i : Fin 2, IsBoundedFn
      (coordFn (Y := closedBox (fun _ => -1) (fun _ => 1)) i) := fun i => ⟨1, fun y => by
    have hy := y.2 i (mem_univ _)
    rw [coordFn, Complex.norm_real, Real.norm_eq_abs]
    exact abs_le.mpr hy⟩
  have hζ : Measurable (coordFn 0 + Complex.I • coordFn 1 :
      closedBox (fun _ : Fin 2 => (-1 : ℝ)) (fun _ => 1) → ℂ) :=
    (hcm 0).add ((hcm 1).const_smul _)
  have hb : IsBoundedFn (coordFn 0 + Complex.I • coordFn 1 :
      closedBox (fun _ : Fin 2 => (-1 : ℝ)) (fun _ => 1) → ℂ) :=
    isBoundedFn_add (hcb 0) (isBoundedFn_smul _ (hcb 1))
  have hCF : C = F.integralOp (coordFn 0 + Complex.I • coordFn 1) := by
    rw [hc.add _ _ (hcm 0) (hcb 0) ((hcm 1).const_smul _) (isBoundedFn_smul _ (hcb 1)),
      hc.smul _ _ (hcm 1) (hcb 1), ← hRep 0, ← hRep 1]
    exact (realPartOp_add_I_smul_imagPartOp C).symm
  have hd := denseRange_resolvent h₁ hU hC
  have hgroup := group_eq_integralOp_phases hU hC hd hc hs hu hk hζ hb hCF
  set ζ : closedBox (fun _ : Fin 2 => (-1 : ℝ)) (fun _ => 1) → ℂ :=
    coordFn 0 + Complex.I • coordFn 1
  have hq : Measurable fun y => (ζ y).im / (ζ y).re :=
    (Complex.measurable_im.comp hζ).div (Complex.measurable_re.comp hζ)
  have hgm : Measurable fun y => (((ζ y).im / (ζ y).re : ℝ) : ℂ) :=
    Complex.measurable_ofReal.comp hq
  have hPI := isSpectralIntegralOf_spectralIntegralOp hu hgm
  have hPS : IsSelfAdjointOp (spectralIntegralOp F fun y => (((ζ y).im / (ζ y).re : ℝ) : ℂ)) :=
    hu.isSelfAdjoint _ hgm (fun y => Complex.ofReal_im _) _
      (hasDomainAndAction_of_isSpectralIntegralOf hPI)
  refine ⟨_, ⟨hPS, fun s => (hgroup s).trans
    (expI_eq_integralOp_phaseFn h₄ hPS hq hPI s).symm⟩, fun B hB Δ => ?_⟩
  obtain ⟨-, -, -, -, -, -, hcc, -, -⟩ := h₄ H _ hPS
  rw [(hcc 2 _ F _ hq hPI).1]
  have hBC : Commute B C := commute_resolvent hU hC hB
  have hBC' : Commute B (star C) :=
    commute_resolvent (isContinuousUnitaryGroup_neg hU) (isResolventOp_star hU hC) fun s => hB (-s)
  exact hFc F hRep B (Fin.forall_fin_two.mpr
    ⟨commute_realPartOp hBC hBC', commute_imagPartOp hBC hBC'⟩) _
theorem stoneGenerator_unique (h₂ : BorelCalculusTheorem)
    (h₃ : JointSpectralTheorem)
    (h₄ : SpectralTheoremHolds) {U : ℝ → H →L[ℂ] H} {P P' : UnboundedOp H}
    (hP : IsStoneGenerator P U) (hP' : IsStoneGenerator P' U) : P = P' := by
  have he : spectralMeasure P = spectralMeasure P' := by
    refine spectralMeasure_eq_of_phases h₂ h₃ _ _ fun s i _ => ?_
    have hi : i = 0 := Subsingleton.elim _ _
    subst hi
    exact (hP.2 s).symm.trans (hP'.2 s)
  obtain ⟨-, -, -, -, -, hs, -, -, -⟩ := h₄ H P hP.1
  obtain ⟨-, -, -, -, -, hs', -, -, -⟩ := h₄ H P' hP'.1
  rw [← he] at hs'
  have hdom : P.domain = P'.domain := by
    ext ψ
    rw [hs.1, hs'.1]
  refine LinearPMap.ext hdom fun x hx hx' => ?_
  rw [hs.2, hs'.2]
theorem opKernel_eq_fixedPoints (h₂ : BorelCalculusTheorem)
    (h₄ : SpectralTheoremHolds) {U : ℝ → H →L[ℂ] H} {P : UnboundedOp H}
    (hU : IsContinuousUnitaryGroup U) (hP : IsStoneGenerator P U) :
    (opKernel P : Set H) = {ψ | ∀ s, U s ψ = ψ} := by
  obtain ⟨-, -, -, -, -, hspec, -, -, -⟩ := h₄ H P hP.1
  obtain ⟨hc, -, -, hu, hk, -, -⟩ := (h₂ H 1).1 _ (spectralMeasure P)
  set E := spectralMeasure P with hE
  have hlc : Measurable fun y : RealLineSet => y.1 0 :=
    (measurable_pi_apply 0).comp measurable_subtype_coe
  have hlv : Measurable (coordVar) := Complex.measurable_ofReal.comp hlc
  have hUs : ∀ s, U s = E.integralOp (phaseFn (fun y : RealLineSet => y.1 0) s) := hP.2
  have hker : (opKernel P : Set H) = Set.range (E (zeroLocus hlv)) := by
    rw [← hk.kernel_eq _ hlv]
    ext ψ
    constructor
    · intro hψ
      obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hψ
      refine ⟨(hspec.1 _).mp x.2, ?_⟩
      have h0 : P x = 0 := hx
      rw [hspec.2 x] at h0
      exact h0
    · rintro ⟨hd, h0⟩
      have hm : ψ ∈ P.domain := (hspec.1 _).mpr hd
      refine Submodule.mem_map.mpr ⟨⟨ψ, hm⟩, ?_, rfl⟩
      change P ⟨ψ, hm⟩ = 0
      rw [hspec.2]
      exact h0
  rw [hker]
  ext ψ
  constructor
  · rintro ⟨χ, rfl⟩ s
    have hr : Measurable ((zeroLocus hlv).1.indicator (1 : RealLineSet → ℂ)) :=
      measurable_one.indicator (zeroLocus hlv).2
    have hrb : IsBoundedFn ((zeroLocus hlv).1.indicator (1 : RealLineSet → ℂ)) :=
      ⟨1, fun y => by
        by_cases hy : y ∈ (zeroLocus hlv).1 <;> simp [hy]⟩
    have hm := hc.mul _ _ (measurable_phaseFn hlc s) (isBoundedFn_phaseFn _ s) hr hrb
    have hfun : phaseFn (fun y : RealLineSet => y.1 0) s * (zeroLocus hlv).1.indicator 1 =
        (zeroLocus hlv).1.indicator 1 := by
      funext y
      by_cases hy : y ∈ (zeroLocus hlv).1
      · have h0 : ((y.1 0 : ℝ) : ℂ) = 0 := hy
        simp [hy, phaseFn, h0]
      · simp [hy]
    rw [hfun, hc.indicator] at hm
    rw [hUs s]
    exact (congrArg (fun T : H →L[ℂ] H => T χ) hm).symm
  · intro hψ
    have hfix : ∀ s : ℝ, U s ψ = ψ := hψ
    have hC := isResolventOp_resolventMap hU
    have hCψ : resolventMap hU ψ = ψ := by
      rw [apply_eq_resolventVec hU hC]
      unfold resolventVec expDampedOrbit
      simp only [hfix]
      rw [integral_smul_const, integral_complex_ofReal, integral_exp_neg_Ioi_zero]
      simp
    have hCE := resolvent_eq_of_phases hc hC hlc fun s _ => hUs s
    set r : RealLineSet → ℂ := fun y => (1 - Complex.I * (y.1 0 : ℝ))⁻¹ with hrdef
    have hrm : Measurable r := measurable_inv_one_sub_I_mul hlc
    have hrb : IsBoundedFn r := isBoundedFn_inv_one_sub_I_mul _
    have hgm : Measurable (r + (-1 : ℂ) • fun _ => (1 : ℂ)) :=
      hrm.add (measurable_const.const_smul _)
    have hbound : IsBoundedFn (r + (-1 : ℂ) • fun _ => (1 : ℂ)) :=
      isBoundedFn_add hrb (isBoundedFn_smul _ ⟨1, fun _ => by simp⟩)
    have hg0 : E.integralOp (r + (-1 : ℂ) • fun _ => (1 : ℂ)) ψ = 0 := by
      rw [hc.add _ _ hrm hrb (measurable_const.const_smul _)
        (isBoundedFn_smul _ ⟨1, fun _ => by simp⟩),
        hc.smul _ _ measurable_const ⟨1, fun _ => by simp⟩, integralOp_one hc, ← hCE]
      simp [hCψ]
    obtain ⟨cg, hcg⟩ := hbound
    have hmem : ψ ∈ {ψ | ψ ∈ E.integralDom (r + (-1 : ℂ) • fun _ => (1 : ℂ)) ∧
        E.integralApply (r + (-1 : ℂ) • fun _ => (1 : ℂ)) ψ = 0} :=
      ⟨by rw [E.integralDom_eq_univ hcg]; trivial,
        by rw [E.integralApply_eq_integralOp hcg]; exact hg0⟩
    rw [hk.kernel_eq _ hgm] at hmem
    have hz : zeroLocus hgm = zeroLocus hlv := by
      refine Subtype.ext (Set.ext fun y => ?_)
      change (r + (-1 : ℂ) • (fun _ => (1 : ℂ)) : RealLineSet → ℂ) y = 0 ↔ ((y.1 0 : ℝ) : ℂ) = 0
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_one, hrdef]
      constructor
      · intro h
        have h1 : (1 - Complex.I * ((y.1 0 : ℝ) : ℂ))⁻¹ = 1 := by linear_combination h
        have h2 : 1 - Complex.I * ((y.1 0 : ℝ) : ℂ) = 1 := by
          simpa using inv_eq_one.mp h1
        have h3 : Complex.I * ((y.1 0 : ℝ) : ℂ) = 0 := by linear_combination -h2
        simpa using h3
      · intro h
        simp [h]
    rwa [hz] at hmem
end Generator
theorem stoneTheoremHolds (h₁ : HilbertSpaceFacts.Facts)
    (h₂ : BorelCalculusTheorem)
    (h₃ : JointSpectralTheorem)
    (h₄ : SpectralTheoremHolds) : StoneTheoremHolds := by
  intro H _ _ _
  refine ⟨fun U hU => ?_, fun n E E' h => spectralMeasure_eq_of_phases h₂ h₃ E E' h⟩
  have hC := isResolventOp_resolventOp hU
  have hd := denseRange_resolvent h₁ hU hC
  have hCs := isResolventOp_star hU hC
  obtain ⟨P₀, hP₀, hP₀c⟩ := exists_stoneGenerator h₁ h₂ h₃ h₄ hU
  have hG : IsStoneGenerator (stoneGenerator U) U :=
    Classical.epsilon_spec (p := fun P => IsStoneGenerator P U) ⟨P₀, hP₀⟩
  have hGe : stoneGenerator U = P₀ := stoneGenerator_unique h₂ h₃ h₄ hG hP₀
  have hform : IsSesquilinear (resolventForm U) :=
    { add_left := fun a b c => by simp only [resolventForm_eq hU, inner_add_left]
      smul_left := fun z a b => by simp only [resolventForm_eq hU, inner_smul_left]
      add_right := fun a b c => by
        simp only [resolventForm_eq hU, resolventVec_add hU, inner_add_right]
      smul_right := fun z a b => by
        simp only [resolventForm_eq hU, resolventVec_smul, inner_smul_right] }
  refine ⟨group_continuous_apply hU, group_star hU, integrableOn_expDampedInner hU, hform, ?_,
    ⟨_, hC, fun C' h => resolventOp_unique hU h hC⟩, hC, hCs, fun B hB =>
      ⟨commute_resolvent hU hC hB,
        commute_resolvent (isContinuousUnitaryGroup_neg hU) hCs fun s => hB (-s)⟩,
    resolvent_star_mul_self hU hC, ?_, eq_zero_of_resolvent_eq_zero hU hC, hd, ?_, ?_,
    ⟨P₀, hP₀, fun P hP => stoneGenerator_unique h₂ h₃ h₄ hP hP₀⟩, hG,
    opKernel_eq_fixedPoints h₂ h₄ hU hG, ?_⟩
  · intro φ ψ
    rw [resolventForm_eq hU]
    exact (norm_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_left (norm_resolventVec_le hU ψ) (norm_nonneg _))
  · rw [(resolvent_commute_star hU hC).eq]
    exact resolvent_star_mul_self hU hC
  · intro n Y F ζ hζ hb hCF
    obtain ⟨hc, hs, -, hu, hk, -, -⟩ := (h₂ H n).1 Y F
    have hcar := isCarriedBy_circleSupport hU hC hc hk hζ hb hCF
    refine ⟨hcar, fun s => ?_⟩
    have hq : Measurable fun y => (ζ y).im / (ζ y).re :=
      (Complex.measurable_im.comp hζ).div (Complex.measurable_re.comp hζ)
    rw [group_eq_integralOp_phases hU hC hd hc hs hu hk hζ hb hCF s]
    have hm : Measurable (phaseFn (fun y => (ζ y).im / (ζ y).re) s) := measurable_phaseFn hq s
    have hme : Measurable (zeroExtend (circleSupport ζ hζ).1 fun y : (circleSupport ζ hζ).1 =>
        Complex.exp (Complex.I * s * (((ζ y.1).im / (ζ y.1).re : ℝ) : ℂ))) :=
      measurable_zeroExtend (circleSupport ζ hζ).2 (hm.comp measurable_subtype_coe)
    refine integralOp_congr hu hm (isBoundedFn_phaseFn _ s) hme ⟨1, fun y => ?_⟩ _ hcar
      fun y hy => ?_
    · unfold zeroExtend
      split_ifs with h
      · exact (norm_phaseFn (fun y => (ζ y).im / (ζ y).re) s y).le
      · simp
    · simp only [zeroExtend, dif_pos hy, phaseFn]
  · intro n Y F q hq h
    obtain ⟨hc, -, -, -, -, -, -⟩ := (h₂ H n).1 Y F
    exact resolvent_eq_of_phases hc hC hq h
  · intro B hB Δ
    rw [hGe]
    exact hP₀c B hB Δ
end YangMills.Construction.UnitaryGroups.Stone
