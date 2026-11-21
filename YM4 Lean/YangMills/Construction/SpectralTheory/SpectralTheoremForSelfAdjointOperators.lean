import YangMills.Construction.SpectralTheory.BorelFunctionalCalculusTheorem
import YangMills.Construction.SpectralTheory.SelfAdjointSpectralMeasure
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
open MeasureTheory Set Filter Topology
open scoped InnerProductSpace ComplexConjugate ComplexOrder
noncomputable section
namespace YangMills.Construction.SpectralTheorem
open YangMills.Construction.BorelSpectral YangMills.Construction.HilbertSpaceBasics
open YangMills.Construction.BorelCalculus
open YangMills.Construction.JointSpectral
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
theorem eq_of_inner_eq_on_dense {D : Set H} (hD : Dense D) {x y : H}
    (h : ∀ v ∈ D, ⟪x, v⟫_ℂ = ⟪y, v⟫_ℂ) : x = y := by
  have hclosed : IsClosed {v : H | ⟪x, v⟫_ℂ = ⟪y, v⟫_ℂ} :=
    isClosed_eq (continuous_const.inner continuous_id) (continuous_const.inner continuous_id)
  have hsub : closure D ⊆ {v : H | ⟪x, v⟫_ℂ = ⟪y, v⟫_ℂ} := hclosed.closure_subset_iff.2 h
  rw [hD.closure_eq] at hsub
  exact ext_inner_right ℂ fun v => hsub (mem_univ v)
theorem cauchySeq_of_dist_le_dist {u v : ℕ → H} (hv : CauchySeq v)
    (h : ∀ m k, dist (u m) (u k) ≤ dist (v m) (v k)) : CauchySeq u := by
  refine Metric.cauchySeq_iff.2 fun ε hε => ?_
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.1 hv ε hε
  exact ⟨N, fun m hm k hk => (h m k).trans_lt (hN m hm k hk)⟩
section SelfAdjoint
variable {A : UnboundedOp H} (hA : IsSelfAdjointOp A)
include hA
theorem inner_op_apply_left (φ ψ : A.domain) : ⟪A φ, (ψ : H)⟫_ℂ = ⟪(φ : H), A ψ⟫_ℂ :=
  (hA.2.2 φ ψ).symm
theorem im_inner_op_apply_self (ψ : A.domain) : (⟪A ψ, (ψ : H)⟫_ℂ).im = 0 := by
  have h := inner_op_apply_left hA ψ ψ
  rw [← inner_conj_symm (ψ : H) (A ψ)] at h
  have := congrArg Complex.im h
  simp only [Complex.conj_im] at this
  linarith
theorem norm_op_add_smul_sq {z : ℂ} (hz : z.re = 0) (hz' : ‖z‖ = 1) (ψ : A.domain) :
    ‖A ψ + z • (ψ : H)‖ ^ 2 = ‖A ψ‖ ^ 2 + ‖(ψ : H)‖ ^ 2 := by
  have h₀ : (⟪A ψ, z • (ψ : H)⟫_ℂ).re = 0 := by
    rw [inner_smul_right, Complex.mul_re, hz, im_inner_op_apply_self hA ψ]
    ring
  have h := @norm_add_sq ℂ H _ _ _ (A ψ) (z • (ψ : H))
  rw [norm_smul, hz'] at h
  simp only [RCLike.re_to_complex] at h
  rw [h, h₀]
  ring
theorem addConst_injective {z : ℂ} (hz : z.re = 0) (hz' : ‖z‖ = 1) :
    Function.Injective (addConst A z).toFun := by
  intro x y hxy
  have hd : A (⟨(x : H) - y, A.domain.sub_mem x.2 y.2⟩ : A.domain) + z • ((x : H) - y) = 0 := by
    have h₁ : (addConst A z).toFun x = A.toFun x + z • (x : H) := rfl
    have h₂ : (addConst A z).toFun y = A.toFun y + z • (y : H) := rfl
    have h₃ : A.toFun (x - y) = A.toFun x - A.toFun y := map_sub _ _ _
    have h₄ : A (⟨(x : H) - y, A.domain.sub_mem x.2 y.2⟩ : A.domain) = A.toFun (x - y) := rfl
    rw [h₄, h₃, smul_sub]
    have := sub_eq_zero.2 hxy
    rw [h₁, h₂] at this
    rw [← this]
    abel
  have h := norm_op_add_smul_sq hA hz hz' ⟨(x : H) - y, A.domain.sub_mem x.2 y.2⟩
  simp only at h
  rw [hd, norm_zero] at h
  have h₀ : ‖(x : H) - y‖ ^ 2 = 0 := by
    have := sq_nonneg ‖A (⟨(x : H) - y, A.domain.sub_mem x.2 y.2⟩ : A.domain)‖
    have := sq_nonneg ‖(x : H) - y‖
    nlinarith
  have h₁ : (x : H) - y = 0 := by simpa using h₀
  exact Subtype.ext (sub_eq_zero.1 h₁)
theorem addConst_range_isClosed {z : ℂ} (hz : z.re = 0) (hz' : ‖z‖ = 1) :
    IsClosed (LinearMap.range (addConst A z).toFun : Set H) := by
  refine IsSeqClosed.isClosed fun {χ χ₀} hχ hlim => ?_
  choose ψ hψ using fun r => (hχ r : χ r ∈ LinearMap.range (addConst A z).toFun)
  have hval : ∀ r, A (ψ r) + z • (ψ r : H) = χ r := hψ
  have hsub : ∀ m k, A (ψ m - ψ k) = A (ψ m) - A (ψ k) := fun m k => map_sub A.toFun _ _
  have hdist : ∀ m k, ‖A (ψ m) - A (ψ k)‖ ^ 2 + ‖(ψ m : H) - ψ k‖ ^ 2 = ‖χ m - χ k‖ ^ 2 := by
    intro m k
    have h := norm_op_add_smul_sq hA hz hz' (ψ m - ψ k)
    have h₁ : A (ψ m - ψ k) + z • ((ψ m - ψ k : A.domain) : H) = χ m - χ k := by
      rw [← hval m, ← hval k, hsub, Submodule.coe_sub, smul_sub]
      abel
    rw [h₁, hsub, Submodule.coe_sub] at h
    rw [h]
  have hc := hlim.cauchySeq
  have hψc : CauchySeq fun r => (ψ r : H) := by
    refine cauchySeq_of_dist_le_dist hc fun m k => ?_
    rw [dist_eq_norm, dist_eq_norm]
    have h := hdist m k
    have h₁ := sq_nonneg ‖A (ψ m) - A (ψ k)‖
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 (by linarith)
  have hAc : CauchySeq fun r => A (ψ r) := by
    refine cauchySeq_of_dist_le_dist hc fun m k => ?_
    rw [dist_eq_norm, dist_eq_norm]
    have h := hdist m k
    have h₁ := sq_nonneg ‖(ψ m : H) - ψ k‖
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 (by linarith)
  obtain ⟨p, hp⟩ := cauchySeq_tendsto_of_complete hψc
  obtain ⟨η, hη⟩ := cauchySeq_tendsto_of_complete hAc
  have hin : ∀ φ : A.domain, ⟪p, A φ⟫_ℂ = ⟪η, (φ : H)⟫_ℂ := fun φ =>
    tendsto_nhds_unique (hp.inner tendsto_const_nhds)
      ((hη.inner tendsto_const_nhds).congr fun r => inner_op_apply_left hA (ψ r) φ)
  have hpd : p ∈ A.domain := (hA.2.1 p).2 ⟨η, hin⟩
  have hAp : A ⟨p, hpd⟩ = η := eq_of_inner_eq_on_dense hA.1 fun v hv => by
    rw [← hA.2.2 ⟨p, hpd⟩ ⟨v, hv⟩]
    exact hin ⟨v, hv⟩
  refine ⟨⟨p, hpd⟩, ?_⟩
  show A ⟨p, hpd⟩ + z • p = χ₀
  rw [hAp]
  exact tendsto_nhds_unique ((hη.add (hp.const_smul z)).congr hval) hlim
theorem addConst_surjective {z : ℂ} (hz : z.re = 0) (hz' : ‖z‖ = 1) :
    Function.Surjective (addConst A z).toFun := by
  have hcl := addConst_range_isClosed hA hz hz'
  haveI : CompleteSpace (LinearMap.range (addConst A z).toFun) := hcl.completeSpace_coe
  have hperp : (LinearMap.range (addConst A z).toFun)ᗮ = ⊥ := by
    refine (Submodule.eq_bot_iff _).2 fun φ hφ => ?_
    have h₁ : ∀ ψ : A.domain, ⟪φ, A ψ⟫_ℂ = ⟪(-conj z) • φ, (ψ : H)⟫_ℂ := by
      intro ψ
      have h₂ : ⟪φ, A ψ + z • (ψ : H)⟫_ℂ = 0 :=
        (Submodule.mem_orthogonal' _ _).1 hφ _ ⟨ψ, rfl⟩
      rw [inner_add_right, inner_smul_right] at h₂
      rw [inner_smul_left, map_neg, Complex.conj_conj]
      linear_combination h₂
    have hd : φ ∈ A.domain := (hA.2.1 φ).2 ⟨_, h₁⟩
    have hv : A ⟨φ, hd⟩ = (-conj z) • φ := eq_of_inner_eq_on_dense hA.1 fun v hv => by
      rw [← hA.2.2 ⟨φ, hd⟩ ⟨v, hv⟩]
      exact h₁ ⟨v, hv⟩
    have h₃ := norm_op_add_smul_sq hA (z := conj z) (by simpa using hz) (by simpa using hz') ⟨φ, hd⟩
    simp only at h₃
    rw [hv, neg_smul, neg_add_cancel, norm_zero] at h₃
    have h₄ : ‖φ‖ ^ 2 = 0 := by
      have := sq_nonneg ‖(-conj z) • φ‖
      have := sq_nonneg ‖φ‖
      have := sq_nonneg ‖-(conj z • φ)‖
      nlinarith
    simpa using h₄
  exact LinearMap.range_eq_top.1 (Submodule.orthogonal_eq_bot_iff.1 hperp)
theorem exists_boundedInverse {z : ℂ} (hz : z.re = 0) (hz' : ‖z‖ = 1) :
    ∃ R : H →L[ℂ] H, IsBoundedInverse R (addConst A z) ∧ ‖R‖ ≤ 1 := by
  let e := LinearEquiv.ofBijective (addConst A z).toFun
    ⟨addConst_injective hA hz hz', addConst_surjective hA hz hz'⟩
  have hb : ∀ χ, ‖(addConst A z).domain.subtype (e.symm χ)‖ ≤ 1 * ‖χ‖ := by
    intro χ
    have h := norm_op_add_smul_sq hA hz hz' (e.symm χ)
    have hv : A (e.symm χ) + z • ((e.symm χ : (addConst A z).domain) : H) = χ :=
      e.apply_symm_apply χ
    rw [hv] at h
    rw [one_mul]
    have h₁ := sq_nonneg ‖A (e.symm χ)‖
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1
      (by change ‖((e.symm χ : (addConst A z).domain) : H)‖ ^ 2 ≤ _; linarith)
  let R : H →L[ℂ] H := ((addConst A z).domain.subtype ∘ₗ e.symm.toLinearMap).mkContinuous 1 hb
  refine ⟨R, ⟨fun χ => ⟨(e.symm χ).2, e.apply_symm_apply χ⟩, fun ψ => ?_⟩,
    LinearMap.mkContinuous_norm_le _ zero_le_one _⟩
  exact congrArg Subtype.val (e.symm_apply_apply ψ)
omit hA in
theorem exists_dom_of_boundedInverse {R : H →L[ℂ] H} {z : ℂ}
    (hR : IsBoundedInverse R (addConst A z)) (χ : H) :
    ∃ a : A.domain, (a : H) = R χ ∧ A a + z • (a : H) = χ := by
  obtain ⟨h, e⟩ := hR.1 χ
  exact ⟨⟨R χ, h⟩, rfl, e⟩
omit hA in
theorem boundedInverse_apply_op_add {R : H →L[ℂ] H} {z : ℂ}
    (hR : IsBoundedInverse R (addConst A z)) (ψ : A.domain) : R (A ψ + z • (ψ : H)) = ψ :=
  hR.2 ψ
theorem resolvent_relations {R R' : H →L[ℂ] H}
    (hR : IsBoundedInverse R (addConst A Complex.I))
    (hR' : IsBoundedInverse R' (addConst A (-Complex.I))) :
    (∀ χ, R χ = 0 → χ = 0) ∧ Set.range R = A.domain ∧ star R = R' ∧
      R - star R = (-2 * Complex.I) • (star R * R) ∧
      R - star R = (-2 * Complex.I) • (R * star R) := by
  have hstar : star R = R' := by
    rw [ContinuousLinearMap.star_eq_adjoint]
    refine ((ContinuousLinearMap.eq_adjoint_iff R' R).2 fun x y => ?_).symm
    obtain ⟨a, ha, ea⟩ := exists_dom_of_boundedInverse hR' x
    obtain ⟨b, hb, eb⟩ := exists_dom_of_boundedInverse hR y
    rw [← ha, ← hb, ← ea, ← eb, inner_add_right, inner_smul_right, inner_add_left, inner_smul_left,
      inner_op_apply_left hA a b]
    simp
  refine ⟨fun χ h => ?_, ?_, hstar, ?_, ?_⟩
  · obtain ⟨a, ha, ea⟩ := exists_dom_of_boundedInverse hR χ
    have h₀ : a = 0 := Subtype.ext (ha.trans h)
    rw [← ea, h₀]
    simp
  · ext ψ
    constructor
    · rintro ⟨χ, rfl⟩
      obtain ⟨a, ha, -⟩ := exists_dom_of_boundedInverse hR χ
      exact ha ▸ a.2
    · intro hψ
      exact ⟨_, boundedInverse_apply_op_add hR ⟨ψ, hψ⟩⟩
  · rw [hstar]
    ext χ
    obtain ⟨a, ha, ea⟩ := exists_dom_of_boundedInverse hR χ
    have r₁ := boundedInverse_apply_op_add hR' a
    have hsum := congrArg R' (show A a + Complex.I • (a : H) =
      (A a + (-Complex.I) • (a : H)) + (2 * Complex.I) • (a : H) by module)
    rw [ea, map_add, r₁, map_smul] at hsum
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.mul_apply]
    rw [← ha, hsum]
    module
  · rw [hstar]
    ext χ
    obtain ⟨a, ha, ea⟩ := exists_dom_of_boundedInverse hR' χ
    have r₁ := boundedInverse_apply_op_add hR a
    have hsum := congrArg R (show A a + (-Complex.I) • (a : H) =
      (A a + Complex.I • (a : H)) + (-2 * Complex.I) • (a : H) by module)
    rw [ea, map_add, r₁, map_smul] at hsum
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.mul_apply]
    rw [← ha, hsum]
    module
end SelfAdjoint
theorem isPositive_const_add_of_norm_le {T : H →L[ℂ] H} (hT : IsSelfAdjoint T) {c : ℝ}
    (hc : ‖T‖ ≤ c) : (((c : ℝ) : ℂ) • (1 : H →L[ℂ] H) + T).IsPositive := by
  have hs : IsSelfAdjoint (((c : ℝ) : ℂ) • (1 : H →L[ℂ] H) + T) :=
    (IsSelfAdjoint.smul (show IsSelfAdjoint ((c : ℝ) : ℂ) from Complex.conj_ofReal c)
      (IsSelfAdjoint.one _)).add hT
  refine (ContinuousLinearMap.isPositive_iff' _).2 ⟨hs, fun x => ?_⟩
  have hsym := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.1 hT
  have him : (⟪T x, x⟫_ℂ).im = 0 := by
    have h : ⟪T x, x⟫_ℂ = ⟪x, T x⟫_ℂ := hsym x x
    rw [← inner_conj_symm x (T x)] at h
    have := congrArg Complex.im h
    simp only [Complex.conj_im] at this
    linarith
  have hval : ⟪(((c : ℝ) : ℂ) • (1 : H →L[ℂ] H) + T) x, x⟫_ℂ =
      (c : ℂ) * ((‖x‖ ^ 2 : ℝ) : ℂ) + ⟪T x, x⟫_ℂ := by
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.one_apply, inner_add_left, inner_smul_left, Complex.conj_ofReal,
      inner_self_eq_norm_sq_to_K]
    push_cast
    rfl
  rw [hval, Complex.le_def]
  have hre : -(‖T‖ * ‖x‖ ^ 2) ≤ (⟪T x, x⟫_ℂ).re := by
    have h₁ := (Complex.abs_re_le_norm ⟪T x, x⟫_ℂ).trans
      ((norm_inner_le_norm (𝕜 := ℂ) (T x) x).trans
        (mul_le_mul_of_nonneg_right (T.le_opNorm x) (norm_nonneg x)))
    have h₂ := (abs_le.1 h₁).1
    nlinarith
  constructor
  · simp only [Complex.zero_re, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero]
    have := mul_le_mul_of_nonneg_right hc (sq_nonneg ‖x‖)
    linarith
  · simp only [Complex.zero_im, Complex.add_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, him]
    ring
theorem neg_const_le_and_le_const_of_norm_le {T : H →L[ℂ] H} (hT : IsSelfAdjoint T) {c : ℝ}
    (hc : ‖T‖ ≤ c) :
    (((-c : ℝ)) : ℂ) • (1 : H →L[ℂ] H) ≤ T ∧ T ≤ ((c : ℝ) : ℂ) • (1 : H →L[ℂ] H) := by
  constructor
  · rw [ContinuousLinearMap.le_def]
    have h := isPositive_const_add_of_norm_le hT hc
    convert h using 1
    push_cast
    module
  · rw [ContinuousLinearMap.le_def]
    have h := isPositive_const_add_of_norm_le (T := -T) hT.neg (by simpa using hc)
    convert h using 1
    module
theorem isBoundedFn_add {X : Type*} {g h : X → ℂ} (hg : IsBoundedFn g)
    (hh : IsBoundedFn h) : IsBoundedFn (g + h) := by
  obtain ⟨c, hc⟩ := hg
  obtain ⟨d, hd⟩ := hh
  exact ⟨c + d, fun x => (norm_add_le _ _).trans (add_le_add (hc x) (hd x))⟩
theorem isBoundedFn_smul {X : Type*} {g : X → ℂ} (z : ℂ) (hg : IsBoundedFn g) :
    IsBoundedFn (z • g) := by
  obtain ⟨c, hc⟩ := hg
  refine ⟨‖z‖ * c, fun x => ?_⟩
  rw [Pi.smul_apply, norm_smul]
  exact mul_le_mul_of_nonneg_left (hc x) (norm_nonneg z)
theorem isBoundedFn_mul {X : Type*} {g h : X → ℂ} (hg : IsBoundedFn g)
    (hh : IsBoundedFn h) : IsBoundedFn (g * h) := by
  obtain ⟨c, hc⟩ := hg
  obtain ⟨d, hd⟩ := hh
  refine ⟨c * d, fun x => ?_⟩
  rw [Pi.mul_apply, norm_mul]
  exact mul_le_mul (hc x) (hd x) (norm_nonneg _) ((norm_nonneg _).trans (hc x))
theorem isBoundedFn_conjFn {X : Type*} {g : X → ℂ} (hg : IsBoundedFn g) :
    IsBoundedFn (conjFn g) := by
  obtain ⟨c, hc⟩ := hg
  exact ⟨c, fun x => by simpa [conjFn] using hc x⟩
theorem isBoundedFn_one {X : Type*} : IsBoundedFn (1 : X → ℂ) :=
  ⟨1, fun _ => by simp⟩
theorem measurable_conjFn {X : Type*} [MeasurableSpace X] {g : X → ℂ} (hg : Measurable g) :
    Measurable (conjFn g) :=
  Complex.continuous_conj.measurable.comp hg
theorem measurable_coordVar : Measurable (coordVar : RealLineSet → ℂ) :=
  Complex.measurable_ofReal.comp ((measurable_pi_apply 0).comp measurable_subtype_coe)
section Calculus
variable (hC : BorelCalculusTheorem)
include hC
theorem boundedCalculus_of {n : ℕ} {Y : Set (Fin n → ℝ)} (E : SpectralMeasure Y H) :
    BoundedFunctionalCalculus E :=
  ((hC H n).1 Y E).1
theorem unboundedCalculus_of {n : ℕ} {Y : Set (Fin n → ℝ)} (E : SpectralMeasure Y H) :
    UnboundedFunctionalCalculus E :=
  ((hC H n).1 Y E).2.2.2.1
theorem kernelAndPositivity_of {n : ℕ} {Y : Set (Fin n → ℝ)} (E : SpectralMeasure Y H) :
    KernelAndPositivity E :=
  ((hC H n).1 Y E).2.2.2.2.1
theorem pushforwardProperties_of {n : ℕ} {Y : Set (Fin n → ℝ)} (E : SpectralMeasure Y H) :
    PushforwardProperties E :=
  ((hC H n).1 Y E).2.2.2.2.2.1
theorem integralOp_one {n : ℕ} {Y : Set (Fin n → ℝ)} (E : SpectralMeasure Y H) :
    E.integralOp 1 = 1 := by
  have h := (boundedCalculus_of hC E).indicator ⟨univ, MeasurableSet.univ⟩
  simp only [indicator_univ] at h
  rw [h]
  exact E.map_univ
theorem integralOp_congr_of_isCarriedBy {n : ℕ} {Y : Set (Fin n → ℝ)} (E : SpectralMeasure Y H)
    {g h : Y → ℂ} (hg : Measurable g) (hh : Measurable h) (hgb : IsBoundedFn g)
    (hhb : IsBoundedFn h) (Δ₀ : BorelSubsets Y) (hΔ : E.IsCarriedBy Δ₀)
    (he : ∀ y ∈ Δ₀.1, g y = h y) : E.integralOp g = E.integralOp h := by
  obtain ⟨c, hc⟩ := hgb
  obtain ⟨d, hd⟩ := hhb
  have hcong := (unboundedCalculus_of hC E).congr g h hg hh Δ₀ hΔ he
  ext ψ
  rw [← E.integralApply_eq_integralOp hc ψ, ← E.integralApply_eq_integralOp hd ψ]
  exact hcong.2 ψ (by rw [E.integralDom_eq_univ hc]; exact mem_univ ψ)
theorem pushforwardToLine_integral {n : ℕ} {Y : Set (Fin n → ℝ)} (E : SpectralMeasure Y H)
    (g : Y → ℝ) (hg : Measurable g) (f : RealLineSet → ℂ) (hf : Measurable f) :
    (pushforwardToLine E g hg).integralDom f =
        E.integralDom (fun y => f ⟨fun _ => g y, mem_univ _⟩) ∧
      ∀ ψ ∈ E.integralDom (fun y => f ⟨fun _ => g y, mem_univ _⟩),
        (pushforwardToLine E g hg).integralApply f ψ =
          E.integralApply (fun y => f ⟨fun _ => g y, mem_univ _⟩) ψ :=
  (pushforwardProperties_of hC E).integral_pushforward le_rfl MeasurableSet.univ _ _ f hf
theorem isSpectralMeasureFor_pushforwardToLine {n : ℕ} {Y : Set (Fin n → ℝ)} {A : UnboundedOp H}
    (E : SpectralMeasure Y H) (g : Y → ℝ) (hg : Measurable g)
    (hA : IsSpectralIntegralOf A E fun y => ((g y : ℝ) : ℂ)) :
    IsSpectralMeasureFor (pushforwardToLine E g hg) A := by
  have h := pushforwardToLine_integral hC E g hg coordVar measurable_coordVar
  refine ⟨fun ψ => ?_, fun ψ => ?_⟩
  · rw [h.1]
    exact hA.1 ψ
  · rw [h.2 ψ ((hA.1 ψ).1 ψ.2)]
    exact hA.2 ψ
end Calculus
theorem quotient_mul_eq_one_add (a b : ℝ) (h₁ : (a : ℂ) + Complex.I * b ≠ 0)
    (h₂ : 2 * Complex.I * (b : ℂ) + 2 * Complex.I *
      (conj ((a : ℂ) + Complex.I * b) * ((a : ℂ) + Complex.I * b)) = 0) :
    ((-a / b : ℝ) : ℂ) * ((a : ℂ) + Complex.I * b) =
      1 + -Complex.I * ((a : ℂ) + Complex.I * b) := by
  have hb : b + (a ^ 2 + b ^ 2) = 0 := by
    have h := congrArg Complex.im h₂
    simp at h
    nlinarith
  have hb₀ : b ≠ 0 := by
    rintro rfl
    have ha : a = 0 := by nlinarith
    exact h₁ (by simp [ha])
  apply Complex.ext
  · simp
    field_simp
    nlinarith
  · simp
    field_simp
section Existence
variable {A : UnboundedOp H} (hC : BorelCalculusTheorem) (hA : IsSelfAdjointOp A)
include hC hA
theorem exists_spectralMeasure_of_resolvent {R : H →L[ℂ] H}
    (hR : IsBoundedInverse R (addConst A Complex.I))
    (hker : ∀ χ, R χ = 0 → χ = 0)
    (hrel : R - star R = (-2 * Complex.I) • (star R * R))
    {Y : Set (Fin 2 → ℝ)} (F : SpectralMeasure Y H)
    (hb : ∀ (y : Y) (i : Fin 2), ‖((y.1 i : ℝ) : ℂ)‖ ≤ 1)
    (h₀ : F.integralOp (coordFn 0) = (1 / 2 : ℂ) • (R + star R))
    (h₁ : F.integralOp (coordFn 1) = (-Complex.I / 2) • (R - star R)) :
    ∃ E : SpectralMeasure RealLineSet H, IsSpectralMeasureFor E A := by
  have bc := boundedCalculus_of hC F
  have uc := unboundedCalculus_of hC F
  have ks := kernelAndPositivity_of hC F
  let c₀ : Y → ℂ := coordFn 0
  let c₁ : Y → ℂ := coordFn 1
  have m₀ : Measurable c₀ :=
    Complex.measurable_ofReal.comp ((measurable_pi_apply 0).comp measurable_subtype_coe)
  have m₁ : Measurable c₁ :=
    Complex.measurable_ofReal.comp ((measurable_pi_apply 1).comp measurable_subtype_coe)
  have b₀ : IsBoundedFn c₀ := ⟨1, fun y => hb y 0⟩
  have b₁ : IsBoundedFn c₁ := ⟨1, fun y => hb y 1⟩
  let ζ : Y → ℂ := c₀ + Complex.I • c₁
  have mζ : Measurable ζ := m₀.add (m₁.const_smul _)
  have bζ : IsBoundedFn ζ := isBoundedFn_add b₀ (isBoundedFn_smul _ b₁)
  have hII : Complex.I * (-Complex.I / 2) = 1 / 2 := by
    have := Complex.I_mul_I
    linear_combination (-1 / 2 : ℂ) * this
  have hII' : (2 * Complex.I) * (-Complex.I / 2) = 1 := by
    have := Complex.I_mul_I
    linear_combination (-1 : ℂ) * this
  have hζ : F.integralOp ζ = R := by
    rw [bc.add c₀ (Complex.I • c₁) m₀ b₀ (m₁.const_smul _) (isBoundedFn_smul _ b₁),
      bc.smul _ c₁ m₁ b₁, h₀, h₁, smul_smul, hII]
    module
  let ζc : Y → ℂ := conjFn ζ
  have mζc : Measurable ζc := measurable_conjFn mζ
  have bζc : IsBoundedFn ζc := isBoundedFn_conjFn bζ
  have hζc : F.integralOp ζc = star R := by
    rw [bc.star_eq ζ mζ bζ, hζ]
  let g₂ : Y → ℂ := (2 * Complex.I) • c₁ + (2 * Complex.I) • (ζc * ζ)
  have mg₂ : Measurable g₂ := (m₁.const_smul _).add ((mζc.mul mζ).const_smul _)
  have bg₂ : IsBoundedFn g₂ :=
    isBoundedFn_add (isBoundedFn_smul _ b₁) (isBoundedFn_smul _ (isBoundedFn_mul bζc bζ))
  have hg₂ : F.integralOp g₂ = 0 := by
    rw [bc.add _ _ (m₁.const_smul _) (isBoundedFn_smul _ b₁) ((mζc.mul mζ).const_smul _)
        (isBoundedFn_smul _ (isBoundedFn_mul bζc bζ)),
      bc.smul _ c₁ m₁ b₁, bc.smul _ _ (mζc.mul mζ) (isBoundedFn_mul bζc bζ),
      bc.mul _ _ mζc bζc mζ bζ, h₁, hζ, hζc, smul_smul, hII', one_smul, hrel]
    module
  have hN : F (nonzeroLocus mg₂) = 0 := (ks.eq_zero_iff g₂ mg₂).1 fun ψ _ => by
    obtain ⟨c, hc⟩ := bg₂
    rw [F.integralApply_eq_integralOp hc, hg₂]
    rfl
  have hZ : F (zeroLocus mζ) = 0 := by
    refine ContinuousLinearMap.ext fun x => ?_
    have hm : F (zeroLocus mζ) x ∈ {ψ | ψ ∈ F.integralDom ζ ∧ F.integralApply ζ ψ = 0} := by
      rw [ks.kernel_eq ζ mζ]
      exact ⟨x, rfl⟩
    obtain ⟨c, hc⟩ := bζ
    have h := hm.2
    rw [F.integralApply_eq_integralOp hc, hζ] at h
    simpa using hker _ h
  let Y₀ : BorelSubsets Y := ⟨(zeroLocus mζ).1ᶜ ∩ (nonzeroLocus mg₂).1ᶜ,
    (zeroLocus mζ).2.compl.inter (nonzeroLocus mg₂).2.compl⟩
  have hcar : F.IsCarriedBy Y₀ := by
    have hU := bc.apply_iUnion Bool (fun b => cond b (zeroLocus mζ) (nonzeroLocus mg₂)) (by
      intro b
      cases b
      · exact hN
      · exact hZ)
    refine bc.apply_subset _ _ hU fun y hy => ?_
    simp only [mem_iUnion]
    by_cases hz : y ∈ (zeroLocus mζ).1
    · exact ⟨true, hz⟩
    · by_cases hn : y ∈ (nonzeroLocus mg₂).1
      · exact ⟨false, hn⟩
      · exact absurd ⟨hz, hn⟩ hy
  have hpt : ∀ y ∈ Y₀.1, ((-(y.1 0) / (y.1 1) : ℝ) : ℂ) * ζ y = 1 + -Complex.I * ζ y := by
    intro y hy
    refine quotient_mul_eq_one_add (y.1 0) (y.1 1) hy.1 ?_
    have h := hy.2
    simp only [nonzeroLocus, mem_compl_iff, mem_preimage, mem_singleton_iff, not_not] at h
    exact h
  let q : Y → ℝ := Y₀.1.indicator fun y => -(y.1 0) / (y.1 1)
  have mq : Measurable q := Measurable.indicator
    ((((measurable_pi_apply 0).comp measurable_subtype_coe).neg).div
      ((measurable_pi_apply 1).comp measurable_subtype_coe)) Y₀.2
  let qc : Y → ℂ := fun y => ((q y : ℝ) : ℂ)
  have mqc : Measurable qc := Complex.measurable_ofReal.comp mq
  let w : Y → ℂ := 1 + (-Complex.I) • ζ
  have mw : Measurable w := measurable_const.add (mζ.const_smul _)
  have bw : IsBoundedFn w := isBoundedFn_add isBoundedFn_one (isBoundedFn_smul _ bζ)
  have hw : F.integralOp w = 1 + (-Complex.I) • R := by
    rw [bc.add (1 : Y → ℂ) ((-Complex.I) • ζ) measurable_const isBoundedFn_one
        (mζ.const_smul _) (isBoundedFn_smul _ bζ),
      bc.smul _ ζ mζ bζ, hζ, integralOp_one hC]
  have hon : ∀ y ∈ Y₀.1, (qc * ζ) y = w y := by
    intro y hy
    show ((q y : ℝ) : ℂ) * ζ y = _
    rw [show q y = -(y.1 0) / (y.1 1) from indicator_of_mem hy _]
    exact hpt y hy
  have bqζ : IsBoundedFn (qc * ζ) := by
    obtain ⟨c, hc⟩ := bw
    refine ⟨max c 0, fun y => ?_⟩
    by_cases hy : y ∈ Y₀.1
    · rw [hon y hy]
      exact (hc y).trans (le_max_left _ _)
    · have h : (qc * ζ) y = 0 := by
        show ((q y : ℝ) : ℂ) * ζ y = 0
        rw [show q y = 0 from indicator_of_notMem hy _]
        simp
      rw [h, norm_zero]
      exact le_max_right _ _
  have hqζ : F.integralOp (qc * ζ) = F.integralOp w :=
    integralOp_congr_of_isCarriedBy hC F (mqc.mul mζ) mw bqζ bw Y₀ hcar hon
  obtain ⟨A', -, hA'⟩ := uc.exists_op qc mqc
  have hsa := uc.isSelfAdjoint qc mqc (fun y => Complex.ofReal_im _) A' hA'
  have hsub : ∀ ψ : A.domain, (ψ : H) ∈ F.integralDom qc ∧
      F.integralApply qc ψ = A ψ := by
    intro ψ
    have hr := uc.range_subset_dom qc ζ mqc mζ bζ bqζ (A ψ + Complex.I • (ψ : H))
    rw [hζ, boundedInverse_apply_op_add hR ψ, hqζ, hw] at hr
    refine ⟨hr.1, hr.2.trans ?_⟩
    show (A ψ + Complex.I • (ψ : H)) + (-Complex.I) • R (A ψ + Complex.I • (ψ : H)) = A ψ
    rw [boundedInverse_apply_op_add hR ψ]
    module
  have hdom : ∀ φ ∈ F.integralDom qc, φ ∈ A.domain := by
    intro φ hφ
    have hφ' : φ ∈ A'.domain := by
      exact show φ ∈ (A'.domain : Set H) from hA'.1 ▸ hφ
    refine (hA.2.1 φ).2 ⟨A' ⟨φ, hφ'⟩, fun ψ => ?_⟩
    have hψ' : (ψ : H) ∈ A'.domain := by
      exact show (ψ : H) ∈ (A'.domain : Set H) from hA'.1 ▸ (hsub ψ).1
    have h := hsa.2.2 ⟨φ, hφ'⟩ ⟨ψ, hψ'⟩
    have hv := hA'.2 ⟨ψ, hψ'⟩
    simp only at hv h
    rw [hv, (hsub ψ).2] at h
    exact h
  exact ⟨pushforwardToLine F q mq, isSpectralMeasureFor_pushforwardToLine hC F q mq
    ⟨fun ψ => ⟨fun h => (hsub ⟨ψ, h⟩).1, hdom ψ⟩, fun ψ => ((hsub ψ).2).symm⟩⟩
theorem exists_isSpectralMeasureFor (hJ : JointSpectralTheorem) :
    ∃ E : SpectralMeasure RealLineSet H, IsSpectralMeasureFor E A := by
  obtain ⟨R, hR, hRn⟩ := exists_boundedInverse hA (z := Complex.I) (by simp) (by simp)
  obtain ⟨R', hR', -⟩ := exists_boundedInverse hA (z := -Complex.I) (by simp) (by simp)
  obtain ⟨hker, -, -, hr₁, hr₂⟩ := resolvent_relations hA hR hR'
  have hne : (-2 * Complex.I : ℂ) ≠ 0 := by simp
  have hcomm : Commute R (star R) :=
    (smul_right_injective _ hne (hr₁.symm.trans hr₂)).symm
  have hnS : ‖star R‖ ≤ 1 := by rwa [norm_star]
  let Re : H →L[ℂ] H := (1 / 2 : ℂ) • (R + star R)
  let Im : H →L[ℂ] H := (-Complex.I / 2) • (R - star R)
  have sRe : IsSelfAdjoint Re := by
    rw [isSelfAdjoint_iff]
    simp only [Re, star_smul, star_add, star_star]
    rw [add_comm]
    simp
  have sIm : IsSelfAdjoint Im := by
    rw [isSelfAdjoint_iff]
    have hs : star (-Complex.I / 2 : ℂ) = Complex.I / 2 := by simp
    simp only [Im, star_smul, star_sub, star_star, hs]
    module
  have nRe : ‖Re‖ ≤ 1 := by
    have h₂ := norm_add_le R (star R)
    simp only [Re, norm_smul]
    norm_num
    linarith
  have nIm : ‖Im‖ ≤ 1 := by
    have h₂ := norm_sub_le R (star R)
    simp only [Im, norm_smul]
    simp
    linarith
  have cReIm : Commute Re Im := by
    have c₁ : Commute (R + star R) (R - star R) :=
      ((Commute.refl R).add_left hcomm.symm).sub_right (hcomm.add_left (Commute.refl _))
    exact (c₁.smul_left _).smul_right _
  let T : Fin 2 → H →L[ℂ] H := ![Re, Im]
  have hbox : IsCommutingInBox T (fun _ => -1) (fun _ => 1) := by
    refine ⟨?_, ?_, fun _ => by norm_num, ?_, ?_⟩
    · intro i
      fin_cases i
      · exact sRe
      · exact sIm
    · intro i j
      fin_cases i <;> fin_cases j
      · exact Commute.refl _
      · exact cReIm
      · exact cReIm.symm
      · exact Commute.refl _
    · intro i
      fin_cases i
      · exact (neg_const_le_and_le_const_of_norm_le sRe nRe).1
      · exact (neg_const_le_and_le_const_of_norm_le sIm nIm).1
    · intro i
      fin_cases i
      · exact (neg_const_le_and_le_const_of_norm_le sRe nRe).2
      · exact (neg_const_le_and_le_const_of_norm_le sIm nIm).2
  obtain ⟨F, hF, -⟩ := ((hJ H 2 (by norm_num)).1 T _ _ hbox).1
  refine exists_spectralMeasure_of_resolvent hC hA hR hker hr₁ F (fun y i => ?_)
    (hF 0).symm (hF 1).symm
  have h := y.2 i (mem_univ i)
  rw [Complex.norm_real, Real.norm_eq_abs, abs_le]
  exact h
end Existence
def resolventFn (y : RealLineSet) : ℂ := (coordVar y + Complex.I)⁻¹
theorem coordVar_add_I_ne_zero (y : RealLineSet) : coordVar y + Complex.I ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  simp [coordVar] at this
theorem norm_resolventFn_le_one (y : RealLineSet) : ‖resolventFn y‖ ≤ 1 := by
  rw [resolventFn, norm_inv]
  apply inv_le_one_of_one_le₀
  have := Complex.abs_im_le_norm (coordVar y + Complex.I)
  simpa [coordVar] using this
theorem isBoundedFn_resolventFn : IsBoundedFn resolventFn :=
  ⟨1, norm_resolventFn_le_one⟩
theorem measurable_resolventFn : Measurable resolventFn :=
  (measurable_coordVar.add measurable_const).inv
theorem re_im_inv_ofReal_add_I (l : ℝ) :
    (((l : ℂ) + Complex.I)⁻¹).re = l / (l ^ 2 + 1) ∧
      (((l : ℂ) + Complex.I)⁻¹).im = -1 / (l ^ 2 + 1) := by
  have hn : Complex.normSq ((l : ℂ) + Complex.I) = l ^ 2 + 1 := by
    simp [Complex.normSq_apply]
    ring
  rw [Complex.inv_re, Complex.inv_im, hn]
  simp
theorem ofReal_im_eq_combination (z : ℂ) :
    ((z.im : ℝ) : ℂ) = (-Complex.I / 2) * z + (Complex.I / 2) * conj z := by
  apply Complex.ext <;> simp <;> ring
theorem ofReal_re_eq_combination (z : ℂ) :
    ((z.re : ℝ) : ℂ) = (1 / 2 : ℂ) * z + (1 / 2 : ℂ) * conj z := by
  apply Complex.ext <;> simp <;> ring
section Uniqueness
variable {A : UnboundedOp H} (hC : BorelCalculusTheorem)
include hC
theorem integralOp_resolventFn {R : H →L[ℂ] H}
    (hR : IsBoundedInverse R (addConst A Complex.I)) {E : SpectralMeasure RealLineSet H}
    (hE : IsSpectralMeasureFor E A) : E.integralOp resolventFn = R := by
  have bc := boundedCalculus_of hC E
  have uc := unboundedCalculus_of hC E
  have mh := measurable_resolventFn
  have bh := isBoundedFn_resolventFn
  have hlh : (coordVar : RealLineSet → ℂ) * resolventFn =
      1 + (-Complex.I) • resolventFn := by
    funext y
    have h := coordVar_add_I_ne_zero y
    simp only [Pi.mul_apply, Pi.add_apply, Pi.one_apply, Pi.smul_apply, smul_eq_mul,
      resolventFn]
    field_simp
    ring
  have blh : IsBoundedFn ((coordVar : RealLineSet → ℂ) * resolventFn) := by
    rw [hlh]
    exact isBoundedFn_add isBoundedFn_one (isBoundedFn_smul _ bh)
  have hI : E.integralOp ((coordVar : RealLineSet → ℂ) * resolventFn) =
      1 + (-Complex.I) • E.integralOp resolventFn := by
    rw [hlh, bc.add (1 : RealLineSet → ℂ) ((-Complex.I) • resolventFn) measurable_const
      isBoundedFn_one (mh.const_smul _) (isBoundedFn_smul _ bh), bc.smul _ _ mh bh,
      integralOp_one hC]
  refine ContinuousLinearMap.ext fun ψ => ?_
  have hr := uc.range_subset_dom coordVar resolventFn measurable_coordVar mh bh blh ψ
  let a : A.domain := ⟨E.integralOp resolventFn ψ, (hE.1 _).2 hr.1⟩
  have ha : A a = E.integralApply coordVar (E.integralOp resolventFn ψ) := hE.2 a
  have hv : A a + Complex.I • (a : H) = ψ := by
    rw [ha, hr.2, hI]
    show ψ + (-Complex.I) • E.integralOp resolventFn ψ +
      Complex.I • E.integralOp resolventFn ψ = ψ
    module
  have h := boundedInverse_apply_op_add hR a
  rw [hv] at h
  exact h.symm
theorem integralOp_re_resolventFn {R : H →L[ℂ] H}
    (hR : IsBoundedInverse R (addConst A Complex.I)) {E : SpectralMeasure RealLineSet H}
    (hE : IsSpectralMeasureFor E A) :
    E.integralOp (fun y => (((resolventFn y).re : ℝ) : ℂ)) =
      (1 / 2 : ℂ) • R + (1 / 2 : ℂ) • star R := by
  have bc := boundedCalculus_of hC E
  have mh := measurable_resolventFn
  have bh := isBoundedFn_resolventFn
  have hf : (fun y => (((resolventFn y).re : ℝ) : ℂ)) =
      (1 / 2 : ℂ) • resolventFn + (1 / 2 : ℂ) • conjFn resolventFn :=
    funext fun y => ofReal_re_eq_combination _
  rw [hf, bc.add _ _ (mh.const_smul _) (isBoundedFn_smul _ bh)
    ((measurable_conjFn mh).const_smul _) (isBoundedFn_smul _ (isBoundedFn_conjFn bh)),
    bc.smul _ _ mh bh, bc.smul _ _ (measurable_conjFn mh) (isBoundedFn_conjFn bh),
    bc.star_eq _ mh bh, integralOp_resolventFn hC hR hE]
theorem integralOp_im_resolventFn {R : H →L[ℂ] H}
    (hR : IsBoundedInverse R (addConst A Complex.I)) {E : SpectralMeasure RealLineSet H}
    (hE : IsSpectralMeasureFor E A) :
    E.integralOp (fun y => (((resolventFn y).im : ℝ) : ℂ)) =
      (-Complex.I / 2) • R + (Complex.I / 2) • star R := by
  have bc := boundedCalculus_of hC E
  have mh := measurable_resolventFn
  have bh := isBoundedFn_resolventFn
  have hf : (fun y => (((resolventFn y).im : ℝ) : ℂ)) =
      (-Complex.I / 2) • resolventFn + (Complex.I / 2) • conjFn resolventFn :=
    funext fun y => ofReal_im_eq_combination _
  rw [hf, bc.add _ _ (mh.const_smul _) (isBoundedFn_smul _ bh)
    ((measurable_conjFn mh).const_smul _) (isBoundedFn_smul _ (isBoundedFn_conjFn bh)),
    bc.smul _ _ mh bh, bc.smul _ _ (measurable_conjFn mh) (isBoundedFn_conjFn bh),
    bc.star_eq _ mh bh, integralOp_resolventFn hC hR hE]
theorem isSpectralMeasureFor_unique (hJ : JointSpectralTheorem)
    {R : H →L[ℂ] H} (hR : IsBoundedInverse R (addConst A Complex.I))
    {E E' : SpectralMeasure RealLineSet H} (hE : IsSpectralMeasureFor E A)
    (hE' : IsSpectralMeasureFor E' A) : E = E' := by
  have mh := measurable_resolventFn
  let ι : RealLineSet → Fin 2 → ℝ := fun y => ![(resolventFn y).re, (resolventFn y).im]
  let κ : (Fin 2 → ℝ) → RealLineSet := fun y =>
    ⟨fun _ => if y 1 = 0 then 0 else -(y 0) / (y 1), mem_univ _⟩
  refine (hJ H 2 (by norm_num)).2 1 RealLineSet E E' ι κ ?_ ⟨1, fun y => ?_⟩ ?_ (fun y => ?_)
    (fun i => ?_)
  · refine measurable_pi_iff.2 fun i => ?_
    fin_cases i
    · exact Complex.measurable_re.comp mh
    · exact Complex.measurable_im.comp mh
  · refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => ?_
    have hn := norm_resolventFn_le_one y
    fin_cases i
    · exact (Complex.abs_re_le_norm _).trans hn
    · exact (Complex.abs_im_le_norm _).trans hn
  · refine Measurable.subtype_mk (measurable_pi_iff.2 fun _ => ?_)
    exact Measurable.ite (measurableSet_eq_fun (measurable_pi_apply 1) measurable_const)
      measurable_const ((measurable_pi_apply 0).neg.div (measurable_pi_apply 1))
  · refine Subtype.ext (funext fun i => ?_)
    have hi : i = 0 := Subsingleton.elim _ _
    subst hi
    obtain ⟨h₁, h₂⟩ := re_im_inv_ofReal_add_I (y.1 0)
    have hpos : (y.1 0) ^ 2 + 1 ≠ 0 := by positivity
    have e₁ : ι y 0 = y.1 0 / ((y.1 0) ^ 2 + 1) := h₁
    have e₂ : ι y 1 = -1 / ((y.1 0) ^ 2 + 1) := h₂
    show (if ι y 1 = 0 then 0 else -(ι y 0) / (ι y 1)) = y.1 0
    have hne : ι y 1 ≠ 0 := by
      rw [e₂]
      exact div_ne_zero (by norm_num) hpos
    rw [if_neg hne, e₁, e₂]
    field_simp
  · fin_cases i
    · exact (integralOp_re_resolventFn hC hR hE).trans (integralOp_re_resolventFn hC hR hE').symm
    · exact (integralOp_im_resolventFn hC hR hE).trans (integralOp_im_resolventFn hC hR hE').symm
end Uniqueness
theorem isPositive_of_isPositiveOp {P : H →L[ℂ] H} (h : IsPositiveOp P) : P.IsPositive := by
  refine (ContinuousLinearMap.isPositive_iff' P).2 ⟨h.1, fun x => ?_⟩
  have hs := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.1 h.1
  have h₁ : ⟪P x, x⟫_ℂ = ⟪x, P x⟫_ℂ := hs x x
  rw [h₁]
  exact h.2 x
theorem isSpectralMeasureFor_extendCarrier (hC : BorelCalculusTheorem) {B : H →L[ℂ] H}
    {a b : Fin 1 → ℝ} (F : SpectralMeasure (closedBox a b) H)
    (hF : IsJointRepresentation F fun _ : Fin 1 => B) :
    IsSpectralMeasureFor (F.extendCarrier (subset_univ _) MeasurableSet.univ) (ofBounded B) := by
  have h := (pushforwardProperties_of hC F).integral_pushforward F.one_le_dimension
    MeasurableSet.univ (inclusion (subset_univ _)) measurable_subtype_coe.subtype_mk coordVar
    measurable_coordVar
  have hb : ∀ y : closedBox a b, ‖(coordVar ∘ inclusion (subset_univ (closedBox a b))) y‖ ≤
      |a 0| + |b 0| := by
    intro y
    have hy := y.2 0 (mem_univ 0)
    show ‖((y.1 0 : ℝ) : ℂ)‖ ≤ _
    rw [Complex.norm_real, Real.norm_eq_abs, abs_le]
    have h₁ := neg_abs_le (a 0)
    have h₂ := le_abs_self (b 0)
    have h₃ := abs_nonneg (a 0)
    have h₄ := abs_nonneg (b 0)
    exact ⟨by linarith [hy.1], by linarith [hy.2]⟩
  have hdom := F.integralDom_eq_univ hb
  refine ⟨fun ψ => ?_, fun ψ => ?_⟩
  · constructor
    · intro _
      show ψ ∈ (F.extendCarrier (subset_univ _) MeasurableSet.univ).integralDom coordVar
      have h₁ := h.1
      rw [hdom] at h₁
      exact h₁ ▸ mem_univ ψ
    · intro _
      exact Submodule.mem_top
  · have hm : (ψ : H) ∈ F.integralDom (coordVar ∘ inclusion (subset_univ _)) := by
      rw [hdom]
      exact mem_univ _
    have h₂ := h.2 ψ hm
    refine Eq.trans ?_ h₂.symm
    rw [F.integralApply_eq_integralOp hb]
    have h₃ := hF 0
    exact congrArg (fun T : H →L[ℂ] H => T (ψ : H)) h₃
theorem spectralTheoremHolds_of (hC : BorelCalculusTheorem) (hJ : JointSpectralTheorem) :
    SpectralTheoremHolds := by
  intro H _ _ _ A hA
  have hI₁ : Complex.I.re = 0 := by simp
  have hI₂ : ‖Complex.I‖ = 1 := by simp
  have hJ₁ : (-Complex.I).re = 0 := by simp
  have hJ₂ : ‖-Complex.I‖ = 1 := by simp
  obtain ⟨R, hR, hRn⟩ := exists_boundedInverse hA hI₁ hI₂
  obtain ⟨R', hR', -⟩ := exists_boundedInverse hA hJ₁ hJ₂
  obtain ⟨hker, hran, hstar, hr₁, hr₂⟩ := resolvent_relations hA hR hR'
  have hex := exists_isSpectralMeasureFor hC hA hJ
  have huniq : ∀ E E' : SpectralMeasure RealLineSet H, IsSpectralMeasureFor E A →
      IsSpectralMeasureFor E' A → E = E' := fun E E' hE hE' =>
    isSpectralMeasureFor_unique hC hJ hR hE hE'
  have hspec : IsSpectralMeasureFor (spectralMeasure A) A := by
    unfold spectralMeasure
    exact Classical.epsilon_spec hex
  refine ⟨fun ψ => ⟨norm_op_add_smul_sq hA hI₁ hI₂ ψ, ?_⟩,
    ⟨addConst_injective hA hI₁ hI₂, addConst_surjective hA hI₁ hI₂⟩,
    ⟨addConst_injective hA hJ₁ hJ₂, addConst_surjective hA hJ₁ hJ₂⟩,
    ⟨R, R', hR, hR', hRn, hker, hran, hstar, hr₁, hr₂⟩,
    ⟨spectralMeasure A, hspec, fun E hE => huniq _ _ hE hspec⟩, hspec, ?_, ?_, ?_⟩
  · have h := norm_op_add_smul_sq hA hJ₁ hJ₂ ψ
    rwa [neg_smul, ← sub_eq_add_neg] at h
  · intro n Y E g hg hI
    have hE := isSpectralMeasureFor_pushforwardToLine hC E g hg hI
    have heq : spectralMeasure A = pushforwardToLine E g hg := huniq _ _ hspec hE
    refine ⟨heq, fun f hf => ?_⟩
    rw [heq]
    have h := pushforwardToLine_integral hC E g hg (fun y => f (y.1 0))
      (hf.comp ((measurable_pi_apply 0).comp measurable_subtype_coe))
    unfold IntegralsAgree
    exact ⟨h.1, fun ψ hψ => h.2 ψ (h.1 ▸ hψ)⟩
  · have ks := (kernelAndPositivity_of hC (spectralMeasure A)).nonneg_iff coordVar
      measurable_coordVar (fun y => Complex.ofReal_im _)
    have hset : negativeLocus measurable_coordVar = realLineSet negHalfLine :=
      Subtype.ext (by
        ext y
        simp [negativeLocus, realLineSet, negHalfLine, coordVar])
    rw [← hset, ← ks]
    constructor
    · rintro ⟨-, h⟩ ψ hψ
      have hd := (hspec.1 ψ).2 hψ
      have h₁ := h ⟨ψ, hd⟩
      rw [hspec.2 ⟨ψ, hd⟩] at h₁
      exact h₁
    · intro h
      refine ⟨hA, fun ψ => ?_⟩
      rw [hspec.2 ψ]
      exact h ψ ((hspec.1 ψ).1 ψ.2)
  · intro B γ γ' hAB hγ hl hu
    subst hAB
    have sB : IsSelfAdjoint B := hl.1
    have hbox₁ : IsCommutingInBox (fun _ : Fin 1 => B)
        (normBoundLower fun _ : Fin 1 => B) (normBoundUpper fun _ : Fin 1 => B) := by
      refine ⟨fun _ => sB, fun _ _ => Commute.refl _,
        normBoundLower_lt_normBoundUpper _, fun _ => ?_, fun _ => ?_⟩
      · exact (neg_const_le_and_le_const_of_norm_le sB (le_add_of_nonneg_right zero_le_one)).1
      · exact (neg_const_le_and_le_const_of_norm_le sB (le_add_of_nonneg_right zero_le_one)).2
    have hbox₂ : IsCommutingInBox (fun _ : Fin 1 => B) (fun _ => γ) (fun _ => γ') := by
      refine ⟨fun _ => sB, fun _ _ => Commute.refl _, fun _ => hγ, fun _ => ?_, fun _ => ?_⟩
      · rw [ContinuousLinearMap.le_def]
        exact isPositive_of_isPositiveOp hl.2.2
      · rw [ContinuousLinearMap.le_def]
        exact isPositive_of_isPositiveOp hu.2.2
    have hrep := ((hJ H 1 le_rfl).1 (fun _ => B) _ _ hbox₁).2.1
    have hs₁ := isSpectralMeasureFor_extendCarrier hC _ hrep
    obtain ⟨F₂, hF₂, -⟩ := ((hJ H 1 le_rfl).1 (fun _ => B) _ _ hbox₂).1
    have hs₂ := isSpectralMeasureFor_extendCarrier hC _ hF₂
    refine ⟨huniq _ _ hspec hs₁, ?_⟩
    rw [huniq _ _ hspec hs₂]
    have hc := F₂.extendCarrier_isCarriedBy (subset_univ _) MeasurableSet.univ
    have hset : realLineSet ⟨Icc γ γ', measurableSet_Icc⟩ =
        ⟨Subtype.val ⁻¹' closedBox (fun _ : Fin 1 => γ) (fun _ => γ'),
          measurable_subtype_coe F₂.measurableSet_carrier⟩ :=
      Subtype.ext (by
        ext y
        constructor
        · intro h i _
          rw [Subsingleton.elim i 0]
          exact h
        · intro h
          exact h 0 (mem_univ 0))
    rw [hset]
    exact hc
end YangMills.Construction.SpectralTheorem
