import YangMills.Construction.HilbertSpace.BoundedOperatorFacts
import Mathlib
set_option autoImplicit false
open Set Filter Topology
open scoped ComplexConjugate ComplexOrder InnerProductSpace
noncomputable section
namespace YangMills.Construction.BoundedOperators
open HilbertSpaceBasics (IsSesquilinear IsPosSemidef FormSpace completionClass formNullSet)
open EuclideanSpectral
section Forms
variable {V : Type} [AddCommGroup V] [Module ℂ V] {s : V → V → ℂ}
theorem sesquilinear_polarization (hs : IsSesquilinear s) (x y : V) :
    4 * s x y = s (x + y) (x + y) - s (x - y) (x - y) -
      Complex.I * s (x + Complex.I • y) (x + Complex.I • y) +
      Complex.I * s (x - Complex.I • y) (x - Complex.I • y) := by
  have e₁ : x - y = x + (-1 : ℂ) • y := by simp [sub_eq_add_neg]
  have e₂ : x - Complex.I • y = x + (-Complex.I) • y := by simp [sub_eq_add_neg]
  rw [e₁, e₂]
  simp only [hs.add_left, hs.add_right, hs.smul_left, hs.smul_right, map_neg, map_one,
    Complex.conj_I]
  linear_combination (2 * (s x y - s y x)) * Complex.I_sq
theorem sesquilinear_conj_symm_of_im_diag (hs : IsSesquilinear s) (hr : ∀ x, (s x x).im = 0)
    (x y : V) : s y x = conj (s x y) := by
  have d₁ := hr x
  have d₂ := hr y
  have s₁ := hr (x + y)
  have s₂ := hr (x + Complex.I • y)
  rw [hs.add_left, hs.add_right, hs.add_right] at s₁
  rw [hs.add_left, hs.add_right, hs.add_right, hs.smul_left, hs.smul_left, hs.smul_right,
    hs.smul_right] at s₂
  simp only [Complex.add_im, Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.I_re,
    Complex.I_im, Complex.mul_re] at s₁ s₂
  apply Complex.ext
  · simp only [Complex.conj_re]
    linarith
  · simp only [Complex.conj_im]
    linarith
def toFormSpace (h : IsPosSemidef s) (x : V) : FormSpace s h := x
theorem formDiag_eq_norm_sq (h : IsPosSemidef s) (x : V) :
    s x x = ((‖toFormSpace h x‖ ^ 2 : ℝ) : ℂ) := by
  have hn := Complex.le_def.mp (h.nonneg x)
  have hre : (s x x).re = ‖toFormSpace h x‖ ^ 2 :=
    inner_self_eq_norm_sq (𝕜 := ℂ) (toFormSpace h x)
  apply Complex.ext
  · rw [hre, Complex.ofReal_re]
  · rw [Complex.ofReal_im]
    exact hn.2.symm
theorem posSemidef_cauchy_schwarz (h : IsPosSemidef s) (x y : V) :
    ‖s x y‖ ^ 2 ≤ ‖toFormSpace h x‖ ^ 2 * ‖toFormSpace h y‖ ^ 2 := by
  have hle : ‖s x y‖ ≤ ‖toFormSpace h x‖ * ‖toFormSpace h y‖ :=
    norm_inner_le_norm (𝕜 := ℂ) (toFormSpace h x) (toFormSpace h y)
  rw [← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) hle 2
theorem mem_formNullSet_iff (h : IsPosSemidef s) (x : V) :
    x ∈ formNullSet s ↔ ‖toFormSpace h x‖ = 0 := by
  show s x x = 0 ↔ _
  rw [formDiag_eq_norm_sq h x]
  simp
def formNullSubmodule (h : IsPosSemidef s) : Submodule ℂ V where
  carrier := formNullSet s
  add_mem' := by
    intro x y hx hy
    rw [mem_formNullSet_iff h] at hx hy ⊢
    have hle : ‖toFormSpace h (x + y)‖ ≤ ‖toFormSpace h x‖ + ‖toFormSpace h y‖ :=
      norm_add_le (toFormSpace h x) (toFormSpace h y)
    rw [hx, hy, add_zero] at hle
    exact le_antisymm hle (norm_nonneg _)
  zero_mem' := by
    rw [mem_formNullSet_iff h]
    exact norm_zero (E := FormSpace s h)
  smul_mem' := by
    intro z x hx
    rw [mem_formNullSet_iff h] at hx ⊢
    have he : ‖toFormSpace h (z • x)‖ = ‖z‖ * ‖toFormSpace h x‖ :=
      norm_smul (β := FormSpace s h) z (toFormSpace h x)
    rw [he, hx, mul_zero]
theorem norm_completionClass (h : IsPosSemidef s) (x : V) :
    ‖completionClass s h x‖ = ‖toFormSpace h x‖ :=
  UniformSpace.Completion.norm_coe (toFormSpace h x)
theorem posSemidef_completion_facts (h : IsPosSemidef s) :
    (∀ x y : V, ((‖s x y‖ ^ 2 : ℝ) : ℂ) ≤ s x x * s y y) ∧
    (∃ N : Submodule ℂ V, (N : Set V) = formNullSet s) ∧
    Dense (range (completionClass s h)) ∧
    (∀ x y : V, ⟪completionClass s h x, completionClass s h y⟫_ℂ = s x y) ∧
    ∀ x y : V, completionClass s h x = completionClass s h y ↔ x - y ∈ formNullSet s := by
  refine ⟨?_, ⟨formNullSubmodule h, rfl⟩, ?_, ?_, ?_⟩
  · intro x y
    rw [formDiag_eq_norm_sq h x, formDiag_eq_norm_sq h y, ← Complex.ofReal_mul,
      Complex.real_le_real]
    exact posSemidef_cauchy_schwarz h x y
  · exact UniformSpace.Completion.denseRange_coe (α := FormSpace s h)
  · intro x y
    exact UniformSpace.Completion.inner_coe (toFormSpace h x) (toFormSpace h y)
  · intro x y
    rw [mem_formNullSet_iff h, ← norm_completionClass h, map_sub, norm_eq_zero, sub_eq_zero]
end Forms
section Operators
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
omit [CompleteSpace H] in
theorem isSesquilinear_inner_apply (B : H →L[ℂ] H) :
    IsSesquilinear fun u v : H => ⟪u, B v⟫_ℂ where
  add_left a b c := inner_add_left _ _ _
  smul_left z a b := inner_smul_left _ _ _
  add_right a b c := by simp only [map_add, inner_add_right]
  smul_right z a b := by simp only [map_smul, inner_smul_right]
omit [CompleteSpace H] in
theorem isSesquilinear_inner_comp {V : Type} [AddCommGroup V] [Module ℂ V] (T : V →ₗ[ℂ] H) :
    IsSesquilinear fun x y : V => ⟪T x, T y⟫_ℂ where
  add_left a b c := by simp only [map_add, inner_add_left]
  smul_left z a b := by simp only [map_smul, inner_smul_left]
  add_right a b c := by simp only [map_add, inner_add_right]
  smul_right z a b := by simp only [map_smul, inner_smul_right]
theorem isAdjointPair_iff_eq_star (B B' : H →L[ℂ] H) : IsAdjointPair B B' ↔ B' = star B := by
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.eq_adjoint_iff]
  exact ⟨fun h x y => (h x y).symm, fun h x y => (h x y).symm⟩
omit [CompleteSpace H] in
theorem inner_map_eq_of_norm_sq_eq {V : Type} [AddCommGroup V] [Module ℂ V] {s : V → V → ℂ}
    (hs : IsSesquilinear s) (T : V →ₗ[ℂ] H) (hT : ∀ x, ((‖T x‖ ^ 2 : ℝ) : ℂ) = s x x)
    (x y : V) : ⟪T x, T y⟫_ℂ = s x y := by
  have hd : ∀ z, ⟪T z, T z⟫_ℂ = s z z := by
    intro z
    rw [← hT z, inner_self_eq_norm_sq_to_K]
    push_cast
    rfl
  have h₁ := sesquilinear_polarization (isSesquilinear_inner_comp T) x y
  have h₂ := sesquilinear_polarization hs x y
  simp only [hd] at h₁
  have h₃ : (4 : ℂ) * ⟪T x, T y⟫_ℂ = 4 * s x y := h₁.trans h₂.symm
  exact mul_left_cancel₀ (by norm_num) h₃
theorem exists_inverse_adjoint_of_unitary (U : H →L[ℂ] H) (hU : IsUnitaryOp U) :
    ∃ U' : H →L[ℂ] H, U' * U = 1 ∧ U * U' = 1 ∧ IsAdjointPair U U' := by
  have hiso : ∀ u v : H, ⟪U u, U v⟫_ℂ = ⟪u, v⟫_ℂ := by
    intro u v
    refine inner_map_eq_of_norm_sq_eq (s := fun u v : H => ⟪u, v⟫_ℂ) ?_ U.toLinearMap ?_ u v
    · simpa using isSesquilinear_inner_apply (1 : H →L[ℂ] H)
    · intro x
      show ((‖U x‖ ^ 2 : ℝ) : ℂ) = ⟪x, x⟫_ℂ
      rw [hU.norm_map x, inner_self_eq_norm_sq_to_K]
      push_cast
      rfl
  have h₁ : star U * U = 1 := by
    refine ContinuousLinearMap.ext fun v => ext_inner_right ℂ fun u => ?_
    show ⟪star U (U v), u⟫_ℂ = ⟪v, u⟫_ℂ
    rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left, hiso]
  have h₂ : U * star U = 1 := by
    refine ContinuousLinearMap.ext fun v => ?_
    obtain ⟨w, rfl⟩ := hU.bijective.2 v
    have hw : star U (U w) = w := by
      have := congrArg (fun T : H →L[ℂ] H => T w) h₁
      simpa using this
    simp [hw]
  exact ⟨star U, h₁, h₂, (isAdjointPair_iff_eq_star U _).2 rfl⟩
omit [CompleteSpace H] in
theorem forall_of_dense_submodule {D : Submodule ℂ H} (hD : Dense (D : Set H)) {P : H → Prop}
    (hc : IsClosed {v | P v}) (h : ∀ v : D, P v) (v : H) : P v := by
  have hsub : (D : Set H) ⊆ {v | P v} := fun w hw => h ⟨w, hw⟩
  have := closure_minimal hsub hc
  rw [hD.closure_eq] at this
  exact this (mem_univ v)
theorem dense_submodule_facts (D : Submodule ℂ H) (hD : Dense (D : Set H)) :
    (∀ (c : ℝ) (B₀ : D →ₗ[ℂ] H), 0 ≤ c → (∀ v : D, ‖B₀ v‖ ≤ c * ‖(v : H)‖) →
      ∃ B : H →L[ℂ] H, (∀ v : D, B v = B₀ v) ∧ ‖B‖ ≤ c ∧
        ∀ B' : H →L[ℂ] H, (∀ v : D, B' v = B₀ v) → B' = B) ∧
    (∀ B B' : H →L[ℂ] H, (∀ v : D, B v = B' v) → B = B') ∧
    (∀ B B' : H →L[ℂ] H, (∀ u v : D, ⟪(u : H), B v⟫_ℂ = ⟪B' u, (v : H)⟫_ℂ) →
      IsAdjointPair B B') ∧
    ∀ B : H →L[ℂ] H, IsSelfAdjointOp B → (∀ v : D, 0 ≤ (⟪(v : H), B v⟫_ℂ).re) →
      OpGe B (scalarOp 0) := by
  have hagree : ∀ B B' : H →L[ℂ] H, (∀ v : D, B v = B' v) → B = B' := fun B B' h =>
    ContinuousLinearMap.ext (forall_of_dense_submodule hD (isClosed_eq B.continuous B'.continuous) h)
  refine ⟨?_, hagree, ?_, ?_⟩
  · intro c B₀ hc hb
    let f : D →L[ℂ] H := B₀.mkContinuous c hb
    have hdense : DenseRange (D.subtypeL) := hD.denseRange_val
    have hind : IsUniformInducing (D.subtypeL) := isUniformEmbedding_subtype_val.isUniformInducing
    have hext : ∀ v : D, (f.extend D.subtypeL) v = B₀ v := fun v =>
      f.extend_eq hdense hind v
    refine ⟨f.extend D.subtypeL, hext, ?_, ?_⟩
    · refine ContinuousLinearMap.opNorm_le_bound _ hc ?_
      refine forall_of_dense_submodule hD (isClosed_le ?_ ?_) ?_
      · exact (f.extend D.subtypeL).continuous.norm
      · exact continuous_const.mul continuous_norm
      · intro v
        rw [hext v]
        exact hb v
    · intro B' hB'
      exact hagree _ _ fun v => (hB' v).trans (hext v).symm
  · intro B B' h u
    refine forall_of_dense_submodule hD (P := fun u => ∀ v, ⟪u, B v⟫_ℂ = ⟪B' u, v⟫_ℂ) ?_ ?_ u
    · have : {u | ∀ v, ⟪u, B v⟫_ℂ = ⟪B' u, v⟫_ℂ} = ⋂ v, {u | ⟪u, B v⟫_ℂ = ⟪B' u, v⟫_ℂ} := by
        ext u
        simp
      rw [this]
      refine isClosed_iInter fun v => isClosed_eq ?_ ?_
      · exact continuous_id.inner continuous_const
      · exact B'.continuous.inner continuous_const
    · intro u
      exact forall_of_dense_submodule hD
        (isClosed_eq (continuous_const.inner B.continuous)
          (continuous_const.inner continuous_id)) (h u)
  · intro B _ h
    refine forall_of_dense_submodule hD (P := fun v => (⟪v, scalarOp (0 : ℝ) v⟫_ℂ).re ≤
      (⟪v, B v⟫_ℂ).re) ?_ ?_
    · refine isClosed_le ?_ ?_
      · exact Complex.continuous_re.comp
          (continuous_id.inner (scalarOp (0 : ℝ) : H →L[ℂ] H).continuous)
      · exact Complex.continuous_re.comp (continuous_id.inner B.continuous)
    · intro v
      simpa [scalarOp] using h v
theorem norm_sq_eq_of_isStarNormal (C : H →L[ℂ] H) (hC : C * star C = star C * C) :
    ‖C ^ 2‖ = ‖C‖ ^ 2 := by
  have h₁ : star (C ^ 2) * C ^ 2 = star (star C * C) * (star C * C) := by
    rw [star_mul, star_star, star_pow, pow_two, pow_two]
    calc star C * star C * (C * C) = star C * (star C * C) * C := by
          simp only [mul_assoc]
      _ = star C * (C * star C) * C := by rw [hC]
      _ = star C * C * (star C * C) := by simp only [mul_assoc]
  have h₂ : ‖C ^ 2‖ * ‖C ^ 2‖ = (‖C‖ ^ 2) * (‖C‖ ^ 2) := by
    rw [← CStarRing.norm_star_mul_self, h₁, CStarRing.norm_star_mul_self,
      CStarRing.norm_star_mul_self, pow_two]
  have h₃ : ‖C ^ 2‖ ^ 2 = (‖C‖ ^ 2) ^ 2 := by
    rw [pow_two, h₂, pow_two (‖C‖ ^ 2)]
  exact (pow_left_inj₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h₃
theorem norm_pow_two_pow_eq_of_isStarNormal (B : H →L[ℂ] H) (hB : B * star B = star B * B)
    (k : ℕ) : ‖B ^ 2 ^ k‖ = ‖B‖ ^ 2 ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hcomm : Commute B (star B) := hB
    have hC : B ^ 2 ^ k * star (B ^ 2 ^ k) = star (B ^ 2 ^ k) * B ^ 2 ^ k := by
      rw [star_pow]
      exact (hcomm.pow_pow _ _).eq
    rw [pow_succ 2 k, pow_mul, pow_mul, norm_sq_eq_of_isStarNormal _ hC, ih]
theorem isAdjointPair_facts (B B' : H →L[ℂ] H) (h : IsAdjointPair B B') :
    IsAdjointPair B' B ∧ ‖B'‖ = ‖B‖ ∧ ‖B' * B‖ = ‖B‖ ^ 2 ∧
    (∀ B₁ B₁' : H →L[ℂ] H, IsAdjointPair B₁ B₁' →
      IsAdjointPair (B * B₁) (B₁' * B') ∧
      ∀ a a₁ : ℂ, IsAdjointPair (a • B + a₁ • B₁) (conj a • B' + conj a₁ • B₁')) ∧
    (B * B' = B' * B → ∀ k : ℕ, ‖B ^ 2 ^ k‖ = ‖B‖ ^ 2 ^ k) := by
  obtain rfl := (isAdjointPair_iff_eq_star B B').1 h
  refine ⟨(isAdjointPair_iff_eq_star _ _).2 (star_star B).symm, norm_star B, ?_, ?_,
    norm_pow_two_pow_eq_of_isStarNormal B⟩
  · rw [CStarRing.norm_star_mul_self, pow_two]
  · intro B₁ B₁' h₁
    obtain rfl := (isAdjointPair_iff_eq_star B₁ B₁').1 h₁
    refine ⟨(isAdjointPair_iff_eq_star _ _).2 (star_mul B B₁).symm, fun a a₁ => ?_⟩
    refine (isAdjointPair_iff_eq_star _ _).2 ?_
    simp only [star_add, star_smul]
    rfl
omit [CompleteSpace H] in
theorem isContractionOp_of_between_zero_one (B : H →L[ℂ] H) (hB : IsSelfAdjointOp B)
    (h₀ : OpGe B (scalarOp 0)) (h₁ : OpGe (scalarOp 1) B) : IsContractionOp B := by
  have hr : ∀ v : H, (⟪v, B v⟫_ℂ).im = 0 := by
    intro v
    have he : ⟪v, B v⟫_ℂ = conj ⟪v, B v⟫_ℂ := by
      rw [inner_conj_symm]
      exact hB v v
    exact Complex.conj_eq_iff_im.mp he.symm
  have hp : ∀ v : H, 0 ≤ (⟪v, B v⟫_ℂ).re := by
    intro v
    simpa [scalarOp] using h₀ v
  have hu : ∀ v : H, (⟪v, B v⟫_ℂ).re ≤ ‖v‖ ^ 2 := by
    intro v
    have hle := h₁ v
    have hn : (⟪v, v⟫_ℂ).re = ‖v‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) v
    have he : scalarOp (1 : ℝ) v = v := by simp [scalarOp]
    rwa [he, hn] at hle
  let hs : IsPosSemidef fun u v : H => ⟪u, B v⟫_ℂ :=
    { isSesquilinear_inner_apply B with
      nonneg := fun v => Complex.le_def.mpr ⟨hp v, (hr v).symm⟩ }
  have hdiag : ∀ v : H, ‖toFormSpace hs v‖ ^ 2 = (⟪v, B v⟫_ℂ).re := fun v =>
    (inner_self_eq_norm_sq (𝕜 := ℂ) (toFormSpace hs v)).symm
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => ?_
  rw [one_mul]
  have hcs := posSemidef_cauchy_schwarz hs (B v) v
  rw [hdiag, hdiag] at hcs
  have hself : ‖⟪B v, B v⟫_ℂ‖ = ‖B v‖ ^ 2 := by
    rw [inner_self_eq_norm_sq_to_K]
    simp
  have hcs' : ‖B v‖ ^ 2 * ‖B v‖ ^ 2 ≤ ‖B v‖ ^ 2 * ‖v‖ ^ 2 := by
    have e : ‖⟪B v, B v⟫_ℂ‖ ^ 2 ≤ (⟪B v, B (B v)⟫_ℂ).re * (⟪v, B v⟫_ℂ).re := hcs
    rw [hself] at e
    calc ‖B v‖ ^ 2 * ‖B v‖ ^ 2 = (‖B v‖ ^ 2) ^ 2 := (pow_two _).symm
      _ ≤ _ := e
      _ ≤ ‖B v‖ ^ 2 * ‖v‖ ^ 2 :=
        mul_le_mul (hu _) (hu _) (hp _) (by positivity)
  by_contra hlt
  have hlt' : ‖v‖ < ‖B v‖ := not_le.mp hlt
  have hpos : 0 < ‖B v‖ := lt_of_le_of_lt (norm_nonneg _) hlt'
  have hsq : ‖v‖ ^ 2 < ‖B v‖ ^ 2 := pow_lt_pow_left₀ hlt' (norm_nonneg _) two_ne_zero
  have := mul_lt_mul_of_pos_left hsq (by positivity : 0 < ‖B v‖ ^ 2)
  linarith
omit [CompleteSpace H] in
theorem eq_of_isOrthProjection_of_fixedSet_eq (B B' : H →L[ℂ] H) (hB : IsOrthProjection B)
    (hB' : IsOrthProjection B') (hr : fixedSet B = fixedSet B') : B = B' := by
  have hmem : ∀ {P : H →L[ℂ] H}, IsOrthProjection P → ∀ v, P v ∈ fixedSet P := by
    intro P hP v
    exact congrArg (fun T : H →L[ℂ] H => T v) hP.idempotent
  have horth : ∀ {P : H →L[ℂ] H}, IsOrthProjection P → ∀ u ∈ fixedSet P, ∀ v,
      ⟪u, v - P v⟫_ℂ = 0 := by
    intro P hP u hu v
    have e₁ : P u = u := hu
    have e₂ : P (P v) = P v := hmem hP v
    have e₃ := hP.selfAdjoint u (v - P v)
    rw [e₁, map_sub, e₂, sub_self, inner_zero_right] at e₃
    exact e₃.symm
  refine ContinuousLinearMap.ext fun v => ?_
  have h₁ : B v ∈ fixedSet B := hmem hB v
  have h₂ : B' v ∈ fixedSet B := hr ▸ hmem hB' v
  have hd : B v - B' v ∈ fixedSet B := by
    show B (B v - B' v) = B v - B' v
    rw [map_sub, show B (B v) = B v from h₁, show B (B' v) = B' v from h₂]
  have hd' : B v - B' v ∈ fixedSet B' := hr ▸ hd
  have hz : ⟪B v - B' v, B v - B' v⟫_ℂ = 0 := by
    have e : B v - B' v = (v - B' v) - (v - B v) := by abel
    have e₁ := horth hB' _ hd' v
    have e₂ := horth hB _ hd v
    calc ⟪B v - B' v, B v - B' v⟫_ℂ = ⟪B v - B' v, (v - B' v) - (v - B v)⟫_ℂ := by rw [← e]
      _ = 0 := by rw [inner_sub_right, e₁, e₂, sub_zero]
  exact sub_eq_zero.mp (inner_self_eq_zero.mp hz)
end Operators
theorem boundedOperatorFacts_proof : BoundedOperatorFacts := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro V _ _ s hs
    exact ⟨sesquilinear_polarization hs, sesquilinear_conj_symm_of_im_diag hs⟩
  · intro V _ _ s h
    exact posSemidef_completion_facts h
  · intro H _ _ _
    refine ⟨?_, ?_, ?_, exists_inverse_adjoint_of_unitary⟩
    · intro B hB
      refine ContinuousLinearMap.ext fun v => ?_
      have hs := isSesquilinear_inner_apply B
      have h₄ := sesquilinear_polarization hs (B v) v
      simp only [hB, mul_zero, sub_zero, add_zero] at h₄
      have hz : ⟪B v, B v⟫_ℂ = 0 := by
        have : (4 : ℂ) * ⟪B v, B v⟫_ℂ = 0 := h₄
        simpa using this
      simpa using inner_self_eq_zero.mp hz
    · intro B hB u v
      have h₁ := sesquilinear_conj_symm_of_im_diag (isSesquilinear_inner_apply B) hB v u
      have h₂ : ⟪u, B v⟫_ℂ = conj ⟪v, B u⟫_ℂ := h₁
      rw [inner_conj_symm] at h₂
      exact h₂
    · intro V _ _ s hs T hT x y
      exact inner_map_eq_of_norm_sq_eq hs T hT x y
  · intro H _ _ _ D hD
    exact dense_submodule_facts D hD
  · intro H _ _ _ B B' h
    exact isAdjointPair_facts B B' h
  · intro H _ _ _ B hB h₀ h₁
    exact isContractionOp_of_between_zero_one B hB h₀ h₁
  · intro H _ _ _ B B' hB hB' hr
    exact eq_of_isOrthProjection_of_fixedSet_eq B B' hB hB' hr
end YangMills.Construction.BoundedOperators
