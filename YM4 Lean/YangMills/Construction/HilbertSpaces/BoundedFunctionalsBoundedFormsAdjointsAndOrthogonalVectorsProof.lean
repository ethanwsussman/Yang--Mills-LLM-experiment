import YangMills.Construction.HilbertSpaces.BoundedFunctionalsBoundedFormsAdjointsAndOrthogonalVectors
import Mathlib
set_option autoImplicit false
open scoped ComplexConjugate ComplexOrder InnerProductSpace
namespace YangMills.Construction.BoundedRepresentation
open FormsOperators
open EuclideanBorel (IsOrthoProjection)
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
theorem rieszAntilinear_of_nonneg (c : ℝ) (hc : 0 ≤ c) :
    RieszAntilinear H c := by
  intro ℓ hℓ
  let f : H →ₗ[ℂ] ℂ :=
    { toFun := fun χ => conj (ℓ χ)
      map_add' := fun x y => by simp
      map_smul' := fun a x => by simp }
  have hf : ∀ x, ‖f x‖ ≤ c * ‖x‖ := fun x => by
    show ‖conj (ℓ x)‖ ≤ _
    rw [RCLike.norm_conj]
    exact hℓ x
  have hrepr : ∀ χ, ℓ χ = ⟪χ, (InnerProductSpace.toDual ℂ H).symm (f.mkContinuous c hf)⟫_ℂ := by
    intro χ
    rw [← inner_conj_symm, InnerProductSpace.toDual_symm_apply]
    show ℓ χ = conj (conj (ℓ χ))
    simp
  refine ⟨(InnerProductSpace.toDual ℂ H).symm (f.mkContinuous c hf), hrepr, ?_, fun χ' h => ?_⟩
  · rw [LinearIsometryEquiv.norm_map]
    exact LinearMap.mkContinuous_norm_le f hc hf
  · exact ext_inner_left ℂ fun χ => (h χ).symm.trans (hrepr χ)
theorem boundedSesquilinearRepr_of_nonneg (c : ℝ) (hc : 0 ≤ c) :
    BoundedSesquilinearRepr H c := by
  intro q hq hb
  have hvec : ∀ ψ : H, ∃ v : H, (∀ φ, q φ ψ = ⟪φ, v⟫_ℂ) ∧ ‖v‖ ≤ c * ‖ψ‖ := by
    intro ψ
    let ℓ : H →ₛₗ[starRingEnd ℂ] ℂ :=
      { toFun := fun φ => q φ ψ
        map_add' := fun x y => hq.add_left x y ψ
        map_smul' := fun a x => by simpa using hq.smul_left a x ψ }
    have hℓ : ∀ φ, ‖ℓ φ‖ ≤ c * ‖ψ‖ * ‖φ‖ := fun φ => (hb φ ψ).trans_eq (by ring)
    obtain ⟨v, hv, hn, -⟩ :=
      rieszAntilinear_of_nonneg (H := H) (c * ‖ψ‖) (mul_nonneg hc (norm_nonneg ψ)) ℓ hℓ
    exact ⟨v, hv, hn⟩
  choose v hv hn using hvec
  let L : H →ₗ[ℂ] H :=
    { toFun := v
      map_add' := fun x y => ext_inner_left ℂ fun φ => by
        rw [inner_add_right, ← hv, ← hv, ← hv, hq.add_right]
      map_smul' := fun a x => ext_inner_left ℂ fun φ => by
        rw [RingHom.id_apply, inner_smul_right, ← hv, ← hv, hq.smul_right] }
  refine ⟨L.mkContinuous c hn, fun φ ψ => hv ψ φ, LinearMap.mkContinuous_norm_le L hc hn,
    fun B' h => ?_⟩
  exact ContinuousLinearMap.ext fun ψ => ext_inner_left ℂ fun φ => (h φ ψ).symm.trans (hv ψ φ)
omit [CompleteSpace H] in
theorem extOfDiagonal_holds : ExtOfDiagonal H := by
  intro B B' h
  have hl : (B : H →ₗ[ℂ] H) = (B' : H →ₗ[ℂ] H) := by
    refine (ext_inner_map _ _).1 fun x => ?_
    show ⟪B x, x⟫_ℂ = ⟪B' x, x⟫_ℂ
    rw [← inner_conj_symm (B x) x, ← inner_conj_symm (B' x) x, h x]
  exact ContinuousLinearMap.coe_injective hl
theorem isDenselyDefined_ofCLM (B : H →L[ℂ] H) : IsDenselyDefined (ofCLM B) :=
  (isDenseSet_iff_dense _).2 (by
    show Dense (((⊤ : Submodule ℂ H)) : Set H)
    simp)
theorem adj_ofCLM (B : H →L[ℂ] H) (hB : IsDenselyDefined (ofCLM B)) :
    adj (ofCLM B) hB = ofCLM (ContinuousLinearMap.adjoint B) := by
  have hd : (adj (ofCLM B) hB).domain = ⊤ := by
    refine eq_top_iff.2 fun φ _ => ?_
    exact ⟨ContinuousLinearMap.adjoint B φ,
      fun χ => (ContinuousLinearMap.adjoint_inner_left B (χ : H) φ).symm⟩
  refine (unboundedOp_eq_iff _ _).2 ⟨hd, fun χ => ?_⟩
  exact adjValue_unique hB
    (fun y => (ContinuousLinearMap.adjoint_inner_left B (y : H) (χ : H)).symm)
    (adj_spec _ hB χ)
theorem adjBoundedOfBounded_holds : AdjBoundedOfBounded H := by
  intro B
  refine ⟨⟨isDenselyDefined_ofCLM B, ?_, ContinuousLinearMap.adjoint B, adj_ofCLM B _⟩,
    ⟨fun ⟨hA, h⟩ φ ψ => ?_, fun h => ⟨isDenselyDefined_ofCLM B, ?_⟩⟩⟩
  · rw [adj_ofCLM]
    rfl
  · rw [adj_ofCLM] at h
    obtain ⟨hdom, hv⟩ := (unboundedOp_eq_iff _ _).1 h
    have hx : ContinuousLinearMap.adjoint B φ = B φ := (hv ⟨φ, Submodule.mem_top⟩).symm
    rw [← hx, ContinuousLinearMap.adjoint_inner_left]
  · have hs : ContinuousLinearMap.adjoint B = B := by
      refine ContinuousLinearMap.ext fun φ => ext_inner_right ℂ fun ψ => ?_
      rw [ContinuousLinearMap.adjoint_inner_left, h]
    rw [adj_ofCLM, hs]
theorem eqTopOfOrthogonalTrivial_holds : EqTopOfOrthogonalTrivial H := by
  intro K hK h
  have hcl : IsClosed (K : Set H) := (isSeqClosedSubmodule_iff K).1 hK
  have : CompleteSpace K := hcl.completeSpace_coe
  refine Submodule.orthogonal_eq_bot_iff.1 ?_
  refine (Submodule.eq_bot_iff _).2 fun φ hφ => ?_
  exact h φ fun κ hκ => (Submodule.mem_orthogonal' K φ).1 hφ κ hκ
omit [CompleteSpace H] in
theorem orthoProjection_apply_apply {P : H →L[ℂ] H} (hP : IsOrthoProjection P) (ψ : H) :
    P (P ψ) = P ψ :=
  congrArg (fun T : H →L[ℂ] H => T ψ) hP.1
omit [CompleteSpace H] in
theorem orthoProjection_normSq_eq {P : H →L[ℂ] H} (hP : IsOrthoProjection P) (ψ : H) :
    ((‖P ψ‖ ^ 2 : ℝ) : ℂ) = ⟪ψ, P ψ⟫_ℂ := by
  have h : ⟪P ψ, P ψ⟫_ℂ = ⟪ψ, P ψ⟫_ℂ := by
    rw [← hP.2 ψ (P ψ), orthoProjection_apply_apply hP]
  rw [← h, inner_self_eq_norm_sq_to_K]
  push_cast
  rfl
omit [CompleteSpace H] in
theorem orthoProjection_norm_le {P : H →L[ℂ] H} (hP : IsOrthoProjection P) (ψ : H) :
    ‖P ψ‖ ≤ ‖ψ‖ := by
  have h₁ : ‖P ψ‖ ^ 2 ≤ ‖ψ‖ * ‖P ψ‖ := by
    have h₂ : ‖((‖P ψ‖ ^ 2 : ℝ) : ℂ)‖ = ‖P ψ‖ ^ 2 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    rw [← h₂, orthoProjection_normSq_eq hP]
    exact norm_inner_le_norm ψ (P ψ)
  by_contra hlt
  have hlt' : ‖ψ‖ < ‖P ψ‖ := not_le.1 hlt
  have hpos : 0 < ‖P ψ‖ := lt_of_le_of_lt (norm_nonneg ψ) hlt'
  nlinarith
omit [CompleteSpace H] in
theorem orthoProjectionRangeNorm_holds : OrthoProjectionRangeNorm H := by
  refine ⟨fun P hP => ⟨?_, fun ψ => ⟨orthoProjection_normSq_eq hP ψ, ?_⟩⟩, fun P P' hP hP' hr => ?_⟩
  · ext ψ
    constructor
    · rintro ⟨y, rfl⟩
      exact orthoProjection_apply_apply hP y
    · intro h
      exact ⟨ψ, h⟩
  · rw [← orthoProjection_normSq_eq hP ψ]
    exact Complex.real_le_real.2 (pow_le_pow_left₀ (norm_nonneg _) (orthoProjection_norm_le hP ψ) 2)
  · have hfix : ∀ {Q Q' : H →L[ℂ] H}, IsOrthoProjection Q' → Set.range Q = Set.range Q' →
        ∀ ψ, Q' (Q ψ) = Q ψ := by
      intro Q Q' hQ' h ψ
      obtain ⟨y, hy⟩ : Q ψ ∈ Set.range Q' := h ▸ Set.mem_range_self ψ
      rw [← hy, orthoProjection_apply_apply hQ']
    refine ContinuousLinearMap.ext fun ψ => ext_inner_left ℂ fun φ => ?_
    calc ⟪φ, P ψ⟫_ℂ = ⟪φ, P' (P ψ)⟫_ℂ := by rw [hfix hP' hr ψ]
      _ = ⟪P' φ, P ψ⟫_ℂ := hP'.2 φ (P ψ)
      _ = ⟪P (P' φ), ψ⟫_ℂ := hP.2 (P' φ) ψ
      _ = ⟪P' φ, ψ⟫_ℂ := by rw [hfix hP hr.symm φ]
      _ = ⟪φ, P' ψ⟫_ℂ := (hP'.2 φ ψ).symm
theorem claim_holds : Claim := by
  intro H _ _ _ c hc
  exact ⟨rieszAntilinear_of_nonneg c hc, boundedSesquilinearRepr_of_nonneg c hc,
    extOfDiagonal_holds, adjBoundedOfBounded_holds, eqTopOfOrthogonalTrivial_holds,
    orthoProjectionRangeNorm_holds⟩
end YangMills.Construction.BoundedRepresentation
