import YangMills.Construction.HilbertSpace.BasicHilbertSpaceFacts
import Mathlib
set_option autoImplicit false
open scoped ComplexConjugate InnerProductSpace
namespace YangMills.Construction.HilbertSpace.BasicFacts
open YangMills.Construction.OperatorTransport
variable {E F : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
theorem eqOnDenseEq_proof : EqOnDenseEq E F := by
  intro s T T' hs hT
  exact DFunLike.coe_injective (Continuous.ext_on hs T.continuous T'.continuous hT)
theorem surjective_of_norm_eq [CompleteSpace E] (T : E →L[ℂ] F) (hT : ∀ x, ‖T x‖ = ‖x‖)
    (hdense : Dense (Set.range T)) : Function.Surjective T := by
  have hiso : Isometry T := AddMonoidHomClass.isometry_of_norm T hT
  have hclosed : IsClosed (Set.range T) := hiso.isClosedEmbedding.isClosed_range
  have huniv : Set.range T = Set.univ := by rw [← hclosed.closure_eq, hdense.closure_eq]
  exact Set.range_eq_univ.1 huniv
theorem extendsFromDense_proof [CompleteSpace E] [CompleteSpace F] : ExtendsFromDense E F := by
  intro D C T₀ hD hC hbd
  let f : D →L[ℂ] F := T₀.mkContinuous C hbd
  let e : D →L[ℂ] E := D.subtypeL
  have hdr : DenseRange e := hD.denseRange_val
  have hui : IsUniformInducing e := isUniformEmbedding_subtype_val.isUniformInducing
  let T : E →L[ℂ] F := f.extend e
  have hTD : ∀ x : D, T x = T₀ x := fun x => ContinuousLinearMap.extend_eq f hdr hui x
  have hle : ∀ x, ‖T x‖ ≤ C * ‖x‖ := by
    have hcl : IsClosed {x : E | ‖T x‖ ≤ C * ‖x‖} := isClosed_le (by fun_prop) (by fun_prop)
    have hsub : closure (D : Set E) ⊆ {x : E | ‖T x‖ ≤ C * ‖x‖} :=
      hcl.closure_subset_iff.2 fun x hx => by
        have h₁ := hTD ⟨x, hx⟩
        have h₂ := hbd ⟨x, hx⟩
        show ‖T x‖ ≤ C * ‖x‖
        rw [show T x = T₀ ⟨x, hx⟩ from h₁]
        exact h₂
    exact fun x => hsub (hD x)
  refine ⟨T, hTD, ContinuousLinearMap.opNorm_le_bound T hC hle, ?_, ?_⟩
  · intro T' hT'
    exact eqOnDenseEq_proof (D : Set E) T' T hD fun x hx => by
      rw [show T x = T₀ ⟨x, hx⟩ from hTD ⟨x, hx⟩]
      exact hT' ⟨x, hx⟩
  · intro hnm hrg
    have hnorm : ∀ x, ‖T x‖ = ‖x‖ := by
      have hcl : IsClosed {x : E | ‖T x‖ = ‖x‖} := isClosed_eq (by fun_prop) (by fun_prop)
      have hsub : closure (D : Set E) ⊆ {x : E | ‖T x‖ = ‖x‖} :=
        hcl.closure_subset_iff.2 fun x hx => by
          show ‖T x‖ = ‖x‖
          rw [show T x = T₀ ⟨x, hx⟩ from hTD ⟨x, hx⟩]
          exact hnm ⟨x, hx⟩
      exact fun x => hsub (hD x)
    have hdense : Dense (Set.range T) := hrg.mono (by
      rintro _ ⟨x, rfl⟩
      exact ⟨x, hTD x⟩)
    refine ⟨⟨(AddMonoidHomClass.isometry_of_norm T hnorm).injective,
      surjective_of_norm_eq T hnorm hdense⟩, ?_⟩
    exact (LinearMap.norm_map_iff_inner_map_map (T : E →ₗ[ℂ] F)).1 hnorm
theorem formPolarization_proof : FormPolarization E := by
  intro b hb x y
  have hI2 : Complex.I ^ 2 = -1 := Complex.I_sq
  have hI3 : Complex.I ^ 3 = -Complex.I := by rw [pow_succ, hI2]; ring
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_one, hI2, hI3, zero_add,
    hb.add_left, hb.add_right, hb.smul_left, hb.smul_right, map_neg, map_one,
    Complex.conj_I]
  linear_combination ((b x y - b y x) / 2) * hI2
theorem eqZeroOfInnerSelfApply_proof : EqZeroOfInnerSelfApply E := by
  intro T hT
  have h0 : (T : E →ₗ[ℂ] E) = 0 :=
    (inner_map_self_eq_zero _).1 fun x => inner_eq_zero_symm.1 (hT x)
  exact ContinuousLinearMap.coe_injective h0
theorem normPreservingPreservesInner_proof : NormPreservingPreservesInner E F :=
  fun T hT => (LinearMap.norm_map_iff_inner_map_map T).1 hT
theorem adjointUnique_proof : AdjointUnique E := by
  intro T S S' hS hS'
  refine ContinuousLinearMap.ext fun x => ext_inner_right ℂ fun y => ?_
  rw [← hS x y, ← hS' x y]
theorem rieszRepresentation_proof [CompleteSpace E] : RieszRepresentation E := by
  intro l C _ hl
  refine ⟨(InnerProductSpace.toDual ℂ E).symm (l.mkContinuous C hl), fun x => ?_⟩
  rw [InnerProductSpace.toDual_symm_apply]
  rfl
theorem boundedFormRepresentation_proof [CompleteSpace E] : BoundedFormRepresentation E := by
  intro b C hb hC hbd
  have key : ∀ y : E, ∃ v : E, ∀ x, b x y = ⟪x, v⟫_ℂ := by
    intro y
    let l : E →ₗ[ℂ] ℂ :=
      { toFun := fun x => conj (b x y)
        map_add' := fun x x' => by simp [hb.add_left]
        map_smul' := fun c x => by simp [hb.smul_left] }
    obtain ⟨v, hv⟩ := rieszRepresentation_proof l (C * ‖y‖) (by positivity) fun x => by
      show ‖conj (b x y)‖ ≤ _
      rw [RCLike.norm_conj]
      exact (hbd x y).trans_eq (by ring)
    refine ⟨v, fun x => ?_⟩
    have h₁ := hv x
    have h₂ : conj (b x y) = ⟪v, x⟫_ℂ := h₁
    rw [← inner_conj_symm, ← h₂, Complex.conj_conj]
  choose v hv using key
  have hadd : ∀ y y', v (y + y') = v y + v y' := fun y y' => ext_inner_left ℂ fun x => by
    rw [inner_add_right, ← hv, ← hv, ← hv, hb.add_right]
  have hsmul : ∀ (c : ℂ) y, v (c • y) = c • v y := fun c y => ext_inner_left ℂ fun x => by
    rw [inner_smul_right, ← hv, ← hv, hb.smul_right]
  let L : E →ₗ[ℂ] E := { toFun := v, map_add' := hadd, map_smul' := hsmul }
  have hle : ∀ y, ‖L y‖ ≤ C * ‖y‖ := by
    intro y
    show ‖v y‖ ≤ C * ‖y‖
    have h₁ := hbd (v y) y
    have hsq : ‖⟪v y, v y⟫_ℂ‖ = ‖v y‖ * ‖v y‖ := by
      rw [inner_self_eq_norm_sq_to_K]
      simp [sq]
    rw [hv, hsq] at h₁
    have h₂ : ‖v y‖ * ‖v y‖ ≤ ‖v y‖ * (C * ‖y‖) := h₁.trans_eq (by ring)
    rcases (norm_nonneg (v y)).eq_or_lt with h0 | h0
    · rw [← h0]
      positivity
    · exact le_of_mul_le_mul_left h₂ h0
  let T : E →L[ℂ] E := L.mkContinuous C hle
  have hT : ∀ x y, b x y = ⟪x, T y⟫_ℂ := fun x y => hv y x
  refine ⟨T, hT, LinearMap.mkContinuous_norm_le L hC hle, ?_, ?_⟩
  · intro T' hT'
    refine ContinuousLinearMap.ext fun y => ext_inner_left ℂ fun x => ?_
    rw [← hT', ← hT]
  · intro hherm x y
    rw [← inner_conj_symm (T x) y, ← hT y x, hherm x y, Complex.conj_conj, hT x y]
theorem clmBanachAlgebra_proof [CompleteSpace E] : CLMBanachAlgebra E :=
  ⟨inferInstance, fun T S => ContinuousLinearMap.opNorm_comp_le T S⟩
theorem apply_inv_apply {U : E →ₗ[ℂ] F} (hU : IsUnitaryMap U) (y : F) : U (hU.inv y) = y :=
  hU.toLinearEquiv.apply_symm_apply y
theorem norm_map_of_isUnitaryMap {U : E →ₗ[ℂ] F} (hU : IsUnitaryMap U) (x : E) : ‖U x‖ = ‖x‖ :=
  (LinearMap.norm_map_iff_inner_map_map U).2 hU.inner_map_map x
theorem isUnitaryMap_inv {U : E →ₗ[ℂ] F} (hU : IsUnitaryMap U) : IsUnitaryMap hU.inv := by
  refine ⟨hU.toLinearEquiv.symm.bijective, fun x y => ?_⟩
  rw [← hU.inner_map_map, apply_inv_apply, apply_inv_apply]
theorem exists_clm_of_isUnitaryMap {U : E →ₗ[ℂ] F} (hU : IsUnitaryMap U) :
    ∃ T : E →L[ℂ] F, (T : E →ₗ[ℂ] F) = U :=
  ⟨U.mkContinuous 1 fun x => by rw [norm_map_of_isUnitaryMap hU, one_mul], by ext; rfl⟩
theorem unitaryBasicProps_proof : UnitaryBasicProps E F := by
  intro U hU
  refine ⟨exists_clm_of_isUnitaryMap hU, exists_clm_of_isUnitaryMap (isUnitaryMap_inv hU),
    isUnitaryMap_inv hU, ?_⟩
  intro y x
  rw [← hU.inner_map_map (hU.inv y) x, apply_inv_apply]
theorem unitaryInvIsAdjoint_proof : UnitaryInvIsAdjoint E := by
  intro U hU
  obtain ⟨T, hT⟩ := exists_clm_of_isUnitaryMap hU
  obtain ⟨S, hS⟩ := exists_clm_of_isUnitaryMap (isUnitaryMap_inv hU)
  refine ⟨T, S, hT, hS, fun x y => ?_⟩
  have h₁ : T y = U y := congrArg (fun R : E →ₗ[ℂ] E => R y) hT
  have h₂ : S x = hU.inv x := congrArg (fun R : E →ₗ[ℂ] E => R x) hS
  rw [h₁, h₂, ← hU.inner_map_map (hU.inv x) y, apply_inv_apply]
theorem selfAdjointNotionsAgree_proof [CompleteSpace E] : SelfAdjointNotionsAgree E := by
  intro T
  constructor
  · intro h
    refine ⟨by simp [HilbertSpaceBasics.ofBounded], fun x z => ⟨?_, fun hz => ?_⟩⟩
    · rintro ⟨hx, rfl⟩ y
      exact h x y
    · refine ⟨Submodule.mem_top, ?_⟩
      refine ext_inner_right ℂ fun y => ?_
      have h₁ := hz ⟨y, Submodule.mem_top⟩
      have h₂ := h x y
      exact h₂.symm.trans h₁
  · intro h x y
    exact ((h.2 x (T x)).1 ⟨Submodule.mem_top, rfl⟩) ⟨y, Submodule.mem_top⟩
theorem basicHilbertSpaceFacts_proof : BasicHilbertSpaceFacts := by
  intro E F _ _ _ _ _ _
  exact ⟨extendsFromDense_proof, eqOnDenseEq_proof, formPolarization_proof,
    eqZeroOfInnerSelfApply_proof, normPreservingPreservesInner_proof, adjointUnique_proof,
    rieszRepresentation_proof, boundedFormRepresentation_proof, clmBanachAlgebra_proof,
    unitaryBasicProps_proof, unitaryInvIsAdjoint_proof, selfAdjointNotionsAgree_proof⟩
end YangMills.Construction.HilbertSpace.BasicFacts
