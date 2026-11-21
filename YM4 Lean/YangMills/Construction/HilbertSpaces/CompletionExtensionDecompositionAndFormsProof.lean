import YangMills.Construction.HilbertSpaces.CompletionExtensionDecompositionAndForms
import Mathlib
set_option autoImplicit false
open scoped ComplexConjugate ComplexOrder InnerProductSpace
noncomputable section
namespace YangMills.Construction.HilbertToolkit
open OneLoopNotation ComplexHilbert SesquilinearForms
section Forms
variable {V : Type} [AddCommGroup V] [Module ℂ V] {q : V → V → ℂ}
theorem sesqForm_add_smul_self (hq : IsSesqForm q) (F F' : V) (α : ℂ) :
    q (F + α • F') (F + α • F') =
      q F F + α * q F F' + conj α * q F' F + conj α * α * q F' F' := by
  rw [hq.add_left, hq.add_right, hq.add_right, hq.smul_right, hq.smul_left, hq.smul_left,
    hq.smul_right]
  ring
theorem im_apply_self_eq_zero (hP : IsPosSemidefForm q) (G : V) : (q G G).im = 0 := by
  have h := (Complex.le_def.mp (hP.nonneg G)).2
  simpa using h.symm
theorem isHermitianForm_of_posSemidef (hP : IsPosSemidefForm q) : IsHermitianForm q := by
  have hq : IsSesqForm q := hP.toIsSesqForm
  refine { hq with conj_symm := fun F F' => ?_ }
  have h₁ := im_apply_self_eq_zero hP (F + (1 : ℂ) • F')
  have h₂ := im_apply_self_eq_zero hP (F + Complex.I • F')
  rw [sesqForm_add_smul_self hq] at h₁ h₂
  simp [im_apply_self_eq_zero hP] at h₁ h₂
  apply Complex.ext
  · simp
    linarith
  · simp
    linarith
@[reducible] def preInnerCoreOfForm (hH : IsHermitianForm q) (hP : IsPosSemidefForm q) :
    PreInnerProductSpace.Core ℂ V where
  inner := q
  conj_inner_symm x y := (hH.conj_symm y x).symm
  re_inner_nonneg x := (Complex.le_def.mp (hP.nonneg x)).1
  add_left x y z := hH.add_left x y z
  smul_left x y r := hH.smul_left r x y
theorem norm_form_le_mul_seminorm (hH : IsHermitianForm q) (hP : IsPosSemidefForm q)
    (F F' : V) : ‖q F F'‖ ≤ formSeminorm q F * formSeminorm q F' := by
  let c := preInnerCoreOfForm hH hP
  have h : ‖q F F'‖ * ‖q F' F‖ ≤ (q F F).re * (q F' F').re :=
    InnerProductSpace.Core.inner_mul_inner_self_le (𝕜 := ℂ) F F'
  rw [hH.conj_symm F F', Complex.norm_conj] at h
  have ha : 0 ≤ (q F F).re := (Complex.le_def.mp (hP.nonneg F)).1
  rw [formSeminorm, formSeminorm, ← Real.sqrt_mul ha]
  exact Real.le_sqrt_of_sq_le (by rw [sq]; exact h)
theorem exists_seminorm_eq_formSeminorm (hH : IsHermitianForm q) (hP : IsPosSemidefForm q) :
    ∃ p : Seminorm ℂ V, ∀ F, p F = formSeminorm q F := by
  let c := preInnerCoreOfForm hH hP
  let _ : SeminormedAddCommGroup V := InnerProductSpace.Core.toSeminormedAddCommGroup (c := c)
  let _ : NormedSpace ℂ V := InnerProductSpace.Core.toNormedSpace (c := c)
  exact ⟨normSeminorm ℂ V, fun F => rfl⟩
theorem exists_submodule_eq_formNullSpace (hH : IsHermitianForm q) (hP : IsPosSemidefForm q) :
    ∃ N : Submodule ℂ V, (N : Set V) = formNullSpace q := by
  obtain ⟨p, hp⟩ := exists_seminorm_eq_formSeminorm hH hP
  have hmem : ∀ F, F ∈ formNullSpace q ↔ p F = 0 := fun F => by
    rw [hp]
    rfl
  refine ⟨{ carrier := formNullSpace q
            add_mem' := ?_
            zero_mem' := ?_
            smul_mem' := ?_ }, rfl⟩
  · intro F F' h h'
    rw [hmem] at h h' ⊢
    exact le_antisymm ((map_add_le_add p F F').trans (by rw [h, h', add_zero])) (apply_nonneg p _)
  · rw [hmem]
    exact map_zero p
  · intro a F h
    rw [hmem] at h ⊢
    rw [map_smul_eq_mul, h, mul_zero]
theorem exists_denseIsometricPair (hH : IsHermitianForm q) (hP : IsPosSemidefForm q) :
    ∃ (X : Type) (_ : NormedAddCommGroup X) (_ : InnerProductSpace ℂ X) (_ : CompleteSpace X)
      (cl : V →ₗ[ℂ] X), IsDenseIsometricPair q cl := by
  let c := preInnerCoreOfForm hH hP
  let _ : SeminormedAddCommGroup V := InnerProductSpace.Core.toSeminormedAddCommGroup (c := c)
  let _ : InnerProductSpace ℂ V := InnerProductSpace.ofCore c
  refine ⟨UniformSpace.Completion V, inferInstance, inferInstance, inferInstance,
    (UniformSpace.Completion.toComplₗᵢ (𝕜 := ℂ) (E := V)).toLinearMap, ?_, ?_⟩
  · exact (isDenseSet_iff _).mpr UniformSpace.Completion.denseRange_coe
  · intro x y
    exact UniformSpace.Completion.inner_coe x y
variable {X X' : Type} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
  [NormedAddCommGroup X'] [InnerProductSpace ℂ X'] [CompleteSpace X']
theorem norm_apply_eq_formSeminorm {cl : V →ₗ[ℂ] X} (h : IsDenseIsometricPair q cl) (F : V) :
    ‖cl F‖ = formSeminorm q F := by
  rw [norm_eq_sqrt_innerProd, h.inner_eq]
  rfl
theorem apply_eq_apply_iff_sub_mem {cl : V →ₗ[ℂ] X} (h : IsDenseIsometricPair q cl) (F F' : V) :
    cl F = cl F' ↔ F - F' ∈ formNullSpace q := by
  change _ ↔ formSeminorm q (F - F') = 0
  rw [← norm_apply_eq_formSeminorm h, map_sub, norm_eq_zero, sub_eq_zero]
theorem existsUnique_unitary_intertwining {cl : V →ₗ[ℂ] X} {cl' : V →ₗ[ℂ] X'}
    (h : IsDenseIsometricPair q cl) (h' : IsDenseIsometricPair q cl') :
    ∃! W : X →ₗ[ℂ] X', IsUnitaryMap W ∧ ∀ F, W (cl F) = cl' F := by
  have hd : DenseRange cl := (isDenseSet_iff _).mp h.denseRange
  have hd' : DenseRange cl' := (isDenseSet_iff _).mp h'.denseRange
  have hbd : ∃ C, ∀ F, ‖cl' F‖ ≤ C * ‖cl F‖ :=
    ⟨1, fun F => by rw [norm_apply_eq_formSeminorm h, norm_apply_eq_formSeminorm h', one_mul]⟩
  let G : X →L[ℂ] X' := cl'.extendOfNorm cl
  have hG : ∀ F, G (cl F) = cl' F := fun F => LinearMap.extendOfNorm_eq hd hbd F
  have hnorm : ∀ x, ‖G x‖ = ‖x‖ := fun x =>
    hd.induction_on x (isClosed_eq G.continuous.norm continuous_norm) fun F => by
      rw [hG, norm_apply_eq_formSeminorm h, norm_apply_eq_formSeminorm h']
  let GI : X →ₗᵢ[ℂ] X' := ⟨G.toLinearMap, hnorm⟩
  have hclosed : IsClosed (Set.range GI) := GI.isometry.isClosedEmbedding.isClosed_range
  have hsub : Set.range cl' ⊆ Set.range GI := by
    rintro _ ⟨F, rfl⟩
    exact ⟨cl F, hG F⟩
  have honto : Function.Surjective G := fun y =>
    hclosed.closure_subset_iff.2 hsub (hd' y)
  refine ⟨G.toLinearMap, ⟨⟨hnorm, honto⟩, hG⟩, ?_⟩
  rintro W ⟨hW, hWc⟩
  have hWcont : Continuous W :=
    (AddMonoidHomClass.isometry_of_norm W hW.isometric).continuous
  ext x
  refine congrFun (Continuous.ext_on hd hWcont G.continuous ?_) x
  rintro _ ⟨F, rfl⟩
  exact (hWc F).trans (hG F).symm
end Forms
theorem completionPart_holds : CompletionPart := by
  intro V _ _ q hP
  have hH := isHermitianForm_of_posSemidef hP
  obtain ⟨p, hp⟩ := exists_seminorm_eq_formSeminorm hH hP
  refine ⟨hH, norm_form_le_mul_seminorm hH hP, fun F F' => ?_,
    exists_submodule_eq_formNullSpace hH hP, exists_denseIsometricPair hH hP, ?_⟩
  · rw [← hp, ← hp, ← hp]
    exact map_add_le_add p F F'
  · intro X X' _ _ _ _ _ _ cl cl' h h'
    exact ⟨apply_eq_apply_iff_sub_mem h, existsUnique_unitary_intertwining h h'⟩
section Extension
variable {X X' : Type} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
  [NormedAddCommGroup X'] [InnerProductSpace ℂ X'] [CompleteSpace X']
omit [CompleteSpace X'] in
theorem bddOpBetween_eq_of_eqOn_dense {A B : BddOpBetween X X'} {D : Set X} (hD : IsDenseSet D)
    (h : ∀ x ∈ D, A x = B x) : A = B :=
  ContinuousLinearMap.coeFn_injective
    (Continuous.ext_on ((isDenseSet_iff _).mp hD) A.continuous B.continuous h)
theorem extension_from_dense_submodule (X₀ : Submodule ℂ X) (c : ℝ) (A₀ : X₀ →ₗ[ℂ] X')
    (hD : IsDenseSet (X₀ : Set X)) (hc : 0 ≤ c) (hb : ∀ x, ‖A₀ x‖ ≤ c * ‖(x : X)‖) :
    (∃! A : BddOpBetween X X', ∀ x : X₀, A x = A₀ x) ∧
    ∀ A : BddOpBetween X X', (∀ x : X₀, A x = A₀ x) →
      opNormOf A ≤ c ∧
      ((∀ x, ‖A₀ x‖ = ‖(x : X)‖) →
        IsIsometry (A : X →ₗ[ℂ] X') ∧
        (∀ x x', ⟪A x, A x'⟫_ℂ = ⟪x, x'⟫_ℂ) ∧
        IsClosedSet (Set.range A) ∧
        (IsDenseSet (Set.range A₀) → IsUnitaryMap (A : X →ₗ[ℂ] X'))) := by
  have hdS : Dense (X₀ : Set X) := (isDenseSet_iff _).mp hD
  have hd : DenseRange X₀.subtype := by
    intro x
    simpa [DenseRange] using hdS x
  have hbd : ∃ C, ∀ x, ‖A₀ x‖ ≤ C * ‖X₀.subtype x‖ := ⟨c, hb⟩
  have hext : ∀ x : X₀, (A₀.extendOfNorm X₀.subtype) x = A₀ x := fun x =>
    LinearMap.extendOfNorm_eq hd hbd x
  refine ⟨⟨A₀.extendOfNorm X₀.subtype, hext, fun B hB => bddOpBetween_eq_of_eqOn_dense hD ?_⟩, ?_⟩
  · intro x hx
    exact (hB ⟨x, hx⟩).trans (hext ⟨x, hx⟩).symm
  intro A hA
  refine ⟨A.opNorm_le_bound hc fun x => ?_, fun hiso => ?_⟩
  · refine hd.induction_on x
      (isClosed_le A.continuous.norm (continuous_const.mul continuous_norm)) fun y => ?_
    change ‖A (y : X)‖ ≤ c * ‖(y : X)‖
    rw [hA]
    exact hb y
  have hnorm : ∀ x, ‖A x‖ = ‖x‖ := fun x =>
    hd.induction_on x (isClosed_eq A.continuous.norm continuous_norm) fun y => by
      change ‖A (y : X)‖ = ‖(y : X)‖
      rw [hA]
      exact hiso y
  let AI : X →ₗᵢ[ℂ] X' := ⟨A.toLinearMap, hnorm⟩
  have hclosed : IsClosed (Set.range AI) := AI.isometry.isClosedEmbedding.isClosed_range
  refine ⟨hnorm, fun x x' => AI.inner_map_map x x', (isClosedSet_iff _).mpr hclosed,
    fun hr => ⟨hnorm, ?_⟩⟩
  have hsub : Set.range A₀ ⊆ Set.range AI := by
    rintro _ ⟨y, rfl⟩
    exact ⟨y, hA y⟩
  exact fun y => hclosed.closure_subset_iff.2 hsub ((isDenseSet_iff _).mp hr y)
end Extension
theorem extensionPart_holds : ExtensionPart := by
  intro X X' _ _ _ _ _ _
  exact ⟨fun X₀ c A₀ hD hc hb => extension_from_dense_submodule X₀ c A₀ hD hc hb,
    fun A B D hD h => bddOpBetween_eq_of_eqOn_dense hD h⟩
section Decomposition
variable {X : Type} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
omit [CompleteSpace X] in
theorem orthSet_submodule (Y : Submodule ℂ X) : orthSet (Y : Set X) = (Yᗮ : Set X) := by
  ext x
  exact (Submodule.mem_orthogonal' Y x).symm
theorem orthogonal_decomposition_of_closed (Y : Submodule ℂ X) (hY : IsClosedSet (Y : Set X)) :
    (∀ x : X, ∃! p : X × X, p.1 ∈ Y ∧ p.2 ∈ orthSet (Y : Set X) ∧ x = p.1 + p.2) ∧
    orthSet (orthSet (Y : Set X)) = (Y : Set X) := by
  have hcl : IsClosed (Y : Set X) := (isClosedSet_iff _).mp hY
  have : CompleteSpace Y := hcl.completeSpace_coe
  constructor
  · intro x
    obtain ⟨y, hy, z, hz, e⟩ := Y.exists_add_mem_mem_orthogonal x
    refine ⟨(y, z), ⟨hy, ?_, e⟩, ?_⟩
    · rw [orthSet_submodule]
      exact hz
    rintro ⟨y', z'⟩ ⟨hy', hz', e'⟩
    simp only at hy' hz' e'
    rw [orthSet_submodule] at hz'
    have h₁ : y' - y = z - z' := by
      have : y' + z' = y + z := e'.symm.trans e
      rw [sub_eq_sub_iff_add_eq_add, add_comm z y]
      exact this
    have h₂ : y' - y ∈ Y := Y.sub_mem hy' hy
    have h₃ : y' - y ∈ Yᗮ := h₁ ▸ Yᗮ.sub_mem hz hz'
    have h₄ : y' - y = 0 := by
      have := (Submodule.mem_orthogonal' Y _).mp h₃ _ h₂
      exact inner_self_eq_zero.mp this
    have h₅ : y' = y := sub_eq_zero.mp h₄
    have h₆ : z' = z := by
      rw [h₅] at e'
      exact (add_left_cancel (e.symm.trans e')).symm
    rw [h₅, h₆]
  · rw [orthSet_submodule, orthSet_submodule, Submodule.orthogonal_orthogonal]
theorem mem_closedLinSpan_of_orth (Z : Set X) (x : X) (h : ∀ x' ∈ orthSet Z, IsOrth x x') :
    x ∈ closedLinSpan Z := by
  have h₁ : x ∈ (Submodule.span ℂ Z)ᗮᗮ := by
    rw [Submodule.mem_orthogonal']
    intro u hu
    refine h u fun ψ hψ => ?_
    exact (Submodule.mem_orthogonal' _ u).mp hu ψ (Submodule.subset_span hψ)
  rw [Submodule.orthogonal_orthogonal_eq_closure] at h₁
  rw [closedLinSpan, seqClosureOf_eq_closure]
  exact h₁
end Decomposition
theorem decompositionPart_holds : DecompositionPart := by
  intro X _ _ _
  refine ⟨orthogonal_decomposition_of_closed, fun Z => ⟨mem_closedLinSpan_of_orth Z, fun hZ => ?_⟩⟩
  refine Set.eq_univ_of_forall fun x => ?_
  refine mem_closedLinSpan_of_orth Z x fun x' hx' => ?_
  rw [hZ] at hx'
  rw [Set.mem_singleton_iff.mp hx']
  exact inner_zero_right x
section Functionals
variable {X : Type} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
theorem exists_riesz_vector (l : X →ₛₗ[starRingEnd ℂ] ℂ) (c : ℝ) (hc : 0 ≤ c)
    (hb : ∀ x, ‖l x‖ ≤ c * ‖x‖) : ∃ v, RepresentsFunctional l v ∧ ‖v‖ ≤ c := by
  let f : X →ₗ[ℂ] ℂ :=
    { toFun := fun x => conj (l x)
      map_add' := fun x y => by simp
      map_smul' := fun a x => by simp }
  have hf : ∀ x, ‖f x‖ ≤ c * ‖x‖ := fun x => by
    change ‖conj (l x)‖ ≤ _
    rw [RCLike.norm_conj]
    exact hb x
  refine ⟨(InnerProductSpace.toDual ℂ X).symm (f.mkContinuous c hf), fun x => ?_, ?_⟩
  · rw [← inner_conj_symm, InnerProductSpace.toDual_symm_apply]
    change l x = conj (conj (l x))
    simp
  · rw [LinearIsometryEquiv.norm_map]
    exact LinearMap.mkContinuous_norm_le f hc hf
theorem riesz_vector_unique {l : X →ₛₗ[starRingEnd ℂ] ℂ} {v w : X}
    (hv : RepresentsFunctional l v) (hw : RepresentsFunctional l w) : v = w :=
  ext_inner_left ℂ fun x => (hv x).symm.trans (hw x)
theorem functionalPart_holds : FunctionalPart := by
  intro X _ _ _ l c hc hb
  obtain ⟨v, hv, hn⟩ := exists_riesz_vector l c hc hb
  exact ⟨⟨v, hv, fun w hw => riesz_vector_unique hw hv⟩,
    fun w hw => (riesz_vector_unique hw hv) ▸ hn⟩
theorem exists_representing_op (b : X → X → ℂ) (c : ℝ) (hc : 0 ≤ c) (hf : IsSesqForm b)
    (hb : ∀ x x', ‖b x x'‖ ≤ c * ‖x‖ * ‖x'‖) :
    ∃ A, RepresentsForm b A ∧ opNormOf A ≤ c := by
  have ha : ∀ v : X, ∃ w : X, (∀ u, b u v = ⟪u, w⟫_ℂ) ∧ ‖w‖ ≤ c * ‖v‖ := by
    intro v
    let l : X →ₛₗ[starRingEnd ℂ] ℂ :=
      { toFun := fun u => b u v
        map_add' := fun x y => hf.add_left x y v
        map_smul' := fun a x => hf.smul_left a x v }
    obtain ⟨w, hw, hn⟩ := exists_riesz_vector l (c * ‖v‖) (mul_nonneg hc (norm_nonneg v))
      fun u => (hb u v).trans_eq (by ring)
    exact ⟨w, hw, hn⟩
  choose w hw hn using ha
  let L : X →ₗ[ℂ] X :=
    { toFun := w
      map_add' := fun x y => ext_inner_left ℂ fun u => by
        rw [inner_add_right, ← hw, ← hw, ← hw, hf.add_right]
      map_smul' := fun a x => ext_inner_left ℂ fun u => by
        rw [RingHom.id_apply, inner_smul_right, ← hw, ← hw, hf.smul_right] }
  exact ⟨L.mkContinuous c hn, fun u v => (hw v u).symm, LinearMap.mkContinuous_norm_le L hc hn⟩
theorem representing_op_unique {b : X → X → ℂ} {A B : BddOp X} (hA : RepresentsForm b A)
    (hB : RepresentsForm b B) : A = B :=
  ContinuousLinearMap.ext fun v => ext_inner_left ℂ fun u => (hA u v).trans (hB u v).symm
theorem formPart_holds : FormPart := by
  intro X _ _ _ b c hc hf hb
  obtain ⟨A, hA, hn⟩ := exists_representing_op b c hc hf hb
  exact ⟨⟨A, hA, fun B hB => representing_op_unique hB hA⟩,
    fun B hB => (representing_op_unique hB hA) ▸ hn⟩
theorem isAdjointOp_adjoint (A : BddOp X) :
    IsAdjointOp A (ContinuousLinearMap.adjoint A) :=
  fun x x' => ContinuousLinearMap.adjoint_inner_left A x' x
theorem eq_adjoint_of_isAdjointOp {A B : BddOp X} (h : IsAdjointOp A B) :
    B = ContinuousLinearMap.adjoint A :=
  ContinuousLinearMap.ext fun x => ext_inner_right ℂ fun x' =>
    (h x x').trans (isAdjointOp_adjoint A x x').symm
theorem adjointOp_eq_adjoint (A : BddOp X) : adjointOp A = ContinuousLinearMap.adjoint A :=
  eq_adjoint_of_isAdjointOp (Classical.epsilon_spec ⟨_, isAdjointOp_adjoint A⟩)
end Functionals
theorem adjointPart_holds : AdjointPart := by
  intro X _ _ _
  refine ⟨fun A => ⟨?_, fun B hB => ?_, ?_, ?_⟩, fun A A' => ?_, fun c c' A A' => ?_,
    fun U hU => ?_⟩
  · rw [adjointOp_eq_adjoint]
    exact isAdjointOp_adjoint A
  · rw [adjointOp_eq_adjoint]
    exact eq_adjoint_of_isAdjointOp hB
  · rw [adjointOp_eq_adjoint]
    exact LinearIsometryEquiv.norm_map _ A
  · rw [adjointOp_eq_adjoint, adjointOp_eq_adjoint]
    exact ContinuousLinearMap.adjoint_adjoint A
  · rw [adjointOp_eq_adjoint, adjointOp_eq_adjoint, adjointOp_eq_adjoint]
    exact ContinuousLinearMap.adjoint_comp A A'
  · rw [adjointOp_eq_adjoint, adjointOp_eq_adjoint, adjointOp_eq_adjoint, map_add, map_smulₛₗ,
      map_smulₛₗ]
  · rw [adjointOp_eq_adjoint]
    have h₁ : ContinuousLinearMap.adjoint U * U = 1 :=
      (ContinuousLinearMap.norm_map_iff_adjoint_comp_self U).mp hU.isometric
    refine ⟨?_, h₁⟩
    ext x
    obtain ⟨ψ, rfl⟩ := hU.onto x
    have h₂ : ContinuousLinearMap.adjoint U (U ψ) = ψ := by
      have := congrArg (fun T : BddOp X => T ψ) h₁
      exact this
    change U (ContinuousLinearMap.adjoint U (U ψ)) = U ψ
    rw [h₂]
theorem hilbertCompletionExtensionRiesz_holds : HilbertCompletionExtensionRiesz :=
  ⟨completionPart_holds, extensionPart_holds, decompositionPart_holds, functionalPart_holds,
    formPart_holds, adjointPart_holds⟩
end YangMills.Construction.HilbertToolkit
