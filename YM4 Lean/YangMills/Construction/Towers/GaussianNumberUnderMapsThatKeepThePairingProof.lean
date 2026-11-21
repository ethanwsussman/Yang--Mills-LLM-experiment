import YangMills.Construction.Towers.GaussianNumberUnderMapsThatKeepThePairing
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.Tower.IsometryInvariance
open GaussianConstraint
section Spaces
variable {E F E' F' : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup E'] [InnerProductSpace ℝ E'] [FiniteDimensional ℝ E']
  [NormedAddCommGroup F'] [InnerProductSpace ℝ F'] [FiniteDimensional ℝ F']
theorem adjoint_conj_eq (O : E ≃ₗ[ℝ] E') (O' : F ≃ₗ[ℝ] F')
    (hO : ∀ x y, inner ℝ (O x) (O y) = inner ℝ x y)
    (hO' : ∀ x y, inner ℝ (O' x) (O' y) = inner ℝ x y)
    (M : E →ₗ[ℝ] F) (M' : E' →ₗ[ℝ] F') (hM : ∀ x, M' (O x) = O' (M x)) :
    LinearMap.adjoint M' = (O : E →ₗ[ℝ] E') ∘ₗ LinearMap.adjoint M ∘ₗ (O'.symm : F' →ₗ[ℝ] F) := by
  symm
  rw [LinearMap.eq_adjoint_iff]
  intro x y
  obtain ⟨w, rfl⟩ := O'.surjective x
  obtain ⟨z, rfl⟩ := O.surjective y
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
  rw [hO, hM, hO', LinearMap.adjoint_inner_left]
theorem det_comp_adjoint_conj (O : E ≃ₗ[ℝ] E') (O' : F ≃ₗ[ℝ] F')
    (hO : ∀ x y, inner ℝ (O x) (O y) = inner ℝ x y)
    (hO' : ∀ x y, inner ℝ (O' x) (O' y) = inner ℝ x y)
    (M : E →ₗ[ℝ] F) (M' : E' →ₗ[ℝ] F') (hM : ∀ x, M' (O x) = O' (M x)) :
    LinearMap.det (M' ∘ₗ LinearMap.adjoint M') = LinearMap.det (M ∘ₗ LinearMap.adjoint M) := by
  have h : M' ∘ₗ LinearMap.adjoint M' =
      (O' : F →ₗ[ℝ] F') ∘ₗ (M ∘ₗ LinearMap.adjoint M) ∘ₗ (O'.symm : F' →ₗ[ℝ] F) := by
    rw [adjoint_conj_eq O O' hO hO' M M' hM]
    ext x
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, hM]
  rw [h, LinearMap.det_conj]
def kerEquivOfConj (O : E ≃ₗ[ℝ] E') (O' : F ≃ₗ[ℝ] F') (M : E →ₗ[ℝ] F) (M' : E' →ₗ[ℝ] F')
    (hM : ∀ x, M' (O x) = O' (M x)) : LinearMap.ker M ≃ₗ[ℝ] LinearMap.ker M' where
  toFun X := ⟨O X.1, by
    have hX : M X.1 = 0 := X.2
    rw [LinearMap.mem_ker, hM, hX, map_zero]⟩
  invFun X := ⟨O.symm X.1, by
    have hX : M' X.1 = 0 := X.2
    have h : O' (M (O.symm X.1)) = 0 := by
      rw [← hM, LinearEquiv.apply_symm_apply, hX]
    rw [LinearMap.mem_ker]
    simpa using h⟩
  map_add' X Y := by ext1; simp
  map_smul' c X := by ext1; simp
  left_inv X := by ext1; simp
  right_inv X := by ext1; simp
theorem kernelGaussianIntegral_conj (O : E ≃ₗ[ℝ] E') (O' : F ≃ₗ[ℝ] F')
    (hO : ∀ x y, inner ℝ (O x) (O y) = inner ℝ x y)
    (M : E →ₗ[ℝ] F) (M' : E' →ₗ[ℝ] F') (hM : ∀ x, M' (O x) = O' (M x))
    (T : QuadraticForm ℝ (LinearMap.ker M)) (T' : QuadraticForm ℝ (LinearMap.ker M'))
    (hT : ∀ (X : LinearMap.ker M) (Y : LinearMap.ker M'), Y.1 = O X.1 → T' Y = T X) :
    kernelGaussianIntegral M' T' = kernelGaussianIntegral M T := by
  unfold kernelGaussianIntegral
  letI : MeasurableSpace (LinearMap.ker M) := borel _
  haveI : BorelSpace (LinearMap.ker M) := ⟨rfl⟩
  letI : MeasurableSpace (LinearMap.ker M') := borel _
  haveI : BorelSpace (LinearMap.ker M') := ⟨rfl⟩
  let e : LinearMap.ker M ≃ₗᵢ[ℝ] LinearMap.ker M' :=
    (kerEquivOfConj O O' M M' hM).isometryOfInner (fun x y => hO x.1 y.1)
  have h := e.measurePreserving.integral_comp e.toHomeomorph.measurableEmbedding
    (fun X => Real.exp (-(1 / 2) * T' X))
  rw [← h]
  refine integral_congr_ae (Filter.Eventually.of_forall fun X => ?_)
  have hX : T' (e X) = T X := hT X (e X) rfl
  simp only [hX]
theorem constrainedGaussianNumber_conj (O : E ≃ₗ[ℝ] E') (O' : F ≃ₗ[ℝ] F')
    (hO : ∀ x y, inner ℝ (O x) (O y) = inner ℝ x y)
    (hO' : ∀ x y, inner ℝ (O' x) (O' y) = inner ℝ x y)
    (M : E →ₗ[ℝ] F) (M' : E' →ₗ[ℝ] F') (hM : ∀ x, M' (O x) = O' (M x))
    (T : QuadraticForm ℝ (LinearMap.ker M)) (T' : QuadraticForm ℝ (LinearMap.ker M'))
    (hT : ∀ (X : LinearMap.ker M) (Y : LinearMap.ker M'), Y.1 = O X.1 → T' Y = T X) :
    constrainedGaussianNumber M' T' = constrainedGaussianNumber M T := by
  unfold constrainedGaussianNumber
  rw [det_comp_adjoint_conj O O' hO hO' M M' hM, kernelGaussianIntegral_conj O O' hO M M' hM T T' hT]
end Spaces
theorem constrainedGaussianNumberOfCores_conj {V V' W W' : Type*}
    [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    [AddCommGroup V'] [Module ℝ V'] [FiniteDimensional ℝ V']
    [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ W]
    [AddCommGroup W'] [Module ℝ W'] [FiniteDimensional ℝ W']
    (c : InnerProductSpace.Core ℝ V) (c' : InnerProductSpace.Core ℝ V')
    (d : InnerProductSpace.Core ℝ W) (d' : InnerProductSpace.Core ℝ W')
    (O : V ≃ₗ[ℝ] W) (O' : V' ≃ₗ[ℝ] W')
    (hO : ∀ x y, d.inner (O x) (O y) = c.inner x y)
    (hO' : ∀ x y, d'.inner (O' x) (O' y) = c'.inner x y)
    (M : V →ₗ[ℝ] V') (M' : W →ₗ[ℝ] W') (hM : ∀ x, M' (O x) = O' (M x))
    (T : QuadraticForm ℝ (LinearMap.ker M)) (T' : QuadraticForm ℝ (LinearMap.ker M'))
    (hT : ∀ (X : LinearMap.ker M) (Y : LinearMap.ker M'), Y.1 = O X.1 → T' Y = T X) :
    constrainedGaussianNumberOfCores d d' M' T' = constrainedGaussianNumberOfCores c c' M T := by
  unfold constrainedGaussianNumberOfCores
  letI := c.toNormedAddCommGroup
  letI := InnerProductSpace.ofCore c.toCore
  letI := c'.toNormedAddCommGroup
  letI := InnerProductSpace.ofCore c'.toCore
  letI := d.toNormedAddCommGroup
  letI := InnerProductSpace.ofCore d.toCore
  letI := d'.toNormedAddCommGroup
  letI := InnerProductSpace.ofCore d'.toCore
  exact constrainedGaussianNumber_conj O O' hO hO' M M' hM T T' hT
def coreTransfer {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    (c : InnerProductSpace.Core ℝ V) (O : V ≃ₗ[ℝ] W) : InnerProductSpace.Core ℝ W where
  inner x y := c.inner (O.symm x) (O.symm y)
  conj_inner_symm x y := c.conj_inner_symm _ _
  re_inner_nonneg x := c.re_inner_nonneg _
  add_left x y z := by rw [map_add]; exact c.add_left _ _ _
  smul_left x y r := by rw [map_smul]; exact c.smul_left _ _ _
  definite x h := by
    have := c.definite _ h
    simpa using this
open Matrices
theorem edgeFormsEuclidean_of_equiv {L n k p L₂ n₂ k₂ q : ℕ}
    (O : edgeFormSpace L n k p ≃ₗ[ℝ] edgeFormSpace L₂ n₂ k₂ q)
    (hO : ∀ X Y : edgeFormSpace L n k p,
      (edgeFormPairing (O X : Edge L₂ n₂ k₂ q → ComplexMatrix2) (O Y)).re =
      (edgeFormPairing (X : Edge L n k p → ComplexMatrix2) Y).re)
    (h : EdgeFormsEuclidean L n k p) : EdgeFormsEuclidean L₂ n₂ k₂ q := by
  obtain ⟨hf, c, hc⟩ := h
  refine ⟨Module.Finite.equiv O, coreTransfer c O, fun X Y => ?_⟩
  have h1 : (coreTransfer c O).inner X Y = c.inner (O.symm X) (O.symm Y) := rfl
  rw [h1, hc, ← hO]
  simp
theorem symm_preserves_edgeFormPairing {L n k p L₂ n₂ k₂ q : ℕ}
    (O : edgeFormSpace L n k p ≃ₗ[ℝ] edgeFormSpace L₂ n₂ k₂ q)
    (hO : ∀ X Y : edgeFormSpace L n k p,
      (edgeFormPairing (O X : Edge L₂ n₂ k₂ q → ComplexMatrix2) (O Y)).re =
      (edgeFormPairing (X : Edge L n k p → ComplexMatrix2) Y).re) :
    ∀ X Y : edgeFormSpace L₂ n₂ k₂ q,
      (edgeFormPairing (O.symm X : Edge L n k p → ComplexMatrix2) (O.symm Y)).re =
      (edgeFormPairing (X : Edge L₂ n₂ k₂ q → ComplexMatrix2) Y).re := by
  intro X Y
  rw [← hO]
  simp
theorem constrainedGaussianIsometryInvariance_holds : ConstrainedGaussianIsometryInvariance := by
  intro L n k p p' L₂ n₂ k₂ q q' O O' hO hO' M M' hM T T' hT
  unfold constrainedGaussianOnEdgeForms
  by_cases h : EdgeFormsEuclidean L n k p ∧ EdgeFormsEuclidean L n k p'
  · have h' : EdgeFormsEuclidean L₂ n₂ k₂ q ∧ EdgeFormsEuclidean L₂ n₂ k₂ q' :=
      ⟨edgeFormsEuclidean_of_equiv O hO h.1, edgeFormsEuclidean_of_equiv O' hO' h.2⟩
    rw [dif_pos h, dif_pos h']
    haveI := h.1.1
    haveI := h.2.1
    haveI := h'.1.1
    haveI := h'.2.1
    refine constrainedGaussianNumberOfCores_conj _ _ _ _ O O' (fun x y => ?_) (fun x y => ?_)
      M M' hM T T' hT
    · rw [h'.1.2.choose_spec, h.1.2.choose_spec, hO]
    · rw [h'.2.2.choose_spec, h.2.2.choose_spec, hO']
  · have h' : ¬(EdgeFormsEuclidean L₂ n₂ k₂ q ∧ EdgeFormsEuclidean L₂ n₂ k₂ q') := fun g =>
      h ⟨edgeFormsEuclidean_of_equiv O.symm (symm_preserves_edgeFormPairing O hO) g.1,
        edgeFormsEuclidean_of_equiv O'.symm (symm_preserves_edgeFormPairing O' hO') g.2⟩
    rw [dif_neg h, dif_neg h']
end YangMills.Construction.Tower.IsometryInvariance
end
