import YangMills.Construction.Gaussian.KernelGaussianIntegral
import YangMills.Construction.Towers.ChangeOfTheGaugeFixingAndOfTheConstraint
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YangMills.Construction.GaussianConstraint.GaugeFixingChangeProof
section Gram
variable {V F : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
def formMatrix (B : LinearMap.BilinForm ℝ V) (u : ι → V) : Matrix ι ι ℝ :=
  Matrix.of fun i j => B (u i) (u j)
def innerMatrix (u : ι → V) (w : κ → V) : Matrix ι κ ℝ :=
  Matrix.of fun i j => inner ℝ (u i) (w j)
def gramDeterminant (u : ι → V) : ℝ := (innerMatrix u u).det
def innerPullback (f : V →ₗ[ℝ] F) : LinearMap.BilinForm ℝ V :=
  (innerₗ F).compl₁₂ f f
omit [DecidableEq ι] [DecidableEq κ] in
lemma formMatrix_innerPullback (f : V →ₗ[ℝ] F) (u : ι → V) :
    formMatrix (innerPullback f) u = innerMatrix (fun i => f (u i)) (fun i => f (u i)) := by
  ext i j
  simp [formMatrix, innerMatrix, innerPullback]
def coordMatrix (b : OrthonormalBasis κ ℝ V) (u : ι → V) : Matrix ι κ ℝ :=
  Matrix.of fun i k => inner ℝ (b k) (u i)
omit [DecidableEq ι] [DecidableEq κ] in
lemma innerMatrix_eq_coordMatrix_mul {ι' : Type*} [Fintype ι'] (b : OrthonormalBasis κ ℝ V)
    (u : ι → V) (w : ι' → V) : innerMatrix u w = coordMatrix b u * (coordMatrix b w).transpose := by
  ext i j
  simp only [innerMatrix, coordMatrix, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply]
  rw [← b.sum_inner_mul_inner (u i) (w j)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [real_inner_comm (u i) (b k)]
omit [DecidableEq ι] [DecidableEq κ] in
lemma formMatrix_of_expansion {ι' : Type*} [Fintype ι'] (B : LinearMap.BilinForm ℝ V)
    (z : ι' → V) (u : ι → V) (P : Matrix ι ι' ℝ) (h : ∀ i, u i = ∑ k, P i k • z k) :
    formMatrix B u = P * formMatrix B z * P.transpose := by
  ext i j
  simp only [formMatrix, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply]
  rw [h i, h j]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring
lemma gramDeterminant_orthonormalBasis (b : OrthonormalBasis ι ℝ V) : gramDeterminant b = 1 := by
  have : innerMatrix b b = 1 := by
    ext i j
    simp only [innerMatrix, Matrix.of_apply, Matrix.one_apply]
    exact orthonormal_iff_ite.mp b.orthonormal i j
  rw [gramDeterminant, this, Matrix.det_one]
lemma gramDeterminant_eq_coordMatrix_det_sq (b : OrthonormalBasis ι ℝ V) (u : ι → V) :
    gramDeterminant u = (coordMatrix b u).det ^ 2 := by
  rw [gramDeterminant, innerMatrix_eq_coordMatrix_mul b u u, Matrix.det_mul, Matrix.det_transpose,
    sq]
lemma innerMatrix_det_sq (b : OrthonormalBasis ι ℝ V) (u w : ι → V) :
    (innerMatrix u w).det ^ 2 = gramDeterminant u * gramDeterminant w := by
  rw [gramDeterminant_eq_coordMatrix_det_sq b u, gramDeterminant_eq_coordMatrix_det_sq b w,
    innerMatrix_eq_coordMatrix_mul b u w, Matrix.det_mul, Matrix.det_transpose]
  ring
lemma formMatrix_det_eq (B : LinearMap.BilinForm ℝ V) (b : OrthonormalBasis ι ℝ V) (u : ι → V) :
    (formMatrix B u).det = (formMatrix B b).det * gramDeterminant u := by
  have h := formMatrix_of_expansion B b u (coordMatrix b u) fun i => by
    simpa [coordMatrix] using (b.sum_repr' (u i)).symm
  rw [h, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
    gramDeterminant_eq_coordMatrix_det_sq b u]
  ring
lemma det_submatrix_equiv (M : Matrix ι ι ℝ) (e : κ ≃ ι) :
    (M.submatrix e e).det = M.det := Matrix.det_submatrix_equiv_self e M
lemma gramDeterminant_comp_equiv (u : ι → V) (e : κ ≃ ι) :
    gramDeterminant (u ∘ e) = gramDeterminant u := by
  have : innerMatrix (u ∘ e) (u ∘ e) = (innerMatrix u u).submatrix e e := by
    ext i j
    simp [innerMatrix]
  rw [gramDeterminant, this, det_submatrix_equiv, gramDeterminant]
lemma formMatrix_det_orthonormalBasis (B : LinearMap.BilinForm ℝ V) (b : OrthonormalBasis ι ℝ V)
    (b' : OrthonormalBasis κ ℝ V) (e : κ ≃ ι) :
    (formMatrix B b').det = (formMatrix B b).det := by
  have h1 : formMatrix B (b.reindex e.symm) = (formMatrix B b).submatrix e e := by
    ext i j
    simp [formMatrix]
  have h2 := formMatrix_det_eq B (b.reindex e.symm) b'
  rw [gramDeterminant_orthonormalBasis, mul_one, h1, det_submatrix_equiv] at h2
  exact h2
lemma innerMatrix_sumElim {ι' κ' : Type*} (x : ι → V) (y : κ → V) (x' : ι' → V) (y' : κ' → V) :
    innerMatrix (Sum.elim x y) (Sum.elim x' y') =
      Matrix.fromBlocks (innerMatrix x x') (innerMatrix x y') (innerMatrix y x')
        (innerMatrix y y') := by
  ext (i | i) (j | j) <;> simp [innerMatrix]
lemma gramDeterminant_sumElim_of_orthogonal (x : ι → V) (y : κ → V)
    (h : ∀ i j, inner ℝ (x i) (y j) = 0) :
    gramDeterminant (Sum.elim x y) = gramDeterminant x * gramDeterminant y := by
  have h0 : innerMatrix x y = 0 := by
    ext i j
    simp [innerMatrix, h]
  have h1 : innerMatrix y x = 0 := by
    ext i j
    simp [innerMatrix, real_inner_comm, h]
  rw [gramDeterminant, innerMatrix_sumElim, h0, h1, Matrix.det_fromBlocks_zero₂₁, gramDeterminant,
    gramDeterminant]
lemma gramDeterminant_replace (b : OrthonormalBasis (ι ⊕ κ) ℝ V) (x x' : ι → V) (y : κ → V)
    (hxy : ∀ i j, inner ℝ (x i) (y j) = 0) (hx : gramDeterminant x = 1)
    (hy : gramDeterminant y ≠ 0) :
    gramDeterminant (Sum.elim x' y) = (innerMatrix x x').det ^ 2 * gramDeterminant y := by
  have hc := innerMatrix_det_sq b (Sum.elim x y) (Sum.elim x' y)
  have h0 : innerMatrix x y = 0 := by
    ext i j
    simp [innerMatrix, hxy]
  rw [innerMatrix_sumElim, h0, Matrix.det_fromBlocks_zero₁₂,
    gramDeterminant_sumElim_of_orthogonal x y hxy, hx] at hc
  have hy' : gramDeterminant y = (innerMatrix y y).det := rfl
  rw [← hy', one_mul, mul_pow] at hc
  have : gramDeterminant y * ((innerMatrix x x').det ^ 2 * gramDeterminant y) =
      gramDeterminant y * gramDeterminant (Sum.elim x' y) := by
    rw [← hc]
    ring
  exact (mul_left_cancel₀ hy this).symm
lemma det_comp_adjoint_eq_gramDeterminant [FiniteDimensional ℝ V] [FiniteDimensional ℝ F]
    (M : V →ₗ[ℝ] F) (f : OrthonormalBasis κ ℝ F) :
    LinearMap.det (M ∘ₗ LinearMap.adjoint M) =
      gramDeterminant (fun i => LinearMap.adjoint M (f i)) := by
  rw [← LinearMap.det_toMatrix f.toBasis, gramDeterminant]
  congr 1
  ext i j
  rw [LinearMap.toMatrix_apply]
  simp only [OrthonormalBasis.coe_toBasis, OrthonormalBasis.coe_toBasis_repr_apply,
    OrthonormalBasis.repr_apply_apply, innerMatrix, Matrix.of_apply, LinearMap.comp_apply]
  exact (LinearMap.adjoint_inner_left M (LinearMap.adjoint M (f j)) (f i)).symm
lemma coarea_identity [FiniteDimensional ℝ V] [FiniteDimensional ℝ F] (M : V →ₗ[ℝ] F)
    (w : ι → V) (hw : ∀ i, M (w i) = 0) (l : κ → V) (f : OrthonormalBasis κ ℝ F)
    (b : OrthonormalBasis (ι ⊕ κ) ℝ V) (hG : gramDeterminant w ≠ 0) :
    gramDeterminant w * gramDeterminant (fun i => M (l i)) =
      LinearMap.det (M ∘ₗ LinearMap.adjoint M) * gramDeterminant (Sum.elim w l) := by
  have hort : ∀ i j, inner ℝ (w i) (LinearMap.adjoint M (f j)) = 0 := by
    intro i j
    rw [LinearMap.adjoint_inner_right, hw, inner_zero_left]
  have h1 : innerMatrix (fun i => LinearMap.adjoint M (f i)) w = 0 := by
    ext i j
    simp only [innerMatrix, Matrix.of_apply, Matrix.zero_apply]
    rw [LinearMap.adjoint_inner_left, hw, inner_zero_right]
  have h2 : innerMatrix (fun i => LinearMap.adjoint M (f i)) l =
      innerMatrix f (fun i => M (l i)) := by
    ext i j
    simp only [innerMatrix, Matrix.of_apply]
    rw [LinearMap.adjoint_inner_left]
  have hc := innerMatrix_det_sq b (Sum.elim w fun i => LinearMap.adjoint M (f i)) (Sum.elim w l)
  rw [innerMatrix_sumElim, h1, Matrix.det_fromBlocks_zero₂₁,
    gramDeterminant_sumElim_of_orthogonal w _ hort, h2,
    ← det_comp_adjoint_eq_gramDeterminant M f] at hc
  have hf := innerMatrix_det_sq f f (fun i => M (l i))
  rw [gramDeterminant_orthonormalBasis, one_mul] at hf
  have hw' : (innerMatrix w w).det = gramDeterminant w := rfl
  rw [hw', mul_pow, hf] at hc
  have : gramDeterminant w * (gramDeterminant w * gramDeterminant (fun i => M (l i))) =
      gramDeterminant w *
        (LinearMap.det (M ∘ₗ LinearMap.adjoint M) * gramDeterminant (Sum.elim w l)) := by
    rw [← mul_assoc, ← sq, hc, mul_assoc]
  exact mul_left_cancel₀ hG this
lemma formMatrix_det_sumElim (B : LinearMap.BilinForm ℝ V) (x : ι → V) (y : κ → V)
    (h : ∀ i j, B (x i) (y j) = 0) (h' : ∀ i j, B (y j) (x i) = 0) :
    (formMatrix B (Sum.elim x y)).det = (formMatrix B x).det * (formMatrix B y).det := by
  have : formMatrix B (Sum.elim x y) =
      Matrix.fromBlocks (formMatrix B x) 0 0 (formMatrix B y) := by
    ext (i | i) (j | j) <;> simp [formMatrix, h, h']
  rw [this, Matrix.det_fromBlocks_zero₂₁]
lemma formMatrix_det_pos (B : LinearMap.BilinForm ℝ V) (hs : ∀ x y, B x y = B y x)
    (hp : ∀ x, x ≠ 0 → 0 < B x x) (b : OrthonormalBasis ι ℝ V) :
    0 < (formMatrix B b).det := by
  apply Matrix.PosDef.det_pos
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ ?_
  · ext i j
    simp [formMatrix, hs]
  · intro x hx
    have hv : (∑ i, x i • b i) ≠ 0 := by
      intro h0
      apply hx
      ext i
      have := b.orthonormal.inner_right_fintype x i
      rw [h0, inner_zero_right] at this
      simpa using this.symm
    have key : dotProduct (star x) (Matrix.mulVec (formMatrix B b) x) =
        B (∑ i, x i • b i) (∑ i, x i • b i) := by
      simp only [dotProduct, Matrix.mulVec, formMatrix, Matrix.of_apply, map_sum, map_smul,
        LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, Finset.mul_sum, Pi.star_apply,
        star_trivial]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [key]
    exact hp _ hv
lemma gramDeterminant_subtype (S : Submodule ℝ V) (u : ι → S) :
    gramDeterminant u = gramDeterminant (fun i => (u i : V)) := by
  have : innerMatrix u u = innerMatrix (fun i => (u i : V)) (fun i => (u i : V)) := by
    ext i j
    simp [innerMatrix, Submodule.coe_inner]
  rw [gramDeterminant, this, gramDeterminant]
lemma absDetInBases_sq [FiniteDimensional ℝ V] [FiniteDimensional ℝ F]
    (b : OrthonormalBasis ι ℝ V) (c : OrthonormalBasis ι ℝ F) (f : V →ₗ[ℝ] F) :
    absDetInBases b c f ^ 2 = gramDeterminant (fun i => f (b i)) := by
  have h : LinearMap.toMatrix b.toBasis c.toBasis f = innerMatrix c (fun i => f (b i)) := by
    ext i j
    rw [LinearMap.toMatrix_apply]
    simp [innerMatrix, OrthonormalBasis.coe_toBasis_repr_apply,
      OrthonormalBasis.repr_apply_apply]
  have hs := innerMatrix_det_sq c c (fun i => f (b i))
  rw [gramDeterminant_orthonormalBasis, one_mul] at hs
  rw [absDetInBases, sq_abs, h, hs]
lemma absDetInBases_eq [FiniteDimensional ℝ V] [FiniteDimensional ℝ F]
    (b : OrthonormalBasis ι ℝ V) (c : OrthonormalBasis ι ℝ F) (b' : OrthonormalBasis κ ℝ V)
    (c' : OrthonormalBasis κ ℝ F) (e : κ ≃ ι) (f : V →ₗ[ℝ] F) :
    absDetInBases b c f = absDetInBases b' c' f := by
  have h1 : 0 ≤ absDetInBases b c f := abs_nonneg _
  have h2 : 0 ≤ absDetInBases b' c' f := abs_nonneg _
  refine (sq_eq_sq₀ h1 h2).mp ?_
  rw [absDetInBases_sq, absDetInBases_sq]
  have g1 : gramDeterminant (fun i => f (b i)) = (formMatrix (innerPullback f) b).det := by
    rw [formMatrix_innerPullback]; rfl
  have g2 : gramDeterminant (fun i => f (b' i)) = (formMatrix (innerPullback f) b').det := by
    rw [formMatrix_innerPullback]; rfl
  rw [g1, g2, formMatrix_det_orthonormalBasis (innerPullback f) b b' e]
lemma absDetInBases_eq_absDet [FiniteDimensional ℝ V] [FiniteDimensional ℝ F]
    (h : Module.finrank ℝ V = Module.finrank ℝ F) (b : OrthonormalBasis ι ℝ V)
    (c : OrthonormalBasis ι ℝ F) (f : V →ₗ[ℝ] F) :
    absDetInBases b c f = absDet f := by
  rw [absDet, dif_pos h]
  have e : Fin (Module.finrank ℝ V) ≃ ι :=
    Fintype.equivOfCardEq (by
      rw [Fintype.card_fin, Module.finrank_eq_card_basis b.toBasis])
  exact absDetInBases_eq b c _ _ e.symm.symm f
def orthonormalBasisOfCard (ι : Type*) [Fintype ι] (V : Type*) [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] (h : Fintype.card ι = Module.finrank ℝ V) :
    OrthonormalBasis ι ℝ V :=
  (stdOrthonormalBasis ℝ V).reindex (Fintype.equivFinOfCardEq h).symm
lemma associated_eq_zero_of_isotropic (H : QuadraticForm ℝ V) (h0 : ∀ x, 0 ≤ H x) (x : V)
    (hx : H x = 0) (y : V) : QuadraticMap.associated H x y = 0 := by
  have hH : ∀ z, QuadraticMap.associated H z z = H z :=
    fun z => QuadraticMap.associated_eq_self_apply ℝ H z
  have hs : QuadraticMap.associated H y x = QuadraticMap.associated H x y :=
    QuadraticMap.associated_isSymm ℝ H y x
  by_contra hb
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t * QuadraticMap.associated H x y = -(H y + 1) / 2 :=
    ⟨-(H y + 1) / (2 * QuadraticMap.associated H x y), by field_simp⟩
  have h := h0 (t • x + y)
  rw [← hH] at h
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hH, hx,
    hs] at h
  linarith [h, ht]
lemma formMatrix_innerPullback_det_pos (f : V →ₗ[ℝ] F) (hf : Function.Injective f)
    (b : OrthonormalBasis ι ℝ V) : 0 < (formMatrix (innerPullback f) b).det := by
  refine formMatrix_det_pos _ (fun x y => ?_) (fun x hx => ?_) b
  · simp [innerPullback, real_inner_comm]
  · have hne : f x ≠ 0 := fun h => hx (hf (by rw [h, map_zero]))
    show 0 < inner ℝ (f x) (f x)
    rw [real_inner_self_eq_norm_sq]
    positivity
end Gram
section Key
variable {A C G Gc W : Type} [NormedAddCommGroup A] [InnerProductSpace ℝ A] [FiniteDimensional ℝ A]
  [NormedAddCommGroup C] [InnerProductSpace ℝ C] [FiniteDimensional ℝ C]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G]
  [NormedAddCommGroup Gc] [InnerProductSpace ℝ Gc] [FiniteDimensional ℝ Gc]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
variable {ιa ιt ιq ιγ : Type} [Fintype ιa] [DecidableEq ιa] [Fintype ιt] [DecidableEq ιt]
  [Fintype ιq] [DecidableEq ιq] [Fintype ιγ] [DecidableEq ιγ]
def orthogonalInside (D : G →ₗ[ℝ] A) (E : Submodule ℝ A) : Submodule ℝ E :=
  ((LinearMap.range D).comap E.subtype)ᗮ
lemma associated_gaugeFixedForm {E K : Submodule ℝ A} (H : QuadraticForm ℝ E) (hK : K ≤ E)
    (L : K →ₗ[ℝ] W) (x y : K) :
    QuadraticMap.associated (gaugeFixedForm H hK L) x y =
      QuadraticMap.associated H (Submodule.inclusion hK x) (Submodule.inclusion hK y) +
        inner ℝ (L x) (L y) := by
  rw [gaugeFixedForm, map_add, LinearMap.add_apply, LinearMap.add_apply,
    QuadraticMap.associated_comp, QuadraticMap.associated_comp]
  simp only [LinearMap.compl₁₂_apply]
  rw [QuadraticMap.associated_toQuadraticMap]
  simp only [innerₗ_apply_apply, real_inner_comm (L x) (L y)]
  simp
  ring
lemma sub_expansion_mem_range (D : G →ₗ[ℝ] A) (E : Submodule ℝ A)
    (a0 : OrthonormalBasis ιa ℝ (orthogonalInside D E)) (z : E) :
    ((z - ∑ k, (inner ℝ (((a0 k : orthogonalInside D E) : E) : A) (z : A)) •
      ((a0 k : orthogonalInside D E) : E) : E) : A) ∈ LinearMap.range D := by
  obtain ⟨p, hp, q, hq, hz⟩ := (orthogonalInside D E).exists_add_mem_mem_orthogonal z
  have hq' : q ∈ (LinearMap.range D).comap E.subtype := by
    have h := Submodule.orthogonal_orthogonal ((LinearMap.range D).comap E.subtype)
    rw [orthogonalInside] at hq
    rwa [h] at hq
  have hcoef : ∀ k, inner ℝ (((a0 k : orthogonalInside D E) : E) : A) (z : A) =
      inner ℝ (a0 k) (⟨p, hp⟩ : orthogonalInside D E) := by
    intro k
    have h1 : inner ℝ ((a0 k : orthogonalInside D E) : E) q = 0 :=
      (Submodule.mem_orthogonal _ _).mp hq _ (a0 k).2
    have h2 : inner ℝ (((a0 k : orthogonalInside D E) : E) : A) (z : A) =
        inner ℝ ((a0 k : orthogonalInside D E) : E) z := rfl
    rw [h2, hz, inner_add_right, h1, add_zero]
    rfl
  have hsum : (∑ k, (inner ℝ (((a0 k : orthogonalInside D E) : E) : A) (z : A)) •
      ((a0 k : orthogonalInside D E) : E)) = p := by
    have h := congrArg (Subtype.val) (a0.sum_repr' (⟨p, hp⟩ : orthogonalInside D E))
    simp only [AddSubmonoidClass.coe_finsetSum, Submodule.coe_smul] at h
    refine Eq.trans ?_ h
    exact Finset.sum_congr rfl fun k _ => by rw [hcoef]
  rw [hsum, hz, add_sub_cancel_left]
  exact hq'
lemma determinant_algebra (Ha mu Gw Gl Dq Gs p4 c3 p2 GD c1 c2 Gg Dr d : ℝ)
    (e1 : d * Gw = Ha * mu) (e2 : Gw * Gl = Dq * Gs) (e7 : Gl = p4 * c3) (e4 : Gs = p2 * GD)
    (e5 : Ha = c1 * p2) (e6 : GD = c2 * Gg) (e3 : 1 = Dr * Gg) (hp : p2 ≠ 0) :
    c1 * c3 * p4 * mu * Dr = Dq * d * c2 := by
  apply mul_left_cancel₀ hp
  linear_combination (-(c3 * p4 * mu * Dr)) * e5 - (c3 * p4 * Dr) * e1 - (d * Gw * Dr) * e7
    + (d * Dr) * e2 + (d * Dr * Dq) * e4 + (d * Dr * Dq * p2) * e6 - (d * Dq * p2 * c2) * e3
theorem determinant_identity
    (D : G →ₗ[ℝ] A) (Dc : Gc →ₗ[ℝ] C) (Q' : A →ₗ[ℝ] C) (r' : G →ₗ[ℝ] Gc)
    (hDi : Function.Injective D) (hDci : Function.Injective Dc)
    (hQ' : Function.Surjective Q') (hr' : Function.Surjective r')
    (hc : Q' ∘ₗ D = Dc ∘ₗ r')
    (E : Submodule ℝ A) (hKE : LinearMap.ker Q' ≤ E) (hDE : ∀ x, D x ∈ E)
    (H : QuadraticForm ℝ E) (hH0 : ∀ x, 0 ≤ H x)
    (hHn : ∀ x, H x = 0 ↔ (x : A) ∈ LinearMap.range D)
    (L : LinearMap.ker Q' →ₗ[ℝ] W)
    (hW : Module.finrank ℝ W = Module.finrank ℝ (LinearMap.ker r'))
    (hv : Function.Bijective (L ∘ₗ gaugeRestrictKer D Dc Q' r' hc))
    (hT : (gaugeFixedForm H hKE L).PosDef)
    (a0 : OrthonormalBasis ιa ℝ (orthogonalInside D E)) (l0 : OrthonormalBasis ιt ℝ Eᗮ)
    (c0 : OrthonormalBasis ιt ℝ (LinearMap.range Dc)ᗮ) (e0 : OrthonormalBasis ιq ℝ Gc)
    (γ0 : OrthonormalBasis ιγ ℝ G)
    (d : ℝ)
    (hd : ∀ (ι : Type) [Fintype ι] [DecidableEq ι]
      (b : OrthonormalBasis ι ℝ (LinearMap.ker Q')),
      (Gaussian.KernelIntegral.formMatrixInBasis Q'
        (gaugeFixedForm H hKE L) b).det = d) :
    (formMatrix (QuadraticMap.associated H)
        (fun k => ((a0 k : orthogonalInside D E) : E))).det *
      gramDeterminant (fun i => Dc (e0 i)) *
      (innerMatrix (fun i => ((c0 i : (LinearMap.range Dc)ᗮ) : C))
        (fun i => Q' ((l0 i : Eᗮ) : A))).det ^ 2 *
      absDet (L ∘ₗ gaugeRestrictKer D Dc Q' r' hc) ^ 2 *
      LinearMap.det (r' ∘ₗ LinearMap.adjoint r') =
    LinearMap.det (Q' ∘ₗ LinearMap.adjoint Q') * d * (formMatrix (innerPullback D) γ0).det := by
  classical
  have hdK : Module.finrank ℝ (LinearMap.ker Q') + Module.finrank ℝ C = Module.finrank ℝ A := by
    have h := LinearMap.finrank_range_add_finrank_ker Q'
    rw [LinearMap.range_eq_top.mpr hQ', finrank_top] at h
    omega
  have hdk : Module.finrank ℝ (LinearMap.ker r') + Module.finrank ℝ Gc = Module.finrank ℝ G := by
    have h := LinearMap.finrank_range_add_finrank_ker r'
    rw [LinearMap.range_eq_top.mpr hr', finrank_top] at h
    omega
  have hLs : Function.Surjective L := fun y => by
    obtain ⟨x, hx⟩ := hv.2 y
    exact ⟨_, hx⟩
  have hdL : Module.finrank ℝ (LinearMap.ker L) + Module.finrank ℝ W =
      Module.finrank ℝ (LinearMap.ker Q') := by
    have h := LinearMap.finrank_range_add_finrank_ker L
    rw [LinearMap.range_eq_top.mpr hLs, finrank_top] at h
    omega
  have hdC : Module.finrank ℝ (LinearMap.range Dc)ᗮ + Module.finrank ℝ Gc =
      Module.finrank ℝ C := by
    have h := Submodule.finrank_add_finrank_orthogonal (LinearMap.range Dc)
    rw [LinearMap.finrank_range_of_inj hDci] at h
    omega
  have hdE : Module.finrank ℝ E + Module.finrank ℝ Eᗮ = Module.finrank ℝ A :=
    Submodule.finrank_add_finrank_orthogonal E
  have hdP : Module.finrank ℝ (orthogonalInside D E) + Module.finrank ℝ G =
      Module.finrank ℝ E := by
    have h1 := Submodule.finrank_add_finrank_orthogonal ((LinearMap.range D).comap E.subtype)
    have h3 : ((LinearMap.range D).comap E.subtype).map E.subtype = LinearMap.range D := by
      rw [Submodule.map_comap_subtype]
      refine inf_eq_right.mpr ?_
      rintro _ ⟨x, rfl⟩
      exact hDE x
    have h2 : Module.finrank ℝ ((LinearMap.range D).comap E.subtype) = Module.finrank ℝ G := by
      rw [(Submodule.equivMapOfInjective E.subtype E.injective_subtype _).finrank_eq, h3,
        LinearMap.finrank_range_of_inj hDi]
    rw [orthogonalInside]
    omega
  have cA : Module.finrank ℝ (orthogonalInside D E) = Fintype.card ιa :=
    Module.finrank_eq_card_basis a0.toBasis
  have cT : Module.finrank ℝ Eᗮ = Fintype.card ιt := Module.finrank_eq_card_basis l0.toBasis
  have cT' : Module.finrank ℝ (LinearMap.range Dc)ᗮ = Fintype.card ιt :=
    Module.finrank_eq_card_basis c0.toBasis
  have cQ : Module.finrank ℝ Gc = Fintype.card ιq := Module.finrank_eq_card_basis e0.toBasis
  have cG : Module.finrank ℝ G = Fintype.card ιγ := Module.finrank_eq_card_basis γ0.toBasis
  obtain ⟨s, hs⟩ := LinearMap.exists_rightInverse_of_surjective r' (LinearMap.range_eq_top.mpr hr')
  have hs' : ∀ y, r' (s y) = y := fun y => LinearMap.congr_fun hs y
  have hcx : ∀ x, Q' (D x) = Dc (r' x) := fun x => LinearMap.congr_fun hc x
  let p := Module.finrank ℝ (LinearMap.ker r')
  let κ : OrthonormalBasis (Fin p) ℝ (LinearMap.ker r') := stdOrthonormalBasis ℝ _
  let aL : OrthonormalBasis ιa ℝ (LinearMap.ker L) := orthonormalBasisOfCard ιa _ (by omega)
  let bK : OrthonormalBasis (ιa ⊕ Fin p) ℝ (LinearMap.ker Q') :=
    orthonormalBasisOfCard _ _ (by simp only [Fintype.card_sum, Fintype.card_fin]; omega)
  let cW : OrthonormalBasis (Fin p) ℝ W :=
    orthonormalBasisOfCard _ _ (by simp only [Fintype.card_fin]; omega)
  let aK : ιa → LinearMap.ker Q' := fun i => (aL i : LinearMap.ker Q')
  let kK : Fin p → LinearMap.ker Q' := fun j => gaugeRestrictKer D Dc Q' r' hc (κ j)
  let BH := QuadraticMap.associated H
  let T := gaugeFixedForm H hKE L
  let BT := QuadraticMap.associated T
  let incl := Submodule.inclusion hKE
  have hform : ∀ x y, BT x y = BH (incl x) (incl y) + inner ℝ (L x) (L y) :=
    fun x y => associated_gaugeFixedForm H hKE L x y
  have hBs : ∀ x y, BH x y = BH y x := fun x y => QuadraticMap.associated_isSymm ℝ H x y
  have hkH : ∀ x, H (⟨D x, hDE x⟩ : E) = 0 := fun x => (hHn _).2 ⟨x, rfl⟩
  have hrad : ∀ x y, BH (⟨D x, hDE x⟩ : E) y = 0 :=
    fun x y => associated_eq_zero_of_isotropic H hH0 _ (hkH x) y
  have hinclk : ∀ j, incl (kK j) = (⟨D (κ j), hDE _⟩ : E) := fun j => rfl
  have hLa : ∀ i, L (aK i) = 0 := fun i => (aL i).2
  have E1a : (formMatrix BT (Sum.elim aK kK)).det =
      (formMatrix BT aK).det * (formMatrix BT kK).det := by
    refine formMatrix_det_sumElim BT aK kK (fun i j => ?_) (fun i j => ?_)
    · rw [hform, hLa, inner_zero_left, add_zero, hinclk, hBs, hrad]
    · rw [hform, hLa, inner_zero_right, add_zero, hinclk, hrad]
  let φ : LinearMap.ker L →ₗ[ℝ] E := incl ∘ₗ (LinearMap.ker L).subtype
  let BL : LinearMap.BilinForm ℝ (LinearMap.ker L) := BH.compl₁₂ φ φ
  have E1b : formMatrix BT aK = formMatrix BL aL := by
    ext i j
    simp only [formMatrix, Matrix.of_apply]
    rw [hform, hLa, inner_zero_left, add_zero]
    rfl
  have E1c : formMatrix BT kK = innerMatrix (fun j => (L ∘ₗ gaugeRestrictKer D Dc Q' r' hc) (κ j))
      (fun j => (L ∘ₗ gaugeRestrictKer D Dc Q' r' hc) (κ j)) := by
    ext i j
    simp only [formMatrix, innerMatrix, Matrix.of_apply]
    rw [hform, hinclk, hrad, zero_add]
    rfl
  have hmu : absDet (L ∘ₗ gaugeRestrictKer D Dc Q' r' hc) ^ 2 =
      (innerMatrix (fun j => (L ∘ₗ gaugeRestrictKer D Dc Q' r' hc) (κ j))
        (fun j => (L ∘ₗ gaugeRestrictKer D Dc Q' r' hc) (κ j))).det := by
    rw [← absDetInBases_eq_absDet hW.symm κ cW, absDetInBases_sq]
    rfl
  have hbK : (formMatrix BT bK).det = d := by
    rw [← hd _ bK]
    congr 1
    ext i j
    simp [formMatrix, Gaussian.KernelIntegral.formMatrixInBasis,
      LinearMap.BilinForm.toMatrix_apply, BT, T]
  have e1 : d * gramDeterminant (Sum.elim aK kK) =
      (formMatrix BL aL).det * absDet (L ∘ₗ gaugeRestrictKer D Dc Q' r' hc) ^ 2 := by
    rw [← hbK, ← formMatrix_det_eq BT bK, E1a, E1b, E1c, hmu]
  have hHa : 0 < (formMatrix BL aL).det := by
    refine formMatrix_det_pos BL (fun x y => hBs _ _) (fun x hx => ?_) aL
    have hx' : (x : LinearMap.ker Q') ≠ 0 := fun h => hx (Subtype.ext h)
    have h1 : 0 < T (x : LinearMap.ker Q') := hT _ hx'
    have h2 : BT (x : LinearMap.ker Q') (x : LinearMap.ker Q') = T (x : LinearMap.ker Q') :=
      QuadraticMap.associated_eq_self_apply ℝ T _
    have h3 : BT (x : LinearMap.ker Q') (x : LinearMap.ker Q') = BL x x := by
      rw [hform, show L (x : LinearMap.ker Q') = 0 from x.2, inner_zero_left, add_zero]
      rfl
    rw [← h3, h2]
    exact h1
  have hmupos : 0 < absDet (L ∘ₗ gaugeRestrictKer D Dc Q' r' hc) ^ 2 := by
    rw [hmu, ← formMatrix_innerPullback]
    exact formMatrix_innerPullback_det_pos _ hv.1 κ
  have hGw : gramDeterminant (Sum.elim aK kK) ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at e1
    exact (mul_pos hHa hmupos).ne e1
  let aA : ιa → A := fun i => ((aK i : LinearMap.ker Q') : A)
  let kA : Fin p → A := fun j => D (κ j)
  let gg : ιq → G := fun i => s (e0 i)
  let Dg : ιq → A := fun i => D (gg i)
  let lA : ιt → A := fun i => ((l0 i : Eᗮ) : A)
  have hwA : gramDeterminant (Sum.elim aK kK) = gramDeterminant (Sum.elim aA kA) := by
    rw [gramDeterminant_subtype]
    congr 1
    funext i
    rcases i with i | j <;> rfl
  rw [hwA] at e1 hGw
  let fC : OrthonormalBasis (ιq ⊕ ιt) ℝ C :=
    orthonormalBasisOfCard _ _ (by simp only [Fintype.card_sum]; omega)
  let fC' : OrthonormalBasis (ιt ⊕ ιq) ℝ C :=
    orthonormalBasisOfCard _ _ (by simp only [Fintype.card_sum]; omega)
  let bA : OrthonormalBasis ((ιa ⊕ Fin p) ⊕ (ιq ⊕ ιt)) ℝ A :=
    orthonormalBasisOfCard _ _ (by simp only [Fintype.card_sum, Fintype.card_fin]; omega)
  let bA' : OrthonormalBasis (ιa ⊕ ((Fin p ⊕ ιq) ⊕ ιt)) ℝ A :=
    orthonormalBasisOfCard _ _ (by simp only [Fintype.card_sum, Fintype.card_fin]; omega)
  let bG : OrthonormalBasis (Fin p ⊕ ιq) ℝ G :=
    orthonormalBasisOfCard _ _ (by simp only [Fintype.card_sum, Fintype.card_fin]; omega)
  have hker : ∀ i, Q' (Sum.elim aA kA i) = 0 := by
    rintro (i | j)
    · exact (aK i).2
    · exact (kK j).2
  have e2 := coarea_identity Q' (Sum.elim aA kA) hker (Sum.elim Dg lA) fC bA hGw
  have hQl : (fun i => Q' (Sum.elim Dg lA i)) =
      Sum.elim (fun i => Dc (e0 i)) (fun i => Q' (lA i)) := by
    funext i
    rcases i with i | i
    · show Q' (D (s (e0 i))) = Dc (e0 i)
      rw [hcx, hs']
    · rfl
  have hxc : ∀ i j, inner ℝ ((c0 i : (LinearMap.range Dc)ᗮ) : C) (Dc (e0 j)) = 0 :=
    fun i j => (Submodule.mem_orthogonal' _ _).mp (c0 i).2 _ ⟨e0 j, rfl⟩
  have hc0 : gramDeterminant (fun i => ((c0 i : (LinearMap.range Dc)ᗮ) : C)) = 1 := by
    rw [← gramDeterminant_subtype]
    exact gramDeterminant_orthonormalBasis c0
  have hc3 : 0 < gramDeterminant (fun i => Dc (e0 i)) := by
    have h := formMatrix_innerPullback_det_pos Dc hDci e0
    rwa [formMatrix_innerPullback] at h
  have e7' := gramDeterminant_replace fC' _ (fun i => Q' (lA i)) (fun i => Dc (e0 i)) hxc hc0
    hc3.ne'
  have e7 : gramDeterminant (fun i => Q' (Sum.elim Dg lA i)) =
      (innerMatrix (fun i => ((c0 i : (LinearMap.range Dc)ᗮ) : C))
        (fun i => Q' (lA i))).det ^ 2 * gramDeterminant (fun i => Dc (e0 i)) := by
    rw [hQl, ← e7', ← gramDeterminant_comp_equiv
      (Sum.elim (fun i => Q' (lA i)) (fun i => Dc (e0 i))) (Equiv.sumComm ιq ιt)]
    congr 1
    funext i
    rcases i with i | i <;> rfl
  let κG : Fin p → G := fun j => (κ j : G)
  have hκ1 : gramDeterminant κG = 1 := by
    rw [← gramDeterminant_orthonormalBasis κ]
    exact (gramDeterminant_subtype _ _).symm
  have e3' := coarea_identity r' κG (fun j => (κ j).2) gg e0 bG (by rw [hκ1]; exact one_ne_zero)
  have hrg : (fun i => r' (gg i)) = e0 := funext fun i => hs' (e0 i)
  have e3 : 1 = LinearMap.det (r' ∘ₗ LinearMap.adjoint r') * gramDeterminant (Sum.elim κG gg) := by
    rw [hκ1, one_mul, hrg, gramDeterminant_orthonormalBasis] at e3'
    exact e3'
  have hDγ : Sum.elim kA Dg = fun i => D (Sum.elim κG gg i) := by
    funext i
    rcases i with i | i <;> rfl
  have e6 : gramDeterminant (Sum.elim kA Dg) =
      (formMatrix (innerPullback D) γ0).det * gramDeterminant (Sum.elim κG gg) := by
    have h1 : gramDeterminant (fun i => D (Sum.elim κG gg i)) =
        (formMatrix (innerPullback D) (Sum.elim κG gg)).det := by
      rw [formMatrix_innerPullback]
      rfl
    have hcard : Fintype.card (Fin p ⊕ ιq) = Fintype.card ιγ := by
      simp only [Fintype.card_sum, Fintype.card_fin]
      omega
    rw [hDγ, h1, formMatrix_det_eq (innerPullback D) bG,
      formMatrix_det_orthonormalBasis (innerPullback D) γ0 bG (Fintype.equivOfCardEq hcard)]
  have hc2 := formMatrix_innerPullback_det_pos D hDi γ0
  have hGg : gramDeterminant (Sum.elim κG gg) ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at e3
    exact one_ne_zero e3
  have hGD : gramDeterminant (Sum.elim kA Dg) ≠ 0 := by
    rw [e6]
    exact mul_ne_zero hc2.ne' hGg
  let a0A : ιa → A := fun k => (((a0 k : orthogonalInside D E) : E) : A)
  have hl : ∀ (x : E) j, inner ℝ (x : A) (lA j) = 0 :=
    fun x j => (Submodule.mem_orthogonal _ _).mp (l0 j).2 _ x.2
  have hlD : ∀ x j, inner ℝ (D x) (lA j) = 0 := fun x j => hl ⟨D x, hDE x⟩ j
  have hperp : ∀ i x, inner ℝ (a0A i) (D x) = 0 := fun i x =>
    (Submodule.mem_orthogonal' _ _).mp (a0 i).2 (⟨D x, hDE x⟩ : E) ⟨x, rfl⟩
  have hy : gramDeterminant (Sum.elim (Sum.elim kA Dg) lA) = gramDeterminant (Sum.elim kA Dg) := by
    have hl1 : gramDeterminant lA = 1 := by
      rw [← gramDeterminant_orthonormalBasis l0]
      exact (gramDeterminant_subtype _ _).symm
    rw [gramDeterminant_sumElim_of_orthogonal (Sum.elim kA Dg) lA, hl1, mul_one]
    rintro (i | i) j
    · exact hlD _ j
    · exact hlD _ j
  have hxy : ∀ i j, inner ℝ (a0A i) (Sum.elim (Sum.elim kA Dg) lA j) = 0 := by
    rintro i ((j | j) | j)
    · exact hperp i _
    · exact hperp i _
    · exact hl _ j
  have ha1 : gramDeterminant a0A = 1 := by
    have h1 : gramDeterminant a0A =
        gramDeterminant (fun k => ((a0 k : orthogonalInside D E) : E)) :=
      (gramDeterminant_subtype E _).symm
    rw [h1, ← gramDeterminant_subtype, gramDeterminant_orthonormalBasis]
  have e4' := gramDeterminant_replace bA' a0A aA (Sum.elim (Sum.elim kA Dg) lA) hxy ha1
    (by rw [hy]; exact hGD)
  have e4 : gramDeterminant (Sum.elim (Sum.elim aA kA) (Sum.elim Dg lA)) =
      (innerMatrix a0A aA).det ^ 2 * gramDeterminant (Sum.elim kA Dg) := by
    rw [← hy, ← e4', ← gramDeterminant_comp_equiv (Sum.elim aA (Sum.elim (Sum.elim kA Dg) lA))
      ((Equiv.sumAssoc ιa (Fin p) (ιq ⊕ ιt)).trans
        (Equiv.sumCongr (Equiv.refl ιa) (Equiv.sumAssoc (Fin p) ιq ιt).symm))]
    congr 1
    funext i
    rcases i with (i | i) | (i | i) <;> rfl
  let aE : ιa → E := fun i => incl (aK i)
  let a0E : ιa → E := fun k => ((a0 k : orthogonalInside D E) : E)
  let P : Matrix ιa ιa ℝ := Matrix.of fun i k => inner ℝ (a0A k) (aA i)
  let yy : ιa → E := fun i => ∑ k, P i k • a0E k
  have hrest : ∀ i, ∃ x, aE i = yy i + (⟨D x, hDE x⟩ : E) := by
    intro i
    obtain ⟨x, hx⟩ := sub_expansion_mem_range D E a0 (aE i)
    refine ⟨x, ?_⟩
    have h1 : aE i - yy i = (⟨D x, hDE x⟩ : E) := Subtype.ext hx.symm
    exact sub_eq_iff_eq_add'.mp h1
  have hBHeq : formMatrix BH aE = formMatrix BH yy := by
    ext i j
    obtain ⟨x, hx⟩ := hrest i
    obtain ⟨x', hx'⟩ := hrest j
    simp only [formMatrix, Matrix.of_apply]
    rw [hx, hx', map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, hrad, hrad, add_zero,
      add_zero, hBs (yy i) ⟨D x', hDE x'⟩, hrad, add_zero]
  have e5 : (formMatrix BL aL).det = (formMatrix BH a0E).det * (innerMatrix a0A aA).det ^ 2 := by
    have h1 : formMatrix BL aL = formMatrix BH aE := by
      ext i j
      rfl
    have h2 := formMatrix_of_expansion BH a0E yy P (fun i => rfl)
    have h3 : P = (innerMatrix a0A aA).transpose := by
      ext i j
      rfl
    rw [h1, hBHeq, h2, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, h3,
      Matrix.det_transpose]
    ring
  have hp2 : (innerMatrix a0A aA).det ^ 2 ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at e5
    exact hHa.ne' e5
  exact determinant_algebra _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ e1 e2 e7 e4 e5 e6 e3 hp2
lemma finrank_orthogonal_constraintPreimage (Dc : Gc →ₗ[ℝ] C) (Q : A →ₗ[ℝ] C)
    (hQ : Function.Surjective Q) :
    Module.finrank ℝ (constraintPreimage Q Dc)ᗮ = Module.finrank ℝ (LinearMap.range Dc)ᗮ := by
  let K := (LinearMap.range Dc)ᗮ
  let f : A →ₗ[ℝ] K := (K.orthogonalProjectionOnto : C →ₗ[ℝ] K) ∘ₗ Q
  have hs : Function.Surjective f := fun y => by
    obtain ⟨x, hx⟩ := hQ (y : C)
    refine ⟨x, ?_⟩
    show K.orthogonalProjectionOnto (Q x) = y
    rw [hx]
    exact Submodule.orthogonalProjectionOnto_mem_subspace_eq_self y
  have hk : LinearMap.ker f = constraintPreimage Q Dc := by
    ext x
    have h1 : x ∈ LinearMap.ker f ↔ K.orthogonalProjectionOnto (Q x) = 0 := Iff.rfl
    rw [h1, Submodule.orthogonalProjectionOnto_eq_zero_iff, Submodule.orthogonal_orthogonal]
    rfl
  have h := LinearMap.finrank_range_add_finrank_ker f
  rw [LinearMap.range_eq_top.mpr hs, finrank_top, hk] at h
  have h2 := Submodule.finrank_add_finrank_orthogonal (constraintPreimage Q Dc)
  change _ = Module.finrank ℝ K
  omega
lemma gaugeFixedForm_posDef (D : G →ₗ[ℝ] A) (Dc : Gc →ₗ[ℝ] C) (Q' : A →ₗ[ℝ] C)
    (r' : G →ₗ[ℝ] Gc) (hDci : Function.Injective Dc) (hc : Q' ∘ₗ D = Dc ∘ₗ r')
    (E : Submodule ℝ A) (hKE : LinearMap.ker Q' ≤ E)
    (H : QuadraticForm ℝ E) (hH0 : ∀ x, 0 ≤ H x)
    (hHn : ∀ x, H x = 0 ↔ (x : A) ∈ LinearMap.range D)
    (L : LinearMap.ker Q' →ₗ[ℝ] W)
    (hv : Function.Injective (L ∘ₗ gaugeRestrictKer D Dc Q' r' hc)) :
    (gaugeFixedForm H hKE L).PosDef := by
  intro x hx
  have hT : gaugeFixedForm H hKE L x =
      H (Submodule.inclusion hKE x) + inner ℝ (L x) (L x) := by
    rw [← QuadraticMap.associated_eq_self_apply ℝ (gaugeFixedForm H hKE L) x,
      associated_gaugeFixedForm, QuadraticMap.associated_eq_self_apply ℝ H]
  rw [hT]
  have h1 := hH0 (Submodule.inclusion hKE x)
  have h2 : 0 ≤ inner ℝ (L x) (L x) := real_inner_self_nonneg
  by_contra hcon
  have h3 : H (Submodule.inclusion hKE x) = 0 := by linarith
  have h4 : inner ℝ (L x) (L x) = 0 := by linarith
  have h5 : L x = 0 := inner_self_eq_zero.mp h4
  obtain ⟨t, ht⟩ := (hHn _).1 h3
  have ht' : D t = (x : A) := ht
  have h6 : r' t = 0 := by
    apply hDci
    have h7 : Q' (D t) = Dc (r' t) := LinearMap.congr_fun hc t
    rw [map_zero, ← h7, ht']
    exact x.2
  have h8 : gaugeRestrictKer D Dc Q' r' hc ⟨t, h6⟩ = x := Subtype.ext ht'
  have h9 : (L ∘ₗ gaugeRestrictKer D Dc Q' r' hc) ⟨t, h6⟩ =
      (L ∘ₗ gaugeRestrictKer D Dc Q' r' hc) 0 := by
    rw [map_zero, LinearMap.comp_apply, h8, h5]
  have h10 := hv h9
  apply hx
  rw [← h8, h10, map_zero]
lemma absDet_nonneg {V F : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (f : V →ₗ[ℝ] F) : 0 ≤ absDet f := by
  rw [absDet]
  split_ifs
  · exact abs_nonneg _
  · exact le_rfl
lemma number_arithmetic (Dq d Dr mu S c2 Pw : ℝ) (hDq : 0 < Dq) (hd : 0 < d) (hDr : 0 < Dr)
    (hmu : 0 ≤ mu) (hc2 : 0 < c2) (h : S * mu ^ 2 * Dr = Dq * d * c2) :
    Dq ^ (-(1 / 2) : ℝ) * (Pw * d ^ (-(1 / 2) : ℝ)) * mu * Dr ^ (1 / 2 : ℝ) =
      Pw * (c2 / S) ^ (1 / 2 : ℝ) := by
  have hS : S ≠ 0 := by
    intro h0
    rw [h0, zero_mul, zero_mul] at h
    exact (mul_pos (mul_pos hDq hd) hc2).ne h
  have a1 : (Dr ^ (1 / 2 : ℝ)) ^ 2 = Dr := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hDr.le]
    norm_num
  have a2 : ∀ x : ℝ, 0 < x → (x ^ (-(1 / 2) : ℝ)) ^ 2 = x⁻¹ := by
    intro x hx
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]
    norm_num
    exact Real.rpow_neg_one x
  have e : c2 / S = (mu * Dr ^ (1 / 2 : ℝ) * Dq ^ (-(1 / 2) : ℝ) * d ^ (-(1 / 2) : ℝ)) ^ 2 := by
    rw [mul_pow, mul_pow, mul_pow, a1, a2 _ hDq, a2 _ hd]
    field_simp
    linarith
  have h5 : ∀ y : ℝ, 0 ≤ y → (y ^ 2) ^ (1 / 2 : ℝ) = y := fun y hy => by
    rw [← Real.sqrt_eq_rpow, Real.sqrt_sq hy]
  rw [e, h5 _ (by positivity)]
  ring
end Key
theorem gaugeFixingIndependence_proof
    (hGauss : Gaussian.KernelIntegral.GaussianIntegralOnKernel) : GaugeFixingIndependence := by
  refine ⟨?_, ?_⟩
  · intro V W _ _ _ _ _ _ f _ ι _ _ b c
    have h : Module.finrank ℝ V = Module.finrank ℝ W := by
      rw [Module.finrank_eq_card_basis b.toBasis, Module.finrank_eq_card_basis c.toBasis]
    exact absDetInBases_eq_absDet h b c f
  · intro A C G Gc _ _ _ _ _ _ _ _ _ _ _ _ D Dc Q r hDi hDci hQ hr hc H hH0 hHn
    let E := constraintPreimage Q Dc
    have hfin := finrank_orthogonal_constraintPreimage Dc Q hQ
    let a0 := stdOrthonormalBasis ℝ (orthogonalInside D E)
    let l0 := stdOrthonormalBasis ℝ Eᗮ
    let c0 : OrthonormalBasis (Fin (Module.finrank ℝ Eᗮ)) ℝ (LinearMap.range Dc)ᗮ :=
      (stdOrthonormalBasis ℝ (LinearMap.range Dc)ᗮ).reindex (finCongr hfin.symm)
    let e0 := stdOrthonormalBasis ℝ Gc
    let γ0 := stdOrthonormalBasis ℝ G
    refine ⟨(2 * Real.pi) ^ (((Module.finrank ℝ A - Module.finrank ℝ C : ℕ) : ℝ) / 2) *
      ((formMatrix (innerPullback D) γ0).det /
        ((formMatrix (QuadraticMap.associated H)
            (fun k => ((a0 k : orthogonalInside D E) : E))).det *
          gramDeterminant (fun i => Dc (e0 i)) *
          (innerMatrix (fun i => ((c0 i : (LinearMap.range Dc)ᗮ) : C))
            (fun i => Q ((l0 i : Eᗮ) : A))).det ^ 2)) ^ (1 / 2 : ℝ), ?_⟩
    intro m hm
    have hcx : ∀ x, Q (D x) = Dc (r x) := fun x => LinearMap.congr_fun hc x
    have hQ'x : ∀ x, shiftedConstraint Q Dc m x = Q x + Dc (m x) := fun x => rfl
    have hr'x : ∀ x, shiftedGaugeMap r m D x = r x + m (D x) := fun x => rfl
    have hcomm : shiftedConstraint Q Dc m ∘ₗ D = Dc ∘ₗ shiftedGaugeMap r m D := by
      ext x
      simp only [LinearMap.comp_apply, hQ'x, hr'x, hcx, map_add]
    have hcx' : ∀ x, shiftedConstraint Q Dc m (D x) = Dc (shiftedGaugeMap r m D x) :=
      fun x => LinearMap.congr_fun hcomm x
    have hQ's : Function.Surjective (shiftedConstraint Q Dc m) := by
      intro y
      obtain ⟨x, hx⟩ := hQ y
      obtain ⟨g, hg⟩ := hm (m x)
      refine ⟨x - D g, ?_⟩
      rw [map_sub, hcx', hg, hQ'x, hx]
      abel
    have hKE : LinearMap.ker (shiftedConstraint Q Dc m) ≤ E := by
      intro x hx
      have h0 : Q x + Dc (m x) = 0 := hx
      refine ⟨-m x, ?_⟩
      rw [map_neg]
      exact (eq_neg_of_add_eq_zero_left h0).symm
    have hDE : ∀ x, D x ∈ E := fun x => ⟨r x, (hcx x).symm⟩
    let T0 : QuadraticForm ℝ (LinearMap.ker (shiftedGaugeMap r m D)) :=
      LinearMap.BilinMap.toQuadraticMap (innerₗ _)
    have hT0 : T0.PosDef := by
      intro x hx
      have hpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
      show 0 < inner ℝ x x
      rw [real_inner_self_eq_norm_sq]
      positivity
    have hDr : 0 < LinearMap.det
        (shiftedGaugeMap r m D ∘ₗ LinearMap.adjoint (shiftedGaugeMap r m D)) :=
      (hGauss G Gc _ hm T0 hT0).1
    refine ⟨hQ's, hDr, hcomm, hKE, ?_⟩
    intro W _ _ _ L hW hv
    have hT := gaugeFixedForm_posDef D Dc _ _ hDci hcomm E hKE H hH0 hHn L hv.1
    refine ⟨hT, ?_⟩
    obtain ⟨hDq, d, hd0, hdall, -, -, hval⟩ := hGauss A C _ hQ's _ hT
    have hk := determinant_identity D Dc _ _ hDi hDci hQ's hm hcomm E hKE hDE H hH0 hHn L hW hv
      hT a0 l0 c0 e0 γ0 d hdall
    have hp4 : innerMatrix (fun i => ((c0 i : (LinearMap.range Dc)ᗮ) : C))
          (fun i => shiftedConstraint Q Dc m ((l0 i : Eᗮ) : A)) =
        innerMatrix (fun i => ((c0 i : (LinearMap.range Dc)ᗮ) : C))
          (fun i => Q ((l0 i : Eᗮ) : A)) := by
      ext i j
      simp only [innerMatrix, Matrix.of_apply, hQ'x, inner_add_right]
      rw [(Submodule.mem_orthogonal' _ _).mp (c0 i).2 _ ⟨m _, rfl⟩, add_zero]
    rw [hp4] at hk
    have hI : kernelGaussianIntegral (shiftedConstraint Q Dc m) (gaugeFixedForm H hKE L) = _ :=
      hval
    have hdim : Module.finrank ℝ (LinearMap.ker (shiftedConstraint Q Dc m)) =
        Module.finrank ℝ A - Module.finrank ℝ C := by
      have h := LinearMap.finrank_range_add_finrank_ker (shiftedConstraint Q Dc m)
      rw [LinearMap.range_eq_top.mpr hQ's, finrank_top] at h
      omega
    rw [gaugeFixedNumber, constrainedGaussianNumber, hI, hdim]
    exact number_arithmetic _ _ _ _ _ _ _ hDq hd0 hDr (absDet_nonneg _)
      (formMatrix_innerPullback_det_pos D hDi γ0) hk
end YangMills.Construction.GaussianConstraint.GaugeFixingChangeProof
end
