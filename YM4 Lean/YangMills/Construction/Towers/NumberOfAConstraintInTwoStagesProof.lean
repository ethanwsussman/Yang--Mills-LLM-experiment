import YangMills.Construction.Gaussian.KernelGaussianIntegral
import YangMills.Construction.Towers.NumberOfAConstraintInTwoStages
import Mathlib
set_option autoImplicit false
open Matrix Module
open scoped InnerProductSpace
noncomputable section
namespace YangMills.Construction.ConstraintStages
open YangMills.Construction.GaussianConstraint
open YangMills.Construction.Gaussian.KernelIntegral (formMatrixInBasis)
section Gram
variable {V : Type} [AddCommGroup V] [Module ℝ V]
theorem gram_matrix_of_linear_combinations {ι κ : Type} [Fintype ι] [Fintype κ]
    (B : LinearMap.BilinForm ℝ V)
    (w : κ → V) (y : ι → V) (R : Matrix κ ι ℝ) (h : ∀ j, y j = ∑ i, R i j • w i) :
    (Matrix.of fun i j => B (y i) (y j)) = Rᵀ * (Matrix.of fun k l => B (w k) (w l)) * R := by
  ext i j
  simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, h i, h j]
  simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, smul_eq_mul,
    Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
theorem det_gram_sum_elim_of_orthogonal {α β : Type} [Fintype α] [Fintype β] [DecidableEq α]
    [DecidableEq β]
    (B : LinearMap.BilinForm ℝ V) (w₁ : α → V) (w₂ x : β → V) (X : Matrix α β ℝ)
    (A : Matrix β β ℝ) (h₁₂ : ∀ a b, B (w₁ a) (w₂ b) = 0) (h₂₁ : ∀ b a, B (w₂ b) (w₁ a) = 0)
    (hx : ∀ b, x b = ∑ a, X a b • w₁ a + ∑ i, A i b • w₂ i) :
    (Matrix.of fun i j => B (Sum.elim w₁ x i) (Sum.elim w₁ x j)).det =
      A.det ^ 2 * (Matrix.of fun a a' => B (w₁ a) (w₁ a')).det *
        (Matrix.of fun b b' => B (w₂ b) (w₂ b')).det := by
  set R : Matrix (α ⊕ β) (α ⊕ β) ℝ := fromBlocks 1 X 0 A with hR
  have hy : ∀ j, Sum.elim w₁ x j = ∑ i, R i j • Sum.elim w₁ w₂ i := by
    rintro (a | b)
    · simp [hR, Fintype.sum_sum_type, Matrix.one_apply]
    · simp [hR, Fintype.sum_sum_type, hx b]
  have hG : (Matrix.of fun k l => B (Sum.elim w₁ w₂ k) (Sum.elim w₁ w₂ l)) =
      fromBlocks (Matrix.of fun a a' => B (w₁ a) (w₁ a')) 0 0
        (Matrix.of fun b b' => B (w₂ b) (w₂ b')) := by
    ext (i | i) (j | j) <;> simp [h₁₂, h₂₁]
  rw [gram_matrix_of_linear_combinations B _ _ R hy, hG, det_mul, det_mul, det_transpose, hR,
    det_fromBlocks_zero₂₁, det_fromBlocks_zero₂₁]
  simp only [det_one, one_mul]
  ring
end Gram
section Euclid
variable {V W : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
theorem det_comp_adjoint_eq_det_block_sq {ι γ : Type} [Fintype ι] [Fintype γ] [DecidableEq γ]
    (P : V →ₗ[ℝ] W) (e : OrthonormalBasis (ι ⊕ γ) ℝ V) (w : OrthonormalBasis γ ℝ W)
    (h : ∀ i, P (e (Sum.inl i)) = 0) :
    LinearMap.det (P ∘ₗ LinearMap.adjoint P) =
      (Matrix.of fun i j => ⟪w i, P (e (Sum.inr j))⟫_ℝ).det ^ 2 := by
  have hm : LinearMap.toMatrix w.toBasis w.toBasis (P ∘ₗ LinearMap.adjoint P) =
      (Matrix.of fun i j => ⟪w i, P (e (Sum.inr j))⟫_ℝ) *
        (Matrix.of fun i j => ⟪w i, P (e (Sum.inr j))⟫_ℝ)ᵀ := by
    ext i j
    rw [LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis,
      OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.repr_apply_apply,
      LinearMap.comp_apply, ← LinearMap.adjoint_inner_left, ← e.sum_inner_mul_inner,
      Fintype.sum_sum_type]
    simp only [mul_apply, of_apply, transpose_apply, LinearMap.adjoint_inner_left,
      LinearMap.adjoint_inner_right, h, inner_zero_right, zero_mul, Finset.sum_const_zero, zero_add]
    exact Finset.sum_congr rfl fun k _ => by rw [real_inner_comm (P (e (Sum.inr k))) (w j)]
  rw [← LinearMap.det_toMatrix w.toBasis, hm, det_mul, det_transpose, sq]
theorem exists_orthonormalBasis_sum_elim {ι κ : Type} [Fintype ι] [Fintype κ] (u : ι → V)
    (v : κ → V)
    (hu : Orthonormal ℝ u) (hv : Orthonormal ℝ v) (huv : ∀ i j, ⟪u i, v j⟫_ℝ = 0)
    (hc : finrank ℝ V = Fintype.card ι + Fintype.card κ) :
    ∃ b : OrthonormalBasis (ι ⊕ κ) ℝ V, (∀ i, b (Sum.inl i) = u i) ∧ ∀ j, b (Sum.inr j) = v j := by
  classical
  have ho : Orthonormal ℝ (Sum.elim u v) := by
    rw [orthonormal_iff_ite]
    rintro (i | i) (j | j)
    · simpa using orthonormal_iff_ite.1 hu i j
    · simpa using huv i j
    · simpa [real_inner_comm] using huv j i
    · simpa using orthonormal_iff_ite.1 hv i j
  obtain ⟨b, hb⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq (𝕜 := ℝ)
    (ι := ι ⊕ κ) (by simpa using hc) (v := Sum.elim u v) (s := Set.univ)
    (ho.comp _ Subtype.val_injective)
  exact ⟨b, fun i => by simpa using hb (.inl i) trivial,
    fun j => by simpa using hb (.inr j) trivial⟩
theorem exists_orthonormal_family_in_submodule (U : Submodule ℝ V) {ι : Type} [Fintype ι]
    (h : Fintype.card ι = finrank ℝ U) : ∃ v : ι → V, Orthonormal ℝ v ∧ ∀ i, v i ∈ U := by
  classical
  have e : Fin (finrank ℝ U) ≃ ι := Fintype.equivOfCardEq (by simpa using h.symm)
  let b := (stdOrthonormalBasis ℝ U).reindex e
  exact ⟨fun i => (b i : V), b.orthonormal.comp_linearIsometry U.subtypeₗᵢ, fun i => (b i).2⟩
omit [FiniteDimensional ℝ W] in
theorem finrank_ker_add_finrank_of_surjective (P : V →ₗ[ℝ] W) (hP : Function.Surjective P) :
    finrank ℝ (LinearMap.ker P) + finrank ℝ W = finrank ℝ V := by
  have := LinearMap.finrank_range_add_finrank_ker P
  rw [LinearMap.range_eq_top.2 hP, finrank_top] at this
  omega
end Euclid
section Stages
variable {E F F' : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup F'] [InnerProductSpace ℝ F'] [FiniteDimensional ℝ F']
omit [FiniteDimensional ℝ F'] in
theorem exists_orthogonal_section (M : E →ₗ[ℝ] F) (N : F →ₗ[ℝ] F')
    (T : QuadraticForm ℝ (LinearMap.ker (N ∘ₗ M))) (hM : Function.Surjective M) (hT : T.PosDef) :
    ∃ σ : LinearMap.ker N →ₗ[ℝ] LinearMap.ker (N ∘ₗ M), (∀ ζ, M (σ ζ : E) = ζ) ∧
      ∀ ζ (κ : LinearMap.ker (N ∘ₗ M)), M (κ : E) = 0 →
        QuadraticMap.associated T (σ ζ) κ = 0 := by
  let Q : LinearMap.ker (N ∘ₗ M) →ₗ[ℝ] LinearMap.ker N :=
    (M ∘ₗ (LinearMap.ker (N ∘ₗ M)).subtype).codRestrict (LinearMap.ker N)
      (fun x => LinearMap.mem_ker.2 (LinearMap.mem_ker.1 x.2))
  have hQ : Function.Surjective Q := by
    intro ζ
    obtain ⟨x, hx⟩ := hM ζ
    refine ⟨⟨x, ?_⟩, Subtype.ext hx⟩
    simp [hx]
  obtain ⟨ρ, hρ⟩ := Q.exists_rightInverse_of_surjective (LinearMap.range_eq_top.2 hQ)
  have hρ' : ∀ ζ, Q (ρ ζ) = ζ := fun ζ => LinearMap.congr_fun hρ ζ
  let B : LinearMap.BilinForm ℝ (LinearMap.ker (N ∘ₗ M)) := QuadraticMap.associated T
  have hsymm : ∀ x y, B x y = B y x := fun x y => QuadraticMap.associated_isSymm ℝ T x y
  have hrefl : B.IsRefl := fun x y h => by rw [hsymm]; exact h
  have hdisj : Disjoint (LinearMap.ker Q) (B.orthogonal (LinearMap.ker Q)) := by
    rw [Submodule.disjoint_def]
    intro x hx hx'
    by_contra hne
    have hpos := hT x hne
    have h0 : B x x = 0 := (LinearMap.BilinForm.mem_orthogonal_iff.1 hx') x hx
    have h1 : B x x = T x := QuadraticMap.associated_eq_self_apply ℝ T x
    linarith
  have hc : IsCompl (LinearMap.ker Q) (B.orthogonal (LinearMap.ker Q)) :=
    (LinearMap.BilinForm.restrict_nondegenerate_iff_isCompl_orthogonal hrefl).1
      (LinearMap.BilinForm.nondegenerate_restrict_of_disjoint_orthogonal B hrefl hdisj)
  let P := Submodule.prodEquivOfIsCompl _ _ hc
  have hsplit : ∀ y, ((P.symm y).1 : LinearMap.ker (N ∘ₗ M)) + ((P.symm y).2 : _) = y := fun y => by
    have := P.apply_symm_apply y
    rwa [Submodule.coe_prodEquivOfIsCompl'] at this
  refine ⟨(B.orthogonal (LinearMap.ker Q)).subtype ∘ₗ LinearMap.snd ℝ _ _ ∘ₗ P.symm.toLinearMap ∘ₗ ρ,
    fun ζ => ?_, fun ζ κ hκ => ?_⟩
  · have h1 : Q ((P.symm (ρ ζ)).1 : LinearMap.ker (N ∘ₗ M)) = 0 := (P.symm (ρ ζ)).1.2
    have h2 := congrArg Q (hsplit (ρ ζ))
    rw [map_add, h1, zero_add, hρ'] at h2
    exact congrArg Subtype.val h2
  · have hκ' : κ ∈ LinearMap.ker Q := Subtype.ext hκ
    have := (LinearMap.BilinForm.mem_orthogonal_iff.1 (P.symm (ρ ζ)).2.2) κ hκ'
    exact (hsymm _ _).trans this
theorem det_comp_adjoint_mul_block_sq {α β ρ : Type} [Fintype α] [Fintype β] [Fintype ρ]
    [DecidableEq α] [DecidableEq β] [DecidableEq ρ] (M : E →ₗ[ℝ] F) (N : F →ₗ[ℝ] F')
    (e : OrthonormalBasis ((α ⊕ β) ⊕ ρ) ℝ E) (f : OrthonormalBasis (β ⊕ ρ) ℝ F)
    (g : OrthonormalBasis ρ ℝ F') (he₁ : ∀ a, M (e (Sum.inl (Sum.inl a))) = 0)
    (he₂ : ∀ b, N (M (e (Sum.inl (Sum.inr b)))) = 0) (hf₁ : ∀ b, N (f (Sum.inl b)) = 0)
    (hf₂ : ∀ r x, N x = 0 → ⟪f (Sum.inr r), x⟫_ℝ = 0) :
    LinearMap.det ((N ∘ₗ M) ∘ₗ LinearMap.adjoint (N ∘ₗ M)) *
        (Matrix.of fun i j => ⟪f (Sum.inl i), M (e (Sum.inl (Sum.inr j)))⟫_ℝ).det ^ 2 =
      LinearMap.det (M ∘ₗ LinearMap.adjoint M) * LinearMap.det (N ∘ₗ LinearMap.adjoint N) := by
  set A : Matrix β β ℝ := Matrix.of fun i j => ⟪f (Sum.inl i), M (e (Sum.inl (Sum.inr j)))⟫_ℝ
  set G : Matrix ρ ρ ℝ := Matrix.of fun i j => ⟪f (Sum.inr i), M (e (Sum.inr j))⟫_ℝ
  set N₂ : Matrix ρ ρ ℝ := Matrix.of fun i j => ⟪g i, N (f (Sum.inr j))⟫_ℝ
  set C : Matrix β ρ ℝ := Matrix.of fun i j => ⟪f (Sum.inl i), M (e (Sum.inr j))⟫_ℝ
  have h1 : LinearMap.det ((N ∘ₗ M) ∘ₗ LinearMap.adjoint (N ∘ₗ M)) = (N₂ * G).det ^ 2 := by
    rw [det_comp_adjoint_eq_det_block_sq (N ∘ₗ M) e g (by
      rintro (a | b)
      · simp [he₁ a]
      · simpa using he₂ b)]
    congr 2
    ext i j
    simp only [Matrix.of_apply, Matrix.mul_apply, LinearMap.comp_apply, N₂, G]
    conv_lhs => rw [← f.sum_repr' (M (e (Sum.inr j)))]
    rw [map_sum, inner_sum, Fintype.sum_sum_type]
    simp only [map_smul, hf₁, smul_zero, inner_zero_right, Finset.sum_const_zero, zero_add,
      real_inner_smul_right]
    exact Finset.sum_congr rfl fun r _ => mul_comm _ _
  have h2 : LinearMap.det (M ∘ₗ LinearMap.adjoint M) = (fromBlocks A C 0 G).det ^ 2 := by
    rw [det_comp_adjoint_eq_det_block_sq M (e.reindex (Equiv.sumAssoc α β ρ)) f
      (by simpa using he₁)]
    congr 2
    ext (i | i) (j | j)
    · simp [A]
    · simp [C]
    · simpa using hf₂ i _ (he₂ j)
    · simp [G]
  have h3 : LinearMap.det (N ∘ₗ LinearMap.adjoint N) = N₂.det ^ 2 :=
    det_comp_adjoint_eq_det_block_sq N f g hf₁
  rw [h1, h2, h3, det_fromBlocks_zero₂₁, det_mul]
  ring
omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [FiniteDimensional ℝ F'] in
theorem det_gram_inclusion_sum_elim {α β : Type} [Fintype α] [Fintype β] [DecidableEq α]
    [DecidableEq β]
    (M : E →ₗ[ℝ] F) (N : F →ₗ[ℝ] F') (T : QuadraticForm ℝ (LinearMap.ker (N ∘ₗ M)))
    (σ : LinearMap.ker N →ₗ[ℝ] LinearMap.ker (N ∘ₗ M)) (hσ : ∀ ζ, M (σ ζ : E) = ζ)
    (hB : ∀ ζ (κ : LinearMap.ker (N ∘ₗ M)), M (κ : E) = 0 →
      QuadraticMap.associated T (σ ζ) κ = 0)
    (u : OrthonormalBasis α ℝ (LinearMap.ker M)) (v : OrthonormalBasis β ℝ (LinearMap.ker N))
    (c : β → LinearMap.ker (N ∘ₗ M)) :
    (Matrix.of fun i j => QuadraticMap.associated T
      (Sum.elim (fun a => Submodule.inclusion (LinearMap.ker_le_ker_comp M N) (u a)) c i)
      (Sum.elim (fun a => Submodule.inclusion (LinearMap.ker_le_ker_comp M N) (u a)) c j)).det =
    (Matrix.of fun i j => ⟪(v i : F), M (c j : E)⟫_ℝ).det ^ 2 *
      (formMatrixInBasis M (restrictToInnerKernel M N T) u).det *
      (formMatrixInBasis N (T.comp σ) v).det := by
  let incl := Submodule.inclusion (LinearMap.ker_le_ker_comp M N)
  let B : LinearMap.BilinForm ℝ (LinearMap.ker (N ∘ₗ M)) := QuadraticMap.associated T
  have hsymm : ∀ x y, B x y = B y x := fun x y => QuadraticMap.associated_isSymm ℝ T x y
  let ζ : β → LinearMap.ker N := fun b =>
    ⟨M (c b : E), LinearMap.mem_ker.2 (LinearMap.mem_ker.1 (c b).2)⟩
  have hκ : ∀ b, M ((c b - σ (ζ b) : LinearMap.ker (N ∘ₗ M)) : E) = 0 := fun b => by
    simp [hσ, ζ]
  let κ : β → LinearMap.ker M := fun b => ⟨(c b - σ (ζ b) : LinearMap.ker (N ∘ₗ M)), hκ b⟩
  let X : Matrix α β ℝ := Matrix.of fun a b => ⟪u a, κ b⟫_ℝ
  let A : Matrix β β ℝ := Matrix.of fun i j => ⟪(v i : F), M (c j : E)⟫_ℝ
  have hx : ∀ b, c b = ∑ a, X a b • incl (u a) + ∑ i, A i b • σ (v i) := by
    intro b
    have e1 : ∑ a, X a b • incl (u a) = c b - σ (ζ b) := by
      have : ∑ a, X a b • incl (u a) = incl (∑ a, ⟪u a, κ b⟫_ℝ • u a) := by
        simp only [map_sum, map_smul]
        rfl
      rw [this, u.sum_repr']
      rfl
    have e2 : ∑ i, A i b • σ (v i) = σ (ζ b) := by
      conv_rhs => rw [← v.sum_repr' (ζ b)]
      simp only [map_sum, map_smul]
      rfl
    rw [e1, e2]
    abel
  have h₁₂ : ∀ a b, B (incl (u a)) (σ (v b)) = 0 := fun a b => by
    rw [hsymm]
    exact hB _ _ (u a).2
  have h₂₁ : ∀ b a, B (σ (v b)) (incl (u a)) = 0 := fun b a => hB _ _ (u a).2
  have key := det_gram_sum_elim_of_orthogonal B (fun a => incl (u a)) (fun b => σ (v b)) c X A
    h₁₂ h₂₁ hx
  have m1 : (Matrix.of fun a a' => B (incl (u a)) (incl (u a'))) =
      formMatrixInBasis M (restrictToInnerKernel M N T) u := by
    ext a a'
    simp [formMatrixInBasis, LinearMap.BilinForm.toMatrix_apply, restrictToInnerKernel,
      QuadraticMap.associated_comp, B, incl]
  have m2 : (Matrix.of fun b b' => B (σ (v b)) (σ (v b'))) = formMatrixInBasis N (T.comp σ) v := by
    ext b b'
    simp [formMatrixInBasis, LinearMap.BilinForm.toMatrix_apply, QuadraticMap.associated_comp, B]
  rw [m1, m2] at key
  exact key
theorem exists_basis_det_identity {α β : Type} [Fintype α] [Fintype β] [DecidableEq α]
    [DecidableEq β]
    (M : E →ₗ[ℝ] F) (N : F →ₗ[ℝ] F') (T : QuadraticForm ℝ (LinearMap.ker (N ∘ₗ M)))
    (σ : LinearMap.ker N →ₗ[ℝ] LinearMap.ker (N ∘ₗ M))
    (hM : Function.Surjective M) (hN : Function.Surjective N) (hσ : ∀ ζ, M (σ ζ : E) = ζ)
    (hB : ∀ ζ (κ : LinearMap.ker (N ∘ₗ M)), M (κ : E) = 0 →
      QuadraticMap.associated T (σ ζ) κ = 0)
    (u : OrthonormalBasis α ℝ (LinearMap.ker M)) (v : OrthonormalBasis β ℝ (LinearMap.ker N)) :
    ∃ b : OrthonormalBasis (α ⊕ β) ℝ (LinearMap.ker (N ∘ₗ M)),
      LinearMap.det ((N ∘ₗ M) ∘ₗ LinearMap.adjoint (N ∘ₗ M)) *
          (formMatrixInBasis (N ∘ₗ M) T b).det =
        LinearMap.det (M ∘ₗ LinearMap.adjoint M) * LinearMap.det (N ∘ₗ LinearMap.adjoint N) *
          (formMatrixInBasis M (restrictToInnerKernel M N T) u).det *
          (formMatrixInBasis N (T.comp σ) v).det := by
  have hNM : Function.Surjective (N ∘ₗ M) := by
    rw [LinearMap.coe_comp]
    exact hN.comp hM
  have r1 := finrank_ker_add_finrank_of_surjective M hM
  have r2 := finrank_ker_add_finrank_of_surjective N hN
  have r3 := finrank_ker_add_finrank_of_surjective (N ∘ₗ M) hNM
  have cα : finrank ℝ (LinearMap.ker M) = Fintype.card α := finrank_eq_card_basis u.toBasis
  have cβ : finrank ℝ (LinearMap.ker N) = Fintype.card β := finrank_eq_card_basis v.toBasis
  let g := stdOrthonormalBasis ℝ F'
  let incl := Submodule.inclusion (LinearMap.ker_le_ker_comp M N)
  let w : α → LinearMap.ker (N ∘ₗ M) := fun a => incl (u a)
  have hw : Orthonormal ℝ w := by
    rw [orthonormal_iff_ite]
    intro i j
    exact orthonormal_iff_ite.1 u.orthonormal i j
  let Mk : LinearMap.ker (N ∘ₗ M) →ₗ[ℝ] F := M ∘ₗ (LinearMap.ker (N ∘ₗ M)).subtype
  have hrange : LinearMap.range Mk = LinearMap.ker N := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact LinearMap.mem_ker.2 (LinearMap.mem_ker.1 x.2)
    · intro hy
      exact ⟨σ ⟨y, hy⟩, hσ ⟨y, hy⟩⟩
  have cU : Fintype.card β = finrank ℝ (LinearMap.ker Mk)ᗮ := by
    have h1 := (LinearMap.ker Mk).finrank_add_finrank_orthogonal
    have h2 := LinearMap.finrank_range_add_finrank_ker Mk
    rw [hrange] at h2
    omega
  obtain ⟨c, hc, hcU⟩ := exists_orthonormal_family_in_submodule (LinearMap.ker Mk)ᗮ cU
  obtain ⟨b, hb₁, hb₂⟩ := exists_orthonormalBasis_sum_elim w c hw hc
    (fun a j => Submodule.inner_right_of_mem_orthogonal
      (show w a ∈ LinearMap.ker Mk from (u a).2) (hcU j)) (by omega)
  have cK : Fintype.card (Fin (finrank ℝ F')) = finrank ℝ (LinearMap.ker (N ∘ₗ M))ᗮ := by
    have h1 := (LinearMap.ker (N ∘ₗ M)).finrank_add_finrank_orthogonal
    simp only [Fintype.card_fin]
    omega
  obtain ⟨p, hp, hpK⟩ := exists_orthonormal_family_in_submodule (LinearMap.ker (N ∘ₗ M))ᗮ cK
  obtain ⟨e, he₁, he₂⟩ := exists_orthonormalBasis_sum_elim (fun x => (b x : E)) p
    (b.orthonormal.comp_linearIsometry (LinearMap.ker (N ∘ₗ M)).subtypeₗᵢ) hp
    (fun x j => Submodule.inner_right_of_mem_orthogonal (b x).2 (hpK j))
    (by
      have h1 := finrank_eq_card_basis b.toBasis
      simp only [Fintype.card_sum, Fintype.card_fin] at h1 ⊢
      omega)
  have cN : Fintype.card (Fin (finrank ℝ F')) = finrank ℝ (LinearMap.ker N)ᗮ := by
    have h1 := (LinearMap.ker N).finrank_add_finrank_orthogonal
    simp only [Fintype.card_fin]
    omega
  obtain ⟨q, hq, hqK⟩ := exists_orthonormal_family_in_submodule (LinearMap.ker N)ᗮ cN
  obtain ⟨f, hf₁, hf₂⟩ := exists_orthonormalBasis_sum_elim (fun x => (v x : F)) q
    (v.orthonormal.comp_linearIsometry (LinearMap.ker N).subtypeₗᵢ) hq
    (fun x j => Submodule.inner_right_of_mem_orthogonal (v x).2 (hqK j))
    (by simp only [Fintype.card_fin]; omega)
  have hJ := det_comp_adjoint_mul_block_sq M N e f g
    (fun a => by rw [he₁, hb₁]; exact (u a).2)
    (fun j => by
      rw [he₁]
      exact LinearMap.mem_ker.1 (b (Sum.inr j)).2)
    (fun j => by rw [hf₁]; exact (v j).2)
    (fun r x hx => by
      rw [hf₂, real_inner_comm]
      exact Submodule.inner_right_of_mem_orthogonal (LinearMap.mem_ker.2 hx) (hqK r))
  have hD := det_gram_inclusion_sum_elim M N T σ hσ hB u v c
  have hmat : formMatrixInBasis (N ∘ₗ M) T b = Matrix.of fun i j => QuadraticMap.associated T
      (Sum.elim (fun a => Submodule.inclusion (LinearMap.ker_le_ker_comp M N) (u a)) c i)
      (Sum.elim (fun a => Submodule.inclusion (LinearMap.ker_le_ker_comp M N) (u a)) c j) := by
    ext (i | i) (j | j) <;>
      simp [formMatrixInBasis, LinearMap.BilinForm.toMatrix_apply, hb₁, hb₂, w, incl]
  have hA : (Matrix.of fun i j => ⟪f (Sum.inl i), M (e (Sum.inl (Sum.inr j)))⟫_ℝ) =
      Matrix.of fun i j => ⟪(v i : F), M (c j : E)⟫_ℝ := by
    ext i j
    simp [hf₁, he₁, hb₂]
  rw [hA] at hJ
  refine ⟨b, ?_⟩
  rw [hmat, hD]
  linear_combination
    (formMatrixInBasis M (restrictToInnerKernel M N T) u).det *
      (formMatrixInBasis N (T.comp σ) v).det * hJ
theorem rpow_neg_half_mul_eq_of_det {a b c d d₁ d₂ t : ℝ} {n n₁ n₂ : ℕ} (ha : 0 < a)
    (hb : 0 < b)
    (hc : 0 < c) (hd : 0 < d) (hd₁ : 0 < d₁) (hd₂ : 0 < d₂) (ht : 0 < t) (hn : n = n₁ + n₂)
    (h : a * d = b * c * d₁ * d₂) :
    a ^ (-(1 / 2) : ℝ) * (t ^ ((n : ℝ) / 2) * d ^ (-(1 / 2) : ℝ)) =
      (b ^ (-(1 / 2) : ℝ) * (t ^ ((n₁ : ℝ) / 2) * d₁ ^ (-(1 / 2) : ℝ))) *
        (c ^ (-(1 / 2) : ℝ) * (t ^ ((n₂ : ℝ) / 2) * d₂ ^ (-(1 / 2) : ℝ))) := by
  have h1 : a ^ (-(1 / 2) : ℝ) * d ^ (-(1 / 2) : ℝ) =
      b ^ (-(1 / 2) : ℝ) * c ^ (-(1 / 2) : ℝ) * d₁ ^ (-(1 / 2) : ℝ) * d₂ ^ (-(1 / 2) : ℝ) := by
    rw [← Real.mul_rpow ha.le hd.le, h, Real.mul_rpow (by positivity) hd₂.le,
      Real.mul_rpow (by positivity) hd₁.le, Real.mul_rpow hb.le hc.le]
  have h2 : t ^ ((n : ℝ) / 2) = t ^ ((n₁ : ℝ) / 2) * t ^ ((n₂ : ℝ) / 2) := by
    rw [← Real.rpow_add ht, hn]
    push_cast
    ring_nf
  rw [h2]
  linear_combination t ^ ((n₁ : ℝ) / 2) * t ^ ((n₂ : ℝ) / 2) * h1
end Stages
theorem gaussianNumberOfComposite_of_kernelIntegral
    (hG : YangMills.Construction.Gaussian.KernelIntegral.GaussianIntegralOnKernel) :
    GaussianNumberOfComposite := by
  intro E F F' _ _ _ _ _ _ _ _ _ M N T hM hN hT
  obtain ⟨σ, hσ, hB⟩ := exists_orthogonal_section M N T hM hT
  have hσ0 : ∀ ζ, ζ ≠ 0 → σ ζ ≠ 0 := fun ζ hζ h0 => by
    apply hζ
    have := hσ ζ
    rw [h0] at this
    exact Subtype.ext (by simpa using this.symm)
  have hT₂ : (T.comp σ).PosDef := fun ζ hζ => hT _ (hσ0 ζ hζ)
  have hincl : ∀ x : LinearMap.ker M, x ≠ 0 →
      Submodule.inclusion (LinearMap.ker_le_ker_comp M N) x ≠ 0 := fun x hx h0 =>
    hx (Subtype.ext (congrArg (fun y : LinearMap.ker (N ∘ₗ M) => (y : E)) h0))
  have hT₁ : (restrictToInnerKernel M N T).PosDef := fun x hx => hT _ (hincl x hx)
  have hNM : Function.Surjective (N ∘ₗ M) := by
    rw [LinearMap.coe_comp]
    exact hN.comp hM
  refine ⟨T.comp σ, hT₂, ?_, ?_⟩
  · intro ζ
    refine ⟨⟨σ ζ, hσ ζ, rfl⟩, ?_⟩
    rintro t ⟨ξ, hξ, rfl⟩
    have hκ : M ((ξ - σ ζ : LinearMap.ker (N ∘ₗ M)) : E) = 0 := by
      simp [hσ, hξ]
    have hadd : T ξ = T (σ ζ) + T (ξ - σ ζ) := by
      have h2 := LinearMap.congr_fun₂ (QuadraticMap.two_nsmul_associated ℝ T) (σ ζ) (ξ - σ ζ)
      rw [LinearMap.smul_apply, LinearMap.smul_apply, hB ζ _ hκ, smul_zero,
        QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, add_sub_cancel] at h2
      linarith
    have hnn : 0 ≤ T (ξ - σ ζ) := hT.nonneg _
    show T (σ ζ) ≤ T ξ
    linarith
  · obtain ⟨b, hb⟩ := exists_basis_det_identity M N T σ hM hN hσ hB
      (stdOrthonormalBasis ℝ (LinearMap.ker M)) (stdOrthonormalBasis ℝ (LinearMap.ker N))
    obtain ⟨hJ, d, hd, hdall, -, -, hint⟩ := hG E F' (N ∘ₗ M) hNM T hT
    obtain ⟨hJ₁, d₁, hd₁, hdall₁, -, -, hint₁⟩ :=
      hG E F M hM (restrictToInnerKernel M N T) hT₁
    obtain ⟨hJ₂, d₂, hd₂, hdall₂, -, -, hint₂⟩ := hG F F' N hN (T.comp σ) hT₂
    have e : kernelGaussianIntegral (N ∘ₗ M) T = _ := hint
    have e₁ : kernelGaussianIntegral M (restrictToInnerKernel M N T) = _ := hint₁
    have e₂ : kernelGaussianIntegral N (T.comp σ) = _ := hint₂
    rw [hdall, hdall₁, hdall₂] at hb
    have hn : finrank ℝ (LinearMap.ker (N ∘ₗ M)) =
        finrank ℝ (LinearMap.ker M) + finrank ℝ (LinearMap.ker N) := by
      have := finrank_eq_card_basis b.toBasis
      simpa using this
    simp only [constrainedGaussianNumber]
    rw [e, e₁, e₂]
    exact rpow_neg_half_mul_eq_of_det hJ hJ₁ hJ₂ hd hd₁ hd₂ (by positivity) hn hb
end YangMills.Construction.ConstraintStages
end
