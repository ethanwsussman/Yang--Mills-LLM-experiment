import YangMills.Construction.Lattice.GreenOperatorsOfCubes
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.CubeCovering.GreenOperators
open YangMills.Construction.PeriodicLattice YangMills.Construction.PeriodicLattice.ScaledFun
structure DecayConstantsLE (k k' : DecayConstants) : Prop where
  base : k.base ≤ k'.base
  holder : ∀ α, k.holder α ≤ k'.holder α
  grad : ∀ ε, k.grad ε ≤ k'.grad ε
  gradHolder : ∀ α ε, k.gradHolder α ε ≤ k'.gradHolder α ε
def maxConstants (k k' : DecayConstants) : DecayConstants where
  base := max k.base k'.base
  holder α := max (k.holder α) (k'.holder α)
  grad ε := max (k.grad ε) (k'.grad ε)
  gradHolder α ε := max (k.gradHolder α ε) (k'.gradHolder α ε)
  base_pos := lt_max_of_lt_left k.base_pos
  holder_pos α h₀ h₁ := lt_max_of_lt_left (k.holder_pos α h₀ h₁)
  grad_pos ε h₀ h₁ := lt_max_of_lt_left (k.grad_pos ε h₀ h₁)
  gradHolder_pos α ε h₀ h₁ h₂ := lt_max_of_lt_left (k.gradHolder_pos α ε h₀ h₁ h₂)
theorem mul_mul_le_mul_mul {a a' e e' n : ℝ} (ha : 0 ≤ a) (h₁ : a ≤ a') (he : 0 ≤ e) (h₂ : e ≤ e')
    (hn : 0 ≤ n) : a * e * n ≤ a' * e' * n :=
  mul_le_mul_of_nonneg_right (mul_le_mul h₁ h₂ he (ha.trans h₁)) hn
theorem mul_mul_mul_le {a a' e e' m n : ℝ} (ha : 0 ≤ a) (h₁ : a ≤ a') (he : 0 ≤ e) (h₂ : e ≤ e')
    (hm : 0 ≤ m) (hn : 0 ≤ n) : a * e * m * n ≤ a' * e' * m * n :=
  mul_le_mul_of_nonneg_right (mul_mul_le_mul_mul ha h₁ he h₂ hm) hn
section Norms
variable {N : ℕ} {s : Mesh N} {ι : Type}
theorem multiField_normAt_nonneg [Fintype ι] (f : MultiField 4 s ι) (x : GridPoint 4 s) :
    0 ≤ MultiField.normAt f x :=
  Real.iSup_nonneg fun _ => abs_nonneg _
theorem multiField_maxNorm_nonneg [Fintype ι] (f : MultiField 4 s ι) : 0 ≤ MultiField.maxNorm f :=
  Real.iSup_nonneg fun _ => multiField_normAt_nonneg f _
theorem siteFun_maxNorm_nonneg (f : SiteFun 4 s) : 0 ≤ SiteFun.maxNorm f :=
  Real.iSup_nonneg fun _ => abs_nonneg _
theorem holderQuotientSup_nonneg (α : ℝ) (w : GridPoint 4 s → GridPoint 4 s → ℝ)
    (hw : ∀ x y, 0 ≤ w x y) : 0 ≤ holderQuotientSup s α w := by
  refine Real.sSup_nonneg ?_
  rintro t ⟨x, y, h₀, -, rfl⟩
  exact mul_nonneg (Real.rpow_nonneg h₀.le _) (hw x y)
theorem multiField_holderSemi_nonneg [Fintype ι] (α : ℝ) (f : MultiField 4 s ι) :
    0 ≤ MultiField.holderSemi α f :=
  holderQuotientSup_nonneg α _ fun _ _ => Real.iSup_nonneg fun _ => abs_nonneg _
theorem siteFun_holderSemi_nonneg (α : ℝ) (f : SiteFun 4 s) :
    0 ≤ SiteFun.holderSemi α f :=
  holderQuotientSup_nonneg α _ fun _ _ => abs_nonneg _
end Norms
section Monotone
variable {N : ℕ} {s : Mesh N}
theorem pointwiseDecayBounds_mono {k k' : DecayConstants} (hk : DecayConstantsLE k k')
    {O : OneForm 4 s →ₗ[ℝ] OneForm 4 s} {E E' : ℝ} (hE : 0 ≤ E) (hEE : E ≤ E') {x : GridPoint 4 s}
    {ζ : SiteFun 4 s} {J : OneForm 4 s} {J' : MultiField 4 s (Fin 4 × Fin 4)}
    {J'' : MultiField 4 s (Fin 4 × Fin 4 × Fin 4)} (h : s.PointwiseDecayBounds k O E x ζ J J' J'') :
    s.PointwiseDecayBounds k' O E' x ζ J J' J'' where
  normAt_le := h.normAt_le.trans
    (mul_mul_le_mul_mul k.base_pos.le hk.base hE hEE (multiField_maxNorm_nonneg _))
  gradNormAt_le := h.gradNormAt_le.trans
    (mul_mul_le_mul_mul k.base_pos.le hk.base hE hEE (multiField_maxNorm_nonneg _))
  laplacianNormAt_le := h.laplacianNormAt_le.trans
    (mul_mul_le_mul_mul k.base_pos.le hk.base hE hEE (multiField_maxNorm_nonneg _))
  adjNormAt_le := h.adjNormAt_le.trans
    (mul_mul_le_mul_mul k.base_pos.le hk.base hE hEE (multiField_maxNorm_nonneg _))
  holder_grad α h₀ h₁ := (h.holder_grad α h₀ h₁).trans
    (mul_mul_mul_le (k.holder_pos α h₀ h₁).le (hk.holder α) hE hEE
      (add_nonneg (siteFun_holderSemi_nonneg _ _) (siteFun_maxNorm_nonneg _))
      (multiField_maxNorm_nonneg _))
  holder_adj α h₀ h₁ := (h.holder_adj α h₀ h₁).trans
    (mul_mul_mul_le (k.holder_pos α h₀ h₁).le (hk.holder α) hE hEE
      (add_nonneg (siteFun_holderSemi_nonneg _ _) (siteFun_maxNorm_nonneg _))
      (multiField_maxNorm_nonneg _))
  gradAdjNormAt_le ε h₀ h₁ := (h.gradAdjNormAt_le ε h₀ h₁).trans
    (mul_mul_le_mul_mul (k.grad_pos ε h₀ h₁).le (hk.grad ε) hE hEE
      (add_nonneg (multiField_holderSemi_nonneg _ _) (multiField_maxNorm_nonneg _)))
  holder_gradAdj α ε h₀ h₁ h₂ := (h.holder_gradAdj α ε h₀ h₁ h₂).trans
    (mul_mul_mul_le (k.gradHolder_pos α ε h₀ h₁ h₂).le (hk.gradHolder α ε) hE hEE
      (add_nonneg (siteFun_holderSemi_nonneg _ _) (siteFun_maxNorm_nonneg _))
      (add_nonneg (multiField_holderSemi_nonneg _ _) (multiField_maxNorm_nonneg _)))
  norm_mul_le := h.norm_mul_le.trans
    (mul_mul_mul_le k.base_pos.le hk.base hE hEE (siteFun_maxNorm_nonneg _) (norm_nonneg _))
  norm_mul_grad_le := h.norm_mul_grad_le.trans
    (mul_mul_mul_le k.base_pos.le hk.base hE hEE (siteFun_maxNorm_nonneg _) (norm_nonneg _))
  norm_mul_gradGrad_le := h.norm_mul_gradGrad_le.trans
    (mul_mul_mul_le k.base_pos.le hk.base hE hEE (siteFun_maxNorm_nonneg _) (norm_nonneg _))
  norm_mul_adj_le := h.norm_mul_adj_le.trans
    (mul_mul_mul_le k.base_pos.le hk.base hE hEE (siteFun_maxNorm_nonneg _) (norm_nonneg _))
  norm_mul_gradAdj_le := h.norm_mul_gradAdj_le.trans
    (mul_mul_mul_le k.base_pos.le hk.base hE hEE (siteFun_maxNorm_nonneg _) (norm_nonneg _))
  norm_mul_gradGradAdj_le := h.norm_mul_gradGradAdj_le.trans
    (mul_mul_mul_le k.base_pos.le hk.base hE hEE (siteFun_maxNorm_nonneg _) (norm_nonneg _))
end Monotone
section Translations
variable {N : ℕ} {s : Mesh N} (v : GridPoint 4 s) {ι : Type}
end Translations
section FirstCase
variable {L j N : ℕ} (S : Scales 4 L j N) (Λ' : Set (GridPoint 4 S.coarseMesh))
end FirstCase
section SecondCase
open YangMills.Construction.DirichletLaplacian
variable {N : ℕ} {hN : 0 < N} (𝔟 : Set (Link 4 (Mesh.one hN)))
  (𝔭 : Set (DirichletLaplacian.Plaquette 4 (Mesh.one hN))) (𝔰 : Set (GridPoint 4 (Mesh.one hN)))
end SecondCase
end YangMills.Construction.CubeCovering.GreenOperators
