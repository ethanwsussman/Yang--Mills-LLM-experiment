import YangMills.Construction.Lattice.GreenOperatorsOfCubesProof
import YangMills.Construction.SeparatedSequences.ChosenConstantsOfTheConditions
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.SeparatedClasses.CubeGreenRaise
open PeriodicLattice
structure ConstantsLe (k k' : DecayConstants) : Prop where
  base_le : k.base ≤ k'.base
  holder_le : ∀ α, k.holder α ≤ k'.holder α
  grad_le : ∀ ε, k.grad ε ≤ k'.grad ε
  gradHolder_le : ∀ α ε, k.gradHolder α ε ≤ k'.gradHolder α ε
theorem mul_mul_le_of_le {a a' e n : ℝ} (h : a ≤ a') (he : 0 ≤ e) (hn : 0 ≤ n) :
    a * e * n ≤ a' * e * n :=
  mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h he) hn
theorem mul_mul_mul_le_of_le {a a' e m n : ℝ} (h : a ≤ a') (he : 0 ≤ e) (hm : 0 ≤ m)
    (hn : 0 ≤ n) : a * e * m * n ≤ a' * e * m * n :=
  mul_le_mul_of_nonneg_right (mul_mul_le_of_le h he hm) hn
section Norms
variable {N : ℕ} {s : Mesh N} {ι : Type}
theorem multiField_normAt_nonneg [Fintype ι] (f : MultiField 4 s ι) (x : GridPoint 4 s) :
    0 ≤ MultiField.normAt f x :=
  Real.iSup_nonneg fun _ => abs_nonneg _
theorem multiField_maxNorm_nonneg [Fintype ι] (f : MultiField 4 s ι) : 0 ≤ MultiField.maxNorm f :=
  Real.iSup_nonneg fun _ => multiField_normAt_nonneg f _
theorem siteFun_maxNorm_nonneg (f : SiteFun 4 s) : 0 ≤ SiteFun.maxNorm f :=
  Real.iSup_nonneg fun _ => abs_nonneg _
theorem holderQuotientSup_nonneg' (α : ℝ) (v : GridPoint 4 s → GridPoint 4 s → ℝ)
    (hv : ∀ x x', 0 ≤ v x x') : 0 ≤ holderQuotientSup s α v := by apply _root_.YangMills.Construction.CubeCovering.GreenOperators.holderQuotientSup_nonneg <;> assumption
theorem multiField_holderSemi_nonneg [Fintype ι] (α : ℝ) (f : MultiField 4 s ι) :
    0 ≤ MultiField.holderSemi α f :=
  holderQuotientSup_nonneg' α _ fun _ _ => Real.iSup_nonneg fun _ => abs_nonneg _
theorem siteFun_holderSemi_nonneg (α : ℝ) (f : SiteFun 4 s) :
    0 ≤ SiteFun.holderSemi α f :=
  holderQuotientSup_nonneg' α _ fun _ _ => abs_nonneg _
end Norms
section Monotone
variable {N : ℕ} {s : Mesh N}
theorem pointwiseDecayBounds_mono {k k' : DecayConstants} (hk : ConstantsLe k k')
    {O : OneForm 4 s →ₗ[ℝ] OneForm 4 s} {E : ℝ} (hE : 0 ≤ E) {x : GridPoint 4 s}
    {ζ : SiteFun 4 s} {J : OneForm 4 s} {J' : MultiField 4 s (Fin 4 × Fin 4)}
    {J'' : MultiField 4 s (Fin 4 × Fin 4 × Fin 4)} (h : s.PointwiseDecayBounds k O E x ζ J J' J'') :
    s.PointwiseDecayBounds k' O E x ζ J J' J'' where
  normAt_le := h.normAt_le.trans (mul_mul_le_of_le hk.base_le hE (multiField_maxNorm_nonneg _))
  gradNormAt_le := h.gradNormAt_le.trans
    (mul_mul_le_of_le hk.base_le hE (multiField_maxNorm_nonneg _))
  laplacianNormAt_le := h.laplacianNormAt_le.trans
    (mul_mul_le_of_le hk.base_le hE (multiField_maxNorm_nonneg _))
  adjNormAt_le := h.adjNormAt_le.trans
    (mul_mul_le_of_le hk.base_le hE (multiField_maxNorm_nonneg _))
  holder_grad α h₀ h₁ := (h.holder_grad α h₀ h₁).trans
    (mul_mul_mul_le_of_le (hk.holder_le α) hE
      (add_nonneg (siteFun_holderSemi_nonneg _ _) (siteFun_maxNorm_nonneg _))
      (multiField_maxNorm_nonneg _))
  holder_adj α h₀ h₁ := (h.holder_adj α h₀ h₁).trans
    (mul_mul_mul_le_of_le (hk.holder_le α) hE
      (add_nonneg (siteFun_holderSemi_nonneg _ _) (siteFun_maxNorm_nonneg _))
      (multiField_maxNorm_nonneg _))
  gradAdjNormAt_le ε h₀ h₁ := (h.gradAdjNormAt_le ε h₀ h₁).trans
    (mul_mul_le_of_le (hk.grad_le ε) hE
      (add_nonneg (multiField_holderSemi_nonneg _ _) (multiField_maxNorm_nonneg _)))
  holder_gradAdj α ε h₀ h₁ h₂ := (h.holder_gradAdj α ε h₀ h₁ h₂).trans
    (mul_mul_mul_le_of_le (hk.gradHolder_le α ε) hE
      (add_nonneg (siteFun_holderSemi_nonneg _ _) (siteFun_maxNorm_nonneg _))
      (add_nonneg (multiField_holderSemi_nonneg _ _) (multiField_maxNorm_nonneg _)))
  norm_mul_le := h.norm_mul_le.trans
    (mul_mul_mul_le_of_le hk.base_le hE (siteFun_maxNorm_nonneg _) (norm_nonneg _))
  norm_mul_grad_le := h.norm_mul_grad_le.trans
    (mul_mul_mul_le_of_le hk.base_le hE (siteFun_maxNorm_nonneg _) (norm_nonneg _))
  norm_mul_gradGrad_le := h.norm_mul_gradGrad_le.trans
    (mul_mul_mul_le_of_le hk.base_le hE (siteFun_maxNorm_nonneg _) (norm_nonneg _))
  norm_mul_adj_le := h.norm_mul_adj_le.trans
    (mul_mul_mul_le_of_le hk.base_le hE (siteFun_maxNorm_nonneg _) (norm_nonneg _))
  norm_mul_gradAdj_le := h.norm_mul_gradAdj_le.trans
    (mul_mul_mul_le_of_le hk.base_le hE (siteFun_maxNorm_nonneg _) (norm_nonneg _))
  norm_mul_gradGradAdj_le := h.norm_mul_gradGradAdj_le.trans
    (mul_mul_mul_le_of_le hk.base_le hE (siteFun_maxNorm_nonneg _) (norm_nonneg _))
end Monotone
section Combined
variable (L : ℕ)
end Combined
end YangMills.Construction.SeparatedClasses.CubeGreenRaise
end
