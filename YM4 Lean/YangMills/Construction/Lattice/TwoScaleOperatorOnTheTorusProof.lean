import YangMills.Construction.Lattice.FieldNormPropertiesProof
import YangMills.Construction.Lattice.SingleScaleOperatorBounds
import YangMills.Construction.Lattice.OperatorsOfTheRepresentationProof
import YangMills.Construction.Lattice.UnitToFineLiftClass
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
open Finset
noncomputable section
namespace YangMills.Construction.PeriodicLattice
open ScaledFun
namespace TwoScaleTorus
variable {d N : ℕ}
theorem taxicabDist_nonneg (u v : Torus d N) : 0 ≤ taxicabDist u v :=
  sum_nonneg fun _ _ => norm_nonneg _
theorem taxicabDist_comm (u v : Torus d N) : taxicabDist u v = taxicabDist v u := by apply _root_.YangMills.SharedProofs.p1021 <;> assumption
theorem taxicabDist_self (u : Torus d N) : taxicabDist u u = 0 := by
  simp [taxicabDist]
theorem taxicabDist_triangle (u v w : Torus d N) :
    taxicabDist u w ≤ taxicabDist u v + taxicabDist v w := by apply _root_.YangMills.Construction.PeriodicLattice.CenteredCubeDecay.taxicabDist_triangle <;> assumption
section Kernels
variable {s : Mesh N} {Y Y' : Type} [Fintype Y] [Fintype Y']
theorem inner_basisVec (p : Y) (f : ScaledFun d s Y) :
    inner ℝ (basisVec p : ScaledFun d s Y) f = s.h ^ d * f p := by
  classical
  rw [ScaledFun.inner_eq, sum_eq_single p]
  · simp [basisVec]
  · intro q _ hq
    simp [basisVec, hq]
  · intro h
    exact absurd (mem_univ p) h
variable [HasSitePosition d s Y] [HasSitePosition d s Y']
theorem posDist_nonneg (p : Y) (q : Y') : 0 ≤ posDist (d := d) (s := s) p q :=
  taxicabDist_nonneg _ _
theorem posDist_comm (p : Y) (q : Y') :
    posDist (d := d) (s := s) p q = posDist (d := d) (s := s) q p :=
  taxicabDist_comm _ _
theorem expDecayClass_mono {δ δ' c c' : ℝ} (hδ : δ' ≤ δ) (hc : c ≤ c') (hc' : 0 ≤ c')
    {U : ScaledFun d s Y' →ₗ[ℝ] ScaledFun d s Y} (h : U ∈ expDecayClass δ c) :
    U ∈ expDecayClass δ' c' := by
  intro p q
  refine (h p q).trans ?_
  have hr := posDist_nonneg (d := d) (s := s) p q
  calc c * Real.exp (-δ * posDist (d := d) (s := s) p q)
      ≤ c' * Real.exp (-δ * posDist (d := d) (s := s) p q) :=
        mul_le_mul_of_nonneg_right hc (Real.exp_pos _).le
    _ ≤ c' * Real.exp (-δ' * posDist (d := d) (s := s) p q) := by
        refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hc'
        nlinarith
theorem expDecayClass_add {δ c₁ c₂ : ℝ} {U₁ U₂ : ScaledFun d s Y' →ₗ[ℝ] ScaledFun d s Y}
    (h₁ : U₁ ∈ expDecayClass δ c₁) (h₂ : U₂ ∈ expDecayClass δ c₂) :
    U₁ + U₂ ∈ expDecayClass δ (c₁ + c₂) := by
  intro p q
  have e : matrixEntry (U₁ + U₂) p q = matrixEntry U₁ p q + matrixEntry U₂ p q := by
    simp [matrixEntry, inner_add_right]
  rw [e, add_mul]
  exact (abs_add_le _ _).trans (add_le_add (h₁ p q) (h₂ p q))
theorem expDecayClass_neg {δ c : ℝ} {U : ScaledFun d s Y' →ₗ[ℝ] ScaledFun d s Y}
    (h : U ∈ expDecayClass δ c) : -U ∈ expDecayClass δ c := by
  intro p q
  have e : matrixEntry (-U) p q = -matrixEntry U p q := by
    simp [matrixEntry, inner_neg_right]
  rw [e, abs_neg]
  exact h p q
theorem expDecayClass_adjoint {δ c : ℝ} {U : ScaledFun d s Y' →ₗ[ℝ] ScaledFun d s Y}
    (h : U ∈ expDecayClass δ c) : LinearMap.adjoint U ∈ expDecayClass δ c := by
  intro p q
  have e : matrixEntry (LinearMap.adjoint U) p q = matrixEntry U q p := by
    simp only [matrixEntry]
    rw [LinearMap.adjoint_inner_right, real_inner_comm]
  rw [e, posDist_comm]
  exact h q p
theorem expDecayClass_id (hs : s.h = 1) {δ : ℝ} :
    (LinearMap.id : ScaledFun d s Y →ₗ[ℝ] ScaledFun d s Y) ∈ expDecayClass δ 1 := by
  classical
  intro p q
  simp only [matrixEntry, LinearMap.id_apply, inner_basisVec, hs, one_pow, one_mul]
  by_cases h : p = q
  · subst h
    simp [basisVec, posDist, taxicabDist_self]
  · have : (basisVec q : ScaledFun d s Y) p = 0 := by simp [basisVec, h]
    rw [this, abs_zero]
    exact (Real.exp_pos _).le
end Kernels
section Norms
variable {s : Mesh N} {ι : Type} [Fintype ι]
theorem normAt_nonneg (f : MultiField d s ι) (x : GridPoint d s) : 0 ≤ MultiField.normAt f x :=
  Real.iSup_nonneg fun _ => abs_nonneg _
theorem maxNorm_nonneg (f : MultiField d s ι) : 0 ≤ MultiField.maxNorm f :=
  Real.iSup_nonneg fun x => normAt_nonneg f x
theorem siteFun_maxNorm_nonneg (f : SiteFun d s) : 0 ≤ SiteFun.maxNorm f :=
  Real.iSup_nonneg fun _ => abs_nonneg _
theorem abs_le_normAt (f : MultiField d s ι) (x : GridPoint d s) (i : ι) :
    |f (i, x)| ≤ MultiField.normAt f x :=
  le_ciSup (f := fun i => |f (i, x)|) (Set.finite_range _).bddAbove i
theorem normAt_add_le {f g : MultiField d s ι} {x : GridPoint d s} {a b : ℝ}
    (hf : MultiField.normAt f x ≤ a) (hg : MultiField.normAt g x ≤ b) :
    MultiField.normAt (f + g) x ≤ a + b := by
  have ha := (normAt_nonneg f x).trans hf
  have hb := (normAt_nonneg g x).trans hg
  refine Real.iSup_le (fun i => ?_) (add_nonneg ha hb)
  exact (abs_add_le _ _).trans
    (add_le_add ((abs_le_normAt f x i).trans hf) ((abs_le_normAt g x i).trans hg))
theorem holderQuotientSup_bddAbove (α : ℝ) (v : GridPoint d s → GridPoint d s → ℝ) :
    BddAbove {t | ∃ x x' : GridPoint d s,
      0 < taxicabDist (x : Torus d N) x' ∧ taxicabDist (x : Torus d N) x' ≤ 1 ∧
        t = taxicabDist (x : Torus d N) x' ^ (-α) * v x x'} := by apply _root_.YangMills.Construction.PeriodicLattice.FieldNormProofs.holderQuotientSup_bddAbove <;> assumption
theorem holderQuotientSup_nonneg (α : ℝ) {v : GridPoint d s → GridPoint d s → ℝ}
    (hv : ∀ x x', 0 ≤ v x x') : 0 ≤ holderQuotientSup s α v := by apply _root_.YangMills.Construction.CubeCovering.RescaledGreen.holderQuotientSup_nonneg <;> assumption
theorem holderQuotientSup_add_le (α : ℝ) {v v₁ v₂ : GridPoint d s → GridPoint d s → ℝ}
    (h₁ : ∀ x x', 0 ≤ v₁ x x') (h₂ : ∀ x x', 0 ≤ v₂ x x')
    (h : ∀ x x', v x x' ≤ v₁ x x' + v₂ x x') :
    holderQuotientSup s α v ≤ holderQuotientSup s α v₁ + holderQuotientSup s α v₂ := by
  refine Real.sSup_le ?_
    (add_nonneg (holderQuotientSup_nonneg α h₁) (holderQuotientSup_nonneg α h₂))
  rintro t ⟨x, x', h0, h1, rfl⟩
  have hr := Real.rpow_nonneg h0.le (-α)
  have e₁ := le_csSup (holderQuotientSup_bddAbove α v₁) ⟨x, x', h0, h1, rfl⟩
  have e₂ := le_csSup (holderQuotientSup_bddAbove α v₂) ⟨x, x', h0, h1, rfl⟩
  calc taxicabDist (x : Torus d N) x' ^ (-α) * v x x'
      ≤ taxicabDist (x : Torus d N) x' ^ (-α) * (v₁ x x' + v₂ x x') :=
        mul_le_mul_of_nonneg_left (h x x') hr
    _ = taxicabDist (x : Torus d N) x' ^ (-α) * v₁ x x' +
          taxicabDist (x : Torus d N) x' ^ (-α) * v₂ x x' := mul_add _ _ _
    _ ≤ _ := add_le_add e₁ e₂
theorem siteFun_holderSemi_nonneg (α : ℝ) (f : SiteFun d s) :
    0 ≤ SiteFun.holderSemi α f := by apply _root_.YangMills.Construction.CubeCovering.RescaledGreen.siteFun_holderSemi_nonneg <;> assumption
theorem iSup_abs_sub_nonneg (f : MultiField d s ι) (x x' : GridPoint d s) :
    0 ≤ ⨆ i, |f (i, x) - f (i, x')| :=
  Real.iSup_nonneg fun _ => abs_nonneg _
theorem holderSemi_nonneg (α : ℝ) (f : MultiField d s ι) : 0 ≤ MultiField.holderSemi α f := by apply _root_.YangMills.Construction.CubeCovering.RescaledGreen.multiField_holderSemi_nonneg <;> assumption
theorem holderSemi_add_le {α a b : ℝ} {f g : MultiField d s ι}
    (hf : MultiField.holderSemi α f ≤ a) (hg : MultiField.holderSemi α g ≤ b) :
    MultiField.holderSemi α (f + g) ≤ a + b := by
  refine le_trans ?_ (add_le_add hf hg)
  refine holderQuotientSup_add_le α (fun x x' => iSup_abs_sub_nonneg f x x')
    (fun x x' => iSup_abs_sub_nonneg g x x') fun x x' => ?_
  refine Real.iSup_le (fun i => ?_)
    (add_nonneg (iSup_abs_sub_nonneg f x x') (iSup_abs_sub_nonneg g x x'))
  have e : (f + g) (i, x) - (f + g) (i, x') = (f (i, x) - f (i, x')) + (g (i, x) - g (i, x')) := by
    simp only [ScaledFun.add_apply]; ring
  rw [e]
  exact (abs_add_le _ _).trans (add_le_add
    (le_ciSup (f := fun i => |f (i, x) - f (i, x')|) (Set.finite_range _).bddAbove i)
    (le_ciSup (f := fun i => |g (i, x) - g (i, x')|) (Set.finite_range _).bddAbove i))
theorem mulLeft_add (ζ : SiteFun d s) (f g : MultiField d s ι) :
    MultiField.mulLeft ζ (f + g) = MultiField.mulLeft ζ f + MultiField.mulLeft ζ g :=
  ScaledFun.ext fun q => mul_add _ _ _
theorem holderSemi_mulLeft_add_le {α a b : ℝ} {ζ : SiteFun d s} {f g : MultiField d s ι}
    (hf : MultiField.holderSemi α (MultiField.mulLeft ζ f) ≤ a)
    (hg : MultiField.holderSemi α (MultiField.mulLeft ζ g) ≤ b) :
    MultiField.holderSemi α (MultiField.mulLeft ζ (f + g)) ≤ a + b := by
  rw [mulLeft_add]
  exact holderSemi_add_le hf hg
theorem norm_mulLeft_add_le {a b : ℝ} {ζ : SiteFun d s} {f g : MultiField d s ι}
    (hf : ‖MultiField.mulLeft ζ f‖ ≤ a) (hg : ‖MultiField.mulLeft ζ g‖ ≤ b) :
    ‖MultiField.mulLeft ζ (f + g)‖ ≤ a + b := by
  rw [mulLeft_add]
  exact (norm_add_le _ _).trans (add_le_add hf hg)
end Norms
def sumConstants (c₁ c₂ : DecayConstants) : DecayConstants where
  base := c₁.base + c₂.base
  holder α := c₁.holder α + c₂.holder α
  grad ε := c₁.grad ε + c₂.grad ε
  gradHolder α ε := c₁.gradHolder α ε + c₂.gradHolder α ε
  base_pos := add_pos c₁.base_pos c₂.base_pos
  holder_pos α h0 h1 := add_pos (c₁.holder_pos α h0 h1) (c₂.holder_pos α h0 h1)
  grad_pos ε h0 h1 := add_pos (c₁.grad_pos ε h0 h1) (c₂.grad_pos ε h0 h1)
  gradHolder_pos α ε h0 h1 h2 :=
    add_pos (c₁.gradHolder_pos α ε h0 h1 h2) (c₂.gradHolder_pos α ε h0 h1 h2)
section Inequalities
variable {L j : ℕ} (S : Scales d L j N)
theorem pointwiseDecayBounds_add {c₁ c₂ : DecayConstants}
    {O₁ O₂ : OneForm d S.fineMesh →ₗ[ℝ] OneForm d S.fineMesh} {E : ℝ} {x : GridPoint d S.fineMesh}
    {ζ : SiteFun d S.fineMesh} {J : OneForm d S.fineMesh}
    {J' : MultiField d S.fineMesh (Fin d × Fin d)}
    {J'' : MultiField d S.fineMesh (Fin d × Fin d × Fin d)}
    (h₁ : S.PointwiseDecayBounds c₁ O₁ E x ζ J J' J'')
    (h₂ : S.PointwiseDecayBounds c₂ O₂ E x ζ J J' J'') :
    S.PointwiseDecayBounds (sumConstants c₁ c₂) (O₁ + O₂) E x ζ J J' J'' := by
  have g₁ (A : OneForm d S.fineMesh) : S.oneFormGrad ((O₁ + O₂) A) =
      S.oneFormGrad (O₁ A) + S.oneFormGrad (O₂ A) := by
    rw [LinearMap.add_apply, map_add]
  have g₂ (A : OneForm d S.fineMesh) : fieldLaplacian S.fineMesh (Fin d) ((O₁ + O₂) A) =
      fieldLaplacian S.fineMesh (Fin d) (O₁ A) + fieldLaplacian S.fineMesh (Fin d) (O₂ A) := by
    rw [LinearMap.add_apply, map_add]
  have g₃ (A : OneForm d S.fineMesh) : S.oneFormGradGrad ((O₁ + O₂) A) =
      S.oneFormGradGrad (O₁ A) + S.oneFormGradGrad (O₂ A) := by
    rw [LinearMap.add_apply, map_add]
  refine
    { norm_at_le := ?_, grad_norm_at_le := ?_, laplacian_norm_at_le := ?_,
      adj_norm_at_le := ?_, holder_grad_le := ?_, holder_adj_le := ?_,
      grad_adj_norm_at_le := ?_, holder_grad_adj_le := ?_, norm_mulLeft_le := ?_,
      norm_mulLeft_grad_le := ?_, norm_mulLeft_gradGrad_le := ?_, norm_mulLeft_adj_le := ?_,
      norm_mulLeft_grad_adj_le := ?_, norm_mulLeft_gradGrad_adj_le := ?_ }
  · exact (normAt_add_le h₁.norm_at_le h₂.norm_at_le).trans_eq
      (by simp only [sumConstants]; ring)
  · rw [g₁]
    exact (normAt_add_le h₁.grad_norm_at_le h₂.grad_norm_at_le).trans_eq
      (by simp only [sumConstants]; ring)
  · rw [g₂]
    exact (normAt_add_le h₁.laplacian_norm_at_le h₂.laplacian_norm_at_le).trans_eq
      (by simp only [sumConstants]; ring)
  · exact (normAt_add_le h₁.adj_norm_at_le h₂.adj_norm_at_le).trans_eq
      (by simp only [sumConstants]; ring)
  · intro α h0 h1
    rw [g₁]
    exact (holderSemi_mulLeft_add_le (h₁.holder_grad_le α h0 h1)
      (h₂.holder_grad_le α h0 h1)).trans_eq (by simp only [sumConstants]; ring)
  · intro α h0 h1
    exact (holderSemi_mulLeft_add_le (h₁.holder_adj_le α h0 h1)
      (h₂.holder_adj_le α h0 h1)).trans_eq (by simp only [sumConstants]; ring)
  · intro ε h0 h1
    rw [g₁]
    exact (normAt_add_le (h₁.grad_adj_norm_at_le ε h0 h1)
      (h₂.grad_adj_norm_at_le ε h0 h1)).trans_eq (by simp only [sumConstants]; ring)
  · intro α ε h0 h1 h2
    rw [g₁]
    exact (holderSemi_mulLeft_add_le (h₁.holder_grad_adj_le α ε h0 h1 h2)
      (h₂.holder_grad_adj_le α ε h0 h1 h2)).trans_eq (by simp only [sumConstants]; ring)
  · exact (norm_mulLeft_add_le h₁.norm_mulLeft_le h₂.norm_mulLeft_le).trans_eq
      (by simp only [sumConstants]; ring)
  · rw [g₁]
    exact (norm_mulLeft_add_le h₁.norm_mulLeft_grad_le h₂.norm_mulLeft_grad_le).trans_eq
      (by simp only [sumConstants]; ring)
  · rw [g₃]
    exact (norm_mulLeft_add_le h₁.norm_mulLeft_gradGrad_le
      h₂.norm_mulLeft_gradGrad_le).trans_eq (by simp only [sumConstants]; ring)
  · exact (norm_mulLeft_add_le h₁.norm_mulLeft_adj_le h₂.norm_mulLeft_adj_le).trans_eq
      (by simp only [sumConstants]; ring)
  · rw [g₁]
    exact (norm_mulLeft_add_le h₁.norm_mulLeft_grad_adj_le
      h₂.norm_mulLeft_grad_adj_le).trans_eq (by simp only [sumConstants]; ring)
  · exact (norm_mulLeft_add_le h₁.norm_mulLeft_gradGrad_adj_le
      h₂.norm_mulLeft_gradGrad_adj_le).trans_eq (by simp only [sumConstants]; ring)
theorem hasLocalizedDecay_add {δ : ℝ} {c₁ c₂ : DecayConstants}
    {O₁ O₂ : OneForm d S.fineMesh →ₗ[ℝ] OneForm d S.fineMesh}
    (h₁ : S.HasLocalizedDecay δ c₁ O₁)
    (h₂ : S.HasLocalizedDecay δ c₂ O₂) :
    S.HasLocalizedDecay δ (sumConstants c₁ c₂) (O₁ + O₂) :=
  ⟨h₁.1, fun u u' x hx ζ hζ J J' J'' hJ hJ' hJ'' => pointwiseDecayBounds_add S
    (h₁.2 u u' x hx ζ hζ J J' J'' hJ hJ' hJ'') (h₂.2 u u' x hx ζ hζ J J' J'' hJ hJ' hJ'')⟩
theorem mul_mul_le_mul_mul {c E E' X : ℝ} (hc : 0 ≤ c) (hE : E ≤ E') (hX : 0 ≤ X) :
    c * E * X ≤ c * E' * X :=
  mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hE hc) hX
theorem mul_mul_mul_le_mul_mul_mul {c E E' X Z : ℝ} (hc : 0 ≤ c) (hE : E ≤ E') (hX : 0 ≤ X)
    (hZ : 0 ≤ Z) : c * E * X * Z ≤ c * E' * X * Z :=
  mul_le_mul_of_nonneg_right (mul_mul_le_mul_mul hc hE hX) hZ
theorem pointwiseDecayBounds_mono {c : DecayConstants}
    {O : OneForm d S.fineMesh →ₗ[ℝ] OneForm d S.fineMesh} {E E' : ℝ} (hE : E ≤ E')
    {x : GridPoint d S.fineMesh}
    {ζ : SiteFun d S.fineMesh} {J : OneForm d S.fineMesh}
    {J' : MultiField d S.fineMesh (Fin d × Fin d)}
    {J'' : MultiField d S.fineMesh (Fin d × Fin d × Fin d)}
    (h : S.PointwiseDecayBounds c O E x ζ J J' J'') :
    S.PointwiseDecayBounds c O E' x ζ J J' J'' := by
  have hc := c.base_pos.le
  have sJ := maxNorm_nonneg J
  have sJ' := maxNorm_nonneg J'
  have sζ := siteFun_maxNorm_nonneg ζ
  have nJ := norm_nonneg J
  have nJ' := norm_nonneg J'
  have nJ'' := norm_nonneg J''
  have hz (α : ℝ) : 0 ≤ SiteFun.holderSemi α ζ + SiteFun.maxNorm ζ :=
    add_nonneg (siteFun_holderSemi_nonneg α ζ) sζ
  have hj (α : ℝ) : 0 ≤ MultiField.holderSemi α J' + MultiField.maxNorm J' :=
    add_nonneg (holderSemi_nonneg α J') sJ'
  exact
    { norm_at_le := h.norm_at_le.trans (mul_mul_le_mul_mul hc hE sJ)
      grad_norm_at_le := h.grad_norm_at_le.trans (mul_mul_le_mul_mul hc hE sJ)
      laplacian_norm_at_le := h.laplacian_norm_at_le.trans (mul_mul_le_mul_mul hc hE sJ)
      adj_norm_at_le := h.adj_norm_at_le.trans (mul_mul_le_mul_mul hc hE sJ')
      holder_grad_le := fun α h0 h1 => (h.holder_grad_le α h0 h1).trans
        (mul_mul_mul_le_mul_mul_mul (c.holder_pos α h0 h1).le hE (hz α) sJ)
      holder_adj_le := fun α h0 h1 => (h.holder_adj_le α h0 h1).trans
        (mul_mul_mul_le_mul_mul_mul (c.holder_pos α h0 h1).le hE (hz α) sJ')
      grad_adj_norm_at_le := fun ε h0 h1 => (h.grad_adj_norm_at_le ε h0 h1).trans
        (mul_mul_le_mul_mul (c.grad_pos ε h0 h1).le hE (hj ε))
      holder_grad_adj_le := fun α ε h0 h1 h2 => (h.holder_grad_adj_le α ε h0 h1 h2).trans
        (mul_mul_mul_le_mul_mul_mul (c.gradHolder_pos α ε h0 h1 h2).le hE (hz α) (hj (α + ε)))
      norm_mulLeft_le := h.norm_mulLeft_le.trans (mul_mul_mul_le_mul_mul_mul hc hE sζ nJ)
      norm_mulLeft_grad_le :=
        h.norm_mulLeft_grad_le.trans (mul_mul_mul_le_mul_mul_mul hc hE sζ nJ)
      norm_mulLeft_gradGrad_le :=
        h.norm_mulLeft_gradGrad_le.trans (mul_mul_mul_le_mul_mul_mul hc hE sζ nJ)
      norm_mulLeft_adj_le :=
        h.norm_mulLeft_adj_le.trans (mul_mul_mul_le_mul_mul_mul hc hE sζ nJ')
      norm_mulLeft_grad_adj_le :=
        h.norm_mulLeft_grad_adj_le.trans (mul_mul_mul_le_mul_mul_mul hc hE sζ nJ')
      norm_mulLeft_gradGrad_adj_le :=
        h.norm_mulLeft_gradGrad_adj_le.trans (mul_mul_mul_le_mul_mul_mul hc hE sζ nJ'') }
theorem hasLocalizedDecay_anti {δ δ' : ℝ} {c : DecayConstants}
    {O : OneForm d S.fineMesh →ₗ[ℝ] OneForm d S.fineMesh} (h0 : 0 < δ') (hδ : δ' ≤ δ)
    (h : S.HasLocalizedDecay δ c O) : S.HasLocalizedDecay δ' c O := by
  refine ⟨h0, fun u u' x hx ζ hζ J J' J'' hJ hJ' hJ'' => ?_⟩
  refine pointwiseDecayBounds_mono S ?_ (h.2 u u' x hx ζ hζ J J' J'' hJ hJ' hJ'')
  refine Real.exp_le_exp.mpr ?_
  have := taxicabDist_nonneg u u'
  nlinarith
theorem linkWeight_anti {δ δ' : ℝ} (hδ : δ' ≤ δ) (b : Link d S.unitMesh) (u : Torus d N) :
    S.linkWeight δ b u ≤ S.linkWeight δ' b u := by
  refine Real.exp_le_exp.mpr ?_
  have := taxicabDist_nonneg u (Link.source b : Torus d N)
  nlinarith
theorem liftedFormBounds_mono {κ κ' : BoundFamily} {E E' : ℝ} {x : GridPoint d S.fineMesh}
    {ζ : SiteFun d S.fineMesh} {g : OneForm d S.fineMesh} (hE0 : 0 ≤ E) (hE : E ≤ E')
    (hk : κ.main ≤ κ'.main) (hk' : 0 ≤ κ'.main)
    (hh : ∀ α, 0 ≤ α → α < 1 → κ.holder α ≤ κ'.holder α)
    (hh' : ∀ α, 0 ≤ α → α < 1 → 0 ≤ κ'.holder α)
    (h : S.LiftedFormBounds κ E x ζ g) : S.LiftedFormBounds κ' E' x ζ g := by
  have hm : κ.main * E ≤ κ'.main * E' := mul_le_mul hk hE hE0 hk'
  have sζ := siteFun_maxNorm_nonneg ζ
  exact
    { norm_at_le := h.norm_at_le.trans hm
      grad_norm_at_le := h.grad_norm_at_le.trans hm
      laplacian_norm_at_le := h.laplacian_norm_at_le.trans hm
      holder_grad_le := fun α h0 h1 => (h.holder_grad_le α h0 h1).trans
        (mul_le_mul_of_nonneg_right (mul_le_mul (hh α h0 h1) hE hE0 (hh' α h0 h1))
          (add_nonneg (siteFun_holderSemi_nonneg α ζ) sζ))
      norm_mulLeft_gradGrad_le :=
        h.norm_mulLeft_gradGrad_le.trans (mul_le_mul_of_nonneg_right hm sζ) }
theorem liftClass_mono {δ δ' : ℝ} {κ κ' : BoundFamily} (hδ : δ' ≤ δ)
    (hk : κ.main ≤ κ'.main) (hk' : 0 ≤ κ'.main)
    (hh : ∀ α, 0 ≤ α → α < 1 → κ.holder α ≤ κ'.holder α)
    (hh' : ∀ α, 0 ≤ α → α < 1 → 0 ≤ κ'.holder α)
    {Y : OneForm d S.unitMesh →ₗ[ℝ] OneForm d S.fineMesh} (h : Y ∈ S.liftClass δ κ) :
    Y ∈ S.liftClass δ' κ' := fun b u x hx ζ hζ =>
  liftedFormBounds_mono S (Real.exp_pos _).le (linkWeight_anti S hδ b u) hk hk' hh hh'
    (h b u x hx ζ hζ)
end Inequalities
section Inverses
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
end Inverses
section UnitLattice
variable {L j : ℕ} (S : Scales d L j N)
theorem mem_coarseCell {y' : GridPoint d S.coarseMesh} {y : GridPoint d S.unitMesh} :
    y ∈ S.coarseCell y' ↔ (y : Torus d N) ∈ halfOpenCube (y' : Torus d N) L := by
  simp [Scales.coarseCell, sitesInCube]
end UnitLattice
section Families
variable {d L : ℕ}
variable (d L) in
abbrev UnitOpFamily : Type :=
  ∀ (j N : ℕ) (S : Scales d L j N), Set (GridPoint d S.coarseMesh) →
    (OneForm d S.unitMesh →ₗ[ℝ] OneForm d S.unitMesh)
variable (d L) in
abbrev LiftOpFamily : Type :=
  ∀ (j N : ℕ) (S : Scales d L j N), Set (GridPoint d S.coarseMesh) →
    (OneForm d S.unitMesh →ₗ[ℝ] OneForm d S.fineMesh)
variable (d L) in
abbrev FineOpFamily : Type :=
  ∀ (j N : ℕ) (S : Scales d L j N), Set (GridPoint d S.coarseMesh) →
    (OneForm d S.fineMesh →ₗ[ℝ] OneForm d S.fineMesh)
def UniformDecay (T : UnitOpFamily d L) : Prop :=
  ∃ δ c : ℝ, 0 < δ ∧ 0 < c ∧ ∀ (j N : ℕ) (S : Scales d L j N)
    (Λ' : Set (GridPoint d S.coarseMesh)),
    T j N S Λ' ∈ (expDecayClass δ c : Set (OneForm d S.unitMesh →ₗ[ℝ] OneForm d S.unitMesh))
theorem UniformDecay.congr {T T' : UnitOpFamily d L}
    (h : ∀ (j N : ℕ) (S : Scales d L j N) (Λ' : Set (GridPoint d S.coarseMesh)),
      T j N S Λ' = T' j N S Λ') (hT : UniformDecay T) : UniformDecay T' := by
  obtain ⟨δ, c, a, b, e⟩ := hT
  exact ⟨δ, c, a, b, fun j N S Λ' => h j N S Λ' ▸ e j N S Λ'⟩
theorem UniformDecay.add {T₁ T₂ : UnitOpFamily d L} (h₁ : UniformDecay T₁)
    (h₂ : UniformDecay T₂) : UniformDecay fun j N S Λ' => T₁ j N S Λ' + T₂ j N S Λ' := by
  obtain ⟨δ₁, c₁, a₁, b₁, e₁⟩ := h₁
  obtain ⟨δ₂, c₂, a₂, b₂, e₂⟩ := h₂
  exact ⟨min δ₁ δ₂, c₁ + c₂, lt_min a₁ a₂, add_pos b₁ b₂, fun j N S Λ' => expDecayClass_add
    (expDecayClass_mono (min_le_left _ _) le_rfl b₁.le (e₁ j N S Λ'))
    (expDecayClass_mono (min_le_right _ _) le_rfl b₂.le (e₂ j N S Λ'))⟩
theorem UniformDecay.neg {T : UnitOpFamily d L} (h : UniformDecay T) :
    UniformDecay fun j N S Λ' => -T j N S Λ' := by
  obtain ⟨δ, c, a, b, e⟩ := h
  exact ⟨δ, c, a, b, fun j N S Λ' => expDecayClass_neg (e j N S Λ')⟩
theorem UniformDecay.adjoint {T : UnitOpFamily d L} (h : UniformDecay T) :
    UniformDecay fun j N S Λ' => LinearMap.adjoint (T j N S Λ') := by
  obtain ⟨δ, c, a, b, e⟩ := h
  exact ⟨δ, c, a, b, fun j N S Λ' => expDecayClass_adjoint (e j N S Λ')⟩
theorem UniformDecay.id : UniformDecay (d := d) (L := L) fun j N S Λ' => LinearMap.id :=
  ⟨1, 1, one_pos, one_pos, fun j N S Λ' => expDecayClass_id rfl⟩
theorem expDecayCompBound_of (hCT : CombesThomasEstimateHolds) {j N : ℕ}
    (S : Scales d L j N) {δ c₁ c₂ : ℝ} (hδ : 0 < δ) (h₁ : 0 < c₁) (h₂ : 0 < c₂) :
    S.ExpDecayCompBound δ c₁ c₂ :=
  (hCT.1 d L j N S δ c₁ c₂ hδ h₁ h₂).2
theorem UniformDecay.comp (hCT : CombesThomasEstimateHolds) {T₁ T₂ : UnitOpFamily d L}
    (h₁ : UniformDecay T₁) (h₂ : UniformDecay T₂) :
    UniformDecay fun j N S Λ' => T₁ j N S Λ' ∘ₗ T₂ j N S Λ' := by
  obtain ⟨δ₁, c₁, a₁, b₁, e₁⟩ := h₁
  obtain ⟨δ₂, c₂, a₂, b₂, e₂⟩ := h₂
  have hδ : 0 < min δ₁ δ₂ := lt_min a₁ a₂
  refine ⟨min δ₁ δ₂ / 2, |latticeExpSum d (min δ₁ δ₂ / 2) * c₁ * c₂| + 1, by positivity,
    by positivity, fun j N S Λ' => ?_⟩
  have hp := expDecayCompBound_of hCT S hδ b₁ b₂
  exact expDecayClass_mono le_rfl ((le_abs_self _).trans (by linarith)) (by positivity)
    (hp.2.2.2 (T₁ j N S Λ') (T₂ j N S Λ')
      (expDecayClass_mono (min_le_left _ _) le_rfl b₁.le (e₁ j N S Λ'))
      (expDecayClass_mono (min_le_right _ _) le_rfl b₂.le (e₂ j N S Λ')))
def UniformLiftClass (c₀ : DecayConstants) (Y : LiftOpFamily d L) : Prop :=
  ∃ δ M : ℝ, 0 < δ ∧ 0 < M ∧ ∀ (j N : ℕ) (S : Scales d L j N)
    (Λ' : Set (GridPoint d S.coarseMesh)),
    Y j N S Λ' ∈ S.liftClass δ (c₀.toBoundFamily.smul M)
theorem liftClass_smul_mono {j N : ℕ} (S : Scales d L j N) {c₀ : DecayConstants}
    {δ δ' M M' : ℝ} (hδ : δ' ≤ δ) (hM : M ≤ M') (hM' : 0 ≤ M')
    {Y : OneForm d S.unitMesh →ₗ[ℝ] OneForm d S.fineMesh}
    (h : Y ∈ S.liftClass δ (c₀.toBoundFamily.smul M)) :
    Y ∈ S.liftClass δ' (c₀.toBoundFamily.smul M') :=
  liftClass_mono S hδ (mul_le_mul_of_nonneg_right hM c₀.base_pos.le)
    (mul_nonneg hM' c₀.base_pos.le)
    (fun α h0 h1 => mul_le_mul_of_nonneg_right hM (c₀.holder_pos α h0 h1).le)
    (fun α h0 h1 => mul_nonneg hM' (c₀.holder_pos α h0 h1).le) h
theorem smul_smul_eq (κ : BoundFamily) (M t : ℝ) :
    (κ.smul M).smul t = κ.smul (t * M) := by
  simp only [BoundFamily.smul, mul_assoc]
theorem UniformLiftClass.comp (hcl : LiftClassPropertiesHold)
    {c₀ : DecayConstants} {Y : LiftOpFamily d L} {U : UnitOpFamily d L}
    (hY : UniformLiftClass c₀ Y) (hU : UniformDecay U) :
    UniformLiftClass c₀ fun j N S Λ' => Y j N S Λ' ∘ₗ U j N S Λ' := by
  obtain ⟨δ₁, M, a₁, b₁, e₁⟩ := hY
  obtain ⟨δ₂, c, a₂, b₂, e₂⟩ := hU
  have hδ : 0 < min δ₁ δ₂ := lt_min a₁ a₂
  refine ⟨min δ₁ δ₂ / 2, |latticeExpSum d (min δ₁ δ₂ / 2) * c * M| + 1, by positivity,
    by positivity, fun j N S Λ' => ?_⟩
  have hp := ((hcl d (min δ₁ δ₂) hδ).1 L j N S) (c₀.toBoundFamily.smul M) c (Y j N S Λ')
    (U j N S Λ') b₂ (liftClass_smul_mono S (min_le_left _ _) le_rfl b₁.le (e₁ j N S Λ'))
    (expDecayClass_mono (min_le_right _ _) le_rfl b₂.le (e₂ j N S Λ'))
  rw [smul_smul_eq] at hp
  exact liftClass_smul_mono S le_rfl ((le_abs_self _).trans (by linarith)) (by positivity) hp
theorem UniformLiftClass.products (hcl : LiftClassPropertiesHold)
    {c₀ : DecayConstants} {Y Z : LiftOpFamily d L}
    (hY : UniformLiftClass c₀ Y) (hZ : UniformLiftClass c₀ Z) :
    (UniformDecay fun j N S Λ' => LinearMap.adjoint (Z j N S Λ') ∘ₗ
      fieldLaplacian S.fineMesh (Fin d) ∘ₗ Y j N S Λ') ∧
    (UniformDecay fun j N S Λ' =>
      LinearMap.adjoint (LinearMap.adjoint (discreteGrad S.fineMesh) ∘ₗ Z j N S Λ') ∘ₗ
        (LinearMap.adjoint (discreteGrad S.fineMesh) ∘ₗ Y j N S Λ')) ∧
    (UniformDecay fun j N S Λ' => S.fineFormAverage ∘ₗ Y j N S Λ') := by
  obtain ⟨δ₁, M₁, a₁, b₁, e₁⟩ := hY
  obtain ⟨δ₂, M₂, a₂, b₂, e₂⟩ := hZ
  have hδ : 0 < min δ₁ δ₂ := lt_min a₁ a₂
  have hM : 0 < max M₁ M₂ := lt_max_of_lt_left b₁
  have hC := (hcl d (min δ₁ δ₂) hδ).2.1
  set C := liftProductsConstant d (min δ₁ δ₂) with hCdef
  have hk : 0 < (c₀.toBoundFamily.smul (max M₁ M₂)).main := mul_pos hM c₀.base_pos
  have key : ∀ (j N : ℕ) (S : Scales d L j N) (Λ' : Set (GridPoint d S.coarseMesh)), _ :=
    fun j N S Λ' => hC.2 L j N S (c₀.toBoundFamily.smul (max M₁ M₂)) (Y j N S Λ')
      (Z j N S Λ')
      (liftClass_smul_mono S (min_le_left _ _) (le_max_left _ _) hM.le (e₁ j N S Λ'))
      (liftClass_smul_mono S (min_le_right _ _) (le_max_right _ _) hM.le (e₂ j N S Λ'))
  have hCk := mul_pos hC.1 (pow_pos hk 2)
  have hCk' := mul_pos hC.1 hk
  exact ⟨⟨_, _, half_pos hδ, hCk, fun j N S Λ' => (key j N S Λ').2.1⟩,
    ⟨_, _, half_pos hδ, hCk, fun j N S Λ' => (key j N S Λ').2.2.1⟩,
    ⟨_, _, hδ, hCk', fun j N S Λ' => (key j N S Λ').2.2.2⟩⟩
def UniformLocalizedDecay (T : FineOpFamily d L) : Prop :=
  ∃ (δ : ℝ) (c : DecayConstants), 0 < δ ∧
    ∀ (j N : ℕ) (S : Scales d L j N) (Λ' : Set (GridPoint d S.coarseMesh)),
      S.HasLocalizedDecay δ c (T j N S Λ')
theorem UniformLocalizedDecay.add {T₁ T₂ : FineOpFamily d L} (h₁ : UniformLocalizedDecay T₁)
    (h₂ : UniformLocalizedDecay T₂) :
    UniformLocalizedDecay fun j N S Λ' => T₁ j N S Λ' + T₂ j N S Λ' := by
  obtain ⟨δ₁, c₁, a₁, e₁⟩ := h₁
  obtain ⟨δ₂, c₂, a₂, e₂⟩ := h₂
  have hδ : 0 < min δ₁ δ₂ := lt_min a₁ a₂
  exact ⟨min δ₁ δ₂, sumConstants c₁ c₂, hδ, fun j N S Λ' => hasLocalizedDecay_add S
    (hasLocalizedDecay_anti S hδ (min_le_left _ _) (e₁ j N S Λ'))
    (hasLocalizedDecay_anti S hδ (min_le_right _ _) (e₂ j N S Λ'))⟩
def productDecayConstants (C : ℝ) (hC : 0 < C) (κ : BoundFamily) (hk : 0 < κ.main)
    (hh : ∀ α, 0 ≤ α → α < 1 → 0 < κ.holder α) : DecayConstants where
  base := C * κ.main ^ 2
  holder α := C * κ.main * (κ.main + κ.holder α)
  grad _ := C * κ.main ^ 2
  gradHolder α _ := C * κ.main * (κ.main + κ.holder α)
  base_pos := by positivity
  holder_pos α h0 h1 := by
    have := hh α h0 h1
    positivity
  grad_pos _ _ _ := by positivity
  gradHolder_pos α ε h0 h1 h2 := by
    have := hh α h0 (by linarith)
    positivity
theorem UniformLiftClass.localizedDecay (hcl : LiftClassPropertiesHold)
    {c₀ : DecayConstants} {Y Z : LiftOpFamily d L}
    (hY : UniformLiftClass c₀ Y) (hZ : UniformLiftClass c₀ Z) :
    UniformLocalizedDecay fun j N S Λ' => Y j N S Λ' ∘ₗ LinearMap.adjoint (Z j N S Λ') := by
  obtain ⟨δ₁, M₁, a₁, b₁, e₁⟩ := hY
  obtain ⟨δ₂, M₂, a₂, b₂, e₂⟩ := hZ
  have hδ : 0 < min δ₁ δ₂ := lt_min a₁ a₂
  have hM : 0 < max M₁ M₂ := lt_max_of_lt_left b₁
  have hC := (hcl d (min δ₁ δ₂) hδ).2.2.2
  have hk : 0 < (c₀.toBoundFamily.smul (max M₁ M₂)).main := mul_pos hM c₀.base_pos
  have hh : ∀ α, 0 ≤ α → α < 1 → 0 < (c₀.toBoundFamily.smul (max M₁ M₂)).holder α :=
    fun α h0 h1 => mul_pos hM (c₀.holder_pos α h0 h1)
  refine ⟨min δ₁ δ₂ / 2, productDecayConstants _ hC.1 _ hk hh, half_pos hδ,
    fun j N S Λ' => ?_⟩
  exact hC.2 L j N S _ (Y j N S Λ') (Z j N S Λ')
    (liftClass_smul_mono S (min_le_left _ _) (le_max_left _ _) hM.le (e₁ j N S Λ'))
    (liftClass_smul_mono S (min_le_right _ _) (le_max_right _ _) hM.le (e₂ j N S Λ'))
    _ rfl (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ _ _ => rfl)
end Families
section Steps
variable {d L : ℕ}
end Steps
section Assembly
variable {d L : ℕ}
theorem twoScaleOpInv_eq_ringInverse {j N : ℕ} (S : Scales d L j N)
    (Λ' : Set (GridPoint d S.coarseMesh))
    (h : IsUnit (S.twoScaleOp Λ' 1 : Module.End ℝ (OneForm d S.fineMesh))) :
    S.twoScaleOpInv Λ' 1 h =
      Ring.inverse (S.twoScaleOp Λ' 1 : Module.End ℝ (OneForm d S.fineMesh)) := by
  rw [Scales.twoScaleOpInv]
  conv_rhs => rw [← h.unit_spec]
  exact (Ring.inverse_unit h.unit).symm
theorem twoScaleOpInv_pos {j N : ℕ} (S : Scales d L j N) (Λ' : Set (GridPoint d S.coarseMesh))
    (hpos : ∀ A : OneForm d S.fineMesh, A ≠ 0 → 0 < inner ℝ A (S.twoScaleOp Λ' 1 A))
    (h : IsUnit (S.twoScaleOp Λ' 1 : Module.End ℝ (OneForm d S.fineMesh)))
    (A : OneForm d S.fineMesh)
    (hA : A ≠ 0) : 0 < inner ℝ A (S.twoScaleOpInv Λ' 1 h A) := by
  rw [twoScaleOpInv_eq_ringInverse]
  set G : Module.End ℝ (OneForm d S.fineMesh) :=
    Ring.inverse (S.twoScaleOp Λ' 1 : Module.End ℝ (OneForm d S.fineMesh)) with hG
  have hr : S.twoScaleOp Λ' 1 (G A) = A :=
    LinearMap.congr_fun
      (Ring.mul_inverse_cancel (S.twoScaleOp Λ' 1 : Module.End ℝ (OneForm d S.fineMesh)) h) A
  have hne : G A ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hr
    exact hA hr.symm
  have := hpos (G A) hne
  rw [hr, real_inner_comm] at this
  exact this
end Assembly
end TwoScaleTorus
end YangMills.Construction.PeriodicLattice
