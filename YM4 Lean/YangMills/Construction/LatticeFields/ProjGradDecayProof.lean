import YangMills.Construction.LatticeFields.DirichletBlockOps
import YangMills.Construction.LatticeFields.WeightConjRules
import YangMills.Construction.LatticeFields.WeightConjMassiveLaplacianFormBoundProof
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YangMills.Construction.LatticeFields.ProjGradDecayProof
theorem finite_torusSites {d : ℕ} (N : ℕ) [NeZero N] (ℓ : Fin d → ℕ) (hℓ : ∀ μ, 1 ≤ ℓ μ) :
    Finite (LatticeSite N (LatticeShape.torus ℓ hℓ)) := by apply _root_.YangMills.Construction.LatticeFields.WeightConjProjComplProof.finite_torusSites <;> assumption
section InnerProduct
variable {d M : ℕ} {κ : LatticeShape d} {I : Type} [Fintype (LatticeSite M κ)] [Fintype I]
def toEuclidean (F : LatticeField M κ I) : EuclideanSpace ℝ (LatticeSite M κ × I) :=
  WithLp.toLp 2 fun p => Real.sqrt (latticeSpacing M ^ d) * F p.1 p.2
theorem latticeSpacing_pow_nonneg : 0 ≤ latticeSpacing M ^ d := by apply _root_.YangMills.Construction.LatticeFields.WeightConjGreen.latticeSpacing_pow_nonneg_aux <;> assumption
theorem inner_toEuclidean (F G : LatticeField M κ I) :
    inner ℝ (toEuclidean F) (toEuclidean G) = fieldInner F G := by
  have hw : Real.sqrt (latticeSpacing M ^ d) * Real.sqrt (latticeSpacing M ^ d) =
      latticeSpacing M ^ d :=
    Real.mul_self_sqrt latticeSpacing_pow_nonneg
  rw [fieldInner, tsum_fintype, PiLp.inner_apply]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp only [toEuclidean, RCLike.inner_apply, conj_trivial]
  linear_combination (F p.1 p.2 * G p.1 p.2) * hw
theorem fieldNorm_eq_norm (F : LatticeField M κ I) : fieldNorm F = ‖toEuclidean F‖ := by
  rw [fieldNorm, ← inner_toEuclidean, real_inner_self_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]
theorem toEuclidean_add (F G : LatticeField M κ I) :
    toEuclidean (F + G) = toEuclidean F + toEuclidean G := by
  ext p
  simp [toEuclidean, mul_add]
theorem toEuclidean_sub (F G : LatticeField M κ I) :
    toEuclidean (F - G) = toEuclidean F - toEuclidean G := by
  ext p
  simp [toEuclidean, mul_sub]
theorem fieldInner_add_right (F G G' : LatticeField M κ I) :
    fieldInner F (G + G') = fieldInner F G + fieldInner F G' := by
  simp only [← inner_toEuclidean, toEuclidean_add, inner_add_right]
theorem fieldInner_sub_right (F G G' : LatticeField M κ I) :
    fieldInner F (G - G') = fieldInner F G - fieldInner F G' := by
  simp only [← inner_toEuclidean, toEuclidean_sub, inner_sub_right]
theorem fieldInner_sub_left (F F' G : LatticeField M κ I) :
    fieldInner (F - F') G = fieldInner F G - fieldInner F' G := by apply _root_.YangMills.Construction.LatticeFields.WeightConjGreen.fieldInner_sub_left_aux <;> assumption
theorem fieldInner_comm (F G : LatticeField M κ I) : fieldInner F G = fieldInner G F := by apply _root_.YangMills.Construction.LatticeFields.WeightConjGreen.fieldInner_comm_aux <;> assumption
theorem abs_fieldInner_le (F G : LatticeField M κ I) :
    |fieldInner F G| ≤ fieldNorm F * fieldNorm G := by apply _root_.YangMills.Construction.LatticeFields.WeightConjGreen.abs_fieldInner_le_aux <;> assumption
theorem fieldInner_le (F G : LatticeField M κ I) : fieldInner F G ≤ fieldNorm F * fieldNorm G :=
  (le_abs_self _).trans (abs_fieldInner_le F G)
theorem fieldNorm_nonneg (F : LatticeField M κ I) : 0 ≤ fieldNorm F := Real.sqrt_nonneg _
theorem fieldInner_self (F : LatticeField M κ I) : fieldInner F F = fieldNorm F ^ 2 := by apply _root_.YangMills.Construction.LatticeFields.WeightConjGreen.fieldInner_self_aux <;> assumption
theorem fieldNorm_add_le (F G : LatticeField M κ I) :
    fieldNorm (F + G) ≤ fieldNorm F + fieldNorm G := by apply _root_.YangMills.Construction.LatticeFields.WeightConjMassiveLaplacianFormBoundProof.fieldNorm_add_le <;> assumption
theorem fieldNorm_le_add_sub (F G : LatticeField M κ I) :
    fieldNorm F ≤ fieldNorm G + fieldNorm (F - G) := by apply _root_.YangMills.Construction.LatticeFields.WeightConjMassiveLaplacianFormBoundProof.fieldNorm_le_add_sub <;> assumption
theorem fieldNorm_le_of_sq_le (F : LatticeField M κ I) {C : ℝ} (hC : 0 ≤ C)
    (h : fieldNorm F ^ 2 ≤ C * fieldNorm F) : fieldNorm F ≤ C := by apply _root_.YangMills.Construction.LatticeFields.WeightConjMassiveLaplacianFormBoundProof.fieldNorm_le_of_sq_le <;> assumption
end InnerProduct
section WeightConjugation
variable {d N : ℕ} [NeZero N] {κ : LatticeShape d}
theorem fieldInner_weightMul (w : LatticeSite N κ → ℝ) (s : LatticeScale) {I : Type}
    (F G : LatticeField (s.invSpacing N) κ I) :
    fieldInner (weightMul w s F) G = fieldInner F (weightMul w s G) := by
  cases s <;> refine tsum_congr fun p => ?_ <;> simp only [weightMul, mulBase] <;> ring
end WeightConjugation
section TorusOperators
variable {d N : ℕ} {κ : LatticeShape d}
theorem tensorGrad_eq_latticeGrad (f : ScalarField N κ) :
    (tensorGrad f : LatticeOneForm N κ) = latticeGrad f := by
  funext x i
  change forwardDiff (i 0) f x (Fin.tail i) = forwardDiff (i 0) f x scalarIndex
  rw [Subsingleton.elim (Fin.tail i) scalarIndex]
theorem tensorLaplacian_eq_div_grad (f : ScalarField N κ) :
    tensorLaplacian f = latticeDiv (latticeGrad f) := by
  funext x i
  have hc : ∀ μ : Fin d, (Fin.cons μ i : Fin (0 + 1) → Fin d) = directionIndex μ := by
    intro μ
    funext j
    have hj : j = 0 := Subsingleton.elim (α := Fin 1) j 0
    rw [hj]
    rfl
  change ∑ μ, backwardDiff μ (tensorGrad f) x (Fin.cons μ i) =
    ∑ μ, backwardDiff μ (latticeGrad f) x (directionIndex μ)
  rw [tensorGrad_eq_latticeGrad]
  exact Finset.sum_congr rfl fun μ _ => by rw [hc]
variable [NeZero N] [Fintype (LatticeSite N κ)] [Fintype (LatticeSite 1 κ)]
theorem abs_fieldInner_sub_le {M : ℕ} {I : Type} {κ' : LatticeShape d}
    [Fintype (LatticeSite M κ')] [Fintype I]
    (A A₀ B B₀ : LatticeField M κ' I) {ε₁ ε₂ : ℝ} (h₁ : fieldNorm (A - A₀) ≤ ε₁)
    (h₂ : fieldNorm (B - B₀) ≤ ε₂) :
    |fieldInner A B - fieldInner A₀ B₀| ≤
      ε₁ * fieldNorm B₀ + fieldNorm A₀ * ε₂ + ε₁ * ε₂ := by
  have hid : fieldInner A B - fieldInner A₀ B₀ = fieldInner (A - A₀) B₀ +
      fieldInner A₀ (B - B₀) + fieldInner (A - A₀) (B - B₀) := by
    simp only [fieldInner_sub_left, fieldInner_sub_right]
    ring
  have e₁ : 0 ≤ ε₁ := (fieldNorm_nonneg _).trans h₁
  rw [hid]
  refine (abs_add_three _ _ _).trans (add_le_add (add_le_add ?_ ?_) ?_)
  · exact (abs_fieldInner_le _ _).trans (mul_le_mul_of_nonneg_right h₁ (fieldNorm_nonneg _))
  · exact (abs_fieldInner_le _ _).trans (mul_le_mul_of_nonneg_left h₂ (fieldNorm_nonneg _))
  · exact (abs_fieldInner_le _ _).trans (mul_le_mul h₁ h₂ (fieldNorm_nonneg _) e₁)
structure TorusOperatorData (κ : LatticeShape d) (γ : ℝ)
    (P : ScalarField N κ → ScalarField N κ) : Prop where
  grad_adj : ∀ (f : ScalarField N κ) (A : LatticeOneForm N κ),
    fieldInner (latticeGrad f) A = fieldInner f (latticeDiv A)
  avg_adj : ∀ (f : ScalarField N κ) (ω : ScalarField 1 κ),
    fieldInner (siteBlockAvg f) ω = fieldInner f (siteBlockAvgAdj ω)
  avg_norm_le : ∀ f : ScalarField N κ, fieldNorm (siteBlockAvg f) ≤ fieldNorm f
  avgAdj_norm_le : ∀ ω : ScalarField 1 κ,
    fieldNorm (siteBlockAvgAdj ω : ScalarField N κ) ≤ fieldNorm ω
  coercive : ∀ f : ScalarField N κ,
    (d : ℝ)⁻¹ * (fieldNorm (latticeGrad f) ^ 2 + fieldNorm f ^ 2) ≤
      fieldInner f (massiveBlockLaplacian f)
  lap_green : ∀ g : ScalarField N κ,
    massiveBlockLaplacian (dirichletBlockGreen Set.univ g) = g
  green_lap : ∀ g : ScalarField N κ,
    dirichletBlockGreen Set.univ (massiveBlockLaplacian g) = g
  green_sq_le : ∀ g : ScalarField N κ,
    fieldNorm (latticeGrad (dirichletBlockGreen Set.univ g)) ^ 2 +
      fieldNorm (dirichletBlockGreen Set.univ g) ^ 2 ≤ (d : ℝ) ^ 2 * fieldNorm g ^ 2
  moment_coercive : ∀ ω : ScalarField 1 κ,
    γ * fieldNorm ω ^ 2 ≤ fieldInner ω (blockGreenMoment (Set.univ : Set (LatticeSite N κ)) ω)
  moment_momentInv : ∀ ω : ScalarField 1 κ,
    blockGreenMoment (Set.univ : Set (LatticeSite N κ))
      (blockGreenMomentInv (Set.univ : Set (LatticeSite N κ)) Set.univ ω) = ω
  proj_eq : ∀ f : ScalarField N κ,
    P f = dirichletProjCompl Set.univ Set.univ f
variable {γ ε : ℝ} {P : ScalarField N κ → ScalarField N κ} {θ : LatticeSite N κ → ℝ}
theorem fieldInner_massiveBlockLaplacian (H : TorusOperatorData κ γ P) (g f : ScalarField N κ) :
    fieldInner g (massiveBlockLaplacian f) =
      fieldInner (latticeGrad g) (latticeGrad f) + fieldInner (siteBlockAvg g) (siteBlockAvg f) := by
  rw [massiveBlockLaplacian, fieldInner_add_right, tensorLaplacian_eq_div_grad, ← H.grad_adj,
    ← H.avg_adj]
theorem massiveBlockLaplacian_symm (H : TorusOperatorData κ γ P) (g f : ScalarField N κ) :
    fieldInner g (massiveBlockLaplacian f) = fieldInner (massiveBlockLaplacian g) f := by
  rw [fieldInner_comm (massiveBlockLaplacian g) f, fieldInner_massiveBlockLaplacian H,
    fieldInner_massiveBlockLaplacian H, fieldInner_comm (latticeGrad g),
    fieldInner_comm (siteBlockAvg g)]
theorem green_symm (H : TorusOperatorData κ γ P) (k g : ScalarField N κ) :
    fieldInner (dirichletBlockGreen Set.univ k) g =
      fieldInner k (dirichletBlockGreen Set.univ g) := by
  calc fieldInner (dirichletBlockGreen Set.univ k) g
      = fieldInner (dirichletBlockGreen Set.univ k)
          (massiveBlockLaplacian (dirichletBlockGreen Set.univ g)) := by
        rw [H.lap_green]
    _ = fieldInner (massiveBlockLaplacian (dirichletBlockGreen Set.univ k))
          (dirichletBlockGreen Set.univ g) :=
        massiveBlockLaplacian_symm H _ _
    _ = fieldInner k (dirichletBlockGreen Set.univ g) := by rw [H.lap_green]
end TorusOperators
section MomentConjugation
variable {d N : ℕ} {κ : LatticeShape d} [NeZero N] [Fintype (LatticeSite N κ)]
  [Fintype (LatticeSite 1 κ)]
variable {γ ε : ℝ} {P : ScalarField N κ → ScalarField N κ} {θ : LatticeSite N κ → ℝ}
end MomentConjugation
section Decay
variable {d N : ℕ} {κ : LatticeShape d} [NeZero N] [Fintype (LatticeSite N κ)]
  [Fintype (LatticeSite 1 κ)]
end Decay
theorem blockMomentLowerBound_pos (d : ℕ) : 0 < blockMomentLowerBound d := by apply _root_.YangMills.SharedProofs.p223 <;> assumption
end YangMills.Construction.LatticeFields.ProjGradDecayProof
