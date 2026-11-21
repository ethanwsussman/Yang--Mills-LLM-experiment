import YangMills.Construction.Lattice.GaugeTermOnACubeProof
import YangMills.Construction.LatticeFields.DifferenceIdentities
import YangMills.Construction.LatticeFields.KernelProjectionUnique
import YangMills.Construction.LatticeFields.MassiveLaplacianForms
import YangMills.Construction.LatticeFields.WeightConjDirichletGreenBoundsProof
import YangMills.Construction.LatticeFields.WeightConjLaplacianForm
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YangMills.Construction.LatticeFields.WeightConjMassiveLaplacianFormBoundProof
theorem finite_torusSites {d : ℕ} (N : ℕ) [NeZero N] (ℓ : Fin d → ℕ) (hℓ : ∀ μ, 1 ≤ ℓ μ) :
    Finite (LatticeSite N (LatticeShape.torus ℓ hℓ)) := by apply _root_.YangMills.Construction.LatticeFields.WeightConjProjComplProof.finite_torusSites <;> assumption
section Inner
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
    fieldNorm (F + G) ≤ fieldNorm F + fieldNorm G := by
  simp only [fieldNorm_eq_norm, toEuclidean_add]
  exact norm_add_le _ _
theorem fieldNorm_le_add_sub (F G : LatticeField M κ I) :
    fieldNorm F ≤ fieldNorm G + fieldNorm (F - G) := by
  have h := fieldNorm_add_le G (F - G)
  rwa [add_sub_cancel] at h
theorem eq_zero_of_fieldNorm_eq_zero [NeZero M] (F : LatticeField M κ I) (h : fieldNorm F = 0) :
    F = 0 := by apply _root_.YangMills.Construction.LatticeFields.WeightConjGreen.eq_zero_of_fieldNorm_eq_zero_aux <;> assumption
theorem map_sub_of_adjoint {M' : ℕ} {J : Type} [Fintype (LatticeSite M' κ)] [Fintype J]
    [NeZero M'] {O : LatticeField M κ I → LatticeField M' κ J}
    {S : LatticeField M' κ J → LatticeField M κ I}
    (h : ∀ F G, fieldInner (O F) G = fieldInner F (S G)) (F F' : LatticeField M κ I) :
    O (F - F') = O F - O F' := by
  rw [← sub_eq_zero]
  refine eq_zero_of_fieldNorm_eq_zero _ ?_
  have hz : fieldInner (O (F - F') - (O F - O F')) (O (F - F') - (O F - O F')) = 0 := by
    rw [fieldInner_sub_left, fieldInner_sub_left, h, h, h, fieldInner_sub_left]
    ring
  rw [fieldInner_self] at hz
  exact pow_eq_zero_iff (by norm_num) |>.mp hz
theorem fieldInner_smul_right (c : ℝ) (F G : LatticeField M κ I) :
    fieldInner F (c • G) = c * fieldInner F G := by
  have hv : toEuclidean (c • G) = c • toEuclidean G := by
    ext p
    simp only [toEuclidean, Pi.smul_apply, smul_eq_mul, PiLp.smul_apply]
    ring
  simp only [← inner_toEuclidean, hv, inner_smul_right]
theorem abs_fieldInner_sub_le {F' F G' G : LatticeField M κ I} {e' e : ℝ}
    (h' : fieldNorm (F' - G') ≤ e') (h : fieldNorm (F - G) ≤ e) :
    |fieldInner F' F - fieldInner G' G| ≤ e' * fieldNorm G + fieldNorm G' * e + e' * e := by apply _root_.YangMills.Construction.LatticeFields.WeightConjGreen.abs_fieldInner_sub_le_of_near <;> assumption
theorem abs_fieldInner_proj_sub_le {Pj Pθ : LatticeField M κ I → LatticeField M κ I} {k ρ' ρ : ℝ}
    (hsub : ∀ x y, Pθ (x - y) = Pθ x - Pθ y) (hbd : ∀ h, fieldNorm (Pθ h) ≤ 2 * fieldNorm h)
    (hnear : ∀ f, fieldNorm (Pθ f - Pj f) ≤ k * fieldNorm f) (x' x f' f : LatticeField M κ I)
    (hr' : fieldNorm (x' - f') ≤ ρ') (hr : fieldNorm (x - f) ≤ ρ) :
    |fieldInner x' (Pθ x) - fieldInner f' (Pj f)| ≤
      fieldNorm f' * (k * fieldNorm f) + ρ' * (2 * fieldNorm f) + fieldNorm f' * (2 * ρ) +
        ρ' * (2 * ρ) := by
  have id : fieldInner x' (Pθ x) - fieldInner f' (Pj f) =
      fieldInner f' (Pθ f - Pj f) + fieldInner (x' - f') (Pθ f) + fieldInner f' (Pθ (x - f)) +
        fieldInner (x' - f') (Pθ (x - f)) := by
    rw [hsub]
    simp only [fieldInner_sub_left, fieldInner_sub_right]
    ring
  have hρ' : 0 ≤ ρ' := (fieldNorm_nonneg _).trans hr'
  have hb : fieldNorm (Pθ (x - f)) ≤ 2 * ρ := (hbd _).trans (by linarith)
  have h1 : |fieldInner f' (Pθ f - Pj f)| ≤ fieldNorm f' * (k * fieldNorm f) :=
    (abs_fieldInner_le _ _).trans (mul_le_mul_of_nonneg_left (hnear f) (fieldNorm_nonneg _))
  have h2 : |fieldInner (x' - f') (Pθ f)| ≤ ρ' * (2 * fieldNorm f) :=
    (abs_fieldInner_le _ _).trans (mul_le_mul hr' (hbd f) (fieldNorm_nonneg _) hρ')
  have h3 : |fieldInner f' (Pθ (x - f))| ≤ fieldNorm f' * (2 * ρ) :=
    (abs_fieldInner_le _ _).trans (mul_le_mul_of_nonneg_left hb (fieldNorm_nonneg _))
  have h4 : |fieldInner (x' - f') (Pθ (x - f))| ≤ ρ' * (2 * ρ) :=
    (abs_fieldInner_le _ _).trans (mul_le_mul hr' hb (fieldNorm_nonneg _) hρ')
  obtain ⟨l1, u1⟩ := abs_le.mp h1
  obtain ⟨l2, u2⟩ := abs_le.mp h2
  obtain ⟨l3, u3⟩ := abs_le.mp h3
  obtain ⟨l4, u4⟩ := abs_le.mp h4
  rw [id]
  exact abs_le.mpr ⟨by linarith, by linarith⟩
theorem fieldNorm_le_of_sq_le (F : LatticeField M κ I) {C : ℝ} (hC : 0 ≤ C)
    (h : fieldNorm F ^ 2 ≤ C * fieldNorm F) : fieldNorm F ≤ C := by
  by_contra hlt
  rw [not_le] at hlt
  nlinarith
end Inner
section Weight
variable {d N : ℕ} [NeZero N] {κ : LatticeShape d}
theorem weightMul_exp_weightMul_exp_neg (θ : LatticeSite N κ → ℝ) (s : LatticeScale) {I : Type}
    (F : LatticeField (s.invSpacing N) κ I) :
    weightMul (fun x => Real.exp (θ x)) s (weightMul (fun x => Real.exp (-θ x)) s F) = F := by
  cases s <;> funext x i <;>
    simp [weightMul, mulBase, restrictUnitSites, ← mul_assoc, ← Real.exp_add]
theorem fieldInner_weightMul (w : LatticeSite N κ → ℝ) (s : LatticeScale) {I : Type}
    (F G : LatticeField (s.invSpacing N) κ I) :
    fieldInner (weightMul w s F) G = fieldInner F (weightMul w s G) := by
  cases s <;> refine tsum_congr fun p => ?_ <;> simp only [weightMul, mulBase] <;> ring
theorem weightMul_sub (w : LatticeSite N κ → ℝ) (s : LatticeScale) {I : Type}
    (F G : LatticeField (s.invSpacing N) κ I) :
    weightMul w s (F - G) = weightMul w s F - weightMul w s G := by
  cases s <;> funext x i <;> simp [weightMul, mulBase, mul_sub]
theorem fieldInner_weightConj_neg (θ : LatticeSite N κ → ℝ) (s s' : LatticeScale) {I J : Type}
    (O O₂ : LatticeField (s.invSpacing N) κ I → LatticeField (s'.invSpacing N) κ J)
    (F G : LatticeField (s.invSpacing N) κ I) :
    fieldInner (weightConj (-θ) s s' O F) (weightConj θ s s' O₂ G) =
      fieldInner (O (weightMul (fun x => Real.exp (-θ x)) s F))
        (O₂ (weightMul (fun x => Real.exp (θ x)) s G)) := by
  have hneg : (fun x => Real.exp (-(-θ) x)) = fun x => Real.exp (θ x) := by
    funext x
    simp
  have hpos : (fun x => Real.exp ((-θ) x)) = fun x => Real.exp (-θ x) := rfl
  simp only [weightConj]
  rw [hneg, hpos, fieldInner_weightMul, weightMul_exp_weightMul_exp_neg]
theorem weightConj_comp (θ : LatticeSite N κ → ℝ) (s s' s'' : LatticeScale) {I J K : Type}
    (O : LatticeField (s'.invSpacing N) κ J → LatticeField (s''.invSpacing N) κ K)
    (O' : LatticeField (s.invSpacing N) κ I → LatticeField (s'.invSpacing N) κ J)
    (F : LatticeField (s.invSpacing N) κ I) :
    weightConj θ s s'' (fun G => O (O' G)) F =
      weightConj θ s' s'' O (weightConj θ s s' O' F) := by
  simp only [weightConj]
  rw [weightMul_exp_weightMul_exp_neg]
theorem weightConj_sub (θ : LatticeSite N κ → ℝ) (s s' : LatticeScale) {I J : Type}
    {O : LatticeField (s.invSpacing N) κ I → LatticeField (s'.invSpacing N) κ J}
    (h : ∀ x y, O (x - y) = O x - O y) (x y : LatticeField (s.invSpacing N) κ I) :
    weightConj θ s s' O (x - y) = weightConj θ s s' O x - weightConj θ s s' O y := by
  simp only [weightConj]
  rw [weightMul_sub, h, weightMul_sub]
end Weight
section Core
variable {d N : ℕ} {κ : LatticeShape d}
def complLaplacianForm (Pj : ScalarField N κ → ScalarField N κ) (a : ℝ) (X : LatticeOneForm N κ) :
    LatticeOneForm N κ :=
  tensorLaplacian X - latticeGrad (Pj (latticeDiv X)) + a • bondBlockAvgAdj (bondBlockAvg X)
structure TorusOperatorFacts (κ : LatticeShape d) (N : ℕ) (Pj : ScalarField N κ → ScalarField N κ) :
    Prop where
  tensorGrad_adjoint : ∀ (F : LatticeOneForm N κ) (G : LatticeTensor N κ (1 + 1)),
    fieldInner (tensorGrad F) G = fieldInner F (tensorGradAdjoint G)
  grad_adjoint : ∀ (f : ScalarField N κ) (A : LatticeOneForm N κ),
    fieldInner (latticeGrad f) A = fieldInner f (latticeDiv A)
  bond_adjoint : ∀ (A : LatticeOneForm N κ) (B : LatticeOneForm 1 κ),
    fieldInner (bondBlockAvg A) B = fieldInner A (bondBlockAvgAdj B)
  div_le : ∀ A : LatticeOneForm N κ, fieldNorm (latticeDiv A) ≤ fieldNorm (tensorGrad A)
  bond_le : ∀ A : LatticeOneForm N κ, fieldNorm (bondBlockAvg A) ≤ fieldNorm A
  proj_sub : ∀ x y : ScalarField N κ, Pj (x - y) = Pj x - Pj y
  proj_le : ∀ f : ScalarField N κ, fieldNorm (Pj f) ≤ fieldNorm f
variable [Fintype (LatticeSite N κ)] [Fintype (LatticeSite 1 κ)]
  {Pj : ScalarField N κ → ScalarField N κ}
theorem fieldInner_complLaplacianForm (H : TorusOperatorFacts κ N Pj) (a : ℝ)
    (v u : LatticeOneForm N κ) :
    fieldInner v (complLaplacianForm Pj a u) =
      fieldInner (tensorGrad v) (tensorGrad u) - fieldInner (latticeDiv v) (Pj (latticeDiv u)) +
        a * fieldInner (bondBlockAvg v) (bondBlockAvg u) := by
  have h1 : fieldInner v (tensorLaplacian u) = fieldInner (tensorGrad v) (tensorGrad u) :=
    (H.tensorGrad_adjoint v (tensorGrad u)).symm
  have h2 : fieldInner v (latticeGrad (Pj (latticeDiv u))) =
      fieldInner (latticeDiv v) (Pj (latticeDiv u)) := by
    rw [fieldInner_comm, H.grad_adjoint, fieldInner_comm]
  have h3 : fieldInner v (bondBlockAvgAdj (bondBlockAvg u)) =
      fieldInner (bondBlockAvg v) (bondBlockAvg u) :=
    (H.bond_adjoint v (bondBlockAvg u)).symm
  rw [complLaplacianForm, fieldInner_add_right, fieldInner_sub_right, fieldInner_smul_right, h1,
    h2, h3]
theorem fieldInner_weightConj_complLaplacianForm [NeZero N] (H : TorusOperatorFacts κ N Pj)
    (a : ℝ) (θ : LatticeSite N κ → ℝ) (A' A : LatticeOneForm N κ) :
    fieldInner A' (weightConj θ .fine .fine (complLaplacianForm Pj a) A) =
      fieldInner (weightConj (-θ) .fine .fine (tensorGrad (r := 1)) A')
          (weightConj θ .fine .fine (tensorGrad (r := 1)) A) -
        fieldInner (weightConj (-θ) .fine .fine latticeDiv A')
          (weightConj θ .fine .fine Pj (weightConj θ .fine .fine latticeDiv A)) +
        a * fieldInner (weightConj (-θ) .fine .unit bondBlockAvg A')
          (weightConj θ .fine .unit bondBlockAvg A) := by
  have c1 := fieldInner_weightConj_neg θ .fine .fine (tensorGrad (r := 1) (N := N) (κ := κ))
    tensorGrad A' A
  have c2 := fieldInner_weightConj_neg θ .fine .fine (latticeDiv (N := N) (κ := κ))
    (fun G => Pj (latticeDiv G)) A' A
  have c3 := fieldInner_weightConj_neg θ .fine .unit (bondBlockAvg (N := N) (κ := κ))
    bondBlockAvg A' A
  rw [weightConj_comp θ .fine .fine .fine Pj latticeDiv A] at c2
  rw [c1, c2, c3]
  exact (fieldInner_weightMul _ .fine A' _).symm.trans (fieldInner_complLaplacianForm H a _ _)
theorem three_term_arith {ε c a T a1 a2 b1 b2 t1 t2 t3 : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1)
    (hc : 0 ≤ c) (ha : 0 ≤ a) (ha1 : 0 ≤ a1) (ha2 : 0 ≤ a2) (hS : a1 * b2 + b1 * a2 ≤ T)
    (hU : a1 * a2 ≤ T) (hV : b1 * b2 ≤ T)
    (ht1 : t1 ≤ ε * a1 * b2 + b1 * (ε * a2) + ε * a1 * (ε * a2))
    (ht2 : t2 ≤ c * ε * (b1 * b2) + 2 * ε * (a1 * b2) + 2 * ε * (b1 * a2) +
      2 * ε ^ 2 * (a1 * a2))
    (ht3 : t3 ≤ 3 * ε * (a1 * a2)) : t1 + t2 + a * t3 ≤ (c + 6 + 3 * a) * ε * T := by
  have e2 : ε ^ 2 ≤ ε := by nlinarith
  have U0 : 0 ≤ a1 * a2 := mul_nonneg ha1 ha2
  have s1 : ε * (a1 * b2 + b1 * a2) ≤ ε * T := mul_le_mul_of_nonneg_left hS h0
  have s2 : ε * (a1 * a2) ≤ ε * T := mul_le_mul_of_nonneg_left hU h0
  have s3 : ε ^ 2 * (a1 * a2) ≤ ε * (a1 * a2) := mul_le_mul_of_nonneg_right e2 U0
  have s4 : c * ε * (b1 * b2) ≤ c * ε * T := mul_le_mul_of_nonneg_left hV (mul_nonneg hc h0)
  have s5 : a * t3 ≤ a * (3 * (ε * T)) :=
    mul_le_mul_of_nonneg_left (ht3.trans (by linarith)) ha
  have r1 : ε * a1 * b2 + b1 * (ε * a2) + ε * a1 * (ε * a2) =
      ε * (a1 * b2 + b1 * a2) + ε ^ 2 * (a1 * a2) := by ring
  have r3 : (c + 6 + 3 * a) * ε * T = c * ε * T + 6 * (ε * T) + a * (3 * (ε * T)) := by ring
  rw [r3]
  rw [r1] at ht1
  linarith
theorem abs_fieldInner_weightConj_sub_le [NeZero N] (H : TorusOperatorFacts κ N Pj)
    {θ : LatticeSite N κ → ℝ} {ε c a T : ℝ}
    (h0 : 0 ≤ ε) (h1 : ε ≤ 1) (hc : 0 ≤ c) (hcε : c * ε ≤ 1) (ha : 0 ≤ a)
    (nP : ∀ A : LatticeOneForm N κ,
      fieldNorm (weightConj θ .fine .fine (tensorGrad (r := 1)) A - tensorGrad A) ≤
        ε * fieldNorm A)
    (nM : ∀ A : LatticeOneForm N κ,
      fieldNorm (weightConj (-θ) .fine .fine (tensorGrad (r := 1)) A - tensorGrad A) ≤
        ε * fieldNorm A)
    (dP : ∀ A : LatticeOneForm N κ,
      fieldNorm (weightConj θ .fine .fine latticeDiv A - latticeDiv A) ≤ ε * fieldNorm A)
    (dM : ∀ A : LatticeOneForm N κ,
      fieldNorm (weightConj (-θ) .fine .fine latticeDiv A - latticeDiv A) ≤ ε * fieldNorm A)
    (qP : ∀ A : LatticeOneForm N κ,
      fieldNorm (weightConj θ .fine .unit bondBlockAvg A - bondBlockAvg A) ≤ ε * fieldNorm A)
    (qM : ∀ A : LatticeOneForm N κ,
      fieldNorm (weightConj (-θ) .fine .unit bondBlockAvg A - bondBlockAvg A) ≤ ε * fieldNorm A)
    (pP : ∀ f : ScalarField N κ,
      fieldNorm (weightConj θ .fine .fine Pj f - Pj f) ≤ c * ε * fieldNorm f)
    (A' A : LatticeOneForm N κ)
    (hS : fieldNorm A' * fieldNorm (tensorGrad A) + fieldNorm (tensorGrad A') * fieldNorm A ≤ T)
    (hU : fieldNorm A' * fieldNorm A ≤ T)
    (hV : fieldNorm (tensorGrad A') * fieldNorm (tensorGrad A) ≤ T) :
    |fieldInner A' (weightConj θ .fine .fine (complLaplacianForm Pj a) A -
        complLaplacianForm Pj a A)| ≤ (c + 6 + 3 * a) * ε * T := by
  have hsub : ∀ x y : ScalarField N κ,
      weightConj θ .fine .fine Pj (x - y) =
        weightConj θ .fine .fine Pj x - weightConj θ .fine .fine Pj y :=
    weightConj_sub θ .fine .fine H.proj_sub
  have hbd : ∀ h : ScalarField N κ,
      fieldNorm (weightConj θ .fine .fine Pj h) ≤ 2 * fieldNorm h := by
    intro h
    have e1 := fieldNorm_le_add_sub (M := N) (weightConj θ .fine .fine Pj h) (Pj h)
    have e2 := H.proj_le h
    have e3 := pP h
    have e4 : c * ε * fieldNorm h ≤ fieldNorm h :=
      mul_le_of_le_one_left (fieldNorm_nonneg _) hcε
    linarith
  have t1 := abs_fieldInner_sub_le (M := N) (nM A') (nP A)
  have t2 := abs_fieldInner_proj_sub_le (M := N) hsub hbd pP
    (weightConj (-θ) .fine .fine latticeDiv A')
    (weightConj θ .fine .fine latticeDiv A) (latticeDiv A') (latticeDiv A) (dM A') (dP A)
  have t3 := abs_fieldInner_sub_le (M := 1) (qM A') (qP A)
  have ha1 : 0 ≤ fieldNorm A' := fieldNorm_nonneg _
  have ha2 : 0 ≤ fieldNorm A := fieldNorm_nonneg _
  have hb1 : 0 ≤ fieldNorm (tensorGrad A') := fieldNorm_nonneg _
  have hf1 := H.div_le A'
  have hf2 := H.div_le A
  have hq1 := H.bond_le A'
  have hq2 := H.bond_le A
  have hf2' : 0 ≤ fieldNorm (latticeDiv A) := fieldNorm_nonneg _
  have hcε0 : 0 ≤ c * ε := mul_nonneg hc h0
  have ht2 : |fieldInner (weightConj (-θ) .fine .fine latticeDiv A')
        (weightConj θ .fine .fine Pj (weightConj θ .fine .fine latticeDiv A)) -
      fieldInner (latticeDiv A') (Pj (latticeDiv A))| ≤
      c * ε * (fieldNorm (tensorGrad A') * fieldNorm (tensorGrad A)) +
        2 * ε * (fieldNorm A' * fieldNorm (tensorGrad A)) +
        2 * ε * (fieldNorm (tensorGrad A') * fieldNorm A) +
        2 * ε ^ 2 * (fieldNorm A' * fieldNorm A) := by
    refine t2.trans ?_
    have m1 : fieldNorm (latticeDiv A') * fieldNorm (latticeDiv A) ≤
        fieldNorm (tensorGrad A') * fieldNorm (tensorGrad A) := mul_le_mul hf1 hf2 hf2' hb1
    have m2 : fieldNorm A' * fieldNorm (latticeDiv A) ≤ fieldNorm A' * fieldNorm (tensorGrad A) :=
      mul_le_mul_of_nonneg_left hf2 ha1
    have m3 : fieldNorm (latticeDiv A') * fieldNorm A ≤ fieldNorm (tensorGrad A') * fieldNorm A :=
      mul_le_mul_of_nonneg_right hf1 ha2
    have n1 := mul_le_mul_of_nonneg_left m1 hcε0
    have n2 := mul_le_mul_of_nonneg_left m2 (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) h0)
    have n3 := mul_le_mul_of_nonneg_left m3 (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) h0)
    nlinarith
  have ht3 : |fieldInner (weightConj (-θ) .fine .unit bondBlockAvg A')
        (weightConj θ .fine .unit bondBlockAvg A) -
      fieldInner (bondBlockAvg A') (bondBlockAvg A)| ≤ 3 * ε * (fieldNorm A' * fieldNorm A) := by
    refine t3.trans ?_
    have m1 : fieldNorm A' * fieldNorm (bondBlockAvg A) ≤ fieldNorm A' * fieldNorm A :=
      mul_le_mul_of_nonneg_left hq2 ha1
    have m2 : fieldNorm (bondBlockAvg A') * fieldNorm A ≤ fieldNorm A' * fieldNorm A :=
      mul_le_mul_of_nonneg_right hq1 ha2
    have U0 : 0 ≤ fieldNorm A' * fieldNorm A := mul_nonneg ha1 ha2
    have n1 := mul_le_mul_of_nonneg_left m1 h0
    have n2 := mul_le_mul_of_nonneg_left m2 h0
    have n3 : ε * (ε * (fieldNorm A' * fieldNorm A)) ≤ 1 * (ε * (fieldNorm A' * fieldNorm A)) :=
      mul_le_mul_of_nonneg_right h1 (mul_nonneg h0 U0)
    nlinarith
  have hfin := three_term_arith h0 h1 hc ha ha1 ha2 hS hU hV t1 ht2 ht3
  rw [fieldInner_sub_right, fieldInner_weightConj_complLaplacianForm H a θ A' A,
    fieldInner_complLaplacianForm H a A' A]
  refine le_trans ?_ hfin
  generalize fieldInner (weightConj (-θ) .fine .fine (tensorGrad (r := 1)) A')
      (weightConj θ .fine .fine (tensorGrad (r := 1)) A) = x1
  generalize fieldInner (tensorGrad A') (tensorGrad A) = y1
  generalize fieldInner (weightConj (-θ) .fine .fine latticeDiv A')
      (weightConj θ .fine .fine Pj (weightConj θ .fine .fine latticeDiv A)) = x2
  generalize fieldInner (latticeDiv A') (Pj (latticeDiv A)) = y2
  generalize fieldInner (weightConj (-θ) .fine .unit bondBlockAvg A')
      (weightConj θ .fine .unit bondBlockAvg A) = x3
  generalize fieldInner (bondBlockAvg A') (bondBlockAvg A) = y3
  have e : x1 - x2 + a * x3 - (y1 - y2 + a * y3) = (x1 - y1) - (x2 - y2) + a * (x3 - y3) := by
    ring
  have e3 : |a * (x3 - y3)| = a * |x3 - y3| := by rw [abs_mul, abs_of_nonneg ha]
  rw [e, ← e3]
  have l1 := neg_abs_le (x1 - y1)
  have l2 := neg_abs_le (x2 - y2)
  have l3 := neg_abs_le (a * (x3 - y3))
  have u1 := le_abs_self (x1 - y1)
  have u2 := le_abs_self (x2 - y2)
  have u3 := le_abs_self (a * (x3 - y3))
  exact abs_le.mpr ⟨by linarith, by linarith⟩
end Core
theorem blockMomentLowerBound_pos (d : ℕ) : 0 < blockMomentLowerBound d := by apply _root_.YangMills.SharedProofs.p223 <;> assumption
theorem proof
    (hAvg : ConjugatedBlockAveragingBound.Claim)
    (hDiff : ConjugatedDifferenceBound.Claim)
    (hProj : WeightConjProjComplBound)
    (hM : DirichletBlockFacts)
    (hExpr : MassiveLaplacianForms.Claim)
    (hA : BlockAveragingBounds)
    (hB : BlockAvgAdjointFacts)
    (hD : TorusLaws.TorusLatticeFacts)
    (hI : DifferenceIdentities.Claim)
    (hF : SobolevOneNormProducts.Claim)
    (hK : KernelProjectionUnique.Claim) :
    WeightConjMassiveLaplacianFormBound := by
  intro P ℓ hℓ δ θ hδ hlip hc A A'
  have : Finite (LatticeSite P.N (LatticeShape.torus ℓ hℓ)) := finite_torusSites _ ℓ hℓ
  have : Finite (LatticeSite 1 (LatticeShape.torus ℓ hℓ)) := finite_torusSites 1 ℓ hℓ
  letI : Fintype (LatticeSite P.N (LatticeShape.torus ℓ hℓ)) := Fintype.ofFinite _
  letI : Fintype (LatticeSite 1 (LatticeShape.torus ℓ hℓ)) := Fintype.ofFinite _
  obtain ⟨-, al, -, -, bl⟩ := hD P.d P.L P.k P.N P.two_le_d P.two_le_L rfl ℓ hℓ
  obtain ⟨-, -, -, bondAdj⟩ := hB P.d P.N (LatticeShape.torus ℓ hℓ)
  obtain ⟨⟨-, -, -, -, cQ, hcQ, hnQ⟩, -⟩ := hA P.d P.L P.k P.two_le_d P.two_le_L ℓ hℓ
  obtain ⟨-, -, hproj⟩ := hM P.d P.L P.k P.two_le_d P.two_le_L ℓ hℓ
  have hexp : ∀ X : LatticeOneForm P.N (LatticeShape.torus ℓ hℓ),
      massiveLaplacian P.a X = massiveLaplacianAlt P.a X :=
    ((hExpr P.d P.L P.k P.two_le_d P.two_le_L ℓ hℓ).2 P.a P.a_pos).1
  have hproj' : ∀ f : ScalarField P.N (LatticeShape.torus ℓ hℓ),
      kerLaplacianProjCompl f = dirichletProjCompl Set.univ Set.univ f := hproj
  have hQ : ∀ X : LatticeOneForm P.N (LatticeShape.torus ℓ hℓ),
      fieldNorm (bondBlockAvg X) ≤ cQ * fieldNorm X := hnQ.1.2
  have hR : ∀ f : ScalarField P.N (LatticeShape.torus ℓ hℓ),
      IsOrthProj (laplacianImageKer P.N ℓ hℓ) f (kerLaplacianProj f) :=
    fun f => (hK P.d P.N ℓ hℓ f).1
  have horth : ∀ f g : ScalarField P.N (LatticeShape.torus ℓ hℓ),
      fieldInner (kerLaplacianProjCompl f) (kerLaplacianProj g) = 0 :=
    fun f g => (hR f).2 _ (hR g).1
  have hsymm : ∀ f g : ScalarField P.N (LatticeShape.torus ℓ hℓ),
      fieldInner (kerLaplacianProjCompl f) g = fieldInner f (kerLaplacianProjCompl g) := by
    intro f g
    have h1 := horth f g
    have h2 := horth g f
    simp only [kerLaplacianProjCompl, fieldInner_sub_left, fieldInner_sub_right] at h1 h2 ⊢
    rw [fieldInner_comm g (kerLaplacianProj f),
      fieldInner_comm (kerLaplacianProj g) (kerLaplacianProj f)] at h2
    linarith
  have hPle : ∀ f : ScalarField P.N (LatticeShape.torus ℓ hℓ),
      fieldNorm (kerLaplacianProjCompl f) ≤ fieldNorm f := by
    intro f
    refine fieldNorm_le_of_sq_le _ (fieldNorm_nonneg _) ?_
    have e : fieldInner (kerLaplacianProjCompl f) (f - kerLaplacianProj f) =
        fieldInner (kerLaplacianProjCompl f) f := by
      rw [fieldInner_sub_right, horth, sub_zero]
    have e' : fieldNorm (kerLaplacianProjCompl f) ^ 2 =
        fieldInner (kerLaplacianProjCompl f) f := (fieldInner_self _).symm.trans e
    rw [e', mul_comm]
    exact fieldInner_le _ _
  have H : TorusOperatorFacts (LatticeShape.torus ℓ hℓ) P.N kerLaplacianProjCompl :=
    { tensorGrad_adjoint := al.tensorGrad_adjoint 1
      grad_adjoint := al.grad_adjoint
      bond_adjoint := fun X B => bondAdj X B Summable.of_finite Summable.of_finite
      div_le := fun X => by
        have h := (hI P (LatticeShape.torus ℓ hℓ)).norm_tensorGrad_sq X Summable.of_finite
        have h1 : fieldNorm (latticeDiv X) ^ 2 ≤ fieldNorm (tensorGrad X) ^ 2 := by
          rw [h]
          nlinarith [sq_nonneg (fieldNorm (latticeCurl X))]
        exact (pow_le_pow_iff_left₀ (fieldNorm_nonneg _) (fieldNorm_nonneg _) (by norm_num)).mp h1
      bond_le := fun X => (hQ X).trans (mul_le_of_le_one_left (fieldNorm_nonneg _) hcQ)
      proj_sub := map_sub_of_adjoint hsymm
      proj_le := hPle }
  have hlipN : LipschitzWeight δ (-θ) := by
    refine ⟨hlip.pos, ?_, fun x x' => ?_⟩
    · obtain ⟨C, hCb⟩ := hlip.bdd
      exact ⟨C, fun x => by rw [Pi.neg_apply, abs_neg]; exact hCb x⟩
    · rw [Pi.neg_apply, Pi.neg_apply, neg_sub_neg, abs_sub_comm]
      exact hlip.lip x x'
  have hd1 : (0 : ℝ) < 2 * ((P.d : ℝ) + 1) := by positivity
  have hε0 : 0 ≤ 2 * ((P.d : ℝ) + 1) * δ := (mul_pos hd1 hlip.pos).le
  have hε1 : 2 * ((P.d : ℝ) + 1) * δ ≤ 1 := by
    have h := mul_le_mul_of_nonneg_left hδ hd1.le
    rwa [mul_one_div_cancel hd1.ne'] at h
  have hcp : 0 ≤ 2256 * (P.d : ℝ) ^ 5 * blockMomentLowerBound P.d ^ (-2 : ℤ) := by
    have := blockMomentLowerBound_pos P.d
    positivity
  have hX : blockUnion P.N (Set.univ : Set (LatticeSite 1 (LatticeShape.torus ℓ hℓ))) =
      Set.univ := by
    refine Set.eq_univ_of_forall fun x => ?_
    obtain ⟨y, hy, -⟩ := bl.existsUnique_mem x
    exact Set.mem_biUnion (Set.mem_univ y) hy
  have hpb := hProj P ℓ hℓ δ θ hδ hlip hc Set.univ ⟨0, trivial⟩
  rw [hX] at hpb
  have hPeq : (kerLaplacianProjCompl :
      ScalarField P.N (LatticeShape.torus ℓ hℓ) → ScalarField P.N (LatticeShape.torus ℓ hℓ)) =
      dirichletProjCompl Set.univ Set.univ := funext hproj'
  have pP : ∀ f : ScalarField P.N (LatticeShape.torus ℓ hℓ),
      fieldNorm (weightConj θ .fine .fine kerLaplacianProjCompl f - kerLaplacianProjCompl f) ≤
      2256 * (P.d : ℝ) ^ 5 * blockMomentLowerBound P.d ^ (-2 : ℤ) * (2 * ((P.d : ℝ) + 1) * δ) *
        fieldNorm f := fun f => by
    rw [hPeq]
    exact hpb f fun x hx => (hx trivial).elim
  obtain ⟨-, dP, nP, -⟩ := hDiff P ℓ hℓ δ θ hδ hlip
  obtain ⟨-, dM, nM, -⟩ := hDiff P ℓ hℓ δ (-θ) hδ hlipN
  obtain ⟨-, -, qP, -⟩ := hAvg P ℓ hℓ δ θ hδ hlip
  obtain ⟨-, -, qM, -⟩ := hAvg P ℓ hℓ δ (-θ) hδ hlipN
  have hop : (massiveLaplacian P.a :
      LatticeOneForm P.N (LatticeShape.torus ℓ hℓ) → LatticeOneForm P.N (LatticeShape.torus ℓ hℓ)) =
      complLaplacianForm kerLaplacianProjCompl P.a := funext hexp
  rw [hop]
  obtain ⟨hS, hU, hV⟩ := hF P.d P.N 1 ℓ hℓ (Nat.pos_of_ne_zero (NeZero.ne _)) le_rfl A A'
  exact (abs_fieldInner_weightConj_sub_le H hε0 hε1 hcp hc P.a_pos.le (nP 1) (nM 1) dP dM qP qM
    pP A' A hS hU hV).trans (le_of_eq (by ring))
end YangMills.Construction.LatticeFields.WeightConjMassiveLaplacianFormBoundProof
