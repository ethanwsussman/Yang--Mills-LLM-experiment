import YangMills.Construction.LatticeFields.ConjugatedDifferenceBound
import YangMills.Construction.LatticeFields.WeightConjProjComplProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.LatticeFields
namespace WeightConjugation
variable {d N : ℕ} {κ : LatticeShape d}
theorem torus_finite [NeZero N] (ℓ : Fin d → ℕ) (hℓ : ∀ μ, 1 ≤ ℓ μ) :
    Finite (LatticeSite N (LatticeShape.torus ℓ hℓ)) := by apply _root_.YangMills.Construction.LatticeFields.WeightConjProjComplProof.finite_torusSites <;> assumption
theorem siteDist_add_unitStep_le [NeZero N] (x : LatticeSite N κ) (μ : Fin d) :
    siteDist (x + unitStep N κ μ) x ≤ latticeSpacing N := by
  have hη : 0 ≤ latticeSpacing N := inv_nonneg.mpr (Nat.cast_nonneg N)
  have habs : ∀ ν, |(Pi.single μ (latticeSpacing N) : Fin d → ℝ) ν| =
      if ν = μ then latticeSpacing N else 0 := by
    intro ν
    by_cases h : ν = μ
    · subst h
      simp [abs_of_nonneg hη]
    · simp [h]
  have hs : x + unitStep N κ μ - x = unitStep N κ μ := add_sub_cancel_left _ _
  unfold siteDist
  rw [hs]
  unfold unitStep
  refine le_trans (csInf_le ⟨0, ?_⟩ ⟨_, rfl, rfl⟩) ?_
  · rintro t ⟨u, -, rfl⟩
    exact Finset.sum_nonneg fun _ _ => abs_nonneg _
  · simp [habs]
theorem abs_inv_spacing_mul_exp_sub_one_le [NeZero N] {δ t : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (ht : |t| ≤ δ * latticeSpacing N) :
    |(latticeSpacing N)⁻¹ * (Real.exp t - 1)| ≤ 2 * δ := by
  have hN : (1 : ℝ) ≤ N := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have hη : 0 < latticeSpacing N := inv_pos.mpr (by linarith)
  have hη1 : latticeSpacing N ≤ 1 := inv_le_one_of_one_le₀ hN
  have ht1 : |t| ≤ 1 := ht.trans (by nlinarith)
  have he := Real.abs_exp_sub_one_le ht1
  rw [abs_mul, abs_of_pos (inv_pos.mpr hη)]
  calc (latticeSpacing N)⁻¹ * |Real.exp t - 1|
        ≤ (latticeSpacing N)⁻¹ * (2 * (δ * latticeSpacing N)) := by
        refine mul_le_mul_of_nonneg_left (he.trans ?_) (inv_pos.mpr hη).le
        linarith
    _ = 2 * δ := by
        field_simp
theorem fieldInner_self_eq_sum {I : Type} [Fintype (LatticeSite N κ)] [Fintype I]
    (F : LatticeField N κ I) :
    fieldInner F F = latticeSpacing N ^ d * ∑ x, ∑ i, F x i ^ 2 := by
  unfold fieldInner
  rw [tsum_fintype, Fintype.sum_prod_type, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring
theorem fieldNorm_le_of_sum_sq_le {I J : Type} [Fintype (LatticeSite N κ)] [Fintype I] [Fintype J]
    {F : LatticeField N κ I} {G : LatticeField N κ J} {K : ℝ} (hK : 0 ≤ K)
    (h : ∑ x, ∑ j, G x j ^ 2 ≤ K ^ 2 * ∑ x, ∑ i, F x i ^ 2) : fieldNorm G ≤ K * fieldNorm F := by
  have hc : 0 ≤ latticeSpacing N ^ d := pow_nonneg (inv_nonneg.mpr (Nat.cast_nonneg N)) d
  unfold fieldNorm
  rw [fieldInner_self_eq_sum, fieldInner_self_eq_sum]
  calc Real.sqrt (latticeSpacing N ^ d * ∑ x, ∑ j, G x j ^ 2)
      ≤ Real.sqrt (K ^ 2 * (latticeSpacing N ^ d * ∑ x, ∑ i, F x i ^ 2)) := by
        refine Real.sqrt_le_sqrt ?_
        calc latticeSpacing N ^ d * ∑ x, ∑ j, G x j ^ 2
            ≤ latticeSpacing N ^ d * (K ^ 2 * ∑ x, ∑ i, F x i ^ 2) :=
              mul_le_mul_of_nonneg_left h hc
          _ = _ := by ring
    _ = K * Real.sqrt (latticeSpacing N ^ d * ∑ x, ∑ i, F x i ^ 2) := by
        rw [Real.sqrt_mul (sq_nonneg K), Real.sqrt_sq hK]
def tensorIndexCons (d r : ℕ) : Fin d × (Fin r → Fin d) ≃ (Fin (r + 1) → Fin d) where
  toFun p := Fin.cons p.1 p.2
  invFun i := (i 0, Fin.tail i)
  left_inv p := by simp
  right_inv i := Fin.cons_self_tail i
theorem sum_sq_shift_forward {r : ℕ} [Fintype (LatticeSite N κ)] (F : LatticeTensor N κ r) :
    ∑ x, ∑ i : Fin (r + 1) → Fin d, F (x + unitStep N κ (i 0)) (Fin.tail i) ^ 2 =
      (d : ℝ) * ∑ x, ∑ j, F x j ^ 2 := by
  rw [Finset.sum_comm]
  calc ∑ i : Fin (r + 1) → Fin d, ∑ x, F (x + unitStep N κ (i 0)) (Fin.tail i) ^ 2
      = ∑ i : Fin (r + 1) → Fin d, ∑ x, F x (Fin.tail i) ^ 2 := by
        refine Finset.sum_congr rfl fun i _ => ?_
        exact Equiv.sum_comp (Equiv.addRight (unitStep N κ (i 0))) fun x => F x (Fin.tail i) ^ 2
    _ = ∑ p : Fin d × (Fin r → Fin d), ∑ x, F x p.2 ^ 2 := by
        rw [← (tensorIndexCons d r).sum_comp]
        refine Finset.sum_congr rfl fun p _ => ?_
        simp [tensorIndexCons]
    _ = (d : ℝ) * ∑ x, ∑ j, F x j ^ 2 := by
        rw [Fintype.sum_prod_type, Finset.sum_comm (s := Finset.univ (α := LatticeSite N κ))]
        simp
theorem sum_sq_shift_backward {r : ℕ} [Fintype (LatticeSite N κ)] (F : LatticeTensor N κ (r + 1)) :
    ∑ x, ∑ i : Fin r → Fin d, ∑ μ, F (x - unitStep N κ μ) (Fin.cons μ i) ^ 2 =
      ∑ x, ∑ j, F x j ^ 2 := by
  calc ∑ x, ∑ i : Fin r → Fin d, ∑ μ, F (x - unitStep N κ μ) (Fin.cons μ i) ^ 2
      = ∑ p : Fin d × (Fin r → Fin d), ∑ x, F (x - unitStep N κ p.1) (Fin.cons p.1 p.2) ^ 2 := by
        rw [Finset.sum_comm, Fintype.sum_prod_type_right]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_comm]
    _ = ∑ p : Fin d × (Fin r → Fin d), ∑ x, F x (Fin.cons p.1 p.2) ^ 2 := by
        refine Finset.sum_congr rfl fun p _ => ?_
        exact Equiv.sum_comp (Equiv.subRight (unitStep N κ p.1)) fun x => F x (Fin.cons p.1 p.2) ^ 2
    _ = ∑ i : Fin (r + 1) → Fin d, ∑ x, F x i ^ 2 :=
        (tensorIndexCons d r).sum_comp fun i => ∑ x, F x i ^ 2
    _ = ∑ x, ∑ j, F x j ^ 2 := Finset.sum_comm
theorem weightConj_tensorGrad_sub_apply [NeZero N] (θ : LatticeSite N κ → ℝ) {r : ℕ}
    (F : LatticeTensor N κ r) (x : LatticeSite N κ) (i : Fin (r + 1) → Fin d) :
    (weightConj θ .fine .fine (tensorGrad (r := r)) F - tensorGrad F) x i =
      (latticeSpacing N)⁻¹ * (Real.exp (θ (x + unitStep N κ (i 0)) - θ x) - 1) *
        F (x + unitStep N κ (i 0)) (Fin.tail i) := by
  simp only [weightConj, weightMul, mulBase, tensorGrad, forwardDiff, shiftForward, Pi.sub_apply,
    Pi.smul_apply, smul_eq_mul, Real.exp_neg, Real.exp_sub]
  have hb : Real.exp (θ x) ≠ 0 := (Real.exp_pos _).ne'
  field_simp
  ring
theorem weightConj_tensorGradAdjoint_sub_apply [NeZero N] (θ : LatticeSite N κ → ℝ) {r : ℕ}
    (F : LatticeTensor N κ (r + 1)) (x : LatticeSite N κ) (i : Fin r → Fin d) :
    (weightConj θ .fine .fine (tensorGradAdjoint (r := r)) F - tensorGradAdjoint F) x i =
      ∑ μ, (latticeSpacing N)⁻¹ * (Real.exp (θ (x - unitStep N κ μ) - θ x) - 1) *
        F (x - unitStep N κ μ) (Fin.cons μ i) := by
  simp only [weightConj, weightMul, mulBase, tensorGradAdjoint, backwardDiff,
    shiftBackward, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun μ _ => ?_
  simp only [Real.exp_neg, Real.exp_sub]
  have hb : Real.exp (θ x) ≠ 0 := (Real.exp_pos _).ne'
  field_simp
  ring
theorem mul_sq_le_of_abs_le {w b f : ℝ} (h : |w| ≤ b) : (w * f) ^ 2 ≤ b ^ 2 * f ^ 2 := by
  rw [mul_pow, ← sq_abs w]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg w) h 2) (sq_nonneg f)
theorem natCast_mul_sq_le (d : ℕ) (δ : ℝ) :
    (d : ℝ) * (2 * δ) ^ 2 ≤ (2 * ((d : ℝ) + 1) * δ) ^ 2 := by
  have : 0 ≤ 4 * δ ^ 2 * ((d : ℝ) ^ 2 + d + 1) := by positivity
  linarith
theorem weightConj_tensorGrad_close [NeZero N] [Finite (LatticeSite N κ)] {δ : ℝ} (hδ : 0 ≤ δ)
    (hδ1 : δ ≤ 1) (θ : LatticeSite N κ → ℝ)
    (hθ : ∀ y μ, |θ (y + unitStep N κ μ) - θ y| ≤ δ * latticeSpacing N) {r : ℕ}
    (F : LatticeTensor N κ r) :
    fieldNorm (weightConj θ .fine .fine (tensorGrad (r := r)) F - tensorGrad F) ≤
      2 * ((d : ℝ) + 1) * δ * fieldNorm F := by
  let _ : Fintype (LatticeSite N κ) := Fintype.ofFinite _
  refine fieldNorm_le_of_sum_sq_le (by positivity) ?_
  have hS : 0 ≤ ∑ x, ∑ j, F x j ^ 2 :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  calc ∑ x, ∑ i, (weightConj θ .fine .fine (tensorGrad (r := r)) F - tensorGrad F) x i ^ 2
      ≤ ∑ x, ∑ i : Fin (r + 1) → Fin d,
          (2 * δ) ^ 2 * F (x + unitStep N κ (i 0)) (Fin.tail i) ^ 2 := by
        refine Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun i _ => ?_
        rw [weightConj_tensorGrad_sub_apply]
        exact mul_sq_le_of_abs_le (abs_inv_spacing_mul_exp_sub_one_le hδ hδ1 (hθ x (i 0)))
    _ = (2 * δ) ^ 2 * ((d : ℝ) * ∑ x, ∑ j, F x j ^ 2) := by
        simp only [← Finset.mul_sum]
        rw [sum_sq_shift_forward]
    _ = ((d : ℝ) * (2 * δ) ^ 2) * ∑ x, ∑ j, F x j ^ 2 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (natCast_mul_sq_le d δ) hS
theorem weightConj_tensorGradAdjoint_close [NeZero N] [Finite (LatticeSite N κ)] {δ : ℝ}
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (θ : LatticeSite N κ → ℝ)
    (hθ : ∀ y μ, |θ (y + unitStep N κ μ) - θ y| ≤ δ * latticeSpacing N) {r : ℕ}
    (F : LatticeTensor N κ (r + 1)) :
    fieldNorm (weightConj θ .fine .fine (tensorGradAdjoint (r := r)) F - tensorGradAdjoint F) ≤
      2 * ((d : ℝ) + 1) * δ * fieldNorm F := by
  let _ : Fintype (LatticeSite N κ) := Fintype.ofFinite _
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  refine fieldNorm_le_of_sum_sq_le (by positivity) ?_
  have hS : 0 ≤ ∑ x, ∑ j, F x j ^ 2 :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hback : ∀ (x : LatticeSite N κ) (μ : Fin d),
      |(latticeSpacing N)⁻¹ * (Real.exp (θ (x - unitStep N κ μ) - θ x) - 1)| ≤ 2 * δ := by
    intro x μ
    refine abs_inv_spacing_mul_exp_sub_one_le hδ hδ1 ?_
    have h := hθ (x - unitStep N κ μ) μ
    rw [sub_add_cancel, abs_sub_comm] at h
    exact h
  calc ∑ x, ∑ i,
        (weightConj θ .fine .fine (tensorGradAdjoint (r := r)) F - tensorGradAdjoint F) x i ^ 2
      ≤ ∑ x, ∑ i : Fin r → Fin d, (d : ℝ) * ∑ μ,
          (2 * δ) ^ 2 * F (x - unitStep N κ μ) (Fin.cons μ i) ^ 2 := by
        refine Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun i _ => ?_
        rw [weightConj_tensorGradAdjoint_sub_apply]
        refine sq_sum_le_card_mul_sum_sq.trans ?_
        simp only [Finset.card_univ, Fintype.card_fin]
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun μ _ => ?_) hd
        exact mul_sq_le_of_abs_le (hback x μ)
    _ = ((d : ℝ) * (2 * δ) ^ 2) *
          ∑ x, ∑ i : Fin r → Fin d, ∑ μ, F (x - unitStep N κ μ) (Fin.cons μ i) ^ 2 := by
        simp only [Finset.mul_sum]
        refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun i _ =>
          Finset.sum_congr rfl fun μ _ => ?_
        ring
    _ = ((d : ℝ) * (2 * δ) ^ 2) * ∑ x, ∑ j, F x j ^ 2 := by rw [sum_sq_shift_backward]
    _ ≤ _ := mul_le_mul_of_nonneg_right (natCast_mul_sq_le d δ) hS
theorem latticeGrad_eq_tensorGrad :
    (latticeGrad : ScalarField N κ → LatticeOneForm N κ) = tensorGrad (r := 0) := by
  funext g x i
  show forwardDiff (i 0) g x scalarIndex = forwardDiff (i 0) g x (Fin.tail i)
  rw [Subsingleton.elim (Fin.tail i) scalarIndex]
theorem latticeDiv_eq_tensorGradAdjoint :
    (latticeDiv : LatticeOneForm N κ → ScalarField N κ) = tensorGradAdjoint (r := 0) := by
  funext A x i
  show ∑ μ, backwardDiff μ A x (directionIndex μ) = ∑ μ, backwardDiff μ A x (Fin.cons μ i)
  refine Finset.sum_congr rfl fun μ _ => ?_
  congr 1
  funext j
  rw [Subsingleton.elim j 0]
  rfl
end WeightConjugation
open WeightConjugation in
theorem ConjugatedDifferenceBound.claim_holds : ConjugatedDifferenceBound.Claim := by
  intro P ℓ hℓ δ θ hδ hθ
  have := torus_finite (N := P.N) ℓ hℓ
  have hδ0 : 0 ≤ δ := hθ.pos.le
  have hδ1 : δ ≤ 1 := by
    refine hδ.trans ?_
    rw [div_le_one (by positivity)]
    linarith
  have hstep : ∀ y μ, |θ (y + unitStep P.N (LatticeShape.torus ℓ hℓ) μ) - θ y| ≤
      δ * latticeSpacing P.N := fun y μ =>
    (hθ.lip _ _).trans (mul_le_mul_of_nonneg_left (siteDist_add_unitStep_le y μ) hδ0)
  refine ⟨fun f => ?_, fun A => ?_, fun r F => ?_, fun r F => ?_⟩
  · rw [latticeGrad_eq_tensorGrad]
    exact weightConj_tensorGrad_close hδ0 hδ1 θ hstep f
  · rw [latticeDiv_eq_tensorGradAdjoint]
    exact weightConj_tensorGradAdjoint_close hδ0 hδ1 θ hstep A
  · exact weightConj_tensorGrad_close hδ0 hδ1 θ hstep F
  · exact weightConj_tensorGradAdjoint_close hδ0 hδ1 θ hstep F
end YangMills.Construction.LatticeFields
