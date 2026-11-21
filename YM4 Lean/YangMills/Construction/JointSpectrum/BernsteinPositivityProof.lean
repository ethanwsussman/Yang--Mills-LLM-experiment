import YangMills.Construction.HilbertSpace.CommutingPositiveProduct
import YangMills.Construction.JointSpectrum.BernsteinPositivity
import Mathlib
set_option autoImplicit false
open Filter Topology MvPolynomial
open scoped InnerProductSpace ComplexOrder
noncomputable section
namespace YangMills.Construction
open HilbertSpaceBasics OperatorPolynomials
namespace BernsteinPositivity
private def stirlingSecond : ℕ → ℕ → ℝ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 0
  | a + 1, j + 1 => stirlingSecond a j + (j + 1) * stirlingSecond a (j + 1)
private lemma stirlingSecond_eq_zero_of_lt : ∀ (a j : ℕ), a < j → stirlingSecond a j = 0
  | 0, 0, h => absurd h (lt_irrefl 0)
  | 0, _ + 1, _ => rfl
  | _ + 1, 0, h => absurd h (Nat.not_lt_zero _)
  | a + 1, j + 1, h => by
      have hlt : a < j := Nat.lt_of_succ_lt_succ h
      have hlt' : a < j + 1 := by omega
      simp [stirlingSecond, stirlingSecond_eq_zero_of_lt a j hlt,
        stirlingSecond_eq_zero_of_lt a (j + 1) hlt']
private lemma stirlingSecond_self : ∀ a : ℕ, stirlingSecond a a = 1
  | 0 => rfl
  | a + 1 => by
      simp [stirlingSecond, stirlingSecond_self a,
        stirlingSecond_eq_zero_of_lt a (a + 1) (Nat.lt_succ_self a)]
private lemma natCast_mul_descFactorial (k j : ℕ) :
    (k : ℝ) * (k.descFactorial j : ℝ) =
      (k.descFactorial (j + 1) : ℝ) + (j : ℝ) * (k.descFactorial j : ℝ) := by
  rcases le_or_gt j k with h | h
  · rw [Nat.descFactorial_succ, Nat.cast_mul, Nat.cast_sub h]
    ring
  · rw [Nat.descFactorial_eq_zero_iff_lt.2 h,
      Nat.descFactorial_eq_zero_iff_lt.2 (show k < j + 1 by omega)]
    simp
private lemma pow_eq_sum_stirlingSecond_mul_descFactorial (k a : ℕ) :
    (k : ℝ) ^ a =
      ∑ j ∈ Finset.range (a + 1), stirlingSecond a j * (k.descFactorial j : ℝ) := by
  induction a with
  | zero => simp [stirlingSecond]
  | succ a ih =>
    have hshift : ∑ j ∈ Finset.range (a + 1),
        ((j + 1 : ℕ) : ℝ) * stirlingSecond a (j + 1) * (k.descFactorial (j + 1) : ℝ) =
        ∑ j ∈ Finset.range (a + 1), (j : ℝ) * stirlingSecond a j * (k.descFactorial j : ℝ) := by
      have e1 := Finset.sum_range_succ'
        (fun j : ℕ => (j : ℝ) * stirlingSecond a j * (k.descFactorial j : ℝ)) (a + 1)
      have e2 := Finset.sum_range_succ
        (fun j : ℕ => (j : ℝ) * stirlingSecond a j * (k.descFactorial j : ℝ)) (a + 1)
      have e3 : stirlingSecond a (a + 1) = 0 :=
        stirlingSecond_eq_zero_of_lt a (a + 1) (Nat.lt_succ_self a)
      simp only [e3, Nat.cast_zero, zero_mul, mul_zero, add_zero] at e1 e2
      exact e1.symm.trans e2
    rw [Finset.sum_range_succ', pow_succ, ih, Finset.sum_mul]
    simp only [stirlingSecond, zero_mul, add_zero]
    have hterm : ∀ j : ℕ, (stirlingSecond a j + ((j : ℝ) + 1) * stirlingSecond a (j + 1)) *
        (k.descFactorial (j + 1) : ℝ) =
        stirlingSecond a j * (k.descFactorial (j + 1) : ℝ) +
          ((j + 1 : ℕ) : ℝ) * stirlingSecond a (j + 1) * (k.descFactorial (j + 1) : ℝ) := by
      intro j
      push_cast
      ring
    simp only [hterm]
    rw [Finset.sum_add_distrib, hshift, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    have := natCast_mul_descFactorial k j
    linear_combination stirlingSecond a j * this
private lemma sum_descFactorial_mul_bernsteinBasis {R : Type*} [CommRing R] (x : R) (j : ℕ) :
    ∀ r : ℕ, ∑ k ∈ Finset.range (r + 1),
      (k.descFactorial j : R) * ((r.choose k : R) * x ^ k * (1 - x) ^ (r - k)) =
        (r.descFactorial j : R) * x ^ j := by
  induction j with
  | zero =>
    intro r
    have h := add_pow x (1 - x) r
    simp only [add_sub_cancel, one_pow] at h
    simp only [Nat.descFactorial_zero, Nat.cast_one, one_mul, pow_zero, mul_one]
    refine Eq.trans ?_ h.symm
    exact Finset.sum_congr rfl fun k _ => by ring
  | succ j ih =>
    intro r
    cases r with
    | zero => simp
    | succ r =>
      rw [Finset.sum_range_succ']
      simp only [Nat.zero_descFactorial_succ, Nat.cast_zero, zero_mul, add_zero]
      have hterm : ∀ k : ℕ, (((k + 1).descFactorial (j + 1) : ℕ) : R) *
          (((r + 1).choose (k + 1) : R) * x ^ (k + 1) * (1 - x) ^ (r + 1 - (k + 1))) =
          ((r + 1 : ℕ) : R) * x *
            ((k.descFactorial j : R) * ((r.choose k : R) * x ^ k * (1 - x) ^ (r - k))) := by
        intro k
        have h1 : (((k + 1).descFactorial (j + 1) : ℕ) : R) =
            ((k + 1 : ℕ) : R) * (k.descFactorial j : R) := by
          rw [Nat.succ_descFactorial_succ, Nat.cast_mul]
        have h2 : ((r + 1 : ℕ) : R) * (r.choose k : R) =
            ((r + 1).choose (k + 1) : R) * ((k + 1 : ℕ) : R) := by
          rw [← Nat.cast_mul, ← Nat.cast_mul, Nat.add_one_mul_choose_eq]
        rw [h1, Nat.add_sub_add_right]
        linear_combination (-(k.descFactorial j : R) * x ^ (k + 1) * (1 - x) ^ (r - k)) * h2
      simp only [hterm]
      rw [← Finset.mul_sum, ih r, Nat.succ_descFactorial_succ, Nat.cast_mul]
      ring
private def bernsteinPowCoeff (r a j : ℕ) : ℝ :=
  stirlingSecond a j * (r.descFactorial j : ℝ) / (r : ℝ) ^ a
private lemma sum_bernsteinBasis_pow {n : ℕ} (x : MvPolynomial (Fin n) ℝ) (a : ℕ) {r : ℕ} :
    ∑ k ∈ Finset.range (r + 1), C (((k : ℝ) / (r : ℝ)) ^ a) *
        (C ((r.choose k : ℕ) : ℝ) * x ^ k * (1 - x) ^ (r - k)) =
      ∑ j ∈ Finset.range (a + 1), C (bernsteinPowCoeff r a j) * x ^ j := by
  have hk : ∀ k : ℕ, C (((k : ℝ) / (r : ℝ)) ^ a) =
      ∑ j ∈ Finset.range (a + 1),
        (C (stirlingSecond a j / (r : ℝ) ^ a) : MvPolynomial (Fin n) ℝ) *
        (k.descFactorial j : MvPolynomial (Fin n) ℝ) := by
    intro k
    rw [div_pow, pow_eq_sum_stirlingSecond_mul_descFactorial k a, Finset.sum_div, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← map_natCast (C : ℝ →+* MvPolynomial (Fin n) ℝ), ← map_mul]
    congr 1
    ring
  simp only [hk, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h := sum_descFactorial_mul_bernsteinBasis x j r
  simp only [mul_assoc, ← Finset.mul_sum]
  have h' : ∑ k ∈ Finset.range (r + 1), (k.descFactorial j : MvPolynomial (Fin n) ℝ) *
      (C ((r.choose k : ℕ) : ℝ) * (x ^ k * (1 - x) ^ (r - k))) =
      (r.descFactorial j : MvPolynomial (Fin n) ℝ) * x ^ j := by
    rw [← h]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_natCast, mul_assoc]
  rw [h', ← mul_assoc, ← map_natCast (C : ℝ →+* MvPolynomial (Fin n) ℝ), ← map_mul]
  congr 2
  unfold bernsteinPowCoeff
  ring
private lemma tendsto_bernsteinPowCoeff_nat (a j : ℕ) (hj : j ≤ a) :
    Tendsto (fun r : ℕ => bernsteinPowCoeff r a j) atTop (𝓝 (if j = a then 1 else 0)) := by
  have h1 : Tendsto (fun r : ℕ => (r.descFactorial j : ℝ) / (r : ℝ) ^ j) atTop (𝓝 1) := by
    have hz : ∀ᶠ r : ℕ in atTop, ((r : ℝ) ^ j) ≠ 0 := by
      filter_upwards [eventually_gt_atTop 0] with r hr
      positivity
    exact (Asymptotics.isEquivalent_iff_tendsto_one hz).1 (isEquivalent_descFactorial j)
  have h2 : Tendsto (fun r : ℕ => stirlingSecond a j * ((r.descFactorial j : ℝ) / (r : ℝ) ^ j) *
      ((r : ℝ) ^ (a - j))⁻¹) atTop (𝓝 (if j = a then 1 else 0)) := by
    rcases eq_or_lt_of_le hj with rfl | hlt
    · simpa [stirlingSecond_self] using h1
    · have h3 : Tendsto (fun r : ℕ => ((r : ℝ) ^ (a - j))⁻¹) atTop (𝓝 0) :=
        ((tendsto_pow_atTop (by omega)).comp tendsto_natCast_atTop_atTop).inv_tendsto_atTop
      have := (h1.const_mul (stirlingSecond a j)).mul h3
      simpa [hlt.ne] using this
  refine h2.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with r hr
  unfold bernsteinPowCoeff
  have : (r : ℝ) ^ a = (r : ℝ) ^ j * (r : ℝ) ^ (a - j) := by
    rw [← pow_add, Nat.add_sub_cancel' hj]
  rw [this]
  field_simp
private lemma tendsto_bernsteinPowCoeff (a j : ℕ) (hj : j ≤ a) :
    Tendsto (fun r : ℕ+ => bernsteinPowCoeff (r : ℕ) a j) atTop
      (𝓝 (if j = a then 1 else 0)) := by
  have hcoe : Tendsto (fun r : ℕ+ => (r : ℕ)) atTop atTop :=
    Monotone.tendsto_atTop_atTop (fun _ _ h => h) fun b => ⟨b.succPNat, by simp⟩
  exact (tendsto_bernsteinPowCoeff_nat a j hj).comp hcoe
variable {n : ℕ} [NeZero n]
private lemma bernsteinApprox_monomial (r : ℕ+) (α : Fin n →₀ ℕ) :
    bernsteinApprox r (monomial α (1 : ℝ)) =
      ∑ β ∈ Fintype.piFinset (fun i => Finset.range (α i + 1)),
        monomial (Finsupp.equivFunOnFinite.symm β) (∏ i, bernsteinPowCoeff r (α i) (β i)) := by
  unfold OperatorPolynomials.bernsteinApprox
  have hterm : ∀ k : Fin n → ℕ,
      C (eval (fun i => (k i : ℝ) / ((r : ℕ) : ℝ)) (monomial α (1 : ℝ))) *
        ∏ i, (C (((r : ℕ).choose (k i) : ℕ) : ℝ) * X i ^ k i * (1 - X i) ^ ((r : ℕ) - k i)) =
      ∏ i, (C (((k i : ℝ) / ((r : ℕ) : ℝ)) ^ α i) *
        (C (((r : ℕ).choose (k i) : ℕ) : ℝ) * X i ^ k i * (1 - X i) ^ ((r : ℕ) - k i))) := by
    intro k
    rw [eval_monomial, Finsupp.prod_fintype _ _ (by simp), one_mul, map_prod,
      ← Finset.prod_mul_distrib]
  simp only [hterm]
  rw [← Finset.prod_univ_sum (fun _ : Fin n => Finset.range ((r : ℕ) + 1))
    (fun i j => C (((j : ℝ) / ((r : ℕ) : ℝ)) ^ α i) *
      (C (((r : ℕ).choose j : ℕ) : ℝ) * X i ^ j * (1 - X i) ^ ((r : ℕ) - j)))]
  simp only [sum_bernsteinBasis_pow]
  rw [Finset.prod_univ_sum]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [monomial_eq, Finsupp.prod_fintype _ _ (by simp), map_prod, ← Finset.prod_mul_distrib]
  simp
private lemma coeff_bernsteinApprox_monomial (r : ℕ+) (α γ : Fin n →₀ ℕ) :
    coeff γ (bernsteinApprox r (monomial α (1 : ℝ))) =
      if ∀ i, γ i ≤ α i then ∏ i, bernsteinPowCoeff r (α i) (γ i) else 0 := by
  rw [bernsteinApprox_monomial, coeff_sum]
  simp only [coeff_monomial]
  have hiff : ∀ β : Fin n → ℕ, Finsupp.equivFunOnFinite.symm β = γ ↔ β = ⇑γ := by
    intro β
    rw [Equiv.symm_apply_eq]
    rfl
  simp only [hiff]
  rw [Finset.sum_ite_eq']
  simp only [Fintype.mem_piFinset, Finset.mem_range, Nat.lt_succ_iff]
private lemma tendsto_coeff_bernsteinApprox_monomial (α γ : Fin n →₀ ℕ) :
    Tendsto (fun r : ℕ+ => coeff γ (bernsteinApprox r (monomial α (1 : ℝ)))) atTop
      (𝓝 (if α = γ then 1 else 0)) := by
  simp only [coeff_bernsteinApprox_monomial]
  by_cases h : ∀ i, γ i ≤ α i
  · simp only [h, implies_true, if_true]
    have hlim := tendsto_finsetProd (Finset.univ : Finset (Fin n))
      (fun i _ => tendsto_bernsteinPowCoeff (α i) (γ i) (h i))
    convert hlim using 2
    by_cases hαγ : α = γ
    · subst hαγ
      simp
    · obtain ⟨i, hi⟩ : ∃ i, α i ≠ γ i := by
        by_contra hne
        exact hαγ (Finsupp.ext (by simpa using hne))
      rw [if_neg hαγ]
      exact (Finset.prod_eq_zero (Finset.mem_univ i) (if_neg (Ne.symm hi))).symm
  · have hne : α ≠ γ := by
      rintro rfl
      exact h fun _ => le_rfl
    simp only [h, if_false, hne]
    exact tendsto_const_nhds
private lemma bernsteinApprox_finsetMvSum (r : ℕ+) (𝒜 : Finset (Fin n →₀ ℕ))
    (c : (Fin n →₀ ℕ) → ℝ) :
    bernsteinApprox r (finsetMvSum 𝒜 c) =
      ∑ α ∈ 𝒜, C (c α) * bernsteinApprox r (monomial α (1 : ℝ)) := by
  unfold OperatorPolynomials.bernsteinApprox finsetMvSum
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [← mul_assoc, ← map_mul]
  congr 2
  rw [eval_monomial, eval_monomial, one_mul]
private lemma exists_bernsteinApprox_coeffs (p : RealMvPolynomial n) (𝒜 : Finset (Fin n →₀ ℕ))
    (c : (Fin n →₀ ℕ) → ℝ) (hp : p = finsetMvSum 𝒜 c) (h𝒜 : IsDownwardClosed 𝒜) :
    ∃ cr : ℕ+ → (Fin n →₀ ℕ) → ℝ,
      (∀ r, bernsteinApprox r p = finsetMvSum 𝒜 (cr r)) ∧
        ∀ α ∈ 𝒜, Tendsto (fun r => cr r α) atTop (𝓝 (c α)) := by
  have hcoeff : ∀ (r : ℕ+) (γ : Fin n →₀ ℕ), coeff γ (bernsteinApprox r p) =
      ∑ α ∈ 𝒜, c α * coeff γ (bernsteinApprox r (monomial α (1 : ℝ))) := by
    intro r γ
    rw [hp, bernsteinApprox_finsetMvSum, coeff_sum]
    simp only [coeff_C_mul]
  refine ⟨fun r γ => coeff γ (bernsteinApprox r p), fun r => ?_, fun γ hγ => ?_⟩
  · ext γ
    unfold finsetMvSum
    rw [coeff_sum]
    simp only [coeff_monomial]
    rw [Finset.sum_ite_eq']
    split_ifs with hγ
    · rfl
    · rw [hcoeff]
      refine Finset.sum_eq_zero fun α hα => ?_
      rw [coeff_bernsteinApprox_monomial, if_neg, mul_zero]
      exact fun hle => hγ (h𝒜 α hα γ hle)
  · simp only [hcoeff]
    have hlim := tendsto_finsetSum 𝒜 (fun α _ =>
      (tendsto_coeff_bernsteinApprox_monomial α γ).const_mul (c α))
    convert hlim using 2
    simp [Finset.sum_ite_eq', hγ]
section Operators
variable {ℋ : Type} [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]
open scoped IsMulCommutative in
private lemma exists_evalAlgHom (A : Fin n → ℋ →L[ℂ] ℋ) (hA : PairwiseCommute A) :
    ∃ φ : RealMvPolynomial n →ₐ[ℝ] (ℋ →L[ℂ] ℋ),
      (∀ i, φ (X i) = A i) ∧ ∀ p, φ p = evalOperators p A hA := by
  have hc : ∀ a ∈ Set.range A, ∀ b ∈ Set.range A, a * b = b * a := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    exact hA i j
  haveI := Algebra.isMulCommutative_adjoin ℝ hc
  letI : CommRing (Algebra.adjoin ℝ (Set.range A)) := inferInstance
  let a : Fin n → Algebra.adjoin ℝ (Set.range A) := fun i =>
    ⟨A i, Algebra.subset_adjoin ⟨i, rfl⟩⟩
  refine ⟨(Algebra.adjoin ℝ (Set.range A)).val.comp (aeval a), fun i => by simp [a], fun p => ?_⟩
  have hpow : ∀ α : Fin n →₀ ℕ,
      ((∏ i, a i ^ α i : Algebra.adjoin ℝ (Set.range A)) : ℋ →L[ℂ] ℋ) = orderedMonomial A α := by
    intro α
    unfold orderedMonomial
    rw [← Fin.prod_ofFn]
    simp [a, map_list_prod]
    rfl
  simp only [AlgHom.comp_apply, aeval_def, eval₂_eq']
  unfold evalOperators
  rw [map_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [map_mul, AlgHom.commutes]
  simp [hpow, Algebra.smul_def]
private def evalAlgHom (A : Fin n → ℋ →L[ℂ] ℋ) (hA : PairwiseCommute A) :
    RealMvPolynomial n →ₐ[ℝ] (ℋ →L[ℂ] ℋ) :=
  Classical.choose (exists_evalAlgHom A hA)
private lemma evalAlgHom_X (A : Fin n → ℋ →L[ℂ] ℋ) (hA : PairwiseCommute A) (i : Fin n) :
    evalAlgHom A hA (X i) = A i :=
  (Classical.choose_spec (exists_evalAlgHom A hA)).1 i
private lemma evalAlgHom_apply (A : Fin n → ℋ →L[ℂ] ℋ) (hA : PairwiseCommute A)
    (p : RealMvPolynomial n) : evalAlgHom A hA p = evalOperators p A hA :=
  (Classical.choose_spec (exists_evalAlgHom A hA)).2 p
private lemma evalAlgHom_C (A : Fin n → ℋ →L[ℂ] ℋ) (hA : PairwiseCommute A) (t : ℝ) :
    evalAlgHom A hA (C t) = (t : ℂ) • 1 := by
  have h : evalAlgHom A hA (C t) = algebraMap ℝ (ℋ →L[ℂ] ℋ) t := (evalAlgHom A hA).commutes t
  rw [h, Algebra.algebraMap_eq_smul_one]
  ext x
  simp
private lemma evalAlgHom_commute (A : Fin n → ℋ →L[ℂ] ℋ) (hA : PairwiseCommute A)
    (p q : RealMvPolynomial n) : Commute (evalAlgHom A hA p) (evalAlgHom A hA q) := by
  change evalAlgHom A hA p * evalAlgHom A hA q = evalAlgHom A hA q * evalAlgHom A hA p
  rw [← map_mul, ← map_mul, mul_comm]
private lemma isSelfAdjoint_ofReal_smul {t : ℝ} {S : ℋ →L[ℂ] ℋ} (hS : IsSelfAdjoint S) :
    IsSelfAdjoint ((t : ℂ) • S) := by
  rw [isSelfAdjoint_iff, star_smul, hS.star_eq]
  simp
private lemma isPositiveOp_ofReal_smul {t : ℝ} (ht : 0 ≤ t) {S : ℋ →L[ℂ] ℋ}
    (hS : IsPositiveOp S) : IsPositiveOp ((t : ℂ) • S) := by
  refine ⟨isSelfAdjoint_ofReal_smul hS.1, fun ψ => ?_⟩
  simp only [ContinuousLinearMap.smul_apply, inner_smul_right]
  exact mul_nonneg (Complex.zero_le_real.2 ht) (hS.2 ψ)
private lemma isPositiveOp_add {S T : ℋ →L[ℂ] ℋ} (hS : IsPositiveOp S) (hT : IsPositiveOp T) :
    IsPositiveOp (S + T) := by
  refine ⟨hS.1.add hT.1, fun ψ => ?_⟩
  simpa [inner_add_right] using add_nonneg (hS.2 ψ) (hT.2 ψ)
private lemma isPositiveOp_zero : IsPositiveOp (0 : ℋ →L[ℂ] ℋ) :=
  ⟨IsSelfAdjoint.zero _, fun ψ => by simp⟩
private lemma isPositiveOp_one : IsPositiveOp (1 : ℋ →L[ℂ] ℋ) := by
  refine ⟨IsSelfAdjoint.one _, fun ψ => ?_⟩
  have h : ⟪ψ, ψ⟫_ℂ = ((‖ψ‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]
    simp
  rw [ContinuousLinearMap.one_apply, h]
  exact Complex.zero_le_real.2 (sq_nonneg _)
private lemma isPositiveOp_mul (hP : PositiveOperators.CommutingPositiveProduct)
    {S T : ℋ →L[ℂ] ℋ} (hST : Commute S T) (hS : IsPositiveOp S) (hT : IsPositiveOp T) :
    IsPositiveOp (S * T) := by
  have h := hP ℋ 2 (by norm_num) ![S, T] ?_ ?_
  · simpa using h
  · intro i j hij
    fin_cases i <;> fin_cases j <;> first | exact absurd rfl hij | exact hST | exact hST.symm
  · intro i
    fin_cases i
    · exact hS
    · exact hT
private lemma isSelfAdjoint_evalOperators (A : Fin n → ℋ →L[ℂ] ℋ) (hA : PairwiseCommute A)
    (hs : ∀ i, IsSelfAdjoint (A i)) (p : RealMvPolynomial n) :
    IsSelfAdjoint (evalOperators p A hA) := by
  rw [← evalAlgHom_apply]
  induction p using MvPolynomial.induction_on with
  | C t =>
    rw [evalAlgHom_C]
    exact isSelfAdjoint_ofReal_smul (IsSelfAdjoint.one _)
  | add p q hp hq =>
    rw [map_add]
    exact hp.add hq
  | mul_X p i hp =>
    have hc := evalAlgHom_commute A hA p (X i)
    rw [map_mul, isSelfAdjoint_iff, star_mul, evalAlgHom_X, (hs i).star_eq, hp.star_eq]
    rw [evalAlgHom_X] at hc
    exact hc.symm.eq
private lemma exists_isDownwardClosed_support (p : RealMvPolynomial n) :
    ∃ 𝒜 : Finset (Fin n →₀ ℕ),
      p = finsetMvSum 𝒜 (fun α => coeff α p) ∧ IsDownwardClosed 𝒜 := by
  classical
  refine ⟨p.support.biUnion fun α => Finset.Icc 0 α, ?_, ?_⟩
  · ext γ
    unfold finsetMvSum
    rw [coeff_sum]
    simp only [coeff_monomial]
    rw [Finset.sum_ite_eq']
    split_ifs with hγ
    · rfl
    · by_contra hne
      exact hγ (Finset.mem_biUnion.2 ⟨γ, mem_support_iff.2 hne, by simp⟩)
  · intro α hα α' hle
    obtain ⟨β, hβ, hαβ⟩ := Finset.mem_biUnion.1 hα
    refine Finset.mem_biUnion.2 ⟨β, hβ, ?_⟩
    have h2 := (Finset.mem_Icc.1 hαβ).2
    exact Finset.mem_Icc.2 ⟨fun i => Nat.zero_le _, fun i => (hle i).trans (h2 i)⟩
private lemma isPositiveOp_of_nonneg_on_unitCube (hP : PositiveOperators.CommutingPositiveProduct)
    (A : Fin n → ℋ →L[ℂ] ℋ) (hA : PairwiseCommute A) (h0 : ∀ i, IsPositiveOp (A i))
    (h1 : ∀ i, IsPositiveOp (1 - A i)) (p : RealMvPolynomial n)
    (hp : ∀ y : Fin n → ℝ, (∀ i, 0 ≤ y i ∧ y i ≤ 1) → 0 ≤ eval y p) :
    IsPositiveOp (evalOperators p A hA) := by
  set φ := evalAlgHom A hA with hφ
  have hmul : ∀ q q' : RealMvPolynomial n, IsPositiveOp (φ q) → IsPositiveOp (φ q') →
      IsPositiveOp (φ (q * q')) := by
    intro q q' hq hq'
    rw [map_mul]
    exact isPositiveOp_mul hP (evalAlgHom_commute A hA q q') hq hq'
  have hone : IsPositiveOp (φ 1) := by
    rw [map_one]
    exact isPositiveOp_one
  have hpow : ∀ (q : RealMvPolynomial n) (k : ℕ), IsPositiveOp (φ q) →
      IsPositiveOp (φ (q ^ k)) := by
    intro q k hq
    induction k with
    | zero => simpa using hone
    | succ k ih =>
      rw [pow_succ]
      exact hmul _ _ ih hq
  have hprod : ∀ f : Fin n → RealMvPolynomial n, (∀ i, IsPositiveOp (φ (f i))) →
      IsPositiveOp (φ (∏ i, f i)) := fun f hf =>
    Finset.prod_induction f (fun q => IsPositiveOp (φ q)) hmul hone fun i _ => hf i
  have hC : ∀ t : ℝ, 0 ≤ t → IsPositiveOp (φ (C t)) := by
    intro t ht
    rw [hφ, evalAlgHom_C]
    exact isPositiveOp_ofReal_smul ht isPositiveOp_one
  have hX : ∀ i, IsPositiveOp (φ (X i)) := by
    intro i
    rw [hφ, evalAlgHom_X]
    exact h0 i
  have hY : ∀ i, IsPositiveOp (φ (1 - X i)) := by
    intro i
    rw [map_sub, map_one, hφ, evalAlgHom_X]
    exact h1 i
  have hB : ∀ r : ℕ+, IsPositiveOp (φ (OperatorPolynomials.bernsteinApprox r p)) := by
    intro r
    unfold OperatorPolynomials.bernsteinApprox
    rw [map_sum]
    refine Finset.sum_induction _ IsPositiveOp (fun _ _ => isPositiveOp_add) isPositiveOp_zero ?_
    intro k hk
    refine hmul _ _ (hC _ (hp _ fun i => ?_)) (hprod _ fun i =>
      hmul _ _ (hmul _ _ (hC _ (by positivity)) (hpow _ _ (hX i))) (hpow _ _ (hY i)))
    have hki : k i ≤ (r : ℕ) := by
      have := Fintype.mem_piFinset.1 hk i
      simpa [Nat.lt_succ_iff] using this
    have hr : (0 : ℝ) < ((r : ℕ) : ℝ) := by exact_mod_cast r.pos
    exact ⟨by positivity, (div_le_one hr).2 (by exact_mod_cast hki)⟩
  obtain ⟨𝒜, hsum, hlow⟩ := exists_isDownwardClosed_support p
  obtain ⟨cr, hcr, hlim⟩ := exists_bernsteinApprox_coeffs p 𝒜 _ hsum hlow
  have hexp : ∀ d : (Fin n →₀ ℕ) → ℝ, φ (finsetMvSum 𝒜 d) =
      ∑ α ∈ 𝒜, d α • φ (monomial α (1 : ℝ)) := by
    intro d
    unfold finsetMvSum
    rw [map_sum]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [← map_smul, smul_monomial, smul_eq_mul, mul_one]
  have hten : Tendsto (fun r : ℕ+ => φ (OperatorPolynomials.bernsteinApprox r p)) atTop
      (𝓝 (φ p)) := by
    simp only [hcr]
    conv => arg 3; rw [hsum]
    simp only [hexp]
    exact tendsto_finsetSum 𝒜 fun α hα => (hlim α hα).smul_const _
  rw [← evalAlgHom_apply]
  refine ⟨?_, fun ψ => ?_⟩
  · rw [evalAlgHom_apply]
    exact isSelfAdjoint_evalOperators A hA (fun i => (h0 i).1) p
  · have hcont : Continuous fun T : ℋ →L[ℂ] ℋ => ⟪ψ, T ψ⟫_ℂ :=
      continuous_const.inner (ContinuousLinearMap.apply ℂ ℋ ψ).continuous
    exact ge_of_tendsto' ((hcont.tendsto _).comp hten) fun r => (hB r).2 ψ
private lemma isPositiveOp_of_nonneg_on_coordBox
    (hP : PositiveOperators.CommutingPositiveProduct)
    (A : Fin n → ℋ →L[ℂ] ℋ) (hA : PairwiseCommute A) (γ γ' : Fin n → ℝ)
    (hb : SpectrallyBetween A γ γ') (p : RealMvPolynomial n)
    (hp : ∀ y ∈ coordBox γ γ', 0 ≤ eval y p) :
    IsPositiveOp (evalOperators p A hA) := by
  have hd : ∀ i, 0 < γ' i - γ i := fun i => sub_pos.2 (hb i).2.1
  let A' : Fin n → ℋ →L[ℂ] ℋ := fun i =>
    (((γ' i - γ i)⁻¹ : ℝ) : ℂ) • (A i - (γ i : ℂ) • 1)
  have hA' : PairwiseCommute A' := by
    intro i j
    refine Commute.smul_left (Commute.smul_right ?_ _) _
    exact Commute.sub_left
      (Commute.sub_right (hA i j) ((Commute.one_right _).smul_right _))
      (Commute.sub_right ((Commute.one_left _).smul_left _)
        ((Commute.one_left _).smul_right _ |>.smul_left _))
  have h0 : ∀ i, IsPositiveOp (A' i) := fun i =>
    isPositiveOp_ofReal_smul (inv_nonneg.2 (hd i).le) (hb i).2.2.1.2.2
  have h1 : ∀ i, IsPositiveOp (1 - A' i) := by
    intro i
    have hne : ((γ' i : ℂ) - (γ i : ℂ)) ≠ 0 := by
      exact_mod_cast (hd i).ne'
    have e : 1 - A' i = (((γ' i - γ i)⁻¹ : ℝ) : ℂ) • ((γ' i : ℂ) • 1 - A i) := by
      simp only [A']
      push_cast
      match_scalars <;> field_simp <;> ring
    rw [e]
    exact isPositiveOp_ofReal_smul (inv_nonneg.2 (hd i).le) (hb i).2.2.2.2.2
  let g : Fin n → RealMvPolynomial n := fun i => C (γ i) + C (γ' i - γ i) * X i
  have hcomp : (evalAlgHom A' hA').comp (aeval g) = evalAlgHom A hA := by
    refine MvPolynomial.algHom_ext fun i => ?_
    have hne : ((γ' i : ℂ) - (γ i : ℂ)) ≠ 0 := by
      exact_mod_cast (hd i).ne'
    simp only [AlgHom.comp_apply, aeval_X, g, map_add, map_mul, evalAlgHom_C, evalAlgHom_X, A',
      smul_mul_assoc, one_mul]
    push_cast
    match_scalars <;> field_simp <;> ring
  have hvals : ∀ (y : Fin n → ℝ) (q : RealMvPolynomial n),
      eval y (aeval g q) = eval (fun i => γ i + (γ' i - γ i) * y i) q := by
    intro y q
    induction q using MvPolynomial.induction_on with
    | C t => simp
    | add q q' hq hq' => rw [map_add, map_add, map_add, hq, hq']
    | mul_X q i hq =>
      rw [map_mul, map_mul, map_mul, hq, aeval_X, eval_X]
      congr 1
      simp [g]
  rw [← evalAlgHom_apply, ← hcomp, AlgHom.comp_apply, evalAlgHom_apply]
  refine isPositiveOp_of_nonneg_on_unitCube hP A' hA' h0 h1 _ fun y hy => ?_
  rw [hvals]
  refine hp _ fun i _ => ?_
  have hi := hy i
  have := hd i
  exact ⟨by nlinarith [hi.1], by nlinarith [hi.2]⟩
private lemma norm_inner_evalOperators_le (hP : PositiveOperators.CommutingPositiveProduct)
    (A : Fin n → ℋ →L[ℂ] ℋ) (hA : PairwiseCommute A) (γ γ' : Fin n → ℝ)
    (hb : SpectrallyBetween A γ γ') (p : RealMvPolynomial n) (ψ : ℋ) :
    ‖⟪ψ, evalOperators p A hA ψ⟫_ℂ‖ ≤
      (⨆ y : coordBox γ γ', |eval (y : Fin n → ℝ) p|) * ‖ψ‖ ^ 2 := by
  set c := ⨆ y : coordBox γ γ', |eval (y : Fin n → ℝ) p| with hc
  have hcompact : IsCompact (coordBox γ γ') := isCompact_univ_pi fun _ => isCompact_Icc
  have hcont : Continuous fun y : Fin n → ℝ => |eval y p| := (continuous_eval p).abs
  have hbdd : BddAbove (Set.range fun y : coordBox γ γ' => |eval (y : Fin n → ℝ) p|) := by
    have := (hcompact.image hcont).bddAbove
    rwa [Set.image_eq_range] at this
  have hle : ∀ y ∈ coordBox γ γ', |eval y p| ≤ c := fun y hy =>
    le_ciSup hbdd (⟨y, hy⟩ : coordBox γ γ')
  have hplus := isPositiveOp_of_nonneg_on_coordBox hP A hA γ γ' hb (C c + p) fun y hy => by
    have := abs_le.1 (hle y hy)
    simp only [map_add, eval_C]
    linarith [this.1]
  have hminus := isPositiveOp_of_nonneg_on_coordBox hP A hA γ γ' hb (C c - p) fun y hy => by
    have := abs_le.1 (hle y hy)
    simp only [map_sub, eval_C]
    linarith [this.2]
  rw [← evalAlgHom_apply] at hplus hminus
  rw [map_add, evalAlgHom_C, evalAlgHom_apply] at hplus
  rw [map_sub, evalAlgHom_C, evalAlgHom_apply] at hminus
  have hnorm : ⟪ψ, (((c : ℂ) • 1 : ℋ →L[ℂ] ℋ)) ψ⟫_ℂ = ((c * ‖ψ‖ ^ 2 : ℝ) : ℂ) := by
    simp [inner_self_eq_norm_sq_to_K]
  have e1 := hplus.2 ψ
  have e2 := hminus.2 ψ
  rw [add_apply, inner_add_right, hnorm] at e1
  rw [sub_apply, inner_sub_right, hnorm] at e2
  set z := ⟪ψ, evalOperators p A hA ψ⟫_ℂ with hz
  obtain ⟨a1, b1⟩ := Complex.nonneg_iff.1 e1
  obtain ⟨a2, _⟩ := Complex.nonneg_iff.1 e2
  simp only [Complex.add_re, Complex.sub_re, Complex.ofReal_re, Complex.add_im,
    Complex.ofReal_im, zero_add] at a1 a2 b1
  have hzr : z = (z.re : ℂ) := Complex.ext rfl (by simpa using b1.symm)
  rw [hzr, Complex.norm_real, Real.norm_eq_abs]
  exact abs_le.2 ⟨by linarith, by linarith⟩
end Operators
theorem bernsteinPositivityStatement_of_commutingPositiveProduct
    (hP : PositiveOperators.CommutingPositiveProduct) : BernsteinPositivityStatement := by
  intro n _
  refine ⟨fun p 𝒜 c hp h𝒜 => ⟨exists_bernsteinApprox_coeffs p 𝒜 c hp h𝒜, ?_⟩, ?_, ?_⟩
  · intro ℋ _ _ _ A hA γ γ' hb hpos
    exact isPositiveOp_of_nonneg_on_coordBox hP A hA γ γ' hb p hpos
  · intro ℋ _ _ _ A hA γ γ' hb p ψ
    exact norm_inner_evalOperators_le hP A hA γ γ' hb p ψ
  · intro ℋ _ _ _ A hA
    refine ⟨⟨fun p q => ?_, fun t p => ?_⟩, fun p q => ?_, fun hs p => ?_⟩
    · simp only [← evalAlgHom_apply, map_add]
    · simp only [← evalAlgHom_apply, map_smul]
    · simp only [← evalAlgHom_apply, map_mul]
    · exact isSelfAdjoint_evalOperators A hA hs p
end BernsteinPositivity
end YangMills.Construction
