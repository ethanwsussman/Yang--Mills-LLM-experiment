import YangMills.Construction.RunningCouplingSlope.LaplaceOfAFamilyOfExponentsProof
import YangMills.Construction.IdentificationOfTheOneLoopNumber.MixedVariationOfALogDeterminant
import YangMills.Construction.RunningCouplingSlope.SecondDerivativeOfALogDeterminant
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YangMills.Construction
open MeasureTheory ColdStepAtMirrorFrames Filter Topology
namespace GaussianMeans
variable {ι : Type} [Fintype ι] [DecidableEq ι]
private def coordFun (p : ι × Fin 3) : BondField ι →L[ℝ] ℝ :=
  (EuclideanSpace.proj p.2 : BondVector →L[ℝ] ℝ).comp (ContinuousLinearMap.proj p.1)
private def fieldOfCoords (x : ι × Fin 3 → ℝ) : BondField ι := fun b => WithLp.toLp 2 fun k => x (b, k)
private lemma coordFun_fieldOfCoords (x : ι × Fin 3 → ℝ) (p : ι × Fin 3) :
    coordFun p (fieldOfCoords x) = x p := rfl
private lemma abs_coordFun_le_norm (p : ι × Fin 3) (η : BondField ι) : |coordFun p η| ≤ ‖η‖ :=
  calc |coordFun p η| = ‖(η p.1) p.2‖ := rfl
    _ ≤ ‖η p.1‖ := PiLp.norm_apply_le _ _
    _ ≤ ‖η‖ := norm_le_pi_norm _ _
private lemma hasFDerivAt_quadraticForm (S : Matrix (ι × Fin 3) (ι × Fin 3) ℝ) (η : BondField ι) :
    HasFDerivAt (quadraticForm S)
      (∑ i, ∑ j, S i j • (coordFun i η • coordFun j + coordFun j η • coordFun i)) η := by
  have h : quadraticForm S = fun η => ∑ i, ∑ j, S i j * (coordFun i η * coordFun j η) := rfl
  rw [h]
  refine HasFDerivAt.fun_sum fun i _ => HasFDerivAt.fun_sum fun j _ => ?_
  exact (((coordFun i).hasFDerivAt).mul ((coordFun j).hasFDerivAt)).const_mul (S i j)
private lemma fderiv_quadraticForm_apply (S : Matrix (ι × Fin 3) (ι × Fin 3) ℝ) (η v : BondField ι) :
    fderiv ℝ (quadraticForm S) η v =
      ∑ i, ∑ j, S i j * (coordFun i η * coordFun j v + coordFun j η * coordFun i v) := by
  rw [(hasFDerivAt_quadraticForm S η).fderiv]
  simp [mul_add]
private def PolyGrowth (f : BondField ι → ℝ) : Prop :=
  Continuous f ∧ ∃ (C : ℝ) (n : ℕ), ∀ η, |f η| ≤ C * (1 + ‖η‖) ^ n
private lemma PolyGrowth.mul {f g : BondField ι → ℝ} (hf : PolyGrowth f) (hg : PolyGrowth g) :
    PolyGrowth (fun η => f η * g η) := by
  obtain ⟨hfc, C, n, hC⟩ := hf
  obtain ⟨hgc, C', n', hC'⟩ := hg
  refine ⟨hfc.mul hgc, C * C', n + n', fun η => ?_⟩
  rw [abs_mul, pow_add]
  calc |f η| * |g η| ≤ (C * (1 + ‖η‖) ^ n) * (C' * (1 + ‖η‖) ^ n') :=
        mul_le_mul (hC η) (hC' η) (abs_nonneg _) ((abs_nonneg _).trans (hC η))
    _ = _ := by ring
private lemma PolyGrowth.add {f g : BondField ι → ℝ} (hf : PolyGrowth f) (hg : PolyGrowth g) :
    PolyGrowth (fun η => f η + g η) := by
  obtain ⟨hfc, C, n, hC⟩ := hf
  obtain ⟨hgc, C', n', hC'⟩ := hg
  refine ⟨hfc.add hgc, |C| + |C'|, n + n', fun η => ?_⟩
  have h1 : (1 : ℝ) ≤ 1 + ‖η‖ := by linarith [norm_nonneg η]
  have hn : (1 + ‖η‖) ^ n ≤ (1 + ‖η‖) ^ (n + n') := pow_le_pow_right₀ h1 (by omega)
  have hn' : (1 + ‖η‖) ^ n' ≤ (1 + ‖η‖) ^ (n + n') := pow_le_pow_right₀ h1 (by omega)
  calc |f η + g η| ≤ |f η| + |g η| := abs_add_le _ _
    _ ≤ C * (1 + ‖η‖) ^ n + C' * (1 + ‖η‖) ^ n' := add_le_add (hC η) (hC' η)
    _ ≤ |C| * (1 + ‖η‖) ^ (n + n') + |C'| * (1 + ‖η‖) ^ (n + n') :=
        add_le_add
          ((mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)).trans
            (mul_le_mul_of_nonneg_left hn (abs_nonneg C)))
          ((mul_le_mul_of_nonneg_right (le_abs_self C') (by positivity)).trans
            (mul_le_mul_of_nonneg_left hn' (abs_nonneg C')))
    _ = _ := by ring
private lemma PolyGrowth.const (a : ℝ) : PolyGrowth (fun _ : BondField ι => a) :=
  ⟨continuous_const, |a|, 0, fun η => by simp⟩
private lemma polyGrowth_coordFun (p : ι × Fin 3) : PolyGrowth (fun η : BondField ι => coordFun p η) :=
  ⟨(coordFun p).continuous, 1, 1, fun η => by
    have := abs_coordFun_le_norm p η
    simp only [one_mul, pow_one]
    linarith⟩
private lemma PolyGrowth.sum {α : Type} (s : Finset α) {f : α → BondField ι → ℝ}
    (h : ∀ a ∈ s, PolyGrowth (f a)) : PolyGrowth (fun η => ∑ a ∈ s, f a η) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using PolyGrowth.const (ι := ι) 0
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add
      (ih fun b hb => h b (Finset.mem_insert_of_mem hb))
private lemma polyGrowth_quadraticForm (S : Matrix (ι × Fin 3) (ι × Fin 3) ℝ) :
    PolyGrowth (quadraticForm S) := by
  have h : quadraticForm S = fun η => ∑ i, ∑ j, S i j * (coordFun i η * coordFun j η) := rfl
  rw [h]
  exact PolyGrowth.sum _ fun i _ => PolyGrowth.sum _ fun j _ =>
    (PolyGrowth.const _).mul ((polyGrowth_coordFun i).mul (polyGrowth_coordFun j))
private lemma one_add_pow_mul_exp_neg_sq_le (N : ℕ) {b s : ℝ} (hb : 0 < b) (hs : 0 ≤ s) :
    (1 + s) ^ N * Real.exp (-(b * s ^ 2)) ≤ Real.exp ((N : ℝ) ^ 2 / (4 * b)) := by
  have h1 : (1 + s) ^ N ≤ Real.exp (N * s) := by
    rw [Real.exp_nat_mul]
    exact pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp s]) N
  calc (1 + s) ^ N * Real.exp (-(b * s ^ 2))
      ≤ Real.exp (N * s) * Real.exp (-(b * s ^ 2)) :=
        mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    _ = Real.exp (N * s - b * s ^ 2) := by rw [← Real.exp_add]; ring_nf
    _ ≤ _ := Real.exp_le_exp.2 (by
      rw [le_div_iff₀ (by positivity)]
      nlinarith [sq_nonneg (2 * b * s - N)])
private lemma norm_sq_le_sum_norm_sq (η : BondField ι) : ‖η‖ ^ 2 ≤ ∑ b, ‖η b‖ ^ 2 := by apply _root_.YangMills.DeltaSharedProofs.p501099 <;> assumption
private def gaussWeight (M : Matrix (ι × Fin 3) (ι × Fin 3) ℝ) (η : BondField ι) : ℝ :=
  Real.exp (-(1 / 2 * quadraticForm M η))
private lemma continuous_gaussWeight (M : Matrix (ι × Fin 3) (ι × Fin 3) ℝ) :
    Continuous (gaussWeight M) :=
  Real.continuous_exp.comp ((continuous_const.mul (polyGrowth_quadraticForm M).1).neg)
private lemma PolyGrowth.integrable {M : Matrix (ι × Fin 3) (ι × Fin 3) ℝ} {c : ℝ} (hc : 0 < c)
    (hfl : ∀ η : BondField ι, c * ∑ b, ‖η b‖ ^ 2 ≤ quadraticForm M η)
    {f : BondField ι → ℝ} (hf : PolyGrowth f) : Integrable (fun η => f η * gaussWeight M η) := by
  obtain ⟨hfc, C, n, hC⟩ := hf
  obtain ⟨R, hR⟩ : ∃ R : ℕ, (Module.finrank ℝ (BondField ι) : ℝ) < R :=
    ⟨Module.finrank ℝ (BondField ι) + 1, by simp⟩
  have hint := integrable_one_add_norm (E := BondField ι) (μ := volume) hR
  have hb : 0 < c / 2 := by positivity
  refine (hint.const_mul (|C| * Real.exp (((n + R : ℕ) : ℝ) ^ 2 / (4 * (c / 2))))).mono'
    (hfc.mul (continuous_gaussWeight M)).aestronglyMeasurable (Eventually.of_forall fun η => ?_)
  have hs : 0 ≤ ‖η‖ := norm_nonneg η
  have hpos : 0 < 1 + ‖η‖ := by linarith
  have hw : gaussWeight M η ≤ Real.exp (-(c / 2 * ‖η‖ ^ 2)) := by
    refine Real.exp_le_exp.2 ?_
    have h1 := hfl η
    have h2 := mul_le_mul_of_nonneg_left (norm_sq_le_sum_norm_sq η) hc.le
    linarith
  have hA := one_add_pow_mul_exp_neg_sq_le (n + R) hb hs
  have hCabs : |f η| ≤ |C| * (1 + ‖η‖) ^ n :=
    (hC η).trans (mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity))
  have hwpos : 0 < gaussWeight M η := Real.exp_pos _
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos hwpos,
    Real.rpow_neg hpos.le, Real.rpow_natCast]
  calc |f η| * gaussWeight M η ≤ (|C| * (1 + ‖η‖) ^ n) * Real.exp (-(c / 2 * ‖η‖ ^ 2)) :=
        mul_le_mul hCabs hw (Real.exp_pos _).le (by positivity)
    _ = |C| * (((1 + ‖η‖) ^ (n + R) * Real.exp (-(c / 2 * ‖η‖ ^ 2))) * ((1 + ‖η‖) ^ R)⁻¹) := by
        rw [pow_add]
        field_simp
    _ ≤ |C| * (Real.exp (((n + R : ℕ) : ℝ) ^ 2 / (4 * (c / 2))) * ((1 + ‖η‖) ^ R)⁻¹) := by
        refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
        exact mul_le_mul_of_nonneg_right hA (by positivity)
    _ = _ := by ring
private lemma fderiv_gaussWeight_apply (M : Matrix (ι × Fin 3) (ι × Fin 3) ℝ) (η v : BondField ι) :
    fderiv ℝ (gaussWeight M) η v = -(1 / 2 * fderiv ℝ (quadraticForm M) η v) * gaussWeight M η := by
  have h := (((hasFDerivAt_quadraticForm M η).const_mul (1 / 2 : ℝ)).neg).exp
  have h' : HasFDerivAt (gaussWeight M) _ η := h
  rw [h'.fderiv, (hasFDerivAt_quadraticForm M η).fderiv]
  simp [gaussWeight, mul_comm]
private lemma differentiable_quadraticForm (S : Matrix (ι × Fin 3) (ι × Fin 3) ℝ) :
    Differentiable ℝ (quadraticForm S) :=
  fun η => (hasFDerivAt_quadraticForm S η).differentiableAt
private lemma differentiable_gaussWeight (M : Matrix (ι × Fin 3) (ι × Fin 3) ℝ) :
    Differentiable ℝ (gaussWeight M) := fun η =>
  ((((hasFDerivAt_quadraticForm M η).const_mul (1 / 2 : ℝ)).neg).exp).differentiableAt
private lemma half_fderiv_quadraticForm_inverse_row {M T : Matrix (ι × Fin 3) (ι × Fin 3) ℝ}
    (hsym : M.IsSymm) (hT : T * M = 1) (i : ι × Fin 3) (η : BondField ι) :
    1 / 2 * fderiv ℝ (quadraticForm M) η (fieldOfCoords (T i)) = coordFun i η := by
  have hrow : ∀ a, ∑ b, T i b * M b a = (1 : Matrix (ι × Fin 3) (ι × Fin 3) ℝ) i a := fun a => by
    rw [← hT, Matrix.mul_apply]
  have h1 : ∑ a, ∑ b, M a b * (coordFun a η * T i b) = coordFun i η := by
    calc ∑ a, ∑ b, M a b * (coordFun a η * T i b) = ∑ a, coordFun a η * ∑ b, T i b * M b a := by
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun b _ => ?_
          rw [hsym.apply b a]
          ring
      _ = ∑ a, coordFun a η * (1 : Matrix (ι × Fin 3) (ι × Fin 3) ℝ) i a := by simp only [hrow]
      _ = coordFun i η := by simp [Matrix.one_apply]
  have h2 : ∑ a, ∑ b, M a b * (coordFun b η * T i a) = coordFun i η := by
    calc ∑ a, ∑ b, M a b * (coordFun b η * T i a) = ∑ b, coordFun b η * ∑ a, T i a * M a b := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun b _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun a _ => ?_
          ring
      _ = ∑ a, coordFun a η * (1 : Matrix (ι × Fin 3) (ι × Fin 3) ℝ) i a := by simp only [hrow]
      _ = coordFun i η := by simp [Matrix.one_apply]
  rw [fderiv_quadraticForm_apply]
  simp only [coordFun_fieldOfCoords, mul_add, Finset.sum_add_distrib, h1, h2]
  ring
private lemma integral_mul_coord_eq_integral_fderiv {M T : Matrix (ι × Fin 3) (ι × Fin 3) ℝ}
    {c : ℝ} (hc : 0 < c)
    (hfl : ∀ η : BondField ι, c * ∑ b, ‖η b‖ ^ 2 ≤ quadraticForm M η) (hsym : M.IsSymm)
    (hT : T * M = 1) (i : ι × Fin 3) {g : BondField ι → ℝ} (hg : PolyGrowth g)
    (hd : Differentiable ℝ g) (hg' : PolyGrowth fun η => fderiv ℝ g η (fieldOfCoords (T i))) :
    ∫ η, (g η * coordFun i η) * gaussWeight M η =
      ∫ η, fderiv ℝ g η (fieldOfCoords (T i)) * gaussWeight M η := by
  have hw : ∀ η, g η * fderiv ℝ (gaussWeight M) η (fieldOfCoords (T i)) =
      -((g η * coordFun i η) * gaussWeight M η) :=
    fun η => by
      rw [fderiv_gaussWeight_apply, half_fderiv_quadraticForm_inverse_row hsym hT]
      ring
  have hi : Integrable fun η => (g η * coordFun i η) * gaussWeight M η :=
    (hg.mul (polyGrowth_coordFun i)).integrable hc hfl
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume) (f := g)
    (g := gaussWeight M) (v := fieldOfCoords (T i)) (hg'.integrable hc hfl)
    (by simp only [hw]; exact hi.neg) (hg.integrable hc hfl)
    (fun x _ => hd x) (fun x _ => differentiable_gaussWeight M x)
  simp only [hw] at h
  rw [integral_neg] at h
  exact neg_injective h
private def entrywisePairing (S R : Matrix (ι × Fin 3) (ι × Fin 3) ℝ) : ℝ := ∑ i, ∑ j, S i j * R i j
private lemma entrywisePairing_eq_trace (S R : Matrix (ι × Fin 3) (ι × Fin 3) ℝ) :
    entrywisePairing S R = (S * R.transpose).trace := by
  simp [entrywisePairing, Matrix.trace, Matrix.mul_apply]
section GaussianMoments
variable {M T : Matrix (ι × Fin 3) (ι × Fin 3) ℝ} {c : ℝ} (hc : 0 < c)
  (hfl : ∀ η : BondField ι, c * ∑ b, ‖η b‖ ^ 2 ≤ quadraticForm M η) (hsym : M.IsSymm)
  (hT : T * M = 1)
include hc hfl in
private lemma integrable_gaussWeight : Integrable (gaussWeight M) := by
  simpa using (PolyGrowth.const (ι := ι) 1).integrable hc hfl
include hc hfl hsym hT
private lemma integral_coord_mul_coord (i j : ι × Fin 3) :
    ∫ η, (coordFun j η * coordFun i η) * gaussWeight M η = T i j * ∫ η, gaussWeight M η := by
  have hfd : ∀ η, fderiv ℝ (fun η : BondField ι => coordFun j η) η (fieldOfCoords (T i)) = T i j :=
    fun η => by
      have h : HasFDerivAt (fun η : BondField ι => coordFun j η) (coordFun j) η :=
        (coordFun j).hasFDerivAt
      rw [h.fderiv]
      rfl
  have h := integral_mul_coord_eq_integral_fderiv hc hfl hsym hT i (polyGrowth_coordFun j)
    (coordFun j).differentiable (by simp only [hfd]; exact PolyGrowth.const _)
  rw [h]
  simp only [hfd]
  exact integral_const_mul _ _
private lemma integral_coord_mul_form_mul_coord {B : Matrix (ι × Fin 3) (ι × Fin 3) ℝ} (hB : B.IsSymm)
    (i j : ι × Fin 3) :
    ∫ η, (coordFun j η * quadraticForm B η) * coordFun i η * gaussWeight M η =
      T i j * (∫ η, quadraticForm B η * gaussWeight M η) +
        2 * (T * B * T) i j * ∫ η, gaussWeight M η := by
  have hfd : ∀ η, fderiv ℝ (fun η : BondField ι => coordFun j η * quadraticForm B η) η
      (fieldOfCoords (T i)) = T i j * quadraticForm B η + ∑ a, ∑ b,
        ((B a b * T i b) * (coordFun j η * coordFun a η) +
          (B a b * T i a) * (coordFun j η * coordFun b η)) :=
    fun η => by
      have h := ((coordFun j).hasFDerivAt (x := η)).mul (hasFDerivAt_quadraticForm B η)
      have h' : HasFDerivAt (fun η : BondField ι => coordFun j η * quadraticForm B η) _ η := h
      rw [h'.fderiv, add_apply, smul_apply, smul_apply, ← (hasFDerivAt_quadraticForm B η).fderiv,
        fderiv_quadraticForm_apply]
      simp only [coordFun_fieldOfCoords, smul_eq_mul]
      have e : coordFun j η * ∑ a, ∑ b, B a b * (coordFun a η * T i b + coordFun b η * T i a) =
          ∑ a, ∑ b, ((B a b * T i b) * (coordFun j η * coordFun a η) +
            (B a b * T i a) * (coordFun j η * coordFun b η)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun b _ => ?_
        ring
      rw [e]
      ring
  have hdiff : Differentiable ℝ fun η : BondField ι => coordFun j η * quadraticForm B η :=
    (coordFun j).differentiable.mul (differentiable_quadraticForm B)
  have hgrowth : PolyGrowth fun η : BondField ι => T i j * quadraticForm B η + ∑ a, ∑ b,
      ((B a b * T i b) * (coordFun j η * coordFun a η) +
        (B a b * T i a) * (coordFun j η * coordFun b η)) :=
    ((PolyGrowth.const _).mul (polyGrowth_quadraticForm B)).add
      (PolyGrowth.sum _ fun a _ => PolyGrowth.sum _ fun b _ =>
        ((PolyGrowth.const _).mul ((polyGrowth_coordFun j).mul (polyGrowth_coordFun a))).add
          ((PolyGrowth.const _).mul ((polyGrowth_coordFun j).mul (polyGrowth_coordFun b))))
  have h := integral_mul_coord_eq_integral_fderiv hc hfl hsym hT i
    ((polyGrowth_coordFun j).mul (polyGrowth_quadraticForm B)) hdiff
    (by simp only [hfd]; exact hgrowth)
  rw [h]
  simp only [hfd]
  have hI : ∀ a, Integrable fun η => (coordFun j η * coordFun a η) * gaussWeight M η := fun a =>
    ((polyGrowth_coordFun j).mul (polyGrowth_coordFun a)).integrable hc hfl
  have hF : Integrable fun η => quadraticForm B η * gaussWeight M η :=
    (polyGrowth_quadraticForm B).integrable hc hfl
  have expand : ∀ η, (T i j * quadraticForm B η + ∑ a, ∑ b,
      ((B a b * T i b) * (coordFun j η * coordFun a η) +
        (B a b * T i a) * (coordFun j η * coordFun b η))) *
        gaussWeight M η = T i j * (quadraticForm B η * gaussWeight M η) + ∑ a, ∑ b,
      ((B a b * T i b) * ((coordFun j η * coordFun a η) * gaussWeight M η) +
        (B a b * T i a) * ((coordFun j η * coordFun b η) * gaussWeight M η)) := fun η => by
    rw [add_mul, Finset.sum_mul, mul_assoc]
    congr 1
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun b _ => ?_
    ring
  simp only [expand]
  have hab : ∀ a b, Integrable fun η =>
      ((B a b * T i b) * ((coordFun j η * coordFun a η) * gaussWeight M η) +
        (B a b * T i a) * ((coordFun j η * coordFun b η) * gaussWeight M η)) := fun a b =>
    ((hI a).const_mul _).add ((hI b).const_mul _)
  have inner : ∀ a b, ∫ η, ((B a b * T i b) * ((coordFun j η * coordFun a η) * gaussWeight M η) +
      (B a b * T i a) * ((coordFun j η * coordFun b η) * gaussWeight M η)) =
      (B a b * T i b) * (T a j * ∫ η, gaussWeight M η) +
        (B a b * T i a) * (T b j * ∫ η, gaussWeight M η) := fun a b => by
    rw [integral_add ((hI a).const_mul _) ((hI b).const_mul _), integral_const_mul,
      integral_const_mul, integral_coord_mul_coord hc hfl hsym hT a j,
      integral_coord_mul_coord hc hfl hsym hT b j]
  rw [integral_add (hF.const_mul _)
      (integrable_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ => hab a b),
    integral_const_mul, integral_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ => hab a b]
  have hsum : ∀ a, ∫ η, ∑ b, ((B a b * T i b) * ((coordFun j η * coordFun a η) * gaussWeight M η) +
      (B a b * T i a) * ((coordFun j η * coordFun b η) * gaussWeight M η)) =
      ∑ b, ((B a b * T i b) * (T a j * ∫ η, gaussWeight M η) +
        (B a b * T i a) * (T b j * ∫ η, gaussWeight M η)) := fun a => by
    rw [integral_finsetSum _ fun b _ => hab a b]
    exact Finset.sum_congr rfl fun b _ => inner a b
  simp only [hsum]
  have hP : (T * B * T) i j = ∑ a, ∑ b, T i a * B a b * T b j := by
    simp only [Matrix.mul_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
  have s2 : ∑ a, ∑ b, (B a b * T i a) * (T b j * ∫ η, gaussWeight M η) =
      (T * B * T) i j * ∫ η, gaussWeight M η := by
    rw [hP, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun b _ => ?_
    ring
  have s1 : ∑ a, ∑ b, (B a b * T i b) * (T a j * ∫ η, gaussWeight M η) =
      (T * B * T) i j * ∫ η, gaussWeight M η := by
    rw [← s2, Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [hB.apply a b]
  simp only [Finset.sum_add_distrib]
  rw [s1, s2]
  ring
private lemma integral_quadraticForm_mul_gaussWeight (S : Matrix (ι × Fin 3) (ι × Fin 3) ℝ) :
    ∫ η, quadraticForm S η * gaussWeight M η = entrywisePairing S T * ∫ η, gaussWeight M η := by
  have expand : ∀ η, quadraticForm S η * gaussWeight M η =
      ∑ i, ∑ j, S i j * ((coordFun j η * coordFun i η) * gaussWeight M η) := fun η => by
    have h : quadraticForm S η = ∑ i, ∑ j, S i j * (coordFun i η * coordFun j η) := rfl
    rw [h, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have hI : ∀ i j, Integrable fun η => S i j * ((coordFun j η * coordFun i η) * gaussWeight M η) :=
    fun i j => (((polyGrowth_coordFun j).mul (polyGrowth_coordFun i)).integrable hc hfl).const_mul _
  simp only [expand]
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hI i j, entrywisePairing,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ fun j _ => hI i j, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_const_mul, integral_coord_mul_coord hc hfl hsym hT i j]
  ring
private lemma integral_quadraticForm_mul_quadraticForm_mul_gaussWeight
    (A : Matrix (ι × Fin 3) (ι × Fin 3) ℝ)
    {B : Matrix (ι × Fin 3) (ι × Fin 3) ℝ} (hB : B.IsSymm) :
    ∫ η, quadraticForm A η * quadraticForm B η * gaussWeight M η =
      (entrywisePairing A T * entrywisePairing B T + 2 * entrywisePairing A (T * B * T)) *
        ∫ η, gaussWeight M η := by
  have expand : ∀ η, quadraticForm A η * quadraticForm B η * gaussWeight M η =
      ∑ i, ∑ j, A i j * ((coordFun j η * quadraticForm B η) * coordFun i η * gaussWeight M η) :=
    fun η => by
    have h : quadraticForm A η = ∑ i, ∑ j, A i j * (coordFun i η * coordFun j η) := rfl
    rw [h, Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have hI : ∀ i j, Integrable fun η =>
      A i j * ((coordFun j η * quadraticForm B η) * coordFun i η * gaussWeight M η) := fun i j =>
    ((((polyGrowth_coordFun j).mul (polyGrowth_quadraticForm B)).mul
      (polyGrowth_coordFun i)).integrable hc hfl).const_mul _
  simp only [expand]
  have hB' := integral_quadraticForm_mul_gaussWeight hc hfl hsym hT B
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hI i j]
  have hrow : ∀ i, ∫ η, ∑ j, A i j *
      ((coordFun j η * quadraticForm B η) * coordFun i η * gaussWeight M η) =
      ∑ j, A i j * (T i j * (entrywisePairing B T * ∫ η, gaussWeight M η) +
        2 * (T * B * T) i j * ∫ η, gaussWeight M η) := fun i => by
    rw [integral_finsetSum _ fun j _ => hI i j]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_const_mul, integral_coord_mul_form_mul_coord hc hfl hsym hT hB i j, hB']
  simp only [hrow]
  have e : ∀ i j, A i j * (T i j * (entrywisePairing B T * ∫ η, gaussWeight M η) +
      2 * (T * B * T) i j * ∫ η, gaussWeight M η) =
        (A i j * T i j) * (entrywisePairing B T * ∫ η, gaussWeight M η) +
          (A i j * (T * B * T) i j) * (2 * ∫ η, gaussWeight M η) := fun i j => by ring
  simp only [e, Finset.sum_add_distrib, ← Finset.sum_mul]
  simp only [entrywisePairing]
  ring
private lemma gaussianExpectation_mixed_identity (S A : Matrix (ι × Fin 3) (ι × Fin 3) ℝ)
    {B : Matrix (ι × Fin 3) (ι × Fin 3) ℝ} (hB : B.IsSymm) :
    gaussianExpectation M (fun η => -(1 / 2 * quadraticForm S η) +
        1 / 2 * quadraticForm A η * (1 / 2 * quadraticForm B η)) -
      gaussianExpectation M (fun η => 1 / 2 * quadraticForm A η) *
        gaussianExpectation M (fun η => 1 / 2 * quadraticForm B η) =
      -(1 / 2) * entrywisePairing S T + 1 / 2 * entrywisePairing A (T * B * T) := by
  have hmean : ∀ g : BondField ι → ℝ, gaussianExpectation M g =
      (∫ η, g η * gaussWeight M η) / ∫ η, gaussWeight M η := fun _ => rfl
  have hZ : 0 < ∫ η, gaussWeight M η := integral_exp_pos (integrable_gaussWeight hc hfl)
  have hS : Integrable fun η => quadraticForm S η * gaussWeight M η :=
    (polyGrowth_quadraticForm S).integrable hc hfl
  have hAB : Integrable fun η => quadraticForm A η * quadraticForm B η * gaussWeight M η :=
    ((polyGrowth_quadraticForm A).mul (polyGrowth_quadraticForm B)).integrable hc hfl
  have half : ∀ R : Matrix (ι × Fin 3) (ι × Fin 3) ℝ,
      ∫ η, 1 / 2 * quadraticForm R η * gaussWeight M η =
        1 / 2 * (entrywisePairing R T * ∫ η, gaussWeight M η) := by
    intro R
    simp only [mul_assoc]
    rw [integral_const_mul, integral_quadraticForm_mul_gaussWeight hc hfl hsym hT R]
  have e : ∀ η, (-(1 / 2 * quadraticForm S η) +
      1 / 2 * quadraticForm A η * (1 / 2 * quadraticForm B η)) * gaussWeight M η =
      -(1 / 2) * (quadraticForm S η * gaussWeight M η) +
        1 / 4 * (quadraticForm A η * quadraticForm B η * gaussWeight M η) := fun η => by ring
  rw [hmean, hmean, hmean, half, half]
  simp only [e]
  rw [integral_add (hS.const_mul _) (hAB.const_mul _), integral_const_mul, integral_const_mul,
    integral_quadraticForm_mul_gaussWeight hc hfl hsym hT S,
    integral_quadraticForm_mul_quadraticForm_mul_gaussWeight hc hfl hsym hT A hB]
  field_simp
  ring
end GaussianMoments
private def twoParamLine (u t : ℝ) : Fin 2 → ℝ := u • Pi.single 0 1 + t • Pi.single 1 1
private lemma twoParamLine_zero_zero : twoParamLine 0 0 = 0 := by simp [twoParamLine]
private lemma hasDerivAt_mixed_of_contDiffAt {f : (Fin 2 → ℝ) → ℝ} (hf : ContDiffAt ℝ 2 f 0) :
    (∀ᶠ u in 𝓝 (0 : ℝ), DifferentiableAt ℝ (fun t => f (twoParamLine u t)) 0) ∧
      HasDerivAt (fun u => f (twoParamLine u 0)) (fderiv ℝ f 0 (Pi.single 0 1)) 0 ∧
      HasDerivAt (fun t => f (twoParamLine 0 t)) (fderiv ℝ f 0 (Pi.single 1 1)) 0 ∧
      HasDerivAt (fun u => deriv (fun t => f (twoParamLine u t)) 0)
        (iteratedFDeriv ℝ 2 f 0 fun l => Pi.single l 1) 0 := by
  have hu : ∀ t, HasDerivAt (fun u => twoParamLine u t) (Pi.single 0 1) 0 := fun t => by
    simpa [twoParamLine] using ((hasDerivAt_id (0 : ℝ)).smul_const
      (Pi.single 0 1 : Fin 2 → ℝ)).add_const (t • (Pi.single 1 1 : Fin 2 → ℝ))
  have ht : ∀ u, HasDerivAt (fun t => twoParamLine u t) (Pi.single 1 1) 0 := fun u => by
    simpa [twoParamLine] using ((hasDerivAt_id (0 : ℝ)).smul_const
      (Pi.single 1 1 : Fin 2 → ℝ)).const_add (u • (Pi.single 0 1 : Fin 2 → ℝ))
  have hev : ∀ᶠ x in 𝓝 (0 : Fin 2 → ℝ), DifferentiableAt ℝ f x :=
    (hf.eventually (by simp)).mono fun x hx => hx.differentiableAt (by norm_num)
  have hcont : Tendsto (fun u => twoParamLine u 0) (𝓝 0) (𝓝 0) := by
    have := (hu 0).continuousAt.tendsto
    rwa [twoParamLine_zero_zero] at this
  have hev' : ∀ᶠ u in 𝓝 (0 : ℝ), DifferentiableAt ℝ f (twoParamLine u 0) := hcont.eventually hev
  have hderiv : ∀ u, DifferentiableAt ℝ f (twoParamLine u 0) →
      HasDerivAt (fun t => f (twoParamLine u t)) (fderiv ℝ f (twoParamLine u 0) (Pi.single 1 1)) 0 :=
    fun u h => h.hasFDerivAt.comp_hasDerivAt 0 (ht u)
  have h0 : HasFDerivAt f (fderiv ℝ f 0) (twoParamLine 0 0) := by
    rw [twoParamLine_zero_zero]
    exact (hf.differentiableAt (by norm_num)).hasFDerivAt
  have hf1 : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) 0) (twoParamLine 0 0) := by
    rw [twoParamLine_zero_zero]
    exact ((hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  refine ⟨hev'.mono fun u h => (hderiv u h).differentiableAt,
    HasFDerivAt.comp_hasDerivAt (f := fun u => twoParamLine u 0) 0 h0 (hu 0),
    h0.comp_hasDerivAt 0 (ht 0), ?_⟩
  have h1 : HasDerivAt (fun u => fderiv ℝ f (twoParamLine u 0))
      (fderiv ℝ (fderiv ℝ f) 0 (Pi.single 0 1)) 0 :=
    HasFDerivAt.comp_hasDerivAt (f := fun u => twoParamLine u 0) 0 hf1 (hu 0)
  have h2 : HasDerivAt (fun u => fderiv ℝ f (twoParamLine u 0) (Pi.single 1 1))
      (fderiv ℝ (fderiv ℝ f) 0 (Pi.single 0 1) (Pi.single 1 1)) 0 :=
    (ContinuousLinearMap.apply ℝ ℝ (Pi.single 1 1 : Fin 2 → ℝ)).hasFDerivAt.comp_hasDerivAt 0 h1
  rw [iteratedFDeriv_two_apply]
  exact h2.congr_of_eventuallyEq (hev'.mono fun u h => (hderiv u h).deriv)
private lemma contDiffAt_det_of_entries {H : (Fin 2 → ℝ) → Matrix (ι × Fin 3) (ι × Fin 3) ℝ}
    (hH : ∀ i j, ContDiffAt ℝ 3 (fun τ => H τ i j) 0) :
    ContDiffAt ℝ 3 (fun τ => (H τ).det) 0 := by
  simp only [Matrix.det_apply']
  exact ContDiffAt.sum fun σ _ => contDiffAt_const.mul (contDiffAt_prod fun i _ => hH _ _)
private lemma posDef_of_lower_bound {D : Matrix (ι × Fin 3) (ι × Fin 3) ℝ} {c : ℝ} (hc : 0 < c)
    (hD : D.IsSymm) (hfl : ∀ η : BondField ι, c * ∑ b, ‖η b‖ ^ 2 ≤ quadraticForm D η) :
    D.PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos
    (by rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]; exact hD) ?_
  intro x hx
  obtain ⟨p, hp⟩ := Function.ne_iff.1 hx
  have hform : quadraticForm D (fieldOfCoords x) = star x ⬝ᵥ D.mulVec x := by
    have h : quadraticForm D (fieldOfCoords x) = ∑ i, ∑ j, D i j * (x i * x j) := rfl
    rw [h]
    simp only [dotProduct, Matrix.mulVec, star_trivial, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [← hform]
  have h1 : |x p| ≤ ‖fieldOfCoords x p.1‖ := PiLp.norm_apply_le (fieldOfCoords x p.1) p.2
  have h2 : 0 < |x p| := abs_pos.2 hp
  have h3 : ‖fieldOfCoords x p.1‖ ^ 2 ≤ ∑ b, ‖fieldOfCoords x b‖ ^ 2 :=
    Finset.single_le_sum (f := fun b => ‖fieldOfCoords x b‖ ^ 2) (fun _ _ => by positivity)
      (Finset.mem_univ p.1)
  have h4 : 0 < ‖fieldOfCoords x p.1‖ ^ 2 := by
    have := lt_of_lt_of_le h2 h1
    positivity
  exact lt_of_lt_of_le (mul_pos hc (lt_of_lt_of_le h4 h3)) (hfl _)
private lemma trace_map_ofRealHom (X : Matrix (ι × Fin 3) (ι × Fin 3) ℝ) :
    (X.map Complex.ofRealHom).trace = (X.trace : ℂ) := by
  simp [Matrix.trace]
private lemma iteratedFDeriv_two_log_det
    (hMix : OneLoopCoefficient.hasDerivAt_mixed_logDet_statement)
    {H : (Fin 2 → ℝ) → Matrix (ι × Fin 3) (ι × Fin 3) ℝ}
    (hH : ∀ i j, ContDiffAt ℝ 3 (fun τ => H τ i j) 0) (hdet : 0 < (H 0).det) :
    iteratedFDeriv ℝ 2 (fun τ => Real.log (H τ).det) 0 (fun l => Pi.single l 1) =
      ((H 0)⁻¹ * familyMixedDeriv H).trace -
        ((H 0)⁻¹ * familyPartialDeriv H 0 * ((H 0)⁻¹ * familyPartialDeriv H 1)).trace := by
  have hdetC := contDiffAt_det_of_entries hH
  have hlog : ContDiffAt ℝ 3 (fun τ => Real.log (H τ).det) 0 := hdetC.log hdet.ne'
  have hG := hasDerivAt_mixed_of_contDiffAt (hlog.of_le (by norm_num))
  have hE := fun i j => hasDerivAt_mixed_of_contDiffAt ((hH i j).of_le (by norm_num))
  set K : ℝ → ℝ → Matrix (ι × Fin 3) (ι × Fin 3) ℂ :=
    fun u t => (H (twoParamLine u t)).map Complex.ofRealHom with hK
  have hdiff : ∀ᶠ u in 𝓝 (0 : ℝ), ∀ i j, DifferentiableAt ℝ (fun t => K u t i j) 0 := by
    simp only [eventually_all]
    exact fun i j => (hE i j).1.mono fun u hu => hu.hasDerivAt.ofReal_comp.differentiableAt
  have hd1 : ∀ i j, HasDerivAt (fun u => K u 0 i j)
      ((familyPartialDeriv H 0).map Complex.ofRealHom i j) 0 :=
    fun i j => (hE i j).2.1.ofReal_comp
  have hd2 : ∀ i j, HasDerivAt (fun t => K 0 t i j)
      ((familyPartialDeriv H 1).map Complex.ofRealHom i j) 0 :=
    fun i j => (hE i j).2.2.1.ofReal_comp
  have hd3 : ∀ i j, HasDerivAt (fun u => deriv (fun t => K u t i j) 0)
      ((familyMixedDeriv H).map Complex.ofRealHom i j) 0 := fun i j =>
    (hE i j).2.2.2.ofReal_comp.congr_of_eventuallyEq
      ((hE i j).1.mono fun u hu => hu.hasDerivAt.ofReal_comp.deriv)
  have hKdet : ∀ u t, (K u t).det = ((H (twoParamLine u t)).det : ℂ) := fun u t =>
    (RingHom.map_det Complex.ofRealHom (H (twoParamLine u t))).symm
  have hK0 : K 0 0 = (H 0).map Complex.ofRealHom := by simp only [hK, twoParamLine_zero_zero]
  have hslit : (K 0 0).det ∈ Complex.slitPlane := by
    rw [hKdet, twoParamLine_zero_zero]
    exact Complex.ofReal_mem_slitPlane.2 hdet
  obtain ⟨-, hfin⟩ := hMix (ι × Fin 3) K _ _ _ hdiff hd1 hd2 hd3 hslit
  have hcontLine : ContinuousAt (fun p : ℝ × ℝ => twoParamLine p.1 p.2) (0, 0) := by
    unfold twoParamLine
    fun_prop
  have hpos : ∀ᶠ p : ℝ × ℝ in 𝓝 (0, 0), 0 < (H (twoParamLine p.1 p.2)).det := by
    have h1 : ∀ᶠ τ in 𝓝 (0 : Fin 2 → ℝ), 0 < (H τ).det :=
      hdetC.continuousAt.eventually (lt_mem_nhds hdet)
    have h2 : Tendsto (fun p : ℝ × ℝ => twoParamLine p.1 p.2) (𝓝 (0, 0)) (𝓝 0) := by
      have := hcontLine.tendsto
      simpa [twoParamLine_zero_zero] using this
    exact h2.eventually h1
  have hpos' : ∀ᶠ u in 𝓝 (0 : ℝ), ∀ᶠ t in 𝓝 (0 : ℝ), 0 < (H (twoParamLine u t)).det :=
    hpos.curry_nhds
  have hfin' : HasDerivAt
      (fun u => ((deriv (fun t => Real.log (H (twoParamLine u t)).det) 0 : ℝ) : ℂ))
      (((K 0 0)⁻¹ * (familyMixedDeriv H).map Complex.ofRealHom).trace -
        ((K 0 0)⁻¹ * (familyPartialDeriv H 0).map Complex.ofRealHom *
          ((K 0 0)⁻¹ * (familyPartialDeriv H 1).map Complex.ofRealHom)).trace) 0 := by
    refine hfin.congr_of_eventuallyEq ?_
    filter_upwards [hG.1, hpos'] with u hu hu2
    have e : (fun t => Complex.log (K u t).det) =ᶠ[𝓝 0]
        fun t => ((Real.log (H (twoParamLine u t)).det : ℝ) : ℂ) := hu2.mono fun t ht => by
      show Complex.log (K u t).det = ((Real.log (H (twoParamLine u t)).det : ℝ) : ℂ)
      rw [hKdet, Complex.ofReal_log ht.le]
    rw [e.deriv_eq, hu.hasDerivAt.ofReal_comp.deriv]
  have hinv : (K 0 0)⁻¹ = ((H 0)⁻¹).map Complex.ofRealHom := by
    refine Matrix.inv_eq_left_inv ?_
    rw [hK0, ← Matrix.map_mul, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hdet.ne'),
      Matrix.map_one _ (map_zero _) (map_one _)]
  have huniq := hG.2.2.2.ofReal_comp.unique hfin'
  rw [hinv, ← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_mul,
    trace_map_ofRealHom, trace_map_ofRealHom] at huniq
  exact_mod_cast huniq
theorem logDetMixedDerivGaussian_of_mixed_logDet
    (hMix : OneLoopCoefficient.hasDerivAt_mixed_logDet_statement) :
    LogDetMixedDerivGaussian := by
  intro ι _ _ c H hc hH hsym hfl
  have hD : (H 0).IsSymm := hsym.self_of_nhds
  have hdet : 0 < (H 0).det := (posDef_of_lower_bound hc hD hfl).det_pos
  have hunit : IsUnit (H 0).det := isUnit_iff_ne_zero.2 hdet.ne'
  have hT : (H 0)⁻¹ * H 0 = 1 := Matrix.nonsing_inv_mul _ hunit
  have hTs : ((H 0)⁻¹).IsSymm := by
    rw [Matrix.IsSymm, Matrix.transpose_nonsing_inv, hD.eq]
  have hslope : ∀ l, (familyPartialDeriv H l).IsSymm := fun l => by
    refine Matrix.IsSymm.ext fun i j => ?_
    have e : (fun τ => H τ j i) =ᶠ[𝓝 0] fun τ => H τ i j := hsym.mono fun τ hτ => hτ.apply i j
    simp only [familyPartialDeriv]
    rw [e.fderiv_eq]
  refine ⟨((contDiffAt_det_of_entries hH).log hdet.ne').of_le (by norm_num), ?_⟩
  rw [iteratedFDeriv_two_log_det hMix hH hdet,
    gaussianExpectation_mixed_identity hc hfl hD hT (familyMixedDeriv H) (familyPartialDeriv H 0)
      (hslope 1),
    entrywisePairing_eq_trace, entrywisePairing_eq_trace, hTs.eq, Matrix.transpose_mul,
    Matrix.transpose_mul, hTs.eq, (hslope 1).eq, Matrix.trace_mul_comm (familyMixedDeriv H),
    Matrix.trace_mul_comm (familyPartialDeriv H 0),
    Matrix.trace_mul_comm ((H 0)⁻¹ * familyPartialDeriv H 0)]
  simp only [Matrix.mul_assoc]
  ring
end GaussianMeans
end YangMills.Construction
end
