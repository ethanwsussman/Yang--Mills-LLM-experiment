import YangMills.Construction.InfiniteLattice.TraceOnTheGroupAndOneBondWeight
import YangMills.Construction.Matrices.CharactersOfGProof
import YangMills.Construction.Matrices.ClassicalHarmonicAnalysisOnG
import YangMills.Construction.TransferOperators.CharacterCoefficientsOfTheOneBondWeight
import Mathlib
set_option autoImplicit false
open MeasureTheory Filter YangMills.Construction.TransferOperators YangMills.Construction.Matrices YangMills.Construction.Matrices.ComplexMatrix2 YangMills.Construction.InfiniteLattice YangMills.Construction.Schatten
open scoped Topology
noncomputable section
namespace YangMills.Construction.SpinHarmonics.BondWeightCoeffs
theorem integral_cos_intCast_mul_zero_pi (q : ℤ) :
    ∫ φ in (0 : ℝ)..Real.pi, Real.cos ((q : ℝ) * φ) = if q = 0 then Real.pi else 0 := by
  split_ifs with hq0
  · subst hq0
    simp
  · have hq : (q : ℝ) ≠ 0 := by exact_mod_cast hq0
    have := intervalIntegral.integral_comp_mul_left (a := 0) (b := Real.pi) Real.cos hq
    simp only [mul_zero] at this
    rw [this, integral_cos]
    simp [Real.sin_int_mul_pi]
theorem integral_cos_intCast_mul_mul_cos (p n : ℤ) :
    ∫ φ in (0 : ℝ)..Real.pi, Real.cos ((p : ℝ) * φ) * Real.cos ((n : ℝ) * φ) =
      Real.pi / 2 * ((if p = n then 1 else 0) + (if p = -n then 1 else 0)) := by
  have hprod : ∀ φ : ℝ, Real.cos ((p : ℝ) * φ) * Real.cos ((n : ℝ) * φ) =
      (Real.cos (((p - n : ℤ) : ℝ) * φ) + Real.cos (((p + n : ℤ) : ℝ) * φ)) / 2 := by
    intro φ
    push_cast
    rw [sub_mul, add_mul, Real.cos_sub, Real.cos_add]
    ring
  simp_rw [hprod]
  rw [intervalIntegral.integral_div, intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) _ _)
    (Continuous.intervalIntegrable (by fun_prop) _ _), integral_cos_intCast_mul_zero_pi,
    integral_cos_intCast_mul_zero_pi]
  have hsub : (p - n = 0) ↔ p = n := sub_eq_zero
  have hadd : (p + n = 0) ↔ p = -n := eq_neg_iff_add_eq_zero.symm
  simp only [hsub, hadd]
  split_ifs <;> ring
theorem two_mul_cos_pow_eq_sum (a : ℕ) (φ : ℝ) :
    (2 * Real.cos φ) ^ a =
      ∑ m ∈ Finset.range (a + 1),
        (a.choose m : ℝ) * Real.cos (((2 * (m : ℤ) - a : ℤ) : ℝ) * φ) := by
  have hc : ((2 * Real.cos φ : ℝ) : ℂ) =
      Complex.exp ((φ : ℂ) * Complex.I) + Complex.exp (-(φ : ℂ) * Complex.I) := by
    push_cast
    rw [Complex.two_cos]
  have hsum : (((2 * Real.cos φ) ^ a : ℝ) : ℂ) =
      ∑ m ∈ Finset.range (a + 1), (((a.choose m : ℝ) : ℂ)) *
        Complex.exp (((((2 * (m : ℤ) - a : ℤ) : ℝ) * φ : ℝ) : ℂ) * Complex.I) := by
    rw [Complex.ofReal_pow, hc, add_pow]
    refine Finset.sum_congr rfl fun m hm => ?_
    have hma : m ≤ a := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
    rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_add, mul_comm]
    congr 2
    push_cast [Nat.cast_sub hma]
    ring
  have hre := congrArg Complex.re hsum
  rw [Complex.ofReal_re, Complex.re_sum] at hre
  rw [hre]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
theorem two_pow_mul_integral_cos_pow_mul_cos (a n : ℕ) :
    (2 : ℝ) ^ a * ∫ φ in (0 : ℝ)..Real.pi, Real.cos φ ^ a * Real.cos ((n : ℝ) * φ) =
      Real.pi / 2 * ∑ m ∈ Finset.range (a + 1), (a.choose m : ℝ) *
        ((if 2 * (m : ℤ) - a = n then 1 else 0) + (if 2 * (m : ℤ) - a = -n then 1 else 0)) := by
  rw [← intervalIntegral.integral_const_mul]
  have hexpand : ∀ φ : ℝ, (2 : ℝ) ^ a * (Real.cos φ ^ a * Real.cos ((n : ℝ) * φ)) =
      ∑ m ∈ Finset.range (a + 1), (a.choose m : ℝ) *
        (Real.cos (((2 * (m : ℤ) - a : ℤ) : ℝ) * φ) * Real.cos (((n : ℤ) : ℝ) * φ)) := by
    intro φ
    rw [← mul_assoc, ← mul_pow, two_mul_cos_pow_eq_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Int.cast_natCast]
    ring
  simp_rw [hexpand]
  rw [intervalIntegral.integral_finsetSum
    (fun m _ => Continuous.intervalIntegrable (by fun_prop) _ _), Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [intervalIntegral.integral_const_mul, integral_cos_intCast_mul_mul_cos]
  ring
theorem integral_cos_pow_add_two_mul_mul_cos (n k : ℕ) :
    ∫ φ in (0 : ℝ)..Real.pi, Real.cos φ ^ (n + 2 * k) * Real.cos ((n : ℝ) * φ) =
      Real.pi * ((n + 2 * k).choose k : ℝ) / 2 ^ (n + 2 * k) := by
  have hmom := two_pow_mul_integral_cos_pow_mul_cos (n + 2 * k) n
  have hplus : ∀ m : ℕ, (2 * (m : ℤ) - ((n + 2 * k : ℕ) : ℤ) = n) ↔ m = n + k := by
    intro m
    push_cast
    omega
  have hminus : ∀ m : ℕ, (2 * (m : ℤ) - ((n + 2 * k : ℕ) : ℤ) = -n) ↔ m = k := by
    intro m
    push_cast
    omega
  simp only [hplus, hminus, mul_add, Finset.sum_add_distrib, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_range] at hmom
  rw [if_pos (by omega), if_pos (by omega),
    Nat.choose_symm_of_eq_add (show n + 2 * k = (n + k) + k by omega)] at hmom
  rw [eq_div_iff (by positivity), mul_comm, hmom]
  ring
theorem integral_cos_pow_mul_cos_eq_zero (a n : ℕ) (hne : ∀ k, a ≠ n + 2 * k) :
    ∫ φ in (0 : ℝ)..Real.pi, Real.cos φ ^ a * Real.cos ((n : ℝ) * φ) = 0 := by
  have hmom := two_pow_mul_integral_cos_pow_mul_cos a n
  have hzero : ∑ m ∈ Finset.range (a + 1), (a.choose m : ℝ) *
      ((if 2 * (m : ℤ) - a = n then (1 : ℝ) else 0) +
        (if 2 * (m : ℤ) - a = -n then 1 else 0)) = 0 := by
    refine Finset.sum_eq_zero fun m hm => ?_
    have hma : m ≤ a := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
    have hplus : ¬ (2 * (m : ℤ) - a = n) := by
      intro e
      exact hne (m - n) (by omega)
    have hminus : ¬ (2 * (m : ℤ) - a = -n) := by
      intro e
      exact hne m (by omega)
    simp [hplus, hminus]
  rw [hzero, mul_zero] at hmom
  exact (mul_eq_zero.mp hmom).resolve_left (by positivity)
theorem hasSum_integral_exp_mul_cos (n : ℕ) (z : ℝ) :
    HasSum (fun a : ℕ => z ^ a / (a.factorial : ℝ) *
        ∫ φ in (0 : ℝ)..Real.pi, Real.cos φ ^ a * Real.cos ((n : ℝ) * φ))
      (∫ φ in (0 : ℝ)..Real.pi, Real.exp (z * Real.cos φ) * Real.cos ((n : ℝ) * φ)) := by
  have hexp : ∀ x : ℝ, HasSum (fun a : ℕ => x ^ a / (a.factorial : ℝ)) (Real.exp x) := by
    intro x
    rw [Real.exp_eq_exp_ℝ]
    exact NormedSpace.expSeries_div_hasSum_exp x
  have := intervalIntegral.hasSum_integral_of_dominated_convergence (μ := volume) (a := 0)
    (b := Real.pi)
    (F := fun (a : ℕ) (φ : ℝ) => z ^ a / (a.factorial : ℝ) *
      (Real.cos φ ^ a * Real.cos ((n : ℝ) * φ)))
    (f := fun φ => Real.exp (z * Real.cos φ) * Real.cos ((n : ℝ) * φ))
    (fun a _ => |z| ^ a / (a.factorial : ℝ))
    (fun a => (Continuous.aestronglyMeasurable (by fun_prop)))
    (fun a => Eventually.of_forall fun φ _ => by
      have hone : |Real.cos φ ^ a * Real.cos ((n : ℝ) * φ)| ≤ 1 := by
        rw [abs_mul, abs_pow]
        exact mul_le_one₀ (pow_le_one₀ (abs_nonneg _) (Real.abs_cos_le_one _))
          (abs_nonneg _) (Real.abs_cos_le_one _)
      rw [Real.norm_eq_abs, abs_mul, abs_div, abs_pow, Nat.abs_cast]
      exact mul_le_of_le_one_right (by positivity) hone)
    (Eventually.of_forall fun _ _ => Real.summable_pow_div_factorial _)
    (by simp)
    (Eventually.of_forall fun φ _ => by
      have := (hexp (z * Real.cos φ)).mul_right (Real.cos ((n : ℝ) * φ))
      refine this.congr_fun ?_
      intro a
      rw [mul_pow]
      ring)
  simpa only [intervalIntegral.integral_const_mul] using this
def besselSeriesTerm (n : ℕ) (z : ℝ) (k : ℕ) : ℝ :=
  (z / 2) ^ (n + 2 * k) / ((k.factorial : ℝ) * ((n + k).factorial : ℝ))
theorem hasSum_besselSeriesTerm (n : ℕ) (z : ℝ) :
    HasSum (besselSeriesTerm n z) (modBesselI n z) := by
  have hscaled := (hasSum_integral_exp_mul_cos n z).mul_left (1 / Real.pi)
  have hinj : Function.Injective (fun k : ℕ => n + 2 * k) := by
    intro a b e
    simpa using e
  have hvanish : ∀ a ∉ Set.range (fun k : ℕ => n + 2 * k),
      1 / Real.pi * (z ^ a / (a.factorial : ℝ) *
        ∫ φ in (0 : ℝ)..Real.pi, Real.cos φ ^ a * Real.cos ((n : ℝ) * φ)) = 0 := by
    intro a ha
    rw [integral_cos_pow_mul_cos_eq_zero a n (fun k e => ha ⟨k, e.symm⟩)]
    simp
  have hsub := (hinj.hasSum_iff hvanish).mpr hscaled
  unfold modBesselI
  convert hsub using 1
  funext k
  simp only [Function.comp, integral_cos_pow_add_two_mul_mul_cos, besselSeriesTerm]
  have hchoose : ((n + 2 * k).choose k : ℝ) * (k.factorial : ℝ) * ((n + k).factorial : ℝ) =
      ((n + 2 * k).factorial : ℝ) := by
    have := Nat.choose_mul_factorial_mul_factorial (show k ≤ n + 2 * k by omega)
    rw [show n + 2 * k - k = n + k by omega] at this
    exact_mod_cast this
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  have hk : (k.factorial : ℝ) ≠ 0 := by positivity
  have hm : ((n + k).factorial : ℝ) ≠ 0 := by positivity
  have hC : ((n + 2 * k).choose k : ℝ) ≠ 0 := by
    have := Nat.choose_pos (show k ≤ n + 2 * k by omega)
    positivity
  rw [← hchoose, div_pow]
  field_simp
theorem besselSeriesTerm_pos (n : ℕ) {z : ℝ} (hz : 0 < z) (k : ℕ) :
    0 < besselSeriesTerm n z k := by
  unfold besselSeriesTerm
  positivity
theorem modBesselI_pos (n : ℕ) {z : ℝ} (hz : 0 < z) : 0 < modBesselI n z := by
  have hs := hasSum_besselSeriesTerm n z
  rw [← hs.tsum_eq]
  exact hs.summable.tsum_pos (fun k => (besselSeriesTerm_pos n hz k).le) 0
    (besselSeriesTerm_pos n hz 0)
theorem modBesselI_sub_modBesselI_add_two (m : ℕ) {z : ℝ} (hz : 0 < z) :
    modBesselI m z - modBesselI (m + 2) z =
      2 * ((m : ℝ) + 1) / z * modBesselI (m + 1) z := by
  let e : ℕ → ℝ := fun k => Nat.casesOn k 0 (besselSeriesTerm (m + 2) z)
  have he : HasSum e (modBesselI (m + 2) z) := by
    have hs := (hasSum_nat_add_iff (f := e) 1).mp (hasSum_besselSeriesTerm (m + 2) z)
    simpa [e] using hs
  have hdiff := (hasSum_besselSeriesTerm m z).sub he
  have hright := (hasSum_besselSeriesTerm (m + 1) z).mul_left (2 * ((m : ℝ) + 1) / z)
  refine hdiff.unique (hright.congr_fun ?_)
  intro k
  have hz' : z ≠ 0 := hz.ne'
  have e0 : e 0 = 0 := rfl
  have es : ∀ k, e (k + 1) = besselSeriesTerm (m + 2) z k := fun _ => rfl
  cases k with
  | zero =>
    rw [e0]
    simp only [besselSeriesTerm, Nat.mul_zero, Nat.add_zero, Nat.factorial_zero,
      Nat.factorial_succ, pow_succ]
    have hm : (m.factorial : ℝ) ≠ 0 := by positivity
    have hm1 : (m : ℝ) + 1 ≠ 0 := by positivity
    push_cast
    field_simp
    ring
  | succ k =>
    rw [es]
    simp only [besselSeriesTerm]
    rw [show m + 2 * (k + 1) = m + 2 * k + 2 by ring, show m + 2 + 2 * k = m + 2 * k + 2 by ring,
      show m + 1 + 2 * (k + 1) = (m + 2 * k + 2) + 1 by ring, show m + (k + 1) = m + k + 1 by ring,
      show m + 2 + k = m + k + 1 + 1 by ring, show m + 1 + (k + 1) = m + k + 1 + 1 by ring]
    rw [Nat.factorial_succ (m + k + 1), Nat.factorial_succ k, pow_succ _ (m + 2 * k + 2)]
    have hk : (k.factorial : ℝ) ≠ 0 := by positivity
    have hm : ((m + k + 1).factorial : ℝ) ≠ 0 := by positivity
    have hk1 : (k : ℝ) + 1 ≠ 0 := by positivity
    have hm1 : (m : ℝ) + k + 1 + 1 ≠ 0 := by positivity
    push_cast
    field_simp
    ring
theorem modBesselI_succ_le (n : ℕ) {z : ℝ} (hz : 0 < z) :
    modBesselI (n + 1) z ≤ z / (2 * ((n : ℝ) + 1)) * modBesselI n z := by
  refine hasSum_le (fun k => ?_) (hasSum_besselSeriesTerm (n + 1) z)
    ((hasSum_besselSeriesTerm n z).mul_left _)
  have hfac : ((n + 1 + k).factorial : ℝ) = ((n : ℝ) + k + 1) * ((n + k).factorial : ℝ) := by
    rw [show n + 1 + k = (n + k) + 1 by ring, Nat.factorial_succ]
    push_cast
    ring
  have hterm : besselSeriesTerm (n + 1) z k =
      z / (2 * ((n : ℝ) + k + 1)) * besselSeriesTerm n z k := by
    simp only [besselSeriesTerm]
    rw [hfac, show n + 1 + 2 * k = (n + 2 * k) + 1 by ring, pow_succ]
    have hk : (k.factorial : ℝ) ≠ 0 := by positivity
    have hm : ((n + k).factorial : ℝ) ≠ 0 := by positivity
    have hn : (n : ℝ) + k + 1 ≠ 0 := by positivity
    field_simp
  rw [hterm]
  refine mul_le_mul_of_nonneg_right ?_ (besselSeriesTerm_pos n hz k).le
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  exact div_le_div_of_nonneg_left hz.le (by positivity) (by linarith)
theorem modBesselI_le (n : ℕ) {z : ℝ} (hz : 0 < z) :
    modBesselI n z ≤ (z / 2) ^ n / (n.factorial : ℝ) * Real.exp (z ^ 2 / 4) := by
  have hexp : HasSum (fun a : ℕ => (z ^ 2 / 4) ^ a / (a.factorial : ℝ))
      (Real.exp (z ^ 2 / 4)) := by
    rw [Real.exp_eq_exp_ℝ]
    exact NormedSpace.expSeries_div_hasSum_exp _
  refine hasSum_le (fun k => ?_) (hasSum_besselSeriesTerm n z) (hexp.mul_left _)
  simp only [besselSeriesTerm]
  have hpow : (z / 2) ^ (n + 2 * k) = (z / 2) ^ n * (z ^ 2 / 4) ^ k := by
    rw [pow_add, pow_mul]
    congr 2
    ring
  have hfac : (n.factorial : ℝ) ≤ ((n + k).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_le (by omega)
  rw [hpow, div_mul_div_comm, mul_comm (n.factorial : ℝ)]
  have hk : (0 : ℝ) < k.factorial := by positivity
  exact div_le_div_of_nonneg_left (by positivity) (by positivity)
    (mul_le_mul_of_nonneg_left hfac hk.le)
theorem continuous_singleBondWeight (β : ℝ) : Continuous (singleBondWeight β) := by
  unfold singleBondWeight
  exact Complex.continuous_exp.comp (continuous_const.mul (continuous_const.sub
    (continuous_const.mul (Continuous.matrix_trace continuous_subtype_val))))
def bondWeightFun (β : ℝ) : C(specialUnitary, ℂ) :=
  ⟨singleBondWeight β, continuous_singleBondWeight β⟩
@[simp] theorem bondWeightFun_apply (β : ℝ) (g : specialUnitary) :
    bondWeightFun β g = singleBondWeight β g := rfl
section PositiveCoupling
variable {β : ℝ}
theorem bondWeightFun_isConjInvariant (hW : TraceAndSingleBondWeight) (hβ : 0 < β) :
    IsConjInvariant (bondWeightFun β) :=
  fun g h => (hW.2 β hβ).1.2.2.1 h g
theorem norm_singleBondWeight_le (hW : TraceAndSingleBondWeight) (hβ : 0 < β)
    (w : specialUnitary) : ‖singleBondWeight β w‖ ≤ 1 := by
  have him := (hW.2 β hβ).1.1 w
  have hb := (hW.2 β hβ).2.1 w
  rw [← Complex.abs_re_eq_norm.mpr him, abs_of_nonneg ((Real.exp_pos _).le.trans hb.1)]
  exact hb.2
theorem two_mul_toReal_add_one (l : HalfNatural) : 2 * l.toReal + 1 = (l.doubled : ℝ) + 1 := by apply _root_.YangMills.Construction.SpinHarmonics.SpinCharacters.two_mul_toReal_add_one <;> assumption
theorem singleBondWeight_diagPhase (hC : HarmonicAnalysisFacts) (β : ℝ) {φ : ℝ}
    (hφ : φ ∈ Set.Icc 0 Real.pi) :
    singleBondWeight β (diagPhase φ) = ((Real.exp (-β * (1 - Real.cos φ)) : ℝ) : ℂ) := by
  have htr := ((hC ⟨0⟩ ⟨0⟩).2.2.1.of_eq_conj_diagPhase (diagPhase φ) 1 φ hφ (by simp)).2.1
  unfold singleBondWeight
  rw [show (1 / 2 : ℂ) * fullTrace ((diagPhase φ : specialUnitary) : ComplexMatrix2) =
    halfTrace ((diagPhase φ : specialUnitary) : ComplexMatrix2) from rfl, htr]
  push_cast
  rfl
def besselCoeffValue (β : ℝ) (n : ℕ) : ℝ := 2 * Real.exp (-β) / β * modBesselI (n + 1) β
theorem besselCoeffValue_pos (hβ : 0 < β) (n : ℕ) : 0 < besselCoeffValue β n := by
  have := modBesselI_pos (n + 1) hβ
  unfold besselCoeffValue
  positivity
theorem integral_exp_mul_sin_mul_sin (β : ℝ) (n : ℕ) :
    ∫ φ in (0 : ℝ)..Real.pi, Real.exp (-β * (1 - Real.cos φ)) *
        (Real.sin (((n : ℝ) + 1) * φ) * Real.sin φ) =
      Real.exp (-β) / 2 * Real.pi * (modBesselI n β - modBesselI (n + 2) β) := by
  have hpt : ∀ φ : ℝ, Real.exp (-β * (1 - Real.cos φ)) *
      (Real.sin (((n : ℝ) + 1) * φ) * Real.sin φ) =
      Real.exp (-β) / 2 * (Real.exp (β * Real.cos φ) * Real.cos ((n : ℝ) * φ) -
        Real.exp (β * Real.cos φ) * Real.cos (((n + 2 : ℕ) : ℝ) * φ)) := by
    intro φ
    have hexp : Real.exp (-β * (1 - Real.cos φ)) =
        Real.exp (-β) * Real.exp (β * Real.cos φ) := by
      rw [← Real.exp_add]
      ring_nf
    have hlow : Real.cos ((n : ℝ) * φ) = Real.cos (((n : ℝ) + 1) * φ - φ) := by ring_nf
    have hhigh : Real.cos (((n + 2 : ℕ) : ℝ) * φ) = Real.cos (((n : ℝ) + 1) * φ + φ) := by
      push_cast
      ring_nf
    rw [hexp, hlow, hhigh, Real.cos_sub, Real.cos_add]
    ring
  simp_rw [hpt]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_sub
    (Continuous.intervalIntegrable (by fun_prop) _ _)
    (Continuous.intervalIntegrable (by fun_prop) _ _)]
  unfold modBesselI
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp
theorem weightCharCoeff_eq (hC : HarmonicAnalysisFacts)
    (hW : TraceAndSingleBondWeight) (hβ : 0 < β) (l : HalfNatural) :
    weightCharCoeff β l = ((besselCoeffValue β l.doubled : ℝ) : ℂ) := by
  have hF : IsConjInvariant (bondWeightFun β * spinCharacter l) := by
    intro g h
    have h1 := bondWeightFun_isConjInvariant hW hβ g h
    have h2 := (hC l l).2.2.1.isConjInvariant g h
    simp only [ContinuousMap.mul_apply]
    rw [h1, h2]
  have hweyl := (hC l l).2.2.2.1 (bondWeightFun β * spinCharacter l) hF
  have hint : ∫ φ in (0 : ℝ)..Real.pi, (bondWeightFun β * spinCharacter l) (diagPhase φ) *
      ((Real.sin φ ^ 2 : ℝ) : ℂ) =
      ((∫ φ in (0 : ℝ)..Real.pi, Real.exp (-β * (1 - Real.cos φ)) *
        (Real.sin (((l.doubled : ℝ) + 1) * φ) * Real.sin φ) : ℝ) : ℂ) := by
    rw [← intervalIntegral.integral_ofReal]
    refine intervalIntegral.integral_congr fun φ hφ => ?_
    have hφ' : φ ∈ Set.Icc 0 Real.pi := by rwa [Set.uIcc_of_le Real.pi_pos.le] at hφ
    have hchar := ((hC l l).2.2.1.of_eq_conj_diagPhase (diagPhase φ) 1 φ hφ'
      (by simp)).2.2
    rw [two_mul_toReal_add_one] at hchar
    simp only [ContinuousMap.mul_apply, bondWeightFun_apply]
    rw [singleBondWeight_diagPhase hC β hφ']
    push_cast at hchar ⊢
    rw [← hchar]
    ring
  rw [hint, integral_exp_mul_sin_mul_sin] at hweyl
  have hrec := modBesselI_sub_modBesselI_add_two l.doubled hβ
  unfold weightCharCoeff
  have hI : ∫ g : specialUnitary, singleBondWeight β g * spinCharacter l g ∂haarProb =
      ∫ g, (bondWeightFun β * spinCharacter l) g ∂haarProb := rfl
  rw [hI, hweyl, hrec, two_mul_toReal_add_one]
  unfold besselCoeffValue
  have hn : (l.doubled : ℝ) + 1 ≠ 0 := by positivity
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  rw [← Complex.ofReal_inv, ← Complex.ofReal_mul, ← Complex.ofReal_mul]
  congr 1
  field_simp
theorem integral_star_spinCharacter_mul (hC : HarmonicAnalysisFacts) (l : HalfNatural) :
    ∫ g, star (spinCharacter l g) * bondWeightFun β g ∂haarProb =
      ((2 * l.toReal + 1 : ℝ) : ℂ) * weightCharCoeff β l := by
  have hn : ((2 * l.toReal + 1 : ℝ) : ℂ) ≠ 0 := by
    rw [two_mul_toReal_add_one]
    exact_mod_cast (show (l.doubled : ℝ) + 1 ≠ 0 by positivity)
  unfold weightCharCoeff
  rw [mul_inv_cancel_left₀ hn]
  refine integral_congr_ae (Eventually.of_forall fun g => ?_)
  have him := (hC l l).2.2.1.im_eq_zero g
  have hs : star (spinCharacter l g) = spinCharacter l g := Complex.conj_eq_iff_im.mpr him
  simp only [hs, bondWeightFun_apply]
  ring
theorem norm_weightCharCoeff_le (hC : HarmonicAnalysisFacts)
    (hW : TraceAndSingleBondWeight) (hβ : 0 < β) (l : HalfNatural) :
    ‖weightCharCoeff β l‖ ≤ 1 := by
  have hpos : (0 : ℝ) < 2 * l.toReal + 1 := by
    rw [two_mul_toReal_add_one]
    positivity
  have hb : ‖∫ g : specialUnitary, singleBondWeight β g * spinCharacter l g ∂haarProb‖ ≤
      2 * l.toReal + 1 := by
    have := norm_integral_le_of_norm_le_const (μ := (haarProb : Measure specialUnitary))
      (f := fun g : specialUnitary => singleBondWeight β g * spinCharacter l g)
      (C := 2 * l.toReal + 1)
      (Eventually.of_forall fun g => by
        rw [norm_mul]
        calc ‖singleBondWeight β g‖ * ‖spinCharacter l g‖ ≤ 1 * (2 * l.toReal + 1) :=
              mul_le_mul (norm_singleBondWeight_le hW hβ g)
                ((hC l l).2.2.1.norm_le g) (norm_nonneg _) zero_le_one
          _ = 2 * l.toReal + 1 := one_mul _)
    simpa using this
  unfold weightCharCoeff
  rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos]
  rw [inv_mul_le_iff₀ hpos, mul_one]
  exact hb
theorem exists_hasKernel_of_continuous (K : specialUnitary × specialUnitary → ℂ)
    (hK : Continuous K) :
    ∃ T : Lp ℂ 2 haarProb →L[ℂ] Lp ℂ 2 haarProb, HasKernel haarProb K T := by
  let k : C(specialUnitary, C(specialUnitary, ℂ)) :=
    ContinuousMap.curry ⟨fun p : specialUnitary × specialUnitary => star (K p),
      continuous_star.comp hK⟩
  let kk : C(specialUnitary, Lp ℂ 2 haarProb) :=
    (ContinuousMap.mk (ContinuousMap.toLp (E := ℂ) 2 haarProb ℂ)
      (ContinuousLinearMap.continuous _)).comp k
  have hkk : ∀ g, (kk g : specialUnitary → ℂ) =ᵐ[haarProb] fun h => star (K (g, h)) :=
    fun g => ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) haarProb (k g)
  let L : Lp ℂ 2 haarProb →ₗ[ℂ] C(specialUnitary, ℂ) :=
    { toFun := fun ψ => ⟨fun g => inner ℂ (kk g) ψ, kk.continuous.inner continuous_const⟩
      map_add' := fun ψ ψ' => by
        ext g
        simp [inner_add_right]
      map_smul' := fun c ψ => by
        ext g
        simp [inner_smul_right] }
  have hb : ∀ ψ, ‖L ψ‖ ≤ ‖kk‖ * ‖ψ‖ := fun ψ =>
    (ContinuousMap.norm_le _ (by positivity)).mpr fun g =>
      (norm_inner_le_norm (𝕜 := ℂ) _ _).trans
        (mul_le_mul_of_nonneg_right (kk.norm_coe_le_norm g) (norm_nonneg _))
  refine ⟨(ContinuousMap.toLp (E := ℂ) 2 haarProb ℂ).comp (L.mkContinuous _ hb), fun ψ => ?_⟩
  have h1 := ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) haarProb (L ψ)
  refine h1.trans (Eventually.of_forall fun g => ?_)
  change inner ℂ (kk g) ψ = ∫ h, K (g, h) * ψ h ∂haarProb
  rw [L2.inner_def]
  refine integral_congr_ae ((hkk g).mono fun h e => ?_)
  simp only [e, RCLike.inner_apply]
  simp [mul_comm]
theorem hasKernel_singleLinkOperator (β : ℝ) :
    HasKernel haarProb
      (fun p : specialUnitary × specialUnitary => singleBondWeight β (p.1 * p.2⁻¹))
      (singleLinkOperator β) :=
  Classical.epsilon_spec (exists_hasKernel_of_continuous _
    ((continuous_singleBondWeight β).comp (continuous_fst.mul continuous_snd.inv)))
theorem singleLinkOperator_apply_of_mem (hC : HarmonicAnalysisFacts)
    (hW : TraceAndSingleBondWeight) (hβ : 0 < β) (l : HalfNatural)
    (ψ : Lp ℂ 2 haarProb) (hψ : ψ ∈ coeffSpanL2 l) :
    singleLinkOperator β ψ = weightCharCoeff β l • ψ := by
  obtain ⟨ψ₀, h₀, rfl⟩ := hψ
  change singleLinkOperator β (ContinuousMap.toLp (E := ℂ) 2 haarProb ℂ ψ₀) =
    weightCharCoeff β l • ContinuousMap.toLp (E := ℂ) 2 haarProb ℂ ψ₀
  have hI := hasKernel_singleLinkOperator β
    (ContinuousMap.toLp (E := ℂ) 2 haarProb ℂ ψ₀)
  have hc := ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) haarProb ψ₀
  have hsm := Lp.coeFn_smul (weightCharCoeff β l)
    (ContinuousMap.toLp (E := ℂ) 2 haarProb ℂ ψ₀)
  have hn : ((2 * l.toReal + 1 : ℝ) : ℂ) ≠ 0 := by
    rw [two_mul_toReal_add_one]
    exact_mod_cast (show (l.doubled : ℝ) + 1 ≠ 0 by positivity)
  have hk : ∀ g, kernelApply haarProb
      (fun p : specialUnitary × specialUnitary => singleBondWeight β (p.1 * p.2⁻¹))
      (ContinuousMap.toLp (E := ℂ) 2 haarProb ℂ ψ₀) g = weightCharCoeff β l * ψ₀ g := by
    intro g
    unfold kernelApply
    rw [integral_congr_ae (g := fun h => bondWeightFun β (g * h⁻¹) * ψ₀ h)
      (hc.mono fun h e => by simp only [bondWeightFun_apply]; rw [e])]
    rw [(hC l l).2.2.2.2.2.2.2 (bondWeightFun β) (bondWeightFun_isConjInvariant hW hβ) ψ₀ h₀ g,
      integral_star_spinCharacter_mul hC l, inv_mul_cancel_left₀ hn]
  refine Lp.ext (hI.trans ?_)
  filter_upwards [hsm, hc] with g h1 h2
  rw [hk, h1, Pi.smul_apply, h2, smul_eq_mul]
theorem singleLinkOpDiagonal_of_pos (hC : HarmonicAnalysisFacts)
    (hW : TraceAndSingleBondWeight) (hβ : 0 < β) :
    SingleLinkOpDiagonal β := by
  refine ⟨singleLinkOperator_apply_of_mem hC hW hβ, fun F => ?_⟩
  have hs := (singleLinkOperator β).hasSum ((hC ⟨0⟩ ⟨0⟩).2.1.hasSum_coeffProjection F)
  refine hs.congr_fun fun l => ?_
  exact (singleLinkOperator_apply_of_mem hC hW hβ l _
    ((coeffSpanL2 l).starProjection_apply_mem F)).symm
theorem weightCharCoeffBounds_of_pos (hC : HarmonicAnalysisFacts)
    (hW : TraceAndSingleBondWeight) (hβ : 0 < β) (l : HalfNatural) :
    WeightCharCoeffBounds β l := by
  have hv : ∀ t : HalfNatural, (weightCharCoeff β t).re = besselCoeffValue β t.doubled := by
    intro t
    rw [weightCharCoeff_eq hC hW hβ t, Complex.ofReal_re]
  have hvalue : l.toReal = (l.doubled : ℝ) / 2 := rfl
  have hI1 := modBesselI_pos (l.doubled + 1) hβ
  have hI2 := modBesselI_pos (l.doubled + 1 + 1) hβ
  have hcoef : 0 < 2 * Real.exp (-β) / β := by positivity
  have hdown : modBesselI (l.doubled + 1 + 1) β ≤
      (4 * (l.toReal + 1) / β + β) * modBesselI (l.doubled + 1) β := by
    have hs := modBesselI_succ_le (l.doubled + 1) hβ
    refine hs.trans (mul_le_mul_of_nonneg_right ?_ hI1.le)
    have h1 : β / (2 * (((l.doubled + 1 : ℕ) : ℝ) + 1)) ≤ β := by
      refine div_le_self hβ.le ?_
      push_cast
      linarith
    have h2 : 0 ≤ 4 * (l.toReal + 1) / β := by
      rw [hvalue]
      positivity
    linarith
  have hup : modBesselI (l.doubled + 1) β ≤
      (4 * (l.toReal + 1) / β + β) * modBesselI (l.doubled + 1 + 1) β := by
    have hr := modBesselI_sub_modBesselI_add_two (l.doubled + 1) hβ
    have hs := modBesselI_succ_le (l.doubled + 1 + 1) hβ
    have h1 : β / (2 * (((l.doubled + 1 + 1 : ℕ) : ℝ) + 1)) ≤ β := by
      refine div_le_self hβ.le ?_
      push_cast
      linarith
    have h3 : modBesselI (l.doubled + 1 + 2) β ≤ β * modBesselI (l.doubled + 1 + 1) β :=
      hs.trans (mul_le_mul_of_nonneg_right h1 hI2.le)
    have h4 : 2 * (((l.doubled + 1 : ℕ) : ℝ) + 1) / β = 4 * (l.toReal + 1) / β := by
      rw [hvalue]
      push_cast
      ring
    rw [h4] at hr
    nlinarith
  refine ⟨weightCharCoeff_eq hC hW hβ l, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hv]
    exact besselCoeffValue_pos hβ _
  · exact (Complex.re_le_norm _).trans (norm_weightCharCoeff_le hC hW hβ l)
  · rw [hv]
    unfold besselCoeffValue
    have hb := modBesselI_le (l.doubled + 1) hβ
    have hle : Real.exp (-β) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have hX : 0 ≤ (β / 2) ^ l.doubled * Real.exp (β ^ 2 / 4) /
        ((l.doubled + 1).factorial : ℝ) := by
      positivity
    calc 2 * Real.exp (-β) / β * modBesselI (l.doubled + 1) β
        ≤ 2 * Real.exp (-β) / β *
          ((β / 2) ^ (l.doubled + 1) / ((l.doubled + 1).factorial : ℝ) *
            Real.exp (β ^ 2 / 4)) :=
          mul_le_mul_of_nonneg_left hb hcoef.le
      _ = Real.exp (-β) *
          ((β / 2) ^ l.doubled * Real.exp (β ^ 2 / 4) / ((l.doubled + 1).factorial : ℝ)) := by
          rw [pow_succ]
          field_simp
      _ ≤ 1 * ((β / 2) ^ l.doubled * Real.exp (β ^ 2 / 4) /
          ((l.doubled + 1).factorial : ℝ)) :=
          mul_le_mul_of_nonneg_right hle hX
      _ = _ := one_mul _
  · rw [hv, hv]
    simp only [besselCoeffValue]
    refine max_le ?_ ?_
    · rw [mul_div_mul_left _ _ hcoef.ne', div_le_iff₀ hI1]
      exact hdown
    · rw [mul_div_mul_left _ _ hcoef.ne', div_le_iff₀ hI2]
      exact hup
  · unfold besselRatioBound
    have hv0 : 0 ≤ l.toReal := by
      rw [hvalue]
      positivity
    have : (4 / β + β) * (1 + l.toReal) - (4 * (l.toReal + 1) / β + β) = β * l.toReal := by
      field_simp
      ring
    nlinarith [mul_nonneg hβ.le hv0]
theorem four_le_besselRatioBound (hβ : 0 < β) : 4 ≤ besselRatioBound β := by
  unfold besselRatioBound
  have : 4 / β + β - 4 = (β - 2) ^ 2 / β := by
    field_simp
    ring
  have hsq : 0 ≤ (β - 2) ^ 2 / β := by positivity
  linarith
def coeffMajorant (β ς₁ ς₂ : ℝ) (n : ℕ) : ℝ :=
  ((n : ℝ) + 1) ^ ς₁ *
    ((β / 2) ^ n * Real.exp (β ^ 2 / 4) / ((n + 1).factorial : ℝ)) ^ ς₂
theorem summable_coeffMajorant (hβ : 0 < β) {ς₁ ς₂ : ℝ} (h₂ : 0 < ς₂) :
    Summable (coeffMajorant β ς₁ ς₂) := by
  have hA : ∀ n : ℕ, 0 < (β / 2) ^ n * Real.exp (β ^ 2 / 4) / ((n + 1).factorial : ℝ) := by
    intro n
    positivity
  have hpos : ∀ n, 0 < coeffMajorant β ς₁ ς₂ n := by
    intro n
    unfold coeffMajorant
    have h1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    exact mul_pos (Real.rpow_pos_of_pos h1 _) (Real.rpow_pos_of_pos (hA n) _)
  have hratio : ∀ n : ℕ, ‖coeffMajorant β ς₁ ς₂ (n + 1)‖ / ‖coeffMajorant β ς₁ ς₂ n‖ =
      (((n : ℝ) + 2) / ((n : ℝ) + 1)) ^ ς₁ * ((β / 2) / ((n : ℝ) + 2)) ^ ς₂ := by
    intro n
    rw [Real.norm_of_nonneg (hpos _).le, Real.norm_of_nonneg (hpos _).le]
    have h1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have h2 : (0 : ℝ) < (n : ℝ) + 2 := by positivity
    have hq : (0 : ℝ) < (β / 2) / ((n : ℝ) + 2) := by positivity
    have hAn : (β / 2) ^ (n + 1) * Real.exp (β ^ 2 / 4) / ((n + 1 + 1).factorial : ℝ) =
        ((β / 2) ^ n * Real.exp (β ^ 2 / 4) / ((n + 1).factorial : ℝ)) *
          ((β / 2) / ((n : ℝ) + 2)) := by
      rw [Nat.factorial_succ (n + 1), pow_succ]
      have hf : ((n + 1).factorial : ℝ) ≠ 0 := by positivity
      push_cast
      field_simp
      ring
    have hn2 : (((n + 1 : ℕ) : ℝ) + 1) = ((n : ℝ) + 1) * (((n : ℝ) + 2) / ((n : ℝ) + 1)) := by
      push_cast
      field_simp
      ring
    unfold coeffMajorant
    rw [hAn, hn2, Real.mul_rpow h1.le (by positivity), Real.mul_rpow (hA n).le hq.le]
    have e1 : ((n : ℝ) + 1) ^ ς₁ ≠ 0 := (Real.rpow_pos_of_pos h1 _).ne'
    have e2 : ((β / 2) ^ n * Real.exp (β ^ 2 / 4) / ((n + 1).factorial : ℝ)) ^ ς₂ ≠ 0 :=
      (Real.rpow_pos_of_pos (hA n) _).ne'
    field_simp
  have hlim : Tendsto (fun n : ℕ => (((n : ℝ) + 2) / ((n : ℝ) + 1)) ^ ς₁ *
      ((β / 2) / ((n : ℝ) + 2)) ^ ς₂) atTop (𝓝 0) := by
    have t1 : Tendsto (fun n : ℕ => ((n : ℝ) + 2) / ((n : ℝ) + 1)) atTop (𝓝 1) := by
      have ht : Tendsto (fun n : ℕ => 1 + 1 / ((n : ℝ) + 1)) atTop (𝓝 (1 + 0)) :=
        tendsto_const_nhds.add tendsto_one_div_add_atTop_nhds_zero_nat
      rw [add_zero] at ht
      refine ht.congr fun n => ?_
      have : (n : ℝ) + 1 ≠ 0 := by positivity
      field_simp
      ring
    have t2 : Tendsto (fun n : ℕ => (β / 2) / ((n : ℝ) + 2)) atTop (𝓝 0) := by
      refine Tendsto.div_atTop tendsto_const_nhds ?_
      exact tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
    have u1 := t1.rpow_const (p := ς₁) (Or.inl one_ne_zero)
    have u2 := t2.rpow_const (p := ς₂) (Or.inr h₂.le)
    have := u1.mul u2
    rwa [Real.zero_rpow h₂.ne', mul_zero] at this
  exact summable_of_ratio_test_tendsto_lt_one (l := 0) zero_lt_one
    (Eventually.of_forall fun n => (hpos n).ne')
    (hlim.congr fun n => (hratio n).symm)
def natEquivHalfNatural : ℕ ≃ HalfNatural where
  toFun n := ⟨n⟩
  invFun l := l.doubled
  left_inv _ := rfl
  right_inv _ := rfl
theorem weightCharCoeffSummable_of_pos (hC : HarmonicAnalysisFacts)
    (hW : TraceAndSingleBondWeight) (hβ : 0 < β) :
    WeightCharCoeffSummable β := by
  intro ς₁ ς₂ h₁ h₂
  rw [← natEquivHalfNatural.summable_iff]
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_)
    (summable_coeffMajorant (ς₁ := ς₁) hβ h₂)
  · have hb := weightCharCoeffBounds_of_pos hC hW hβ (natEquivHalfNatural n)
    simp only [Function.comp]
    have h1 : (0 : ℝ) ≤ 2 * (natEquivHalfNatural n).toReal + 1 := by
      rw [two_mul_toReal_add_one]
      positivity
    exact mul_nonneg (Real.rpow_nonneg h1 _) (Real.rpow_nonneg hb.2.1.le _)
  · have hb := weightCharCoeffBounds_of_pos hC hW hβ (natEquivHalfNatural n)
    simp only [Function.comp]
    rw [two_mul_toReal_add_one]
    unfold coeffMajorant
    have h1 : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow hb.2.1.le hb.2.2.2.1 h₂.le) (Real.rpow_nonneg h1 _)
def charExpansionTerm (β : ℝ) (l : HalfNatural) : C(specialUnitary, ℂ) :=
  (((2 * l.toReal + 1 : ℝ) : ℂ) * weightCharCoeff β l) • spinCharacter l
theorem summable_norm_charExpansionTerm (hC : HarmonicAnalysisFacts)
    (hW : TraceAndSingleBondWeight) (hβ : 0 < β) :
    Summable fun l => ‖charExpansionTerm β l‖ := by
  have hs := weightCharCoeffSummable_of_pos hC hW hβ 2 1 (by norm_num) one_pos
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun l => ?_) hs
  have hb := weightCharCoeffBounds_of_pos hC hW hβ l
  have hpos : (0 : ℝ) ≤ 2 * l.toReal + 1 := by
    rw [two_mul_toReal_add_one]
    positivity
  have hnorm : ‖weightCharCoeff β l‖ = (weightCharCoeff β l).re := by
    rw [weightCharCoeff_eq hC hW hβ l, Complex.ofReal_re, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (besselCoeffValue_pos hβ _)]
  have hchar : ‖spinCharacter l‖ ≤ 2 * l.toReal + 1 :=
    (ContinuousMap.norm_le _ hpos).mpr (hC l l).2.2.1.norm_le
  unfold charExpansionTerm
  rw [norm_smul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hpos, hnorm,
    Real.rpow_one, Real.rpow_two]
  calc (2 * l.toReal + 1) * (weightCharCoeff β l).re * ‖spinCharacter l‖
      ≤ (2 * l.toReal + 1) * (weightCharCoeff β l).re * (2 * l.toReal + 1) :=
        mul_le_mul_of_nonneg_left hchar (mul_nonneg hpos hb.2.1.le)
    _ = _ := by ring
theorem hasSum_charExpansionTerm (hC : HarmonicAnalysisFacts)
    (hW : TraceAndSingleBondWeight) (hβ : 0 < β) :
    HasSum (charExpansionTerm β) (bondWeightFun β) := by
  have hsum : Summable (charExpansionTerm β) :=
    (summable_norm_charExpansionTerm hC hW hβ).of_norm
  have hS := hsum.hasSum
  have hL := (ContinuousMap.toLp (E := ℂ) 2 haarProb ℂ).hasSum hS
  have hF : MemLp (bondWeightFun β) 2 haarProb :=
    MemLp.of_bound (bondWeightFun β).continuous.aestronglyMeasurable 1
      (Eventually.of_forall fun g => norm_singleBondWeight_le hW hβ g)
  have hZ : hF.toLp (bondWeightFun β) =
      ContinuousMap.toLp (E := ℂ) 2 haarProb ℂ (bondWeightFun β) :=
    Lp.ext (hF.coeFn_toLp.trans (ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) haarProb _).symm)
  have hproj : ∀ l, ContinuousMap.toLp (E := ℂ) 2 haarProb ℂ (charExpansionTerm β l) =
      coeffProjection l (ContinuousMap.toLp (E := ℂ) 2 haarProb ℂ (bondWeightFun β)) := by
    intro l
    rw [← hZ, (hC l l).2.2.2.2.1.apply_of_isConjInvariant (bondWeightFun β)
      (bondWeightFun β).continuous.measurable (bondWeightFun_isConjInvariant hW hβ) hF,
      integral_star_spinCharacter_mul hC l]
    unfold charExpansionTerm
    rw [map_smul]
  have hP := (hC ⟨0⟩ ⟨0⟩).2.1.hasSum_coeffProjection
    (ContinuousMap.toLp (E := ℂ) 2 haarProb ℂ (bondWeightFun β))
  have hU := (hL.congr_fun fun l => (hproj l).symm).unique hP
  have hopen : (haarProb : Measure specialUnitary).IsOpenPosMeasure := by
    unfold haarProb
    infer_instance
  have hEq := ContinuousMap.toLp_injective (p := 2) (𝕜 := ℂ) (E := ℂ)
    (haarProb : Measure specialUnitary) hU
  rw [← hEq]
  exact hS
theorem bondWeightCharExpansion_of_pos (hC : HarmonicAnalysisFacts)
    (hW : TraceAndSingleBondWeight) (hβ : 0 < β) :
    BondWeightCharExpansion β := by
  refine ⟨fun g => ?_, ?_⟩
  · refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun l => ?_)
      (summable_norm_charExpansionTerm hC hW hβ)
    exact (charExpansionTerm β l).norm_coe_le_norm g
  · have hT : Tendsto (fun s : Finset HalfNatural => ∑ b ∈ s, charExpansionTerm β b) atTop
        (𝓝 (bondWeightFun β)) := by
      have hs := hasSum_charExpansionTerm hC hW hβ
      rwa [HasSum, SummationFilter.unconditional_filter] at hs
    have hu := ContinuousMap.tendsto_iff_tendstoUniformly.mp hT
    have e : (fun (s : Finset HalfNatural) (g : specialUnitary) =>
        ∑ l ∈ s, bondWeightCharTerm β l g) =
        fun s g => (∑ b ∈ s, charExpansionTerm β b) g := by
      funext s g
      rw [ContinuousMap.sum_apply]
      refine Finset.sum_congr rfl fun l _ => ?_
      simp [charExpansionTerm, bondWeightCharTerm]
    rw [e]
    exact hu
end PositiveCoupling
theorem bondWeightCharCoeffStatement_holds (hC : HarmonicAnalysisFacts)
    (hW : TraceAndSingleBondWeight) :
    BondWeightCharCoeffStatement := by
  refine ⟨fun n z hz => ⟨hasSum_besselSeriesTerm n z, modBesselI_pos n hz, fun hn => ?_,
    modBesselI_succ_le n hz, modBesselI_le n hz⟩, fun β hβ =>
    ⟨singleLinkOpDiagonal_of_pos hC hW hβ, weightCharCoeffBounds_of_pos hC hW hβ,
      four_le_besselRatioBound hβ, weightCharCoeffSummable_of_pos hC hW hβ,
      bondWeightCharExpansion_of_pos hC hW hβ⟩⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have := modBesselI_sub_modBesselI_add_two m hz
  simpa using this
end YangMills.Construction.SpinHarmonics.BondWeightCoeffs
end
