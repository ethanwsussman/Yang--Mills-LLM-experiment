import YangMills.Construction.Lattice.SpreadOfAContourFamilyProof
import YangMills.Construction.ColdChainAtEveryLevel.SecondVariationOfAFitInTheChartProof
import YangMills.Construction.Matrices.ExpLogEstimates
import YangMills.Construction.Matrices.NormExpLogBasics
import YangMills.Construction.Matrices.RepresentationsFieldsAndSmoothFunctionsOnG
import YangMills.Construction.Matrices.UnitaryLogarithmClosedForm
import YangMills.Construction.Numerics.ExpLogNumericBounds
import Mathlib
open scoped Matrix.Norms.L2Operator
open Filter Topology MeasureTheory
noncomputable section
namespace YangMills.Construction.Matrices.ComplexMatrix2.ExpLogEstimates
instance completeSpace : CompleteSpace ComplexMatrix2 := FiniteDimensional.complete ℂ ComplexMatrix2
theorem hasSum_expSeries_matExp (Z : ComplexMatrix2) :
    HasSum (fun n : ℕ => ((n.factorial : ℂ)⁻¹) • Z ^ n) (matExp Z) :=
  NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) Z
theorem hasSum_pow_div_factorial_realExp (x : ℝ) :
    HasSum (fun n : ℕ => x ^ n / (n.factorial : ℝ)) (Real.exp x) := by apply _root_.YangMills.Construction.BlockAverages.ChartFit.hasSum_pow_div_factorial <;> assumption
theorem norm_natCast_inv_smul (c : ℕ) (X : ComplexMatrix2) :
    ‖((c : ℂ)⁻¹) • X‖ = ‖X‖ / (c : ℝ) := by
  rw [norm_smul, norm_inv, Complex.norm_natCast, div_eq_inv_mul]
theorem norm_le_of_hasSum_of_bound {f : ℕ → ComplexMatrix2} {S : ComplexMatrix2} {g : ℕ → ℝ} {a : ℝ}
    (hf : HasSum f S) (hg : HasSum g a) (h : ∀ n, ‖f n‖ ≤ g n) : ‖S‖ ≤ a := by
  rw [← hf.tsum_eq]
  exact tsum_of_norm_bounded hg h
theorem hasSum_matExp_sub_one (Z : ComplexMatrix2) :
    HasSum (fun n : ℕ => (((n + 1).factorial : ℂ)⁻¹) • Z ^ (n + 1)) (matExp Z - 1) := by
  have h := (hasSum_nat_add_iff' 1).2 (hasSum_expSeries_matExp Z)
  simpa using h
theorem hasSum_realExp_sub_one (x : ℝ) :
    HasSum (fun n : ℕ => x ^ (n + 1) / ((n + 1).factorial : ℝ)) (Real.exp x - 1) := by
  have h := (hasSum_nat_add_iff' 1).2 (hasSum_pow_div_factorial_realExp x)
  simpa using h
theorem norm_matExp_le (Z : ComplexMatrix2) : ‖matExp Z‖ ≤ Real.exp ‖Z‖ := by
  refine norm_le_of_hasSum_of_bound (hasSum_expSeries_matExp Z)
    (hasSum_pow_div_factorial_realExp ‖Z‖) fun n => ?_
  rw [norm_natCast_inv_smul]
  gcongr
  exact norm_pow_le Z n
theorem norm_matExp_sub_one_le (Z : ComplexMatrix2) : ‖matExp Z - 1‖ ≤ Real.exp ‖Z‖ - 1 := by
  refine norm_le_of_hasSum_of_bound (hasSum_matExp_sub_one Z) (hasSum_realExp_sub_one ‖Z‖)
    fun n => ?_
  rw [norm_natCast_inv_smul]
  gcongr
  exact norm_pow_le Z _
theorem norm_pow_succ_sub_pow_succ_le {Z Z' : ComplexMatrix2} {r : ℝ} (hZ : ‖Z‖ ≤ r)
    (hZ' : ‖Z'‖ ≤ r) (n : ℕ) :
    ‖Z ^ (n + 1) - Z' ^ (n + 1)‖ ≤ ((n : ℝ) + 1) * r ^ n * ‖Z - Z'‖ := by
  have hr : 0 ≤ r := (norm_nonneg Z).trans hZ
  induction n with
  | zero => simp
  | succ n ih =>
    have key : Z ^ (n + 1 + 1) - Z' ^ (n + 1 + 1)
        = Z ^ (n + 1) * (Z - Z') + (Z ^ (n + 1) - Z' ^ (n + 1)) * Z' := by
      rw [pow_succ Z (n + 1), pow_succ Z' (n + 1)]
      noncomm_ring
    have h1 : ‖Z ^ (n + 1) * (Z - Z')‖ ≤ r ^ (n + 1) * ‖Z - Z'‖ :=
      (norm_mul_le _ _).trans (by
        gcongr
        exact (norm_pow_le Z _).trans (by gcongr))
    have h2 : ‖(Z ^ (n + 1) - Z' ^ (n + 1)) * Z'‖ ≤ ((n : ℝ) + 1) * r ^ n * ‖Z - Z'‖ * r :=
      (norm_mul_le _ _).trans (by gcongr)
    rw [key]
    refine (norm_add_le _ _).trans ((add_le_add h1 h2).trans (le_of_eq ?_))
    push_cast
    ring
theorem hasSum_matExp_sub_matExp (Z Z' : ComplexMatrix2) :
    HasSum (fun n : ℕ => (((n + 1).factorial : ℂ)⁻¹) • (Z ^ (n + 1) - Z' ^ (n + 1)))
      (matExp Z - matExp Z') := by
  have h := (hasSum_matExp_sub_one Z).sub (hasSum_matExp_sub_one Z')
  simpa [smul_sub] using h
theorem norm_matExp_sub_matExp_le {Z Z' : ComplexMatrix2} {r : ℝ} (hZ : ‖Z‖ ≤ r) (hZ' : ‖Z'‖ ≤ r) :
    ‖matExp Z - matExp Z'‖ ≤ Real.exp r * ‖Z - Z'‖ := by
  refine norm_le_of_hasSum_of_bound (hasSum_matExp_sub_matExp Z Z')
    ((hasSum_pow_div_factorial_realExp r).mul_right _) fun n => ?_
  rw [norm_natCast_inv_smul]
  rw [div_le_iff₀ (by exact_mod_cast (n + 1).factorial_pos), Nat.factorial_succ]
  refine (norm_pow_succ_sub_pow_succ_le hZ hZ' n).trans (le_of_eq ?_)
  push_cast
  field_simp
theorem norm_matExp_sub_matExp_sub_le {Z Z' : ComplexMatrix2} {r : ℝ} (hZ : ‖Z‖ ≤ r)
    (hZ' : ‖Z'‖ ≤ r) :
    ‖matExp Z - matExp Z' - (Z - Z')‖ ≤ (Real.exp r - 1) * ‖Z - Z'‖ := by
  have h := (hasSum_nat_add_iff' 1).2 (hasSum_matExp_sub_matExp Z Z')
  have h' : HasSum (fun n : ℕ => (((n + 1 + 1).factorial : ℂ)⁻¹) •
      (Z ^ (n + 1 + 1) - Z' ^ (n + 1 + 1))) (matExp Z - matExp Z' - (Z - Z')) := by
    simpa using h
  refine norm_le_of_hasSum_of_bound h' ((hasSum_realExp_sub_one r).mul_right _) fun n => ?_
  rw [norm_natCast_inv_smul]
  rw [div_le_iff₀ (by exact_mod_cast (n + 1 + 1).factorial_pos), Nat.factorial_succ (n + 1)]
  refine (norm_pow_succ_sub_pow_succ_le hZ hZ' (n + 1)).trans (le_of_eq ?_)
  push_cast
  field_simp
theorem norm_mul_matExp_sub_one_le (W Z : ComplexMatrix2) :
    ‖W * matExp Z - 1‖ ≤ (1 + ‖W - 1‖) * Real.exp ‖Z‖ - 1 := by
  have key : W * matExp Z - 1 = (W - 1) * matExp Z + (matExp Z - 1) := by noncomm_ring
  rw [key]
  have h1 : ‖(W - 1) * matExp Z‖ ≤ ‖W - 1‖ * Real.exp ‖Z‖ :=
    (norm_mul_le _ _).trans (by gcongr; exact norm_matExp_le Z)
  have h2 := norm_matExp_sub_one_le Z
  refine (norm_add_le _ _).trans ((add_le_add h1 h2).trans (le_of_eq ?_))
  ring
theorem isUnit_one_add_of_norm_lt_one {E : ComplexMatrix2} (h : ‖E‖ < 1) : IsUnit (1 + E) := by
  have := isUnit_one_sub_of_norm_lt_one (x := -E) (by simpa using h)
  simpa using this
theorem one_add_mul_inv {E : ComplexMatrix2} (h : ‖E‖ < 1) : (1 + E) * (1 + E)⁻¹ = 1 :=
  Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 (isUnit_one_add_of_norm_lt_one h))
theorem inv_mul_one_add {E : ComplexMatrix2} (h : ‖E‖ < 1) : (1 + E)⁻¹ * (1 + E) = 1 :=
  Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 (isUnit_one_add_of_norm_lt_one h))
theorem norm_inv_one_add_le {E : ComplexMatrix2} (h : ‖E‖ < 1) :
    ‖(1 + E)⁻¹‖ ≤ 1 / (1 - ‖E‖) := by
  have key : (1 + E)⁻¹ = 1 - (1 + E)⁻¹ * E := by
    have := inv_mul_one_add h
    rw [mul_add, mul_one] at this
    exact eq_sub_of_add_eq this
  have hb : ‖(1 + E)⁻¹‖ ≤ 1 + ‖(1 + E)⁻¹‖ * ‖E‖ := by
    conv_lhs => rw [key]
    refine (norm_sub_le _ _).trans ?_
    rw [norm_one]
    gcongr
    exact norm_mul_le _ _
  rw [le_div_iff₀ (by linarith)]
  nlinarith
theorem norm_inv_one_add_sub_one_le {E : ComplexMatrix2} (h : ‖E‖ < 1) :
    ‖(1 + E)⁻¹ - 1‖ ≤ ‖E‖ / (1 - ‖E‖) := by
  have key : (1 + E)⁻¹ - 1 = -((1 + E)⁻¹ * E) := by
    have := inv_mul_one_add h
    rw [mul_add, mul_one] at this
    rw [sub_eq_iff_eq_add, neg_add_eq_sub]
    exact eq_sub_of_add_eq this
  rw [key, norm_neg]
  refine (norm_mul_le _ _).trans ?_
  have := norm_inv_one_add_le h
  calc ‖(1 + E)⁻¹‖ * ‖E‖ ≤ 1 / (1 - ‖E‖) * ‖E‖ := by gcongr
    _ = ‖E‖ / (1 - ‖E‖) := by ring
theorem hasSum_neg_pow_inv_one_add {E : ComplexMatrix2} (h : ‖E‖ < 1) :
    HasSum (fun n : ℕ => (-E) ^ n) (1 + E)⁻¹ := by
  have hn : ‖-E‖ < 1 := by simpa using h
  have hs : Summable (fun n : ℕ => (-E) ^ n) := summable_geometric_of_norm_lt_one hn
  have hm := mul_neg_geom_series (-E) hn
  have : (1 + E)⁻¹ = ∑' n : ℕ, (-E) ^ n := by
    refine Matrix.inv_eq_right_inv ?_
    simpa using hm
  rw [this]
  exact hs.hasSum
theorem continuousAt_inv_one_add_smul {E : ComplexMatrix2} {t : ℝ} (h : |t| * ‖E‖ < 1) :
    ContinuousAt (fun s : ℝ => (1 + (s : ℂ) • E)⁻¹) t := by
  have hE : ‖(t : ℂ) • E‖ < 1 := by simpa [norm_smul] using h
  obtain ⟨u, hu⟩ := isUnit_one_add_of_norm_lt_one hE
  have hc : ContinuousAt (fun s : ℝ => 1 + (s : ℂ) • E) t := by fun_prop
  have hi := NormedRing.inverse_continuousAt u
  rw [hu] at hi
  simp only [Matrix.nonsing_inv_eq_ringInverse]
  exact ContinuousAt.comp (f := fun s : ℝ => 1 + (s : ℂ) • E) hi hc
theorem integral_neg_ofReal_pow (t : ℝ) (n : ℕ) :
    ∫ s in (0 : ℝ)..t, (-(s : ℂ)) ^ n = -((n + 1 : ℂ)⁻¹ * (-(t : ℂ)) ^ (n + 1)) := by
  have h : ∀ s : ℝ, (-(s : ℂ)) ^ n = (((-1) ^ n * s ^ n : ℝ) : ℂ) := by
    intro s
    push_cast
    rw [neg_pow]
  simp only [h]
  rw [intervalIntegral.integral_ofReal, intervalIntegral.integral_const_mul, integral_pow]
  push_cast
  rw [neg_pow (t : ℂ) (n + 1), pow_succ (-1 : ℂ) n]
  simp
  ring
theorem logSeries_one_add_smul_eq_integral {E : ComplexMatrix2} {t : ℝ} (h : |t| * ‖E‖ < 1) :
    logSeries (1 + (t : ℂ) • E) = ∫ s in (0 : ℝ)..t, E * (1 + (s : ℂ) • E)⁻¹ := by
  set a : ℝ := |t| * ‖E‖ with ha
  have ha0 : 0 ≤ a := by positivity
  have hs_in : ∀ s ∈ Set.uIoc (0 : ℝ) t, |s| ≤ |t| := by
    intro s hs
    rcases Set.mem_uIoc.1 hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [abs_of_pos h1]; exact h2.trans (le_abs_self _)
    · rw [abs_le]
      have : |t| = -t := abs_of_neg (lt_of_lt_of_le h1 h2)
      rw [this]; constructor <;> linarith
  have hsum := intervalIntegral.hasSum_integral_of_dominated_convergence (μ := volume)
    (a := (0 : ℝ)) (b := t)
    (F := fun (n : ℕ) (s : ℝ) => (-(s : ℂ)) ^ n • E ^ (n + 1))
    (f := fun s : ℝ => E * (1 + (s : ℂ) • E)⁻¹)
    (fun n _ => a ^ n * ‖E‖)
    (fun n => by
      apply Continuous.aestronglyMeasurable
      fun_prop)
    (fun n => ae_of_all _ fun s hs => by
      rw [norm_smul, norm_pow, norm_neg, Complex.norm_real, Real.norm_eq_abs]
      have hs' := hs_in s hs
      calc |s| ^ n * ‖E ^ (n + 1)‖ ≤ |t| ^ n * ‖E‖ ^ (n + 1) := by
            gcongr
            exact norm_pow_le E _
        _ = a ^ n * ‖E‖ := by rw [ha, mul_pow, pow_succ]; ring)
    (ae_of_all _ fun s _ => (summable_geometric_of_lt_one ha0 h).mul_right _)
    (by simp)
    (ae_of_all _ fun s hs => by
      have hs' := hs_in s hs
      have hn : ‖(s : ℂ) • E‖ < 1 := by
        rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
        exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hs' (norm_nonneg _)) h
      have := (hasSum_neg_pow_inv_one_add hn).mul_left E
      have heq : (fun n : ℕ => E * (-((s : ℂ) • E)) ^ n)
          = fun n : ℕ => (-(s : ℂ)) ^ n • E ^ (n + 1) := by
        funext n
        rw [← neg_smul, smul_pow, mul_smul_comm, pow_succ' E n]
      rwa [heq] at this)
  have hterm : (fun n : ℕ => -∫ s in (0 : ℝ)..t, (-(s : ℂ)) ^ n • E ^ (n + 1))
      = fun n : ℕ => ((n + 1 : ℂ)⁻¹) • (1 - (1 + (t : ℂ) • E)) ^ (n + 1) := by
    funext n
    rw [intervalIntegral.integral_smul_const, integral_neg_ofReal_pow, neg_smul, neg_neg, mul_smul]
    congr 1
    rw [sub_add_cancel_left, ← neg_smul, smul_pow]
  have hfin := hsum.neg
  rw [hterm] at hfin
  rw [logSeries, hfin.tsum_eq, neg_neg]
theorem matExp_add_of_commute {X Y : ComplexMatrix2} (h : Commute X Y) :
    matExp (X + Y) = matExp X * matExp Y :=
  Matrix.exp_add_of_commute X Y h
theorem norm_logSeries_one_add_le {E : ComplexMatrix2} (h : ‖E‖ < 1) :
    ‖logSeries (1 + E)‖ ≤ -Real.log (1 - ‖E‖) := by
  have hg := Real.hasSum_pow_div_log_of_abs_lt_one (x := ‖E‖) (by
    rwa [abs_of_nonneg (norm_nonneg E)])
  rw [logSeries, norm_neg]
  refine tsum_of_norm_bounded hg fun n => ?_
  have hc : ‖((n + 1 : ℂ)⁻¹)‖ = ((n : ℝ) + 1)⁻¹ := by
    rw [norm_inv]
    congr 1
    exact_mod_cast Complex.norm_natCast (n + 1)
  rw [norm_smul, hc, div_eq_inv_mul, sub_add_cancel_left]
  gcongr
  simpa using norm_pow_le (-E) (n + 1)
theorem neg_log_one_sub_le {t : ℝ} (h1 : t < 1) : -Real.log (1 - t) ≤ t / (1 - t) := by
  have hp : 0 < 1 - t := by linarith
  have := Real.one_sub_inv_le_log_of_pos hp
  have he : t / (1 - t) = (1 - t)⁻¹ - 1 := by field_simp; ring
  rw [he]
  linarith
theorem commute_logSeries {X Y : ComplexMatrix2} (h : Commute Y X) : Commute Y (logSeries X) := by
  rw [logSeries]
  refine Commute.neg_right (Commute.tsum_right Y fun n => ?_)
  exact (((Commute.one_right Y).sub_right h).pow_right _).smul_right _
theorem continuousOn_inv_one_add_smul {E : ComplexMatrix2} :
    ContinuousOn (fun s : ℝ => (1 + (s : ℂ) • E)⁻¹) {s : ℝ | |s| * ‖E‖ < 1} :=
  fun _ hs => (continuousAt_inv_one_add_smul hs).continuousWithinAt
theorem isOpen_abs_mul_norm_lt_one (E : ComplexMatrix2) : IsOpen {s : ℝ | |s| * ‖E‖ < 1} :=
  isOpen_lt (by fun_prop) continuous_const
theorem uIcc_subset_abs_mul_norm_lt_one {E : ComplexMatrix2} {t : ℝ} (h : |t| * ‖E‖ < 1) :
    Set.uIcc 0 t ⊆ {s : ℝ | |s| * ‖E‖ < 1} := by
  intro s hs
  have hs' : |s| ≤ |t| := by
    have := Set.abs_sub_left_of_mem_uIcc hs
    simpa using this
  exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hs' (norm_nonneg _)) h
theorem hasDerivAt_logSeries_one_add_smul {E : ComplexMatrix2} {t : ℝ} (h : |t| * ‖E‖ < 1) :
    HasDerivAt (fun s : ℝ => logSeries (1 + (s : ℂ) • E)) (E * (1 + (t : ℂ) • E)⁻¹) t := by
  have hc : ContinuousOn (fun s : ℝ => E * (1 + (s : ℂ) • E)⁻¹) {s : ℝ | |s| * ‖E‖ < 1} :=
    continuousOn_const.mul continuousOn_inv_one_add_smul
  have hI : IntervalIntegrable (fun s : ℝ => E * (1 + (s : ℂ) • E)⁻¹) volume 0 t :=
    (hc.mono (uIcc_subset_abs_mul_norm_lt_one h)).intervalIntegrable
  have hd := intervalIntegral.integral_hasDerivAt_right hI
    (hc.stronglyMeasurableAtFilter (isOpen_abs_mul_norm_lt_one E) t h)
    (hc.continuousAt ((isOpen_abs_mul_norm_lt_one E).mem_nhds h))
  refine hd.congr_of_eventuallyEq ?_
  filter_upwards [(isOpen_abs_mul_norm_lt_one E).mem_nhds h] with s hs
  exact logSeries_one_add_smul_eq_integral hs
theorem hasDerivAt_matExp_of_commute {L : ℝ → ComplexMatrix2} {L' : ComplexMatrix2} {t : ℝ}
    (hL : HasDerivAt L L' t) (hc : ∀ s, Commute (L t) (L s)) :
    HasDerivAt (fun s => matExp (L s)) (matExp (L t) * L') t := by
  have h0 : HasDerivAt (fun s => L s - L t) L' t := hL.sub_const _
  have he : HasFDerivAt (matExp : ComplexMatrix2 → ComplexMatrix2)
      (1 : ComplexMatrix2 →L[ℂ] ComplexMatrix2) 0 := hasFDerivAt_exp_zero
  have he' := he.restrictScalars ℝ
  have h1 : HasFDerivAt (matExp : ComplexMatrix2 → ComplexMatrix2)
      ((1 : ComplexMatrix2 →L[ℂ] ComplexMatrix2).restrictScalars ℝ)
      ((fun s => L s - L t) t) := by simpa using he'
  have h2 := h1.comp_hasDerivAt t h0
  have h3 := h2.const_mul (matExp (L t))
  have hfun : (fun s => matExp (L t) * ((matExp ∘ fun s => L s - L t) s))
      = fun s => matExp (L s) := by
    funext s
    have : Commute (L t) (L s - L t) := (hc s).sub_right (Commute.refl _)
    simp only [Function.comp]
    rw [← matExp_add_of_commute this, add_sub_cancel]
  rw [hfun] at h3
  simpa using h3
theorem commute_one_add_smul (E : ComplexMatrix2) (s t : ℂ) : Commute (1 + s • E) (1 + t • E) :=
  (Commute.one_left _).add_left
    ((Commute.one_right _).add_right (((Commute.refl E).smul_left _).smul_right _))
theorem logSeries_one : logSeries (1 : ComplexMatrix2) = 0 := by simp [logSeries]
theorem matExp_zero : matExp (0 : ComplexMatrix2) = 1 := NormedSpace.exp_zero
theorem matExp_mul_matExp_neg (X : ComplexMatrix2) : matExp X * matExp (-X) = 1 := by apply _root_.YangMills.Construction.SpinHarmonics.matExp_mul_matExp_neg <;> assumption
theorem matExp_logSeries_one_add {E : ComplexMatrix2} (h : ‖E‖ < 1) :
    matExp (logSeries (1 + E)) = 1 + E := by
  set L : ℝ → ComplexMatrix2 := fun s => logSeries (1 + (s : ℂ) • E) with hLdef
  set g : ℝ → ComplexMatrix2 := fun s => matExp (-L s) * (1 + (s : ℂ) • E) with hg
  have hpath : ∀ t ∈ Set.Icc (0 : ℝ) 1, |t| * ‖E‖ < 1 := by
    intro t ht
    rw [abs_of_nonneg ht.1]
    nlinarith [ht.1, ht.2, norm_nonneg E]
  have hd : ∀ t : ℝ, |t| * ‖E‖ < 1 → HasDerivAt g 0 t := by
    intro t ht
    have hL : HasDerivAt (fun s => -L s) (-(E * (1 + (t : ℂ) • E)⁻¹)) t :=
      (hasDerivAt_logSeries_one_add_smul ht).neg
    have hexp := hasDerivAt_matExp_of_commute hL (fun s =>
      (commute_logSeries (commute_logSeries (commute_one_add_smul E _ _).symm).symm).neg_left.neg_right)
    have hlin : HasDerivAt (fun s : ℝ => 1 + (s : ℂ) • E) E t := by
      have h1 : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 t := (hasDerivAt_id t).ofReal_comp
      have := (h1.smul_const E).const_add 1
      simpa using this
    have hmul := hexp.mul hlin
    have hz : matExp (-L t) * -(E * (1 + (t : ℂ) • E)⁻¹) * (1 + (t : ℂ) • E)
        + matExp (-L t) * E = 0 := by
      have hn : ‖(t : ℂ) • E‖ < 1 := by simpa [norm_smul] using ht
      have hr := inv_mul_one_add hn
      rw [mul_assoc, neg_mul, mul_assoc, hr, mul_one, mul_neg, neg_add_cancel]
    rw [hz] at hmul
    exact hmul
  have hconst := constant_of_has_deriv_right_zero (f := g) (a := 0) (b := 1)
    (fun t ht => (hd t (hpath t ht)).continuousAt.continuousWithinAt)
    (fun t ht => (hd t (hpath t ⟨ht.1, ht.2.le⟩)).hasDerivWithinAt)
    1 (by simp)
  have h0 : g 0 = 1 := by simp [hg, hLdef, logSeries_one]
  have h1 : g 1 = matExp (-logSeries (1 + E)) * (1 + E) := by simp [hg, hLdef]
  rw [h1, h0] at hconst
  calc matExp (logSeries (1 + E))
        = matExp (logSeries (1 + E)) * (matExp (-logSeries (1 + E)) * (1 + E)) := by
        rw [hconst, mul_one]
    _ = 1 + E := by rw [← mul_assoc, matExp_mul_matExp_neg, one_mul]
theorem mul_inv_one_add_sub_mul_inv_one_add {E F : ComplexMatrix2} {c : ℂ} (hE : ‖c • E‖ < 1)
    (hF : ‖c • F‖ < 1) :
    E * (1 + c • E)⁻¹ - F * (1 + c • F)⁻¹ = (1 + c • E)⁻¹ * (E - F) * (1 + c • F)⁻¹ := by
  have hRP := inv_mul_one_add hE
  have hPR := one_add_mul_inv hE
  have hQR := one_add_mul_inv hF
  set R := (1 + c • E)⁻¹
  set R' := (1 + c • F)⁻¹
  have hcomm : (1 + c • E) * E = E * (1 + c • E) := by
    rw [add_mul, mul_add, one_mul, mul_one, smul_mul_assoc, mul_smul_comm]
  have hER : E * R = R * E := by
    calc E * R = (R * (1 + c • E)) * E * R := by rw [hRP, one_mul]
      _ = R * ((1 + c • E) * E) * R := by noncomm_ring
      _ = R * E * ((1 + c • E) * R) := by rw [hcomm]; noncomm_ring
      _ = R * E := by rw [hPR, mul_one]
  have hmid : E * (1 + c • F) - (1 + c • E) * F = E - F := by
    rw [add_mul, mul_add, one_mul, mul_one, smul_mul_assoc, mul_smul_comm]
    abel
  calc E * R - F * R' = R * E * ((1 + c • F) * R') - (R * (1 + c • E)) * F * R' := by
        rw [hQR, hRP, hER, mul_one, one_mul]
    _ = R * (E * (1 + c • F) - (1 + c • E) * F) * R' := by noncomm_ring
    _ = R * (E - F) * R' := by rw [hmid]
theorem norm_smul_le_and_lt_one {E : ComplexMatrix2} {ε s : ℝ} (hE : ‖E‖ ≤ ε) (hε : ε < 1)
    (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    ‖(s : ℂ) • E‖ ≤ s * ε ∧ s * ε < 1 := by
  have h0 : 0 ≤ ε := (norm_nonneg E).trans hE
  refine ⟨?_, by nlinarith [hs.1, hs.2]⟩
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs.1]
  gcongr
  exact hs.1
theorem norm_inv_one_add_smul_le {E : ComplexMatrix2} {ε s : ℝ} (hE : ‖E‖ ≤ ε) (hε : ε < 1)
    (hs : s ∈ Set.Icc (0 : ℝ) 1) : ‖(1 + (s : ℂ) • E)⁻¹‖ ≤ 1 / (1 - s * ε) := by
  obtain ⟨h1, h2⟩ := norm_smul_le_and_lt_one hE hε hs
  refine (norm_inv_one_add_le (lt_of_le_of_lt h1 h2)).trans ?_
  have : 0 < 1 - s * ε := by linarith
  gcongr
theorem norm_inv_one_add_smul_sub_one_le {E : ComplexMatrix2} {ε s : ℝ} (hE : ‖E‖ ≤ ε)
    (hε : ε < 1) (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    ‖(1 + (s : ℂ) • E)⁻¹ - 1‖ ≤ s * ε / (1 - s * ε) := by
  obtain ⟨h1, h2⟩ := norm_smul_le_and_lt_one hE hε hs
  refine (norm_inv_one_add_sub_one_le (lt_of_le_of_lt h1 h2)).trans ?_
  have : 0 < 1 - s * ε := by linarith
  have hx : 0 ≤ s * ε := mul_nonneg hs.1 ((norm_nonneg E).trans hE)
  gcongr
theorem abs_mul_norm_lt_one_of_mem_Icc {E : ComplexMatrix2} (h : ‖E‖ < 1) {s : ℝ}
    (hs : s ∈ Set.Icc (0 : ℝ) 1) : |s| * ‖E‖ < 1 := by
  rw [abs_of_nonneg hs.1]
  nlinarith [hs.1, hs.2, norm_nonneg E]
theorem continuousOn_inv_one_add_smul_Icc {E : ComplexMatrix2} (h : ‖E‖ < 1) :
    ContinuousOn (fun s : ℝ => (1 + (s : ℂ) • E)⁻¹) (Set.Icc 0 1) :=
  continuousOn_inv_one_add_smul.mono fun _ hs => abs_mul_norm_lt_one_of_mem_Icc h hs
theorem logSeries_eq_integral {A : ComplexMatrix2} (h : ‖A - 1‖ < 1) :
    logSeries A = ∫ s in (0 : ℝ)..1, (A - 1) * (1 + (s : ℂ) • (A - 1))⁻¹ := by
  have := logSeries_one_add_smul_eq_integral (E := A - 1) (t := 1) (by simpa using h)
  simpa using this
theorem logSeries_sub_logSeries_eq_integral {A B : ComplexMatrix2} (hA : ‖A - 1‖ < 1)
    (hB : ‖B - 1‖ < 1) :
    logSeries A - logSeries B =
      ∫ t in (0 : ℝ)..1, (1 + (t : ℂ) • (A - 1))⁻¹ * (A - B) * (1 + (t : ℂ) • (B - 1))⁻¹ := by
  have icc : Set.uIcc (0 : ℝ) 1 = Set.Icc 0 1 := Set.uIcc_of_le zero_le_one
  have iA : IntervalIntegrable (fun s : ℝ => (A - 1) * (1 + (s : ℂ) • (A - 1))⁻¹) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [icc]
    exact continuousOn_const.mul (continuousOn_inv_one_add_smul_Icc hA)
  have iB : IntervalIntegrable (fun s : ℝ => (B - 1) * (1 + (s : ℂ) • (B - 1))⁻¹) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [icc]
    exact continuousOn_const.mul (continuousOn_inv_one_add_smul_Icc hB)
  rw [logSeries_eq_integral hA, logSeries_eq_integral hB, ← intervalIntegral.integral_sub iA iB]
  refine intervalIntegral.integral_congr fun s hs => ?_
  rw [icc] at hs
  have hsA := abs_mul_norm_lt_one_of_mem_Icc hA hs
  have hsB := abs_mul_norm_lt_one_of_mem_Icc hB hs
  have := mul_inv_one_add_sub_mul_inv_one_add (E := A - 1) (F := B - 1) (c := (s : ℂ))
    (by simpa [norm_smul] using hsA) (by simpa [norm_smul] using hsB)
  rw [this, sub_sub_sub_cancel_right]
theorem integral_inv_one_sub_mul_sq {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε < 1) :
    ∫ s in (0 : ℝ)..1, ((1 - s * ε) ^ 2)⁻¹ = 1 / (1 - ε) := by
  have icc : Set.uIcc (0 : ℝ) 1 = Set.Icc 0 1 := Set.uIcc_of_le zero_le_one
  have hpos : ∀ s ∈ Set.Icc (0 : ℝ) 1, 0 < 1 - s * ε := fun s hs => by
    nlinarith [hs.1, hs.2]
  have hd : ∀ s ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (fun x : ℝ => x / (1 - x * ε)) (((1 - s * ε) ^ 2)⁻¹) s := by
    intro s hs
    rw [icc] at hs
    have hne := (hpos s hs).ne'
    have h2 : HasDerivAt (fun x : ℝ => 1 - x * ε) (-ε) s := by
      simpa using ((hasDerivAt_id s).mul_const ε).const_sub 1
    have h3 : HasDerivAt (fun x : ℝ => x / (1 - x * ε))
        ((1 * (1 - s * ε) - s * (-ε)) / (1 - s * ε) ^ 2) s := (hasDerivAt_id s).div h2 hne
    rwa [show 1 * (1 - s * ε) - s * (-ε) = 1 by ring, one_div] at h3
  have hc : IntervalIntegrable (fun s : ℝ => ((1 - s * ε) ^ 2)⁻¹) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [icc]
    refine ContinuousOn.inv₀ (by fun_prop) fun s hs => (pow_pos (hpos s hs) 2).ne'
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hc]
  simp
theorem norm_logSeries_sub_logSeries_le {A B : ComplexMatrix2} {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε < 1)
    (hA : ‖A - 1‖ ≤ ε) (hB : ‖B - 1‖ ≤ ε) :
    ‖logSeries A - logSeries B‖ ≤ 1 / (1 - ε) * ‖A - B‖ := by
  have icc : Set.uIcc (0 : ℝ) 1 = Set.Icc 0 1 := Set.uIcc_of_le zero_le_one
  have hpos : ∀ s ∈ Set.Icc (0 : ℝ) 1, 0 < 1 - s * ε := fun s hs => by
    nlinarith [hs.1, hs.2]
  rw [logSeries_sub_logSeries_eq_integral (lt_of_le_of_lt hA h1) (lt_of_le_of_lt hB h1)]
  have hi : IntervalIntegrable (fun s : ℝ => ((1 - s * ε) ^ 2)⁻¹ * ‖A - B‖) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [icc]
    exact (ContinuousOn.inv₀ (by fun_prop) fun s hs => (pow_pos (hpos s hs) 2).ne').mul
      continuousOn_const
  refine (intervalIntegral.norm_integral_le_of_norm_le zero_le_one
    (ae_of_all _ fun s hs => ?_) hi).trans (le_of_eq ?_)
  · have hs' : s ∈ Set.Icc (0 : ℝ) 1 := ⟨hs.1.le, hs.2⟩
    have hp := hpos s hs'
    have r1 := norm_inv_one_add_smul_le hA h1 hs'
    have r2 := norm_inv_one_add_smul_le hB h1 hs'
    calc ‖(1 + (s : ℂ) • (A - 1))⁻¹ * (A - B) * (1 + (s : ℂ) • (B - 1))⁻¹‖
        ≤ ‖(1 + (s : ℂ) • (A - 1))⁻¹‖ * ‖A - B‖ * ‖(1 + (s : ℂ) • (B - 1))⁻¹‖ :=
          norm_mul₃_le
      _ ≤ 1 / (1 - s * ε) * ‖A - B‖ * (1 / (1 - s * ε)) := by gcongr
      _ = ((1 - s * ε) ^ 2)⁻¹ * ‖A - B‖ := by field_simp
  · rw [intervalIntegral.integral_mul_const, integral_inv_one_sub_mul_sq h0 h1]
theorem norm_logSeries_sub_logSeries_sub_le {A B : ComplexMatrix2} {ε : ℝ} (h0 : 0 ≤ ε)
    (h1 : ε < 1) (hA : ‖A - 1‖ ≤ ε) (hB : ‖B - 1‖ ≤ ε) :
    ‖logSeries A - logSeries B - (A - B)‖ ≤ ε / (1 - ε) * ‖A - B‖ := by
  have icc : Set.uIcc (0 : ℝ) 1 = Set.Icc 0 1 := Set.uIcc_of_le zero_le_one
  have hpos : ∀ s ∈ Set.Icc (0 : ℝ) 1, 0 < 1 - s * ε := fun s hs => by
    nlinarith [hs.1, hs.2]
  have hA1 := lt_of_le_of_lt hA h1
  have hB1 := lt_of_le_of_lt hB h1
  have hint : IntervalIntegrable (fun t : ℝ => (1 + (t : ℂ) • (A - 1))⁻¹ * (A - B) *
      (1 + (t : ℂ) • (B - 1))⁻¹) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [icc]
    exact ((continuousOn_inv_one_add_smul_Icc hA1).mul continuousOn_const).mul
      (continuousOn_inv_one_add_smul_Icc hB1)
  have hconst : (A - B) = ∫ _t in (0 : ℝ)..1, (A - B) := by simp
  have hid : logSeries A - logSeries B - (A - B) = ∫ t in (0 : ℝ)..1,
      ((1 + (t : ℂ) • (A - 1))⁻¹ * (A - B) * (1 + (t : ℂ) • (B - 1))⁻¹ - (A - B)) := by
    rw [intervalIntegral.integral_sub hint intervalIntegrable_const, ← hconst,
      logSeries_sub_logSeries_eq_integral hA1 hB1]
  rw [hid]
  have hi : IntervalIntegrable (fun s : ℝ => (((1 - s * ε) ^ 2)⁻¹ - 1) * ‖A - B‖) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [icc]
    exact ((ContinuousOn.inv₀ (by fun_prop) fun s hs => (pow_pos (hpos s hs) 2).ne').sub
      continuousOn_const).mul continuousOn_const
  refine (intervalIntegral.norm_integral_le_of_norm_le zero_le_one
    (ae_of_all _ fun s hs => ?_) hi).trans (le_of_eq ?_)
  · have hs' : s ∈ Set.Icc (0 : ℝ) 1 := ⟨hs.1.le, hs.2⟩
    have hp := hpos s hs'
    have r1 := norm_inv_one_add_smul_sub_one_le hA h1 hs'
    have r2 := norm_inv_one_add_smul_le hB h1 hs'
    have r3 := norm_inv_one_add_smul_sub_one_le hB h1 hs'
    set R := (1 + (s : ℂ) • (A - 1))⁻¹
    set R' := (1 + (s : ℂ) • (B - 1))⁻¹
    have hx : 0 ≤ s * ε := mul_nonneg hs'.1 h0
    have key : R * (A - B) * R' - (A - B) = (R - 1) * (A - B) * R' + (A - B) * (R' - 1) := by
      noncomm_ring
    rw [key]
    calc ‖(R - 1) * (A - B) * R' + (A - B) * (R' - 1)‖
        ≤ ‖R - 1‖ * ‖A - B‖ * ‖R'‖ + ‖A - B‖ * ‖R' - 1‖ :=
          (norm_add_le _ _).trans (add_le_add norm_mul₃_le (norm_mul_le _ _))
      _ ≤ s * ε / (1 - s * ε) * ‖A - B‖ * (1 / (1 - s * ε)) +
            ‖A - B‖ * (s * ε / (1 - s * ε)) := by gcongr
      _ = (((1 - s * ε) ^ 2)⁻¹ - 1) * ‖A - B‖ := by field_simp; ring
  · have hi0 : IntervalIntegrable (fun s : ℝ => ((1 - s * ε) ^ 2)⁻¹) volume 0 1 := by
      apply ContinuousOn.intervalIntegrable
      rw [icc]
      exact ContinuousOn.inv₀ (by fun_prop) fun s hs => (pow_pos (hpos s hs) 2).ne'
    rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_sub hi0
      intervalIntegrable_const, integral_inv_one_sub_mul_sq h0 h1]
    have : 0 < 1 - ε := by linarith
    rw [intervalIntegral.integral_const]
    simp only [sub_zero, smul_eq_mul, mul_one]
    congr 1
    field_simp
    ring
theorem eq_zero_of_matExp_eq_one {Y : ComplexMatrix2} (h : ‖Y‖ < 1 / 2) (he : matExp Y = 1) :
    Y = 0 := by
  have hb := norm_matExp_sub_matExp_sub_le (Z := Y) (Z' := 0) (r := ‖Y‖) le_rfl (by simp)
  rw [he, matExp_zero, sub_self, zero_sub, sub_zero, norm_neg] at hb
  have hlog : (1 / 2 : ℝ) < Real.log 2 := by
    have := Real.log_two_gt_d9
    linarith
  have hexp : Real.exp ‖Y‖ < 2 := by
    have := Real.exp_lt_exp.2 (h.trans hlog)
    rwa [Real.exp_log (by norm_num)] at this
  by_contra hne
  have hpos : 0 < ‖Y‖ := norm_pos_iff.2 hne
  nlinarith
theorem commute_matExp (Y : ComplexMatrix2) : Commute Y (matExp Y) := by
  rw [← (hasSum_expSeries_matExp Y).tsum_eq]
  exact Commute.tsum_right Y fun n => ((Commute.refl Y).pow_right n).smul_right _
theorem hasDerivAt_matExp_smul (Z : ComplexMatrix2) (t : ℝ) :
    HasDerivAt (fun s : ℝ => matExp ((s : ℂ) • Z)) (matExp ((t : ℂ) • Z) * Z) t := by
  have h1 : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 t := (hasDerivAt_id t).ofReal_comp
  have h2 : HasDerivAt (fun s : ℝ => (s : ℂ) • Z) Z t := by
    simpa using h1.smul_const Z
  exact hasDerivAt_matExp_of_commute h2 fun s => ((Commute.refl Z).smul_left _).smul_right _
theorem logSeries_matExp {Z : ComplexMatrix2} (h : ‖Z‖ < Real.log 2) : logSeries (matExp Z) = Z := by
  set ε : ℝ := Real.exp ‖Z‖ - 1 with hεdef
  have hexp2 : Real.exp ‖Z‖ < 2 := by
    have := Real.exp_lt_exp.2 h
    rwa [Real.exp_log (by norm_num)] at this
  have hε1 : ε < 1 := by rw [hεdef]; linarith
  have hε0 : 0 ≤ ε := by
    have := Real.add_one_le_exp ‖Z‖
    have := norm_nonneg Z
    rw [hεdef]; linarith
  set D : ℝ → ComplexMatrix2 := fun t => matExp ((t : ℂ) • Z) with hDdef
  have hD1 : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖D t - 1‖ ≤ ε := by
    intro t ht
    refine (norm_matExp_sub_one_le _).trans ?_
    have hn : ‖(t : ℂ) • Z‖ ≤ ‖Z‖ := by
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1]
      exact mul_le_of_le_one_left (norm_nonneg _) ht.2
    have := Real.exp_le_exp.2 hn
    rw [hεdef]; linarith
  have hDc : Continuous D :=
    continuous_iff_continuousAt.2 fun t => (hasDerivAt_matExp_smul Z t).continuousAt
  have hL : LipschitzOnWith (Real.toNNReal (1 / (1 - ε))) logSeries (Metric.closedBall 1 ε) := by
    refine LipschitzOnWith.of_dist_le_mul fun A hA B hB => ?_
    rw [mem_closedBall_iff_norm] at hA hB
    rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ (by
      have : 0 < 1 - ε := by linarith
      positivity)]
    exact norm_logSeries_sub_logSeries_le hε0 hε1 hA hB
  have hlogc : ContinuousOn (fun t => logSeries (D t)) (Set.Icc 0 1) :=
    hL.continuousOn.comp hDc.continuousOn fun t ht => by
      rw [mem_closedBall_iff_norm]
      exact hD1 t ht
  set φ : ℝ → ComplexMatrix2 := fun t => logSeries (D t) - (t : ℂ) • Z with hφdef
  have hφc : ContinuousOn φ (Set.Icc 0 1) := hlogc.sub (by fun_prop)
  have hφexp : ∀ t ∈ Set.Icc (0 : ℝ) 1, matExp (φ t) = 1 := by
    intro t ht
    have hlt : ‖D t - 1‖ < 1 := lt_of_le_of_lt (hD1 t ht) hε1
    have hc : Commute (logSeries (D t)) (-((t : ℂ) • Z)) :=
      ((commute_logSeries (commute_matExp _)).symm).neg_right
    simp only [hφdef]
    rw [sub_eq_add_neg, matExp_add_of_commute hc]
    have hel := matExp_logSeries_one_add hlt
    rw [add_sub_cancel] at hel
    rw [hel]
    exact matExp_mul_matExp_neg _
  have hclosed : IsClosed ({t : ℝ | φ t = 0} ∩ Set.Icc 0 1) := by
    have := hφc.preimage_isClosed_of_isClosed isClosed_Icc
      (isClosed_singleton (x := (0 : ComplexMatrix2)))
    rw [Set.inter_comm]
    exact this
  have h0 : φ 0 = 0 := by simp [hφdef, hDdef, logSeries_one]
  have hall := IsClosed.Icc_subset_of_forall_exists_gt (a := (0 : ℝ)) (b := 1) hclosed h0 ?_
  · have h1 : φ 1 = 0 := hall (by simp)
    simpa [hφdef, hDdef, sub_eq_zero] using h1
  · rintro x ⟨hx, hxI⟩ y hy
    have hxIcc : x ∈ Set.Icc (0 : ℝ) 1 := ⟨hxI.1, hxI.2.le⟩
    obtain ⟨δ, hδ, hcl⟩ := Metric.continuousWithinAt_iff.1 (hφc x hxIcc) (1 / 2) (by norm_num)
    have hy' : x < y := hy
    set t : ℝ := min y (min 1 (x + δ / 2)) with ht
    have hxt : x < t := lt_min hy' (lt_min hxI.2 (by linarith))
    have hty : t ≤ y := min_le_left _ _
    have ht1 : t ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
    have htδ : t ≤ x + δ / 2 := (min_le_right _ _).trans (min_le_right _ _)
    have htI : t ∈ Set.Icc (0 : ℝ) 1 := ⟨hxI.1.trans hxt.le, ht1⟩
    have hd : dist t x < δ := by
      rw [Real.dist_eq, abs_of_pos (by linarith)]
      linarith
    have hsmall := hcl htI hd
    have hx0 : φ x = 0 := hx
    rw [hx0, dist_zero_right] at hsmall
    exact ⟨t, eq_zero_of_matExp_eq_one hsmall (hφexp t htI), hxt, hty⟩
theorem det_matExp (Z : ComplexMatrix2) : (matExp Z).det = Complex.exp (fullTrace Z) := by
  set D : ℝ → ComplexMatrix2 := fun t => matExp ((t : ℂ) • Z) with hDdef
  have hent : ∀ (i j : Fin 2) (t : ℝ), HasDerivAt (fun s => D s i j) ((D t * Z) i j) t := by
    intro i j t
    let ℓ : ComplexMatrix2 →L[ℂ] ℂ :=
      LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℂ ℂ i j)
    have := (ℓ.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t (hasDerivAt_matExp_smul Z t)
    exact this
  set c : ℂ := fullTrace Z with hc
  set f : ℝ → ℂ := fun s => (D s 0 0 * D s 1 1 - D s 0 1 * D s 1 0) * Complex.exp (-(s : ℂ) * c)
    with hf
  have hd : ∀ t : ℝ, HasDerivAt f 0 t := by
    intro t
    have h1 := ((hent 0 0 t).mul (hent 1 1 t)).sub ((hent 0 1 t).mul (hent 1 0 t))
    have he : HasDerivAt (fun s : ℝ => Complex.exp (-(s : ℂ) * c))
        (Complex.exp (-(t : ℂ) * c) * (-1 * c)) t :=
      (((hasDerivAt_id t).ofReal_comp.neg).mul_const c).cexp
    have h2 : HasDerivAt f _ t := h1.mul he
    convert h2 using 1
    simp only [Matrix.mul_apply, Fin.sum_univ_two, hc, fullTrace, Matrix.trace_fin_two,
      Pi.sub_apply, Pi.mul_apply]
    ring
  have hconst := constant_of_has_deriv_right_zero (f := f) (a := 0) (b := 1)
    (fun t _ => (hd t).continuousAt.continuousWithinAt)
    (fun t _ => (hd t).hasDerivWithinAt) 1 (by simp)
  have h0 : f 0 = 1 := by simp [hf, hDdef]
  have h1 : f 1 = (matExp Z).det * Complex.exp (-c) := by
    simp [hf, hDdef, Matrix.det_fin_two]
  rw [h0, h1] at hconst
  calc (matExp Z).det = (matExp Z).det * Complex.exp (-c) * Complex.exp c := by
        rw [mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one]
    _ = Complex.exp c := by rw [hconst, one_mul]
theorem fullTrace_logSeries_eq_zero (hel : NormExpLogBasics) (hnum : Numerics.ExpLogNumericBounds)
    {X : ComplexMatrix2} (hd : X.det = 1) (hX : ‖X - 1‖ ≤ 9 / 10) : fullTrace (logSeries X) = 0 := by
  have hlt : ‖X - 1‖ < 1 := by linarith
  have hel1 := matExp_logSeries_one_add hlt
  rw [add_sub_cancel] at hel1
  have hexp : Complex.exp (fullTrace (logSeries X)) = 1 := by
    rw [← det_matExp, hel1, hd]
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.1 hexp
  have hnorm : ‖fullTrace (logSeries X)‖ < 2 * Real.pi := by
    have h1 : ‖fullTrace (logSeries X)‖ ≤ 2 * ‖logSeries X‖ := hel.1.2.2.2.2.2.2.1 _
    have h2 := norm_logSeries_one_add_le hlt
    rw [add_sub_cancel] at h2
    have h3 : Real.log (1 / 10) ≤ Real.log (1 - ‖X - 1‖) :=
      Real.log_le_log (by norm_num) (by linarith)
    have h4 : Real.log (1 / 10) = -Real.log 10 := by
      rw [one_div, Real.log_inv]
    have h5 : Real.log 10 < Real.pi := hnum.2.2.2.2.2.2.2.2
    linarith
  rw [hn] at hnorm ⊢
  have hn0 : n = 0 := by
    by_contra hne
    have hge : (1 : ℝ) ≤ |(n : ℝ)| := by
      exact_mod_cast Int.one_le_abs hne
    have hnn : ‖(n : ℂ) * (2 * Real.pi * Complex.I)‖ = |(n : ℝ)| * (2 * Real.pi) := by
      rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Complex.norm_intCast]
      simp [abs_of_pos Real.pi_pos]
    rw [hnn] at hnorm
    have := Real.pi_pos
    nlinarith
  simp [hn0]
theorem norm_eq_one_of_conj_mul_self {p : ℂ} (h : (starRingEnd ℂ) p * p = 1) : ‖p‖ = 1 := by
  have h1 : ((‖p‖ : ℂ)) ^ 2 = 1 := by rw [← Complex.conj_mul']; exact h
  have h2 : ‖p‖ ^ 2 = 1 ^ 2 := by
    rw [one_pow]
    exact_mod_cast h1
  exact (sq_eq_sq₀ (norm_nonneg p) zero_le_one).1 h2
theorem exists_unitary_diagonal_conj {A : ComplexMatrix2} (hA : A ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    ∃ u ∈ Matrix.unitaryGroup (Fin 2) ℂ, ∃ z : Fin 2 → ℂ, (∀ j, ‖z j‖ = 1) ∧
      A = u * Matrix.diagonal z * star u := by
  obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue (Matrix.toLin' A)
  obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
  have hAv : A.mulVec v = μ • v := by
    simpa [Matrix.toLin'_apply] using hv.apply_eq_smul
  have hv0 : v ≠ 0 := hv.2
  set N : ℝ := Real.sqrt (Complex.normSq (v 0) + Complex.normSq (v 1)) with hN
  have hsum : 0 < Complex.normSq (v 0) + Complex.normSq (v 1) := by
    by_contra hle
    have h0 := Complex.normSq_nonneg (v 0)
    have h1 := Complex.normSq_nonneg (v 1)
    have e0 : Complex.normSq (v 0) = 0 := by linarith
    have e1 : Complex.normSq (v 1) = 0 := by linarith
    apply hv0
    funext i
    fin_cases i
    · simpa using e0
    · simpa using e1
  have hNpos : 0 < N := Real.sqrt_pos.2 hsum
  set a : ℂ := v 0 / N with ha
  set b : ℂ := v 1 / N with hb
  have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast hNpos.ne'
  have hab : a * star a + b * star b = 1 := by
    have hsq : N ^ 2 = Complex.normSq (v 0) + Complex.normSq (v 1) := Real.sq_sqrt hsum.le
    have e0 : v 0 * star (v 0) = (Complex.normSq (v 0) : ℂ) := Complex.mul_conj _
    have e1 : v 1 * star (v 1) = (Complex.normSq (v 1) : ℂ) := Complex.mul_conj _
    have hconj : ((star (N : ℂ))) = N := Complex.conj_ofReal N
    simp only [ha, hb, star_div₀, hconj]
    have : (N : ℂ) ^ 2 = (Complex.normSq (v 0) : ℂ) + (Complex.normSq (v 1) : ℂ) := by
      exact_mod_cast hsq
    field_simp
    rw [this, ← e0, ← e1]
  have e0 : A 0 0 * a + A 0 1 * b = μ * a := by
    have := congrFun hAv 0
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Pi.smul_apply, smul_eq_mul] at this
    simp only [ha, hb]
    field_simp
    linear_combination this
  have e1 : A 1 0 * a + A 1 1 * b = μ * b := by
    have := congrFun hAv 1
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Pi.smul_apply, smul_eq_mul] at this
    simp only [ha, hb]
    field_simp
    linear_combination this
  clear_value a b
  set u : ComplexMatrix2 := !![a, -star b; b, star a] with hu
  have hsu : star u = !![star a, star b; -b, a] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hu, Matrix.star_apply]
  have habc : a * (starRingEnd ℂ) a + b * (starRingEnd ℂ) b = 1 := hab
  have hu1 : star u * u = 1 := by
    rw [hsu, hu]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two] <;> first | linear_combination habc | ring
  have hu2 : u * star u = 1 := mul_eq_one_comm.1 hu1
  have huU : u ∈ Matrix.unitaryGroup (Fin 2) ℂ := Matrix.mem_unitaryGroup_iff.2 hu2
  set D : ComplexMatrix2 := star u * A * u with hD
  have hDU : D ∈ Matrix.unitaryGroup (Fin 2) ℂ :=
    mul_mem (mul_mem (Unitary.star_mem huU) hA) huU
  have hD10 : D 1 0 = 0 := by
    rw [hD, hsu, hu]
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]
    linear_combination (-b) * e0 + a * e1
  have hstar : star D * D = 1 := Matrix.mem_unitaryGroup_iff'.1 hDU
  have h00 : (starRingEnd ℂ) (D 0 0) * D 0 0 = 1 := by
    have e := congrFun (congrFun hstar 0) 0
    simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply, hD10] using e
  have hp1 := norm_eq_one_of_conj_mul_self h00
  have hp0 : D 0 0 ≠ 0 := by
    intro h0
    rw [h0] at hp1
    simp at hp1
  have hq : D 0 1 = 0 := by
    have e := congrFun (congrFun hstar 0) 1
    have e' : (starRingEnd ℂ) (D 0 0) * D 0 1 = 0 := by
      simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply, hD10] using e
    rcases mul_eq_zero.1 e' with h | h
    · exact absurd ((map_eq_zero _).1 h) hp0
    · exact h
  have h11 : (starRingEnd ℂ) (D 1 1) * D 1 1 = 1 := by
    have e := congrFun (congrFun hstar 1) 1
    simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply, hq] using e
  have hs1 := norm_eq_one_of_conj_mul_self h11
  have hDd : D = Matrix.diagonal ![D 0 0, D 1 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hq, hD10]
  refine ⟨u, huU, ![D 0 0, D 1 1], ?_, ?_⟩
  · intro j
    fin_cases j
    · simpa using hp1
    · simpa using hs1
  · rw [← hDd, hD]
    calc A = (u * star u) * A * (u * star u) := by rw [hu2, one_mul, mul_one]
      _ = u * (star u * A * u) * star u := by noncomm_ring
theorem norm_pi_fin_two (v : Fin 2 → ℂ) : ‖v‖ = max ‖v 0‖ ‖v 1‖ := by
  refine le_antisymm ((pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_)
    (max_le (norm_le_pi_norm v 0) (norm_le_pi_norm v 1))
  fin_cases i
  · exact le_max_left _ _
  · exact le_max_right _ _
theorem norm_diagonal_fin_two (v : Fin 2 → ℂ) : ‖Matrix.diagonal v‖ = max ‖v 0‖ ‖v 1‖ := by
  rw [Matrix.l2_opNorm_diagonal, norm_pi_fin_two]
theorem one_sub_diagonal_eq (z : Fin 2 → ℂ) :
    (1 : ComplexMatrix2) - Matrix.diagonal z = Matrix.diagonal fun j => 1 - z j := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp
theorem diagonal_sub_one_eq (z : Fin 2 → ℂ) :
    Matrix.diagonal z - (1 : ComplexMatrix2) = Matrix.diagonal fun j => z j - 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp
theorem logSeries_diagonal {z : Fin 2 → ℂ} (hz : ∀ j, ‖z j - 1‖ < 1) :
    logSeries (Matrix.diagonal z) = Matrix.diagonal fun j => Complex.log (z j) := by
  have hj : ∀ j, HasSum (fun n : ℕ => (1 - z j) ^ (n + 1) / ((n + 1 : ℕ) : ℂ))
      (-Complex.log (z j)) := by
    intro j
    have h := Complex.hasSum_taylorSeries_neg_log (z := 1 - z j) (by
      rw [← norm_neg]; simpa using hz j)
    have h' := (hasSum_nat_add_iff' 1).2 h
    simpa using h'
  have hp : HasSum (fun (n : ℕ) (j : Fin 2) => (1 - z j) ^ (n + 1) / ((n + 1 : ℕ) : ℂ))
      (fun j => -Complex.log (z j)) := Pi.hasSum.2 hj
  have hm := hp.matrix_diagonal
  have hterm : (fun n : ℕ => Matrix.diagonal fun j => (1 - z j) ^ (n + 1) / ((n + 1 : ℕ) : ℂ))
      = fun n : ℕ => ((n + 1 : ℂ)⁻¹) • (1 - Matrix.diagonal z) ^ (n + 1) := by
    funext n
    rw [one_sub_diagonal_eq, Matrix.diagonal_pow, ← Matrix.diagonal_smul]
    congr 1
    funext j
    simp [div_eq_inv_mul]
  rw [hterm] at hm
  rw [logSeries, hm.tsum_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp
theorem matExp_diagonal (v : Fin 2 → ℂ) :
    matExp (Matrix.diagonal v) = Matrix.diagonal fun j => Complex.exp (v j) := by
  refine (Matrix.exp_diagonal v).trans ?_
  congr 1
  funext j
  simp [Complex.exp_eq_exp_ℂ]
theorem abs_sin_half_eq {θ : ℝ} (h : |θ| ≤ Real.pi) : |Real.sin (θ / 2)| = Real.sin (|θ| / 2) := by
  rcases le_total 0 θ with h0 | h0
  · rw [abs_of_nonneg h0] at h ⊢
    exact abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith))
  · rw [abs_of_nonpos h0] at h ⊢
    have hs : 0 ≤ Real.sin (-θ / 2) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
    have he : Real.sin (-θ / 2) = -Real.sin (θ / 2) := by
      rw [neg_div, Real.sin_neg]
    rw [he] at hs ⊢
    exact abs_of_nonpos (by linarith)
theorem abs_lt_pi_div_three_of_sin {θ : ℝ} (h : |θ| ≤ Real.pi) (hs : 2 * Real.sin (|θ| / 2) < 1) :
    |θ| < Real.pi / 3 := by
  by_contra hge
  have := Real.sin_le_sin_of_le_of_le_pi_div_two (x := Real.pi / 6) (y := |θ| / 2)
    (by linarith [Real.pi_pos]) (by linarith) (by linarith)
  rw [Real.sin_pi_div_six] at this
  linarith
theorem one_half_le_re {z : ℂ} (h1 : ‖z‖ = 1) (h2 : ‖z - 1‖ < 1) : 1 / 2 ≤ z.re := by
  have e1 : z.re * z.re + z.im * z.im = 1 := by
    have := Complex.normSq_eq_norm_sq z
    rw [h1, Complex.normSq_apply] at this
    simpa using this
  have e2 : (z.re - 1) * (z.re - 1) + z.im * z.im < 1 := by
    have := Complex.normSq_eq_norm_sq (z - 1)
    rw [Complex.normSq_apply] at this
    simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, sub_zero] at this
    rw [this]
    nlinarith [norm_nonneg (z - 1)]
  nlinarith
theorem unitary_conj_facts {u : ComplexMatrix2} (hu : u ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    star u * u = 1 ∧ u * star u = 1 ∧ u⁻¹ = star u ∧ IsUnit u := by
  have h1 : star u * u = 1 := Matrix.mem_unitaryGroup_iff'.1 hu
  have h2 : u * star u = 1 := Matrix.mem_unitaryGroup_iff.1 hu
  exact ⟨h1, h2, Matrix.inv_eq_right_inv h2, ⟨⟨u, star u, h2, h1⟩, rfl⟩⟩
theorem norm_unitary_conj (hel : NormExpLogBasics) {u : ComplexMatrix2}
    (hu : u ∈ Matrix.unitaryGroup (Fin 2) ℂ) (X : ComplexMatrix2) : ‖u * X * star u‖ = ‖X‖ :=
  hel.1.2.2.2.1 X u (star u) hu (Unitary.star_mem hu)
theorem norm_sub_one_eq_max (hel : NormExpLogBasics) {A u : ComplexMatrix2} {z : Fin 2 → ℂ}
    (hu : u ∈ Matrix.unitaryGroup (Fin 2) ℂ) (hA : A = u * Matrix.diagonal z * star u) :
    ‖A - 1‖ = max ‖z 0 - 1‖ ‖z 1 - 1‖ := by
  obtain ⟨-, h2, -, -⟩ := unitary_conj_facts hu
  have e : A - 1 = u * (Matrix.diagonal z - 1) * star u := by
    rw [hA, mul_sub, sub_mul, mul_one, h2]
  rw [e, norm_unitary_conj hel hu, diagonal_sub_one_eq, norm_diagonal_fin_two]
theorem norm_inv_one_add_smul_unitary_le (hel : NormExpLogBasics) {A : ComplexMatrix2}
    (hA : A ∈ Matrix.unitaryGroup (Fin 2) ℂ) (h1 : ‖A - 1‖ < 1) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) : ‖(1 + (t : ℂ) • (A - 1))⁻¹‖ ≤ 1 / (1 - t * (1 / 2)) := by
  obtain ⟨u, hu, z, hz, hAe⟩ := exists_unitary_diagonal_conj hA
  obtain ⟨hus, hus', -, -⟩ := unitary_conj_facts hu
  have hmax := norm_sub_one_eq_max hel hu hAe
  have hzj : ∀ j, ‖z j - 1‖ < 1 := by
    intro j
    rw [hmax] at h1
    fin_cases j
    · exact lt_of_le_of_lt (le_max_left _ _) h1
    · exact lt_of_le_of_lt (le_max_right _ _) h1
  set w : Fin 2 → ℂ := fun j => 1 + (t : ℂ) * (z j - 1) with hw
  have hpos : 0 < 1 - t * (1 / 2) := by linarith [ht.2]
  have hwn : ∀ j, 1 - t * (1 / 2) ≤ ‖w j‖ := by
    intro j
    have hr := one_half_le_re (hz j) (hzj j)
    have hre : (w j).re = 1 + t * ((z j).re - 1) := by simp [hw]
    refine le_trans ?_ (Complex.re_le_norm _)
    rw [hre]
    nlinarith [ht.1]
  have hw0 : ∀ j, w j ≠ 0 := fun j h0 => by
    have := hwn j
    rw [h0, norm_zero] at this
    linarith
  have he : 1 + (t : ℂ) • (A - 1) = u * Matrix.diagonal w * star u := by
    have hd : Matrix.diagonal w = 1 + (t : ℂ) • (Matrix.diagonal z - 1) := by
      rw [diagonal_sub_one_eq, ← Matrix.diagonal_smul, ← Matrix.diagonal_one, Matrix.diagonal_add]
      congr 1
    rw [hd, mul_add, add_mul, mul_one, hus', Matrix.mul_smul, Matrix.smul_mul, mul_sub, sub_mul,
      mul_one, hus', ← hAe]
  have hinv : (1 + (t : ℂ) • (A - 1))⁻¹ = u * Matrix.diagonal (fun j => (w j)⁻¹) * star u := by
    refine Matrix.inv_eq_right_inv ?_
    rw [he]
    calc u * Matrix.diagonal w * star u * (u * Matrix.diagonal (fun j => (w j)⁻¹) * star u)
        = u * Matrix.diagonal w * (star u * u) * Matrix.diagonal (fun j => (w j)⁻¹) * star u := by
          noncomm_ring
      _ = u * (Matrix.diagonal w * Matrix.diagonal (fun j => (w j)⁻¹)) * star u := by
          rw [hus, mul_one]; noncomm_ring
      _ = 1 := by
          rw [Matrix.diagonal_mul_diagonal]
          have : (fun j => w j * (w j)⁻¹) = fun _ => (1 : ℂ) := by
            funext j
            exact mul_inv_cancel₀ (hw0 j)
          rw [this, Matrix.diagonal_one, mul_one, hus']
  rw [hinv, norm_unitary_conj hel hu, norm_diagonal_fin_two]
  have hb : ∀ j, ‖(w j)⁻¹‖ ≤ 1 / (1 - t * (1 / 2)) := by
    intro j
    rw [norm_inv, one_div]
    exact inv_anti₀ hpos (hwn j)
  exact max_le (hb 0) (hb 1)
theorem norm_logSeries_sub_logSeries_unitary_le (hel : NormExpLogBasics) {A B : ComplexMatrix2}
    (hA : A ∈ Matrix.unitaryGroup (Fin 2) ℂ) (hB : B ∈ Matrix.unitaryGroup (Fin 2) ℂ)
    (h1 : ‖A - 1‖ < 1) (h2 : ‖B - 1‖ < 1) : ‖logSeries A - logSeries B‖ ≤ 2 * ‖A - B‖ := by
  have icc : Set.uIcc (0 : ℝ) 1 = Set.Icc 0 1 := Set.uIcc_of_le zero_le_one
  have hpos : ∀ s ∈ Set.Icc (0 : ℝ) 1, 0 < 1 - s * (1 / 2) := fun s hs => by
    linarith [hs.2]
  rw [logSeries_sub_logSeries_eq_integral h1 h2]
  have hi : IntervalIntegrable (fun s : ℝ => ((1 - s * (1 / 2)) ^ 2)⁻¹ * ‖A - B‖) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [icc]
    exact (ContinuousOn.inv₀ (by fun_prop) fun s hs => (pow_pos (hpos s hs) 2).ne').mul
      continuousOn_const
  refine (intervalIntegral.norm_integral_le_of_norm_le zero_le_one
    (ae_of_all _ fun s hs => ?_) hi).trans (le_of_eq ?_)
  · have hs' : s ∈ Set.Icc (0 : ℝ) 1 := ⟨hs.1.le, hs.2⟩
    have hp := hpos s hs'
    have r1 := norm_inv_one_add_smul_unitary_le hel hA h1 hs'
    have r2 := norm_inv_one_add_smul_unitary_le hel hB h2 hs'
    calc ‖(1 + (s : ℂ) • (A - 1))⁻¹ * (A - B) * (1 + (s : ℂ) • (B - 1))⁻¹‖
        ≤ ‖(1 + (s : ℂ) • (A - 1))⁻¹‖ * ‖A - B‖ * ‖(1 + (s : ℂ) • (B - 1))⁻¹‖ :=
          norm_mul₃_le
      _ ≤ 1 / (1 - s * (1 / 2)) * ‖A - B‖ * (1 / (1 - s * (1 / 2))) := by gcongr
      _ = ((1 - s * (1 / 2)) ^ 2)⁻¹ * ‖A - B‖ := by field_simp
  · rw [intervalIntegral.integral_mul_const, integral_inv_one_sub_mul_sq (by norm_num) (by norm_num)]
    norm_num
theorem ne_neg_one_of_norm_sub_one_lt {A : ComplexMatrix2} (h1 : ‖A - 1‖ < 1) : A ≠ -1 := by apply _root_.YangMills.Construction.PeriodicLattice.ContourSpread.ne_neg_one_of_operatorNorm_sub_one_lt <;> assumption
theorem logSeries_unitary (hel : NormExpLogBasics) (hint : UnitaryLogarithmProperties)
    {A : ComplexMatrix2} (hA : A ∈ Matrix.unitaryGroup (Fin 2) ℂ) (h1 : ‖A - 1‖ < 1) :
    ∃ H : ComplexMatrix2, H.IsHermitian ∧ logSeries A = Complex.I • H ∧
      operatorNorm H < Real.pi / 3 ∧ matExp (Complex.I • H) = A ∧
      operatorNorm (A - 1) = 2 * Real.sin (operatorNorm H / 2) ∧
      (A.det = 1 →
        fullTrace H = 0 ∧ H ∈ hermitianTraceless ∧
          (∃ Y ∈ hermitianTraceless, logSeries A = Complex.I • Y) ∧ H = unitaryLieLog A) := by
  obtain ⟨u, hu, z, hz, hAe⟩ := exists_unitary_diagonal_conj hA
  obtain ⟨hus, hus', hinv, hunit⟩ := unitary_conj_facts hu
  have hmax := norm_sub_one_eq_max hel hu hAe
  have hzj : ∀ j, ‖z j - 1‖ < 1 := by
    intro j
    have h := h1
    rw [hmax] at h
    fin_cases j
    · exact lt_of_le_of_lt (le_max_left _ _) h
    · exact lt_of_le_of_lt (le_max_right _ _) h
  set θ : Fin 2 → ℝ := fun j => Complex.arg (z j) with hθdef
  have hθπ : ∀ j, |θ j| ≤ Real.pi := fun j => Complex.abs_arg_le_pi _
  have hzθ : ∀ j, z j = Complex.exp (Complex.I * (θ j : ℂ)) := by
    intro j
    have := Complex.norm_mul_exp_arg_mul_I (z j)
    rw [hz j] at this
    simpa [mul_comm] using this.symm
  have hlogz : ∀ j, Complex.log (z j) = Complex.I * (θ j : ℂ) := by
    intro j
    simp [Complex.log, hz j, hθdef, mul_comm]
  have hsin : ∀ j, ‖z j - 1‖ = 2 * Real.sin (|θ j| / 2) := by
    intro j
    rw [hzθ j, Complex.norm_exp_I_mul_ofReal_sub_one, norm_mul, Real.norm_eq_abs,
      ← abs_sin_half_eq (hθπ j)]
    simp
  have hθ3 : ∀ j, |θ j| < Real.pi / 3 := fun j =>
    abs_lt_pi_div_three_of_sin (hθπ j) (by rw [← hsin j]; exact hzj j)
  set D : ComplexMatrix2 := Matrix.diagonal fun j => (θ j : ℂ) with hD
  set H : ComplexMatrix2 := u * D * star u with hH
  have hDstar : star D = D := by
    rw [hD, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose]
    congr 1
    funext j
    simp
  have hHstar : star H = H := by
    rw [hH, star_mul, star_mul, star_star, hDstar, mul_assoc]
  have hHherm : H.IsHermitian := hHstar
  have hDI : Complex.I • D = Matrix.diagonal fun j => Complex.I * (θ j : ℂ) := by
    rw [hD, ← Matrix.diagonal_smul]
    rfl
  have hIH : Complex.I • H = u * (Complex.I • D) * u⁻¹ := by
    rw [hH, hinv, Matrix.mul_smul, Matrix.smul_mul]
  have hdiag1 : ‖Matrix.diagonal z - 1‖ < 1 := by
    rw [diagonal_sub_one_eq, norm_diagonal_fin_two]
    exact max_lt (hzj 0) (hzj 1)
  have hlogA : logSeries A = Complex.I • H := by
    have hc := (hel.2.2.1 (Matrix.diagonal z) u hdiag1 hu).2
    have hAe' : A = u * Matrix.diagonal z * u⁻¹ := by rw [hinv]; exact hAe
    rw [hAe', hc, logSeries_diagonal hzj, hIH, hDI]
    congr 3
    funext j
    exact hlogz j
  have hHn : ‖H‖ = max |θ 0| |θ 1| := by
    rw [hH, norm_unitary_conj hel hu, hD, norm_diagonal_fin_two]
    simp
  have hHlt : operatorNorm H < Real.pi / 3 := by
    show ‖H‖ < _
    rw [hHn]
    exact max_lt (hθ3 0) (hθ3 1)
  have hexp : matExp (Complex.I • H) = A := by
    have hc := (hel.2.1 (Complex.I • D)).2.2.2.2.2.2 u hunit
    rw [hIH, ← hc, hDI, matExp_diagonal, hinv]
    have hzz : (fun j => Complex.exp (Complex.I * (θ j : ℂ))) = z := funext fun j => (hzθ j).symm
    rw [hzz]
    exact hAe.symm
  have hnorm : operatorNorm (A - 1) = 2 * Real.sin (operatorNorm H / 2) := by
    show ‖A - 1‖ = 2 * Real.sin (‖H‖ / 2)
    have hmono : ∀ {a b : ℝ}, 0 ≤ a → a ≤ b → b ≤ Real.pi →
        2 * Real.sin (a / 2) ≤ 2 * Real.sin (b / 2) := fun {a b} ha hab hb => by
      have := Real.sin_le_sin_of_le_of_le_pi_div_two (x := a / 2) (y := b / 2)
        (by linarith [Real.pi_pos]) (by linarith) (by linarith)
      linarith
    rw [hmax, hsin 0, hsin 1, hHn]
    rcases le_total |θ 0| |θ 1| with h | h
    · rw [max_eq_right h, max_eq_right (hmono (abs_nonneg _) h (hθπ 1))]
    · rw [max_eq_left h, max_eq_left (hmono (abs_nonneg _) h (hθπ 0))]
  refine ⟨H, hHherm, hlogA, hHlt, hexp, hnorm, fun hdet => ?_⟩
  have hdz : z 0 * z 1 = 1 := by
    have hd := hdet
    rw [hAe, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Fin.prod_univ_two] at hd
    have hdu : u.det * (star u).det = 1 := by rw [← Matrix.det_mul, hus', Matrix.det_one]
    calc z 0 * z 1 = (u.det * (star u).det) * (z 0 * z 1) := by rw [hdu, one_mul]
      _ = u.det * (z 0 * z 1) * (star u).det := by ring
      _ = 1 := hd
  have hsum : θ 0 + θ 1 = 0 := by
    have he : Complex.exp (((θ 0 + θ 1 : ℝ) : ℂ) * Complex.I) = 1 := by
      have h01 : Complex.exp (Complex.I * (θ 0 : ℂ)) * Complex.exp (Complex.I * (θ 1 : ℂ)) = 1 := by
        rw [← hzθ 0, ← hzθ 1]
        exact hdz
      rw [← h01, ← Complex.exp_add]
      congr 1
      push_cast
      ring
    obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.1 he
    have hr : θ 0 + θ 1 = n * (2 * Real.pi) := by
      have hc : ((θ 0 + θ 1 : ℝ) : ℂ) = (((n : ℝ) * (2 * Real.pi) : ℝ) : ℂ) := by
        apply mul_right_cancel₀ Complex.I_ne_zero
        rw [hn]
        push_cast
        ring
      exact_mod_cast hc
    have habs : |θ 0 + θ 1| < 2 * Real.pi / 3 := by
      have := abs_add_le (θ 0) (θ 1)
      have := hθ3 0
      have := hθ3 1
      linarith
    have hn0 : n = 0 := by
      by_contra hne
      have hge : (1 : ℝ) ≤ |(n : ℝ)| := by
        exact_mod_cast Int.one_le_abs hne
      rw [hr, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)] at habs
      nlinarith [Real.pi_pos]
    rw [hr, hn0]
    simp
  have htr : fullTrace H = 0 := by
    have ht : fullTrace H = ((θ 0 + θ 1 : ℝ) : ℂ) := by
      show Matrix.trace (u * D * star u) = _
      rw [Matrix.trace_mul_comm, ← mul_assoc, hus, one_mul, hD, Matrix.trace_fin_two]
      simp
    rw [ht, hsum]
    simp
  have hHsu : H ∈ hermitianTraceless := ⟨hHherm.symm, htr⟩
  have hSU : A ∈ specialUnitary := Matrix.mem_specialUnitaryGroup_iff.2 ⟨hA, hdet⟩
  have hdom : A ∈ unitaryLogDomain := ⟨hSU, ne_neg_one_of_norm_sub_one_lt h1⟩
  have hHpi : operatorNorm H < Real.pi := by linarith [Real.pi_pos]
  have e1 := (hint.2.2.1 A hdom H).1 ⟨hHsu, hHpi, hexp⟩
  obtain ⟨l1, l2, l3, -⟩ := hint.2.2.2.2.1 A hdom
  have e2 := (hint.2.2.1 A hdom (unitaryLieLog A)).1 ⟨l1, l2, l3⟩
  exact ⟨htr, hHsu, ⟨H, hHsu, hlogA⟩, e1.trans e2.symm⟩
theorem holds (hel : NormExpLogBasics) (hint : UnitaryLogarithmProperties)
    (hnum : Numerics.ExpLogNumericBounds) : ComplexMatrix2.ExpLogEstimates := by
  refine ⟨fun Z => ⟨norm_matExp_le Z, norm_matExp_sub_one_le Z⟩, fun Z Z' r h => ?_,
    norm_mul_matExp_sub_one_le, fun E hE => ?_, fun Z hZ => ?_, det_matExp, fun X hd hX => ?_,
    fun A hA h1 => logSeries_unitary hel hint hA h1, fun ε A B h0 h1 hA hB => ?_,
    fun A hA B hB h1 h2 => norm_logSeries_sub_logSeries_unitary_le hel hA hB h1 h2⟩
  · have h1 := (le_max_left _ _).trans h
    have h2 := (le_max_right _ _).trans h
    exact ⟨norm_matExp_sub_matExp_le h1 h2, norm_matExp_sub_matExp_sub_le h1 h2⟩
  · exact ⟨norm_logSeries_one_add_le hE, neg_log_one_sub_le hE, isUnit_one_add_of_norm_lt_one hE,
      norm_inv_one_add_sub_one_le hE, matExp_logSeries_one_add hE⟩
  · refine ⟨lt_of_le_of_lt (norm_matExp_sub_one_le Z) ?_, logSeries_matExp hZ⟩
    have := Real.exp_lt_exp.2 hZ
    rw [Real.exp_log (by norm_num)] at this
    linarith
  · have ht := fullTrace_logSeries_eq_zero hel hnum hd hX
    exact ⟨ht, ht⟩
  · have hA1 := lt_of_le_of_lt hA h1
    have hB1 := lt_of_le_of_lt hB h1
    refine ⟨fun t ht => ?_, logSeries_sub_logSeries_eq_integral hA1 hB1,
      norm_logSeries_sub_logSeries_sub_le h0 h1 hA hB, norm_logSeries_sub_logSeries_le h0 h1 hA hB⟩
    obtain ⟨a1, a2⟩ := norm_smul_le_and_lt_one hA h1 ht
    obtain ⟨b1, b2⟩ := norm_smul_le_and_lt_one hB h1 ht
    exact ⟨isUnit_one_add_of_norm_lt_one (lt_of_le_of_lt a1 a2),
      isUnit_one_add_of_norm_lt_one (lt_of_le_of_lt b1 b2)⟩
end YangMills.Construction.Matrices.ComplexMatrix2.ExpLogEstimates
