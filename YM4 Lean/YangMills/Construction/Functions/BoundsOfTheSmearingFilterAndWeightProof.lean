import YangMills.Construction.Functions.BoundsOfTheSmearingFilterAndWeight
import YangMills.Construction.Functions.PropertiesOfTheSmearingSequenceAndTheTriangleFunction
import YangMills.Construction.Functions.SmearingSeriesConvergence
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.SmearingFilter.Bounds
open Real YangMills.Construction.ReflectionPositivity.EnergyMomentum YangMills.Construction.TriangleKernel YangMills.Construction.SmearingFilter
theorem distTwoPiInt_add_le (a b : ℝ) :
    distTwoPiInt (a + b) ≤ distTwoPiInt a + distTwoPiInt b := by
  rw [distTwoPiInt_eq_norm, distTwoPiInt_eq_norm, distTwoPiInt_eq_norm, AddCircle.coe_add]
  exact norm_add_le _ _
theorem distTwoPiInt_neg (a : ℝ) : distTwoPiInt (-a) = distTwoPiInt a := by
  rw [distTwoPiInt_eq_norm, distTwoPiInt_eq_norm, AddCircle.coe_neg, norm_neg]
theorem distTwoPiInt_of_mem_Ioc {v : ℝ} (hv : v ∈ Set.Ioc (-π) π) : distTwoPiInt v = |v| := by
  rw [distTwoPiInt_eq_norm, norm_addCircle_coe_of_mem_Ioc hv]
theorem half_pi_le_distTwoPiInt_half_pi : π / 2 ≤ distTwoPiInt (π / 2) := by
  have hpi := Real.pi_pos
  rw [distTwoPiInt_of_mem_Ioc ⟨by linarith, by linarith⟩, abs_of_pos (by linarith)]
theorem half_pi_le_distTwoPiInt_pi : π / 2 ≤ distTwoPiInt π := by
  have hpi := Real.pi_pos
  rw [distTwoPiInt_of_mem_Ioc ⟨by linarith, le_refl _⟩, abs_of_pos hpi]
  linarith
theorem half_pi_le_distTwoPiInt_neg_half_pi : π / 2 ≤ distTwoPiInt (-(π / 2)) := by
  rw [distTwoPiInt_neg]
  exact half_pi_le_distTwoPiInt_half_pi
theorem tentFunction_add_eq_zero
    (hBz : ∀ u : ℝ, π / 4 ≤ distTwoPiInt u → tentFunction u = 0) {u c : ℝ}
    (hu : distTwoPiInt u ≤ π / 4) (hc : π / 2 ≤ distTwoPiInt c) :
    tentFunction (u + c) = 0 := by
  apply hBz
  have h := distTwoPiInt_add_le (u + c) (-u)
  rw [distTwoPiInt_neg, show u + c + -u = c by ring] at h
  linarith
theorem abs_smearingSeq_le (j : ℤ) : |(smearingSeq j : ℝ)| ≤ 2 := by
  unfold smearingSeq
  split_ifs <;> norm_num
theorem exp_I_int_mul_eq_zpow {c : ℝ} {w : ℂ} (h : Complex.exp ((c : ℂ) * Complex.I) = w) (j : ℤ) :
    Complex.exp (Complex.I * j * c) = w ^ j := by
  rw [← h, ← Complex.exp_int_mul]
  congr 1
  ring
theorem exp_half_pi_mul_I : Complex.exp (((π / 2 : ℝ) : ℂ) * Complex.I) = Complex.I := by
  rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_pi_div_two,
    Real.sin_pi_div_two]
  simp
theorem exp_neg_half_pi_mul_I : Complex.exp (((-(π / 2) : ℝ) : ℂ) * Complex.I) = -Complex.I := by
  rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg, Real.sin_neg,
    Real.cos_pi_div_two, Real.sin_pi_div_two]
  simp
def SeqClosedForm : Prop :=
  ∀ j : ℤ, (smearingSeq j : ℂ) =
    1 / 2 * Complex.I ^ j - (-1 : ℂ) ^ j + 1 / 2 * (-Complex.I) ^ j
theorem smearingSeq_eq_sum_exp (hzc : SeqClosedForm) (j : ℤ) :
    (smearingSeq j : ℂ) =
      1 / 2 * Complex.exp (Complex.I * j * ((π / 2 : ℝ) : ℂ))
        - Complex.exp (Complex.I * j * (π : ℝ))
        + 1 / 2 * Complex.exp (Complex.I * j * ((-(π / 2) : ℝ) : ℂ)) := by
  rw [exp_I_int_mul_eq_zpow exp_half_pi_mul_I, exp_I_int_mul_eq_zpow Complex.exp_pi_mul_I,
    exp_I_int_mul_eq_zpow exp_neg_half_pi_mul_I]
  exact hzc j
theorem hasSum_smearingSeq_mul (hzc : SeqClosedForm) {c : ℤ → ℂ} {g : ℝ → ℂ}
    (hc : ∀ u : ℝ, HasSum (fun j : ℤ => c j * Complex.exp (Complex.I * j * u)) (g u)) (u : ℝ) :
    HasSum (fun j : ℤ => (smearingSeq j : ℂ) * c j * Complex.exp (Complex.I * j * u))
      (1 / 2 * g (u + π / 2) - g (u + π) + 1 / 2 * g (u + -(π / 2))) := by
  have h := (((hc (u + π / 2)).mul_left (1 / 2)).sub (hc (u + π))).add
    ((hc (u + -(π / 2))).mul_left (1 / 2))
  have e : (fun j : ℤ => (smearingSeq j : ℂ) * c j * Complex.exp (Complex.I * j * u)) =
      fun j : ℤ => 1 / 2 * (c j * Complex.exp (Complex.I * j * ((u + π / 2 : ℝ) : ℂ)))
        - c j * Complex.exp (Complex.I * j * ((u + π : ℝ) : ℂ))
        + 1 / 2 * (c j * Complex.exp (Complex.I * j * ((u + -(π / 2) : ℝ) : ℂ))) := by
    funext j
    have shift : ∀ a : ℝ, Complex.exp (Complex.I * j * ((u + a : ℝ) : ℂ)) =
        Complex.exp (Complex.I * j * u) * Complex.exp (Complex.I * j * (a : ℂ)) := fun a => by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [smearingSeq_eq_sum_exp hzc j, shift, shift, shift]
    ring
  rw [e]
  exact h
theorem filterSeries_eq_tent_shifts (hzc : SeqClosedForm)
    (hF : ∀ u : ℝ, HasSum
      (fun j : ℤ => tentFourierCoeff j * Complex.exp (Complex.I * j * u))
      (tentFunction u : ℂ)) (u : ℝ) :
    filterSeries u =
      ((1 / 2 * tentFunction (u + π / 2) - tentFunction (u + π)
        + 1 / 2 * tentFunction (u - π / 2) : ℝ) : ℂ) := by
  have h := (hasSum_smearingSeq_mul hzc (g := fun u => (tentFunction u : ℂ)) hF u).tsum_eq
  rw [filterSeries, h, sub_eq_add_neg u (π / 2)]
  push_cast
  ring
theorem filterProperties (hp : SeqAndTentProperties) : FilterProperties := by
  obtain ⟨⟨-, -, hzc⟩, ⟨hBc, hBb, hB0, hBz, -⟩, -, ⟨hF, -, -⟩, -⟩ := hp
  have hclosed := filterSeries_eq_tent_shifts hzc hF
  have hle : ∀ v : ℝ, tentFunction v ≤ 8 := fun v => hB0 ▸ (hBb v).2
  have hsup : (⨆ v : ℝ, tentFunction v) = 8 := by
    refine le_antisymm (ciSup_le hle) ?_
    rw [← hB0]
    exact le_ciSup (f := tentFunction) ⟨8, by rintro _ ⟨v, rfl⟩; exact hle v⟩ 0
  refine ⟨fun u => by rw [hclosed]; exact Complex.ofReal_im _, ?_, hclosed, fun u => ?_, hsup,
    fun u hu => ?_⟩
  · have e : filterSeries = fun u : ℝ =>
        ((1 / 2 * tentFunction (u + π / 2) - tentFunction (u + π)
          + 1 / 2 * tentFunction (u - π / 2) : ℝ) : ℂ) := funext hclosed
    rw [e]
    have h1 : Continuous fun u : ℝ => tentFunction (u + π / 2) :=
      hBc.comp (continuous_id.add continuous_const)
    have h2 : Continuous fun u : ℝ => tentFunction (u + π) :=
      hBc.comp (continuous_id.add continuous_const)
    have h3 : Continuous fun u : ℝ => tentFunction (u - π / 2) :=
      hBc.comp (continuous_id.sub continuous_const)
    exact Complex.continuous_ofReal.comp
      (((continuous_const.mul h1).sub h2).add (continuous_const.mul h3))
  · rw [hclosed, hsup, Complex.norm_real, Real.norm_eq_abs, abs_le]
    have a1 := hBb (u + π / 2)
    have a2 := hBb (u + π)
    have a3 := hBb (u - π / 2)
    constructor <;> linarith [a1.1, a2.1, a3.1]
  · rw [hclosed, sub_eq_add_neg u (π / 2),
      tentFunction_add_eq_zero hBz hu half_pi_le_distTwoPiInt_half_pi,
      tentFunction_add_eq_zero hBz hu half_pi_le_distTwoPiInt_pi,
      tentFunction_add_eq_zero hBz hu half_pi_le_distTwoPiInt_neg_half_pi]
    simp
theorem hasSum_int_of_even {a : ℤ → ℂ} (he : ∀ j, a (-j) = a j) (h0 : a 0 = 0) {S : ℂ}
    (h : HasSum (fun j : ℕ => 2 * a ((j : ℤ) + 1)) S) : HasSum a S := by
  have hh : HasSum (fun j : ℕ => a ((j : ℤ) + 1)) (S / 2) := by
    have e : (fun j : ℕ => a ((j : ℤ) + 1)) = fun j : ℕ => 1 / 2 * (2 * a ((j : ℤ) + 1)) := by
      funext j
      ring
    rw [e, show S / 2 = 1 / 2 * S by ring]
    exact h.mul_left _
  have hn : HasSum (fun j : ℕ => a (j : ℤ)) (S / 2) := by
    have h1 := (hasSum_nat_add_iff (f := fun j : ℕ => a (j : ℤ)) 1).mp (by simpa using hh)
    simpa [h0] using h1
  have hm : HasSum (fun j : ℕ => a (-((j : ℤ) + 1))) (S / 2) := by
    simpa only [he] using hh
  have h2 := hn.of_nat_of_neg_add_one hm
  rwa [add_halves] at h2
def weightCoeff (j : ℕ) : ℝ :=
  (smearingSeq ((j : ℤ) + 1) : ℝ) * (tentFourierCoeff ((j : ℤ) + 1)).re
theorem tentFourierCoeff_eq_ofReal_re
    (hbr : ∀ j : ℤ, (tentFourierCoeff j).im = 0 ∧ 0 ≤ (tentFourierCoeff j).re) (j : ℤ) :
    tentFourierCoeff j = ((tentFourierCoeff j).re : ℂ) :=
  Complex.ext (by simp) (by simp [(hbr j).1])
theorem weightSeries_im_eq_zero_and_hasSum_re (hp : SeqAndTentProperties)
    (hs : SeriesConvergence.SeriesConverge) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (weightSeries t).im = 0 ∧
      HasSum (fun j : ℕ => 2 * (weightCoeff j * t ^ j)) (weightSeries t).re := by
  obtain ⟨-, -, ⟨-, -, -, hbr, -, -⟩, -, -⟩ := hp
  obtain ⟨-, -, ⟨-, -, hW, -⟩⟩ := hs
  have h := hW t ht
  have e : (fun j : ℕ => 2 * ((smearingSeq ((j : ℤ) + 1) : ℂ) *
      tentFourierCoeff ((j : ℤ) + 1) * (t : ℂ) ^ j)) =
      fun j : ℕ => ((2 * (weightCoeff j * t ^ j) : ℝ) : ℂ) := by
    funext j
    rw [tentFourierCoeff_eq_ofReal_re hbr ((j : ℤ) + 1), weightCoeff]
    push_cast
    ring
  rw [e] at h
  have hre := Complex.hasSum_re h
  have him := Complex.hasSum_im h
  simp only [Complex.ofReal_re] at hre
  simp only [Complex.ofReal_im] at him
  exact ⟨him.unique hasSum_zero, hre⟩
theorem weightSeries_re_le (hp : SeqAndTentProperties)
    (hs : SeriesConvergence.SeriesConverge) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (weightSeries t).re ≤ 2 * absCoeffSum := by
  obtain ⟨-, h⟩ := weightSeries_im_eq_zero_and_hasSum_re hp hs ht
  obtain ⟨-, -, ⟨-, -, -, hbr, -, -⟩, -, ⟨hS, -, -, -⟩⟩ := hp
  have hinj : Function.Injective fun j : ℕ => (j : ℤ) + 1 := fun a b hab => by
    simpa using hab
  have hnn : ∀ j : ℤ, 0 ≤ |(smearingSeq j : ℝ)| * (tentFourierCoeff j).re :=
    fun j => mul_nonneg (abs_nonneg _) (hbr j).2
  have hm : Summable fun j : ℕ => |(smearingSeq ((j : ℤ) + 1) : ℝ)| *
      (tentFourierCoeff ((j : ℤ) + 1)).re := hS.comp_injective hinj
  have hle : ∑' j : ℕ, |(smearingSeq ((j : ℤ) + 1) : ℝ)| *
      (tentFourierCoeff ((j : ℤ) + 1)).re ≤ absCoeffSum :=
    tsum_comp_le_tsum_of_inj hS hnn hinj
  have hterm : ∀ j : ℕ, 2 * (weightCoeff j * t ^ j) ≤
      2 * (|(smearingSeq ((j : ℤ) + 1) : ℝ)| * (tentFourierCoeff ((j : ℤ) + 1)).re) := by
    intro j
    have ht0 : 0 ≤ t ^ j := pow_nonneg ht.1 j
    have ht1 : t ^ j ≤ 1 := pow_le_one₀ ht.1 ht.2
    have hw : weightCoeff j ≤
        |(smearingSeq ((j : ℤ) + 1) : ℝ)| * (tentFourierCoeff ((j : ℤ) + 1)).re :=
      mul_le_mul_of_nonneg_right (le_abs_self _) (hbr _).2
    have hm0 := hnn ((j : ℤ) + 1)
    nlinarith [mul_nonneg (sub_nonneg.2 hw) ht0, mul_nonneg hm0 (sub_nonneg.2 ht1)]
  have h3 := hasSum_le hterm h (hm.hasSum.mul_left 2)
  linarith
theorem weightSeries_zero_re_nonneg (hp : SeqAndTentProperties)
    (hs : SeriesConvergence.SeriesConverge) : 0 ≤ (weightSeries 0).re := by
  obtain ⟨-, h⟩ := weightSeries_im_eq_zero_and_hasSum_re hp hs (t := 0) (by simp)
  obtain ⟨-, -, ⟨-, -, -, hbr, -, -⟩, -, -⟩ := hp
  have h0 : HasSum (fun j : ℕ => 2 * (weightCoeff j * (0 : ℝ) ^ j))
      (2 * (weightCoeff 0 * (0 : ℝ) ^ 0)) :=
    hasSum_single 0 fun j hj => by simp [hj]
  rw [h.unique h0]
  have h1 : smearingSeq (((0 : ℕ) : ℤ) + 1) = 1 := by decide
  have h2 := (hbr (((0 : ℕ) : ℤ) + 1)).2
  simp only [weightCoeff, h1, pow_zero, mul_one, Int.cast_one, one_mul]
  linarith
theorem weightSeries_one_eq_filterSeries_zero (hp : SeqAndTentProperties)
    (hs : SeriesConvergence.SeriesConverge) : weightSeries 1 = filterSeries 0 := by
  obtain ⟨-, -, -, -, ⟨-, -, hze, hz0⟩⟩ := hp
  obtain ⟨-, ⟨-, -, hF, -⟩, ⟨-, -, hW, -⟩⟩ := hs
  have h1 := hW 1 (by simp)
  have h0 := hF 0
  refine HasSum.unique (hasSum_int_of_even (fun j => ?_) ?_ ?_) h0
  · simpa using hze j
  · simpa using hz0
  · simpa using h1
def poissonKernel (r u : ℝ) : ℝ :=
  (1 - r ^ 2) / (1 - 2 * r * Real.cos u + r ^ 2)
theorem poissonDenom_pos {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (u : ℝ) :
    0 < 1 - 2 * r * Real.cos u + r ^ 2 := by
  nlinarith [mul_le_mul_of_nonneg_left (Real.cos_le_one u) hr0.le,
    mul_pos (sub_pos.2 hr1) (sub_pos.2 hr1)]
theorem inv_add_mul_inv_eq {q p R : ℂ} (hq : 1 - q ≠ 0) (hp : 1 - p ≠ 0) (h : q * p = R) :
    (1 - q)⁻¹ + p * (1 - p)⁻¹ = (1 - R) / ((1 - q) * (1 - p)) := by
  field_simp
  linear_combination -h
theorem hasSum_poissonKernel {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (u : ℝ) :
    HasSum (fun j : ℤ => ((r ^ j.natAbs : ℝ) : ℂ) * Complex.exp (Complex.I * j * u))
      (poissonKernel r u : ℂ) := by
  obtain ⟨E, hE⟩ : ∃ E, E = Complex.exp (Complex.I * u) := ⟨_, rfl⟩
  obtain ⟨F, hF⟩ : ∃ F, F = Complex.exp (-(Complex.I * u)) := ⟨_, rfl⟩
  have hEF : E * F = 1 := by
    rw [hE, hF, ← Complex.exp_add]
    simp
  have hcos : Complex.cos (u : ℂ) = (E + F) / 2 := by
    rw [Complex.cos, hE, hF, mul_comm Complex.I, neg_mul]
  have hnE : ‖E‖ = 1 := by
    rw [hE, mul_comm]
    exact Complex.norm_exp_ofReal_mul_I u
  have hnF : ‖F‖ = 1 := by
    have e : -(Complex.I * u) = ((-u : ℝ) : ℂ) * Complex.I := by
      push_cast
      ring
    rw [hF, e]
    exact Complex.norm_exp_ofReal_mul_I _
  have hnq : ‖(r : ℂ) * E‖ < 1 := by
    rw [norm_mul, hnE, mul_one, Complex.norm_real, Real.norm_of_nonneg hr0.le]
    exact hr1
  have hnp : ‖(r : ℂ) * F‖ < 1 := by
    rw [norm_mul, hnF, mul_one, Complex.norm_real, Real.norm_of_nonneg hr0.le]
    exact hr1
  have hD : (1 - (r : ℂ) * E) * (1 - (r : ℂ) * F) =
      ((1 - 2 * r * Real.cos u + r ^ 2 : ℝ) : ℂ) := by
    push_cast
    rw [hcos]
    linear_combination (r : ℂ) ^ 2 * hEF
  have hDne : ((1 - 2 * r * Real.cos u + r ^ 2 : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (poissonDenom_pos hr0 hr1 u).ne'
  have hq : 1 - (r : ℂ) * E ≠ 0 := left_ne_zero_of_mul (hD ▸ hDne)
  have hp : 1 - (r : ℂ) * F ≠ 0 := right_ne_zero_of_mul (hD ▸ hDne)
  have hsum := inv_add_mul_inv_eq hq hp
    (show (r : ℂ) * E * ((r : ℂ) * F) = (r : ℂ) ^ 2 by linear_combination (r : ℂ) ^ 2 * hEF)
  have hval : (poissonKernel r u : ℂ) = (1 - (r : ℂ) * E)⁻¹ +
      (r : ℂ) * F * (1 - (r : ℂ) * F)⁻¹ := by
    rw [hsum, hD, poissonKernel]
    push_cast
    rfl
  rw [hval]
  refine HasSum.of_nat_of_neg_add_one ?_ ?_
  · have e : (fun n : ℕ => ((r ^ ((n : ℤ)).natAbs : ℝ) : ℂ) *
        Complex.exp (Complex.I * ((n : ℤ) : ℂ) * u)) = fun n : ℕ => ((r : ℂ) * E) ^ n := by
      funext n
      have e1 : Complex.I * ((n : ℤ) : ℂ) * u = (n : ℂ) * (Complex.I * u) := by
        push_cast
        ring
      rw [e1, Complex.exp_nat_mul, ← hE, Int.natAbs_natCast, mul_pow]
      push_cast
      rfl
    rw [e]
    exact hasSum_geometric_of_norm_lt_one hnq
  · have e : (fun n : ℕ => ((r ^ (-((n : ℤ) + 1)).natAbs : ℝ) : ℂ) *
        Complex.exp (Complex.I * ((-((n : ℤ) + 1) : ℤ) : ℂ) * u)) =
        fun n : ℕ => (r : ℂ) * F * ((r : ℂ) * F) ^ n := by
      funext n
      have e0 : (-((n : ℤ) + 1)).natAbs = n + 1 := by omega
      have e1 : Complex.I * ((-((n : ℤ) + 1) : ℤ) : ℂ) * u =
          ((n + 1 : ℕ) : ℂ) * (-(Complex.I * u)) := by
        push_cast
        ring
      rw [e0, e1, Complex.exp_nat_mul, ← hF, ← pow_succ', mul_pow]
      push_cast
      rfl
    rw [e]
    exact (hasSum_geometric_of_norm_lt_one hnp).mul_left _
theorem summable_pow_natAbs {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    Summable fun j : ℤ => r ^ j.natAbs := by
  have h := summable_norm_iff.mpr (hasSum_poissonKernel hr0 hr1 0).summable
  have e : (fun j : ℤ => ‖((r ^ j.natAbs : ℝ) : ℂ) *
      Complex.exp (Complex.I * j * ((0 : ℝ) : ℂ))‖) = fun j : ℤ => r ^ j.natAbs := by
    funext j
    simp [abs_of_pos hr0]
  rwa [e] at h
def shiftedPoisson (r u : ℝ) : ℝ :=
  1 / 2 * poissonKernel r (u + π / 2) - poissonKernel r (u + π)
    + 1 / 2 * poissonKernel r (u + -(π / 2))
theorem continuous_shiftedPoisson {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    Continuous (shiftedPoisson r) := by
  have hP : Continuous (poissonKernel r) :=
    continuous_const.div (by fun_prop) fun u => (poissonDenom_pos hr0 hr1 u).ne'
  have h1 : Continuous fun u : ℝ => poissonKernel r (u + π / 2) :=
    hP.comp (continuous_id.add continuous_const)
  have h2 : Continuous fun u : ℝ => poissonKernel r (u + π) :=
    hP.comp (continuous_id.add continuous_const)
  have h3 : Continuous fun u : ℝ => poissonKernel r (u + -(π / 2)) :=
    hP.comp (continuous_id.add continuous_const)
  exact ((continuous_const.mul h1).sub h2).add (continuous_const.mul h3)
theorem half_one_div_add_half_one_div {a b A : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (h : a + b = 2 * A) :
    1 / 2 * (1 / a) + 1 / 2 * (1 / b) = A / (a * b) := by
  field_simp
  linarith
def poissonLowerBound (r : ℝ) : ℝ :=
  (1 - r ^ 2) * (1 / (1 + r ^ 2) - 1 / (1 + r ^ 2 + √2 * r))
theorem poissonLowerBound_le_shiftedPoisson {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) {v : ℝ}
    (hv : |v| ≤ π / 4) : poissonLowerBound r ≤ shiftedPoisson r (-v) := by
  have hpi := Real.pi_pos
  have hc : √2 / 2 ≤ Real.cos v := by
    rw [← Real.cos_abs v, ← Real.cos_pi_div_four]
    exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg v) (by linarith) hv
  have e1 : Real.cos (-v + π / 2) = Real.sin v := by
    rw [Real.cos_add_pi_div_two, Real.sin_neg, neg_neg]
  have e2 : Real.cos (-v + π) = -Real.cos v := by
    rw [Real.cos_add_pi, Real.cos_neg]
  have e3 : Real.cos (-v + -(π / 2)) = -Real.sin v := by
    rw [← sub_eq_add_neg, Real.cos_sub_pi_div_two, Real.sin_neg]
  have d1 := poissonDenom_pos hr0 hr1 (-v + π / 2)
  have d2 := poissonDenom_pos hr0 hr1 (-v + π)
  have d3 := poissonDenom_pos hr0 hr1 (-v + -(π / 2))
  rw [e1] at d1
  rw [e2] at d2
  rw [e3] at d3
  have hA : 0 < 1 + r ^ 2 := by positivity
  have hW : 0 < 1 + r ^ 2 + √2 * r := by positivity
  have hN : 0 ≤ 1 - r ^ 2 := by nlinarith
  have h1 : 1 / (1 + r ^ 2) ≤ 1 / 2 * (1 / (1 - 2 * r * Real.sin v + r ^ 2))
      + 1 / 2 * (1 / (1 - 2 * r * -Real.sin v + r ^ 2)) := by
    rw [half_one_div_add_half_one_div d1.ne' d3.ne' (A := 1 + r ^ 2) (by ring),
      div_le_div_iff₀ hA (mul_pos d1 d3)]
    nlinarith [sq_nonneg (2 * r * Real.sin v)]
  have h2 : 1 / (1 - 2 * r * -Real.cos v + r ^ 2) ≤ 1 / (1 + r ^ 2 + √2 * r) := by
    apply one_div_le_one_div_of_le hW
    nlinarith [mul_le_mul_of_nonneg_left hc hr0.le]
  have h3 := mul_le_mul_of_nonneg_left
    (show 1 / (1 + r ^ 2) - 1 / (1 + r ^ 2 + √2 * r) ≤
      1 / 2 * (1 / (1 - 2 * r * Real.sin v + r ^ 2))
        - 1 / (1 - 2 * r * -Real.cos v + r ^ 2)
        + 1 / 2 * (1 / (1 - 2 * r * -Real.sin v + r ^ 2)) by linarith) hN
  unfold shiftedPoisson poissonKernel poissonLowerBound
  rw [e1, e2, e3]
  calc _ ≤ _ := h3
    _ = _ := by ring
theorem norm_seq_mul_pow_mul_tent_le {r : ℝ} (hr0 : 0 < r)
    (hB : ∀ v : ℝ, 0 ≤ tentFunction v ∧ tentFunction v ≤ 8) (j : ℤ) (v : ℝ) :
    ‖(smearingSeq j : ℂ) * ((r ^ j.natAbs : ℝ) : ℂ) *
      ((tentFunction v : ℂ) * Complex.exp (-(Complex.I * j * v)))‖ ≤ 16 * r ^ j.natAbs := by
  have e : -(Complex.I * j * v) = ((-((j : ℝ) * v) : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  have hpow : 0 ≤ r ^ j.natAbs := pow_nonneg hr0.le _
  rw [norm_mul, norm_mul, norm_mul, e, Complex.norm_exp_ofReal_mul_I, Complex.norm_intCast,
    Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg hpow,
    Real.norm_of_nonneg (hB v).1, mul_one]
  calc |(smearingSeq j : ℝ)| * r ^ j.natAbs * tentFunction v
      ≤ 2 * r ^ j.natAbs * 8 :=
        mul_le_mul (mul_le_mul_of_nonneg_right (abs_smearingSeq_le j) hpow) (hB v).2 (hB v).1
          (by positivity)
    _ = 16 * r ^ j.natAbs := by ring
theorem mul_weightSeries_eq_integral (hp : SeqAndTentProperties)
    (hs : SeriesConvergence.SeriesConverge) {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    (r : ℂ) * weightSeries r =
      ((1 / (2 * π) * ∫ v in (-π)..π, tentFunction v * shiftedPoisson r (-v) : ℝ) : ℂ) := by
  obtain ⟨⟨hzn, hz0, hzc⟩, ⟨hBc, hBb, hB0, -, -⟩, ⟨-, -, hbe, -, -, -⟩, -, -⟩ := hp
  obtain ⟨-, -, ⟨-, -, hW, -⟩⟩ := hs
  have hB : ∀ v : ℝ, 0 ≤ tentFunction v ∧ tentFunction v ≤ 8 :=
    fun v => ⟨(hBb v).1, hB0 ▸ (hBb v).2⟩
  have h1 : HasSum (fun j : ℤ => (smearingSeq j : ℂ) * ((r ^ j.natAbs : ℝ) : ℂ) *
      tentFourierCoeff j) ((r : ℂ) * weightSeries r) := by
    refine hasSum_int_of_even (fun j => ?_) ?_ ?_
    · rw [hzn, Int.natAbs_neg, ← hbe]
    · simp [hz0]
    · have h := (hW r ⟨hr0.le, hr1.le⟩).mul_left (r : ℂ)
      have e : (fun j : ℕ => 2 * ((smearingSeq ((j : ℤ) + 1) : ℂ) *
          ((r ^ ((j : ℤ) + 1).natAbs : ℝ) : ℂ) * tentFourierCoeff ((j : ℤ) + 1))) =
          fun j : ℕ => (r : ℂ) * (2 * ((smearingSeq ((j : ℤ) + 1) : ℂ) *
            tentFourierCoeff ((j : ℤ) + 1) * (r : ℂ) ^ j)) := by
        funext j
        have e0 : ((j : ℤ) + 1).natAbs = j + 1 := by omega
        rw [e0]
        push_cast
        ring
      rw [e]
      exact h
  have key : HasSum (fun j : ℤ => ∫ v in (-π)..π, (smearingSeq j : ℂ) *
      ((r ^ j.natAbs : ℝ) : ℂ) *
        ((tentFunction v : ℂ) * Complex.exp (-(Complex.I * j * v))))
      (∫ v in (-π)..π, ((tentFunction v * shiftedPoisson r (-v) : ℝ) : ℂ)) := by
    apply intervalIntegral.hasSum_integral_of_dominated_convergence
      (fun j _ => 16 * r ^ j.natAbs)
    · intro j
      have hcont : Continuous fun v : ℝ => (smearingSeq j : ℂ) *
          ((r ^ j.natAbs : ℝ) : ℂ) *
          ((tentFunction v : ℂ) * Complex.exp (-(Complex.I * j * v))) :=
        continuous_const.mul ((Complex.continuous_ofReal.comp hBc).mul
          (Complex.continuous_exp.comp (by fun_prop)))
      exact hcont.aestronglyMeasurable
    · intro j
      exact .of_forall fun v _ => norm_seq_mul_pow_mul_tent_le hr0 hB j v
    · exact .of_forall fun v _ => (summable_pow_natAbs hr0 hr1).mul_left 16
    · exact intervalIntegrable_const
    · refine .of_forall fun v _ => ?_
      have h3 := (hasSum_smearingSeq_mul hzc (c := fun j : ℤ => ((r ^ j.natAbs : ℝ) : ℂ))
        (g := fun u => (poissonKernel r u : ℂ)) (hasSum_poissonKernel hr0 hr1) (-v)).mul_left
        (tentFunction v : ℂ)
      have ev : (fun j : ℤ => (smearingSeq j : ℂ) * ((r ^ j.natAbs : ℝ) : ℂ) *
          ((tentFunction v : ℂ) * Complex.exp (-(Complex.I * j * v)))) =
          fun j : ℤ => (tentFunction v : ℂ) * ((smearingSeq j : ℂ) *
            ((r ^ j.natAbs : ℝ) : ℂ) * Complex.exp (Complex.I * j * ((-v : ℝ) : ℂ))) := by
        funext j
        have e : Complex.I * j * ((-v : ℝ) : ℂ) = -(Complex.I * j * v) := by
          push_cast
          ring
        rw [e]
        ring
      have vv : ((tentFunction v * shiftedPoisson r (-v) : ℝ) : ℂ) = (tentFunction v : ℂ) *
          (1 / 2 * (poissonKernel r (-v + π / 2) : ℂ) - (poissonKernel r (-v + π) : ℂ)
            + 1 / 2 * (poissonKernel r (-v + -(π / 2)) : ℂ)) := by
        rw [shiftedPoisson]
        push_cast
        ring
      rw [ev, vv]
      exact h3
  have h2 := key.mul_left (1 / (2 * (π : ℂ)))
  have e : (fun j : ℤ => 1 / (2 * (π : ℂ)) * ∫ v in (-π)..π, (smearingSeq j : ℂ) *
      ((r ^ j.natAbs : ℝ) : ℂ) *
        ((tentFunction v : ℂ) * Complex.exp (-(Complex.I * j * v)))) =
      fun j : ℤ => (smearingSeq j : ℂ) * ((r ^ j.natAbs : ℝ) : ℂ) *
        tentFourierCoeff j := by
    funext j
    rw [intervalIntegral.integral_const_mul, tentFourierCoeff]
    ring
  rw [e, intervalIntegral.integral_ofReal] at h2
  rw [h1.unique h2]
  push_cast
  rfl
theorem poissonLowerBound_le_mul_weightSeries_re (hp : SeqAndTentProperties)
    (hs : SeriesConvergence.SeriesConverge) {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    poissonLowerBound r ≤ r * (weightSeries r).re := by
  have hI := congrArg Complex.re (mul_weightSeries_eq_integral hp hs hr0 hr1)
  rw [Complex.re_ofReal_mul, Complex.ofReal_re] at hI
  rw [hI]
  obtain ⟨-, ⟨hBc, hBb, -, -, hBm⟩, -, -, -⟩ := hp
  have hpi := Real.pi_pos
  have hmono : ∫ v in (-π)..π, poissonLowerBound r * tentFunction v ≤
      ∫ v in (-π)..π, tentFunction v * shiftedPoisson r (-v) := by
    apply intervalIntegral.integral_mono_on (by linarith)
    · exact (continuous_const.mul hBc).intervalIntegrable _ _
    · exact (hBc.mul ((continuous_shiftedPoisson hr0 hr1).comp continuous_neg)).intervalIntegrable _ _
    · intro v hv
      by_cases h : |v| ≤ π / 4
      · rw [mul_comm]
        exact mul_le_mul_of_nonneg_left (poissonLowerBound_le_shiftedPoisson hr0 hr1 h) (hBb v).1
      · have h0 : tentFunction v = 0 := by
          rw [isTentFunction_tentFunction.formula v (abs_le.2 hv)]
          have h4 : 1 ≤ 4 * |v| / π := by
            rw [le_div_iff₀ hpi]
            linarith [not_le.1 h]
          rw [max_eq_right (by linarith), mul_zero]
        rw [h0]
        simp
  rw [intervalIntegral.integral_const_mul] at hmono
  have h2 : 0 ≤ 1 / (2 * π) := by positivity
  calc poissonLowerBound r
        = poissonLowerBound r * (1 / (2 * π) * ∫ u in (-π)..π, tentFunction u) := by
        rw [hBm, mul_one]
    _ = 1 / (2 * π) * (poissonLowerBound r * ∫ u in (-π)..π, tentFunction u) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hmono h2
theorem tanh_eq_of_exp_neg {y r : ℝ} (hr : r = Real.exp (-y)) :
    Real.tanh y = (1 - r ^ 2) / (1 + r ^ 2) := by
  have hr0 : 0 < r := hr ▸ Real.exp_pos _
  have hy : Real.exp y * r = 1 := by
    rw [hr, ← Real.exp_add]
    simp
  rw [Real.tanh_eq_sinh_div_cosh, Real.sinh_eq, Real.cosh_eq, ← hr,
    div_div_div_cancel_right₀ (two_ne_zero), div_eq_div_iff (by positivity) (by positivity)]
  linear_combination 2 * r * hy
theorem weightConst_mul_le_poissonLowerBound {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    weightConst * ((1 - r ^ 2) / (1 + r ^ 2)) * r ≤ poissonLowerBound r := by
  have hs2 : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hs0 : 0 ≤ √2 := Real.sqrt_nonneg 2
  have hs1 : 1 ≤ √2 := Real.one_le_sqrt.2 (by norm_num)
  have hA : 0 < 1 + r ^ 2 := by positivity
  have hW : 0 < 1 + r ^ 2 + √2 * r := by positivity
  have hN : 0 ≤ 1 - r ^ 2 := by nlinarith
  have hb : 1 + r ^ 2 + √2 * r ≤ 2 + √2 := by nlinarith
  have hc : (√2 - 1) * (1 + r ^ 2 + √2 * r) ≤ √2 := by
    calc (√2 - 1) * (1 + r ^ 2 + √2 * r) ≤ (√2 - 1) * (2 + √2) :=
          mul_le_mul_of_nonneg_left hb (by linarith)
      _ = √2 := by linear_combination hs2
  have e : 1 / (1 + r ^ 2) - 1 / (1 + r ^ 2 + √2 * r) =
      √2 * r / ((1 + r ^ 2) * (1 + r ^ 2 + √2 * r)) := by
    field_simp
    ring
  have h1 : (√2 - 1) * r / (1 + r ^ 2) ≤ √2 * r / ((1 + r ^ 2) * (1 + r ^ 2 + √2 * r)) := by
    rw [div_le_div_iff₀ hA (mul_pos hA hW)]
    nlinarith [mul_le_mul_of_nonneg_left hc (mul_pos hr0 hA).le]
  rw [poissonLowerBound, e, weightConst]
  calc (√2 - 1) * ((1 - r ^ 2) / (1 + r ^ 2)) * r
      = (1 - r ^ 2) * ((√2 - 1) * r / (1 + r ^ 2)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left h1 hN
theorem exp_neg_lt_one_of_pos {y : ℝ} (hy : 0 < y) : Real.exp (-y) < 1 := by
  rw [← Real.exp_zero]
  exact Real.exp_lt_exp.2 (by linarith)
theorem weightConst_mul_tanh_le (hp : SeqAndTentProperties)
    (hs : SeriesConvergence.SeriesConverge) {y : ℝ} (hy : 0 < y) :
    weightConst * Real.tanh y ≤ (weightSeries (Real.exp (-y))).re := by
  have hr0 : 0 < Real.exp (-y) := Real.exp_pos _
  have hr1 : Real.exp (-y) < 1 := exp_neg_lt_one_of_pos hy
  have h1 := weightConst_mul_le_poissonLowerBound hr0 hr1
  have h2 := poissonLowerBound_le_mul_weightSeries_re hp hs hr0 hr1
  rw [← tanh_eq_of_exp_neg rfl] at h1
  rw [mul_comm (Real.exp (-y))] at h2
  exact le_of_mul_le_mul_right (h1.trans h2) hr0
theorem tanh_pos_of_pos {y : ℝ} (hy : 0 < y) : 0 < Real.tanh y := by
  rw [Real.tanh_eq_sinh_div_cosh]
  exact div_pos (Real.sinh_pos_iff.2 hy) (Real.cosh_pos y)
theorem weightSeries_re_nonneg (hp : SeqAndTentProperties)
    (hs : SeriesConvergence.SeriesConverge) (hone : weightSeries 1 = 0) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) : 0 ≤ (weightSeries t).re := by
  rcases ht.1.eq_or_lt with rfl | h0
  · exact weightSeries_zero_re_nonneg hp hs
  rcases ht.2.eq_or_lt with rfl | h1
  · rw [hone]
    simp
  have hy : 0 < -Real.log t := by
    have := Real.log_neg h0 h1
    linarith
  have h := weightConst_mul_tanh_le hp hs hy
  rw [neg_neg, Real.exp_log h0] at h
  have hc : 0 < weightConst := by
    have : 1 < √2 := Real.one_lt_sqrt_two
    rw [weightConst]
    linarith
  exact (mul_pos hc (tanh_pos_of_pos hy)).le.trans h
theorem weightProperties (hp : SeqAndTentProperties)
    (hs : SeriesConvergence.SeriesConverge) : WeightProperties := by
  have hzero : filterSeries 0 = 0 := by
    obtain ⟨-, -, -, -, -, h⟩ := filterProperties hp
    apply h
    have hpi := Real.pi_pos
    rw [distTwoPiInt_of_mem_Ioc ⟨by linarith, hpi.le⟩, abs_zero]
    positivity
  have hone := weightSeries_one_eq_filterSeries_zero hp hs
  refine ⟨?_, fun t ht => ⟨(weightSeries_im_eq_zero_and_hasSum_re hp hs ht).1,
    weightSeries_re_nonneg hp hs (hone.trans hzero) ht, weightSeries_re_le hp hs ht⟩, hone, hzero,
    fun x h0 hinf => ?_⟩
  · obtain ⟨-, -, ⟨-, -, hW, hU⟩⟩ := hs
    exact hU.continuousOn (Filter.Frequently.of_forall fun s =>
      Continuous.continuousOn (by fun_prop))
  · have hy : 0 < x.toReal := ENNReal.toReal_pos h0.ne' hinf.ne
    have e : weightSeriesAtExp x = weightSeries (Real.exp (-x.toReal)) := by
      simp [weightSeriesAtExp, extendedExpNeg, hinf.ne]
    rw [e]
    exact ⟨(weightSeries_im_eq_zero_and_hasSum_re hp hs ⟨(Real.exp_pos _).le,
      (exp_neg_lt_one_of_pos hy).le⟩).1, weightConst_mul_tanh_le hp hs hy⟩
theorem filterWeightBounds_holds (hp : SeqAndTentProperties)
    (hs : SeriesConvergence.SeriesConverge) : FilterWeightBounds :=
  ⟨filterProperties hp, weightProperties hp hs⟩
end YangMills.Construction.SmearingFilter.Bounds
