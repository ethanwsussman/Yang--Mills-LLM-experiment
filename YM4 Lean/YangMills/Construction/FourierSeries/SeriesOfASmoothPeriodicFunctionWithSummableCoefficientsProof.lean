import YangMills.Construction.FourierSeries.FejerMeansUniformLimit
import YangMills.Construction.FourierSeries.SeriesOfASmoothPeriodicFunctionWithSummableCoefficients
import Mathlib
set_option autoImplicit false
open MeasureTheory Filter Topology
open scoped Matrix
noncomputable section
namespace YangMills.Construction.FourierSeries.SmoothPeriodicSummable
variable {D : ℕ}
def torusCube (D : ℕ) : Set (Fin D → ℝ) :=
  Set.pi Set.univ (fun _ : Fin D => Set.Icc (-Real.pi) Real.pi)
def fourierChar (k : Fin D → ℤ) (y : Fin D → ℝ) : ℂ :=
  Complex.exp ((∑ j, (k j : ℂ) * (y j : ℂ)) * Complex.I)
def fourierCharConj (k : Fin D → ℤ) (y : Fin D → ℝ) : ℂ :=
  Complex.exp (-((∑ j, (k j : ℂ) * (y j : ℂ)) * Complex.I))
theorem continuous_fourierChar (k : Fin D → ℤ) : Continuous (fourierChar k) := by
  unfold fourierChar
  fun_prop
theorem continuous_fourierCharConj (k : Fin D → ℤ) : Continuous (fourierCharConj k) := by
  unfold fourierCharConj
  fun_prop
theorem intSum_mul_eq_ofReal (k : Fin D → ℤ) (y : Fin D → ℝ) :
    (∑ j, (k j : ℂ) * (y j : ℂ)) = ((∑ j, (k j : ℝ) * y j : ℝ) : ℂ) := by
  push_cast
  rfl
theorem norm_fourierChar (k : Fin D → ℤ) (y : Fin D → ℝ) : ‖fourierChar k y‖ = 1 := by
  unfold fourierChar
  rw [intSum_mul_eq_ofReal, Complex.norm_exp_ofReal_mul_I]
theorem norm_fourierCharConj (k : Fin D → ℤ) (y : Fin D → ℝ) : ‖fourierCharConj k y‖ = 1 := by
  unfold fourierCharConj
  rw [intSum_mul_eq_ofReal, ← neg_mul, ← Complex.ofReal_neg, Complex.norm_exp_ofReal_mul_I]
theorem isCompact_torusCube : IsCompact (torusCube D) :=
  isCompact_univ_pi fun _ => isCompact_Icc
theorem measurableSet_torusCube : MeasurableSet (torusCube D) :=
  MeasurableSet.univ_pi fun _ => measurableSet_Icc
theorem integral_Icc_exp_int_mul_I (n : ℤ) :
    ∫ u in Set.Icc (-Real.pi) Real.pi, Complex.exp ((n : ℂ) * (u : ℂ) * Complex.I) =
      if n = 0 then 2 * (Real.pi : ℂ) else 0 := by
  have hle : -Real.pi ≤ Real.pi := by linarith [Real.pi_pos]
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hle]
  split_ifs with hn
  · subst hn
    simp
    ring
  · have hc : (n : ℂ) * Complex.I ≠ 0 :=
      mul_ne_zero (by exact_mod_cast hn) Complex.I_ne_zero
    have hrew : ∀ u : ℝ, Complex.exp ((n : ℂ) * (u : ℂ) * Complex.I) =
        Complex.exp (((n : ℂ) * Complex.I) * (u : ℂ)) := fun u => by ring_nf
    simp only [hrew]
    rw [integral_exp_mul_complex hc]
    have hper : Complex.exp ((n : ℂ) * Complex.I * (Real.pi : ℂ)) =
        Complex.exp ((n : ℂ) * Complex.I * ((-Real.pi : ℝ) : ℂ)) := by
      have h2 : (n : ℂ) * Complex.I * (Real.pi : ℂ) =
          (n : ℂ) * Complex.I * ((-Real.pi : ℝ) : ℂ) + (n : ℂ) * (2 * Real.pi * Complex.I) := by
        push_cast
        ring
      rw [h2, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
    rw [hper, sub_self, zero_div]
theorem integral_fourierChar_mul_fourierCharConj (j k : Fin D → ℤ) :
    ∫ y in torusCube D, fourierChar j y * fourierCharConj k y =
      if j = k then (2 * (Real.pi : ℂ)) ^ D else 0 := by
  have hprod : ∀ y : Fin D → ℝ, fourierChar j y * fourierCharConj k y =
      ∏ l, Complex.exp (((j l - k l : ℤ) : ℂ) * (y l : ℂ) * Complex.I) := by
    intro y
    unfold fourierChar fourierCharConj
    rw [← Complex.exp_add, ← Complex.exp_sum]
    congr 1
    push_cast
    simp only [sub_mul, Finset.sum_sub_distrib, Finset.sum_mul]
    ring
  simp only [hprod]
  unfold torusCube
  rw [volume_pi, Measure.restrict_pi_pi]
  rw [integral_fintype_prod_eq_prod
    (f := fun l (u : ℝ) => Complex.exp (((j l - k l : ℤ) : ℂ) * (u : ℂ) * Complex.I))]
  simp only [integral_Icc_exp_int_mul_I]
  split_ifs with hjk
  · subst hjk
    simp
  · obtain ⟨l, hl⟩ := Function.ne_iff.mp hjk
    refine Finset.prod_eq_zero (Finset.mem_univ l) ?_
    rw [if_neg (sub_ne_zero.mpr hl)]
def charSeries (c : (Fin D → ℤ) → ℂ) (y : Fin D → ℝ) : ℂ :=
  ∑' k, c k * fourierChar k y
theorem continuous_charSeries {c : (Fin D → ℤ) → ℂ} (hc : Summable fun k => ‖c k‖) :
    Continuous (charSeries c) := by
  unfold charSeries
  refine continuous_tsum (fun k => continuous_const.mul (continuous_fourierChar k)) hc ?_
  intro k y
  rw [norm_mul, norm_fourierChar, mul_one]
theorem fourierChar_update_add_two_pi (k : Fin D → ℤ) (j : Fin D) (y : Fin D → ℝ) :
    fourierChar k (Function.update y j (y j + 2 * Real.pi)) = fourierChar k y := by
  have hsum : (∑ l, (k l : ℂ) * ((Function.update y j (y j + 2 * Real.pi) l : ℝ) : ℂ)) =
      (∑ l, (k l : ℂ) * (y l : ℂ)) + (k j : ℂ) * (2 * Real.pi) := by
    have hterm : ∀ l, (k l : ℂ) * ((Function.update y j (y j + 2 * Real.pi) l : ℝ) : ℂ) =
        (k l : ℂ) * (y l : ℂ) + if l = j then (k j : ℂ) * (2 * Real.pi) else 0 := by
      intro l
      by_cases hl : l = j
      · subst hl
        simp
        ring
      · simp [hl]
    simp only [hterm, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  unfold fourierChar
  rw [hsum, add_mul, Complex.exp_add]
  have h1 : (k j : ℂ) * (2 * Real.pi) * Complex.I = (k j : ℂ) * (2 * Real.pi * Complex.I) := by
    ring
  rw [h1, Complex.exp_int_mul_two_pi_mul_I, mul_one]
theorem isTwoPiPeriodic_charSeries (c : (Fin D → ℤ) → ℂ) :
    IsTwoPiPeriodicInEachCoord (charSeries c) := by
  intro j y
  unfold charSeries
  exact tsum_congr fun k => by rw [fourierChar_update_add_two_pi]
theorem fourierCoeffOnTorus_charSeries {c : (Fin D → ℤ) → ℂ} (hc : Summable fun k => ‖c k‖)
    (k : Fin D → ℤ) : fourierCoeffOnTorus (charSeries c) k = c k := by
  have hcont : ∀ j, Continuous fun y => c j * fourierChar j y * fourierCharConj k y := fun j =>
    (continuous_const.mul (continuous_fourierChar j)).mul (continuous_fourierCharConj k)
  have hint : ∀ j, Integrable (fun y => c j * fourierChar j y * fourierCharConj k y)
      (volume.restrict (torusCube D)) := fun j =>
    (hcont j).continuousOn.integrableOn_compact isCompact_torusCube
  have hnorm : ∀ j, (∫ y in torusCube D, ‖c j * fourierChar j y * fourierCharConj k y‖) =
      ‖c j‖ * volume.real (torusCube D) := by
    intro j
    simp only [norm_mul, norm_fourierChar, norm_fourierCharConj, mul_one]
    rw [setIntegral_const, smul_eq_mul, mul_comm]
  have hs : Summable fun j => ∫ y in torusCube D, ‖c j * fourierChar j y * fourierCharConj k y‖ := by
    simp only [hnorm]
    exact hc.mul_right _
  have hsum := hasSum_integral_of_summable_integral_norm hint hs
  have hterm : ∀ j, (∫ y in torusCube D, c j * fourierChar j y * fourierCharConj k y) =
      if j = k then c k * (2 * (Real.pi : ℂ)) ^ D else 0 := by
    intro j
    simp only [mul_assoc]
    rw [integral_const_mul, integral_fourierChar_mul_fourierCharConj]
    split_ifs with h
    · rw [h]
    · simp
  simp only [hterm] at hsum
  have hval := hsum.unique (hasSum_ite_eq k _)
  have hpull : ∀ y, (∑' j, c j * fourierChar j y * fourierCharConj k y) =
      charSeries c y * fourierCharConj k y := fun y => tsum_mul_right
  simp only [hpull] at hval
  have hpi : (2 * (Real.pi : ℂ)) ^ D ≠ 0 :=
    pow_ne_zero _ (mul_ne_zero two_ne_zero (by exact_mod_cast Real.pi_ne_zero))
  have hcoef : fourierCoeffOnTorus (charSeries c) k =
      ((2 * (Real.pi : ℂ)) ^ D)⁻¹ * ∫ y in torusCube D, charSeries c y * fourierCharConj k y := rfl
  rw [hcoef, hval]
  field_simp
theorem supCoord_closedBall_eq_pi (hD : 1 ≤ D) (m : ℝ) (a : Fin D → ℝ) :
    {x : Fin D → ℝ | EuclideanCoords.supCoord (x - a) ≤ m} =
      Set.pi Set.univ (fun i => Set.Icc (a i - m) (a i + m)) := by
  have : Nonempty (Fin D) := ⟨⟨0, hD⟩⟩
  ext x
  simp only [Set.mem_ofPred_eq, EuclideanCoords.supCoord, Set.mem_pi, Set.mem_univ, true_implies,
    Set.mem_Icc, Pi.sub_apply]
  rw [ciSup_le_iff (Set.finite_range _).bddAbove]
  refine forall_congr' fun i => ?_
  rw [abs_le]
  constructor
  · rintro ⟨h1, h2⟩
    constructor <;> linarith
  · rintro ⟨h1, h2⟩
    constructor <;> linarith
theorem integral_supCoord_closedBall (hD : 1 ≤ D) {m : ℝ} (hm : 0 < m) (a : Fin D → ℝ)
    (h : (Fin D → ℝ) → ℂ) :
    ∫ x in {x : Fin D → ℝ | EuclideanCoords.supCoord (x - a) ≤ m}, h x =
      (((m / Real.pi) ^ D : ℝ) : ℂ) * ∫ y in torusCube D, h (a + (m / Real.pi) • y) := by
  set s := m / Real.pi with hs
  have hspos : 0 < s := div_pos hm Real.pi_pos
  have hsm : s * Real.pi = m := by
    rw [hs]
    field_simp
  set S := {x : Fin D → ℝ | EuclideanCoords.supCoord (x - a) ≤ m} with hS
  have hSm : MeasurableSet S := by
    rw [hS, supCoord_closedBall_eq_pi hD]
    exact MeasurableSet.univ_pi fun _ => measurableSet_Icc
  have hmem : ∀ y, a + s • y ∈ S ↔ y ∈ torusCube D := by
    intro y
    rw [hS, supCoord_closedBall_eq_pi hD]
    simp only [Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Icc, torusCube, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul]
    refine forall_congr' fun i => ?_
    rw [← hsm]
    constructor
    · rintro ⟨h1, h2⟩
      constructor
      · have : s * (-Real.pi) ≤ s * y i := by linarith
        exact le_of_mul_le_mul_left this hspos
      · have : s * y i ≤ s * Real.pi := by linarith
        exact le_of_mul_le_mul_left this hspos
    · rintro ⟨h1, h2⟩
      have h3 := mul_le_mul_of_nonneg_left h1 hspos.le
      have h4 := mul_le_mul_of_nonneg_left h2 hspos.le
      constructor <;> linarith
  have hind : ∀ y, S.indicator h (a + s • y) =
      (torusCube D).indicator (fun y => h (a + s • y)) y := by
    intro y
    by_cases hy : y ∈ torusCube D
    · rw [Set.indicator_of_mem ((hmem y).mpr hy), Set.indicator_of_mem hy]
    · rw [Set.indicator_of_notMem (fun hh => hy ((hmem y).mp hh)), Set.indicator_of_notMem hy]
  have hstep : ∫ y, S.indicator h (a + s • y) =
      |(s ^ D)⁻¹| • ∫ x, S.indicator h x := by
    have h1 := Measure.integral_comp_smul (volume : Measure (Fin D → ℝ))
      (fun z => S.indicator h (a + z)) s
    rw [Module.finrank_fin_fun] at h1
    rw [h1, integral_add_left_eq_self (fun x => S.indicator h x) a]
  have hspow : 0 < s ^ D := pow_pos hspos D
  rw [← integral_indicator hSm, ← integral_indicator measurableSet_torusCube]
  simp only [← hind]
  rw [hstep, abs_of_pos (inv_pos.mpr hspow), Complex.real_smul, ← mul_assoc]
  have : ((s ^ D : ℝ) : ℂ) * (((s ^ D)⁻¹ : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, mul_inv_cancel₀ hspow.ne', Complex.ofReal_one]
  rw [this, one_mul]
def scaledFreq (m : ℝ) (k : Fin D → ℤ) : Fin D → ℝ := fun i => Real.pi / m * k i
theorem scaledFreq_dotProduct {m : ℝ} (hm : 0 < m) (k : Fin D → ℤ) (v : Fin D → ℝ) :
    scaledFreq m k ⬝ᵥ v = ∑ j, (k j : ℝ) * ((m / Real.pi)⁻¹ * v j) := by
  unfold scaledFreq dotProduct
  refine Finset.sum_congr rfl fun j _ => ?_
  have := Real.pi_pos
  field_simp
theorem cubeCoeff_scaledFreq_eq (hD : 1 ≤ D) {m : ℝ} (hm : 0 < m) (a : Fin D → ℝ)
    (W : (Fin D → ℝ) → ℂ) (k : Fin D → ℤ) :
    cubeCoeff m a W (scaledFreq m k) =
      fourierCoeffOnTorus (fun y => W (a + (m / Real.pi) • y)) k := by
  have hpi := Real.pi_pos
  have hs : m / Real.pi ≠ 0 := (div_pos hm hpi).ne'
  unfold cubeCoeff fourierCoeffOnTorus
  rw [integral_supCoord_closedBall hD hm]
  have hint : ∀ y : Fin D → ℝ,
      W (a + (m / Real.pi) • y) * Complex.exp (-(Complex.I *
        ((scaledFreq m k ⬝ᵥ (a + (m / Real.pi) • y - a) : ℝ) : ℂ))) =
      W (a + (m / Real.pi) • y) *
        Complex.exp (-((∑ j, (k j : ℂ) * (y j : ℂ)) * Complex.I)) := by
    intro y
    have hdot : scaledFreq m k ⬝ᵥ (a + (m / Real.pi) • y - a) = ∑ j, (k j : ℝ) * y j := by
      rw [scaledFreq_dotProduct hm]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_sub_cancel_left]
      rw [inv_mul_cancel_left₀ hs]
    rw [hdot, intSum_mul_eq_ofReal, mul_comm Complex.I]
  simp only [hint]
  rw [← mul_assoc]
  congr 1
  have hreal : ((2 * m) ^ D)⁻¹ * (m / Real.pi) ^ D = ((2 * Real.pi) ^ D)⁻¹ := by
    rw [← inv_pow, ← inv_pow, ← mul_pow]
    congr 1
    field_simp
  rw [← Complex.ofReal_mul, hreal]
  push_cast
  rfl
def dualLatticeEquiv {m : ℝ} (hm : 0 < m) : (Fin D → ℤ) ≃ dualLattice D m :=
  Equiv.ofBijective (fun k => ⟨scaledFreq m k, k, fun _ => rfl⟩) (by
    constructor
    · intro k k' h
      funext i
      have hi := congrFun (Subtype.ext_iff.mp h) i
      have hne : Real.pi / m ≠ 0 := (div_pos Real.pi_pos hm).ne'
      exact_mod_cast mul_left_cancel₀ hne hi
    · rintro ⟨ξ, ζ, hζ⟩
      exact ⟨ζ, Subtype.ext (funext fun i => (hζ i).symm)⟩)
theorem dualLatticeEquiv_coe {m : ℝ} (hm : 0 < m) (k : Fin D → ℤ) :
    ((dualLatticeEquiv hm k : dualLattice D m) : Fin D → ℝ) = scaledFreq m k := rfl
theorem fourierSeries_eq_of_smooth_periodic_summable_holds
    (hFejer : FejerTheoremAndTorusUniqueness) :
    fourierSeries_eq_of_smooth_periodic_summable := by
  intro D hD m hm a W hW hper hsum x
  have hpi := Real.pi_pos
  have hspos : 0 < m / Real.pi := div_pos hm hpi
  set s := m / Real.pi with hs
  have hsm : s * (2 * Real.pi) = 2 * m := by
    rw [hs]
    field_simp
  have hWc : Continuous W := ContDiff.continuous (n := (⊤ : ℕ∞)) hW
  set F : (Fin D → ℝ) → ℂ := fun y => W (a + s • y) with hFdef
  have hFc : Continuous F := hWc.comp (by fun_prop)
  have hFp : IsTwoPiPeriodicInEachCoord F := by
    intro j y
    have hupd : a + s • Function.update y j (y j + 2 * Real.pi) =
        Function.update (a + s • y) j ((a + s • y) j + 2 * m) := by
      funext i
      by_cases hi : i = j
      · subst hi
        simp only [Pi.add_apply, Pi.smul_apply, Function.update_self, smul_eq_mul]
        rw [mul_add, hsm]
        ring
      · simp [hi]
    simp only [hFdef]
    rw [hupd]
    exact hper j (a + s • y)
  have hlink : ∀ k, cubeCoeff m a W (dualLatticeEquiv hm k : Fin D → ℝ) =
      fourierCoeffOnTorus F k := fun k => cubeCoeff_scaledFreq_eq hD hm a W k
  have hsum' : Summable fun k => ‖fourierCoeffOnTorus F k‖ := by
    have h1 := (dualLatticeEquiv hm).summable_iff.mpr hsum
    refine h1.congr fun k => ?_
    simp only [Function.comp_apply, hlink]
  have hFG : F = charSeries (fourierCoeffOnTorus F) :=
    hFejer.2 D F _ hFc (continuous_charSeries hsum') hFp (isTwoPiPeriodic_charSeries _)
      fun k => (fourierCoeffOnTorus_charSeries hsum' k).symm
  have hy : a + s • (s⁻¹ • (x - a)) = x := by
    rw [smul_smul, mul_inv_cancel₀ hspos.ne', one_smul, add_sub_cancel]
  have hx : W x = charSeries (fourierCoeffOnTorus F) (s⁻¹ • (x - a)) := by
    rw [← hFG]
    simp only [hFdef]
    rw [hy]
  rw [hx, ← (dualLatticeEquiv hm).tsum_eq]
  unfold charSeries
  refine tsum_congr fun k => ?_
  rw [hlink k, dualLatticeEquiv_coe, scaledFreq_dotProduct hm]
  congr 1
  unfold fourierChar
  rw [intSum_mul_eq_ofReal, mul_comm Complex.I]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, hs]
end YangMills.Construction.FourierSeries.SmoothPeriodicSummable
