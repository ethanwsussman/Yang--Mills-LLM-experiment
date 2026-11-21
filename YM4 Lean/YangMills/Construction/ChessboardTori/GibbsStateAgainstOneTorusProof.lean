import YangMills.Construction.ChessboardTori.ChessboardEstimateAndSubadditivityProof
import YangMills.Construction.ChessboardTori.GibbsStateAgainstOneTorus
import YangMills.Construction.ChessboardTori.JensenAgainstTheChessboardProof
import YangMills.Construction.ChessboardTori.ParitiesAndCoarseGrids
import YangMills.Construction.InfiniteLattice.PeriodsFoldCompactnessAndLimitsOfToriProof
import YangMills.Construction.InfiniteLattice.TorusStatesAsPeriodicMeasures
import YangMills.Construction.Matrices.CharactersOfGProof
import YangMills.Construction.SixteenPointsOnASmallTorus.ArrayMeanIsTheMeanOfTheCopiesProof
import Mathlib
set_option autoImplicit false
open Set MeasureTheory
noncomputable section
namespace YangMills.Construction.ChessboardTori
open InfiniteLattice (AmbientSpace)
namespace GibbsBoundOnOneTorus
theorem sub_sq_le_log_one_add_of_abs_le_half {y : ℝ} (hy : |y| ≤ 1 / 2) :
    y - y ^ 2 ≤ Real.log (1 + y) := by
  have hx : |(-y)| < 1 := by rw [abs_neg]; linarith
  have h := Real.abs_log_sub_add_sum_range_le hx 4
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, abs_neg, sub_neg_eq_add] at h
  have h2 := (abs_le.mp h).1
  norm_num at h2
  have hn3 : (-y) ^ 3 = -y ^ 3 := by ring
  have ha0 : 0 ≤ |y| := abs_nonneg y
  have hy2 : y ^ 2 = |y| ^ 2 := (sq_abs y).symm
  have hy4 : y ^ 4 = |y| ^ 4 := by
    rw [show y ^ 4 = (y ^ 2) ^ 2 by ring, hy2]; ring
  have hy3 : -(|y| ^ 3) ≤ y ^ 3 := by
    have h1 : -|y| ≤ y := neg_abs_le y
    have h3 : y ^ 3 = y * |y| ^ 2 := by rw [← hy2]; ring
    rw [h3]
    nlinarith [sq_nonneg (|y|)]
  have h3 : |y| ^ 3 ≤ |y| ^ 2 * (1 / 2) := by nlinarith [sq_nonneg (|y|)]
  have h4 : |y| ^ 4 ≤ |y| ^ 2 * (1 / 4) := by nlinarith [sq_nonneg (|y|), pow_nonneg ha0 3]
  have h5 : |y| ^ 5 ≤ |y| ^ 2 * (1 / 8) := by nlinarith [sq_nonneg (|y|), pow_nonneg ha0 4]
  have hq : |y| ^ 5 / (1 - |y|) ≤ 2 * |y| ^ 5 := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith [pow_nonneg ha0 5]
  rw [hn3] at h2
  linarith [sq_nonneg (|y|)]
theorem measurable_finprod_mem_of_finite {X ι : Type*} [MeasurableSpace X] {O : Set ι}
    (hO : O.Finite) {F : ι → X → ℂ} (hF : ∀ i ∈ O, Measurable (F i)) :
    Measurable fun x => ∏ᶠ i ∈ O, F i x := by
  classical
  have h : (fun x => ∏ᶠ i ∈ O, F i x) = fun x => ∏ i ∈ hO.toFinset, F i x := by
    funext x
    exact finprod_mem_eq_finite_toFinset_prod _ hO
  rw [h]
  exact Finset.measurable_fun_prod _ fun i hi => hF i (by simpa using hi)
theorem exists_bound_finset_prod {X ι : Type*} (s : Finset ι) {F : ι → X → ℂ}
    (hF : ∀ i ∈ s, ∃ C : ℝ, ∀ x, ‖F i x‖ ≤ C) : ∃ C : ℝ, ∀ x, ‖∏ i ∈ s, F i x‖ ≤ C := by
  classical
  choose! C hC using hF
  refine ⟨∏ i ∈ s, C i, fun x => ?_⟩
  rw [norm_prod]
  exact Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun i hi => hC i hi x
theorem measurable_ofReal_re_const_mul {X : Type*} [MeasurableSpace X] {P : X → ℂ}
    (hP : Measurable P) (c : ℂ) : Measurable fun x => (((c * P x).re : ℝ) : ℂ) :=
  Complex.measurable_ofReal.comp (Complex.measurable_re.comp (hP.const_mul c))
theorem measurable_ofReal_log_one_add_re {X : Type*} [MeasurableSpace X] {P : X → ℂ}
    (hP : Measurable P) (c : ℂ) (t : ℝ) :
    Measurable fun x => ((Real.log (1 + t * (c * P x).re) : ℝ) : ℂ) :=
  Complex.measurable_ofReal.comp (Real.measurable_log.comp
    (((Complex.measurable_re.comp (hP.const_mul c)).const_mul t).const_add 1))
theorem norm_exp_neg_I_mul (x : ℝ) : ‖Complex.exp (-(Complex.I * (x : ℂ)))‖ = 1 := by apply _root_.YangMills.Construction.SpinHarmonics.SpinCharacters.norm_cexp_neg_I_mul <;> assumption
variable {a : ℝ}
theorem norm_le_supNorm {A : InfiniteLattice.GaugeField a → ℂ}
    (hA : InfiniteLattice.IsBoundedObservable A) (U : InfiniteLattice.GaugeField a) :
    ‖A U‖ ≤ InfiniteLattice.observableSupNorm A := by apply _root_.YangMills.Construction.LatticeConventions.TranslationReflectionProof.norm_le_supNorm <;> assumption
theorem integrable_of_isBoundedObservable {A : InfiniteLattice.GaugeField a → ℂ}
    (hA : InfiniteLattice.IsBoundedObservable A) (ν : Measure (InfiniteLattice.GaugeField a))
    [IsFiniteMeasure ν] : Integrable A ν := by apply _root_.YangMills.Construction.InfiniteLattice.PeriodicGibbsFoldAndCompactness.integrable_of_isBoundedObservable <;> assumption
theorem isBoundedObservable_finset_prod {ι : Type*} (s : Finset ι)
    {A : ι → InfiniteLattice.GaugeField a → ℂ}
    (hA : ∀ i ∈ s, InfiniteLattice.IsBoundedObservable (A i)) :
    InfiniteLattice.IsBoundedObservable fun U => ∏ i ∈ s, A i U := by apply _root_.YangMills.Construction.ChessboardTori.ChessboardEstimateAndSubadditivity.isBoundedObservable_finset_prod <;> assumption
theorem isRegionMeasurable_mono {S S' : Set AmbientSpace} (h : S ⊆ S')
    {A : InfiniteLattice.GaugeField a → ℂ}
    (hA : InfiniteLattice.IsRegionMeasurable S A) : InfiniteLattice.IsRegionMeasurable S' A := by apply _root_.YangMills.Construction.ChessboardTori.JensenChessboardBound.isRegionMeasurable_mono <;> assumption
section Logarithm
variable {D : ChessboardSetup} {O : Set (Set AmbientSpace)}
  {F : Set AmbientSpace → D.GaugeField → ℂ} {φ t : ℝ}
open ReflectionGrid InfiniteLattice
theorem abs_rotatedRealPart_le_supNorm (hP : IsBoundedObservable (cellFamilyProduct O F))
    (U : D.GaugeField) :
    |rotatedRealPart φ O F U| ≤ observableSupNorm (cellFamilyProduct O F) := by
  have h1 : |(Complex.exp (-(Complex.I * φ)) * cellFamilyProduct O F U).re| ≤
      ‖Complex.exp (-(Complex.I * φ)) * cellFamilyProduct O F U‖ := Complex.abs_re_le_norm _
  rw [norm_mul, norm_exp_neg_I_mul, one_mul] at h1
  exact h1.trans (norm_le_supNorm hP U)
theorem abs_mul_rotatedRealPart_le_half (hP : IsBoundedObservable (cellFamilyProduct O F))
    (ht : 0 < t) (ht' : t < (2 * observableSupNorm (cellFamilyProduct O F) + 1)⁻¹)
    (U : D.GaugeField) :
    |t * rotatedRealPart φ O F U| ≤ 1 / 2 := by
  have h1 := abs_rotatedRealPart_le_supNorm (φ := φ) hP U
  have hN0 : 0 ≤ observableSupNorm (cellFamilyProduct O F) := (abs_nonneg _).trans h1
  have hpos : 0 < 2 * observableSupNorm (cellFamilyProduct O F) + 1 := by linarith
  have h2 : t * (2 * observableSupNorm (cellFamilyProduct O F) + 1) < 1 := by
    calc t * (2 * observableSupNorm (cellFamilyProduct O F) + 1)
        < (2 * observableSupNorm (cellFamilyProduct O F) + 1)⁻¹ *
          (2 * observableSupNorm (cellFamilyProduct O F) + 1) := mul_lt_mul_of_pos_right ht' hpos
      _ = 1 := inv_mul_cancel₀ hpos.ne'
  rw [abs_mul, abs_of_pos ht]
  nlinarith
theorem logOnePlusRotated_bounds (hP : IsBoundedObservable (cellFamilyProduct O F)) (ht : 0 < t)
    (ht' : t < (2 * observableSupNorm (cellFamilyProduct O F) + 1)⁻¹) (U : D.GaugeField) :
    t * rotatedRealPart φ O F U - t ^ 2 * observableSupNorm (cellFamilyProduct O F) ^ 2 ≤
        logOnePlusRotated φ t O F U ∧
      logOnePlusRotated φ t O F U ≤ t * rotatedRealPart φ O F U := by
  have hy := abs_mul_rotatedRealPart_le_half (φ := φ) hP ht ht' U
  have h1 := abs_rotatedRealPart_le_supNorm (φ := φ) hP U
  constructor
  · have h2 := sub_sq_le_log_one_add_of_abs_le_half hy
    have h3 : (t * rotatedRealPart φ O F U) ^ 2 ≤
        t ^ 2 * observableSupNorm (cellFamilyProduct O F) ^ 2 := by
      rw [mul_pow]
      have : rotatedRealPart φ O F U ^ 2 ≤ observableSupNorm (cellFamilyProduct O F) ^ 2 := by
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) h1 2
      exact mul_le_mul_of_nonneg_left this (sq_nonneg t)
    exact (by linarith : _ ≤ _).trans h2
  · have hpos : 0 < 1 + t * rotatedRealPart φ O F U := by
      have := (abs_le.mp hy).1
      linarith
    have := Real.log_le_sub_one_of_pos hpos
    simp only [logOnePlusRotated]
    linarith
theorem half_le_one_add_mul_rotatedRealPart (hP : IsBoundedObservable (cellFamilyProduct O F))
    (ht : 0 < t) (ht' : t < (2 * observableSupNorm (cellFamilyProduct O F) + 1)⁻¹)
    (U : D.GaugeField) :
    1 / 2 ≤ 1 + t * rotatedRealPart φ O F U := by
  have := (abs_le.mp (abs_mul_rotatedRealPart_le_half (φ := φ) hP ht ht' U)).1
  linarith
theorem isBoundedObservable_rotatedRealPart (hP : IsBoundedObservable (cellFamilyProduct O F)) :
    IsBoundedObservable fun U => ((rotatedRealPart φ O F U : ℝ) : ℂ) := by
  refine ⟨measurable_ofReal_re_const_mul hP.1 _, observableSupNorm (cellFamilyProduct O F),
    fun U => ?_⟩
  rw [Complex.norm_real, Real.norm_eq_abs]
  exact abs_rotatedRealPart_le_supNorm hP U
theorem isBoundedObservable_logOnePlusRotated (hP : IsBoundedObservable (cellFamilyProduct O F))
    (ht : 0 < t) (ht' : t < (2 * observableSupNorm (cellFamilyProduct O F) + 1)⁻¹) :
    IsBoundedObservable fun U => ((logOnePlusRotated φ t O F U : ℝ) : ℂ) := by
  refine ⟨measurable_ofReal_log_one_add_re hP.1 _ _,
    t * observableSupNorm (cellFamilyProduct O F) +
      t ^ 2 * observableSupNorm (cellFamilyProduct O F) ^ 2,
    fun U => ?_⟩
  rw [Complex.norm_real, Real.norm_eq_abs]
  obtain ⟨h1, h2⟩ := logOnePlusRotated_bounds (φ := φ) hP ht ht' U
  have h3 := abs_le.mp (abs_rotatedRealPart_le_supNorm (φ := φ) hP U)
  have h4 : t * rotatedRealPart φ O F U ≤ t * observableSupNorm (cellFamilyProduct O F) :=
    mul_le_mul_of_nonneg_left h3.2 ht.le
  have h5 : -(t * observableSupNorm (cellFamilyProduct O F)) ≤ t * rotatedRealPart φ O F U := by
    have := mul_le_mul_of_nonneg_left h3.1 ht.le
    linarith
  rw [abs_le]
  constructor <;> linarith
theorem integral_logOnePlusRotated_lower_bound (hP : IsBoundedObservable (cellFamilyProduct O F))
    (ht : 0 < t) (ht' : t < (2 * observableSupNorm (cellFamilyProduct O F) + 1)⁻¹)
    (ν : Measure D.GaugeField) [IsProbabilityMeasure ν]
    (hν : Complex.exp (-(Complex.I * φ)) * ∫ U, cellFamilyProduct O F U ∂ν =
      ((‖∫ U, cellFamilyProduct O F U ∂ν‖ : ℝ) : ℂ)) :
    t * ‖∫ U, cellFamilyProduct O F U ∂ν‖ -
        t ^ 2 * observableSupNorm (cellFamilyProduct O F) ^ 2 ≤
      ∫ U, logOnePlusRotated φ t O F U ∂ν := by
  have hPi : Integrable (cellFamilyProduct O F) ν := integrable_of_isBoundedObservable hP ν
  have hgi : Integrable (rotatedRealPart φ O F) ν :=
    (integrable_of_isBoundedObservable (isBoundedObservable_rotatedRealPart (φ := φ) hP) ν).re
  have hhi : Integrable (logOnePlusRotated φ t O F) ν :=
    (integrable_of_isBoundedObservable
      (isBoundedObservable_logOnePlusRotated (φ := φ) hP ht ht') ν).re
  have hg : ∫ U, rotatedRealPart φ O F U ∂ν = ‖∫ U, cellFamilyProduct O F U ∂ν‖ := by
    have h1 : ∫ U, rotatedRealPart φ O F U ∂ν =
        (∫ U, Complex.exp (-(Complex.I * φ)) * cellFamilyProduct O F U ∂ν).re :=
      Complex.reCLM.integral_comp_comm (hPi.const_mul _)
    rw [h1, integral_const_mul, hν, Complex.ofReal_re]
  calc t * ‖∫ U, cellFamilyProduct O F U ∂ν‖ -
        t ^ 2 * observableSupNorm (cellFamilyProduct O F) ^ 2
      = ∫ U, (t * rotatedRealPart φ O F U -
          t ^ 2 * observableSupNorm (cellFamilyProduct O F) ^ 2) ∂ν := by
        rw [integral_sub (hgi.const_mul t) (integrable_const _), integral_const_mul, hg]
        simp
    _ ≤ ∫ U, logOnePlusRotated φ t O F U ∂ν :=
        integral_mono ((hgi.const_mul t).sub (integrable_const _)) hhi fun U =>
          (logOnePlusRotated_bounds hP ht ht' U).1
end Logarithm
theorem intUnits_eq_or_eq_neg (σ s : ℤˣ) : σ = s ∨ σ = -s := by
  revert σ s
  decide
theorem signedConjFun_neg {X : Type*} (s : ℤˣ) (A : X → ℂ) :
    Conventions.signedConjFun (-s) A =
      fun U => starRingEnd ℂ (Conventions.signedConjFun s A U) := by
  funext U
  rcases Int.units_eq_one_or s with rfl | rfl <;>
    simp [Conventions.signedConjFun, Conventions.signedConj]
theorem signedConj_ofReal (σ : ℤˣ) (x : ℝ) : Conventions.signedConj σ (x : ℂ) = x := by apply _root_.YangMills.SharedProofs.p21399 <;> assumption
theorem sum_intUnits {M : Type*} [AddCommMonoid M] (f : ℤˣ → M) : ∑ s, f s = f 1 + f (-1) := by
  rw [show (Finset.univ : Finset ℤˣ) = {1, -1} by decide]
  simp
theorem prod_one_add_mul_sum_expansion {ι : Type*} [DecidableEq ι] (J : Finset ι)
    (a : ι → ℤˣ → ℂ) (w : ℂ) :
    ∏ c ∈ J, (1 + w * ∑ s, a c s) =
      ∑ T ∈ J.powerset, w ^ T.card * ∑ ς : T → ℤˣ, ∏ c : T, a c.1 (ς c) := by
  rw [Finset.prod_one_add]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [Finset.prod_mul_distrib, Finset.prod_const, ← Finset.prod_coe_sort T fun c => ∑ s, a c s]
  congr 1
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
theorem measurable_finset_sum_complex {X ι : Type*} [MeasurableSpace X] (s : Finset ι)
    {F : ι → X → ℂ} (hF : ∀ i ∈ s, Measurable (F i)) : Measurable fun x => ∑ i ∈ s, F i x :=
  Finset.measurable_fun_sum _ hF
theorem measurable_ofReal_one_add_re {X : Type*} [MeasurableSpace X] {P : X → ℂ}
    (hP : Measurable P) (c : ℂ) (t : ℝ) : Measurable fun x => ((1 + t * (c * P x).re : ℝ) : ℂ) :=
  Complex.measurable_ofReal.comp
    (((Complex.measurable_re.comp (hP.const_mul c)).const_mul t).const_add 1)
theorem norm_exp_neg_I_mul_sign (s : ℤˣ) (φ : ℝ) :
    ‖Complex.exp (-(Complex.I * (((s : ℤˣ) : ℤ) : ℂ) * φ))‖ = 1 := by
  have h := norm_exp_neg_I_mul ((((s : ℤˣ) : ℤ) : ℝ) * φ)
  push_cast at h
  rwa [← mul_assoc] at h
section Copies
variable {D : ChessboardSetup} {O : Set (Set AmbientSpace)}
  {F : Set AmbientSpace → D.GaugeField → ℂ} {φ t : ℝ}
open ReflectionGrid InfiniteLattice
theorem conj_mem_cellObservables {S : Set AmbientSpace} {A : D.GaugeField → ℂ}
    (hA : A ∈ cellObservables (D := D) S) :
    (fun U => starRingEnd ℂ (A U)) ∈ cellObservables (D := D) S := by apply _root_.YangMills.Construction.ChessboardTori.ChessboardEstimateAndSubadditivity.conj_mem_cellObservables <;> assumption
theorem one_add_rotated_eq_sum_signs (hO : O.Finite) (U : D.GaugeField) :
    (((1 + t * rotatedRealPart φ O F U : ℝ)) : ℂ) =
      1 + (t : ℂ) / 2 * ∑ s : ℤˣ, Complex.exp (-(Complex.I * (((s : ℤˣ) : ℤ) : ℂ) * φ)) *
        ∏ᶠ S ∈ O, Conventions.signedConj s (F S U) := by
  have hconj : ∏ᶠ S ∈ O, starRingEnd ℂ (F S U) = starRingEnd ℂ (cellFamilyProduct O F U) := by
    simp only [cellFamilyProduct]
    rw [finprod_mem_eq_finite_toFinset_prod _ hO, finprod_mem_eq_finite_toFinset_prod _ hO,
      map_prod]
  have hphase : Complex.exp (-(Complex.I * ((((-1 : ℤˣ) : ℤˣ) : ℤ) : ℂ) * φ)) =
      starRingEnd ℂ (Complex.exp (-(Complex.I * φ))) := by
    rw [← Complex.exp_conj]
    congr 1
    simp
  have h1 : ∏ᶠ S ∈ O, Conventions.signedConj (1 : ℤˣ) (F S U) = cellFamilyProduct O F U := by
    simp [Conventions.signedConj, cellFamilyProduct]
  have h2 : ∏ᶠ S ∈ O, Conventions.signedConj (-1 : ℤˣ) (F S U) =
      starRingEnd ℂ (cellFamilyProduct O F U) := by
    rw [← hconj]
    simp [Conventions.signedConj]
  rw [sum_intUnits, h1, h2, hphase]
  have h3 : Complex.exp (-(Complex.I * (((1 : ℤˣ) : ℤ) : ℂ) * φ)) =
      Complex.exp (-(Complex.I * φ)) := by
    simp
  rw [h3, ← map_mul, Complex.add_conj]
  simp only [rotatedRealPart]
  push_cast
  ring
theorem transport_ofReal (g' : ReflectionGrid D) (r : g'.reflectionGroup) (f : D.GaugeField → ℝ)
    (U : D.GaugeField) :
    g'.transport r (fun U => (f U : ℂ)) U =
      (f ((g'.toLatticeSym r).pullbackField U) : ℂ) :=
  signedConj_ofReal _ _
theorem transportTo_onePlusRotated (g' : ReflectionGrid D) (S : Set AmbientSpace)
    (U : D.GaugeField) :
    g'.transportTo g'.baseCell S (onePlusRotated φ t O F) U =
      ((1 + t * rotatedRealPart φ O F ((g'.baseCellMover S).pullbackField U) : ℝ) : ℂ) :=
  transport_ofReal g' _ (fun U => 1 + t * rotatedRealPart φ O F U) U
def expansionTerm (g' : ReflectionGrid D) (O : Set (Set AmbientSpace))
    (F : Set AmbientSpace → D.GaugeField → ℂ)
    (T : Finset (Set AmbientSpace)) (ς : T → ℤˣ) : D.GaugeField → ℂ :=
  fun U => ∏ c : T, ∏ᶠ S ∈ O, Conventions.signedConjFun (ς c)
    ((g'.baseCellMover c.1).actOn (F S)) U
def expansionPhase (φ : ℝ) (T : Finset (Set AmbientSpace)) (ς : T → ℤˣ) : ℂ :=
  ∏ c : T, Complex.exp (-(Complex.I * (((ς c : ℤˣ) : ℤ) : ℂ) * φ))
open Classical in
theorem transportedProduct_expansion (g' : ReflectionGrid D) (hO : O.Finite)
    (J : Finset (Set AmbientSpace)) (U : D.GaugeField) :
    g'.transportedProduct J (onePlusRotated φ t O F) U =
      ∑ T ∈ J.powerset, ((t : ℂ) / 2) ^ T.card * ∑ ς : T → ℤˣ,
        expansionPhase φ T ς * expansionTerm g' O F T ς U := by
  simp only [transportedProduct]
  rw [Finset.prod_congr rfl fun c _ =>
    (transportTo_onePlusRotated g' c U).trans (one_add_rotated_eq_sum_signs hO _)]
  rw [prod_one_add_mul_sum_expansion J
    (fun c s => Complex.exp (-(Complex.I * (((s : ℤˣ) : ℤ) : ℂ) * φ)) *
      ∏ᶠ S ∈ O, Conventions.signedConj s (F S ((g'.baseCellMover c).pullbackField U)))]
  refine Finset.sum_congr rfl fun T _ => ?_
  congr 1
  refine Finset.sum_congr rfl fun ς _ => ?_
  rw [Finset.prod_mul_distrib]
  rfl
end Copies
section Setting
variable {D : ChessboardSetup}
open ReflectionGrid InfiniteLattice
structure ChessboardHypotheses (g g' : ReflectionGrid D) (O : Set (Set AmbientSpace))
    (F : Set AmbientSpace → D.GaugeField → ℂ) : Prop where
  fine : g.IsCoarse
  coarse : g'.IsCoarse
  coarse_side : 2 * g'.cellSide ≤ PeriodicLattice.torusSide D.L D.m
  fine_side : 2 * g.cellSide ≤ PeriodicLattice.torusSide D.L D.m
  finite : g.IsFiniteCellFamily O
  mem : ∀ S ∈ O, F S ∈ cellObservables (D := D) S
  subset_base : ∀ S ∈ O, S ⊆ g'.baseCell
  cellObs : D.CellObservablesEqInteriorMeasurable
  lifts : D.LiftedObservableProperties
  isProb : IsProbabilityMeasure D.liftedMeasure
  cellObs_mono : ∀ S ∈ g.cellSet, ∀ S' ∈ g'.cellSet, S ⊆ S' →
    cellObservables (D := D) S ⊆ cellObservables (D := D) S'
  blocks_subset : g'.blocks ⊆ g.blocks
  transport_cells : ∀ S ∈ g.cellSet, ∀ S' ∈ g'.cellSet, S ⊆ S' →
    ∀ F ∈ cellObservables (D := D) S, ∀ r : g'.reflectionGroup,
      r.1 '' S ∈ g.cellSet ∧ r.1 '' S' ∈ g'.cellSet ∧ r.1 '' S ⊆ r.1 '' S' ∧
        g'.transportTo S' (r.1 '' S') F = g.transportTo S (r.1 '' S) F
  images_distinct : ∀ S' ∈ g'.cellSet, ∀ (r₁ r₂ : g'.reflectionGroup) (S₁ S₂ : Set AmbientSpace),
    S₁ ∈ g.cellSet → S₁ ⊆ S' → S₂ ∈ g.cellSet → S₂ ⊆ S' → (r₁, S₁) ≠ (r₂, S₂) →
      r₁.1 '' S₁ ≠ r₂.1 '' S₂
  fine_transport : g.TransportLaws
  coarse_transport : g'.TransportLaws
  unique_mover : g'.UniqueElementMapsCell
  norms : GridChessboardNorm.Statement
  inequality : ChessboardInequality.Statement
variable {g g' : ReflectionGrid D} {O : Set (Set AmbientSpace)}
  {F : Set AmbientSpace → D.GaugeField → ℂ} {φ t : ℝ}
theorem baseCell_mem_cellSet (g' : ReflectionGrid D) : g'.baseCell ∈ g'.cellSet := ⟨0, rfl⟩
theorem ChessboardHypotheses.isBoundedObservable_of_mem (h : ChessboardHypotheses g g' O F)
    {S : Set AmbientSpace} (hS : S ∈ g.cellSet)
    {A : D.GaugeField → ℂ} (hA : A ∈ cellObservables (D := D) S) : IsBoundedObservable A := by
  rw [h.cellObs g h.fine S hS] at hA
  exact hA.1
theorem ChessboardHypotheses.coarse_of_mem (h : ChessboardHypotheses g g' O F)
    {S : Set AmbientSpace} (hS : S ∈ g'.cellSet)
    {A : D.GaugeField → ℂ} (hA : A ∈ cellObservables (D := D) S) :
    IsBoundedObservable A ∧ IsRegionMeasurable (interior S) A := by
  rw [h.cellObs g' h.coarse S hS] at hA
  exact hA
theorem ChessboardHypotheses.cellProduct_props (h : ChessboardHypotheses g g' O F) :
    IsBoundedObservable (cellFamilyProduct O F) ∧
      IsRegionMeasurable (interior g'.baseCell) (cellFamilyProduct O F) := by
  have hF : ∀ S ∈ O, IsBoundedObservable (F S) ∧
      IsRegionMeasurable (interior g'.baseCell) (F S) :=
    fun S hS => h.coarse_of_mem (baseCell_mem_cellSet g')
      (h.cellObs_mono S (h.finite.2 hS) _ (baseCell_mem_cellSet g') (h.subset_base S hS)
        (h.mem S hS))
  refine ⟨⟨measurable_finprod_mem_of_finite h.finite.1 fun S hS => (hF S hS).1.1, ?_⟩,
    @measurable_finprod_mem_of_finite _ _ (regionSigma (interior g'.baseCell)) _ h.finite.1 _
      fun S hS => (hF S hS).2⟩
  obtain ⟨C, hC⟩ := exists_bound_finset_prod (F := F) h.finite.1.toFinset
    fun S hS => (hF S (by simpa using hS)).1.2
  exact ⟨C, fun U => by
    simp only [cellFamilyProduct]
    rw [finprod_mem_eq_finite_toFinset_prod _ h.finite.1]
    exact hC U⟩
theorem ChessboardHypotheses.onePlusRotated_mem (h : ChessboardHypotheses g g' O F) (ht : 0 < t)
    (ht' : t < (2 * observableSupNorm (cellFamilyProduct O F) + 1)⁻¹) :
    onePlusRotated φ t O F ∈ cellObservables (D := D) g'.baseCell := by
  rw [h.cellObs g' h.coarse _ (baseCell_mem_cellSet g')]
  refine ⟨⟨measurable_ofReal_one_add_re h.cellProduct_props.1.1 _ _, 3 / 2, fun U => ?_⟩,
    @measurable_ofReal_one_add_re _ (regionSigma (interior g'.baseCell)) _
      h.cellProduct_props.2 _ _⟩
  have hb := abs_le.mp
    (abs_mul_rotatedRealPart_le_half (φ := φ) h.cellProduct_props.1 ht ht' U)
  simp only [onePlusRotated]
  rw [Complex.norm_real, Real.norm_eq_abs, abs_le]
  constructor <;> linarith [hb.1, hb.2]
theorem ChessboardHypotheses.logOnePlusRotated_mem (h : ChessboardHypotheses g g' O F)
    (ht : 0 < t) (ht' : t < (2 * observableSupNorm (cellFamilyProduct O F) + 1)⁻¹) :
    (fun U => ((logOnePlusRotated φ t O F U : ℝ) : ℂ)) ∈
      cellObservables (D := D) g'.baseCell := by
  rw [h.cellObs g' h.coarse _ (baseCell_mem_cellSet g')]
  exact ⟨isBoundedObservable_logOnePlusRotated h.cellProduct_props.1 ht ht',
    @measurable_ofReal_log_one_add_re _ (regionSigma (interior g'.baseCell)) _
      h.cellProduct_props.2 _ _⟩
theorem ChessboardHypotheses.rotatedRealPart_mem (h : ChessboardHypotheses g g' O F) :
    (fun U => ((rotatedRealPart φ O F U : ℝ) : ℂ)) ∈ cellObservables (D := D) g'.baseCell := by
  rw [h.cellObs g' h.coarse _ (baseCell_mem_cellSet g')]
  exact ⟨isBoundedObservable_rotatedRealPart h.cellProduct_props.1,
    @measurable_ofReal_re_const_mul _ (regionSigma (interior g'.baseCell)) _
      h.cellProduct_props.2 _⟩
theorem ChessboardHypotheses.mover_image_baseCell (h : ChessboardHypotheses g g' O F)
    {c : Set AmbientSpace} (hc : c ∈ g'.cellSet) :
    (g'.mover g'.baseCell c).1 '' g'.baseCell = c := by
  obtain ⟨r, hr, -⟩ := h.unique_mover _ (baseCell_mem_cellSet g') _ hc
  exact Classical.epsilon_spec (p := fun r : g'.reflectionGroup => r.1 '' g'.baseCell = c) ⟨r, hr⟩
theorem ChessboardHypotheses.signed_transport (h : ChessboardHypotheses g g' O F)
    {c : Set AmbientSpace} (hc : c ∈ g'.cellSet)
    {S : Set AmbientSpace} (hSO : S ∈ O) (σ : ℤˣ) :
    (g'.mover g'.baseCell c).1 '' S ∈ g.cellSet ∧ (g'.mover g'.baseCell c).1 '' S ⊆ c ∧
      Conventions.signedConjFun σ ((g'.baseCellMover c).actOn (F S)) ∈
        cellObservables (D := D) ((g'.mover g'.baseCell c).1 '' S) ∧
      g.chessboardNorm ((g'.mover g'.baseCell c).1 '' S)
          (Conventions.signedConjFun σ ((g'.baseCellMover c).actOn (F S))) =
        g.chessboardNorm S (F S) := by
  have hr := h.mover_image_baseCell hc
  have hSc : S ∈ g.cellSet := h.finite.2 hSO
  have hFS := h.mem S hSO
  obtain ⟨h1, -, h3, h4⟩ := h.transport_cells S hSc _ (baseCell_mem_cellSet g')
    (h.subset_base S hSO) (F S) hFS (g'.mover g'.baseCell c)
  rw [hr] at h3 h4
  have hcp : g'.transportTo g'.baseCell c (F S) =
      Conventions.signedConjFun (orientationSign (g'.mover g'.baseCell c).1)
        ((g'.baseCellMover c).actOn (F S)) := rfl
  have hmem := (h.fine_transport.1 S hSc _ h1 _ h1 (F S) hFS (F S) hFS).1
  obtain ⟨-, -, hvc, -⟩ := h.norms D g h.fine h.fine_side (g.block 0) ⟨0, rfl⟩
  have hcopyval := ((hvc S hSc).1 (F S) hFS).2.2.1 _ h1
  have hconjval := ((hvc _ h1).1 _ hmem).2.2.2.1
  refine ⟨h1, h3, ?_⟩
  rcases intUnits_eq_or_eq_neg σ (orientationSign (g'.mover g'.baseCell c).1) with rfl | rfl
  · rw [← hcp, h4]
    exact ⟨hmem, hcopyval⟩
  · rw [signedConjFun_neg, ← hcp, h4]
    exact ⟨conj_mem_cellObservables hmem, hconjval.trans hcopyval⟩
theorem ChessboardHypotheses.expansionTerm_bound (h : ChessboardHypotheses g g' O F)
    {T : Finset (Set AmbientSpace)}
    (hT : (T : Set (Set AmbientSpace)) ⊆ g'.cellsWithin g'.fundamentalBlock) (ς : T → ℤˣ) :
    IsBoundedObservable (expansionTerm g' O F T ς) ∧
      ‖D.periodicExpectation (D.liftedObservable (expansionTerm g' O F T ς))‖ ≤
        g.chessboardNormProduct O F ^ T.card := by
  classical
  let R : T → g'.reflectionGroup := fun c => g'.mover g'.baseCell c.1
  let pos : T × Set AmbientSpace → Set AmbientSpace := fun p => (R p.1).1 '' p.2
  let G : T × Set AmbientSpace → D.GaugeField → ℂ := fun p =>
    Conventions.signedConjFun (ς p.1) ((g'.baseCellMover p.1.1).actOn (F p.2))
  let Q : Finset (T × Set AmbientSpace) := Finset.univ ×ˢ h.finite.1.toFinset
  have hcell : ∀ c : T, c.1 ∈ g'.cellSet := fun c => (hT c.2).1
  have hQ : ∀ p ∈ Q, p.2 ∈ O := fun p hp => by
    simpa using (Finset.mem_product.mp hp).2
  have hfacts : ∀ p ∈ Q, pos p ∈ g.cellSet ∧ pos p ⊆ p.1.1 ∧
      G p ∈ cellObservables (D := D) (pos p) ∧
      g.chessboardNorm (pos p) (G p) = g.chessboardNorm p.2 (F p.2) := fun p hp =>
    h.signed_transport (hcell p.1) (hQ p hp) (ς p.1)
  have hinj : InjOn pos (Q : Set (T × Set AmbientSpace)) := by
    rintro ⟨c, S⟩ hp ⟨c', S'⟩ hp' heq
    by_contra hne
    have hS := hQ _ (Finset.mem_coe.mp hp)
    have hS' := hQ _ (Finset.mem_coe.mp hp')
    refine h.images_distinct _ (baseCell_mem_cellSet g') (R c) (R c') S S' (h.finite.2 hS)
      (h.subset_base S hS) (h.finite.2 hS') (h.subset_base S' hS') (fun he => hne ?_) heq
    obtain ⟨h1, h2⟩ := Prod.mk.inj he
    have h3 : c = c' := Subtype.ext (by
      rw [← h.mover_image_baseCell (hcell c), ← h.mover_image_baseCell (hcell c')]
      exact congrArg (fun r : g'.reflectionGroup => r.1 '' g'.baseCell) h1)
    rw [h3, h2]
  let Ff : Set AmbientSpace → D.GaugeField → ℂ := fun X =>
    if hX : ∃ p ∈ Q, pos p = X then G hX.choose else 1
  have hFf : ∀ p ∈ Q, Ff (pos p) = G p := by
    intro p hp
    have hX : ∃ q ∈ Q, pos q = pos p := ⟨p, hp, rfl⟩
    have h1 := hinj (Finset.mem_coe.mpr hX.choose_spec.1) (Finset.mem_coe.mpr hp)
      hX.choose_spec.2
    simp only [Ff]
    rw [dif_pos hX, h1]
  have hC : pos '' (Q : Set (T × Set AmbientSpace)) ⊆ g.cellsWithin g'.fundamentalBlock := by
    rintro _ ⟨p, hp, rfl⟩
    obtain ⟨h1, h2, -, -⟩ := hfacts p hp
    exact ⟨h1, h2.trans (hT p.1.2).2⟩
  obtain ⟨-, hvb, -, -⟩ := h.norms D g h.fine h.fine_side _ (h.blocks_subset ⟨0, rfl⟩)
  have hbound := hvb _ hC Ff (by
    rintro _ ⟨p, hp, rfl⟩
    rw [hFf p hp]
    exact (hfacts p hp).2.2.1)
  have hprod : ∀ U, ∏ᶠ X ∈ pos '' (Q : Set (T × Set AmbientSpace)), Ff X U =
      ∏ p ∈ Q, G p U := by
    intro U
    rw [finprod_mem_image hinj,
      finprod_mem_congr rfl fun p hp => by rw [hFf p (Finset.mem_coe.mp hp)],
      finprod_mem_coe_finset]
  have hterm : ∀ U, expansionTerm g' O F T ς U = ∏ p ∈ Q, G p U := by
    intro U
    simp only [expansionTerm, Q]
    rw [Finset.prod_product]
    exact Finset.prod_congr rfl fun c _ => finprod_mem_eq_finite_toFinset_prod _ h.finite.1
  refine ⟨?_, ?_⟩
  · rw [show expansionTerm g' O F T ς = fun U => ∏ p ∈ Q, G p U from funext hterm]
    exact isBoundedObservable_finset_prod _ fun p hp =>
      h.isBoundedObservable_of_mem (hfacts p hp).1 (hfacts p hp).2.2.1
  · have e : D.liftedObservable (expansionTerm g' O F T ς) =
        D.liftedObservable fun U => ∏ᶠ X ∈ pos '' (Q : Set (T × Set AmbientSpace)), Ff X U := by
      congr 1
      funext U
      rw [hterm, hprod]
    rw [e]
    refine le_of_le_of_eq hbound ?_
    rw [finprod_mem_image hinj,
      finprod_mem_congr rfl fun p hp => by
        rw [hFf p (Finset.mem_coe.mp hp), (hfacts p (Finset.mem_coe.mp hp)).2.2.2],
      finprod_mem_coe_finset, Finset.prod_product]
    simp only [chessboardNormProduct]
    rw [finprod_mem_eq_finite_toFinset_prod _ h.finite.1]
    simp
theorem ChessboardHypotheses.chessboardNormProduct_nonneg (h : ChessboardHypotheses g g' O F) :
    0 ≤ g.chessboardNormProduct O F := by
  simp only [chessboardNormProduct]
  rw [finprod_mem_eq_finite_toFinset_prod _ h.finite.1]
  refine Finset.prod_nonneg fun S hS => ?_
  have hSO : S ∈ O := by simpa using hS
  exact Real.rpow_nonneg
    ((h.inequality D g h.fine_side).1 (g.block 0) ⟨0, rfl⟩ S (h.finite.2 hSO) (F S)
      (h.mem S hSO)).2.1 _
end Setting
section Conclusions
variable {D : ChessboardSetup}
open ReflectionGrid InfiniteLattice
variable {g g' : ReflectionGrid D} {O : Set (Set AmbientSpace)}
  {F : Set AmbientSpace → D.GaugeField → ℂ} {φ t : ℝ}
def realTransportedProduct (g' : ReflectionGrid D) (φ t : ℝ) (O : Set (Set AmbientSpace))
    (F : Set AmbientSpace → D.GaugeField → ℂ) (J : Finset (Set AmbientSpace)) :
    D.GaugeField → ℝ :=
  fun U => ∏ c ∈ J, (1 + t * rotatedRealPart φ O F ((g'.baseCellMover c).pullbackField U))
theorem transportedProduct_eq_ofReal (g' : ReflectionGrid D) (J : Finset (Set AmbientSpace))
    (U : D.GaugeField) :
    g'.transportedProduct J (onePlusRotated φ t O F) U =
      (realTransportedProduct g' φ t O F J U : ℂ) := by
  simp only [transportedProduct, realTransportedProduct]
  rw [Complex.ofReal_prod]
  exact Finset.prod_congr rfl fun c _ => transportTo_onePlusRotated g' c U
theorem norm_expansionPhase (φ : ℝ) (T : Finset (Set AmbientSpace)) (ς : T → ℤˣ) :
    ‖expansionPhase φ T ς‖ = 1 := by
  simp only [expansionPhase]
  rw [norm_prod]
  exact Finset.prod_eq_one fun c _ => norm_exp_neg_I_mul_sign _ _
theorem ChessboardHypotheses.transportedProduct_isBoundedObservable
    (h : ChessboardHypotheses g g' O F) (ht : 0 < t)
    (ht' : t < (2 * observableSupNorm (cellFamilyProduct O F) + 1)⁻¹)
    {J : Finset (Set AmbientSpace)}
    (hJ : (J : Set (Set AmbientSpace)) ⊆ g'.cellsWithin g'.fundamentalBlock) :
    IsBoundedObservable (g'.transportedProduct J (onePlusRotated φ t O F)) := by
  refine isBoundedObservable_finset_prod J fun c hc => ?_
  have hc' : c ∈ g'.cellSet := (hJ hc).1
  have hf := h.onePlusRotated_mem (φ := φ) ht ht'
  exact (h.coarse_of_mem hc'
    (h.coarse_transport.1 _ (baseCell_mem_cellSet g') c hc' c hc' _ hf _ hf).1).1
theorem ChessboardHypotheses.expectation_transportedProduct_bound
    (h : ChessboardHypotheses g g' O F) (ht : 0 < t)
    (ht' : t < (2 * observableSupNorm (cellFamilyProduct O F) + 1)⁻¹)
    {J : Finset (Set AmbientSpace)}
    (hJ : (J : Set (Set AmbientSpace)) ⊆ g'.cellsWithin g'.fundamentalBlock) :
    (D.periodicExpectation (D.liftedObservable
        (g'.transportedProduct J (onePlusRotated φ t O F)))).im = 0 ∧
      0 < (D.periodicExpectation (D.liftedObservable
        (g'.transportedProduct J (onePlusRotated φ t O F)))).re ∧
      (D.periodicExpectation (D.liftedObservable
        (g'.transportedProduct J (onePlusRotated φ t O F)))).re ≤
        (1 + t * g.chessboardNormProduct O F) ^ J.card := by
  classical
  have hP := h.cellProduct_props.1
  have hPr := h.transportedProduct_isBoundedObservable (φ := φ) ht ht' hJ
  have := h.isProb
  have hE : D.periodicExpectation (D.liftedObservable
      (g'.transportedProduct J (onePlusRotated φ t O F))) =
      ∫ U, g'.transportedProduct J (onePlusRotated φ t O F) U ∂D.liftedMeasure :=
    (h.lifts _ _ hPr hPr).2.1
  have hprI : Integrable (realTransportedProduct g' φ t O F J) D.liftedMeasure := by
    refine (integrable_of_isBoundedObservable hPr D.liftedMeasure).re.congr
      (Filter.Eventually.of_forall fun U => ?_)
    show RCLike.re (g'.transportedProduct J (onePlusRotated φ t O F) U) = _
    rw [transportedProduct_eq_ofReal]
    simp
  have hlow : ∀ U, (1 / 2 : ℝ) ^ J.card ≤ realTransportedProduct g' φ t O F J U := fun U => by
    calc (1 / 2 : ℝ) ^ J.card = ∏ _c ∈ J, (1 / 2 : ℝ) := by rw [Finset.prod_const]
      _ ≤ realTransportedProduct g' φ t O F J U :=
        Finset.prod_le_prod (fun _ _ => by norm_num) fun c _ =>
          half_le_one_add_mul_rotatedRealPart hP ht ht' _
  have hEr : D.periodicExpectation (D.liftedObservable
      (g'.transportedProduct J (onePlusRotated φ t O F))) =
      ((∫ U, realTransportedProduct g' φ t O F J U ∂D.liftedMeasure : ℝ) : ℂ) := by
    rw [hE, ← integral_complex_ofReal]
    exact integral_congr_ae (Filter.Eventually.of_forall (transportedProduct_eq_ofReal g' J))
  have hlower : (1 / 2 : ℝ) ^ J.card ≤
      ∫ U, realTransportedProduct g' φ t O F J U ∂D.liftedMeasure := by
    have h1 := integral_mono (integrable_const ((1 / 2 : ℝ) ^ J.card)) hprI hlow
    simpa using h1
  refine ⟨by rw [hEr]; exact Complex.ofReal_im _, ?_, ?_⟩
  · rw [hEr, Complex.ofReal_re]
    exact lt_of_lt_of_le (by positivity) hlower
  have hsub : ∀ T ∈ J.powerset,
      (T : Set (Set AmbientSpace)) ⊆ g'.cellsWithin g'.fundamentalBlock := fun T hT =>
    (Finset.coe_subset.mpr (Finset.mem_powerset.mp hT)).trans hJ
  have hobs : ∀ T ∈ J.powerset, ∀ ς : T → ℤˣ,
      Integrable (expansionTerm g' O F T ς) D.liftedMeasure := fun T hT ς =>
    integrable_of_isBoundedObservable (h.expansionTerm_bound (hsub T hT) ς).1 _
  have hnorm : ∀ T ∈ J.powerset, ∀ ς : T → ℤˣ,
      ‖∫ U, expansionTerm g' O F T ς U ∂D.liftedMeasure‖ ≤
        g.chessboardNormProduct O F ^ T.card := by
    intro T hT ς
    obtain ⟨h1, h2⟩ := h.expansionTerm_bound (hsub T hT) ς
    rw [(h.lifts _ _ h1 h1).2.1] at h2
    exact h2
  have hint : ∫ U, g'.transportedProduct J (onePlusRotated φ t O F) U ∂D.liftedMeasure =
      ∑ T ∈ J.powerset, ((t : ℂ) / 2) ^ T.card * ∑ ς : T → ℤˣ,
        expansionPhase φ T ς * ∫ U, expansionTerm g' O F T ς U ∂D.liftedMeasure := by
    rw [integral_congr_ae
        (Filter.Eventually.of_forall (transportedProduct_expansion g' h.finite.1 J)),
      integral_finsetSum _ fun T hT => Integrable.const_mul
        (integrable_finsetSum _ fun ς _ => (hobs T hT ς).const_mul _) _]
    refine Finset.sum_congr rfl fun T hT => ?_
    rw [integral_const_mul, integral_finsetSum _ fun ς _ => (hobs T hT ς).const_mul _]
    congr 1
    exact Finset.sum_congr rfl fun ς _ => integral_const_mul _ _
  have hw : ‖(t : ℂ) / 2‖ = t / 2 := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht]
    simp
  have hterm : ∀ T ∈ J.powerset,
      ‖((t : ℂ) / 2) ^ T.card * ∑ ς : T → ℤˣ,
        expansionPhase φ T ς * ∫ U, expansionTerm g' O F T ς U ∂D.liftedMeasure‖ ≤
      (t * g.chessboardNormProduct O F) ^ T.card := by
    intro T hT
    have h1 : ‖∑ ς : T → ℤˣ,
        expansionPhase φ T ς * ∫ U, expansionTerm g' O F T ς U ∂D.liftedMeasure‖ ≤
        2 ^ T.card * g.chessboardNormProduct O F ^ T.card := by
      calc ‖∑ ς : T → ℤˣ,
            expansionPhase φ T ς * ∫ U, expansionTerm g' O F T ς U ∂D.liftedMeasure‖
          ≤ ∑ ς : T → ℤˣ,
              ‖expansionPhase φ T ς * ∫ U, expansionTerm g' O F T ς U ∂D.liftedMeasure‖ :=
            norm_sum_le _ _
        _ ≤ ∑ _ς : T → ℤˣ, g.chessboardNormProduct O F ^ T.card :=
            Finset.sum_le_sum fun ς _ => by
              rw [norm_mul, norm_expansionPhase, one_mul]
              exact hnorm T hT ς
        _ = 2 ^ T.card * g.chessboardNormProduct O F ^ T.card := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, nsmul_eq_mul]
            simp
    rw [norm_mul, norm_pow, hw]
    calc (t / 2) ^ T.card * _
        ≤ (t / 2) ^ T.card * (2 ^ T.card * g.chessboardNormProduct O F ^ T.card) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = (t * g.chessboardNormProduct O F) ^ T.card := by
          rw [← mul_assoc, ← mul_pow, ← mul_pow]
          congr 2
          ring
  calc (D.periodicExpectation (D.liftedObservable
        (g'.transportedProduct J (onePlusRotated φ t O F)))).re
      ≤ ‖D.periodicExpectation (D.liftedObservable
        (g'.transportedProduct J (onePlusRotated φ t O F)))‖ := Complex.re_le_norm _
    _ ≤ ∑ T ∈ J.powerset, (t * g.chessboardNormProduct O F) ^ T.card := by
        rw [hE, hint]
        exact norm_sum_le_of_le _ hterm
    _ = (1 + t * g.chessboardNormProduct O F) ^ J.card := by
        have h1 := Finset.prod_one_add (s := J) (f := fun _ => t * g.chessboardNormProduct O F)
        simpa using h1.symm
theorem ChessboardHypotheses.gibbs_sum_log_bound (h : ChessboardHypotheses g g' O F)
    (ht : 0 < t) (ht' : t < (2 * observableSupNorm (cellFamilyProduct O F) + 1)⁻¹)
    {J : Finset (Set AmbientSpace)}
    (hJ : (J : Set (Set AmbientSpace)) ⊆ g'.cellsWithin g'.fundamentalBlock)
    (hbox : GibbsBoundByTorusOnBlock.Statement) {ν : Measure D.GaugeField}
    (hν : IsGibbs D.β ν) :
    ∑ S ∈ J, ∫ U, (g'.baseCellMover S).actOn (logOnePlusRotated φ t O F) U ∂ν ≤
      (J.card : ℝ) * t * g.chessboardNormProduct O F +
        (Constants.SurfaceTerms.surfaceFactor : ℝ) * D.β *
          (PeriodicLattice.torusSide D.L D.m / D.mesh) ^ 3 := by
  classical
  have := hν.1
  have hP := h.cellProduct_props.1
  let A : Set AmbientSpace → D.GaugeField → ℝ := fun S =>
    (g'.baseCellMover S).actOn (logOnePlusRotated φ t O F)
  have hlog := h.logOnePlusRotated_mem (φ := φ) ht ht'
  have hA : ∀ S ∈ J, IsBoundedObservable (fun U => (A S U : ℂ)) ∧
      IsRegionMeasurable g'.fundamentalBlockInterior (fun U => (A S U : ℂ)) := by
    intro S hS
    have hSc := (hJ hS).1
    have hcp : (fun U => (A S U : ℂ)) =
        g'.transportTo g'.baseCell S (fun U => ((logOnePlusRotated φ t O F U : ℝ) : ℂ)) :=
      funext fun U =>
        (transport_ofReal g' (g'.mover g'.baseCell S) (logOnePlusRotated φ t O F) U).symm
    have hm := (h.coarse_transport.1 _ (baseCell_mem_cellSet g') S hSc S hSc _ hlog _ hlog).1
    rw [← hcp] at hm
    obtain ⟨h1, h2⟩ := h.coarse_of_mem hSc hm
    exact ⟨h1, isRegionMeasurable_mono (interior_mono (hJ hS).2) h2⟩
  let H : D.GaugeField → ℂ := fun U => ((∑ S ∈ J, A S U : ℝ) : ℂ)
  have hHs : H = fun U => ∑ S ∈ J, (A S U : ℂ) := funext fun U => Complex.ofReal_sum _ _
  have hHobs : IsBoundedObservable H := by
    rw [hHs]
    refine ⟨measurable_finset_sum_complex J fun S hS => (hA S hS).1.1, ?_⟩
    have hb : ∀ S ∈ J, ∃ C : ℝ, ∀ U, ‖(A S U : ℂ)‖ ≤ C := fun S hS => (hA S hS).1.2
    choose! C hC using hb
    exact ⟨∑ S ∈ J, C S, fun U =>
      (norm_sum_le _ _).trans (Finset.sum_le_sum fun S hS => hC S hS U)⟩
  have hHm : IsRegionMeasurable g'.fundamentalBlockInterior H := by
    rw [hHs]
    exact @measurable_finset_sum_complex _ _ (regionSigma g'.fundamentalBlockInterior) J _
      fun S hS => (hA S hS).2
  have hb := hbox D g' h.coarse h.coarse_side ν hν H hHobs (fun U => Complex.ofReal_im _) hHm
  have hAi : ∀ S ∈ J, Integrable (A S) ν := fun S hS =>
    (integrable_of_isBoundedObservable (hA S hS).1 ν).re.congr
      (Filter.Eventually.of_forall fun U => by simp)
  have hre : (∫ U, H U ∂ν).re = ∑ S ∈ J, ∫ U, A S U ∂ν := by
    simp only [H]
    rw [integral_complex_ofReal, Complex.ofReal_re, integral_finsetSum _ hAi]
  have hexp : (fun U => Complex.exp (H U)) =
      g'.transportedProduct J (onePlusRotated φ t O F) := by
    funext U
    rw [transportedProduct_eq_ofReal]
    simp only [H, realTransportedProduct]
    rw [← Complex.ofReal_exp, Real.exp_sum]
    congr 1
    refine Finset.prod_congr rfl fun c _ => ?_
    have hpos := half_le_one_add_mul_rotatedRealPart (φ := φ) hP ht ht'
      ((g'.baseCellMover c).pullbackField U)
    exact Real.exp_log (by linarith)
  obtain ⟨-, hpos, hle⟩ := h.expectation_transportedProduct_bound (φ := φ) ht ht' hJ
  rw [hre, hexp] at hb
  have hx : 0 ≤ t * g.chessboardNormProduct O F :=
    mul_nonneg ht.le h.chessboardNormProduct_nonneg
  have hl := Real.log_le_sub_one_of_pos
    (show 0 < 1 + t * g.chessboardNormProduct O F by linarith)
  have hlog2 : Real.log (D.periodicExpectation (D.liftedObservable
      (g'.transportedProduct J (onePlusRotated φ t O F)))).re ≤
      (J.card : ℝ) * t * g.chessboardNormProduct O F := by
    calc _ ≤ Real.log ((1 + t * g.chessboardNormProduct O F) ^ J.card) :=
          Real.log_le_log hpos hle
      _ = (J.card : ℝ) * Real.log (1 + t * g.chessboardNormProduct O F) := Real.log_pow _ _
      _ ≤ (J.card : ℝ) * (t * g.chessboardNormProduct O F) :=
          mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg _)
      _ = _ := by ring
  linarith
end Conclusions
theorem holds (hbox : GibbsBoundByTorusOnBlock.Statement)
    (hcoarse : CellParityAndCoarsening.Statement)
    (hdep : MeasurableObservablesAndLifts.Statement)
    (hgroup : ReflectionGroupAndTransport.Statement)
    (hval : GridChessboardNorm.Statement)
    (hest : ChessboardInequality.Statement)
    (htorus : InfiniteLattice.TorusStatesAsPeriodic.Statement) :
    GibbsBoundOnOneTorus.Statement := by
  intro D g hg O hO F hF hside φ t ht ht'
  have hcg := hcoarse D g hg
  obtain ⟨-, hcells, hcop⟩ :=
    hcg.2.2.1 (minScaleExponent D.L (g.cellIndexSet O)) (minCorner (g.cellIndexSet O))
  have hbase := hcg.2.2.2
  have hg' : (g.enclosingCoarsening O).IsCoarse := hg.coarsen _ _
  have hgr := hgroup D g hg
  have hgr' := hgroup D _ hg'
  have hd := hdep D
  have hfine : 2 * g.cellSide ≤ PeriodicLattice.torusSide D.L D.m := by
    have h1 := hside
    rw [g.cellSide_enclosingCoarsening] at h1
    have hL : 1 ≤ (D.L : ℝ) ^ minScaleExponent D.L (g.cellIndexSet O) :=
      one_le_pow₀ D.one_lt_factor.le
    have h2 := g.cellSide_pos
    nlinarith
  have hS : ChessboardHypotheses g (g.enclosingCoarsening O) O F :=
    { fine := hg
      coarse := hg'
      coarse_side := hside
      fine_side := hfine
      finite := hO
      mem := hF
      subset_base := hbase O hO
      cellObs := hd.2.2.1
      lifts := hd.2.2.2.2
      isProb := (htorus D.toStandingParameters D.β D.beta_pos).2.1.1
      cellObs_mono := hcells.2.2.1
      blocks_subset := hcells.2.2.2 hside
      transport_cells := hcop.1
      images_distinct := hcop.2
      fine_transport := hgr.2.2.2.1
      coarse_transport := hgr'.2.2.2.1
      unique_mover := hgr'.2.1
      norms := hval
      inequality := hest }
  refine ⟨⟨hS.rotatedRealPart_mem, hS.logOnePlusRotated_mem ht ht',
    abs_mul_rotatedRealPart_le_half hS.cellProduct_props.1 ht ht', fun ν hν h' => ?_⟩,
    fun J hJ => ⟨fun U => transportedProduct_expansion _ hO.1 J U,
      hS.expectation_transportedProduct_bound ht ht' hJ,
      fun ν hν => hS.gibbs_sum_log_bound ht ht' hJ hbox hν⟩⟩
  have := hν
  exact integral_logOnePlusRotated_lower_bound hS.cellProduct_props.1 ht ht' ν h'
end GibbsBoundOnOneTorus
end YangMills.Construction.ChessboardTori
end
