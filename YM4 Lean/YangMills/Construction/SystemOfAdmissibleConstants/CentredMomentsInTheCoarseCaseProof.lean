import YangMills.Construction.Lattice.WilsonCumulantWellPosedness
import YangMills.Construction.SystemOfAdmissibleConstants.CentredMomentsInTheCoarseCase
import YangMills.Construction.SystemOfAdmissibleConstants.SizeOfAnObservableOnABall
import Mathlib
set_option autoImplicit false
open MeasureTheory YangMills.Construction.TestFunctions
noncomputable section
namespace YangMills.Construction.SeparatedMoments
open YangMills.Construction.ChessboardTori
open YangMills.Construction.InfiniteLattice (AmbientSpace smearedEnergy)
private theorem abs_integral_centredProduct_le {Ω ι : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (J : Finset ι) (X : ι → Ω → ℝ) (B : ι → ℝ)
    (hB : ∀ i ∈ J, ∀ᵐ U ∂μ, |X i U| ≤ B i) :
    |∫ U, ∏ i ∈ J, (X i U - ∫ V, X i V ∂μ) ∂μ| ≤ ∏ i ∈ J, 2 * B i := by
  have hmean : ∀ i ∈ J, |∫ V, X i V ∂μ| ≤ B i := by
    intro i hi
    have h := norm_integral_le_of_norm_le_const (μ := μ) (f := X i) (C := B i)
      (by simpa [Real.norm_eq_abs] using hB i hi)
    simpa [Real.norm_eq_abs] using h
  have hall : ∀ᵐ U ∂μ, ∀ i ∈ J, |X i U| ≤ B i := (Filter.eventually_all_finset J).2 hB
  have hprod : ∀ᵐ U ∂μ, ‖∏ i ∈ J, (X i U - ∫ V, X i V ∂μ)‖ ≤ ∏ i ∈ J, 2 * B i := by
    filter_upwards [hall] with U hU
    rw [Real.norm_eq_abs, Finset.abs_prod]
    refine Finset.prod_le_prod (fun i _ => abs_nonneg _) fun i hi => ?_
    have h1 := abs_le.1 (hU i hi)
    have h2 := abs_le.1 (hmean i hi)
    exact abs_le.2 ⟨by linarith [h1.1, h2.2], by linarith [h1.2, h2.1]⟩
  have h := norm_integral_le_of_norm_le_const hprod
  simpa [Real.norm_eq_abs] using h
private theorem two_mul_observableSize_le_coarseConstant (L : ℕ) (hL : 1 ≤ L) (a R d l : ℝ) (n : ℕ)
    (ha : 0 < a) (hR : 0 < R) (hd : 0 < d) (hd1 : d ≤ 1) (hn : 2 ≤ n) (hl : IsMaximalScalePower L d l)
    (hla : l / a < max (2 ^ 6 * (n : ℝ)) ((L : ℝ) ^ 2)) (s : ℝ) (hs : 0 ≤ s) :
    2 * (12 * (2 * R / a + 1) ^ 4 * s) ≤ coarseConstant L R n d * s := by
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hLsq : (1 : ℝ) ≤ (L : ℝ) ^ 2 := one_le_pow₀ hL1
  have hLcu : (1 : ℝ) ≤ (L : ℝ) ^ 3 := one_le_pow₀ hL1
  have h1 : l / a < 2 ^ 6 * (n : ℝ) * (L : ℝ) ^ 2 :=
    lt_of_lt_of_le hla (max_le (by nlinarith) (by nlinarith))
  have h2 : l < 2 ^ 6 * (n : ℝ) * (L : ℝ) ^ 2 * a := (div_lt_iff₀ ha).1 h1
  have hLpos : (0 : ℝ) < L := by linarith
  have h3 : (L : ℝ) * l < L * (2 ^ 6 * (n : ℝ) * (L : ℝ) ^ 2 * a) :=
    mul_lt_mul_of_pos_left h2 hLpos
  have h4 : d < 2 ^ 9 * (n : ℝ) * (L : ℝ) ^ 3 * a := by
    have := hl.2.2
    nlinarith
  set t : ℝ := (n : ℝ) / d with ht
  have ht1 : 1 ≤ t := by
    rw [ht, le_div_iff₀ hd]
    linarith
  have h5 : 1 / a ≤ 2 ^ 9 * (L : ℝ) ^ 3 * t := by
    rw [ht, div_le_iff₀ ha]
    have : 2 ^ 9 * (L : ℝ) ^ 3 * ((n : ℝ) / d) * a = (2 ^ 9 * (n : ℝ) * (L : ℝ) ^ 3 * a) / d := by
      field_simp
    rw [this, le_div_iff₀ hd]
    linarith
  set w : ℝ := 2 ^ 10 * (L : ℝ) ^ 3 * t with hw
  have hw1 : 1 ≤ w := by
    rw [hw]
    nlinarith [mul_le_mul hLcu ht1 (by norm_num) (by linarith)]
  have h6 : 2 * R / a + 1 ≤ w * (1 + R) := by
    have e : 2 * R / a = 2 * R * (1 / a) := by ring
    have h7 : 2 * R * (1 / a) ≤ 2 * R * (2 ^ 9 * (L : ℝ) ^ 3 * t) :=
      mul_le_mul_of_nonneg_left h5 (by linarith)
    have e2 : 2 * R * (2 ^ 9 * (L : ℝ) ^ 3 * t) = R * w := by rw [hw]; ring
    rw [e]
    nlinarith
  have h0 : 0 ≤ 2 * R / a + 1 := by positivity
  have h8 : (2 * R / a + 1) ^ 4 ≤ (w * (1 + R)) ^ 4 := pow_le_pow_left₀ h0 h6 4
  have e3 : coarseConstant L R n d = 24 * (w * (1 + R)) ^ 4 := by
    unfold coarseConstant
    rw [hw, ← ht]
    ring
  rw [e3]
  nlinarith [mul_le_mul_of_nonneg_right h8 hs]
private theorem isBoundedFun_of_tsupport_subset_ball {R : ℝ} (hR : 0 < R) {f : AmbientSpace → ℝ}
    (hf : IsLipschitzFor euclidDistR4 f) (hb : ∃ x, tsupport f ⊆ closedBallR4 x R) : IsBoundedFun f := by
  obtain ⟨C, hC0, hC⟩ := hf
  obtain ⟨x, hx⟩ := hb
  refine ⟨‖f x‖ + C * R, fun y => ?_⟩
  by_cases hy : y ∈ tsupport f
  · have h1 : euclidDistR4 y x ≤ R := hx hy
    have h2 := hC y x
    have h3 : ‖f y‖ ≤ ‖f x‖ + ‖f y - f x‖ := by
      simpa using norm_add_le (f x) (f y - f x)
    nlinarith [mul_le_mul_of_nonneg_left h1 hC0]
  · rw [image_eq_zero_of_notMem_tsupport hy, norm_zero]
    positivity
private theorem isBoundedFun_of_tsupport_subset_torusBall {ℓ R : ℝ} (hR : 0 < R)
    {f : TorusMetric.Torus4 ℓ → ℝ}
    (hf : IsLipschitzFor euclidDistTorus f) (hb : ∃ x, tsupport f ⊆ closedBallTorus x R) :
    IsBoundedFun f := by
  obtain ⟨C, hC0, hC⟩ := hf
  obtain ⟨x, hx⟩ := hb
  refine ⟨‖f x‖ + C * R, fun y => ?_⟩
  by_cases hy : y ∈ tsupport f
  · have h1 : euclidDistTorus y x ≤ R := hx hy
    have h2 := hC y x
    have h3 : ‖f y‖ ≤ ‖f x‖ + ‖f y - f x‖ := by
      simpa using norm_add_le (f x) (f y - f x)
    nlinarith [mul_le_mul_of_nonneg_left h1 hC0]
  · rw [image_eq_zero_of_notMem_tsupport hy, norm_zero]
    positivity
private theorem uniformNorm_nonneg' {X : Type*} (f : X → ℝ) : 0 ≤ uniformNorm f :=
  Real.iSup_nonneg fun _ => norm_nonneg _
private theorem coarseConstant_nonneg (L : ℕ) (R : ℝ) (n : ℕ) (d : ℝ) : 0 ≤ coarseConstant L R n d := by
  unfold coarseConstant
  positivity
theorem coarseCaseMomentBound_of_smearedBound
    (hsize : AdmissibleConstants.SmearedObservableBound)
    (hwilson : PeriodicLattice.WilsonCumulantWellPosedness.statement) :
    CoarseCaseMomentBound := by
  intro D M R d l n _ hR hd hd1 hn hl hla
  have hL13 : 13 ≤ D.L := D.isAdmissible.2
  have hLpos : (0 : ℝ) < D.L := by exact_mod_cast (by omega : 0 < D.L)
  have ha : 0 < D.mesh := zpow_pos hLpos _
  have hnum := two_mul_observableSize_le_coarseConstant D.L (by omega) D.mesh R d l n ha hR hd hd1 hn hl hla
  have hsizeNonneg : (0 : ℝ) ≤ 12 * (2 * R / D.mesh + 1) ^ 4 := by positivity
  refine ⟨?_, ?_⟩
  · intro ν hν f hlip hball _ J _
    have : IsProbabilityMeasure ν := hν.1.1
    refine le_trans (abs_integral_centredProduct_le ν J (fun i U => smearedEnergy (f i) U)
      (fun i => 12 * (2 * R / D.mesh + 1) ^ 4 * uniformNorm (f i)) fun i _ => ?_) ?_
    · exact Filter.Eventually.of_forall fun U =>
        hsize.1 D.mesh R ha hR (f i) (isBoundedFun_of_tsupport_subset_ball hR (hlip i) (hball i)) (hball i) U
    · refine Finset.prod_le_prod (fun i _ => ?_) fun i _ => ?_
      · exact mul_nonneg (by norm_num) (mul_nonneg hsizeNonneg (uniformNorm_nonneg' _))
      · exact (hnum _ (uniformNorm_nonneg' _)).trans
          (mul_le_mul_of_nonneg_left (le_max_left _ _) (coarseConstant_nonneg _ _ _ _))
  · intro m f hlip hball _ J _
    have : IsProbabilityMeasure (PeriodicLattice.wilsonGibbsMeasure D.L m D.K D.β) :=
      (hwilson.1 D.L m D.K D.β (by omega) m.pos D.K.pos).2.2.2
    refine le_trans (abs_integral_centredProduct_le _ J
      (fun i U => PeriodicLattice.smearedObservable (f i) U)
      (fun i => 12 * (2 * R / D.mesh + 1) ^ 4 * uniformNorm (f i)) fun i _ => ?_) ?_
    · filter_upwards [hsize.2 D.L m D.K D.β R hL13 D.beta_pos hR (f i)
        (isBoundedFun_of_tsupport_subset_torusBall hR (hlip i) (hball i)) (hball i)] with U hU
      exact hU.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (min_le_left _ _) (by norm_num)) (uniformNorm_nonneg' _))
    · refine Finset.prod_le_prod (fun i _ => ?_) fun i _ => ?_
      · exact mul_nonneg (by norm_num) (mul_nonneg hsizeNonneg (uniformNorm_nonneg' _))
      · exact (hnum _ (uniformNorm_nonneg' _)).trans
          (mul_le_mul_of_nonneg_left (le_max_left _ _) (coarseConstant_nonneg _ _ _ _))
end YangMills.Construction.SeparatedMoments
end
