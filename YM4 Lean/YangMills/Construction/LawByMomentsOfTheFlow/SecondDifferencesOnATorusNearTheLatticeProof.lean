import YangMills.Construction.FreeKernel.DiscreteHeatKernelSeries
import YangMills.Construction.FreeKernel.SecondDifferencesOfTheGreenFunctionOfTheTorusProof
import YangMills.Construction.LawByMomentsOfTheFlow.GreenFunctionAsATimeIntegral
import YangMills.Construction.LawByMomentsOfTheFlow.SecondDifferencesOnATorusNearTheLattice
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.MomentLaw
open MeasureTheory YangMills.Construction.FourDimKernel YangMills.Construction.Constants.HeatKernel
open YangMills.Construction.FreeKernel.HeatKernelGreen
open YangMills.Construction.PeriodicLattice.ShortDistanceTwoPoint
open YangMills.Construction.PeriodicLattice.VectorClasses
private theorem norm_sub_term_le_of_hasSum {ι : Type*} [DecidableEq ι] {F : ι → ℂ} {a : ℂ}
    (hF : HasSum F a) (i₀ : ι) {B : ℝ} (hB : ∀ S : Finset ι, i₀ ∉ S → ∑ i ∈ S, ‖F i‖ ≤ B) :
    ‖a - F i₀‖ ≤ B := by apply _root_.YangMills.Construction.FreeKernel.TorusGreenSecondDiffProof.norm_sub_term_le_of_hasSum <;> assumption
private theorem bracketOnePlus_pos {y : ℝ} (hy : 0 ≤ y) : 0 < bracketOnePlus y := by apply _root_.YangMills.Construction.FreeKernel.TorusGreenSecondDiffProof.bracketOnePlus_pos <;> assumption
private theorem bracketOnePlus_zpow_nonneg {y : ℝ} (hy : 0 ≤ y) : 0 ≤ bracketOnePlus y ^ (-6 : ℤ) :=
  (zpow_pos (bracketOnePlus_pos hy) _).le
private theorem bracketOnePlus_zpow_le_one {y : ℝ} (hy : 0 ≤ y) : bracketOnePlus y ^ (-6 : ℤ) ≤ 1 := by apply _root_.YangMills.Construction.FreeKernel.TorusGreenSecondDiffProof.bracketOnePlus_zpow_le_one <;> assumption
private theorem sum_images_le_small_time {C : ℝ} (hC : 0 ≤ C) {n : ℕ} (hn : 0 < n) {z : Fin 4 → ℤ}
    (hz : ∀ μ, |(z μ : ℝ)| ≤ (n : ℝ) / 2) {F : (Fin 4 → ℤ) → ℂ}
    (hF : ∀ w, ‖F w‖ ≤ C * bracketOnePlus (intVecNorm (z + (n : ℤ) • w)) ^ (-6 : ℤ))
    (S : Finset (Fin 4 → ℤ)) (hS0 : (0 : Fin 4 → ℤ) ∉ S) :
    ∑ w ∈ S, ‖F w‖ ≤ 10368 * C * ((n : ℝ) ^ 6)⁻¹ := by apply _root_.YangMills.Construction.FreeKernel.TorusGreenSecondDiffProof.shortTime_images_sum_le <;> assumption
private theorem sum_images_le_intermediate_time {C : ℝ} (hC : 0 ≤ C) {n : ℕ} (hn : 0 < n) {t : ℝ}
    (ht : 0 < t) (htn : t ≤ (n : ℝ) ^ 2) {z : Fin 4 → ℤ} (hz : ∀ μ, |(z μ : ℝ)| ≤ (n : ℝ) / 2)
    {F : (Fin 4 → ℤ) → ℂ}
    (hF : ∀ w, ‖F w‖ ≤ C * t ^ (-3 : ℤ) *
      ∏ μ, bracketOnePlus (|((z + (n : ℤ) • w) μ : ℝ)| / Real.sqrt t) ^ (-6 : ℤ))
    (S : Finset (Fin 4 → ℤ)) (hS0 : (0 : Fin 4 → ℤ) ∉ S) :
    ∑ w ∈ S, ‖F w‖ ≤ 1024 * 257 ^ 3 * C * ((n : ℝ) ^ 6)⁻¹ := by apply _root_.YangMills.Construction.FreeKernel.TorusGreenSecondDiffProof.longTime_images_sum_le <;> assumption
private theorem mixedSecondDiff_apply {R : Type*} [AddCommGroup R] (ν ν' : Fin 4)
    (f : (Fin 4 → ℤ) → R) (x : Fin 4 → ℤ) :
    mixedSecondDiff ν ν' f x =
      f (x + unitVector ν) - f (x + unitVector ν - unitVector ν') - f x + f (x - unitVector ν') := by apply _root_.YangMills.Construction.FreeKernel.TorusGreenSecondDiffProof.mixedSecondDiff_apply <;> assumption
private theorem hasSum_mixedSecondDiff_translates {p P : (Fin 4 → ℤ) → ℂ} (n : ℕ)
    (hp : ∀ x, HasSum (fun w : Fin 4 → ℤ => p (x + (n : ℤ) • w)) (P x)) (ν ν' : Fin 4)
    (z : Fin 4 → ℤ) :
    HasSum (fun w : Fin 4 → ℤ => mixedSecondDiff ν ν' p (z + (n : ℤ) • w))
      (mixedSecondDiff ν ν' P z) := by apply _root_.YangMills.Construction.FreeKernel.TorusGreenSecondDiffProof.hasSum_mixedSecondDiff_translates <;> assumption
private theorem torus_mixedSecondDiff_large_time {n : ℕ} (hn : 0 < n) (hM : ExpWaveMultipliers)
    (hS : LaplacianSymbolModulusFormAndBounds) {t : ℝ} (ht : (n : ℝ) ^ 2 ≤ t) (ν ν' : Fin 4)
    (z : Fin 4 → ℤ) :
    ‖mixedSecondDiff ν ν' (torusHeatKernel n t) z‖ ≤
      64 * Real.pi ^ 2 * ((n : ℝ) ^ 6)⁻¹ * Real.exp (-8 / (n : ℝ) ^ 2 * t) := by apply _root_.YangMills.Construction.FreeKernel.TorusGreenSecondDiffProof.torusHeatKernel_mixedSecondDiff_decay <;> assumption
private theorem norm_integral_Ioi_exp_tail_le {f : ℝ → ℂ} {n : ℕ} (hn : 0 < n)
    (hf : ∀ t, (n : ℝ) ^ 2 ≤ t →
      ‖f t‖ ≤ 64 * Real.pi ^ 2 * ((n : ℝ) ^ 6)⁻¹ * Real.exp (-8 / (n : ℝ) ^ 2 * t)) :
    ‖∫ t in Set.Ioi ((n : ℝ) ^ 2), f t‖ ≤ 8 * Real.pi ^ 2 * ((n : ℝ) ^ 4)⁻¹ := by apply _root_.YangMills.Construction.FreeKernel.TorusGreenSecondDiffProof.norm_integral_Ioi_of_exp_bound <;> assumption
private theorem norm_integral_Ioi_cube_tail_le {g : ℝ → ℝ} {K : ℝ} {n : ℕ} (hn : 0 < n)
    (hg : ∀ t, (n : ℝ) ^ 2 ≤ t → |g t| ≤ K * t ^ (-3 : ℤ)) :
    ‖∫ t in Set.Ioi ((n : ℝ) ^ 2), g t‖ ≤ 1 / 2 * K * ((n : ℝ) ^ 4)⁻¹ := by apply _root_.YangMills.Construction.FreeKernel.TorusGreenSecondDiffProof.norm_integral_Ioi_of_cube_bound <;> assumption
private theorem norm_sub_time_integrals_le {f : ℝ → ℂ} {g : ℝ → ℝ} (hf : IntegrableOn f (Set.Ioi 0))
    (hg : IntegrableOn g (Set.Ioi 0)) {N a K A₁ c₂ A₃ A₄ : ℝ} (hN : 1 ≤ N) (ha : 0 < a)
    (hK : 0 ≤ K)
    (h₁ : ∀ t ∈ Set.Ioc (0 : ℝ) 1, ‖f t - (g t : ℂ)‖ ≤ A₁)
    (h₂ : ∀ t ∈ Set.Ioc (1 : ℝ) N, ‖f t - (g t : ℂ)‖ ≤
      K * ((Real.sqrt t)⁻¹ * ((Real.sqrt t + a) ^ 6)⁻¹) + c₂)
    (h₃ : ‖∫ t in Set.Ioi N, f t‖ ≤ A₃) (h₄ : ‖∫ t in Set.Ioi N, g t‖ ≤ A₄) :
    ‖(∫ t in Set.Ioi (0 : ℝ), f t) - ((∫ t in Set.Ioi (0 : ℝ), g t : ℝ) : ℂ)‖ ≤
      A₁ + K * (2 / 5 * (a ^ 5)⁻¹) + c₂ * (N - 1) + A₃ + A₄ := by apply _root_.YangMills.Construction.FreeKernel.TorusGreenSecondDiffProof.norm_integral_sub_integral_le <;> assumption
private theorem latticeHeatKernel4_eq_ofReal (hS : YangMills.Construction.FreeKernel.DiscreteHeatKernelSeries)
    {t : ℝ} (ht : 0 < t) (w : Fin 4 → ℤ) :
    latticeHeatKernel4 t w =
      ((YangMills.Construction.FreeKernel.UnitLattice.latticeHeatKernel t w : ℝ) : ℂ) := by
  unfold latticeHeatKernel4 YangMills.Construction.FreeKernel.UnitLattice.latticeHeatKernel
  rw [Complex.ofReal_prod]
  refine Finset.prod_congr rfl fun μ _ => ?_
  apply Complex.ext
  · simp [YangMills.Construction.FreeKernel.UnitLattice.integerHeatKernel]
  · simpa using (hS.2.1 t ht (w μ)).1
private theorem mixedSecondDiff_latticeHeatKernel4_eq_ofReal
    (hS : YangMills.Construction.FreeKernel.DiscreteHeatKernelSeries) {t : ℝ} (ht : 0 < t)
    (ν ν' : Fin 4) (z : Fin 4 → ℤ) :
    mixedSecondDiff ν ν' (latticeHeatKernel4 t) z =
      ((secondDiffMatrix (YangMills.Construction.FreeKernel.UnitLattice.latticeHeatKernel t) z ν ν' : ℝ) : ℂ) := by
  simp only [secondDiffMatrix, mixedSecondDiff_apply, latticeHeatKernel4_eq_ofReal hS ht]
  push_cast
  ring
open YangMills.Construction.FreeKernel.UnitLattice in
theorem torusSecondDiffNearLattice_holds (hH : YangMills.Construction.FreeKernel.HeatKernelGreen.HeatKernelGreenProperties)
    (hT : FourierFactsAndGreenIdentities.Statement)
    (hG : greenAsHeatTimeIntegralStatement) (hS : YangMills.Construction.FreeKernel.DiscreteHeatKernelSeries) :
    torusSecondDiffNearLatticeStatement := by
  set C : ℝ := (gaussianComparison 6).toReal with hCd
  have hC0 : 0 ≤ C := ENNReal.toReal_nonneg
  refine ⟨(10368 + 1024 * 257 ^ 3 + 1 / 2) * C + 8 * Real.pi ^ 2, ?_⟩
  intro n hn ν ν' z hz
  have hn0 : 0 < n := by omega
  have : NeZero n := ⟨hn0.ne'⟩
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn0
  obtain ⟨hP, hTI, -, hB, -⟩ := hH n hn ν ν'
  obtain ⟨hM, hSy, -, -, -⟩ := hT n hn
  obtain ⟨hSh, hLo⟩ := hB 6
  simp only [ShortTimeBounds, LongTimeBounds, Nat.cast_ofNat] at hSh hLo
  obtain ⟨hfI, hfE⟩ := (hTI z).2
  set g : ℝ → ℝ := fun t => secondDiffMatrix (latticeHeatKernel t) z ν ν' with hgd
  have hgI : IntegrableOn g (Set.Ioi 0) := by
    have e : g = fun t => latticeHeatKernel t (z + unitVector ν) -
        latticeHeatKernel t (z + unitVector ν - unitVector ν') -
        latticeHeatKernel t z + latticeHeatKernel t (z - unitVector ν') := by
      funext t
      simp only [hgd, secondDiffMatrix, mixedSecondDiff_apply]
    rw [e]
    exact (((hG.1 _).sub (hG.1 _)).sub (hG.1 _)).add (hG.1 _)
  have hgE : secondDiffMatrix latticeGreen z ν ν' = ∫ t in Set.Ioi (0 : ℝ), g t := by
    have e : g = fun t => latticeHeatKernel t (z + unitVector ν) -
        latticeHeatKernel t (z + unitVector ν - unitVector ν') -
        latticeHeatKernel t z + latticeHeatKernel t (z - unitVector ν') := by
      funext t
      simp only [hgd, secondDiffMatrix, mixedSecondDiff_apply]
    have i1 := hG.1 (z + unitVector ν)
    have i2 := hG.1 (z + unitVector ν - unitVector ν')
    have i3 := hG.1 z
    have i4 := hG.1 (z - unitVector ν')
    have c1 : ∫ t in Set.Ioi (0 : ℝ), g t =
        (∫ t in Set.Ioi (0 : ℝ), (latticeHeatKernel t (z + unitVector ν) -
          latticeHeatKernel t (z + unitVector ν - unitVector ν') -
          latticeHeatKernel t z)) +
        ∫ t in Set.Ioi (0 : ℝ), latticeHeatKernel t (z - unitVector ν') := by
      rw [e]
      exact integral_add ((i1.sub i2).sub i3) i4
    have c2 : ∫ t in Set.Ioi (0 : ℝ), (latticeHeatKernel t (z + unitVector ν) -
          latticeHeatKernel t (z + unitVector ν - unitVector ν') -
          latticeHeatKernel t z) =
        (∫ t in Set.Ioi (0 : ℝ), (latticeHeatKernel t (z + unitVector ν) -
          latticeHeatKernel t (z + unitVector ν - unitVector ν'))) -
        ∫ t in Set.Ioi (0 : ℝ), latticeHeatKernel t z :=
      integral_sub (i1.sub i2) i3
    have c3 : ∫ t in Set.Ioi (0 : ℝ), (latticeHeatKernel t (z + unitVector ν) -
          latticeHeatKernel t (z + unitVector ν - unitVector ν')) =
        (∫ t in Set.Ioi (0 : ℝ), latticeHeatKernel t (z + unitVector ν)) -
        ∫ t in Set.Ioi (0 : ℝ), latticeHeatKernel t (z + unitVector ν - unitVector ν') :=
      integral_sub i1 i2
    rw [c1, c2, c3]
    simp only [secondDiffMatrix, mixedSecondDiff_apply, latticeGreen]
  have hsum : ∀ t, 0 < t → HasSum
      (fun w : Fin 4 → ℤ => mixedSecondDiff ν ν' (latticeHeatKernel4 t) (z + (n : ℤ) • w))
      (mixedSecondDiff ν ν' (torusHeatKernel n t) z) := fun t ht =>
    hasSum_mixedSecondDiff_translates n (fun x => (hP t ht).2.2.2 x) ν ν' z
  have hone : ∀ t ∈ Set.Ioc (0 : ℝ) 1,
      ‖mixedSecondDiff ν ν' (torusHeatKernel n t) z - ((g t : ℝ) : ℂ)‖ ≤
        10368 * C * ((n : ℝ) ^ 6)⁻¹ := by
    rintro t ⟨ht0, ht1⟩
    have hA := norm_sub_term_le_of_hasSum (hsum t ht0) 0 (fun S h0 =>
      sum_images_le_small_time hC0 hn0 hz (fun w => (hSh _ t ht0 ht1).1) S h0)
    simp only [smul_zero, add_zero] at hA
    rwa [mixedSecondDiff_latticeHeatKernel4_eq_ofReal hS ht0] at hA
  have htwo : ∀ t ∈ Set.Ioc (1 : ℝ) ((n : ℝ) ^ 2),
      ‖mixedSecondDiff ν ν' (torusHeatKernel n t) z - ((g t : ℝ) : ℂ)‖ ≤
        0 * ((Real.sqrt t)⁻¹ * ((Real.sqrt t + 1) ^ 6)⁻¹) + 1024 * 257 ^ 3 * C * ((n : ℝ) ^ 6)⁻¹ := by
    rintro t ⟨ht1, htn⟩
    have ht0 : 0 < t := by linarith
    have hA := norm_sub_term_le_of_hasSum (hsum t ht0) 0 (fun S h0 =>
      sum_images_le_intermediate_time hC0 hn0 ht0 htn hz (fun w => (hLo _ t ht1.le).1) S h0)
    simp only [smul_zero, add_zero] at hA
    rw [mixedSecondDiff_latticeHeatKernel4_eq_ofReal hS ht0] at hA
    simpa using hA
  have hn2 : (1 : ℝ) ≤ (n : ℝ) ^ 2 := one_le_pow₀ hn1
  have hgt : ∀ t, (n : ℝ) ^ 2 ≤ t → |g t| ≤ C * t ^ (-3 : ℤ) := by
    intro t ht
    have ht1 : 1 ≤ t := hn2.trans ht
    have ht0 : 0 < t := by linarith
    have h1 := (hLo z t ht1).1
    rw [mixedSecondDiff_latticeHeatKernel4_eq_ofReal hS ht0, Complex.norm_real,
      Real.norm_eq_abs] at h1
    refine h1.trans ?_
    have hp : ∏ μ, bracketOnePlus (|(z μ : ℝ)| / Real.sqrt t) ^ (-6 : ℤ) ≤ 1 :=
      Finset.prod_le_one (fun _ _ => bracketOnePlus_zpow_nonneg (by positivity))
        (fun _ _ => bracketOnePlus_zpow_le_one (by positivity))
    have hc : 0 ≤ C * t ^ (-3 : ℤ) := by positivity
    nlinarith
  have main := norm_sub_time_integrals_le hfI hgI hn2 (a := 1) (K := 0) (by norm_num) le_rfl
    hone htwo
    (norm_integral_Ioi_exp_tail_le hn0 fun t ht => torus_mixedSecondDiff_large_time hn0 hM hSy ht ν ν' z)
    (norm_integral_Ioi_cube_tail_le (K := C) hn0 hgt)
  rw [← hfE, ← hgE] at main
  have hre : secondDiffMatrix (fun w => (greenOnVectors n w).re) z ν ν' =
      (mixedSecondDiff ν ν' (greenOnVectors n) z).re := by
    simp only [secondDiffMatrix, mixedSecondDiff_apply, Complex.add_re, Complex.sub_re]
  rw [hre]
  have h1 : |(mixedSecondDiff ν ν' (greenOnVectors n) z).re -
      secondDiffMatrix latticeGreen z ν ν'| ≤
      ‖mixedSecondDiff ν ν' (greenOnVectors n) z -
        ((secondDiffMatrix latticeGreen z ν ν' : ℝ) : ℂ)‖ := by
    have := Complex.abs_re_le_norm (mixedSecondDiff ν ν' (greenOnVectors n) z -
        ((secondDiffMatrix latticeGreen z ν ν' : ℝ) : ℂ))
    simpa using this
  refine h1.trans (main.trans ?_)
  set Y : ℝ := ((n : ℝ) ^ 4)⁻¹ with hY
  set W : ℝ := ((n : ℝ) ^ 6)⁻¹ with hW
  have hW0 : 0 ≤ W := by positivity
  have e2 : W * (n : ℝ) ^ 2 = Y := by
    rw [hW, hY]
    field_simp
  have hWY : W ≤ Y := by
    rw [← e2]
    nlinarith
  have h2 : 0 ≤ C * Y := by positivity
  have h4 : 0 ≤ C * W := by positivity
  have h5 : C * W * (n : ℝ) ^ 2 = C * Y := by rw [← e2]; ring
  nlinarith
end YangMills.Construction.MomentLaw
end
