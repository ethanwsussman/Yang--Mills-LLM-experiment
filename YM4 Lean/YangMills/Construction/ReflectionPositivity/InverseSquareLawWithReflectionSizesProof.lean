import YangMills.Construction.InfiniteLattice.PureAndErgodicPeriodicGibbsStates
import YangMills.Construction.ReflectionPositivity.DecayOnSiteCubeVectors
import YangMills.Construction.ReflectionPositivity.FormOfTransferPowerInAPicture
import YangMills.Construction.ReflectionPositivity.InverseSquareLawWithReflectionSizes
import YangMills.Construction.ReflectionPositivity.SitePicturesOfADirection
import Mathlib
set_option autoImplicit false
open MeasureTheory
open scoped ComplexConjugate ComplexOrder
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.DirectionPictures
open YangMills.Construction.InfiniteLattice (GaugeField IsUnitShiftErgodic condExpGiven shiftInvariantSigma
  axisStep shift unitRegionObservables plateauUnitSpacing)
open YangMills.Construction.ReflectionPositivity.MirrorHyperplanes (unitPositiveClass siteReflect)
open YangMills.Construction.SmearingFilter (spectralRateConst spectralRateFn)
open YangMills.Construction.ReflectionPositivity.EnergyMomentum (orthProj supNormCoord)
namespace InverseSquareClusteringProof
def axisReflectInGroup (μ : Fin 4) : axisReflectionGroup :=
  ⟨siteReflectPerm μ, Subgroup.subset_closure ⟨μ, rfl⟩⟩
theorem plateauUnitSpacing_eq_conj (ν : Measure (GaugeField (1 : ℝ)))
    (A B : GaugeField (1 : ℝ) → ℂ) : plateauUnitSpacing ν A B = conj (plateauUnitSpacing ν B A) := by
  unfold plateauUnitSpacing
  rw [← integral_conj]
  refine integral_congr_ae (Filter.Eventually.of_forall fun U => ?_)
  simp [mul_comm]
theorem powerOffGroundForm_diag_re_le (hdecay : CubeVectorDecay) (ν : unitPositiveClass)
    (μ : Fin 4) (r : ℕ+) {A : GaugeField (1 : ℝ) → ℂ}
    (hA : A ∈ unitRegionObservables (cubeOfRadius r)) (n : ℕ) (hn : 1 ≤ n) :
    (ReflectionPair.site.powerOffGroundForm ν μ n (cubeVector ν μ r A) (cubeVector ν μ r A)).re ≤
      spectralRateFn ((r : ℝ) / (n : ℝ)) * cubeReflectionNorm ν r A := by
  have h := (Complex.le_def.1 (hdecay.2 ν μ r A hA n hn).2).1
  rw [Complex.ofReal_re] at h
  exact h
theorem clustering_of_pos_coord (hsite : SiteReflectionPair.Conclusion)
    (hdecay : CubeVectorDecay) (hform : PowerOffGround.Holds)
    (ν : unitPositiveClass) (r : ℕ+) {A B : GaugeField (1 : ℝ) → ℂ}
    (hA : A ∈ unitRegionObservables (cubeOfRadius r)) (hB : B ∈ unitRegionObservables (cubeOfRadius r))
    (μ : Fin 4) (n : ℕ) (hn : 1 ≤ n) (y : Fin 4 → ℤ) (hy : y μ = 2 * (r : ℤ) + n) :
    ‖(∫ U, conj (A U) * (shift (intPoint y)).actOn B U
        ∂(ν : Measure (GaugeField (1 : ℝ)))) -
      plateauUnitSpacing (ν : Measure (GaugeField (1 : ℝ))) A B‖ ≤
    spectralRateFn ((r : ℝ) / (n : ℝ)) *
      cubeReflectionNorm ν r A ^ (1 / 2 : ℝ) * cubeReflectionNorm ν r B ^ (1 / 2 : ℝ) := by
  obtain ⟨hCubes, -, -, hZero, hTwo, hSizes⟩ := hsite ν μ r
  have hpic := (hform ν μ n hn).2 ReflectionPair.site
  obtain ⟨-, hsplit, hherm, hinv⟩ := hpic
  have hθA : (siteReflect μ).actOn A ∈ unitRegionObservables (cubeOfRadius r) :=
    hCubes.2.2.2.2.1 (axisReflectInGroup μ) A hA
  have hNθ : cubeReflectionNorm ν r ((siteReflect μ).actOn A) =
      cubeReflectionNorm ν r A := hSizes.2.1 (axisReflectInGroup μ) A hA
  set φA := cubeVector ν μ r ((siteReflect μ).actOn A) with hφA
  set φB := cubeVector ν μ r B with hφB
  set T := ReflectionPair.site.transferOp ν μ with hT
  set P := groundProjection μ ReflectionPair.site ν with hP
  set W := ReflectionPair.site.shiftMonomial ν μ (y - y μ • Pi.single μ 1) with hW
  have hnat : (y μ - 2 * (r : ℤ)).toNat = n := by omega
  have h1 : (∫ U, conj (A U) * (shift (intPoint y)).actOn B U
      ∂(ν : Measure (GaugeField (1 : ℝ)))) = inner ℂ φA ((T ^ n * W) φB) := by
    have h := hTwo.1 A hA B hB y (by omega)
    rw [hnat] at h
    exact h
  have hPW : P * W = P := hsplit.2.2 (orthProj μ y)
  have hTW : T ^ n * W = P + T ^ n * (1 - P) * W := by
    calc T ^ n * W = (P + T ^ n * (1 - P)) * W := by rw [← hsplit.2.1]
      _ = P * W + T ^ n * (1 - P) * W := add_mul _ _ _
      _ = P + T ^ n * (1 - P) * W := by rw [hPW]
  have h2 : inner ℂ φA ((T ^ n * W) φB) =
      inner ℂ φA (P φB) + ReflectionPair.site.powerOffGroundForm ν μ n φA (W φB) := by
    rw [hTW, add_apply, inner_add_right]
    rfl
  have hobsA := hA.1
  have hobsB := hB.1
  have hobsθ := hθA.1
  have h3 : inner ℂ φA (P φB) = plateauUnitSpacing (ν : Measure (GaugeField (1 : ℝ))) A B := by
    have hF := (hCubes.2.2.2.2.2 _ hθA).2.1
    have hH := (hCubes.2.2.2.2.2 _ hB).2.1
    have h := hZero.1 _ hF _ hH
    have e1 := (hZero.2 _ hobsθ ((r : ℕ) • axisStep (1 : ℝ) μ)).2
    have e2 := (hZero.2 _ hobsA ((r : ℕ) • axisStep (1 : ℝ) μ)).1
    have e3 := (hZero.2 _ hobsB ((r : ℕ) • axisStep (1 : ℝ) μ)).2
    refine h.trans ?_
    unfold plateauUnitSpacing
    refine integral_congr_ae ?_
    filter_upwards [e1, e2, e3] with U u1 u2 u3
    rw [← u1, u2, ← u3]
  have hc : 0 ≤ spectralRateFn ((r : ℝ) / (n : ℝ)) :=
    mul_nonneg hdecay.1.le (by positivity)
  have hdA : (ReflectionPair.site.powerOffGroundForm ν μ n φA φA).re ≤
      spectralRateFn ((r : ℝ) / (n : ℝ)) * cubeReflectionNorm ν r A := by
    have h := powerOffGroundForm_diag_re_le hdecay ν μ r hθA n hn
    rwa [hNθ] at h
  have hdB := powerOffGroundForm_diag_re_le hdecay ν μ r hB n hn
  have hWB : ReflectionPair.site.powerOffGroundForm ν μ n (W φB) (W φB) =
      ReflectionPair.site.powerOffGroundForm ν μ n φB φB := hinv (orthProj μ y) φB
  have hcs := (hherm.2.2 φA (W φB)).1
  rw [hWB] at hcs
  rw [h1, h2, h3, add_sub_cancel_left]
  calc ‖ReflectionPair.site.powerOffGroundForm ν μ n φA (W φB)‖
      ≤ Real.sqrt (ReflectionPair.site.powerOffGroundForm ν μ n φA φA).re *
          Real.sqrt (ReflectionPair.site.powerOffGroundForm ν μ n φB φB).re := hcs
    _ ≤ Real.sqrt (spectralRateFn ((r : ℝ) / (n : ℝ)) * cubeReflectionNorm ν r A) *
          Real.sqrt (spectralRateFn ((r : ℝ) / (n : ℝ)) * cubeReflectionNorm ν r B) :=
        mul_le_mul (Real.sqrt_le_sqrt hdA) (Real.sqrt_le_sqrt hdB) (Real.sqrt_nonneg _)
          (Real.sqrt_nonneg _)
    _ = spectralRateFn ((r : ℝ) / (n : ℝ)) *
          cubeReflectionNorm ν r A ^ (1 / 2 : ℝ) * cubeReflectionNorm ν r B ^ (1 / 2 : ℝ) := by
        rw [Real.sqrt_mul hc, Real.sqrt_mul hc, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow]
        have hs := Real.mul_self_sqrt hc
        calc _ = (Real.sqrt (spectralRateFn ((r : ℝ) / (n : ℝ))) *
                Real.sqrt (spectralRateFn ((r : ℝ) / (n : ℝ)))) *
              Real.sqrt (cubeReflectionNorm ν r A) * Real.sqrt (cubeReflectionNorm ν r B) := by ring
          _ = _ := by rw [hs]
theorem inverseSquareClustering_holds (hsite : SiteReflectionPair.Conclusion)
    (hdecay : CubeVectorDecay) (hform : PowerOffGround.Holds)
    (hergodic : YangMills.Construction.InfiniteLattice.ExtremalErgodicPeriodicGibbsStatement) :
    InverseSquareClustering := by
  intro ν r A hA B hB
  refine ⟨fun y hy => ?_, fun herg => ?_⟩
  · obtain ⟨μ, -, hμ⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
      (fun l => |((y l : ℤ) : ℝ)|)
    have hsep : cubeGap r y = |((y μ : ℤ) : ℝ)| - 2 * (r : ℝ) := by
      unfold cubeGap supNormCoord
      rw [hμ]
    rw [hsep] at hy ⊢
    have hint : 2 * (r : ℤ) + 1 ≤ |y μ| := by
      have h : ((2 * (r : ℤ) + 1 : ℤ) : ℝ) ≤ ((|y μ| : ℤ) : ℝ) := by
        push_cast
        linarith
      exact_mod_cast h
    obtain ⟨n, hn⟩ : ∃ n : ℕ, |y μ| = 2 * (r : ℤ) + n :=
      ⟨(|y μ| - 2 * (r : ℤ)).toNat, by omega⟩
    have hn1 : 1 ≤ n := by omega
    have hnR : |((y μ : ℤ) : ℝ)| - 2 * (r : ℝ) = (n : ℝ) := by
      have h : ((|y μ| : ℤ) : ℝ) = ((2 * (r : ℤ) + n : ℤ) : ℝ) := by rw [hn]
      push_cast at h
      linarith
    rw [hnR]
    rcases le_total 0 (y μ) with h0 | h0
    · exact clustering_of_pos_coord hsite hdecay hform ν r hA hB μ n hn1 y
        (by rw [← hn, abs_of_nonneg h0])
    · have hpos := clustering_of_pos_coord hsite hdecay hform ν r hB hA μ n hn1 (-y)
        (by rw [← hn, abs_of_nonpos h0]; rfl)
      have hconj := (hsite ν μ r).2.2.2.2.1.2.1 A hA B hB (-y)
      rw [neg_neg] at hconj
      rw [hconj, plateauUnitSpacing_eq_conj _ A B, ← map_sub, RCLike.norm_conj]
      calc _ ≤ _ := hpos
        _ = _ := by ring
  · have hprob : IsProbabilityMeasure (ν : Measure (GaugeField (1 : ℝ))) := ν.2.1
    have hfacts := ((hergodic 1 one_pos).2.1 _ herg).2
    have eA := hfacts A hA.1
    have eB := hfacts B hB.1
    unfold plateauUnitSpacing
    calc _ = ∫ _, conj (∫ U, A U ∂(ν : Measure (GaugeField (1 : ℝ)))) *
            ∫ U, B U ∂(ν : Measure (GaugeField (1 : ℝ)))
          ∂(ν : Measure (GaugeField (1 : ℝ))) := by
          refine integral_congr_ae ?_
          filter_upwards [eA, eB] with U u1 u2
          rw [u1, u2]
      _ = _ := by simp
end InverseSquareClusteringProof
end YangMills.Construction.ReflectionPositivity.DirectionPictures
