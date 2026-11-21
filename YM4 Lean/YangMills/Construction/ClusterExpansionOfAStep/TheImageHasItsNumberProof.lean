import YangMills.Construction.ClusterExpansionOfAStep.ColdIntegralIsTheColdStep
import YangMills.Construction.ClusterExpansionOfAStep.ColdSettingIsASetting
import YangMills.Construction.ClusterExpansionOfAStep.FloorsOfTheParameters
import YangMills.Construction.ClusterExpansionOfAStep.FormOfTheShares
import YangMills.Construction.ClusterExpansionOfAStep.FourDensitiesOfAStep
import YangMills.Construction.ClusterExpansionOfAStep.NumberOfFourDensities
import YangMills.Construction.ClusterExpansionOfAStep.SumOfTheDensities
import YangMills.Construction.ClusterExpansionOfAStep.TheHotHalf
import YangMills.Construction.ClusterExpansionOfAStep.TheImageHasItsNumber
import YangMills.Construction.ClusterExpansionOfAStep.TheImageIsAnArray
import YangMills.Construction.ColdStepAtMirrorFrames.ColdExpansionIsAnExpansionBelow
import YangMills.Construction.RunningCouplingSlope.DensityOfTheStepAtParametersProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ClusterExpansionOfAStep
open BlockAverages ColdStepAtMirrorFrames StepSettings TorusLumps TorusFields RenormalizationStepParameters ShareFamilies
theorem isCold_trivialField {s : ℝ} (hs : 0 < s) (n : ℕ) : IsCold s (trivialField n) := by apply _root_.YangMills.SharedProofs.p4747 <;> assumption
theorem sum_density_eq_log_sub (n : ℕ) [NeZero n] (f a act : TorusSite n → ℝ) (g : TorusSite n → ℝ)
    (x N logD logI logP : ℝ)
    (hf : ∀ Y, f Y = act Y + x * a Y - N + g Y)
    (hI : logI = ∑ Y, act Y) (hP : logP = (logD + logI) + ∑ Y, g Y) :
    ∑ Y, f Y = logP - logD + x * ∑ Y, a Y - (Fintype.card (TorusSite n) : ℝ) * N := by
  simp only [hf, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, ← Finset.mul_sum]
  rw [hP, hI]
  ring
theorem floor_bounds_of_le {C CE G Ct S X A Bh Rm : ℝ} (hCE : 0 ≤ CE) (hCt : 0 ≤ Ct) (hS : 0 ≤ S)
    (hC1 : CE * G ≤ C) (hC2 : CE ≤ C) (hC3 : 2 * Ct ≤ C) (hC4 : 2 * S ≤ C) (hC5 : 4 ≤ C)
    (hX : 0 ≤ X) (hA : 0 ≤ A) (hB : 0 ≤ Bh) (hR : 0 ≤ Rm) {M : ℝ}
    (hy : C * X + (C * A + Bh) * C + Rm ≤ M) :
    CE * X * G + 2 * (Ct * A) + 2 * (2 * Bh) ≤ M ∧ CE * X + (Ct * A + 2 * Bh) * S ≤ M := by
  have e1 : CE * X * G ≤ C * X := by
    have := mul_le_mul_of_nonneg_right hC1 hX
    linarith
  have e2 : CE * X ≤ C * X := mul_le_mul_of_nonneg_right hC2 hX
  have e3 : 2 * (Ct * A) ≤ C * A * C := by
    have h1 : 2 * Ct * A ≤ C * A := mul_le_mul_of_nonneg_right hC3 hA
    have h2 : C * A ≤ C * A * C := by
      have h0 : 0 ≤ C * A := mul_nonneg (by linarith) hA
      nlinarith
    linarith
  have e4 : 2 * (2 * Bh) ≤ Bh * C := by nlinarith
  have e5 : Ct * A * S ≤ C * A * C := by
    have h1 : Ct ≤ C := by linarith
    have h2 : S ≤ C := by linarith
    have h3 : Ct * A ≤ C * A := mul_le_mul_of_nonneg_right h1 hA
    have h4 : Ct * A * S ≤ C * A * S := mul_le_mul_of_nonneg_right h3 hS
    have h5 : C * A * S ≤ C * A * C := mul_le_mul_of_nonneg_left h2 (mul_nonneg (by linarith) hA)
    linarith
  have e6 : 2 * Bh * S ≤ Bh * C := by nlinarith
  constructor
  · nlinarith
  · nlinarith
theorem imageCarriesItsNumber_holds (h1 : TorusLumps.CurvatureCoefficientOfSum)
    (h2 : ClusterExpansionOfAStep.ExpansionDensityBoundsOfColdStep)
    (h3 : ColdStepAtMirrorFrames.ColdExpansionRegular) (h4 : ClusterExpansionOfAStep.HotFactorization)
    (h5 : StepSettings.ColdImageFactorsThroughColdStep) (h6 : StepSettings.ColdChartSettingIsAdmissible)
    (h7 : ClusterExpansionOfAStep.LogIntegralEqSumActivity) (h8 : TorusLumps.KernelImageIsDensity)
    (h9 : ShareFamilies.LevelSharesFormCurvatureFamily) (h10 : ShareFamilies.LevelSharesHaveUnitCurvatureForm)
    (h11 : StepFloors.EventuallyFloorConditions) (h12 : TorusLumps.PotentialSumsFinite) :
    ClusterExpansionOfAStep.ImageCarriesItsNumber := by
  obtain ⟨r1, hr1, H4⟩ := h4
  obtain ⟨r2, hr2, H7⟩ := h7
  refine ⟨fun c => min (r1 c) (r2 c), fun c => lt_min (hr1 c) (hr2 c), fun T hD hC hrt => ?_⟩
  obtain ⟨yh, Hh⟩ := H4 T hD (hrt.trans (min_le_left _ _))
  obtain ⟨ys, Hs⟩ := H7 T hD (hrt.trans (min_le_right _ _))
  obtain ⟨yc, Hc⟩ := h5 T hD hC
  obtain ⟨yi, Hi⟩ := h6 T hD
  have hF0 := hD.fits T.floorMin le_rfl
  obtain ⟨-, -, -, -, -, hS0, hG1⟩ := h12 T.rt T.n₁ hD.rt_pos hF0.n₁_pos
  have hCE := hD.CE_pos
  have hCt := hD.Ct_pos
  have hCs := hD.Cs_pos
  set G := weightGrowthSup T.rt T.n₁ with hGd
  set S := potentialWeightSum T.rt T.n₁ with hSd
  set C : ℝ := T.CE * G + T.CE + 2 * T.Ct + 2 * S + 4 + (4 * T.n₀ + 2 ^ 16) with hCd
  have hCEG : 0 ≤ T.CE * G := mul_nonneg hCE.le (by linarith)
  have hn0 : (0 : ℝ) ≤ T.n₀ := Nat.cast_nonneg _
  have hCpos : 0 < C := by rw [hCd]; linarith
  obtain ⟨yf, Hf⟩ := h11 T hD C 1 hCpos one_pos
  refine ⟨max (max (max yh ys) (max yc yi)) (max yf (max T.floorMin T.yC)), fun y hy R hR hArr => ?_⟩
  have b1 : yh ≤ y := ((le_max_left _ _).trans (le_max_left _ _)).trans ((le_max_left _ _).trans hy)
  have b2 : ys ≤ y := ((le_max_right _ _).trans (le_max_left _ _)).trans ((le_max_left _ _).trans hy)
  have b3 : yc ≤ y := ((le_max_left _ _).trans (le_max_right _ _)).trans ((le_max_left _ _).trans hy)
  have b4 : yi ≤ y := ((le_max_right _ _).trans (le_max_right _ _)).trans ((le_max_left _ _).trans hy)
  have b5 : yf ≤ y := (le_max_left _ _).trans ((le_max_right _ _).trans hy)
  have b6 : T.floorMin ≤ y := ((le_max_left _ _).trans (le_max_right _ _)).trans ((le_max_right _ _).trans hy)
  have b7 : T.yC ≤ y := ((le_max_right _ _).trans (le_max_right _ _)).trans ((le_max_right _ _).trans hy)
  have hHot := Hh y b1 R hR hArr
  have hSum := Hs y b2 R hR
  have hCI := Hc y b3 R hR
  have hSet := Hi y b4 R hR
  rcases R with ⟨ℓ, t, x, x', D, f, Λ, Dq, Φ, φ, ρA, p⟩
  obtain ⟨hL, hρ, hp, hxy, hstep⟩ := hR
  change ℓ = T.stepParameters y at hL
  change ρA = T.ρA at hρ
  change p = T.cutoff at hp
  change y ≤ x at hxy
  subst hL hρ hp
  set R : StepSetup := ⟨T.stepParameters y, t, x, x', D, f, Λ, Dq, Φ, φ, T.ρA, T.cutoff⟩ with hRd
  obtain ⟨hCold, hHull⟩ := hstep.1
  have hF : (T.stepParameters y).Admissible := hD.fits y b6
  have hy1 : 1 ≤ y := hF.y₁_ge
  have hxpos : 0 < x := by linarith
  have hBelow := h3 (T.stepParameters y) t x D f hF rfl hCold
  obtain ⟨c, nss, ⟨-, hc2, hc3, -, -, -, hc7, -⟩, hDA⟩ := hC
  have hSD0 : ColdStepAtMirrorFrames.ColdStepDensityConditions T.coupling c.ρA (T.threshold / 64) c.lam x T.threshold
      T.rt (T.rt / 2 ^ 10) c.δ₂ T.E T.E₃ T.Ct T.Cs T.CE
      T.side t T.n₀ T.cutoff (localFamilyOfDensity f)
      (interactionFamily T.coupling c.ρA (T.threshold / 64) c.lam x (frameRadius x) T.cutoff (localFamilyOfDensity f))
      (expansionFamily T.coupling c.ρA (T.threshold / 64) x (frameRadius x) T.cutoff (localFamilyOfDensity f))
      (frameFamily T.coupling c.ρA x (frameRadius x)) :=
    hDA T.yC le_rfl t x (b7.trans hxy) (localFamilyOfDensity f) hBelow
  rw [hc2, hc3, hc7] at hSD0
  have hSD := hSD0
  obtain ⟨hsmall, hdisp⟩ := hHot
  have hfour : ExpansionDensityBounds (T.stepParameters y) T.Cs T.CE
      (T.Ct * x * Real.exp (-(T.δc / 8 * R.frameReach)))
      (2 * Real.exp (-(T.gasRate * x / 2))) x (coldInteractionDensity R T.lam) (coldExpansionDensity R)
      (coldFrameDensity R) R.blockDensity :=
    h2 (T.stepParameters y) hF rfl t T.coupling T.ρA (T.threshold / 64) T.lam x T.δc T.Ct T.Cs T.CE
      (Real.exp (-(T.gasRate * x / 2))) T.cutoff
      (localFamilyOfDensity f) _ _ _ R.blockDensity (Real.exp_pos _).le hSD hsmall
  obtain ⟨hfam, hcarA, hsumA⟩ := h9 T hD y b6 t
  have hform := h10 T hD t
  have hσ := hD.σ_pos
  have cold98 : ∀ (n : ℕ) (V : TorusField n), IsCold T.threshold V → IsCold (9 / 8 * T.threshold) V :=
    fun n V hV a μ ν h => lt_of_lt_of_le (hV a μ ν h) (by linarith)
  have hdisplay : ∀ (n : ℕ) [NeZero n], T.n₀ ≤ n → ∀ V : TorusField n, IsCold T.threshold V →
      ∑ z, centered (sumOfFour (coldInteractionDensity R T.lam) (coldExpansionDensity R) (coldFrameDensity R)
          R.blockDensity) n z V =
        Real.log (kernelImage (T.stepParameters y) x D n V) -
          Real.log (kernelImage (T.stepParameters y) x D n (trivialField n)) +
          x * actionAtLevel (T.stepParameters y).coupling (T.stepParameters y).side (t + 1) Finset.univ V := by
    intro n _ hn V hV
    have : NeZero (n * T.side) := ⟨mul_ne_zero (NeZero.ne n) (NeZero.ne T.side)⟩
    have hLpos : 1 ≤ T.side := Nat.pos_of_ne_zero (NeZero.ne T.side)
    have hD1 : 0 < D (n * T.side) (trivialField (n * T.side)) :=
      hCold.positive (n * T.side) (hn.trans (Nat.le_mul_of_pos_right n hLpos)) _ (isCold_trivialField hσ _)
    have hΦ : ∀ W : TorusField n, IsCold T.threshold W →
        ∑ z, sumOfFour (coldInteractionDensity R T.lam) (coldExpansionDensity R) (coldFrameDensity R)
            R.blockDensity n z W =
          Real.log (kernelImage (T.stepParameters y) x D n W) - Real.log (D (n * T.side) (trivialField (n * T.side))) +
            x * ∑ z, levelShareFamily T.coupling T.side (t + 1) n z W -
            (Fintype.card (TorusSite n) : ℝ) * R.coldBlockConstant T.lam := by
      intro W hW
      obtain ⟨hci, -, hlog⟩ := hdisp n hn W hW
      have hz := hSum n hn (coldChartSetting R W) (hSet n hn W (cold98 n W hW))
      have hcd := (hCI n hn W (cold98 n W hW)).2
      have hprod : coldImageIntegral R W = D (n * T.side) (trivialField (n * T.side)) *
          ∫ η, (coldChartSetting R W).cutoffProduct η * Real.exp (-(coldChartSetting R W).potential η) := rfl
      have hI : 0 < ∫ η, (coldChartSetting R W).cutoffProduct η * Real.exp (-(coldChartSetting R W).potential η) := by
        rw [hprod] at hci
        exact (mul_pos_iff_of_pos_left hD1).mp hci
      refine sum_density_eq_log_sub n _ _ (fun Y => (coldChartSetting R W).blockActivity T.lam Y)
        (fun Y => R.blockDensity n Y W) x
        (R.coldBlockConstant T.lam) _ _ _ (fun Y => ?_) hz ?_
      · have e1 := hcd Y
        have e2 : coldLocalDensity R T.lam n Y W = (coldChartSetting R W).blockActivity T.lam Y +
            x * levelShareFamily T.coupling T.side (t + 1) n Y W - R.coldBlockConstant T.lam := by
          unfold coldLocalDensity levelShareFamily
          rw [dif_neg (NeZero.ne n), dif_neg (NeZero.ne n)]
          rfl
        show coldInteractionDensity R T.lam n Y W + coldExpansionDensity R n Y W + coldFrameDensity R n Y W +
          R.blockDensity n Y W = _
        rw [← e1, e2]
      · rw [hlog, hprod, Real.log_mul hD1.ne' hI.ne']
    have hflat := isCold_trivialField hσ n
    have s1 : ∀ (h : LocalDensity), ∑ z, centered h n z V = ∑ z, h n z V - ∑ z, h n z (trivialField n) := by
      intro h
      simp only [centered, Finset.sum_sub_distrib]
    have hA := hsumA n hn V hV
    rw [s1] at hA
    rw [s1, hΦ V hV, hΦ (trivialField n) hflat]
    show _ = _ + x * actionAtLevel T.coupling T.side (t + 1) Finset.univ V
    rw [← hA]
    ring
  have hrange : 4 * T.n₀ + 2 ^ 16 ≤ clusterRange x := by
    have h0 := (Hf x (b5.trans hxy)).range_ge
    have h1' : ((4 * T.n₀ + 2 ^ 16 : ℕ) : ℝ) ≤ clusterRange x := by
      refine le_trans ?_ h0
      push_cast
      rw [hCd]
      linarith
    exact_mod_cast h1'
  have hRow : HasExpansion (T.stepParameters y) t x D := ⟨hArr, f, hCold, Λ, Dq, Φ, φ, hHull⟩
  have hcar : SumInvariantUnderIsometries (T.stepParameters y)
      (sumOfFour (coldInteractionDensity R T.lam) (coldExpansionDensity R) (coldFrameDensity R) R.blockDensity) := by
    intro n _ hn g W W' hW hW' hCar
    have arr := (h8 (T.stepParameters y) hF t x D hxpos hrange hRow n hn).2.2.2.2 g W W' hCar
    have a1 := hsumA n hn W hW
    have a2 := hsumA n hn W' hW'
    have a3 := hcarA n hn g W W' hW hW' hCar
    rw [hdisplay n hn W' hW', hdisplay n hn W hW, arr]
    show _ + x * actionAtLevel T.coupling T.side (t + 1) Finset.univ W' =
      _ + x * actionAtLevel T.coupling T.side (t + 1) Finset.univ W
    rw [← a1, ← a2, a3]
  have hfl := (Hf x (b5.trans hxy)).error_sum
  have hX : 0 ≤ x ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hxpos.le _
  have hAe : 0 ≤ x * Real.exp (-(T.δc / 8 * R.frameReach)) := mul_nonneg hxpos.le (Real.exp_pos _).le
  have hBe : 0 ≤ Real.exp (-(T.gasRate * x / 2)) := (Real.exp_pos _).le
  have hRm : 0 ≤ x ^ C * Real.exp (-(1 * (clusterRange x : ℝ))) :=
    mul_nonneg (Real.rpow_nonneg hxpos.le _) (Real.exp_pos _).le
  have hfl' : C * x ^ (-(1 / 2 : ℝ)) + (C * (x * Real.exp (-(T.δc / 8 * R.frameReach))) +
      Real.exp (-(T.gasRate * x / 2))) * C + x ^ C * Real.exp (-(1 * (clusterRange x : ℝ))) ≤
        min 1 (T.E / 64) := by
    rw [← mul_assoc]
    exact hfl
  obtain ⟨ns1, ns2⟩ := floor_bounds_of_le (C := C) (CE := T.CE) (G := G) (Ct := T.Ct) (S := S) hCE.le
    hCt.le hS0
    (by rw [hCd]; linarith) (by rw [hCd]; linarith) (by rw [hCd]; linarith) (by rw [hCd]; linarith)
    (by rw [hCd]; linarith) hX hAe hBe hRm hfl'
  have eε : T.Ct * x * Real.exp (-(T.δc / 8 * R.frameReach)) =
      T.Ct * (x * Real.exp (-(T.δc / 8 * R.frameReach))) := mul_assoc _ _ _
  have hε0 : 0 ≤ T.Ct * x * Real.exp (-(T.δc / 8 * R.frameReach)) := by
    rw [eε]
    exact mul_nonneg hCt.le hAe
  have hfloor : T.CE * x ^ (-(1 / 2 : ℝ)) + (T.Ct * x * Real.exp (-(T.δc / 8 * R.frameReach)) +
      2 * Real.exp (-(T.gasRate * x / 2))) *
        potentialWeightSum (T.stepParameters y).rt (T.stepParameters y).n₁ ≤ 1 := by
    rw [eε]
    exact ns2.trans (min_le_left _ _)
  obtain ⟨-, -, -, -, -, hform4, hsize⟩ := h1 (T.stepParameters y) hF T.Cs T.CE _ _ x _ _ _ _ hCs.le hCE.le hε0
    (by positivity) hxpos hfour hcar hfloor
  refine ⟨hF, hfour, fun n _ hn V hV => (hdisp n hn V hV).2.1, hdisplay, hfam, hsumA, hform4, hform, hsize,
    hCs.le, hCE.le, ?_, hxpos.le, hε0, by positivity, rfl, ?_, ?_⟩
  · obtain ⟨-, -, -, -, -, -, -, hN, -⟩ := hD.chain
    exact (hN 0).le.trans (le_trans (le_max_left _ _) (le_max_left _ _))
  · show T.E ≤ T.E / T.η₃
    have hE : 0 < T.E := hF.E_pos
    rw [le_div_iff₀ hD.η₃_pos]
    nlinarith [hD.η₃_le]
  · have := ns1.trans (min_le_right _ _)
    show T.CE * x ^ (-(1 / 2 : ℝ)) * G + 2 * (T.Ct * x * Real.exp (-(T.δc / 8 * R.frameReach))) +
      2 * (2 * Real.exp (-(T.gasRate * x / 2))) ≤ T.E / 64
    rw [eε]
    exact this
end YangMills.Construction.ClusterExpansionOfAStep
end
