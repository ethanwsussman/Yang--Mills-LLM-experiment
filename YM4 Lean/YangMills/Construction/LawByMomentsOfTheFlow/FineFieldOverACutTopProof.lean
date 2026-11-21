import YangMills.Construction.LawByMomentsOfTheFlow.FieldOfTheColdGround
import YangMills.Construction.LawByMomentsOfTheFlow.FineFieldOverACutTop
import YangMills.Construction.ResponseInTheExpansion.OneStepOfTheLogarithmsProof
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
open BlockAverages LumpContours ColdStepAtMirrorFrames StepSettings StepCosts TorusFields TorusLumps
open TopLevelSites BlockTrees ColdStepAtMirrorFrames.BlockOffsets ColdStepAtMirrorFrames.SmallUnits
namespace MomentLaw
namespace FineFieldBounds
private theorem norm_minimalLog_le_two_mul (g : UnitQuaternion) (hg : _root_.YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets.distFromOne g < 1) :
    ‖minimalLog g‖ ≤ 2 * _root_.YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets.distFromOne g := by apply _root_.YangMills.SharedProofs.p16086 <;> assumption
private theorem norm_log_mul_sub_le {l x y : imaginaryQuaternions} (h : expUnit l = expUnit x * expUnit y)
    (hl : ‖l‖ ≤ 1) (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) :
    ‖l - x - y‖ ≤ ‖l‖ ^ 2 + ‖x‖ ^ 2 + ‖y‖ ^ 2 + ‖x‖ * ‖y‖ := by
  have el := norm_expUnit_sub_one_sub_le l hl
  have ex := norm_expUnit_sub_one_sub_le x hx
  have ey := norm_expUnit_sub_one_sub_le y hy
  have hprod : ((expUnit l : UnitQuaternion) : ℍ[ℝ]) =
      ((expUnit x : UnitQuaternion) : ℍ[ℝ]) * ((expUnit y : UnitQuaternion) : ℍ[ℝ]) := by
    rw [h]
    rfl
  set a : ℍ[ℝ] := ((expUnit x : UnitQuaternion) : ℍ[ℝ]) with ha
  set b : ℍ[ℝ] := ((expUnit y : UnitQuaternion) : ℍ[ℝ]) with hb
  set c : ℍ[ℝ] := ((expUnit l : UnitQuaternion) : ℍ[ℝ]) with hc
  have hsplit : ((l - x - y : imaginaryQuaternions) : ℍ[ℝ]) =
      -(c - 1 - (l : ℍ[ℝ])) + (a - 1 - (x : ℍ[ℝ])) + (b - 1 - (y : ℍ[ℝ])) + (a - 1) * (b - 1) := by
    rw [Submodule.coe_sub, Submodule.coe_sub, hprod]
    noncomm_ring
  have hcross : ‖(a - 1) * (b - 1)‖ ≤ ‖x‖ * ‖y‖ := by
    rw [norm_mul]
    exact mul_le_mul (distFromOne_expUnit_le x) (distFromOne_expUnit_le y) (norm_nonneg _) (norm_nonneg _)
  change ‖((l - x - y : imaginaryQuaternions) : ℍ[ℝ])‖ ≤ _
  rw [hsplit]
  calc _ ≤ ‖-(c - 1 - (l : ℍ[ℝ]))‖ + ‖a - 1 - (x : ℍ[ℝ])‖ + ‖b - 1 - (y : ℍ[ℝ])‖ + ‖(a - 1) * (b - 1)‖ := by
        refine (norm_add_le _ _).trans ?_
        gcongr
        refine (norm_add_le _ _).trans ?_
        gcongr
        exact norm_add_le _ _
    _ ≤ _ := by
        rw [norm_neg]
        linarith
private theorem expUnit_zero_eq_one : expUnit (0 : imaginaryQuaternions) = 1 := by apply _root_.YangMills.Construction.TorusFields.expUnit_zero <;> assumption
private theorem bond_numeric_bounds {T ω e κ w y x : ℝ} (hκ : 1 ≤ κ) (hT : 0 ≤ T) (hω : 0 ≤ ω) (he : 0 ≤ e)
    (hw : w ≤ κ * T ^ 2 + ω + κ * T) (hκT : κ * T ≤ 1 / 64) (hx : x ≤ w + e) (hy : y ≤ κ * T)
    (hx0 : 0 ≤ x) (hy0 : 0 ≤ y) :
    x + y ≤ 100 * κ ^ 2 * (T + ω) + e ∧
      (6 * (x + y) ^ 2 + κ * T ^ 2 + ω ≤ 100 * κ ^ 2 * (T + ω + e) ^ 2 + ω) := by
  have hT2 : T ^ 2 ≤ T := by nlinarith
  have hκ0 : 0 ≤ κ := by linarith
  have h1 : κ * T ^ 2 ≤ κ * T := mul_le_mul_of_nonneg_left hT2 hκ0
  have hκ2 : κ ≤ κ ^ 2 := by nlinarith
  have hκ1 : 1 ≤ κ ^ 2 := by nlinarith
  constructor
  · have a1 : κ * T ≤ κ ^ 2 * T := mul_le_mul_of_nonneg_right hκ2 hT
    have a2 : ω ≤ κ ^ 2 * ω := by
      have := mul_le_mul_of_nonneg_right hκ1 hω
      linarith
    have hexp : 100 * κ ^ 2 * (T + ω) = 100 * (κ ^ 2 * T) + 100 * (κ ^ 2 * ω) := by ring
    have a3 : 0 ≤ κ ^ 2 * T := by positivity
    have a4 : 0 ≤ κ ^ 2 * ω := by positivity
    rw [hexp]
    linarith
  · have hsum' : x + y ≤ 3 * κ * (T + ω + e) := by
      have a1 : ω ≤ κ * ω := by
        have := mul_le_mul_of_nonneg_right hκ hω
        linarith
      have a2 : e ≤ κ * e := by
        have := mul_le_mul_of_nonneg_right hκ he
        linarith
      have hexp : 3 * κ * (T + ω + e) = 3 * (κ * T) + 3 * (κ * ω) + 3 * (κ * e) := by ring
      rw [hexp]
      have a3 : 0 ≤ κ * ω := by positivity
      have a4 : 0 ≤ κ * e := by positivity
      linarith
    have hsum2 : (x + y) ^ 2 ≤ 9 * (κ ^ 2 * (T + ω + e) ^ 2) := by
      calc (x + y) ^ 2 ≤ (3 * κ * (T + ω + e)) ^ 2 := pow_le_pow_left₀ (by positivity) hsum' 2
        _ = 9 * (κ ^ 2 * (T + ω + e) ^ 2) := by ring
    have hT3 : T ^ 2 ≤ (T + ω + e) ^ 2 := pow_le_pow_left₀ hT (by linarith) 2
    have a5 : κ * T ^ 2 ≤ κ ^ 2 * (T + ω + e) ^ 2 :=
      mul_le_mul hκ2 hT3 (by positivity) (by positivity)
    have hexp : 100 * κ ^ 2 * (T + ω + e) ^ 2 = 100 * (κ ^ 2 * (T + ω + e) ^ 2) := by ring
    rw [hexp]
    have a6 : 0 ≤ κ ^ 2 * (T + ω + e) ^ 2 := by positivity
    linarith
variable {R : StepSetup} {n : ℕ} [NeZero n]
private theorem field_eq_expUnit_mul (hF : coldGroundFieldStatement) (A : TorusBond n → imaginaryQuaternions)
    (hodd : Odd R.params.side) (h2 : 2 ≤ n)
    (η : FreeCoords (coldSettingOver R (expField 1 A)).free) (b : (coldSettingOver R (expField 1 A)).free) :
    (coldSettingOver R (expField 1 A)).field η b.1.1 b.1.2 =
      expUnit (frameCoord R.params R.anchorRadius R.depth R.frameReach (expField 1 A) b.1 + toImaginary (η b)) *
        expUnit (crossingComponent R.params A b.1) := by
  classical
  obtain ⟨-, -, -, hform, -⟩ := hF R n (expField 1 A) hodd h2
  rw [hform η b]
  unfold crossingComponent
  split_ifs with h
  · have hval : expField 1 A (parentBlock R.params.side b.1.1) b.1.2 =
        expUnit (A (parentBlock R.params.side b.1.1, b.1.2)) := by
      unfold expField
      rw [one_smul]
    rw [hval]
  · rw [expUnit_zero_eq_one, mul_one]
private theorem bond_estimates (hF : coldGroundFieldStatement) (A : TorusBond n → imaginaryQuaternions)
    (M : TorusBond (n * R.params.side) → imaginaryQuaternions) (o : TorusSite (n * R.params.side))
    (D : ℕ) (v ω κ : ℝ) (hodd : Odd R.params.side) (h2 : 2 ≤ n) (hN : FramesNearResponse R A M o D v ω κ)
    (hκ : 1 ≤ κ) (hv : 0 ≤ v) (hω : 0 ≤ ω) (hω1 : ω ≤ 1 / 64) (hρ : R.ballRadius ≤ 1 / 64)
    (hsm : κ * (((D : ℝ) + 1) * v) ≤ 1 / 64)
    (η : FreeCoords (coldSettingOver R (expField 1 A)).free) (hη : ∀ b, coordNorm (η b) ≤ R.ballRadius)
    (c : TorusBond (n * R.params.side)) (hcD : TorusFields.supDist c.1 o ≤ D) :
    _root_.YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets.distFromOne ((coldSettingOver R (expField 1 A)).field η c.1 c.2) ≤
        100 * κ ^ 2 * (weightedBondSize o v c + ω) + freeCoordSize (coldSettingOver R (expField 1 A)) η c ∧
    ‖minimalLog ((coldSettingOver R (expField 1 A)).field η c.1 c.2) - M c -
        freeImaginaryCoord (coldSettingOver R (expField 1 A)) η c‖ ≤
        100 * κ ^ 2 * (weightedBondSize o v c + ω + freeCoordSize (coldSettingOver R (expField 1 A)) η c) ^ 2 + ω := by
  classical
  obtain ⟨-, -, hfree, -, htree⟩ := hF R n (expField 1 A) hodd h2
  have hT0 : 0 ≤ weightedBondSize o v c := by
    unfold weightedBondSize
    positivity
  by_cases hc : c ∈ (coldSettingOver R (expField 1 A)).free
  · have hch : c ∈ chartBonds R.params.side n := hfree ▸ hc
    have hform := field_eq_expUnit_mul hF A hodd h2 η ⟨c, hc⟩
    simp only at hform
    obtain ⟨w, hw⟩ : ∃ w : imaginaryQuaternions,
        w = frameCoord R.params R.anchorRadius R.depth R.frameReach (expField 1 A) c := ⟨_, rfl⟩
    obtain ⟨y, hy⟩ : ∃ y : imaginaryQuaternions, y = crossingComponent R.params A c := ⟨_, rfl⟩
    obtain ⟨p, hp⟩ : ∃ p : imaginaryQuaternions, p = toImaginary (η ⟨c, hc⟩) := ⟨_, rfl⟩
    obtain ⟨T, hT⟩ : ∃ T : ℝ, T = weightedBondSize o v c := ⟨_, rfl⟩
    obtain ⟨e, he⟩ : ∃ e : ℝ, e = freeCoordSize (coldSettingOver R (expField 1 A)) η c := ⟨_, rfl⟩
    obtain ⟨W, hWd⟩ : ∃ W : UnitQuaternion, W = (coldSettingOver R (expField 1 A)).field η c.1 c.2 := ⟨_, rfl⟩
    have hfreeCoord : freeImaginaryCoord (coldSettingOver R (expField 1 A)) η c = p := by
      unfold freeImaginaryCoord
      rw [dif_pos hc, hp]
    have hpe : ‖p‖ = e := by
      rw [he, hp]
      unfold freeCoordSize
      rw [dif_pos hc]
      rfl
    rw [← hw, ← hy, ← hp] at hform
    rw [← hWd] at hform ⊢
    rw [hfreeCoord, ← hT, ← he]
    have hfr := hN.frame_le c hch hcD
    have hre := hN.response_le c hch hcD
    have hcr := hN.crossing_le c hch hcD
    rw [← hw, ← hy, ← hT] at hfr
    rw [← hy, ← hT] at hre hcr
    have he0 : 0 ≤ e := by rw [← hpe]; exact norm_nonneg _
    have heρ : e ≤ 1 / 64 := by
      rw [he]
      unfold freeCoordSize
      rw [dif_pos hc]
      exact (hη _).trans hρ
    have hT0' : 0 ≤ T := by rw [hT]; exact hT0
    have hκT : κ * T ≤ 1 / 64 := by
      have h1 : (TorusFields.supDist c.1 o : ℝ) ≤ D := by exact_mod_cast hcD
      have h3 : T ≤ ((D : ℝ) + 1) * v := by
        rw [hT]
        unfold weightedBondSize
        exact mul_le_mul_of_nonneg_right (by linarith) hv
      have h4 := mul_le_mul_of_nonneg_left h3 (by linarith : 0 ≤ κ)
      linarith
    have hwn : ‖w‖ ≤ κ * T ^ 2 + ω + κ * T := by
      have hdecomp : w = (w + y - M c) + (M c - y) := by
        module
      rw [hdecomp]
      exact (norm_add_le _ _).trans (by linarith)
    have hxn : ‖w + p‖ ≤ ‖w‖ + e := by
      have := norm_add_le w p
      linarith
    obtain ⟨n1, n2⟩ := bond_numeric_bounds hκ hT0' hω he0 hwn hκT hxn hcr (norm_nonneg _) (norm_nonneg _)
    have hT1 : T ≤ 1 / 64 := by
      have := mul_le_mul_of_nonneg_right hκ hT0'
      linarith
    have hT2 : T ^ 2 ≤ T := by nlinarith
    have hκ0 : 0 ≤ κ := by linarith
    have hsq : κ * T ^ 2 ≤ κ * T := mul_le_mul_of_nonneg_left hT2 hκ0
    have hsmall : ‖w + p‖ + ‖y‖ ≤ 1 / 8 := by linarith
    have hsmall0 : 0 ≤ ‖w + p‖ + ‖y‖ := by positivity
    have hdist : _root_.YangMills.Construction.ColdStepAtMirrorFrames.BlockOffsets.distFromOne W ≤ ‖w + p‖ + ‖y‖ := by
      rw [hform]
      exact (distFromOne_mul _ _).trans (add_le_add (distFromOne_expUnit_le _) (distFromOne_expUnit_le _))
    refine ⟨hdist.trans n1, ?_⟩
    have hl : ‖minimalLog W‖ ≤ 2 * (‖w + p‖ + ‖y‖) :=
      (norm_minimalLog_le_two_mul W (by linarith)).trans (by linarith)
    have hprod := norm_log_mul_sub_le (l := minimalLog W) (x := w + p) (y := y)
      (by rw [expUnit_minimalLog, hform])
      (by linarith) (by linarith [norm_nonneg y]) (by linarith [norm_nonneg (w + p)])
    have hdecomp : minimalLog W - M c - p = (minimalLog W - (w + p) - y) + (w + y - M c) := by
      module
    rw [hdecomp]
    refine (norm_add_le _ _).trans ?_
    have hsq2 : ‖minimalLog W‖ ^ 2 + ‖w + p‖ ^ 2 + ‖y‖ ^ 2 + ‖w + p‖ * ‖y‖ ≤ 6 * (‖w + p‖ + ‖y‖) ^ 2 := by
      have a1 : ‖minimalLog W‖ ^ 2 ≤ (2 * (‖w + p‖ + ‖y‖)) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hl 2
      nlinarith [norm_nonneg (w + p), norm_nonneg y, mul_nonneg (norm_nonneg (w + p)) (norm_nonneg y)]
    linarith
  · have h1 : (coldSettingOver R (expField 1 A)).field η c.1 c.2 = 1 := htree η c hc
    have hch : c ∉ chartBonds R.params.side n := hfree ▸ hc
    have hfreeCoord : freeImaginaryCoord (coldSettingOver R (expField 1 A)) η c = 0 := by
      unfold freeImaginaryCoord
      rw [dif_neg hc]
    have hs0 : freeCoordSize (coldSettingOver R (expField 1 A)) η c = 0 := by
      unfold freeCoordSize
      rw [dif_neg hc]
    have hl0 : minimalLog (1 : UnitQuaternion) = 0 := by
      rw [← expUnit_zero_eq_one]
      exact minimalLog_expUnit (by simpa using Real.pi_pos)
    rw [h1, hfreeCoord, hs0, hN.eq_zero_of_not_mem c hch, hl0, distFromOne_one]
    constructor
    · have : 0 ≤ 100 * κ ^ 2 * (weightedBondSize o v c + ω) := by positivity
      linarith
    · simp only [sub_self, norm_zero, add_zero]
      have : 0 ≤ 100 * κ ^ 2 * (weightedBondSize o v c + ω) ^ 2 := by positivity
      linarith
private theorem norm_field_sub_field_zero_le (hF : coldGroundFieldStatement) (A : TorusBond n → imaginaryQuaternions)
    (hodd : Odd R.params.side) (h2 : 2 ≤ n)
    (η : FreeCoords (coldSettingOver R (expField 1 A)).free) (c : TorusBond (n * R.params.side)) :
    ‖(((coldSettingOver R (expField 1 A)).field η c.1 c.2 : UnitQuaternion) : ℍ[ℝ]) -
        ((coldSettingOver R (expField 1 A)).field 0 c.1 c.2 : UnitQuaternion)‖ ≤
      freeCoordSize (coldSettingOver R (expField 1 A)) η c := by
  classical
  obtain ⟨-, -, -, -, htree⟩ := hF R n (expField 1 A) hodd h2
  by_cases hc : c ∈ (coldSettingOver R (expField 1 A)).free
  · have h1 := field_eq_expUnit_mul hF A hodd h2 η ⟨c, hc⟩
    have h0 := field_eq_expUnit_mul hF A hodd h2 0 ⟨c, hc⟩
    simp only at h1 h0
    rw [h1, h0]
    refine (norm_mul_sub_mul_le _ _ _ _).trans ?_
    rw [sub_self, norm_zero, add_zero]
    refine (norm_expUnit_sub_le _ _).trans ?_
    unfold freeCoordSize
    rw [dif_pos hc]
    have hzero : toImaginary ((0 : FreeCoords (coldSettingOver R (expField 1 A)).free) ⟨c, hc⟩) = 0 := by
      apply Subtype.ext
      ext <;> simp [toImaginary]
    rw [hzero, add_zero]
    have hdiff : ((frameCoord R.params R.anchorRadius R.depth R.frameReach (expField 1 A) c +
          toImaginary (η ⟨c, hc⟩) : imaginaryQuaternions) : ℍ[ℝ]) -
        ((frameCoord R.params R.anchorRadius R.depth R.frameReach (expField 1 A) c : imaginaryQuaternions) : ℍ[ℝ]) =
          ((toImaginary (η ⟨c, hc⟩) : imaginaryQuaternions) : ℍ[ℝ]) := by
      push_cast
      abel
    rw [hdiff]
    exact le_of_eq rfl
  · rw [htree η c hc, htree 0 c hc, sub_self, norm_zero]
    unfold freeCoordSize
    rw [dif_neg hc]
end FineFieldBounds
open FineFieldBounds in
theorem fineFieldOverCutTop (hF : coldGroundFieldStatement) : fineFieldOverCutTopStatement := by
  intro R n _ A M o D v ω κ hodd h2 hN hκ hv hω hω1 hρ0 hρ hsm η hη
  classical
  have h0 : ∀ b, coordNorm ((0 : FreeCoords (coldSettingOver R (expField 1 A)).free) b) ≤ R.ballRadius := by
    intro b
    have hzero : toImaginary ((0 : FreeCoords (coldSettingOver R (expField 1 A)).free) b) = 0 := by
      apply Subtype.ext
      ext <;> simp [toImaginary]
    unfold coordNorm
    rw [hzero]
    simpa using hρ0
  have hz : ∀ c, freeCoordSize (coldSettingOver R (expField 1 A)) 0 c = 0 := by
    intro c
    unfold freeCoordSize
    split_ifs with hc
    · have hzero : toImaginary ((0 : FreeCoords (coldSettingOver R (expField 1 A)).free) ⟨c, hc⟩) = 0 := by
        apply Subtype.ext
        ext <;> simp [toImaginary]
      unfold coordNorm
      rw [hzero]
      simp
    · rfl
  have hzl : ∀ c, freeImaginaryCoord (coldSettingOver R (expField 1 A)) 0 c = 0 := by
    intro c
    unfold freeImaginaryCoord
    split_ifs with hc
    · apply Subtype.ext
      ext <;> simp [toImaginary]
    · rfl
  refine ⟨fun c => ?_, fun c hc => (bond_estimates hF A M o D v ω κ hodd h2 hN hκ hv hω hω1 hρ hsm η hη c hc).1,
    fun c hc => ?_, fun c _ => norm_field_sub_field_zero_le hF A hodd h2 η c,
    fun c hc => (bond_estimates hF A M o D v ω κ hodd h2 hN hκ hv hω hω1 hρ hsm η hη c hc).2, fun c hc => ?_,
    fun c => ?_, hN.curl_le⟩
  · unfold freeCoordSize
    split_ifs
    · exact norm_nonneg _
    · exact le_rfl
  · have := (bond_estimates hF A M o D v ω κ hodd h2 hN hκ hv hω hω1 hρ hsm 0 h0 c hc).1
    rw [hz, add_zero] at this
    exact this
  · have := (bond_estimates hF A M o D v ω κ hodd h2 hN hκ hv hω hω1 hρ hsm 0 h0 c hc).2
    rw [hz, hzl, add_zero, sub_zero] at this
    exact this
  · unfold freeImaginaryCoord freeCoordSize
    split_ifs with hc
    · exact le_rfl
    · simp
end MomentLaw
end YangMills.Construction
end
