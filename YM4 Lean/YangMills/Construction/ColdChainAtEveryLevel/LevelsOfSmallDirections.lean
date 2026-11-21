import YangMills.Construction.ColdChainAtEveryLevel.ComplexCells
import YangMills.Construction.ColdChainAtEveryLevel.TermsOfTheChainAtRealCoordinates
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Matrix.Norms.L2Operator
namespace YangMills.Construction.RealDirections
open BlockAverages ComplexifiedQuaternions ComplexDifferences ComplexLevels LevelRecursion HullBounds
  ComplexRemainders PlaquetteSecondDifference RealChartTerms WeightedAverages.Chains BlockLines
variable {F : BlockFrame} {j : ℕ}
theorem levelDeviation_zero_realChart (R : F.FieldChain) (W : ChainChart F) (x : F.Site 0) (i : Fin 4) :
    levelDeviation R (realChart W) 0 x i = ofUnit (expUnit (W.fine x i)) - 1 := by
  rw [levelDeviation_realChart]
  simp only [chartField, ofUnit_mul, mul_assoc, ofUnit_mul_inv, mul_one]
theorem levelSource_realChart (W : ChainChart F) (m : ℕ) (y : F.Site (m + 1)) (d : Fin 4) :
    levelSource (realChart W) m y d = ofUnit (expUnit (W.coarse m y d)) := by
  have e : complexifiedImaginary ((realChart W).re.coarse m y d) ((realChart W).im.coarse m y d) =
      complexifiedImaginary (W.coarse m y d) 0 := rfl
  rw [levelSource, e, unitExp_complexifiedImaginary_zero]
theorem norm_ofUnit_expUnit_sub_one_le (x : imaginaryQuaternions) :
    ‖ofUnit (expUnit x) - 1‖ ≤ ‖(x : ℍ[ℝ])‖ := by
  have e : ofUnit (expUnit x) - 1 = ofQuat (((expUnit x : UnitQuaternion) : ℍ[ℝ]) - 1) := by
    simp only [ofUnit, ofQuat_sub_eq, ofQuat_one]
  rw [e, norm_ofQuat]
  exact norm_coe_expUnit_sub_one_le x
theorem norm_ofUnit_expUnit_sub_le {x x' : imaginaryQuaternions} (hx : ‖(x : ℍ[ℝ])‖ ≤ 1 / 4000)
    (hx' : ‖(x' : ℍ[ℝ])‖ ≤ 1 / 4000) :
    ‖ofUnit (expUnit x') - ofUnit (expUnit x)‖ ≤ 2 * ‖((x' - x : imaginaryQuaternions) : ℍ[ℝ])‖ := by
  have h := norm_unitExp_sub_le (y := ofQuat (x : ℍ[ℝ])) (y' := ofQuat (x' : ℍ[ℝ])) (by rwa [norm_ofQuat])
    (by rwa [norm_ofQuat])
  have ex : unitExp (ofQuat (x : ℍ[ℝ])) = ofUnit (expUnit x) := by
    rw [← unitExp_complexifiedImaginary_zero, complexifiedImaginary_zero]
  have ex' : unitExp (ofQuat (x' : ℍ[ℝ])) = ofUnit (expUnit x') := by
    rw [← unitExp_complexifiedImaginary_zero, complexifiedImaginary_zero]
  rw [ex, ex', ← ofQuat_sub_eq, norm_ofQuat] at h
  exact h
theorem abs_le_finsetLpNorm {ι : Type} {P : ℕ} (hP : 1 ≤ P) (s : Finset ι) (f : ι → ℝ) {i : ι} (hi : i ∈ s) :
    |f i| ≤ finsetLpNorm P s f := by apply _root_.YangMills.Construction.ComplexCells.abs_le_finsetLpNorm <;> assumption
theorem weightedScaleNorm_le_mul {D : Finset F.Cell} (hodd : Odd F.blockSide) (p : F.Site 0) (θ : ℝ) {P : ℕ}
    (hP : 1 ≤ P) (m : ℕ) {f g : F.Site m → Fin 4 → ℝ} {κ : ℝ} (hκ : 0 ≤ κ)
    (hfg : ∀ b ∈ innerBonds D m, |f b.1 b.2| ≤ κ * g b.1 b.2)
    (hg : ∀ b ∈ innerBonds D m, 0 ≤ g b.1 b.2) :
    weightedScaleNorm D p θ P m f ≤ κ * weightedScaleNorm D p θ P m g := by
  unfold weightedScaleNorm
  refine le_trans (finsetLpNorm_mono hP _ fun b hb => ?_) (finsetLpNorm_const_mul_le hP _ _ hκ)
  have hw := scaleWeight_pos hodd p θ m b.1
  rw [abs_mul, abs_of_pos hw, abs_mul, abs_mul, abs_of_pos hw, abs_of_nonneg hκ, abs_of_nonneg (hg b hb)]
  have := mul_le_mul_of_nonneg_left (hfg b hb) hw.le
  linarith
theorem exists_deviationBall_realChart (hrec : UniformQuarticBoundAcrossLevels) (L : ℕ) (hodd : Odd L) (h5 : 5 ≤ L)
    {C₀ : ℝ} (hC : 0 ≤ C₀) : ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧ ∀ (F : BlockFrame) (D : Finset F.Cell) (R : F.FieldChain)
      (W : ChainChart F) (s B : ℝ), F.blockSide = L → D.card ≤ 81 → ContoursNearUnit R D C₀ s → 0 ≤ s → s ≤ c →
      0 ≤ B → B ≤ c → finsetLpNorm 4 (innerBonds D 0) (fun b => ‖(W.fine b.1 b.2 : ℍ[ℝ])‖) ≤ B →
      (∀ j, j + 1 < F.top →
        finsetLpNorm 2 (innerBonds D (j + 1)) (fun b => ‖(W.coarse j b.1 b.2 : ℍ[ℝ])‖) ≤ B) →
      DeviationBall R D (realChart W) (4 * B) (4 * B) := by
  obtain ⟨c, hc0, hc1, hcl⟩ := quartic_levelDeviation_bound hrec L hodd h5 hC
  refine ⟨c, hc0, hc1, fun F D R W s B hL hD hn hs0 hs hB0 hB h0 h1 => ?_⟩
  have hgap0 : finsetLpNorm 4 (innerBonds D 0) (fun b => ‖levelDeviation R (realChart W) 0 b.1 b.2‖) ≤ B := by
    refine le_trans (finsetLpNorm_mono (by norm_num) _ fun b _ => ?_) h0
    rw [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (norm_nonneg _), levelDeviation_zero_realChart]
    exact norm_ofUnit_expUnit_sub_one_le _
  have hsrc : ∀ j, j + 1 < F.top →
      finsetLpNorm 2 (innerBonds D (j + 1)) (fun c => ‖levelSource (realChart W) j c.1 c.2 - 1‖) ≤ B := by
    intro j hj
    refine le_trans (finsetLpNorm_mono (by norm_num) _ fun b _ => ?_) (h1 j hj)
    rw [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (norm_nonneg _), levelSource_realChart]
    exact norm_ofUnit_expUnit_sub_one_le _
  have hlev := hcl F D R (realChart W) s B hL hD hn hs0 hs hB0 hB (by rwa [← finsetLpNorm_four_eq_sqrt_sqrt])
    (fun j hj => by
      have := hsrc j hj
      rwa [finsetLpNorm_two_eq_sqrt] at this)
  have hfour : ∀ m, m < F.top →
      finsetLpNorm 4 (innerBonds D m) (fun b => ‖levelDeviation R (realChart W) m b.1 b.2‖) ≤ 4 * B := by
    intro m hm
    rw [finsetLpNorm_four_eq_sqrt_sqrt]
    exact hlev m hm
  have hsf : ∀ m, m + 1 < F.top →
      finsetLpNorm 4 (innerBonds D (m + 1)) (fun c => ‖levelSource (realChart W) m c.1 c.2 - 1‖) ≤ B :=
    fun m hm => (finsetLpNorm_four_le_two _ _).trans (hsrc m hm)
  refine ⟨fun m hm b hb => ?_, hfour, fun m hm c hc => ?_, fun m hm => (hsf m hm).trans (by linarith)⟩
  · have := abs_le_finsetLpNorm (P := 4) (by norm_num) (innerBonds D m)
      (fun b => ‖levelDeviation R (realChart W) m b.1 b.2‖) hb
    rw [abs_of_nonneg (norm_nonneg _)] at this
    exact this.trans (hfour m hm)
  · have := abs_le_finsetLpNorm (P := 2) (by norm_num) (innerBonds D (m + 1))
      (fun c => ‖levelSource (realChart W) m c.1 c.2 - 1‖) hc
    rw [abs_of_nonneg (norm_nonneg _)] at this
    exact this.trans ((hsrc m hm).trans (by linarith))
theorem weightedScaleNorm_realChart_first_diff_le (hodd : Odd F.blockSide) (h2 : 2 ≤ F.blockSide)
    {D : Finset F.Cell} (hD : D.card ≤ 81) (p : F.Site 0)
    {θ : ℝ} (hθ : |θ| ≤ 1 / 8) {R : F.FieldChain} {W W' : ChainChart F} {C₀ s η B Bd : ℝ}
    (hC : 0 < C₀) (hs : 0 < s) (hnear : ContoursNearUnit R D C₀ s) (hb : DeviationBall R D (realChart W) η B)
    (hb' : DeviationBall R D (realChart W') η B) (hη0 : 0 ≤ η) (hη1 : η < 1) (hB0 : 0 ≤ B) (hBd : 0 ≤ Bd)
    (hσ : C₀ * s ≤ 1 / 64)
    (hsm : 3 * (2 * (hullBondCount F.blockSide * η) + C₀ * s) < hullBallRadius F.blockSide)
    (hfac : 568 * firstDiffFactor F.blockSide C₀ s B * hullFactor F.blockSide ≤ 1)
    (hu : ∀ b ∈ innerBonds D 0, ‖(W.fine b.1 b.2 : ℍ[ℝ])‖ ≤ 1 / 4000 ∧ ‖(W'.fine b.1 b.2 : ℍ[ℝ])‖ ≤ 1 / 4000)
    (hmu : ∀ m, m + 1 < F.top → ∀ c ∈ innerBonds D (m + 1), ‖(W.coarse m c.1 c.2 : ℍ[ℝ])‖ ≤ 1 / 4000 ∧
      ‖(W'.coarse m c.1 c.2 : ℍ[ℝ])‖ ≤ 1 / 4000)
    (h0 : weightedScaleNorm D p θ 4 0
      (fun x i => ‖((W'.fine x i - W.fine x i : imaginaryQuaternions) : ℍ[ℝ])‖) ≤ Bd)
    (h1 : ∀ m, m + 1 < F.top → weightedScaleNorm D p θ 2 (m + 1)
      (fun y d => ‖((W'.coarse m y d - W.coarse m y d : imaginaryQuaternions) : ℍ[ℝ])‖) ≤ Bd)
    (m : ℕ) (hm : m < F.top) :
    weightedScaleNorm D p θ 4 m
      (fun z d => ‖(levelDeviation R (realChart W') m - levelDeviation R (realChart W) m) z d‖) ≤ 82272 * Bd := by
  have hS : ∀ m, m + 1 < F.top → weightedScaleNorm D p θ 2 (m + 1)
      (fun y d => 2 * ‖levelSource (realChart W') m y d - levelSource (realChart W) m y d‖) ≤ 4 * Bd := by
    intro m hm
    refine le_trans (weightedScaleNorm_le_mul hodd p θ (by norm_num) (m + 1) (κ := 4) (by norm_num)
      (fun c hc => ?_) (fun _ _ => norm_nonneg _)) (mul_le_mul_of_nonneg_left (h1 m hm) (by norm_num))
    rw [abs_of_nonneg (by positivity), levelSource_realChart, levelSource_realChart]
    have := norm_ofUnit_expUnit_sub_le (hmu m hm c hc).1 (hmu m hm c hc).2
    linarith
  have hf := weightedScaleNorm_first_diff_le hodd h2 hD p hθ hC hs hnear hb hb' hη0 hη1 hB0 (by positivity) hσ hsm
    hfac hS m hm
  have h00 : weightedScaleNorm D p θ 4 0
      (fun z d => ‖(levelDeviation R (realChart W') 0 - levelDeviation R (realChart W) 0) z d‖) ≤ 2 * Bd := by
    refine le_trans (weightedScaleNorm_le_mul hodd p θ (by norm_num) 0 (κ := 2) (by norm_num) (fun b hb => ?_)
      (fun _ _ => norm_nonneg _)) (mul_le_mul_of_nonneg_left h0 (by norm_num))
    rw [abs_of_nonneg (norm_nonneg _)]
    simp only [Pi.sub_apply, levelDeviation_zero_realChart]
    have e : ofUnit (expUnit (W'.fine b.1 b.2)) - 1 - (ofUnit (expUnit (W.fine b.1 b.2)) - 1) =
        ofUnit (expUnit (W'.fine b.1 b.2)) - ofUnit (expUnit (W.fine b.1 b.2)) := by abel
    rw [e]
    exact norm_ofUnit_expUnit_sub_le (hu b hb).1 (hu b hb).2
  linarith
theorem scaleWeight_mul_scaleWeight_neg (hodd : Odd F.blockSide) (p : F.Site 0) (θ : ℝ) (m : ℕ) (x : F.Site m) :
    scaleWeight p θ m x * scaleWeight p (-θ) m x = 1 := by apply _root_.YangMills.Construction.ComplexCells.scaleWeight_mul_scaleWeight_neg <;> assumption
theorem scaleWeight_zero_angle (p : F.Site 0) (m : ℕ) (x : F.Site m) : scaleWeight p 0 m x = 1 := by
  simp [scaleWeight]
theorem weightedScaleNorm_mul_le (hodd : Odd F.blockSide) (D : Finset F.Cell) (p : F.Site 0) (θ : ℝ) (m : ℕ)
    (f g : F.Site m → Fin 4 → ℝ) :
    weightedScaleNorm D p 0 2 m (fun x d => f x d * g x d) ≤
      weightedScaleNorm D p θ 4 m f * weightedScaleNorm D p (-θ) 4 m g := by
  have e : (fun b : F.Site m × Fin 4 => scaleWeight p 0 m b.1 * (f b.1 b.2 * g b.1 b.2)) =
      fun b => (scaleWeight p θ m b.1 * f b.1 b.2) * (scaleWeight p (-θ) m b.1 * g b.1 b.2) := by
    funext b
    have h := scaleWeight_mul_scaleWeight_neg hodd p θ m b.1
    rw [scaleWeight_zero_angle]
    calc 1 * (f b.1 b.2 * g b.1 b.2) = (scaleWeight p θ m b.1 * scaleWeight p (-θ) m b.1) *
          (f b.1 b.2 * g b.1 b.2) := by rw [h]
      _ = _ := by ring
  unfold weightedScaleNorm
  rw [e]
  exact finsetLpNorm_two_mul_le _ _ _
theorem weightedScaleNorm_add_le (D : Finset F.Cell) (p : F.Site 0) (θ : ℝ) {P : ℕ} (hP : 1 ≤ P) (m : ℕ)
    (f g : F.Site m → Fin 4 → ℝ) :
    weightedScaleNorm D p θ P m (fun x d => f x d + g x d) ≤
      weightedScaleNorm D p θ P m f + weightedScaleNorm D p θ P m g := by
  unfold weightedScaleNorm
  simp only [mul_add]
  exact finsetLpNorm_add_le hP _ _ _
theorem weightedScaleNorm_four_le_two (D : Finset F.Cell) (p : F.Site 0) (θ : ℝ) (m : ℕ)
    (f : F.Site m → Fin 4 → ℝ) :
    weightedScaleNorm D p θ 4 m f ≤ weightedScaleNorm D p θ 2 m f := finsetLpNorm_four_le_two _ _
theorem weightedScaleNorm_nonneg' (D : Finset F.Cell) (p : F.Site 0) (θ : ℝ) (P m : ℕ)
    (f : F.Site m → Fin 4 → ℝ) :
    0 ≤ weightedScaleNorm D p θ P m f := finsetLpNorm_nonneg _ _ _
theorem sum_mul_le_weightedScaleNorm (hodd : Odd F.blockSide) (D : Finset F.Cell) (p : F.Site 0) (θ : ℝ) (m : ℕ)
    (f g : F.Site m → Fin 4 → ℝ) :
    ∑ b ∈ innerBonds D m, f b.1 b.2 * g b.1 b.2 ≤
      weightedScaleNorm D p θ 2 m f * weightedScaleNorm D p (-θ) 2 m g := by
  unfold weightedScaleNorm
  rw [finsetLpNorm_two_eq_sqrt, finsetLpNorm_two_eq_sqrt]
  have e : ∀ b : F.Site m × Fin 4, f b.1 b.2 * g b.1 b.2 =
      (scaleWeight p θ m b.1 * f b.1 b.2) * (scaleWeight p (-θ) m b.1 * g b.1 b.2) := by
    intro b
    have h := scaleWeight_mul_scaleWeight_neg hodd p θ m b.1
    calc f b.1 b.2 * g b.1 b.2 = (scaleWeight p θ m b.1 * scaleWeight p (-θ) m b.1) *
          (f b.1 b.2 * g b.1 b.2) := by rw [h, one_mul]
      _ = _ := by ring
  simp only [e]
  exact Real.sum_mul_le_sqrt_mul_sqrt _ _ _
theorem finsetLpNorm_two_le_mul_four {ι : Type} (s : Finset ι) (f : ι → ℝ) {T : ℝ} (hT : 0 ≤ T)
    (hc : (s.card : ℝ) ≤ T ^ 4) :
    finsetLpNorm 2 s f ≤ T * finsetLpNorm 4 s f := by
  rw [finsetLpNorm_two_eq_sqrt, finsetLpNorm_four_eq_sqrt_sqrt]
  set A := ∑ i ∈ s, f i ^ 2 with hA
  set B := ∑ i ∈ s, f i ^ 4 with hB
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun _ _ => by positivity
  have hcs : A ^ 2 ≤ (s.card : ℝ) * B := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq s (fun i => f i ^ 2) (fun _ => (1 : ℝ))
    simp only [mul_one, one_pow, Finset.sum_const, nsmul_eq_mul] at h
    have e : ∑ i ∈ s, (f i ^ 2) ^ 2 = B := Finset.sum_congr rfl fun i _ => by ring
    rw [e] at h
    linarith
  have h1 : A ^ 2 ≤ T ^ 4 * B := hcs.trans (mul_le_mul_of_nonneg_right hc hB0)
  rw [Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  have h2 : A ≤ Real.sqrt (T ^ 4 * B) := Real.le_sqrt_of_sq_le h1
  have e3 : Real.sqrt (T ^ 4 * B) = T ^ 2 * Real.sqrt B := by
    rw [Real.sqrt_mul (by positivity)]
    congr 1
    rw [show T ^ 4 = (T ^ 2) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  rw [e3] at h2
  have e4 : (T * Real.sqrt (Real.sqrt B)) ^ 2 = T ^ 2 * Real.sqrt B := by
    rw [mul_pow, Real.sq_sqrt (Real.sqrt_nonneg _)]
  rwa [e4]
theorem weightedScaleNorm_two_le_four (hodd : Odd F.blockSide) {D : Finset F.Cell} (hD : D.card ≤ 81)
    (p : F.Site 0) (θ : ℝ) (m : ℕ) (f : F.Site m → Fin 4 → ℝ) :
    weightedScaleNorm D p θ 2 m f ≤
      5 * (F.blockSide : ℝ) ^ (F.top - m) * weightedScaleNorm D p θ 4 m f := by
  refine finsetLpNorm_two_le_mul_four _ _ (by positivity) ?_
  have h1 := card_innerBonds_le hodd D m
  have h2 : ((innerBonds D m).card : ℝ) ≤
      ((4 * (D.card * (F.blockSide ^ (F.top - m)) ^ 4) : ℕ) : ℝ) := by exact_mod_cast h1
  push_cast at h2
  have h3 : (D.card : ℝ) ≤ 81 := by exact_mod_cast hD
  have h4 : (0 : ℝ) ≤ ((F.blockSide : ℝ) ^ (F.top - m)) ^ 4 := by positivity
  calc _ ≤ 4 * ((D.card : ℝ) * ((F.blockSide : ℝ) ^ (F.top - m)) ^ 4) := h2
    _ ≤ 4 * (81 * ((F.blockSide : ℝ) ^ (F.top - m)) ^ 4) := by gcongr
    _ ≤ _ := by
        rw [mul_pow]
        nlinarith
theorem norm_ofUnit_expUnit_second_diff_le {x y : imaginaryQuaternions} (hx : ‖(x : ℍ[ℝ])‖ ≤ 1 / 4000)
    (hy : ‖(y : ℍ[ℝ])‖ ≤ 1 / 4000) :
    ‖ofUnit (expUnit (x + y)) - ofUnit (expUnit x) - ofUnit (expUnit y) + 1‖ ≤
      8256 * ‖(x : ℍ[ℝ])‖ * ‖(y : ℍ[ℝ])‖ := by
  have e : ofUnit (expUnit (x + y)) - ofUnit (expUnit x) - ofUnit (expUnit y) + 1 =
      ofQuat (((expUnit (x + y) : UnitQuaternion) : ℍ[ℝ]) - (expUnit x : UnitQuaternion) -
        (expUnit y : UnitQuaternion) + 1) := by
    simp only [ofUnit, ofQuat_add, ofQuat_one, ofQuat_sub_eq]
  rw [e, norm_ofQuat]
  exact norm_expUnit_second_diff_le hx hy
def secondSourceConst (L : ℕ) : ℝ :=
  128 * (200000 * (L : ℝ) ^ 2) * (hullFactor L * 82272) ^ 2 + 6 * 8256 + 4 * (hullFactor L * 82272)
theorem bondHullNorm_nonneg' (c : F.Site (j + 1) × Fin 4) (y : F.Site j → Fin 4 → ComplexQuat) :
    0 ≤ bondHullNorm c y :=
  bondHullSum_nonneg c fun _ _ => norm_nonneg _
theorem weightedScaleNorm_realChart_second_diff_le (hodd : Odd F.blockSide) (h2 : 2 ≤ F.blockSide)
    {D : Finset F.Cell} (hD : D.card ≤ 81) (p : F.Site 0)
    {θ : ℝ} (hθ : |θ| ≤ 1 / 8) {R : F.FieldChain} {W₁ W₂ W₃ : ChainChart F} {C₀ s η B₁ B₂ : ℝ}
    (hC : 0 < C₀) (hs : 0 < s) (hnear : ContoursNearUnit R D C₀ s)
    (hb₀ : DeviationBall R D (realChart (zeroChart F)) η η) (hb₁ : DeviationBall R D (realChart W₁) η η)
    (hb₂ : DeviationBall R D (realChart W₂) η η) (hb₃ : DeviationBall R D (realChart W₃) η η)
    (hη0 : 0 ≤ η) (hη1 : 9 * η ≤ 1) (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
    (hσ : C₀ * s ≤ 1 / 64)
    (hsm : 24 * (6 * (hullBondCount F.blockSide * η) + C₀ * s) < hullBallRadius F.blockSide)
    (hsm' : 3 * (2 * (hullBondCount F.blockSide * η) + C₀ * s) < hullBallRadius F.blockSide)
    (hLip : 12 * (200000 * (F.blockSide : ℝ) ^ 2) * (6 * (hullBondCount F.blockSide * η) + C₀ * s) ≤ 1)
    (ht1 : 2 * (hullBondCount F.blockSide * η) ≤ 1)
    (hfac : 568 * secondDiffFactor F.blockSide C₀ s η * hullFactor F.blockSide ≤ 1)
    (hfac' : 568 * firstDiffFactor F.blockSide C₀ s η * hullFactor F.blockSide ≤ 1)
    (hu₁ : ∀ b ∈ innerBonds D 0, ‖(W₁.fine b.1 b.2 : ℍ[ℝ])‖ ≤ 1 / 4000)
    (hu₂ : ∀ b ∈ innerBonds D 0, ‖(W₂.fine b.1 b.2 : ℍ[ℝ])‖ ≤ 1 / 4000)
    (hu₃ : ∀ b ∈ innerBonds D 0, W₃.fine b.1 b.2 = W₁.fine b.1 b.2 + W₂.fine b.1 b.2)
    (hm₁ : ∀ m, m + 1 < F.top → ∀ c ∈ innerBonds D (m + 1), ‖(W₁.coarse m c.1 c.2 : ℍ[ℝ])‖ ≤ 1 / 4000)
    (hm₂ : ∀ m, m + 1 < F.top → ∀ c ∈ innerBonds D (m + 1), ‖(W₂.coarse m c.1 c.2 : ℍ[ℝ])‖ ≤ 1 / 4000)
    (hm₃ : ∀ m, m + 1 < F.top → ∀ c ∈ innerBonds D (m + 1),
      W₃.coarse m c.1 c.2 = W₁.coarse m c.1 c.2 + W₂.coarse m c.1 c.2)
    (h01 : weightedScaleNorm D p θ 4 0 (fun x i => ‖(W₁.fine x i : ℍ[ℝ])‖) ≤ B₁)
    (h11 : ∀ m, m + 1 < F.top →
      weightedScaleNorm D p θ 2 (m + 1) (fun y d => ‖(W₁.coarse m y d : ℍ[ℝ])‖) ≤ B₁)
    (h02 : weightedScaleNorm D p (-θ) 4 0 (fun x i => ‖(W₂.fine x i : ℍ[ℝ])‖) ≤ B₂)
    (h12 : ∀ m, m + 1 < F.top →
      weightedScaleNorm D p (-θ) 2 (m + 1) (fun y d => ‖(W₂.coarse m y d : ℍ[ℝ])‖) ≤ B₂)
    (m : ℕ) (hm : m < F.top) :
    weightedScaleNorm D p 0 2 m (fun z d => ‖(levelDeviation R (realChart W₃) m -
        levelDeviation R (realChart W₁) m - levelDeviation R (realChart W₂) m +
        levelDeviation R (realChart (zeroChart F)) m) z d‖) ≤
      2 * (142 * 8256 + 284 * secondSourceConst F.blockSide) * (B₁ * B₂) := by
  have hθ' : |(-θ)| ≤ 1 / 8 := by rwa [abs_neg]
  have hη' : η < 1 := by linarith
  have hF0 : 0 ≤ hullFactor F.blockSide := by
    obtain ⟨a, b, c⟩ := one_le_hullFactor_parts (F := F) hodd
    unfold hullFactor
    have : (0 : ℝ) ≤ hullBondCount F.blockSide := by linarith
    positivity
  have e0 : ∀ x i, (zeroChart F).fine x i = 0 := fun _ _ => rfl
  have em0 : ∀ m y d, (zeroChart F).coarse m y d = 0 := fun _ _ _ => rfl
  have hzero : ‖(((0 : imaginaryQuaternions)) : ℍ[ℝ])‖ ≤ 1 / 4000 := by
    have : (((0 : imaginaryQuaternions)) : ℍ[ℝ]) = 0 := rfl
    rw [this, norm_zero]
    norm_num
  have f1 : ∀ m, m < F.top → weightedScaleNorm D p θ 4 m
      (fun z d => ‖(levelDeviation R (realChart W₁) m - levelDeviation R (realChart (zeroChart F)) m) z d‖) ≤
        82272 * B₁ := by
    intro m hm
    refine weightedScaleNorm_realChart_first_diff_le hodd h2 hD p hθ hC hs hnear hb₀ hb₁ hη0 hη' hη0 hB₁ hσ
      hsm' hfac' (fun b hb => ⟨hzero, hu₁ b hb⟩) (fun m hm c hc => ⟨hzero, hm₁ m hm c hc⟩) ?_ (fun m hm => ?_) m hm
    · simpa [e0] using h01
    · simpa [em0] using h11 m hm
  have f2 : ∀ m, m < F.top → weightedScaleNorm D p (-θ) 4 m
      (fun z d => ‖(levelDeviation R (realChart W₂) m - levelDeviation R (realChart (zeroChart F)) m) z d‖) ≤
        82272 * B₂ := by
    intro m hm
    refine weightedScaleNorm_realChart_first_diff_le hodd h2 hD p hθ' hC hs hnear hb₀ hb₂ hη0 hη' hη0 hB₂ hσ
      hsm' hfac' (fun b hb => ⟨hzero, hu₂ b hb⟩) (fun m hm c hc => ⟨hzero, hm₂ m hm c hc⟩) ?_ (fun m hm => ?_) m hm
    · simpa [e0] using h02
    · simpa [em0] using h12 m hm
  have hn1 : ∀ m, m + 1 < F.top → weightedScaleNorm D p θ 4 (m + 1)
      (fun y d => bondHullNorm (y, d)
        (levelDeviation R (realChart W₁) m - levelDeviation R (realChart (zeroChart F)) m)) ≤
        hullFactor F.blockSide * (82272 * B₁) := by
    intro m hm
    refine (weightedScaleNorm_bondHullSum_le hodd hθ (by omega) p 4 (by norm_num) (g := fun z d =>
      ‖(levelDeviation R (realChart W₁) m - levelDeviation R (realChart (zeroChart F)) m) z d‖)
      (fun _ _ => norm_nonneg _)).trans ?_
    exact mul_le_mul_of_nonneg_left (f1 m (by omega)) hF0
  have hn2 : ∀ m, m + 1 < F.top → weightedScaleNorm D p (-θ) 4 (m + 1)
      (fun y d => bondHullNorm (y, d)
        (levelDeviation R (realChart W₂) m - levelDeviation R (realChart (zeroChart F)) m)) ≤
        hullFactor F.blockSide * (82272 * B₂) := by
    intro m hm
    refine (weightedScaleNorm_bondHullSum_le hodd hθ' (by omega) p 4 (by norm_num) (g := fun z d =>
      ‖(levelDeviation R (realChart W₂) m - levelDeviation R (realChart (zeroChart F)) m) z d‖)
      (fun _ _ => norm_nonneg _)).trans ?_
    exact mul_le_mul_of_nonneg_left (f2 m (by omega)) hF0
  have hG0 : 0 ≤ hullFactor F.blockSide * (82272 * B₁) := by positivity
  have hS : ∀ m, m + 1 < F.top → weightedScaleNorm D p 0 2 (m + 1)
      (secondDiffSource R (realChart (zeroChart F)) (realChart W₁) (realChart W₂) (realChart W₃) m) ≤
      secondSourceConst F.blockSide * (B₁ * B₂) := by
    intro m hm
    set n₁ : F.Site (m + 1) → Fin 4 → ℝ := fun y d =>
      bondHullNorm (y, d) (levelDeviation R (realChart W₁) m - levelDeviation R (realChart (zeroChart F)) m)
      with hn₁
    set n₂ : F.Site (m + 1) → Fin 4 → ℝ := fun y d =>
      bondHullNorm (y, d) (levelDeviation R (realChart W₂) m - levelDeviation R (realChart (zeroChart F)) m)
      with hn₂
    set q₁ : F.Site (m + 1) → Fin 4 → ℝ := fun y d => ‖(W₁.coarse m y d : ℍ[ℝ])‖ with hq₁
    set q₂ : F.Site (m + 1) → Fin 4 → ℝ := fun y d => ‖(W₂.coarse m y d : ℍ[ℝ])‖ with hq₂
    have n₁0 : ∀ y d, 0 ≤ n₁ y d := fun y d => bondHullNorm_nonneg' _ _
    have n₂0 : ∀ y d, 0 ≤ n₂ y d := fun y d => bondHullNorm_nonneg' _ _
    have q₁0 : ∀ y d, 0 ≤ q₁ y d := fun y d => norm_nonneg _
    have q₂0 : ∀ y d, 0 ≤ q₂ y d := fun y d => norm_nonneg _
    have hq₁4 : weightedScaleNorm D p θ 4 (m + 1) q₁ ≤ B₁ :=
      (weightedScaleNorm_four_le_two _ _ _ _ _).trans (h11 m hm)
    have hq₂4 : weightedScaleNorm D p (-θ) 4 (m + 1) q₂ ≤ B₂ :=
      (weightedScaleNorm_four_le_two _ _ _ _ _).trans (h12 m hm)
    have a1 : weightedScaleNorm D p 0 2 (m + 1) (fun y d => n₁ y d * n₂ y d) ≤
        (hullFactor F.blockSide * (82272 * B₁)) * (hullFactor F.blockSide * (82272 * B₂)) :=
      (weightedScaleNorm_mul_le hodd D p θ (m + 1) n₁ n₂).trans
        (mul_le_mul (hn1 m hm) (hn2 m hm) (weightedScaleNorm_nonneg' _ _ _ _ _ _) hG0)
    have a2 : weightedScaleNorm D p 0 2 (m + 1) (fun y d => q₁ y d * q₂ y d) ≤ B₁ * B₂ :=
      (weightedScaleNorm_mul_le hodd D p θ (m + 1) q₁ q₂).trans
        (mul_le_mul hq₁4 hq₂4 (weightedScaleNorm_nonneg' _ _ _ _ _ _) hB₁)
    have a3 : weightedScaleNorm D p 0 2 (m + 1) (fun y d => q₁ y d * n₂ y d) ≤
        B₁ * (hullFactor F.blockSide * (82272 * B₂)) :=
      (weightedScaleNorm_mul_le hodd D p θ (m + 1) q₁ n₂).trans
        (mul_le_mul hq₁4 (hn2 m hm) (weightedScaleNorm_nonneg' _ _ _ _ _ _) hB₁)
    have a4 : weightedScaleNorm D p 0 2 (m + 1) (fun y d => n₁ y d * q₂ y d) ≤
        (hullFactor F.blockSide * (82272 * B₁)) * B₂ :=
      (weightedScaleNorm_mul_le hodd D p θ (m + 1) n₁ q₂).trans
        (mul_le_mul (hn1 m hm) hq₂4 (weightedScaleNorm_nonneg' _ _ _ _ _ _) hG0)
    set K := 128 * (200000 * (F.blockSide : ℝ) ^ 2) with hK
    have hK0 : 0 ≤ K := by positivity
    have b1 : weightedScaleNorm D p 0 2 (m + 1) (fun y d => K * n₁ y d * n₂ y d) ≤
        K * weightedScaleNorm D p 0 2 (m + 1) (fun y d => n₁ y d * n₂ y d) :=
      weightedScaleNorm_le_mul hodd p 0 (by norm_num) (m + 1) hK0 (fun c _ => by
        rw [abs_of_nonneg (mul_nonneg (mul_nonneg hK0 (n₁0 _ _)) (n₂0 _ _)), mul_assoc])
        (fun c _ => mul_nonneg (n₁0 _ _) (n₂0 _ _))
    have b2 : weightedScaleNorm D p 0 2 (m + 1) (fun y d => 6 * ‖levelSource (realChart W₃) m y d -
        levelSource (realChart W₁) m y d - levelSource (realChart W₂) m y d +
        levelSource (realChart (zeroChart F)) m y d‖) ≤
        (6 * 8256) * weightedScaleNorm D p 0 2 (m + 1) (fun y d => q₁ y d * q₂ y d) := by
      refine weightedScaleNorm_le_mul hodd p 0 (by norm_num) (m + 1) (by norm_num) (fun c hc => ?_)
        (fun c _ => mul_nonneg (q₁0 _ _) (q₂0 _ _))
      rw [abs_of_nonneg (by positivity), levelSource_realChart, levelSource_realChart, levelSource_realChart,
        levelSource_realChart, hm₃ m hm c hc, em0, expUnit_zero_eq_one, ofUnit_one]
      have := norm_ofUnit_expUnit_second_diff_le (hm₁ m hm c hc) (hm₂ m hm c hc)
      simp only [hq₁, hq₂]
      nlinarith
    have b3 : weightedScaleNorm D p 0 2 (m + 1) (fun y d => 2 * ‖levelSource (realChart W₁) m y d -
        levelSource (realChart (zeroChart F)) m y d‖ * n₂ y d) ≤
        2 * weightedScaleNorm D p 0 2 (m + 1) (fun y d => q₁ y d * n₂ y d) := by
      refine weightedScaleNorm_le_mul hodd p 0 (by norm_num) (m + 1) (by norm_num) (fun c hc => ?_)
        (fun c _ => mul_nonneg (q₁0 _ _) (n₂0 _ _))
      rw [abs_of_nonneg (mul_nonneg (by positivity) (n₂0 _ _)), levelSource_realChart, levelSource_realChart,
        em0, expUnit_zero_eq_one, ofUnit_one]
      have := norm_ofUnit_expUnit_sub_one_le (W₁.coarse m c.1 c.2)
      have h3 := mul_le_mul_of_nonneg_right this (n₂0 c.1 c.2)
      simp only [hq₁]
      linarith
    have b4 : weightedScaleNorm D p 0 2 (m + 1) (fun y d => 2 * ‖levelSource (realChart W₂) m y d -
        levelSource (realChart (zeroChart F)) m y d‖ * n₁ y d) ≤
        2 * weightedScaleNorm D p 0 2 (m + 1) (fun y d => n₁ y d * q₂ y d) := by
      refine weightedScaleNorm_le_mul hodd p 0 (by norm_num) (m + 1) (by norm_num) (fun c hc => ?_)
        (fun c _ => mul_nonneg (n₁0 _ _) (q₂0 _ _))
      rw [abs_of_nonneg (mul_nonneg (by positivity) (n₁0 _ _)), levelSource_realChart, levelSource_realChart,
        em0, expUnit_zero_eq_one, ofUnit_one]
      have := norm_ofUnit_expUnit_sub_one_le (W₂.coarse m c.1 c.2)
      have h3 := mul_le_mul_of_nonneg_right this (n₁0 c.1 c.2)
      simp only [hq₂]
      linarith
    have c1 := weightedScaleNorm_add_le D p 0 (P := 2) (by norm_num) (m + 1) (fun y d => K * n₁ y d * n₂ y d)
      (fun y d => 6 * ‖levelSource (realChart W₃) m y d - levelSource (realChart W₁) m y d -
        levelSource (realChart W₂) m y d + levelSource (realChart (zeroChart F)) m y d‖)
    have c2 := weightedScaleNorm_add_le D p 0 (P := 2) (by norm_num) (m + 1)
      (fun y d => K * n₁ y d * n₂ y d + 6 * ‖levelSource (realChart W₃) m y d -
        levelSource (realChart W₁) m y d - levelSource (realChart W₂) m y d +
        levelSource (realChart (zeroChart F)) m y d‖)
      (fun y d => 2 * ‖levelSource (realChart W₁) m y d - levelSource (realChart (zeroChart F)) m y d‖ * n₂ y d)
    have c3 := weightedScaleNorm_add_le D p 0 (P := 2) (by norm_num) (m + 1)
      (fun y d => K * n₁ y d * n₂ y d + 6 * ‖levelSource (realChart W₃) m y d -
        levelSource (realChart W₁) m y d - levelSource (realChart W₂) m y d +
        levelSource (realChart (zeroChart F)) m y d‖ +
        2 * ‖levelSource (realChart W₁) m y d - levelSource (realChart (zeroChart F)) m y d‖ * n₂ y d)
      (fun y d => 2 * ‖levelSource (realChart W₂) m y d - levelSource (realChart (zeroChart F)) m y d‖ * n₁ y d)
    have e : secondDiffSource R (realChart (zeroChart F)) (realChart W₁) (realChart W₂) (realChart W₃) m =
        fun y d => K * n₁ y d * n₂ y d + 6 * ‖levelSource (realChart W₃) m y d -
          levelSource (realChart W₁) m y d - levelSource (realChart W₂) m y d +
          levelSource (realChart (zeroChart F)) m y d‖ +
          2 * ‖levelSource (realChart W₁) m y d - levelSource (realChart (zeroChart F)) m y d‖ * n₂ y d +
          2 * ‖levelSource (realChart W₂) m y d - levelSource (realChart (zeroChart F)) m y d‖ * n₁ y d := rfl
    rw [e]
    have d1 := mul_le_mul_of_nonneg_left a1 hK0
    have hfin : K * ((hullFactor F.blockSide * (82272 * B₁)) * (hullFactor F.blockSide * (82272 * B₂))) +
        6 * 8256 * (B₁ * B₂) + 2 * (B₁ * (hullFactor F.blockSide * (82272 * B₂))) +
        2 * ((hullFactor F.blockSide * (82272 * B₁)) * B₂) =
        secondSourceConst F.blockSide * (B₁ * B₂) := by
      simp only [secondSourceConst, hK]
      ring
    linarith
  have hS0 : 0 ≤ secondSourceConst F.blockSide * (B₁ * B₂) := by
    have : 0 ≤ secondSourceConst F.blockSide := by
      unfold secondSourceConst
      positivity
    positivity
  have hsd := weightedScaleNorm_second_diff_le hodd h2 p hC hs hnear hb₀ hb₁ hb₂ hb₃ hη0 hη1 hS0 hσ hsm hLip ht1
    hfac hS m hm
  have h0 : weightedScaleNorm D p 0 2 0 (fun z d => ‖(levelDeviation R (realChart W₃) 0 -
      levelDeviation R (realChart W₁) 0 - levelDeviation R (realChart W₂) 0 +
      levelDeviation R (realChart (zeroChart F)) 0) z d‖) ≤ 8256 * (B₁ * B₂) := by
    have a0 : weightedScaleNorm D p 0 2 0 (fun x i => ‖(W₁.fine x i : ℍ[ℝ])‖ * ‖(W₂.fine x i : ℍ[ℝ])‖) ≤
        B₁ * B₂ :=
      (weightedScaleNorm_mul_le hodd D p θ 0 _ _).trans
        (mul_le_mul h01 h02 (weightedScaleNorm_nonneg' _ _ _ _ _ _) hB₁)
    refine le_trans (weightedScaleNorm_le_mul hodd p 0 (by norm_num) 0 (κ := 8256) (by norm_num) (fun b hb => ?_)
      (fun b _ => by positivity)) (mul_le_mul_of_nonneg_left a0 (by norm_num))
    rw [abs_of_nonneg (norm_nonneg _)]
    simp only [Pi.add_apply, Pi.sub_apply, levelDeviation_zero_realChart, hu₃ b hb, e0, expUnit_zero_eq_one,
      ofUnit_one]
    have e : ofUnit (expUnit (W₁.fine b.1 b.2 + W₂.fine b.1 b.2)) - 1 - (ofUnit (expUnit (W₁.fine b.1 b.2)) - 1) -
        (ofUnit (expUnit (W₂.fine b.1 b.2)) - 1) + (1 - 1) =
        ofUnit (expUnit (W₁.fine b.1 b.2 + W₂.fine b.1 b.2)) - ofUnit (expUnit (W₁.fine b.1 b.2)) -
          ofUnit (expUnit (W₂.fine b.1 b.2)) + 1 := by
      abel
    rw [e]
    have := norm_ofUnit_expUnit_second_diff_le (hu₁ b hb) (hu₂ b hb)
    linarith
  have hfin : 2 * (142 * (8256 * (B₁ * B₂)) + 284 * (secondSourceConst F.blockSide * (B₁ * B₂))) =
      2 * (142 * 8256 + 284 * secondSourceConst F.blockSide) * (B₁ * B₂) := by ring
  rw [← hfin]
  have := mul_le_mul_of_nonneg_left h0 (by norm_num : (0 : ℝ) ≤ 142)
  linarith
end YangMills.Construction.RealDirections
end
