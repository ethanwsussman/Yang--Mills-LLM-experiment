import YangMills.Construction.ColdChainAtEveryLevel.CellFamilies
import YangMills.Construction.ColdChainAtEveryLevel.LevelsOfSmallDirections
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Matrix.Norms.L2Operator
namespace YangMills.Construction.LinearLevels
open BlockAverages ComplexifiedQuaternions ComplexContours ComplexRemainders ComplexLevels ComplexDifferences
  ComplexChainStep RealDirections PlaquetteSecondDifference RealChartTerms HullBounds LevelRecursion
variable {F : BlockFrame} {j : ℕ}
theorem conjByUnit_ofQuat (g : UnitQuaternion) (w : ℍ[ℝ]) : conjByUnit g (ofQuat w) = ofQuat (adjointAction g w) := by apply _root_.YangMills.Construction.CellSpans.conjByUnit_ofQuat <;> assumption
theorem transportedAverage_ofQuat (A : F.GaugeField j) (f : F.Site j → Fin 4 → ℍ[ℝ]) (c : F.Site (j + 1) × Fin 4) :
    transportedAverage A (fun x i => ofQuat (f x i)) c = ofQuat (parallelAverage A f c) := by
  simp only [transportedAverage, parallelAverage, blockContourMean, ofQuat_smul, ofQuat_sum, conjByUnit_ofQuat,
    contourWeight]
theorem pureComponent_parallelAverage (A : F.GaugeField j) (f : F.Site j → Fin 4 → ℍ[ℝ])
    (c : F.Site (j + 1) × Fin 4) :
    pureComponent (parallelAverage A f c) = parallelAverage A (fun x i => pureComponent (f x i)) c := by
  simp only [parallelAverage, pureComponent_smul, pureComponent_sum, pureComponent_adjointAction]
theorem pureComponent_imaginary (x : imaginaryQuaternions) : pureComponent (x : ℍ[ℝ]) = x := by
  have : (x : ℍ[ℝ]) - star (x : ℍ[ℝ]) = (2 : ℝ) • (x : ℍ[ℝ]) := by
    rw [star_coe_imaginary, two_smul]
    abel
  rw [pureComponent, this, smul_smul]
  norm_num
theorem pureComponent_linearPart (A : F.FieldChain) (V : ChainChart F) (m : ℕ) (x : F.Site m) (i : Fin 4) :
    pureComponent (linearPart A V m x i) = linearPart A V m x i := by
  induction m generalizing i with
  | zero => exact pureComponent_imaginary _
  | succ m ih =>
    have h : (fun x i => pureComponent (linearPart A V m x i)) = linearPart A V m := by
      funext x' i'
      exact ih x' i'
    simp only [linearPart]
    rw [pureComponent_add, pureComponent_parallelAverage, h]
    congr 1
    split_ifs with hc
    · exact pureComponent_imaginary _
    · have := pureComponent_coe 0
      simpa using this
theorem purePart_transportedAverage_linearPart (A : F.FieldChain) (V : ChainChart F) (m : ℕ)
    (c : F.Site (m + 1) × Fin 4) :
    purePart (transportedAverage (A m) (fun x i => ofQuat (linearPart A V m x i)) c) =
      ofQuat (parallelAverage (A m) (linearPart A V m) c) := by
  have h : (fun x i => pureComponent (linearPart A V m x i)) = linearPart A V m := by
    funext x i
    exact pureComponent_linearPart A V m x i
  rw [transportedAverage_ofQuat, purePart_ofQuat]
  change ofQuat (pureComponent _) = _
  rw [pureComponent_parallelAverage, h]
theorem norm_conjByUnit_sub_le (g : UnitQuaternion) (z : ComplexQuat) :
    ‖conjByUnit g z - z‖ ≤ 2 * ‖(g : ℍ[ℝ]) - 1‖ * ‖z‖ := by
  have e : conjByUnit g z - z = (ofUnit g - 1) * z * ofUnit g⁻¹ + z * (ofUnit g⁻¹ - 1) := by
    simp only [conjByUnit]
    noncomm_ring
  have hg : ‖ofUnit g - 1‖ = ‖(g : ℍ[ℝ]) - 1‖ := by
    have : ofUnit g - 1 = ofQuat ((g : ℍ[ℝ]) - 1) := by simp only [ofUnit, ofQuat_sub_eq, ofQuat_one]
    rw [this, norm_ofQuat]
  have hi : ‖ofUnit g⁻¹ - 1‖ = ‖(g : ℍ[ℝ]) - 1‖ := by
    have : ofUnit g⁻¹ - 1 = ofQuat (((g⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1) := by
      simp only [ofUnit, ofQuat_sub_eq, ofQuat_one]
    rw [this, norm_ofQuat, norm_coe_inv_sub_one]
  rw [e]
  refine (norm_add_le _ _).trans ?_
  have a1 : ‖(ofUnit g - 1) * z * ofUnit g⁻¹‖ = ‖(ofUnit g - 1) * z‖ := norm_mul_ofUnit _ _
  rw [a1]
  have a2 := norm_mul_le (ofUnit g - 1) z
  have a3 := norm_mul_le z (ofUnit g⁻¹ - 1)
  rw [hg] at a2
  rw [hi] at a3
  nlinarith [norm_nonneg z]
theorem norm_ofUnit_expUnit_sub_one_sub_le {x : imaginaryQuaternions} (hx : ‖(x : ℍ[ℝ])‖ ≤ 1) :
    ‖ofUnit (expUnit x) - 1 - ofQuat (x : ℍ[ℝ])‖ ≤ ‖(x : ℍ[ℝ])‖ ^ 2 := by
  have e : ofUnit (expUnit x) - 1 - ofQuat (x : ℍ[ℝ]) =
      ofQuat (((expUnit x : UnitQuaternion) : ℍ[ℝ]) - 1 - (x : ℍ[ℝ])) := by
    simp only [ofUnit, ofQuat_sub_eq, ofQuat_one]
  rw [e, norm_ofQuat]
  exact PlaquetteSecondDifference.norm_expUnit_sub_one_sub_le hx
section Steps
variable (hodd : Odd F.blockSide) (A : F.FieldChain) (V : ChainChart F) {σ t : ℝ}
include hodd
theorem norm_linearizedUnit_sub_linearPart_le (hj : j + 1 ≤ F.top) {c : F.Site (j + 1) × Fin 4} (hσ : σ ≤ 1 / 64)
    (href : ∀ h ∈ centredCube F.blockSide, ∀ π, ‖ofUnit (pathHolonomy (A j) (refineSite c.1)
      (bondContour F.blockSide h π c.2) * (polarUnit (contourAverage (A j) c))⁻¹) - 1‖ ≤ σ)
    (hy : 8 * (F.blockSide : ℝ) * bondHullNorm c (levelDeviation A (realChart V) j) ≤ 1 / 1024) :
    ‖linearizedUnit (A j) c (levelDeviation A (realChart V) j) - 1 -
        ofQuat (parallelAverage (A j) (linearPart A V j) c)‖ ≤
      lineBlockAverage (fun x d => ‖levelDeviation A (realChart V) j x d - ofQuat (linearPart A V j x d)‖) c +
        200000 * (F.blockSide : ℝ) ^ 2 * (bondHullNorm c (levelDeviation A (realChart V) j) ^ 2 +
          σ * bondHullNorm c (levelDeviation A (realChart V) j)) := by
  set y := levelDeviation A (realChart V) j with hyd
  have hω := (remainder_bounds hodd hj hσ hy href).2.1
  have e : linearizedUnit (A j) c y - 1 - ofQuat (parallelAverage (A j) (linearPart A V j) c) =
      purePart (transportedAverage (A j) (fun x d => y x d - ofQuat (linearPart A V j x d)) c) +
        unitRemainder (A j) c y := by
    rw [transportedAverage_sub, purePart_sub, purePart_transportedAverage_linearPart, linearizedUnit]
    abel
  rw [e]
  refine (norm_add_le _ _).trans (add_le_add ?_ hω)
  exact (norm_purePart_le _).trans (norm_transportedAverage_le hodd _ _ c)
theorem norm_linearizedUnit_sub_one_le (hj : j + 1 ≤ F.top) {c : F.Site (j + 1) × Fin 4} (hσ : σ ≤ 1 / 64)
    (href : ∀ h ∈ centredCube F.blockSide, ∀ π, ‖ofUnit (pathHolonomy (A j) (refineSite c.1)
      (bondContour F.blockSide h π c.2) * (polarUnit (contourAverage (A j) c))⁻¹) - 1‖ ≤ σ)
    (hy : 8 * (F.blockSide : ℝ) * bondHullNorm c (levelDeviation A (realChart V) j) ≤ 1 / 1024)
    (hK : 200000 * (F.blockSide : ℝ) ^ 2 * (bondHullNorm c (levelDeviation A (realChart V) j) + σ) ≤ 1) :
    ‖linearizedUnit (A j) c (levelDeviation A (realChart V) j) - 1‖ ≤
      2 * bondHullNorm c (levelDeviation A (realChart V) j) := by
  set y := levelDeviation A (realChart V) j with hyd
  set N := bondHullNorm c y with hN
  have hN0 : 0 ≤ N := bondHullNorm_nonneg' c y
  have hω := (remainder_bounds hodd hj hσ hy href).2.1
  rw [← hN] at hω
  have e : linearizedUnit (A j) c y - 1 = purePart (transportedAverage (A j) y c) + unitRemainder (A j) c y := by
    rw [linearizedUnit]
    abel
  rw [e]
  refine (norm_add_le _ _).trans ?_
  have h1 : ‖purePart (transportedAverage (A j) y c)‖ ≤ N :=
    (norm_purePart_le _).trans ((norm_transportedAverage_le hodd _ _ c).trans
      (lineBlockAverage_le_bondHullSum hodd (fun _ _ => norm_nonneg _) c))
  have h2 : 200000 * (F.blockSide : ℝ) ^ 2 * (N ^ 2 + σ * N) =
      (200000 * (F.blockSide : ℝ) ^ 2 * (N + σ)) * N := by ring
  rw [h2] at hω
  have h3 := mul_le_mul_of_nonneg_right hK hN0
  linarith
theorem norm_levelDeviation_sub_linearPart_succ_le (hj : j + 1 < F.top) {c : F.Site (j + 1) × Fin 4}
    (hσ : σ ≤ 1 / 64)
    (href : ∀ h ∈ centredCube F.blockSide, ∀ π, ‖ofUnit (pathHolonomy (A j) (refineSite c.1)
      (bondContour F.blockSide h π c.2) * (polarUnit (contourAverage (A j) c))⁻¹) - 1‖ ≤ σ)
    (hy : 8 * (F.blockSide : ℝ) * bondHullNorm c (levelDeviation A (realChart V) j) ≤ 1 / 1024)
    (hK : 200000 * (F.blockSide : ℝ) ^ 2 * (bondHullNorm c (levelDeviation A (realChart V) j) + σ) ≤ 1)
    (hcoarse : ‖(V.coarse j c.1 c.2 : ℍ[ℝ])‖ ≤ 1) :
    ‖levelDeviation A (realChart V) (j + 1) c.1 c.2 - ofQuat (linearPart A V (j + 1) c.1 c.2)‖ ≤
      lineBlockAverage (fun x d => ‖levelDeviation A (realChart V) j x d - ofQuat (linearPart A V j x d)‖) c +
        (‖(V.coarse j c.1 c.2 : ℍ[ℝ])‖ ^ 2 +
          2 * ‖(V.coarse j c.1 c.2 : ℍ[ℝ])‖ * bondHullNorm c (levelDeviation A (realChart V) j) +
          4 * ‖((referenceDefect A j c : UnitQuaternion) : ℍ[ℝ]) - 1‖ *
            bondHullNorm c (levelDeviation A (realChart V) j) +
          200000 * (F.blockSide : ℝ) ^ 2 *
            (bondHullNorm c (levelDeviation A (realChart V) j) ^ 2 +
              σ * bondHullNorm c (levelDeviation A (realChart V) j))) := by
  have hj' : j + 1 ≤ F.top := hj.le
  have hdev := levelDeviation_succ_eq hodd hj' A (realChart V) (holdsOnHull_det_realChart A V c)
  have hlin := norm_linearizedUnit_sub_linearPart_le hodd A V hj' hσ href hy
  have hone := norm_linearizedUnit_sub_one_le hodd A V hj' hσ href hy hK
  set y := levelDeviation A (realChart V) j with hyd
  set N := bondHullNorm c y with hN
  set Pu := linearizedUnit (A j) c y with hPu
  set T := parallelAverage (A j) (linearPart A V j) c with hT
  set μ := referenceDefect A j c with hμ
  set x := V.coarse j c.1 c.2 with hx
  have hsrc : levelSource (realChart V) j c.1 c.2 = ofUnit (expUnit x) := levelSource_realChart V j c.1 c.2
  have hlinF : linearPart A V (j + 1) c.1 c.2 = T + (x : ℍ[ℝ]) := by
    simp only [linearPart]
    rw [if_pos hj]
  rw [hdev, hsrc, hlinF, ofQuat_add]
  set E := ofUnit (expUnit x) with hE
  set e := Pu - 1 with he
  have hPue : Pu = 1 + e := by rw [he]; abel
  have hAd : conjByUnit μ Pu = 1 + conjByUnit μ e := by rw [hPue, conjByUnit_add, conjByUnit_one]
  have ident : E * conjByUnit μ Pu - 1 - (ofQuat T + ofQuat (x : ℍ[ℝ])) =
      (E - 1 - ofQuat (x : ℍ[ℝ])) + (E - 1) * conjByUnit μ e + (conjByUnit μ e - e) + (e - ofQuat T) := by
    rw [hAd]
    noncomm_ring
  rw [ident]
  have n1 : ‖E - 1 - ofQuat (x : ℍ[ℝ])‖ ≤ ‖(x : ℍ[ℝ])‖ ^ 2 := norm_ofUnit_expUnit_sub_one_sub_le hcoarse
  have n2 : ‖(E - 1) * conjByUnit μ e‖ ≤ ‖(x : ℍ[ℝ])‖ * (2 * N) := by
    refine (norm_mul_le _ _).trans ?_
    rw [norm_conjByUnit]
    exact mul_le_mul (norm_ofUnit_expUnit_sub_one_le x) hone (norm_nonneg _) (norm_nonneg _)
  have n3 : ‖conjByUnit μ e - e‖ ≤ 2 * ‖(μ : ℍ[ℝ]) - 1‖ * (2 * N) :=
    (norm_conjByUnit_sub_le μ e).trans (mul_le_mul_of_nonneg_left hone (by positivity))
  calc _ ≤ ‖E - 1 - ofQuat (x : ℍ[ℝ])‖ + ‖(E - 1) * conjByUnit μ e‖ + ‖conjByUnit μ e - e‖ +
        ‖e - ofQuat T‖ := by
        refine (norm_add_le _ _).trans (add_le_add_left ?_ _)
        refine (norm_add_le _ _).trans (add_le_add_left ?_ _)
        exact norm_add_le _ _
    _ ≤ _ := by linarith
end Steps
theorem inv_pow_mul_pow_eq_one {L : ℝ} (hL : 1 ≤ L) (e : ℕ) : (1 / L) ^ e * L ^ e = 1 := by
  rw [← mul_pow, one_div, inv_mul_cancel₀ (by linarith), one_pow]
set_option maxHeartbeats 2000000 in
theorem weightedScaleNorm_levelDeviation_sub_linearPart_le (hodd : Odd F.blockSide) (h2 : 2 ≤ F.blockSide)
    {D : Finset F.Cell} (hD : D.card ≤ 81) (p : F.Site 0)
    {θ : ℝ} (hθ : |θ| ≤ 1 / 8) {A : F.FieldChain} {V : ChainChart F} {C₀ s T Bd Y : ℝ}
    (hC : 0 ≤ C₀) (hs : 0 ≤ s) (hnear : ContoursNearUnit A D C₀ s) (hσ : C₀ * s ≤ 1 / 64) (hT0 : 0 ≤ T)
    (hT1 : 200000 * (F.blockSide : ℝ) ^ 2 * (T + C₀ * s) ≤ 1) (hT2 : 8 * (F.blockSide : ℝ) * T ≤ 1 / 1024)
    (hT3 : T ≤ 1)
    (hμ : ∀ m, m + 1 < F.top → ∀ c ∈ innerBonds D (m + 1),
      ‖((referenceDefect A m c : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤
        C₀ * s * ((1 / (F.blockSide : ℝ)) ^ (F.top - (m + 1))) ^ 3)
    (hu : ∀ b ∈ innerBonds D 0, ‖(V.fine b.1 b.2 : ℍ[ℝ])‖ ≤ T)
    (hcoarse : ∀ m, m + 1 < F.top → ∀ c ∈ innerBonds D (m + 1), ‖(V.coarse m c.1 c.2 : ℍ[ℝ])‖ ≤ T)
    (hN : ∀ m, m < F.top → ∀ c ∈ innerBonds D (m + 1), bondHullNorm c (levelDeviation A (realChart V) m) ≤ T)
    (hBd : 0 ≤ Bd) (hY0 : 0 ≤ Y)
    (h0 : weightedScaleNorm D p θ 4 0 (fun x i => ‖(V.fine x i : ℍ[ℝ])‖) ≤ Bd)
    (h1 : ∀ m, m + 1 < F.top → weightedScaleNorm D p θ 2 (m + 1) (fun y d => ‖(V.coarse m y d : ℍ[ℝ])‖) ≤ Bd)
    (hY : ∀ m, m < F.top → weightedScaleNorm D p θ 4 m (fun z d => ‖levelDeviation A (realChart V) m z d‖) ≤ Y)
    (m : ℕ) (hm : m < F.top) :
    weightedScaleNorm D p θ 2 m
        (fun x d => ‖levelDeviation A (realChart V) m x d - ofQuat (linearPart A V m x d)‖) ≤
      142 * (5 * (F.blockSide : ℝ) ^ F.top * (T * Bd)) + 284 * (3 * T * Bd +
        5 * (4 + 200000 * (F.blockSide : ℝ) ^ 2) * (C₀ * s) * (hullFactor F.blockSide * Y) +
        5 * (200000 * (F.blockSide : ℝ) ^ 2) * T * (F.blockSide : ℝ) ^ F.top * (hullFactor F.blockSide * Y)) := by
  have hL1 : (1 : ℝ) ≤ F.blockSide := by exact_mod_cast hodd.pos
  have hF0 : 0 ≤ hullFactor F.blockSide := by
    obtain ⟨a, b, c⟩ := one_le_hullFactor_parts (F := F) hodd
    unfold hullFactor
    have : (0 : ℝ) ≤ hullBondCount F.blockSide := by linarith
    positivity
  set K := 200000 * (F.blockSide : ℝ) ^ 2 with hK
  have hK0 : 0 ≤ K := by positivity
  set Ln := (F.blockSide : ℝ) ^ F.top with hLn
  set a : (m : ℕ) → F.Site m → Fin 4 → ℝ :=
    fun m x d => ‖levelDeviation A (realChart V) m x d - ofQuat (linearPart A V m x d)‖ with ha
  set sf : (m : ℕ) → F.Site (m + 1) → Fin 4 → ℝ := fun m y d =>
    ‖(V.coarse m y d : ℍ[ℝ])‖ ^ 2 +
      2 * ‖(V.coarse m y d : ℍ[ℝ])‖ * bondHullNorm (y, d) (levelDeviation A (realChart V) m) +
      4 * ‖((referenceDefect A m (y, d) : UnitQuaternion) : ℍ[ℝ]) - 1‖ *
        bondHullNorm (y, d) (levelDeviation A (realChart V) m) +
      K * (bondHullNorm (y, d) (levelDeviation A (realChart V) m) ^ 2 +
        contourSpread F C₀ s m * bondHullNorm (y, d) (levelDeviation A (realChart V) m)) with hsf
  have hspread0 : ∀ m, 0 ≤ contourSpread F C₀ s m := by
    intro m
    unfold contourSpread
    positivity
  have ha0 : ∀ m x d, 0 ≤ a m x d := fun _ _ _ => norm_nonneg _
  have hs0 : ∀ m y d, 0 ≤ sf m y d := by
    intro m y d
    have h1 := bondHullNorm_nonneg' (y, d) (levelDeviation A (realChart V) m)
    have h3 := hspread0 m
    simp only [hsf]
    positivity
  have hrec : ∀ m, m + 1 < F.top → ∀ c ∈ innerBonds D (m + 1),
      a (m + 1) c.1 c.2 ≤ lineBlockAverage (a m) c + sf m c.1 c.2 := by
    intro m hm c hc
    have hNc := hN m (by omega) c hc
    have hsp := contourSpread_le hodd hC hs m
    refine norm_levelDeviation_sub_linearPart_succ_le hodd A V hm (σ := contourSpread F C₀ s m) (by linarith)
      (hnear m hm.le c hc) (by nlinarith) ?_ ((hcoarse m hm c hc).trans hT3)
    refine le_trans (mul_le_mul_of_nonneg_left (by linarith) hK0) hT1
  set B := 3 * T * Bd + 5 * (4 + K) * (C₀ * s) * (hullFactor F.blockSide * Y) +
    5 * K * T * Ln * (hullFactor F.blockSide * Y) with hB
  have hB0 : 0 ≤ B := by positivity
  have hBi : ∀ i, i + 1 ≤ m → weightedScaleNorm D p θ 2 (i + 1) (sf i) ≤ B := by
    intro i hi
    have hin : i + 1 < F.top := by omega
    set M := (F.blockSide : ℝ) ^ (F.top - (i + 1)) with hM
    set l := (1 / (F.blockSide : ℝ)) ^ (F.top - (i + 1)) with hl
    have hlM : l * M = 1 := inv_pow_mul_pow_eq_one hL1 _
    have hl0 : 0 ≤ l := by positivity
    have hl1 : l ≤ 1 := by
      rw [hl]
      exact pow_le_one₀ (by positivity) (by rw [one_div]; exact inv_le_one_of_one_le₀ hL1)
    have hMLn : M ≤ Ln := pow_le_pow_right₀ hL1 (by omega)
    set q : F.Site (i + 1) → Fin 4 → ℝ := fun y d => ‖(V.coarse i y d : ℍ[ℝ])‖ with hq
    set n : F.Site (i + 1) → Fin 4 → ℝ :=
      fun y d => bondHullNorm (y, d) (levelDeviation A (realChart V) i) with hn
    have hq0 : ∀ y d, 0 ≤ q y d := fun _ _ => norm_nonneg _
    have hn0 : ∀ y d, 0 ≤ n y d := fun _ _ => bondHullNorm_nonneg' _ _
    set G := 4 * (C₀ * s * l ^ 3) + K * T + K * (C₀ * s * l ^ 2) with hG
    have hG0 : 0 ≤ G := by positivity
    have hpt : weightedScaleNorm D p θ 2 (i + 1) (sf i) ≤
        1 * weightedScaleNorm D p θ 2 (i + 1) (fun y d => 3 * T * q y d + G * n y d) := by
      refine weightedScaleNorm_le_mul hodd p θ (by norm_num) (i + 1) (by norm_num) (fun c hc => ?_)
        (fun c _ => add_nonneg (mul_nonneg (by positivity) (hq0 _ _)) (mul_nonneg hG0 (hn0 _ _)))
      rw [abs_of_nonneg (hs0 _ _ _), one_mul]
      have e1 : bondHullNorm (c.1, c.2) (levelDeviation A (realChart V) i) = n c.1 c.2 := rfl
      have e2 : ‖(V.coarse i c.1 c.2 : ℍ[ℝ])‖ = q c.1 c.2 := rfl
      simp only [hsf, e1, e2]
      have b1 : q c.1 c.2 ≤ T := hcoarse i hin c hc
      have b2 : n c.1 c.2 ≤ T := hN i (by omega) c hc
      have b3 : ‖((referenceDefect A i (c.1, c.2) : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ C₀ * s * l ^ 3 :=
        hμ i hin c hc
      have b4 : contourSpread F C₀ s i = C₀ * s * l ^ 2 := rfl
      rw [b4]
      have q0 := hq0 c.1 c.2
      have n0 := hn0 c.1 c.2
      have c1 : q c.1 c.2 ^ 2 ≤ T * q c.1 c.2 := by nlinarith
      have c2 : 2 * q c.1 c.2 * n c.1 c.2 ≤ 2 * T * q c.1 c.2 := by nlinarith
      have c3 : 4 * ‖((referenceDefect A i (c.1, c.2) : UnitQuaternion) : ℍ[ℝ]) - 1‖ * n c.1 c.2 ≤
          4 * (C₀ * s * l ^ 3) * n c.1 c.2 := by
        have := mul_le_mul_of_nonneg_right b3 n0
        nlinarith
      have c4 : K * (n c.1 c.2 ^ 2 + C₀ * s * l ^ 2 * n c.1 c.2) ≤
          K * T * n c.1 c.2 + K * (C₀ * s * l ^ 2) * n c.1 c.2 := by
        have : n c.1 c.2 ^ 2 ≤ T * n c.1 c.2 := by nlinarith
        have := mul_le_mul_of_nonneg_left this hK0
        nlinarith
      simp only [hG]
      nlinarith
    have hadd := weightedScaleNorm_add_le D p θ (P := 2) (by norm_num) (i + 1) (fun y d => 3 * T * q y d)
      (fun y d => G * n y d)
    have hA : weightedScaleNorm D p θ 2 (i + 1) (fun y d => 3 * T * q y d) ≤ 3 * T * Bd := by
      refine le_trans (weightedScaleNorm_le_mul hodd p θ (by norm_num) (i + 1) (κ := 3 * T) (by positivity)
        (fun c _ => ?_) (fun c _ => hq0 _ _)) (mul_le_mul_of_nonneg_left (h1 i hin) (by positivity))
      rw [abs_of_nonneg (mul_nonneg (by positivity) (hq0 _ _))]
    have hnl : weightedScaleNorm D p θ 2 (i + 1) n ≤ 5 * M * (hullFactor F.blockSide * Y) := by
      refine (weightedScaleNorm_two_le_four hodd hD p θ (i + 1) n).trans
        (mul_le_mul_of_nonneg_left ?_ (by positivity))
      refine (weightedScaleNorm_bondHullSum_le hodd hθ (by omega) p 4 (by norm_num)
        (g := fun z d => ‖levelDeviation A (realChart V) i z d‖) (fun _ _ => norm_nonneg _)).trans ?_
      exact mul_le_mul_of_nonneg_left (hY i (by omega)) hF0
    have hBn : weightedScaleNorm D p θ 2 (i + 1) (fun y d => G * n y d) ≤
        G * (5 * M * (hullFactor F.blockSide * Y)) := by
      refine le_trans (weightedScaleNorm_le_mul hodd p θ (by norm_num) (i + 1) (κ := G) hG0
        (fun c _ => ?_) (fun c _ => hn0 _ _)) (mul_le_mul_of_nonneg_left hnl hG0)
      rw [abs_of_nonneg (mul_nonneg hG0 (hn0 _ _))]
    have hZ : 0 ≤ hullFactor F.blockSide * Y := by positivity
    set Z := hullFactor F.blockSide * Y with hZd
    have hGM : G * (5 * M * Z) ≤ 5 * (4 + K) * (C₀ * s) * Z + 5 * K * T * Ln * Z := by
      have e1 : l ^ 3 * M ≤ 1 := by
        have : l ^ 3 * M = l ^ 2 * (l * M) := by ring
        rw [this, hlM, mul_one]
        exact pow_le_one₀ hl0 hl1
      have e2 : l ^ 2 * M ≤ 1 := by
        have : l ^ 2 * M = l * (l * M) := by ring
        rw [this, hlM, mul_one]
        exact hl1
      have hCs : 0 ≤ C₀ * s := by positivity
      have t1 : 4 * (C₀ * s * l ^ 3) * (5 * M * Z) ≤ 20 * (C₀ * s) * Z := by
        have := mul_le_mul_of_nonneg_left e1 (mul_nonneg hCs hZ)
        nlinarith
      have t2 : K * T * (5 * M * Z) ≤ 5 * K * T * Ln * Z := by
        have := mul_le_mul_of_nonneg_left hMLn (mul_nonneg (mul_nonneg hK0 hT0) hZ)
        nlinarith
      have t3 : K * (C₀ * s * l ^ 2) * (5 * M * Z) ≤ 5 * K * (C₀ * s) * Z := by
        have := mul_le_mul_of_nonneg_left e2 (mul_nonneg (mul_nonneg hK0 hCs) hZ)
        nlinarith
      simp only [hG]
      nlinarith
    simp only [hB]
    linarith
  have hw := (weightedScaleNorm_le_of_recursion hodd h2 D p hθ a sf ha0 hs0 hrec m hBi hB0 hm).2
  have h00 : weightedScaleNorm D p θ 2 0 (a 0) ≤ 5 * Ln * (T * Bd) := by
    have e : (F.blockSide : ℝ) ^ (F.top - 0) = Ln := by simp [hLn]
    have s1 := weightedScaleNorm_two_le_four hodd hD p θ 0 (a 0)
    rw [e] at s1
    refine s1.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    refine le_trans (weightedScaleNorm_le_mul hodd p θ (by norm_num) 0 (κ := T) hT0 (fun b hb => ?_)
      (fun c _ => norm_nonneg _)) (mul_le_mul_of_nonneg_left h0 hT0)
    rw [abs_of_nonneg (ha0 _ _ _)]
    have hb1 := hu b hb
    simp only [ha, levelDeviation_zero_realChart]
    refine (norm_ofUnit_expUnit_sub_one_sub_le (hb1.trans hT3)).trans ?_
    have := norm_nonneg (V.fine b.1 b.2 : ℍ[ℝ])
    nlinarith
  have := mul_le_mul_of_nonneg_left h00 (by norm_num : (0 : ℝ) ≤ 142)
  simp only [hB] at hw
  linarith
end YangMills.Construction.LinearLevels
end
