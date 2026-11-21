import YangMills.Construction.ConfigurationSpace.DiagonalCutoffBounds
import YangMills.Construction.ConfigurationSpace.MinSeparationProperties
import YangMills.Construction.ConfigurationSpace.NearDiagonalPoint
import YangMills.Construction.ConfigurationSpace.ShellCenterCountProof
import YangMills.Construction.ConfigurationSpace.WhitneyPieceSupport
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ConfigurationSpace.CubeBoxes
open YangMills.Construction.BumpFunctions YangMills.Construction.ConfigurationSpace YangMills.Construction.WhitneyScales
section Norms
variable {I : Type*} [Fintype I]
theorem abs_le_maxNorm (x : I → ℝ) (ι : I) : |x ι| ≤ maxNorm x :=
  le_ciSup (f := fun ι => |x ι|) (Set.finite_range _).bddAbove ι
theorem maxNorm_le_l2Norm (x : I → ℝ) : maxNorm x ≤ l2Norm x := by
  refine Real.iSup_le (fun ι => ?_) (Real.sqrt_nonneg _)
  refine Real.abs_le_sqrt ?_
  exact Finset.single_le_sum (f := fun ι => x ι ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ ι)
theorem l2Norm_le_of_abs_le {x : I → ℝ} {c : ℝ} (hc : 0 ≤ c) (h : ∀ ι, |x ι| ≤ c) :
    l2Norm x ≤ Real.sqrt (Fintype.card I) * c := by
  have hsum : ∑ ι, x ι ^ 2 ≤ (Fintype.card I : ℝ) * c ^ 2 := by
    calc ∑ ι, x ι ^ 2 ≤ ∑ _ι : I, c ^ 2 := Finset.sum_le_sum fun ι _ => by
          rw [← sq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) (h ι) 2
      _ = (Fintype.card I : ℝ) * c ^ 2 := by simp
  calc l2Norm x ≤ Real.sqrt ((Fintype.card I : ℝ) * c ^ 2) := Real.sqrt_le_sqrt hsum
    _ = Real.sqrt (Fintype.card I) * c := by
      rw [Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq hc]
end Norms
variable {n : ℕ}
theorem configNorm_add_le (a b : Config n) : configNorm (a + b) ≤ configNorm a + configNorm b := by apply _root_.YangMills.Construction.ConfigurationSpace.ShellCount.configNorm_add_le <;> assumption
theorem configNorm_nonneg (a : Config n) : 0 ≤ configNorm a := Real.sqrt_nonneg _
theorem one_add_configNorm_le (w w' : Config n) :
    1 + configNorm w ≤ (1 + configNorm (w - w')) * (1 + configNorm w') := by
  have h := configNorm_add_le (w - w') w'
  rw [sub_add_cancel] at h
  nlinarith [configNorm_nonneg (w - w'), configNorm_nonneg w',
    mul_nonneg (configNorm_nonneg (w - w')) (configNorm_nonneg w')]
theorem scale_pos (j : ℕ) : 0 < whitneyScale j := by apply _root_.YangMills.Construction.ConfigurationSpace.ShellCount.scale_pos <;> assumption
theorem scale_le_one (j : ℕ) : whitneyScale j ≤ 1 := by
  unfold whitneyScale
  rw [zpow_neg, zpow_natCast]
  exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
theorem side_pos (j : ℕ) : 0 < whitneySide j :=
  mul_pos isWhitneyRatio_whitneyRatio.1 (scale_pos j)
theorem six_mul_side_le_scale (j : ℕ) : 6 * whitneySide j ≤ whitneyScale j := by
  have h := isWhitneyRatio_whitneyRatio.2
  have hs := scale_pos j
  unfold whitneySide
  nlinarith
theorem minSeparation_le_of_ne (x : Config n) {i i' : Fin n} (h : i ≠ i') :
    minSeparation x ≤ ENNReal.ofReal (maxNorm (x i - x i')) := by
  rcases lt_or_gt_of_ne h with h | h
  · exact iInf₂_le (f := fun (p : Fin n × Fin n) (_ : p ∈ orderedPairs n) =>
      ENNReal.ofReal (maxNorm (x p.1 - x p.2))) (i, i') (by simp [orderedPairs, h])
  · have hsymm : maxNorm (x i - x i') = maxNorm (x i' - x i) := by
      unfold maxNorm
      congr 1
      funext c
      simp only [Pi.sub_apply]
      exact abs_sub_comm _ _
    rw [hsymm]
    exact iInf₂_le (f := fun (p : Fin n × Fin n) (_ : p ∈ orderedPairs n) =>
      ENNReal.ofReal (maxNorm (x p.1 - x p.2))) (i', i) (by simp [orderedPairs, h])
theorem abs_sub_center_le_of_piece_ne_zero
    (hSupp : WhitneyPieceSupportProperties)
    (hn : 1 ≤ n) {j : ℕ} {z : IntPoint n} {x : Config n} (h : whitneyPiece j z x ≠ 0)
    (i : Fin n) (c : Fin 4) : |x i c - pieceCenter j z i c| ≤ 3 / 8 * whitneySide j := by
  obtain ⟨-, -, hsup, -⟩ := hSupp n hn j z
  have hx : x ∈ tsupport (whitneyPiece j z) := subset_tsupport _ (Function.mem_support.2 h)
  obtain ⟨w, hw, rfl⟩ := hsup hx
  have h1 : w i c ∈ Set.Icc (-(3 / 8 * whitneySide j)) (3 / 8 * whitneySide j) := hw (toLex (i, c))
  have h2 : (pieceCenter j z + w) i c - pieceCenter j z i c = w i c := by simp
  rw [h2, abs_le]
  exact h1
theorem abs_sub_center_lt_of_mem_pieceBox {j : ℕ} {z : IntPoint n} {x : Config n}
    (hx : x ∈ pieceBox j z) (i : Fin n) (c : Fin 4) :
    |x i c - pieceCenter j z i c| < 1 / 2 * whitneySide j := by
  obtain ⟨w, hw, rfl⟩ := hx
  have h1 : w i c ∈ Set.Ioo (-(1 / 2 * whitneySide j)) (1 / 2 * whitneySide j) := hw (toLex (i, c))
  have h2 : (pieceCenter j z + w) i c - pieceCenter j z i c = w i c := by simp
  rw [h2, abs_lt]
  exact h1
theorem configNorm_sub_center_le {j : ℕ} {z : IntPoint n} {x : Config n}
    (hx : x ∈ pieceBox j z) : configNorm (x - pieceCenter j z) ≤ Real.sqrt n := by
  have hu := side_pos j
  have hu1 : whitneySide j ≤ 1 := by
    have := six_mul_side_le_scale j
    have := scale_le_one j
    linarith
  have hb : ∀ ι, |coords (x - pieceCenter j z) ι| ≤ 1 / 2 * whitneySide j := fun ι =>
    (abs_sub_center_lt_of_mem_pieceBox hx (ofLex ι).1 (ofLex ι).2).le
  have hcard : Fintype.card (CoordIndex n) = n * 4 := by
    simp [CoordIndex]
  have h := l2Norm_le_of_abs_le (by positivity) hb
  rw [hcard] at h
  have hsq : Real.sqrt ((n * 4 : ℕ) : ℝ) = Real.sqrt n * 2 := by
    have : ((n * 4 : ℕ) : ℝ) = (n : ℝ) * 2 ^ 2 := by push_cast; ring
    rw [this, Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq (by norm_num)]
  rw [hsq] at h
  have hn0 := Real.sqrt_nonneg (n : ℝ)
  calc configNorm (x - pieceCenter j z) ≤ Real.sqrt n * 2 * (1 / 2 * whitneySide j) := h
    _ = Real.sqrt n * whitneySide j := by ring
    _ ≤ Real.sqrt n * 1 := mul_le_mul_of_nonneg_left hu1 hn0
    _ = Real.sqrt n := mul_one _
theorem configNorm_sub_comm (a b : Config n) : configNorm (a - b) = configNorm (b - a) := by
  unfold configNorm l2Norm
  congr 1
  refine Finset.sum_congr rfl fun ι _ => ?_
  simp only [coords, Pi.sub_apply]
  ring
theorem setDist_outerCube_ge
    (hSupp : WhitneyPieceSupportProperties)
    (hn : 1 ≤ n) {j : ℕ} {z : IntPoint n} {x : Config n} (h : whitneyPiece j z x ≠ 0)
    (hsep : ENNReal.ofReal (whitneyScale j) < minSeparation x) {i i' : Fin n} (hii : i ≠ i') :
    ENNReal.ofReal (whitneyScale j / 2) ≤
      YangMills.Construction.TestFunctions.setDistR4 (outerCube j z i) (outerCube j z i') := by
  have hs := scale_pos j
  have hu := side_pos j
  have h6 := six_mul_side_le_scale j
  have hlt : whitneyScale j < maxNorm (x i - x i') :=
    (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hs.le).1
      (lt_of_lt_of_le hsep (minSeparation_le_of_ne x hii))
  refine le_iInf₂ fun a ha => le_iInf₂ fun b hb => ENNReal.ofReal_le_ofReal ?_
  have ha' : ∀ c, |a c - pieceCenter j z i c| ≤ whitneySide j := fun c => by
    have h1 := abs_le_maxNorm (a - pieceCenter j z i) c
    have h2 : maxNorm (a - pieceCenter j z i) ≤ 2 * whitneySide j / 2 := ha
    simp only [Pi.sub_apply] at h1
    linarith
  have hb' : ∀ c, |b c - pieceCenter j z i' c| ≤ whitneySide j := fun c => by
    have h1 := abs_le_maxNorm (b - pieceCenter j z i') c
    have h2 : maxNorm (b - pieceCenter j z i') ≤ 2 * whitneySide j / 2 := hb
    simp only [Pi.sub_apply] at h1
    linarith
  have hbound : maxNorm (x i - x i') ≤ maxNorm (a - b) + 3 * whitneySide j := by
    refine Real.iSup_le (fun c => ?_) (add_nonneg ?_ (by positivity))
    · have e1 := abs_sub_center_le_of_piece_ne_zero hSupp hn h i c
      have e2 := abs_sub_center_le_of_piece_ne_zero hSupp hn h i' c
      have e3 := ha' c
      have e4 := hb' c
      have e5 := abs_le_maxNorm (a - b) c
      simp only [Pi.sub_apply] at e5 ⊢
      rw [abs_le] at e1 e2 e3 e4 e5 ⊢
      constructor <;> linarith [e1.1, e1.2, e2.1, e2.2, e3.1, e3.2, e4.1, e4.2, e5.1, e5.2]
    · exact (abs_nonneg _).trans (abs_le_maxNorm (a - b) 0)
  have hfin : maxNorm (a - b) ≤ YangMills.Construction.TorusMetric.euclidNormVec (a - b) :=
    maxNorm_le_l2Norm (a - b)
  linarith
theorem pieceBox_near_fatDiagonal
    (hSupp : WhitneyPieceSupportProperties)
    (hMin : MinSeparationProperties) (hMid : ExistsNearDiagonalPoint)
    (hn : 2 ≤ n) {j : ℕ} {z : IntPoint n} {x₀ x : Config n}
    (h : whitneyPiece j z x₀ ≠ 0)
    (hsep : minSeparation x₀ < ENNReal.ofReal (4 * whitneyScale j)) (hx : x ∈ pieceBox j z) :
    minSeparation x ≤ ENNReal.ofReal (separationConst * whitneyScale j) ∧
      ∃ y ∈ fatDiagonal n, configNorm (x - y) ≤ diagonalDistConst * whitneyScale j := by
  have hu := side_pos j
  obtain ⟨hTop, hLip, -⟩ := (hMin.1 n hn).1
  have hclose : configMaxNorm (x - x₀) ≤ whitneySide j := by
    refine Real.iSup_le (fun ι => ?_) hu.le
    have e1 := abs_sub_center_lt_of_mem_pieceBox hx (ofLex ι).1 (ofLex ι).2
    have e2 := abs_sub_center_le_of_piece_ne_zero hSupp (by omega) h (ofLex ι).1 (ofLex ι).2
    simp only [coords, Pi.sub_apply]
    rw [abs_lt] at e1
    rw [abs_le] at e2 ⊢
    constructor <;> linarith [e1.1, e1.2, e2.1, e2.2]
  have hx₀ : (minSeparation x₀).toReal < 4 * whitneyScale j :=
    ENNReal.toReal_lt_of_lt_ofReal hsep
  have hbound : (minSeparation x).toReal ≤ separationConst * whitneyScale j := by
    have h1 := (abs_le.1 (hLip x x₀)).2
    have h2 : separationConst * whitneyScale j = 4 * whitneyScale j + 2 * whitneySide j := by
      unfold separationConst whitneySide
      ring
    linarith
  have hCm : 0 ≤ separationConst * whitneyScale j :=
    ENNReal.toReal_nonneg.trans hbound
  have hle : minSeparation x ≤ ENNReal.ofReal (separationConst * whitneyScale j) :=
    (ENNReal.le_ofReal_iff_toReal_le (hTop x) hCm).2 hbound
  refine ⟨hle, ?_⟩
  obtain ⟨y, hy, hxy⟩ := hMid n hn x
  refine ⟨y, hy, ?_⟩
  have hprod : ENNReal.ofReal (Real.sqrt 2) * minSeparation x ≤
      ENNReal.ofReal (diagonalDistConst * whitneyScale j) := by
    have e : diagonalDistConst * whitneyScale j =
        Real.sqrt 2 * (separationConst * whitneyScale j) := by
      unfold diagonalDistConst
      ring
    rw [e, ENNReal.ofReal_mul (Real.sqrt_nonneg 2)]
    gcongr
  have hnonneg : 0 ≤ diagonalDistConst * whitneyScale j := by
    have e : diagonalDistConst * whitneyScale j =
        Real.sqrt 2 * (separationConst * whitneyScale j) := by
      unfold diagonalDistConst
      ring
    rw [e]
    exact mul_nonneg (Real.sqrt_nonneg 2) hCm
  exact (ENNReal.ofReal_le_ofReal_iff hnonneg).1 (hxy.trans hprod)
theorem shellDiff_of_one (j : ℕ) (hj : 1 ≤ j) (x : Config 1) : shellDiff j x = 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  simp [shellDiff, pairCutoffProd_one]
theorem whitneyCubeBoxBounds_holds (hShell : DiagonalCutoffProperties)
    (hMin : MinSeparationProperties) (hMid : ExistsNearDiagonalPoint)
    (hSupp : WhitneyPieceSupportProperties) :
    WhitneyCubeBoxBounds := by
  rintro n hn ⟨j, z⟩ ⟨x₀, hx₀⟩
  have hx₀' : whitneyPiece j z x₀ ≠ 0 := hx₀
  have hshell : shellDiff j x₀ ≠ 0 := left_ne_zero_of_mul hx₀'
  obtain ⟨-, -, hfacts⟩ := hShell n hn j
  obtain ⟨-, -, -, hlow, hhigh, -⟩ := hfacts
  have hu := side_pos j
  refine ⟨fun i y hy => ?_, ?_, fun i i' hii => ?_, fun hj x hx => ?_, fun x hx => ?_⟩
  · have hb : ∀ c, |(y - pieceCenter j z i) c| ≤ whitneySide j := fun c => by
      have h1 := abs_le_maxNorm (y - pieceCenter j z i) c
      have h2 : maxNorm (y - pieceCenter j z i) ≤ 2 * whitneySide j / 2 := hy
      linarith
    have h := l2Norm_le_of_abs_le hu.le hb
    have h4 : Real.sqrt (Fintype.card (Fin 4)) = 2 := by
      have : ((Fintype.card (Fin 4) : ℕ) : ℝ) = 2 ^ 2 := by norm_num
      rw [this, Real.sqrt_sq (by norm_num)]
    rw [h4] at h
    exact h
  · have := six_mul_side_le_scale j
    have := scale_le_one j
    show 2 * whitneySide j ≤ 1
    linarith
  · exact setDist_outerCube_ge hSupp hn hx₀' (hlow x₀ hshell) hii
  · have hj' : 1 ≤ j := hj
    rcases Nat.lt_or_ge n 2 with h2 | h2
    · obtain rfl : n = 1 := by omega
      exact absurd (shellDiff_of_one j hj' x₀) hshell
    · exact pieceBox_near_fatDiagonal hSupp hMin hMid h2 hx₀' (hhigh x₀ hshell hj') hx
  · have hd := configNorm_sub_center_le hx
    have hn0 := Real.sqrt_nonneg (n : ℝ)
    have w1 := one_add_configNorm_le (pieceCenter j z) x
    have w2 := one_add_configNorm_le x (pieceCenter j z)
    rw [configNorm_sub_comm] at w1
    have hx1 : 0 ≤ 1 + configNorm x := by linarith [configNorm_nonneg x]
    have hc1 : 0 ≤ 1 + configNorm (pieceCenter j z) := by
      linarith [configNorm_nonneg (pieceCenter j z)]
    refine ⟨hd, ?_, ?_⟩
    · exact w1.trans (mul_le_mul_of_nonneg_right (by linarith) hx1)
    · exact w2.trans (mul_le_mul_of_nonneg_right (by linarith) hc1)
end YangMills.Construction.ConfigurationSpace.CubeBoxes
end
