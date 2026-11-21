import YangMills.Construction.Continuum.OneSpaceOfTestFunctionsFlatTensorsAndTheDualProof
import YangMills.Construction.ConfigurationSpace.CenterCountByVolume
import YangMills.Construction.ConfigurationSpace.DiagonalTubeVolume
import YangMills.Construction.ConfigurationSpace.ShellCenterCount
import YangMills.Construction.ConfigurationSpace.TupleEuclideanBallVolume
import YangMills.Construction.ConfigurationSpace.WhitneyCubeBoxBounds
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ConfigurationSpace.ShellCount
open YangMills.Construction.ConfigurationSpace YangMills.Construction.WhitneyScales MeasureTheory
open scoped ENNReal
theorem configNorm_eq_sqrt_sum {n : ℕ} (x : Config n) :
    configNorm x = Real.sqrt (∑ a, ∑ c, x a c ^ 2) := by apply _root_.YangMills.Construction.Continuum.UnifiedTestSpace.ptNorm_eq_tupleNorm <;> assumption
theorem configNorm_add_le {n : ℕ} (x y : Config n) :
    configNorm (x + y) ≤ configNorm x + configNorm y := by
  have hnorm : ∀ w : Config n, configNorm w =
      ‖(WithLp.toLp 2 (coords w) : EuclideanSpace ℝ (CoordIndex n))‖ := by
    intro w
    simp [configNorm, l2Norm, EuclideanSpace.norm_eq]
  have hsum : (WithLp.toLp 2 (coords (x + y)) : EuclideanSpace ℝ (CoordIndex n)) =
      WithLp.toLp 2 (coords x) + WithLp.toLp 2 (coords y) := rfl
  rw [hnorm, hnorm, hnorm, hsum]
  exact norm_add_le _ _
theorem side_pos (j : ℕ) : 0 < whitneySide j :=
  mul_pos isWhitneyRatio_whitneyRatio.1 (zpow_pos (by norm_num) _)
theorem scale_pos (j : ℕ) : 0 < whitneyScale j :=
  zpow_pos (by norm_num) _
theorem mem_pieceBox_of_mem_quarterBox {n j : ℕ} {z : IntPoint n} {x : Config n}
    (hx : x ∈ translateSet (pieceCenter j z)
      {x | ∀ ι, coords x ι ∈ Set.Ioo (-(1 / 4 * whitneySide j)) (1 / 4 * whitneySide j)}) :
    x ∈ pieceBox j z := by
  obtain ⟨w, hw, rfl⟩ := hx
  refine ⟨w, fun ι => ?_, rfl⟩
  have hu := side_pos j
  have hι := hw ι
  exact ⟨by linarith [hι.1], by linarith [hι.2]⟩
theorem configNorm_le_of_mem_pieceBox (hCubes : WhitneyCubeBoxBounds)
    {n j t : ℕ} (hn : 1 ≤ n) {z : IntPoint n} (hz : (j, z) ∈ pieceIndexSet n)
    (ht : configNorm (pieceCenter j z) < t + 1) {x : Config n} (hx : x ∈ pieceBox j z) :
    configNorm x ≤ (1 + Real.sqrt n) * (t + 1) := by
  have h1 : configNorm (x - pieceCenter j z) ≤ Real.sqrt n :=
    ((hCubes n hn (j, z) hz).2.2.2.2 x hx).1
  have h2 : configNorm x ≤ configNorm (x - pieceCenter j z) + configNorm (pieceCenter j z) := by
    simpa using configNorm_add_le (x - pieceCenter j z) (pieceCenter j z)
  have h3 : 0 ≤ Real.sqrt n * t := mul_nonneg (Real.sqrt_nonneg _) (Nat.cast_nonneg _)
  nlinarith
theorem exists_pair_of_minSeparation_le {n : ℕ} {x : Config n} {r : ℝ} (hr : 0 ≤ r)
    (h : minSeparation x ≤ ENNReal.ofReal r) :
    ∃ p ∈ orderedPairs n, maxNorm (x p.1 - x p.2) ≤ r := by
  rcases (orderedPairs n).eq_empty_or_nonempty with h0 | hne
  · simp [minSeparation, h0] at h
  · obtain ⟨p, hp, hmin⟩ := Finset.exists_min_image (orderedPairs n)
      (fun p => maxNorm (x p.1 - x p.2)) hne
    refine ⟨p, hp, ?_⟩
    have hle : ENNReal.ofReal (maxNorm (x p.1 - x p.2)) ≤ minSeparation x :=
      le_iInf₂ fun q hq => ENNReal.ofReal_le_ofReal (hmin q hq)
    exact (ENNReal.ofReal_le_ofReal_iff hr).1 (hle.trans h)
theorem unitBallVol_nonneg (D : ℕ) : 0 ≤ unitBallVol D := by
  cases D with
  | zero => norm_num [unitBallVol]
  | succ D => exact ENNReal.toReal_nonneg
theorem one_le_two_mul_separationConst : 1 ≤ 2 * separationConst := by
  have := isWhitneyRatio_whitneyRatio.1
  unfold separationConst
  linarith
theorem constants_le_scale_zero (n : ℕ) {A D B T v M : ℝ} (hA : 1 ≤ A) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hT : 0 ≤ T) (hv : 0 ≤ v) (hvM : v ≤ M) :
    D ^ (4 * n) * (v * (B * T) ^ (4 * n)) ≤
      (A ^ 4 * D ^ 4) ^ n * B ^ (4 * n) * M * T ^ (4 * n) := by
  have e : (A ^ 4 * D ^ 4) ^ n = A ^ (4 * n) * D ^ (4 * n) := by
    rw [mul_pow, ← pow_mul, ← pow_mul]
  have a1 : 1 ≤ A ^ (4 * n) := one_le_pow₀ hA
  rw [e, mul_pow]
  calc D ^ (4 * n) * (v * (B ^ (4 * n) * T ^ (4 * n)))
      = 1 * (D ^ (4 * n) * (B ^ (4 * n) * (v * T ^ (4 * n)))) := by ring
    _ ≤ A ^ (4 * n) * (D ^ (4 * n) * (B ^ (4 * n) * (M * T ^ (4 * n)))) := by gcongr
    _ = _ := by ring
theorem constants_le_scale_pos (m : ℕ) {A D B T s Q M : ℝ} (hA : 1 ≤ A) (hB : 1 ≤ B)
    (hD : 0 < D) (hT : 0 ≤ T) (hs : 0 < s) (hQ : 0 ≤ Q) (hQM : Q ≤ M) :
    (D / s) ^ (4 * (m + 1)) * ((A * s) ^ 4 * Q * (B * T) ^ (4 * m)) ≤
      (A ^ 4 * D ^ 4) ^ (m + 1) * B ^ (4 * (m + 1)) * M * T ^ (4 * m) *
        s ^ (4 - 4 * ((m + 1 : ℕ) : ℤ)) := by
  have hz : s ^ (4 - 4 * ((m + 1 : ℕ) : ℤ)) = (s ^ (4 * m))⁻¹ := by
    have h : (4 - 4 * ((m + 1 : ℕ) : ℤ)) = -((4 * m : ℕ) : ℤ) := by
      push_cast
      ring
    rw [h, zpow_neg, zpow_natCast]
  have h1 : (D / s) ^ (4 * (m + 1)) * (A * s) ^ 4 = D ^ (4 * m + 4) * A ^ 4 * (s ^ (4 * m))⁻¹ := by
    have hs' : s ^ (4 * m) ≠ 0 := pow_ne_zero _ hs.ne'
    rw [div_pow, mul_pow, show 4 * (m + 1) = 4 * m + 4 by ring, pow_add s]
    field_simp
  have e : (A ^ 4 * D ^ 4) ^ (m + 1) = A ^ (4 * m + 4) * D ^ (4 * m + 4) := by
    rw [mul_pow, ← pow_mul, ← pow_mul, show 4 * (m + 1) = 4 * m + 4 by ring]
  have a1 : A ^ 4 ≤ A ^ (4 * m + 4) := pow_le_pow_right₀ hA (by omega)
  have b1 : B ^ (4 * m) ≤ B ^ (4 * (m + 1)) := pow_le_pow_right₀ hB (by omega)
  have hK : 0 ≤ (s ^ (4 * m))⁻¹ := inv_nonneg.2 (pow_nonneg hs.le _)
  rw [hz, e, show (D / s) ^ (4 * (m + 1)) * ((A * s) ^ 4 * Q * (B * T) ^ (4 * m)) =
    (D / s) ^ (4 * (m + 1)) * (A * s) ^ 4 * Q * (B * T) ^ (4 * m) by ring, h1, mul_pow]
  generalize (s ^ (4 * m))⁻¹ = K at hK
  calc D ^ (4 * m + 4) * A ^ 4 * K * Q * (B ^ (4 * m) * T ^ (4 * m))
      = D ^ (4 * m + 4) * (A ^ 4 * (B ^ (4 * m) * (Q * (T ^ (4 * m) * K)))) := by ring
    _ ≤ D ^ (4 * m + 4) * (A ^ (4 * m + 4) * (B ^ (4 * (m + 1)) * (M * (T ^ (4 * m) * K)))) := by
        gcongr
    _ = _ := by ring
theorem card_shell_centers_scale_zero (hCount : CenterCountByVolume)
    (hBall : TupleEuclideanBallVolume)
    (hCubes : WhitneyCubeBoxBounds) {n : ℕ} (hn : 1 ≤ n) (t : ℕ) :
    (setCard {z : IntPoint n | (0, z) ∈ pieceIndexSet n ∧
        (t : ℝ) ≤ configNorm (pieceCenter 0 z) ∧ configNorm (pieceCenter 0 z) < t + 1} : ℝ≥0∞) ≤
      ENNReal.ofReal (pieceCountConst n * (1 + (t : ℝ)) ^ (4 * n)) := by
  have hB1 : 1 ≤ 1 + Real.sqrt n := by linarith [Real.sqrt_nonneg (n : ℝ)]
  have hR : 0 < (1 + Real.sqrt n) * ((t : ℝ) + 1) := by positivity
  have hc : 0 < whitneyRatio := isWhitneyRatio_whitneyRatio.1
  have hside : whitneySide 0 = whitneyRatio := by simp [whitneySide, whitneyScale]
  have hsub := hCount n 0 {z : IntPoint n | (0, z) ∈ pieceIndexSet n ∧
      (t : ℝ) ≤ configNorm (pieceCenter 0 z) ∧ configNorm (pieceCenter 0 z) < t + 1}
    {x | configNorm x ≤ (1 + Real.sqrt n) * (t + 1)}
    (fun z hz x hx => configNorm_le_of_mem_pieceBox hCubes hn hz.1 hz.2.2
      (mem_pieceBox_of_mem_quarterBox hx))
  have hvol : volume {x : Config n | configNorm x ≤ (1 + Real.sqrt n) * (t + 1)} =
      ENNReal.ofReal (unitBallVol (4 * n) * ((1 + Real.sqrt n) * (t + 1)) ^ (4 * n)) := by
    have h := hBall (Fin n) (by simpa using hn) _ hR
    simp only [Fintype.card_fin] at h
    rw [← h]
    congr 1
    ext x
    simp only [Set.mem_ofPred_eq, configNorm_eq_sqrt_sum]
  rw [hvol] at hsub
  refine hsub.trans ?_
  have hD : 0 ≤ (2 / whitneySide 0) ^ (4 * n) := by rw [hside]; positivity
  rw [← ENNReal.ofReal_mul hD]
  apply ENNReal.ofReal_le_ofReal
  rw [hside, add_comm (1 : ℝ) (t : ℝ)]
  have hv := unitBallVol_nonneg (4 * n)
  have := constants_le_scale_zero n (A := 2 * separationConst) (D := 2 / whitneyRatio)
    (B := 1 + Real.sqrt n) (T := (t : ℝ) + 1) (v := unitBallVol (4 * n))
    (M := max (choose2Real n * unitBallVol (4 * n - 4)) (unitBallVol (4 * n)))
    one_le_two_mul_separationConst (by linarith) (by positivity) (by linarith) hv (le_max_right _ _)
  simpa [pieceCountConst, countingVolConst] using this
theorem card_shell_centers_scale_pos (hCount : CenterCountByVolume)
    (hTube : DiagonalTubeVolumeBound)
    (hCubes : WhitneyCubeBoxBounds) (m j t : ℕ) (hj : 1 ≤ j) :
    (setCard {z : IntPoint (m + 1) | (j, z) ∈ pieceIndexSet (m + 1) ∧
        (t : ℝ) ≤ configNorm (pieceCenter j z) ∧ configNorm (pieceCenter j z) < t + 1} : ℝ≥0∞) ≤
      ENNReal.ofReal (pieceCountConst (m + 1) * (1 + (t : ℝ)) ^ (4 * (m + 1) - 4) *
        whitneyScale j ^ (4 - 4 * ((m + 1 : ℕ) : ℤ))) := by
  have hn : 1 ≤ m + 1 := by omega
  have hB1 : 1 ≤ 1 + Real.sqrt ((m + 1 : ℕ) : ℝ) := by
    linarith [Real.sqrt_nonneg (((m + 1 : ℕ) : ℝ))]
  have hR : 0 < (1 + Real.sqrt ((m + 1 : ℕ) : ℝ)) * ((t : ℝ) + 1) := by positivity
  have hc : 0 < whitneyRatio := isWhitneyRatio_whitneyRatio.1
  have hs := scale_pos j
  have hsep : 0 ≤ separationConst * whitneyScale j := by
    have := one_le_two_mul_separationConst
    exact mul_nonneg (by linarith) hs.le
  have hsub := hCount (m + 1) j {z : IntPoint (m + 1) | (j, z) ∈ pieceIndexSet (m + 1) ∧
      (t : ℝ) ≤ configNorm (pieceCenter j z) ∧ configNorm (pieceCenter j z) < t + 1}
    (⋃ p ∈ orderedPairs (m + 1), {x : Config (m + 1) |
      maxNorm (x p.1 - x p.2) ≤ separationConst * whitneyScale j ∧
      configNorm x ≤ (1 + Real.sqrt ((m + 1 : ℕ) : ℝ)) * (t + 1)})
    (fun z hz x hx => by
      have hbox := mem_pieceBox_of_mem_quarterBox hx
      obtain ⟨p, hp, hpx⟩ := exists_pair_of_minSeparation_le hsep
        (((hCubes (m + 1) hn (j, z) hz.1).2.2.2.1 hj x hbox).1)
      exact Set.mem_biUnion hp
        ⟨hpx, configNorm_le_of_mem_pieceBox hCubes hn hz.1 hz.2.2 hbox⟩)
  have hvol : volume (⋃ p ∈ orderedPairs (m + 1), {x : Config (m + 1) |
      maxNorm (x p.1 - x p.2) ≤ separationConst * whitneyScale j ∧
      configNorm x ≤ (1 + Real.sqrt ((m + 1 : ℕ) : ℝ)) * (t + 1)}) ≤
      ENNReal.ofReal (choose2Real (m + 1) *
        ((2 * (separationConst * whitneyScale j)) ^ 4 * unitBallVol (4 * (m + 1) - 4) *
          ((1 + Real.sqrt ((m + 1 : ℕ) : ℝ)) * (t + 1)) ^ (4 * (m + 1) - 4))) := by
    refine (measure_biUnion_finset_le _ _).trans ?_
    refine (Finset.sum_le_card_nsmul _ _ _ fun p hp =>
      hTube (m + 1) p.1 p.2 ?_ _ _ hsep hR).trans ?_
    · exact (Finset.mem_filter.1 hp).2.ne
    · rw [choose2Real_eq_card, nsmul_eq_mul,
        ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
  have hD : 0 ≤ (2 / whitneySide j) ^ (4 * (m + 1)) := by
    have := side_pos j
    positivity
  refine hsub.trans ((mul_le_mul' le_rfl hvol).trans ?_)
  rw [← ENNReal.ofReal_mul hD]
  apply ENNReal.ofReal_le_ofReal
  have hv := unitBallVol_nonneg (4 * (m + 1) - 4)
  have hP : 0 ≤ choose2Real (m + 1) := by
    rw [choose2Real_eq_card]
    exact Nat.cast_nonneg _
  have hexp : 4 * (m + 1) - 4 = 4 * m := by omega
  have := constants_le_scale_pos m (A := 2 * separationConst) (D := 2 / whitneyRatio)
    (B := 1 + Real.sqrt ((m + 1 : ℕ) : ℝ)) (T := (t : ℝ) + 1) (s := whitneyScale j)
    (Q := choose2Real (m + 1) * unitBallVol (4 * m))
    (M := max (choose2Real (m + 1) * unitBallVol (4 * m)) (unitBallVol (4 * (m + 1))))
    one_le_two_mul_separationConst hB1 (by positivity) (by linarith) hs
    (mul_nonneg hP (by rw [hexp] at hv; exact hv)) (le_max_left _ _)
  rw [hexp, add_comm (1 : ℝ) (t : ℝ)]
  unfold pieceCountConst countingVolConst
  rw [hexp]
  have e1 : 2 / whitneySide j = 2 / whitneyRatio / whitneyScale j := by
    rw [whitneySide, div_mul_eq_div_div]
  rw [e1]
  calc _ = (2 / whitneyRatio / whitneyScale j) ^ (4 * (m + 1)) *
        ((2 * separationConst * whitneyScale j) ^ 4 *
          (choose2Real (m + 1) * unitBallVol (4 * m)) *
          ((1 + Real.sqrt ((m + 1 : ℕ) : ℝ)) * ((t : ℝ) + 1)) ^ (4 * m)) := by ring
    _ ≤ _ := this
theorem shellCenterCountBound_holds (hCount : CenterCountByVolume)
    (hBall : TupleEuclideanBallVolume)
    (hTube : DiagonalTubeVolumeBound)
    (hCubes : WhitneyCubeBoxBounds) : ShellCenterCountBound := by
  intro n hn j t
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  refine ⟨fun hj => card_shell_centers_scale_pos hCount hTube hCubes m j t hj, ?_⟩
  rintro rfl
  exact card_shell_centers_scale_zero hCount hBall hCubes hn t
end YangMills.Construction.ConfigurationSpace.ShellCount
end
