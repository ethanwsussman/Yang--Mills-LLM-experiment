import YangMills.Construction.Matrices.OperatorNormAbsoluteSeries
import Mathlib
open Filter
open scoped Matrix.Norms.L2Operator Topology
namespace YangMills.Construction.Matrices.ComplexMatrix2
namespace OperatorNormFacts
private theorem norm_toEuclideanLin_le (X : ComplexMatrix2) (v : EuclideanSpace ℂ (Fin 2)) :
    ‖Matrix.toEuclideanLin X v‖ ≤ operatorNorm X * ‖v‖ :=
  (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) X).le_opNorm v
private theorem operatorNorm_le_of_bound (X : ComplexMatrix2) {C : ℝ} (hC : 0 ≤ C)
    (hbd : ∀ v : EuclideanSpace ℂ (Fin 2), ‖Matrix.toEuclideanLin X v‖ ≤ C * ‖v‖) :
    operatorNorm X ≤ C :=
  (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) X).opNorm_le_bound hC hbd
private theorem toEuclideanLin_apply_coord (X : ComplexMatrix2) (v : EuclideanSpace ℂ (Fin 2))
    (i : Fin 2) :
    (Matrix.toEuclideanLin X v) i = X i 0 * v 0 + X i 1 * v 1 := by
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
private theorem norm_entry_le_operatorNorm (X : ComplexMatrix2) (i j : Fin 2) :
    ‖X i j‖ ≤ operatorNorm X := by
  have hX := norm_toEuclideanLin_le X (EuclideanSpace.single j (1 : ℂ))
  have hv : ‖EuclideanSpace.single j (1 : ℂ)‖ = 1 := by simp
  have he : (Matrix.toEuclideanLin X (EuclideanSpace.single j (1 : ℂ))) i = X i j := by
    rw [toEuclideanLin_apply_coord]
    fin_cases j <;> simp
  calc ‖X i j‖ = ‖(Matrix.toEuclideanLin X (EuclideanSpace.single j (1 : ℂ))) i‖ := by rw [he]
    _ ≤ ‖Matrix.toEuclideanLin X (EuclideanSpace.single j (1 : ℂ))‖ := PiLp.norm_apply_le _ _
    _ ≤ operatorNorm X := by simpa [hv] using hX
abbrev _root_.YangMills.DeltaSharedProofs.p500882 := @norm_entry_le_operatorNorm
abbrev _root_.YangMills.SharedProofs.p34458 := @norm_entry_le_operatorNorm
private theorem operatorNorm_le_two_mul_maxEntryNorm (X : ComplexMatrix2) :
    operatorNorm X ≤ 2 * maxEntryNorm X := by
  have hm : ∀ i j, ‖X i j‖ ≤ maxEntryNorm X := fun i j =>
    Finset.le_sup' (fun p : Fin 2 × Fin 2 => ‖X p.1 p.2‖) (Finset.mem_univ (i, j))
  have hm0 : 0 ≤ maxEntryNorm X := (norm_nonneg _).trans (hm 0 0)
  refine operatorNorm_le_of_bound X (by positivity) fun v => ?_
  have hcoord : ∀ i, ‖(Matrix.toEuclideanLin X v) i‖ ≤
      maxEntryNorm X * (‖v 0‖ + ‖v 1‖) := by
    intro i
    rw [toEuclideanLin_apply_coord]
    calc ‖X i 0 * v 0 + X i 1 * v 1‖ ≤ ‖X i 0 * v 0‖ + ‖X i 1 * v 1‖ := norm_add_le _ _
      _ = ‖X i 0‖ * ‖v 0‖ + ‖X i 1‖ * ‖v 1‖ := by rw [norm_mul, norm_mul]
      _ ≤ maxEntryNorm X * ‖v 0‖ + maxEntryNorm X * ‖v 1‖ := by
          gcongr <;> exact hm _ _
      _ = maxEntryNorm X * (‖v 0‖ + ‖v 1‖) := by ring
  have hw : ‖Matrix.toEuclideanLin X v‖ ^ 2 =
      ‖(Matrix.toEuclideanLin X v) 0‖ ^ 2 + ‖(Matrix.toEuclideanLin X v) 1‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]
  have hv : ‖v‖ ^ 2 = ‖v 0‖ ^ 2 + ‖v 1‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]
  have hsq : ∀ i, ‖(Matrix.toEuclideanLin X v) i‖ ^ 2 ≤
      (maxEntryNorm X * (‖v 0‖ + ‖v 1‖)) ^ 2 := fun i =>
    pow_le_pow_left₀ (norm_nonneg _) (hcoord i) 2
  have hab : (‖v 0‖ + ‖v 1‖) ^ 2 ≤ 2 * (‖v 0‖ ^ 2 + ‖v 1‖ ^ 2) := by
    nlinarith [sq_nonneg (‖v 0‖ - ‖v 1‖)]
  refine (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp ?_
  calc ‖Matrix.toEuclideanLin X v‖ ^ 2
      ≤ 2 * (maxEntryNorm X ^ 2 * (‖v 0‖ + ‖v 1‖) ^ 2) := by
        rw [hw]
        have h₀ := hsq 0
        have h₁ := hsq 1
        rw [mul_pow] at h₀ h₁
        linarith
    _ ≤ 2 * (maxEntryNorm X ^ 2 * (2 * (‖v 0‖ ^ 2 + ‖v 1‖ ^ 2))) := by gcongr
    _ = (2 * maxEntryNorm X * ‖v‖) ^ 2 := by
        rw [mul_pow, mul_pow, hv]
        ring
private theorem tendsto_operatorNorm_sub_iff (S : ComplexMatrix2) (T : ℕ → ComplexMatrix2) :
    Tendsto (fun l => operatorNorm (S - T l)) atTop (𝓝 0) ↔
      ∀ i j, Tendsto (fun l => T l i j) atTop (𝓝 (S i j)) := by
  constructor
  · intro hT i j
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun _ => norm_nonneg _) (fun l => ?_) hT
    rw [norm_sub_rev]
    exact norm_entry_le_operatorNorm (S - T l) i j
  · intro hT
    have hz : Tendsto (fun l => 2 * ∑ p : Fin 2 × Fin 2, ‖(S - T l) p.1 p.2‖) atTop (𝓝 0) := by
      have hsum : Tendsto (fun l => ∑ p : Fin 2 × Fin 2, ‖(S - T l) p.1 p.2‖) atTop
          (𝓝 (∑ _p : Fin 2 × Fin 2, (0 : ℝ))) :=
        tendsto_finsetSum _ fun p _ =>
          (tendsto_iff_norm_sub_tendsto_zero.mp (hT p.1 p.2)).congr fun l => norm_sub_rev _ _
      simpa using hsum.const_mul 2
    refine squeeze_zero (fun _ => norm_nonneg _) (fun l => ?_) hz
    refine (operatorNorm_le_two_mul_maxEntryNorm _).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    refine Finset.sup'_le _ _ fun p _ => ?_
    exact Finset.single_le_sum (f := fun p : Fin 2 × Fin 2 => ‖(S - T l) p.1 p.2‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_univ p)
private theorem eq_of_tendsto_operatorNorm (T : ℕ → ComplexMatrix2) (S S' : ComplexMatrix2)
    (hS : Tendsto (fun l => operatorNorm (S - T l)) atTop (𝓝 0))
    (hS' : Tendsto (fun l => operatorNorm (S' - T l)) atTop (𝓝 0)) : S = S' := by
  ext i j
  exact tendsto_nhds_unique ((tendsto_operatorNorm_sub_iff S T).mp hS i j)
    ((tendsto_operatorNorm_sub_iff S' T).mp hS' i j)
private theorem summable_operatorNorm {X : ℕ → ComplexMatrix2}
    (hX : SeriesAbsolutelyConvergent X) :
    Summable fun n => operatorNorm (X n) := by
  obtain ⟨s, hs⟩ := hX
  have hs' : Tendsto (fun l => ∑ n ∈ Finset.range l, operatorNorm (X n)) atTop (𝓝 s) :=
    (tendsto_add_atTop_iff_nat 1).mp hs
  exact ((hasSum_iff_tendsto_nat_of_nonneg (fun n => norm_nonneg _) s).mpr hs').summable
private theorem hasSeriesSum_tsum {X : ℕ → ComplexMatrix2}
    (hs : Summable fun n => operatorNorm (X n)) :
    HasSeriesSum X (∑' n, X n) := by
  have hX : Summable X := Summable.of_norm hs
  have hlim : Tendsto (fun l => ∑ n ∈ Finset.range (l + 1), X n) atTop (𝓝 (∑' n, X n)) :=
    (tendsto_add_atTop_iff_nat 1).mpr hX.hasSum.tendsto_sum_nat
  exact (tendsto_iff_norm_sub_tendsto_zero.mp hlim).congr fun l => norm_sub_rev _ _
private theorem hasSeriesSum_properties {X : ℕ → ComplexMatrix2}
    (hX : SeriesAbsolutelyConvergent X) {S : ComplexMatrix2} (hS : HasSeriesSum X S) :
    (∀ i j,
      (∃ s : ℝ, Tendsto (fun l => ∑ n ∈ Finset.range (l + 1), ‖X n i j‖) atTop (𝓝 s)) ∧
      Tendsto (fun l => ∑ n ∈ Finset.range (l + 1), X n i j) atTop (𝓝 (S i j))) ∧
    (∀ l : ℕ, operatorNorm (S - seriesPartialSum X l) ≤
      ∑' n : ℕ, operatorNorm (X (n + (l + 1)))) ∧
    operatorNorm S ≤ ∑' n : ℕ, operatorNorm (X n) := by
  have hs := summable_operatorNorm hX
  have hXs : Summable X := Summable.of_norm hs
  have hSeq : S = ∑' n, X n := eq_of_tendsto_operatorNorm _ _ _ hS (hasSeriesSum_tsum hs)
  refine ⟨fun i j => ⟨?_, ?_⟩, fun l => ?_, ?_⟩
  · have he : Summable fun n => ‖X n i j‖ :=
      Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
        (fun n => norm_entry_le_operatorNorm (X n) i j) hs
    exact ⟨_, (tendsto_add_atTop_iff_nat 1).mpr he.hasSum.tendsto_sum_nat⟩
  · have he := (tendsto_operatorNorm_sub_iff S (seriesPartialSum X)).mp hS i j
    refine he.congr fun l => ?_
    simp [seriesPartialSum, Matrix.sum_apply]
  · have hsplit : S - seriesPartialSum X l = ∑' n, X (n + (l + 1)) := by
      rw [hSeq, seriesPartialSum, ← hXs.sum_add_tsum_nat_add (l + 1), add_sub_cancel_left]
    rw [hsplit]
    have hshift : Summable fun n => ‖X (n + (l + 1))‖ :=
      (summable_nat_add_iff (f := fun n => ‖X n‖) (l + 1)).mpr hs
    exact norm_tsum_le_tsum_norm hshift
  · rw [hSeq]
    exact norm_tsum_le_tsum_norm hs
end OperatorNormFacts
open OperatorNormFacts in
theorem operatorNormSeriesProperties_holds : OperatorNormSeriesProperties := by
  refine ⟨fun X => ⟨?_, operatorNorm_le_two_mul_maxEntryNorm X⟩, fun X => ?_,
    fun X hX => norm_eq_zero.mp hX,
    fun X v => ?_, fun X C hC => ?_, fun X Y => norm_add_le X Y, fun c X => norm_smul c X,
    fun X Y => norm_mul_le X Y, CStarRing.norm_one, fun X n => ?_, fun X u w hu hw => ?_,
    tendsto_operatorNorm_sub_iff, eq_of_tendsto_operatorNorm,
    fun X S S' hS hS' => eq_of_tendsto_operatorNorm _ S S' hS hS',
    fun X hX => ⟨⟨_, hasSeriesSum_tsum (summable_operatorNorm hX)⟩,
      fun S hS => hasSeriesSum_properties hX hS⟩,
    fun W hW => ⟨⟨fun Y Y' => ?_, fun c Y => ?_⟩, fun Y => ?_, fun S T hST => ?_⟩⟩
  · exact Finset.sup'_le _ _ fun p _ => norm_entry_le_operatorNorm X p.1 p.2
  · refine ⟨operatorNorm X, ?_⟩
    rintro _ ⟨v, hv, rfl⟩
    have h1 : ‖v‖ = 1 := by simpa using hv
    simp only [coordinateNorm_eq_norm]
    simpa [h1] using norm_toEuclideanLin_le X v
  · simp only [coordinateNorm_eq_norm]
    exact norm_toEuclideanLin_le X v
  · simp only [coordinateNorm_eq_norm] at hC
    have hC0 : 0 ≤ C := by
      have h1 := hC (EuclideanSpace.single 0 (1 : ℂ))
      have hv : ‖EuclideanSpace.single (0 : Fin 2) (1 : ℂ)‖ = 1 := by simp
      rw [hv, mul_one] at h1
      exact (norm_nonneg _).trans h1
    exact operatorNorm_le_of_bound X hC0 hC
  · rcases n with _ | n
    · simp
    · exact norm_pow_le' X (Nat.succ_pos n)
  · simp only [operatorNorm]
    rw [CStarRing.norm_mul_mem_unitary _ hw, CStarRing.norm_mem_unitary_mul _ hu]
  · rw [mul_add, add_mul]
  · rw [Matrix.mul_smul, Matrix.smul_mul]
  · calc operatorNorm (W * Y * W⁻¹) ≤ operatorNorm (W * Y) * operatorNorm W⁻¹ := norm_mul_le _ _
      _ ≤ operatorNorm W * operatorNorm Y * operatorNorm W⁻¹ := by
          gcongr
          exact norm_mul_le _ _
      _ = operatorNorm W * operatorNorm W⁻¹ * operatorNorm Y := by ring
  · have hz : Tendsto (fun l => operatorNorm W * operatorNorm W⁻¹ * operatorNorm (S - T l))
        atTop (𝓝 0) := by
      simpa using hST.const_mul (operatorNorm W * operatorNorm W⁻¹)
    refine squeeze_zero (fun _ => norm_nonneg _) (fun l => ?_) hz
    have he : W * S * W⁻¹ - W * T l * W⁻¹ = W * (S - T l) * W⁻¹ := by
      rw [mul_sub, sub_mul]
    rw [he]
    calc operatorNorm (W * (S - T l) * W⁻¹)
        ≤ operatorNorm (W * (S - T l)) * operatorNorm W⁻¹ := norm_mul_le _ _
      _ ≤ operatorNorm W * operatorNorm (S - T l) * operatorNorm W⁻¹ := by
          gcongr
          exact norm_mul_le _ _
      _ = operatorNorm W * operatorNorm W⁻¹ * operatorNorm (S - T l) := by ring
end YangMills.Construction.Matrices.ComplexMatrix2
