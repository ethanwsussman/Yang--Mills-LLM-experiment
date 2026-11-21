import YangMills.Construction.Torus.AveragingOperatorAndMatricesProof
import YangMills.Construction.Weighted.InverseExpansionConstants
import YangMills.Construction.Torus.DistanceAveragesWholePairMatricesAndNorms
import YangMills.Construction.Torus.FloorsOfTheAveragedSquareExpansion
import YangMills.Construction.Torus.KernelThroughScaledMatrices
import YangMills.Construction.Torus.LowerBoundOnTheAveragedGreenSquare
import YangMills.Construction.Torus.UpperBoundOnThePairScaledMatrix
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Weighted
open Set YangMills.Construction.TorusMetric
namespace AvgGreenSqBounds
theorem scale_pos (D : TorusData) (n : ℕ) : 0 < D.scale n := by apply _root_.YangMills.Construction.Weighted.AvgMatrix.chainScale_pos <;> assumption
theorem siteCubes_blocks (hP : CubesLayersBlocksBallsHold) (D : TorusData)
    (B : SeparatedChain D) :
    B.SiteCubesTile ∧ B.BlocksPartition ∧
      ∀ n, ∀ y ∈ B.layerSites n, B.BlockDescription n y := by
  obtain ⟨m, hm⟩ := D.blockNumber_power
  have hL3 : 3 ≤ D.L := D.blocking.three_le_factor
  have hL : (1 : ℝ) ≤ D.L := by
    have : 1 ≤ D.L := by omega
    exact_mod_cast this
  have hbn : (1 : ℝ) ≤ D.blockNumber := by
    have : 1 ≤ D.blockNumber := by
      have := D.le_blockNumber
      omega
    exact_mod_cast this
  have hle : D.scale 0 ≤ (D.blockNumber : ℝ) * D.scale D.top := by
    have h1 : D.scale 0 ≤ D.scale D.top := by
      unfold TorusData.scale
      have := one_le_pow₀ hL (n := D.top)
      have hb := D.bareSpacing_pos
      simp only [pow_zero, one_mul]
      nlinarith
    have h2 := scale_pos D D.top
    nlinarith
  obtain ⟨-, -, -, -, h5, h6, h7, -, -⟩ := hP D B m hm 0 0 le_rfl hle
  exact ⟨h5, h6, h7⟩
theorem greenDecayRate_pos {L : ℕ} (hL : 3 ≤ L) : 0 < greenDecayRate 4 L := by
  have hL0 : (0 : ℝ) < L := by
    have : 0 < L := by omega
    exact_mod_cast this
  unfold greenDecayRate
  exact div_pos one_pos (mul_pos (by norm_num) hL0)
variable {D : TorusData} (B : SeparatedChain D)
theorem allSites_finite (hs : ∀ n, ∀ y ∈ B.layerSites n, B.BlockDescription n y) :
    B.allSites.Finite := by
  have := D.bareSite_finite
  refine (finite_range fun x : D.BareSite => (x : D.Space)).subset fun y hy => ?_
  obtain ⟨n, -, hn⟩ := mem_iUnion₂.1 hy
  obtain ⟨yb, -, rfl⟩ := (hs n y hn).2.2.2.2.1
  exact ⟨yb, rfl⟩
theorem weightedDistance_nonneg (x x' : D.Space) : 0 ≤ B.weightedDistance x x' := by apply _root_.YangMills.Construction.Weighted.AvgMatrix.weightedDistance_nonneg <;> assumption
theorem expWeightedMatrixNorm_zero_le [Finite ↥B.allSites] [Nonempty ↥B.allSites]
    (M : B.LayerMat) {C κ c : ℝ} (hC : 0 ≤ C)
    (hM : ∀ y y' : ↥B.allSites, |M y y'| ≤ C * Real.exp (-κ * B.weightedDistance y y'))
    (hd : ∀ y y' : ↥B.allSites, B.weightedDistance y y' = B.weightedDistance y' y)
    (hsum : ∀ y : ↥B.allSites, ∑ᶠ y' : ↥B.allSites, Real.exp (-κ * B.weightedDistance y y') ≤ c) :
    B.expWeightedMatrixNorm 0 M ≤ C * c := by
  classical
  have := Fintype.ofFinite ↥B.allSites
  have hsum' : ∀ y : ↥B.allSites,
      ∑ y' : ↥B.allSites, Real.exp (-κ * B.weightedDistance y y') ≤ c := fun y => by
    rw [← finsum_eq_sum_of_fintype]
    exact hsum y
  have row : ∀ y : ↥B.allSites,
      ∑ᶠ y' : ↥B.allSites, |M y y'| * Real.exp (0 * B.weightedDistance y y') ≤ C * c := by
    intro y
    rw [finsum_eq_sum_of_fintype]
    calc ∑ y' : ↥B.allSites, |M y y'| * Real.exp (0 * B.weightedDistance y y')
        ≤ ∑ y' : ↥B.allSites, C * Real.exp (-κ * B.weightedDistance y y') :=
          Finset.sum_le_sum fun y' _ => by simpa using hM y y'
      _ = C * ∑ y' : ↥B.allSites, Real.exp (-κ * B.weightedDistance y y') :=
          (Finset.mul_sum _ _ _).symm
      _ ≤ C * c := mul_le_mul_of_nonneg_left (hsum' y) hC
  have col : ∀ y' : ↥B.allSites,
      ∑ᶠ y : ↥B.allSites, |M y y'| * Real.exp (0 * B.weightedDistance y y') ≤ C * c := by
    intro y'
    rw [finsum_eq_sum_of_fintype]
    calc ∑ y : ↥B.allSites, |M y y'| * Real.exp (0 * B.weightedDistance y y')
        ≤ ∑ y : ↥B.allSites, C * Real.exp (-κ * B.weightedDistance y' y) :=
          Finset.sum_le_sum fun y _ => by
            have h := hM y y'
            rw [hd y y'] at h
            simpa using h
      _ = C * ∑ y : ↥B.allSites, Real.exp (-κ * B.weightedDistance y' y) :=
          (Finset.mul_sum _ _ _).symm
      _ ≤ C * c := mul_le_mul_of_nonneg_left (hsum' y') hC
  exact max_le (ciSup_le row) (ciSup_le col)
end AvgGreenSqBounds
end YangMills.Construction.Weighted
