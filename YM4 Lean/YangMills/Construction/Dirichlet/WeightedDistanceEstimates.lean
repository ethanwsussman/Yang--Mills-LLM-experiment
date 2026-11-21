import YangMills.Construction.Dirichlet.CoverCountProof
import YangMills.Construction.Dirichlet.ShellCrossingChains
import YangMills.Construction.Dirichlet.ShellCrossingChainsOfPaths
import YangMills.Construction.Dirichlet.WeightedDistance
import Mathlib
set_option autoImplicit false
open Set Filter Topology
open YangMills.Construction.Torus YangMills.Construction.Dirichlet
open YangMills.Construction.Dirichlet.WeightedDistance YangMills.Construction.WeightedGreen
noncomputable section
namespace YangMills.Construction.Dirichlet
namespace WeightedDistanceEstimates
variable {d L : ℕ} {S aMinus aPlus : ℝ} (𝒮 : BlockSetting d L aMinus aPlus S)
theorem scaleAt_pos (hP : Parameters d L aMinus aPlus) (n : ℤ) : 0 < 𝒮.scaleAt n := by
  have hL : (0 : ℝ) < L := by exact_mod_cast lt_of_lt_of_le (by norm_num) hP.three_le_blockFactor
  exact mul_pos (zpow_pos hL n) 𝒮.isSeparatedChain.scale_pos
theorem lengthWithin_nonneg (Γ : List (TorusSegment d)) (X : Set (PeriodicTorus d S)) :
    0 ≤ lengthWithin Γ X := by apply _root_.YangMills.Construction.Dirichlet.Crossing.lengthWithin_nonneg <;> assumption
theorem chainWeightedLength_nonneg (hP : Parameters d L aMinus aPlus) (Γ : List (TorusSegment d)) :
    0 ≤ chainWeightedLength L 𝒮.ξ 𝒮.t 𝒮.Ω Γ := by
  unfold chainWeightedLength
  refine add_nonneg (Finset.sum_nonneg fun n _ => ?_) ?_
  · exact mul_nonneg (inv_nonneg.mpr (scaleAt_pos 𝒮 hP n).le) (lengthWithin_nonneg _ _)
  · exact mul_nonneg (inv_nonneg.mpr (scaleAt_pos 𝒮 hP 0).le) (lengthWithin_nonneg _ _)
theorem blockDist_nonneg (hP : Parameters d L aMinus aPlus) (p q : PeriodicTorus d S) :
    0 ≤ 𝒮.blockDist p q := by
  apply Real.sInf_nonneg
  rintro r ⟨Γ, -, -, -, rfl⟩
  exact chainWeightedLength_nonneg 𝒮 hP Γ
theorem lastNonemptyIndex_le : lastNonemptyIndex 𝒮.Ω ≤ 𝒮.t := by apply _root_.YangMills.Construction.Dirichlet.CoverCountProof.lastNonemptyIndex_le_t <;> assumption
theorem side_eq_mul (hP : Parameters d L aMinus aPlus) :
    ∃ K : ℕ, 0 < K ∧ S = (K : ℝ) * 𝒮.ξ := by
  obtain ⟨k, hk, hS⟩ := 𝒮.isSeparatedChain.period_eq_even_mul
  have hL : 0 < L := lt_of_lt_of_le (by norm_num) hP.three_le_blockFactor
  have hM : 0 < 𝒮.M :=
    lt_of_lt_of_le hL 𝒮.isSeparatedChain.blockSize_isPowerGe.1
  refine ⟨2 * k * 𝒮.M * L ^ lastNonemptyIndex 𝒮.Ω, by positivity, hS.trans ?_⟩
  simp only [scaleSpacing, zpow_natCast]
  push_cast
  ring
theorem spacingLattice_scaleSpacing_le (n : ℕ) :
    spacingLattice d S (scaleSpacing L 𝒮.ξ n) ≤ spacingLattice d S 𝒮.ξ := by
  rintro x ⟨k, rfl⟩
  refine ⟨fun μ => k μ * (L : ℤ) ^ n, ?_⟩
  funext μ
  simp only [torusProj, scaleSpacing, zpow_natCast]
  push_cast
  ring_nf
theorem centres_finite (hP : Parameters d L aMinus aPlus)
    (hLat : ∀ (σ : ℝ) (k : ℕ), 0 < σ → 0 < k → S = (k : ℝ) * σ → LatticeSumBounds d S σ) :
    𝒮.centres.Finite := by
  obtain ⟨K, hK, hS⟩ := side_eq_mul 𝒮 hP
  refine (hLat 𝒮.ξ K 𝒮.isSeparatedChain.scale_pos hK hS).finite.subset ?_
  rintro y ⟨n, -, -, hy, -⟩
  exact spacingLattice_scaleSpacing_le 𝒮 n hy
section Paths
variable {𝒮}
end Paths
theorem intExpSum_nonneg (κ : ℝ) : 0 ≤ intExpSum κ :=
  tsum_nonneg fun _ => (Real.exp_pos _).le
end WeightedDistanceEstimates
end YangMills.Construction.Dirichlet
