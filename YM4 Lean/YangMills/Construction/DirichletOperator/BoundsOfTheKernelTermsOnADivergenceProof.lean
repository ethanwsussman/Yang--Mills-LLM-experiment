import YangMills.Construction.Dirichlet.CommutatorBoundsProof
import YangMills.Construction.DirichletOperator.BlockNumbersOfTheKernelTermsProof
import YangMills.Construction.DirichletOperator.GreenOperatorOfACubeOnADivergenceOfACell
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction
open Set
open Dirichlet Torus RegionSequence RegionSequence.NestedRegions PartitionCubes RemainderEstimates
open CubeTorus (TensorAnchorSupported levelSpacing)
open CubeOperators (sourceSize)
open CubeGreenDivergence (divForm)
noncomputable section
namespace DivergenceSourceTerms
variable {𝒮 : NestedRegions} {M : ℕ}
theorem finite_fineBond (hl : TorusLengthsStatement) (𝒯 : NestedRegions) :
    Finite 𝒯.FineBond := by apply _root_.YangMills.Construction.RegionSequence.DifferenceAdjointsByParts.finite_fineBond <;> assumption
theorem cornerSet_finite (hl : TorusLengthsStatement) (n : ℕ)
    (hσ : 0 < cubeSide 𝒮 M n) (hk : ∃ k : ℤ, 𝒮.side / cubeSide 𝒮 M n = 2 * (k : ℝ)) :
    (cornerSet 𝒮 M n).Finite := by apply _root_.YangMills.Construction.RemainderAdjointSum.cornerSet_finite <;> assumption
theorem finite_levelCube (hc : ∀ n ≤ topLevel 𝒮, (cornerSet 𝒮 M n).Finite) :
    Finite (LevelCube 𝒮 M) := by apply _root_.YangMills.Construction.RemainderAdjointSum.finite_levelCube <;> assumption
section Lengths
variable {d : ℕ} {S : ℝ}
theorem supNorm_sub_le_add (p q r : PeriodicTorus d S) :
    supNorm (p - r) ≤ supNorm (p - q) + supNorm (q - r) := by apply _root_.YangMills.Construction.Dirichlet.Commutator.supNorm_sub_le_add <;> assumption
end Lengths
theorem norm_piSingle_le {ξ : ℝ} (hξ : 0 ≤ ξ) (ν : Fin 4) :
    ‖(Pi.single ν ξ : Fin 4 → ℝ)‖ ≤ ξ := by apply _root_.YangMills.Construction.PartitionCubes.LocalTorusOperators.norm_pi_single_le <;> assumption
theorem supNorm_source_sub_target_le (b : 𝒮.FineBond) :
    supNorm ((b.source : 𝒮.Point) - (b.target : 𝒮.Point)) ≤ 𝒮.ξ := by apply _root_.YangMills.Construction.CubeAdjointDefect.AsSources.supNorm_source_sub_target <;> assumption
theorem scale_succ (n : ℕ) : 𝒮.scale (n + 1) = (𝒮.L : ℝ) * 𝒮.scale n := by apply _root_.YangMills.Construction.PartitionCoefficients.nestedScale_succ <;> assumption
theorem cubeSide_pos (hM : 𝒮.L ^ 5 ≤ M) (n : ℕ) : 0 < cubeSide 𝒮 M n := by apply _root_.YangMills.Construction.PartitionCubes.PositionByType.cubeSide_pos <;> assumption
theorem mem_centresAt_level {y : 𝒮.Point} (hy : y ∈ 𝒮.allCentres) :
    y ∈ 𝒮.centresAt (𝒮.level y) := by apply _root_.YangMills.Construction.CubeNearSite.mem_centresAt_level <;> assumption
theorem sourceSize_nonneg {𝒯 : NestedRegions} (ε lam : ℝ) (J : 𝒯.Tensor 1) :
    0 ≤ sourceSize ε lam J := by
  refine add_nonneg (Real.iSup_nonneg fun ν => Real.sSup_nonneg ?_)
    (Real.iSup_nonneg fun ν => Real.iSup_nonneg fun b => norm_nonneg _)
  rintro r ⟨b, b', -, h₀, h₁, rfl⟩
  exact mul_nonneg (Real.rpow_nonneg (div_nonneg (h₀.le.trans h₁) h₀.le) _) (norm_nonneg _)
end DivergenceSourceTerms
end
end YangMills.Construction
