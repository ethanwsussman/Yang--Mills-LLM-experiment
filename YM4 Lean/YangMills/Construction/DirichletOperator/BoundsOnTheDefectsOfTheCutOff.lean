import YangMills.Construction.DirichletOperator.OperatorsComparingACubeWithTheTorus
import Mathlib
set_option autoImplicit false
open Set
open YangMills.Construction.Dirichlet YangMills.Construction.RegionSequence YangMills.Construction.RegionSequence.NestedRegions YangMills.Construction.PartitionCubes YangMills.Construction.CubeTorusComparison
open YangMills.Construction.DirichletGreen (fieldModulusAt)
open YangMills.Construction.CubeTorus (torusSetting levelSpacing)
noncomputable section
namespace YangMills.Construction.CubeTorusComparison.CutoffDefects
variable {𝒮 : NestedRegions} {M : ℕ}
structure Bounds (C : ℝ) (Q : LevelCube 𝒮 M) : Prop where
  cellOf_subset_annulus : ∀ y ∈ nonconstantCells Q,
    𝒮.cellOf y ⊆ Q.thicken (5 / 6) \ Q.thicken (5 / 12)
  encard_le : (nonconstantCells Q).encard ≤ ((8 * M) ^ 4 : ℕ)
  pushLapCommutator_eq_zero : ∀ (f : (torusSetting Q).FineSite → ℝ) (u : 𝒮.FineSite),
    ¬InNonconstantCell Q u → pushLapCommutator Q f u = 0
  pushAvgDefect_eq_zero : ∀ (ω : (torusSetting Q).Coarse) (u : 𝒮.FineSite),
    ¬InNonconstantCell Q u → pushAvgDefect Q ω u = 0
  pushLapCommutator_le : ∀ (f : (torusSetting Q).FineSite → ℝ) (u : 𝒮.FineSite) (a b : ℝ),
    InNonconstantCell Q u →
    (∀ u' ∈ cellAndNeighbours u, |f (Q.system.mapSite u')| ≤ a) →
    (∀ u' ∈ cellAndNeighbours u, fieldModulusAt (grad f) (Q.system.mapSite u') ≤ b) →
      |pushLapCommutator Q f u| ≤
        C * (M : ℝ)⁻¹ * ((levelSpacing Q)⁻¹ * b + (levelSpacing Q ^ 2)⁻¹ * a)
  pushAvgDefect_le : ∀ (ω : (torusSetting Q).Coarse) (u : 𝒮.FineSite) (y : 𝒮.Point) (a : ℝ),
    y ∈ nonconstantCells Q → (u : 𝒮.Point) ∈ 𝒮.cellOf y → 0 ≤ a →
    (∀ w : (torusSetting Q).allCentres,
      (w : (torusSetting Q).Point) = Q.system.embed y → |ω w| ≤ a) →
      |pushAvgDefect Q ω u| ≤ C * (M : ℝ)⁻¹ * a
  pullLapCommutator_eq_zero : ∀ (g : 𝒮.FineSite → ℝ) (w : (torusSetting Q).FineSite),
    (∀ u : 𝒮.FineSite, InNonconstantCell Q u → Q.system.mapSite u ≠ w) →
      pullLapCommutator Q g w = 0
  pullAvgDefect_eq_zero : ∀ (ω : 𝒮.Coarse) (w : (torusSetting Q).FineSite),
    (∀ u : 𝒮.FineSite, InNonconstantCell Q u → Q.system.mapSite u ≠ w) →
      pullAvgDefect Q ω w = 0
  pullLapCommutator_le : ∀ (g : 𝒮.FineSite → ℝ) (u : 𝒮.FineSite) (a b : ℝ),
    InNonconstantCell Q u →
    (∀ u' ∈ cellAndNeighbours u, |g u'| ≤ a) →
    (∀ u' ∈ cellAndNeighbours u, fieldModulusAt (grad g) u' ≤ b) →
      |pullLapCommutator Q g (Q.system.mapSite u)| ≤
        C * (M : ℝ)⁻¹ * ((levelSpacing Q)⁻¹ * b + (levelSpacing Q ^ 2)⁻¹ * a)
  pullAvgDefect_le : ∀ (ω : 𝒮.Coarse) (u : 𝒮.FineSite) (y : 𝒮.allCentres),
    (y : 𝒮.Point) ∈ nonconstantCells Q → (u : 𝒮.Point) ∈ 𝒮.cellOf y →
      |pullAvgDefect Q ω (Q.system.mapSite u)| ≤ C * (M : ℝ)⁻¹ * |ω y|
end YangMills.Construction.CubeTorusComparison.CutoffDefects
