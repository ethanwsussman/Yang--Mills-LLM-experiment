import YangMills.Construction.DirichletOperator.BondsCarriedToTheTorusOfACube
import YangMills.Construction.DirichletOperator.FunctionsAndMapsOfTheCubes
import YangMills.Construction.DirichletOperator.TransfersOfTheIndicatorOfACube
import YangMills.Construction.RegionSequence.DifferenceAdjointsByParts
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Set
open Dirichlet Torus RegionSequence RegionSequence.NestedRegions
namespace PartitionCubes.IndicatorTransfer
section FiniteSums
variable {ι : Type}
end FiniteSums
section BondNorms
variable {𝒜 ℬ : RegionSequence.NestedRegions}
theorem finite_fineBond (hT : Torus.TorusLengthsStatement) (𝒯 : RegionSequence.NestedRegions) :
    Finite 𝒯.FineBond := by apply _root_.YangMills.Construction.RegionSequence.DifferenceAdjointsByParts.finite_fineBond <;> assumption
end BondNorms
section OneCube
variable {𝒮 : RegionSequence.NestedRegions} {M : ℕ} (Q : LevelCube 𝒮 M)
def innerBonds : Set 𝒮.FineBond := {b | (b.source : 𝒮.Point) ∈ Q.thicken (5 / 6)}
variable {Q}
theorem thicken_subset_strictPts (hC : Q.TransfersToTorus) (hT : Torus.TorusLengthsStatement) :
    Q.thicken (5 / 6) ⊆ Q.strictPts := fun x hx =>
  (hC.isometry_ball x hx x (by
    rw [sub_self, (hT 4 𝒮.side 𝒮.side_pos).1.supNorm_zero]
    have hξ := 𝒮.ξ_pos
    unfold RegionSequence.NestedRegions.scale Torus.scaleSpacing
    positivity)).1
theorem anchor_eq_source (hC : Q.TransfersToTorus) (c : Q.system.setting.FineBond) :
    ((Q.system.setting.anchor c : Q.system.setting.FineSite) : Q.system.setting.Point) =
      (c.source : Q.system.setting.Point) := by
  have h0 : Q.system.setting.Ω 0 = univ := hC.cube_setting.full_below 0 (Nat.zero_le _)
  simp [RegionSequence.NestedRegions.anchor, h0]
end OneCube
end PartitionCubes.IndicatorTransfer
end YangMills.Construction
