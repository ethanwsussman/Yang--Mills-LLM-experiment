import YangMills.Construction.PartitionCubes.LocalOperators
import Mathlib
set_option autoImplicit false
open Set
open YangMills.Construction.Dirichlet YangMills.Construction.Torus
open YangMills.Construction.RegionSequence YangMills.Construction.RegionSequence.NestedRegions
noncomputable section
namespace YangMills.Construction.PartitionCubes.CubeTorus
variable {𝒮 : NestedRegions} {M : ℕ}
def restrictSites (Q : LevelCube 𝒮 M) (f : 𝒮.FineSite → ℝ) : Q.system.setting.FineSite → ℝ :=
  Q.system.pullSites (indicator (Q.thicken (5 / 6)) 1) f
def restrictBonds (Q : LevelCube 𝒮 M) (A : 𝒮.FineBond → ℝ) : Q.system.setting.FineBond → ℝ :=
  Q.system.pullBonds (indicator (Q.thicken (5 / 6)) 1) A
structure SiteFunctionsMatch (Q : LevelCube 𝒮 M) (f : 𝒮.FineSite → ℝ)
    (g : Q.system.setting.FineSite → ℝ) : Prop where
  vanishes_off : VanishesOff (Q.thicken (5 / 6)) f
  image_vanishes_off : VanishesOff (Q.system.embed '' Q.thicken (5 / 6)) g
  eq_on : ∀ x : 𝒮.FineSite, (x : 𝒮.Point) ∈ Q.thicken (5 / 6) → f x = g (Q.system.mapSite x)
structure BondFunctionsMatch (Q : LevelCube 𝒮 M) (A : 𝒮.FineBond → ℝ)
    (B : Q.system.setting.FineBond → ℝ) : Prop where
  supported : AnchorSupported (Q.thicken (5 / 6)) A
  image_supported : AnchorSupported (Q.system.embed '' Q.thicken (5 / 6)) B
  eq_on : ∀ b : 𝒮.FineBond, AnchoredIn (Q.thicken (5 / 6)) b → A b = B (Q.system.mapBond b)
def averagingOp {𝒯 : NestedRegions} (f : 𝒯.FineSite → ℝ) : 𝒯.FineSite → ℝ :=
  blockAvgAdj (weightMul (blockAvg f))
end YangMills.Construction.PartitionCubes.CubeTorus
