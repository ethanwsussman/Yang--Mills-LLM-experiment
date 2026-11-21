import YangMills.Construction.Dirichlet.CubeCoverAndWalks
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Dirichlet
open YangMills.Construction.Torus
namespace BlockSetting
variable {d L : ℕ} {S aMinus aPlus : ℝ} (𝒮 : BlockSetting d L aMinus aPlus S)
def centresNearBump (Q : CentredCube d S) : Set (PeriodicTorus d S) :=
  {y | y ∈ 𝒮.centres ∧ supSetDist {y} (tsupport (𝒮.cubeBump Q)) ≤ ENNReal.ofReal (3 * 𝒮.centreSpacing y)}
def baseNbhd : Set (PeriodicTorus d S) :=
  {p | supSetDist {p} (𝒮.Ω 0) ≤ ENNReal.ofReal (4 * 𝒮.ξ)}
end BlockSetting
end YangMills.Construction.Dirichlet
