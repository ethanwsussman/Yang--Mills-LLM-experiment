import YangMills.Construction.Dirichlet.BilinearForms
import YangMills.Construction.Dirichlet.CentresAndCells
import YangMills.Construction.WeightedGreen.DecayRateDefs
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
open Torus WeightedGreen
namespace Dirichlet.CoercivityProof
variable {d L : ℕ} {S aMinus aPlus : ℝ}
section Cells
variable (𝒮 : BlockSetting d L aMinus aPlus S) [Fintype (LatticeSite d S 𝒮.ξ)]
open Classical in
def cellSites (y : PeriodicTorus d S) : Finset (LatticeSite d S 𝒮.ξ) :=
  Finset.univ.filter fun x => (x : PeriodicTorus d S) ∈ 𝒮.cell y
end Cells
end Dirichlet.CoercivityProof
end YangMills.Construction
