import YangMills.Construction.Dirichlet.CentresAndCells
import YangMills.Construction.WeightedGreen.DecayRateDefs
import YangMills.Construction.Dirichlet.BilinearForms
import YangMills.Construction.Dirichlet.CollarGeometry
import YangMills.Construction.WeightedGreen.DecayRateBounds
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Dirichlet.ConjugateAveraging
variable {d L : ℕ} {S aMinus aPlus : ℝ}
section Cells
variable (𝒮 : BlockSetting d L aMinus aPlus S) [Fintype (LatticeSite d S 𝒮.ξ)]
open Classical in
def cellSites (y : Torus.PeriodicTorus d S) : Finset (LatticeSite d S 𝒮.ξ) :=
  Finset.univ.filter fun x => (x : Torus.PeriodicTorus d S) ∈ 𝒮.cell y
end Cells
end YangMills.Construction.Dirichlet.ConjugateAveraging
