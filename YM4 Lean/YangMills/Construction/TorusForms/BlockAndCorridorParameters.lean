import YangMills.Construction.TorusForms.FacesAndSumsOfBlocksAndCorridors
import Mathlib
noncomputable section
namespace YangMills.Construction.BlockSpin
open Finset
def plaquetteCornersOver {d : ℕ} {ℓ : Fin d → ℝ} (μ : Fin d) (b : Lattice.Link ℓ 1) :
    Set (Lattice.LatticeSite ℓ 1) :=
  {b.1, b.1 + Lattice.latticeStep ℓ 1 μ,
    b.1 + Lattice.latticeStep ℓ 1 μ + Lattice.latticeStep ℓ 1 b.2, b.1 + Lattice.latticeStep ℓ 1 b.2}
end YangMills.Construction.BlockSpin
