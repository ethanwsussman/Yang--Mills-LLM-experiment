import YangMills.Construction.Lattice.PeriodicLattices
import Mathlib
noncomputable section
namespace YangMills.Construction
namespace PeriodicLattice
variable {L m : ℕ} {j : ℤ}
def Bond.IsParallelToAxis (b : Bond L m j) (μ : Fin 4) : Prop :=
  b.target - b.source = unitStep L m j μ ∨ b.target - b.source = -unitStep L m j μ
def Plaquette.edges (p : Plaquette L m j) : Set (Bond L m j) :=
  {Bond.forwardFrom p.origin p.firstAxis,
    Bond.forwardFrom (p.origin + unitStep L m j p.firstAxis) p.secondAxis,
    Bond.forwardFrom (p.origin + unitStep L m j p.secondAxis) p.firstAxis,
    Bond.forwardFrom p.origin p.secondAxis}
end PeriodicLattice
end YangMills.Construction
end
