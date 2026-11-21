import YangMills.Construction.TorusForms.BlocksCorridorsDomainsTrees
import YangMills.Construction.TorusForms.CoveringLattices
import Mathlib
noncomputable section
namespace YangMills.Construction
namespace BlockSpin
open _root_.YangMills.Construction.Lattice
section Torus
variable (S : LatticeParameters) {ℓ : Fin S.d → ℝ} {ε ε' ε'' : ℝ}
end Torus
end BlockSpin
namespace CoveringLattice
open _root_.YangMills.Construction.Lattice (LatticeParameters scaledIntegerLattice)
open BlockSpin (InBlockIndexRange blockOffset)
structure GridLinkStep (d : ℕ) (ε : ℝ) where
  link : GridLink d ε
  forward : Bool
def GridLinkStep.source {d : ℕ} {ε : ℝ} (t : GridLinkStep d ε) : GridSite d ε :=
  if t.forward then t.link.1 else t.link.head
def GridLinkStep.target {d : ℕ} {ε : ℝ} (t : GridLinkStep d ε) : GridSite d ε :=
  if t.forward then t.link.head else t.link.1
def IsGridWalkFrom {d : ℕ} {ε : ℝ} : GridSite d ε → List (GridLinkStep d ε) → Prop
  | _, [] => True
  | x, t :: ts => t.source = x ∧ IsGridWalkFrom t.target ts
structure GridPath (d : ℕ) (ε : ℝ) where
  origin : GridSite d ε
  steps : List (GridLinkStep d ε)
  isWalk : IsGridWalkFrom origin steps
def gridWalkEnd {d : ℕ} {ε : ℝ} : GridSite d ε → List (GridLinkStep d ε) → GridSite d ε
  | x, [] => x
  | _, t :: ts => gridWalkEnd t.target ts
def GridPath.endpoint {d : ℕ} {ε : ℝ} (γ : GridPath d ε) : GridSite d ε :=
  gridWalkEnd γ.origin γ.steps
section Lattices
variable (S : LatticeParameters) {ε ε' ε'' : ℝ}
end Lattices
end CoveringLattice
namespace BlockSpin
open _root_.YangMills.Construction.Lattice
end BlockSpin
end YangMills.Construction
