import YangMills.Construction.Lattice.LocalizedDecayBounds
import YangMills.Construction.Lattice.TwoScaleOperatorDefs
import Mathlib
set_option autoImplicit false
open scoped ContDiff
noncomputable section
namespace YangMills.Construction.PeriodicLattice
open ScaledFun
variable {d N : ℕ}
def centeredCube (s : Mesh N) (y : Torus d N) : Set (GridPoint d s) :=
  {x | ∃ w : Fin d → ℝ, (∀ μ, -1 ≤ w μ ∧ w μ < 1) ∧
    (x : Torus d N) = y + fun μ => (w μ : AddCircle (N : ℝ))}
namespace Scales
variable {L j : ℕ} (S : Scales d L j N)
end Scales
instance instNonemptyDecayTriple : Nonempty (ℕ × ℝ × DecayConstants) :=
  ⟨(1, 1,
    { base := 1
      holder := fun _ => 1
      grad := fun _ => 1
      gradHolder := fun _ _ => 1
      base_pos := one_pos
      holder_pos := fun _ _ _ => one_pos
      grad_pos := fun _ _ _ => one_pos
      gradHolder_pos := fun _ _ _ _ _ => one_pos })⟩
end YangMills.Construction.PeriodicLattice
