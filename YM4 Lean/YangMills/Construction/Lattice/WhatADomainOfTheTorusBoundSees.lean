import YangMills.Construction.Lattice.LevelsPresentOnTheTorus
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.TorusBound.Setup
variable (D : Setup)
def SeesRegion (j : ℕ) (X A : Set D.Torus) : Prop :=
  ∃ p ∈ D.plaquettesOfThickened j X, p.barycenter ∈ A
def SeesSupport {E : Type*} [Zero E] (j : ℕ) (X : Set D.Torus) (f : D.Torus → E) : Prop :=
  D.SeesRegion j X {y | f y ≠ 0}
end YangMills.Construction.TorusBound.Setup
