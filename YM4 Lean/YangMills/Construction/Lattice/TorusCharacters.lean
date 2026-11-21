import YangMills.Construction.Lattice.PeriodicTorus
import Mathlib
set_option autoImplicit false
open Finset
noncomputable section
namespace YangMills.Construction.PeriodicLattice
def fourierCharacter {d N : ℕ} (m : Fin d → ℤ) (u : Torus d N) : ℂ :=
  ∏ μ, (AddCircle.toCircle (m μ • u μ) : ℂ)
def centeredFrequencies (d N : ℕ) : Finset (Fin d → ℤ) :=
  Fintype.piFinset fun _ => Ico (-((N : ℤ) / 2)) ((N : ℤ) / 2)
def CharactersOrthogonalOn (d : ℕ) {N : ℕ} (s : Mesh N) : Prop :=
  ∀ a : (Fin d → ℤ) → ℂ,
    s.h ^ d * ∑ x : GridPoint d s,
        ‖∑ m ∈ centeredFrequencies d N, a m * fourierCharacter m (x : Torus d N)‖ ^ 2 =
      (N : ℝ) ^ d * ∑ m ∈ centeredFrequencies d N, ‖a m‖ ^ 2
end YangMills.Construction.PeriodicLattice
