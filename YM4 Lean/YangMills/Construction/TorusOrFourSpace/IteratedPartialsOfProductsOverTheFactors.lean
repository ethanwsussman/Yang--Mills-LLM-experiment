import YangMills.Construction.TorusOrFourSpace.FunctionsOfSeveralPoints
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicSpace.PartialDerivatives
open PeriodicSpace.Kind
def IteratedPartialsOfBlockProduct : Prop :=
  ∀ (p : ℕ+) (ν : ℕ) (g : Fin (p : ℕ) → Coords 1 → ℂ),
    (∀ i, Coords.ContPartialsUpTo ν (g i)) →
      Coords.ContPartialsUpTo ν (fun x : Coords p => ∏ i, g i (x.block i)) ∧
      ∀ α : CoordIndex p, α.degree ≤ ν →
        Coords.iterPartial α (fun x : Coords p => ∏ i, g i (x.block i)) =
          fun x => ∏ i : Fin (p : ℕ), Coords.iterPartial
            (fun j => α ⟨4 * (i : ℕ) + (j : ℕ), by
              have hi := i.2
              have hj := j.2
              simp only [PNat.one_coe] at hj
              omega⟩) (g i) (x.block i)
end YangMills.Construction.PeriodicSpace.PartialDerivatives
