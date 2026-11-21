import YangMills.Construction.TorusOrFourSpace.FunctionsOfSeveralPoints
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicSpace.PartialsAlgebra
open Kind
def Statement : Prop :=
  ∀ p : ℕ+,
    (∀ (α : CoordIndex p) (G : Coords p → ℂ) (k : Coords p),
      Coords.iterPartial α (fun x => G (x + k)) =
        fun x => Coords.iterPartial α G (x + k)) ∧
    (∀ (α : CoordIndex p) (G : Coords p → ℂ) (U : Set (Coords p)), IsOpen U →
      (∀ x ∈ U, G x = 0) → ∀ x ∈ U, Coords.iterPartial α G x = 0) ∧
    ∀ (ν : ℕ) (G H : Coords p → ℂ), Coords.ContPartialsUpTo ν G →
      Coords.ContPartialsUpTo ν H →
        (∀ a b : ℂ, Coords.ContPartialsUpTo ν (a • G + b • H)) ∧
        Coords.ContPartialsUpTo ν (G * H) ∧
        Coords.ContPartialsUpTo ν (fun x => ((G x).re : ℂ)) ∧
        Coords.ContPartialsUpTo ν (fun x => ((G x).im : ℂ)) ∧
        ∀ α : CoordIndex p, α.degree ≤ ν →
          Coords.iterPartial α (fun x => ((G x).re : ℂ)) =
              (fun x => ((Coords.iterPartial α G x).re : ℂ)) ∧
            Coords.iterPartial α (fun x => ((G x).im : ℂ)) =
              fun x => ((Coords.iterPartial α G x).im : ℂ)
end YangMills.Construction.PeriodicSpace.PartialsAlgebra
