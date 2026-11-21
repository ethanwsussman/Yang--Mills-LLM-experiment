import YangMills.Construction.TorusOrFourSpace.FunctionsOfSeveralPoints
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicSpace.PartialDerivatives
open PeriodicSpace.Kind
def IteratedPartialsCompose : Prop :=
  ∀ (p : ℕ+) (ν : ℕ) (G : Coords p → ℂ), Coords.ContPartialsUpTo ν G →
    ∀ α : CoordIndex p, α.degree ≤ ν →
      Coords.ContPartialsUpTo (ν - α.degree) (Coords.iterPartial α G) ∧
      ∀ β : CoordIndex p, β.degree ≤ ν - α.degree →
        Coords.iterPartial β (Coords.iterPartial α G) = Coords.iterPartial (α + β) G
end YangMills.Construction.PeriodicSpace.PartialDerivatives
