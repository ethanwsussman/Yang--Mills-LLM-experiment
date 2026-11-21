import YangMills.Construction.TorusOrFourSpace.FunctionsOfSeveralPoints
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicSpace
open Kind
def ContPartialsIffContDiff : Prop :=
  ∀ (p : ℕ+) (ν : ℕ) (F : Coords p → ℂ),
    Coords.ContPartialsUpTo ν F ↔ ContDiff ℝ ν F
end YangMills.Construction.PeriodicSpace
