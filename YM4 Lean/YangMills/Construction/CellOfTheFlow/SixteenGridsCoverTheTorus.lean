import YangMills.Construction.CellOfTheFlow.WindowsOfACell
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.CellWindows
open TorusFields
def shiftedGridsCoverTorusStatement : Prop :=
  ∀ (n r : ℕ) [NeZero n] (G : CellGrid), G.Compatible n → Odd G.side → 2 ^ 7 * r ≤ G.side →
    ∀ x : TorusSite n, ∃ (A : Finset (Fin 4)) (κ : Fin 4 → ℤ),
      κ ∈ (G.shift A).indices n ∧ x ∈ interiorAtDepth (8 * r) ((G.shift A).cell n κ)
end YangMills.Construction.CellWindows
end
