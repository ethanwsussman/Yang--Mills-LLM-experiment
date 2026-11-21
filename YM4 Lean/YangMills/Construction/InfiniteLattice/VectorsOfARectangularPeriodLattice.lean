import YangMills.Construction.InfiniteLattice.FramesRectangularPeriodLatticesAndTheBox
import Mathlib
set_option autoImplicit false
open scoped Matrix
noncomputable section
namespace YangMills.Construction.InfiniteLattice
open YangMills.Construction.NormalFamilies
def RectangularPeriodVectors : Prop :=
  ∀ (F : OrthogonalNormalFrame) (s : Fin 4 → ℕ+),
    (∀ i j, F.vec i ⬝ᵥ F.sideVec s j = if i = j then ((s i : ℕ) : ℝ) else 0) ∧
      ∀ i, F.sideVec s i ∈ latticeSubgroup 1 ↔ F.lengthSq i = 1 ∨ Even (s i : ℕ)
end YangMills.Construction.InfiniteLattice
