import YangMills.Construction.HoleBesideASecondHole.PlacesOfAHole
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.HoleSavings
open YangMills.Construction.BlockAverages YangMills.Construction.LumpContours
open YangMills.Construction.HoleBounds
def quietCellCurvatureStatement : Prop :=
  ∃ K : ℝ, 0 < K ∧ ∃ L₀ : ℕ, ∀ (a C s θ : ℝ) (J₀ L : ℕ) (g : LumpGrid L) (F : BlockFrame)
    (D : HoleData F g a s θ J₀),
    1 ≤ a → 0 < C → 0 < s → Odd L → L₀ ≤ L → F.blockSide = L → IsCubicTorus F 4096 →
    K * C * s ^ 2 < (L : ℝ) ^ (-4 : ℤ) →
    ∀ y ∈ D.cells, y ∉ D.badCells C →
      ∑ p ∈ cutPlaquettes (D.chainSites ∩ cutBelow F.depth (cellBall y 1)), plaquetteDefect D.fineField p ^ 2 ≤
        K * C * s ^ 2
end YangMills.Construction.HoleSavings
end
