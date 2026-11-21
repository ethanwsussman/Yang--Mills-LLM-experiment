import YangMills.Construction.HoleBesideASecondHole.PlacesOfAHole
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages LumpContours HoleSavings HoleBounds
namespace HoleSavings
def CrowdedCellsBound : Prop :=
  ∀ (F : BlockFrame) (L : ℕ) (g : LumpGrid L) (a s θ : ℝ) (J₀ : ℕ) (D : HoleData F g a s θ J₀),
    F.blockSide = L → Odd L → IsCubicTorus F 4096 → J₀ * (D.crowdedCells).card ≤ 625 * D.hotFineLumps.card
end HoleSavings
end YangMills.Construction
end
