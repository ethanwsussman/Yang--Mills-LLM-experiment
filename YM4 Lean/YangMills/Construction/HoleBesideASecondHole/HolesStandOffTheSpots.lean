import YangMills.Construction.HoleBesideASecondHole.HolesOffTheSpots
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.HoleFilling
def holeFamilyExistsStatement : Prop :=
  ∀ J₀ : ℕ, 1 ≤ J₀ → ∃ L₀ : ℕ, ∀ L : ℕ, Odd L → L₀ ≤ L → 2 * J₀ ≤ Holes.topScaleIndex J₀ L ∧
    ∀ (g : LumpContours.LumpGrid L) (a C s θ : ℝ) (F : BlockAverages.BlockFrame)
      (D : HoleSavings.HoleData F g a s θ J₀), 1 ≤ a → F.blockSide = L →
      (∀ i, 64 ≤ F.extent i) →
      ∃ (idx : Finset (Finset (F.Site F.depth)) → ℕ) (o : Finset (Finset (F.Site F.depth)) → F.Site F.depth),
        D.IsHoleFamily C idx o
end YangMills.Construction.HoleFilling
end
