import YangMills.Construction.HoleBesideASecondHole.HolesOffTheSpots
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.HoleSavings
open Classical in
def HoleData.componentsMeeting {F : BlockAverages.BlockFrame} {L : ℕ} {g : LumpContours.LumpGrid L}
    {a s θ : ℝ} {J₀ : ℕ} (D : HoleData F g a s θ J₀)
    (C : ℝ) (idx : Finset (Finset (F.Site F.depth)) → ℕ) (o : Finset (Finset (F.Site F.depth)) → F.Site F.depth)
    (Y : Finset (F.Site F.depth)) : Finset (Finset (Finset (F.Site F.depth))) :=
  (D.componentsAtCore C).filter fun k =>
    ∃ H ∈ Holes.componentHoles J₀ D.hotFineLumps k (idx k) o, (H.outerBox ∩ Y).Nonempty
open Classical in
def countsNearCutStatement : Prop :=
  ∀ (F : BlockAverages.BlockFrame) (g : LumpContours.LumpGrid F.blockSide) (a s θ C : ℝ) (J₀ : ℕ)
    (D : HoleData F g a s θ J₀)
    (idx : Finset (Finset (F.Site F.depth)) → ℕ) (o : Finset (Finset (F.Site F.depth)) → F.Site F.depth),
    Odd F.blockSide → HoleBounds.IsCubicTorus F 4096 → D.IsHoleFamily C idx o →
    (∀ X : Finset F.Cell,
      (D.componentsMeeting C idx o (LumpContours.cutBelow F.depth X)).card ≤ (D.nearbyFineLumps X).card) ∧
    (∀ y, ¬ LumpContours.IsCrowded J₀ D.hotFineLumps y → ∀ X ⊆ LumpContours.cellBall y 1,
      (D.componentsMeeting C idx o (LumpContours.cutBelow F.depth X)).card ≤ J₀) ∧
    ∀ X : Finset F.Cell, ((LumpContours.cutBonds X).filter fun c =>
      ¬ (LumpContours.nearbyLumps D.hotFineLumps c.1 = ∅ ∧
        LumpContours.nearbyLumps D.hotFineLumps (c.1 + BlockAverages.unitStep F.top c.2) = ∅)).card ≤
        9604 * (D.nearbyFineLumps X).card
end YangMills.Construction.HoleSavings
end
