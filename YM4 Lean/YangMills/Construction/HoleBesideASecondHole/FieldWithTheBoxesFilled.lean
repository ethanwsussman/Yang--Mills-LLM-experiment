import YangMills.Construction.HoleBesideASecondHole.HolesOffTheSpots
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
open BlockAverages LumpContours HoleBounds
namespace HoleSavings
variable {F : BlockFrame}
def BondTouches {j : ℕ} (Z : Finset (F.Site j)) (b : F.Site j × Fin 4) : Prop :=
  b.1 ∈ Z ∨ b.1 + unitStep j b.2 ∈ Z
def boxFamily (J₀ : ℕ) (h : Finset (Finset (F.Site F.depth))) (Y : Finset F.Cell) :
    Finset (Finset (F.Site F.depth)) := by
  classical exact Y.biUnion fun y =>
    (excludedBoxes J₀ h y).filter fun Z => (Z ∩ sitesBelow F.depth y).Nonempty
def boxShell (Z : Finset (F.Site F.depth)) : Finset (F.Site F.depth) := thicken 1 Z \ Z
namespace HoleData
variable {L : ℕ} {g : LumpGrid L} {a s θ : ℝ} {J₀ : ℕ} (D : HoleData F g a s θ J₀)
def coreBoxes (C : ℝ) : Finset (Finset (F.Site F.depth)) :=
  boxFamily J₀ D.hotFineLumps (D.coreCells C 5)
open Classical in
structure IsFilledField (C CJ : ℝ) (idx : Finset (Finset (F.Site F.depth)) → ℕ)
    (o : Finset (Finset (F.Site F.depth)) → F.Site F.depth) (Wt : F.GaugeField F.depth) : Prop where
  mem_excludedBoxes_of_adj : ∀ y ∈ D.coreCells C 5, ∀ y' ∈ D.coreCells C 5, cellSupDist y y' ≤ 1 →
    ∀ Z ∈ excludedBoxes J₀ D.hotFineLumps y,
    ((Z ∩ sitesBelow F.depth y).Nonempty ∨ (Z ∩ sitesBelow F.depth y').Nonempty) →
      Z ∈ excludedBoxes J₀ D.hotFineLumps y'
  pairwise_apart : ∀ Z ∈ D.coreBoxes C, ∀ Z' ∈ D.coreBoxes C, Z ≠ Z' → ¬ AreWithin 2 Z Z'
  exists_hole_superset : ∀ Z ∈ D.coreBoxes C, ∃ H ∈ D.holesAt C idx o, Z ⊆ H.innerBox
  exists_gauge : ∃ G : F.Site F.depth → UnitQuaternion, ∀ Z ∈ D.coreBoxes C, (∀ x ∈ Z, G x = 1) ∧
    (∀ b : F.Site F.depth × Fin 4, BondTouches Z b → gaugeTransform G Wt b.1 b.2 = 1) ∧
    ∀ b : F.Site F.depth × Fin 4, b.1 ∈ boxShell Z → b.1 + unitStep F.depth b.2 ∈ boxShell Z →
      ‖((gaugeTransform G D.fineField b.1 b.2 : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ CJ * s
  eq_of_not_touches : ∀ b : F.Site F.depth × Fin 4, (∀ Z ∈ D.coreBoxes C, ¬ BondTouches Z b) →
    Wt b.1 b.2 = D.fineField b.1 b.2
  curvature_le : ∀ y ∈ D.coreCells C 5, ∀ y' ∈ D.coreCells C 5, cellSupDist y y' ≤ 1 →
    ∑ p ∈ cutPlaquettes (sitesBelow F.depth y ∪ sitesBelow F.depth y'), plaquetteDefect Wt p ^ 2 ≤ CJ * s ^ 2
  disjoint_of_nearbyLumps_empty : ∀ y ∈ D.coreCells C 5, nearbyLumps D.hotFineLumps y = ∅ →
    (∀ H ∈ D.holesAt C idx o, H.outerBox ∩ sitesBelow F.depth y = ∅) ∧
      ∀ Z ∈ D.coreBoxes C, Z ∩ sitesBelow F.depth y = ∅
end HoleData
def filledFieldStatement : Prop :=
  ∀ (J₀ : ℕ) (a C : ℝ), 1 ≤ J₀ → 1 ≤ a → 0 < C → ∃ CJ : ℝ, 0 < CJ ∧ ∃ L₀ : ℕ,
    ∀ L : ℕ, Odd L → L₀ ≤ L → ∀ g : LumpGrid L, ∃ s₀ : ℝ, 0 < s₀ ∧ ∀ s : ℝ, 0 < s → s ≤ s₀ →
      ∀ (θ : ℝ) (F : BlockFrame) (D : HoleData F g a s θ J₀), F.blockSide = L → IsCubicTorus F 4096 →
        ∀ (idx : Finset (Finset (F.Site F.depth)) → ℕ) (o : Finset (Finset (F.Site F.depth)) → F.Site F.depth),
          D.IsHoleFamily C idx o → ∃ Wt : F.GaugeField F.depth, D.IsFilledField C CJ idx o Wt
end HoleSavings
end YangMills.Construction
end
