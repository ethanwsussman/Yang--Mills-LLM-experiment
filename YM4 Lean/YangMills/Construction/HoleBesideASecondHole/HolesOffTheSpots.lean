import YangMills.Construction.HoleBesideASecondHole.HolesAtGrowingScales
import YangMills.Construction.HoleBesideASecondHole.PlacesOfAHole
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
open BlockAverages LumpContours Holes HoleBounds
namespace HoleSavings
namespace HoleData
variable {F : BlockFrame} {L : ℕ} {g : LumpGrid L} {a s θ : ℝ} {J₀ : ℕ} (D : HoleData F g a s θ J₀)
def componentsAtCore (C : ℝ) : Finset (Finset (Finset (F.Site F.depth))) :=
  componentsNearCells J₀ L D.hotFineLumps (D.coreCells C 3)
def holesAt (C : ℝ) (idx : Finset (Finset (F.Site F.depth)) → ℕ)
    (o : Finset (Finset (F.Site F.depth)) → F.Site F.depth) : Finset (Hole F) :=
  allHoles J₀ L D.hotFineLumps (D.coreCells C 3) idx o
open Classical in
structure IsHoleFamily (C : ℝ) (idx : Finset (Finset (F.Site F.depth)) → ℕ)
    (o : Finset (Finset (F.Site F.depth)) → F.Site F.depth) : Prop where
  index_stable : ∀ k ∈ D.componentsAtCore C,
    idx k < topScaleIndex J₀ L ∧ IsStableIndex J₀ D.hotFineLumps k (idx k)
  card_lt_of_mem_core : ∀ k ∈ D.componentsAtCore C, ∀ y ∈ D.coreCells C 3, ∀ l ∈ k, l ⊆ sitesBelow F.depth y →
    k.card < J₀ ∧ ∀ l' ∈ k, l' ⊆ cutBelow F.depth (cellBall y 1)
  radius_bounds : ∀ H ∈ D.holesAt C idx o, 99 ≤ H.radius ∧ 100 * H.radius ^ 2 ≤ L
  collar_subset : ∀ H ∈ D.holesAt C idx o, ∀ l ∈ H.lumps, lumpCollar l ⊆ H.innerBox
  outer_subset : ∀ H ∈ D.holesAt C idx o, ∀ l ∈ H.lumps, H.outerBox ⊆ thicken (3 * H.radius) l
  not_within_other : ∀ H ∈ D.holesAt C idx o, ∀ l ∈ D.hotFineLumps, l ∉ H.lumps →
    ¬ AreWithin 1 H.outerBox (lumpNeighbourhood l)
  annulus_apart : ∀ H ∈ D.holesAt C idx o, ∀ l ∈ D.hotFineLumps,
    ¬ AreWithin 1 H.annulus (lumpNeighbourhood l)
  walls : ∀ H ∈ D.holesAt C idx o, ∀ x ∈ thicken (L / 2) H.outerBox,
    enclosingCell x ∈ D.cells ∧ ∀ z ∈ torusCells F \ D.cells, 2 ≤ cellSupDist (enclosingCell x) z
  pairwise_apart : ∀ H ∈ D.holesAt C idx o, ∀ H' ∈ D.holesAt C idx o, H ≠ H' →
    ¬ AreWithin (5 * max H.radius H'.radius) H.outerBox H'.outerBox
  exists_hole_of_core : ∀ l ∈ D.hotFineLumps, ∀ y ∈ D.coreCells C 3, l ⊆ sitesBelow F.depth y →
    ∃ H ∈ D.holesAt C idx o, l ∈ H.lumps
  exists_hole_of_meets : ∀ l ∈ D.hotFineLumps, ∀ y ∈ D.coreCells C 4,
    (lumpNeighbourhood l ∩ sitesBelow F.depth y).Nonempty → ∃ H ∈ D.holesAt C idx o, l ∈ H.lumps
  closed_under_nearby : ∀ H ∈ D.holesAt C idx o, ∀ l ∈ H.lumps, ∀ l' ∈ D.hotFineLumps,
    AreWithin (holeScale J₀ 1) (lumpNeighbourhood l) (lumpNeighbourhood l') → l' ∈ H.lumps
  few_near_uncrowded : ∀ y, ¬ IsCrowded J₀ D.hotFineLumps y →
    ((D.holesAt C idx o).filter fun H => (H.outerBox ∩ cutBelow F.depth (cellBall y 1)).Nonempty).card < J₀
  annulus_energy_le : ∀ k ∈ D.componentsAtCore C,
    (∑ H ∈ componentHoles J₀ D.hotFineLumps k (idx k) o, H.annulusEnergy (D.chain 0)) *
      ((topScaleIndex J₀ L : ℝ) - J₀) ≤ C * s ^ 2
open Classical in
structure IsHoleFillingChain (C C₀ : ℝ) (idx : Finset (Finset (F.Site F.depth)) → ℕ)
    (o : Finset (Finset (F.Site F.depth)) → F.Site F.depth) (U₂ : F.FieldChain) : Prop where
  top_eq_off_holes : ∀ b ∈ cutBonds (cutBelow F.depth (D.coreCells C 4)),
    b.1 ∉ holeSupport (D.holesAt C idx o) →
    b.1 + unitStep F.depth b.2 ∉ holeSupport (D.holesAt C idx o) →
    U₂ F.depth b.1 b.2 = D.fineField b.1 b.2
  energy_le : ∀ Y ⊆ cutBelow F.depth (D.coreCells C 4),
    cutChainEnergy a F.depth Y U₂ ≤
      cutChainEnergy a F.depth (Y \ lumpsNeighbourhood D.hotFineLumps) D.chain +
      C₀ * C * s ^ 2 / ((topScaleIndex J₀ L : ℝ) - J₀) *
        ((D.componentsAtCore C).filter fun k =>
          ∃ H ∈ componentHoles J₀ D.hotFineLumps k (idx k) o, (H.outerBox ∩ Y).Nonempty).card
  curvature_le : ∀ y ∈ D.coreCells C 5,
    ∑ p ∈ cutPlaquettes (cutBelow F.depth (cellBall y 1 ∩ D.coreCells C 4)),
      plaquetteDefect (U₂ F.depth) p ^ 2 ≤ C₀ * C * s ^ 2
end HoleData
end HoleSavings
namespace HoleFilling
open HoleSavings
def holesAwayFromBadCellsStatement : Prop :=
  ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ J₀ : ℕ, 1 ≤ J₀ →
    (∀ m : ℕ, ∃ L₁ : ℕ, ∀ L : ℕ, L₁ ≤ L → m ≤ topScaleIndex J₀ L) ∧
    ∃ L₀ : ℕ, ∀ L : ℕ, Odd L → L₀ ≤ L → 2 * J₀ ≤ topScaleIndex J₀ L ∧
      ∀ (g : LumpGrid L) (a C : ℝ), 1 ≤ a → 0 < C → ∃ s₀ : ℝ, 0 < s₀ ∧ ∀ s : ℝ, 0 < s → s ≤ s₀ →
        ∀ (θ : ℝ) (F : BlockFrame) (D : HoleData F g a s θ J₀), F.blockSide = L → IsCubicTorus F 4096 →
          ∃ (idx : Finset (Finset (F.Site F.depth)) → ℕ) (o : Finset (Finset (F.Site F.depth)) → F.Site F.depth)
            (U₂ : F.FieldChain), D.IsHoleFamily C idx o ∧ D.IsHoleFillingChain C C₀ idx o U₂
end HoleFilling
end YangMills.Construction
end
