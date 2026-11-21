import YangMills.Construction.HoleBesideASecondHole.CutsLumpsBasesAndContours
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.LumpContours
open YangMills.Construction.BlockAverages
def TorusDistanceBlockLumpFacts : Prop :=
  ∀ F : BlockFrame, 0 < F.blockSide → (∀ i, 0 < F.extent i) →
    (∀ (j : ℕ) (x y : F.Site j), supDist x y = supDist y x) ∧
    (∀ (j : ℕ) (x y z : F.Site j), supDist x z ≤ supDist x y + supDist y z) ∧
    (∀ (j : ℕ) (m : ℕ) (X : Finset (F.Site j)) (x : F.Site j),
      x ∈ thicken m X ↔ ∃ y ∈ X, supDist y x ≤ m) ∧
    (Odd F.blockSide → ∀ (x : F.Site F.depth) (y : F.Cell),
      x ∈ sitesBelow F.depth y ↔ enclosingCell x = y) ∧
    (Odd F.blockSide → ∀ (m : ℕ) (x x' : F.Site F.depth), supDist x x' ≤ m * F.blockSide →
      cellSupDist (enclosingCell x) (enclosingCell x') ≤ m) ∧
    (∀ (x y z : F.Cell), cellSupDist x z ≤ cellSupDist x y + cellSupDist y z) ∧
    (∀ (x y : F.Cell), cellSupDist x y = cellSupDist y x) ∧
    (∀ (x : F.Cell) (r : ℕ) (y : F.Cell), y ∈ cellBall x r ↔ cellSupDist x y ≤ r) ∧
    (Odd F.blockSide → ∀ (g : LumpGrid F.blockSide) (x : F.Site F.depth),
      x ∈ lumpOf g x ∧ lumpOf g x ⊆ sitesBelow F.depth (enclosingCell x) ∧
        ∀ u ∈ lumpOf g x, ∀ v ∈ lumpOf g x, supDist u v < 2 ^ 15)
end YangMills.Construction.LumpContours
end
