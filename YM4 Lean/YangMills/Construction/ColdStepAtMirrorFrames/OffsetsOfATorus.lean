import YangMills.Construction.ColdStepAtMirrorFrames.ExpansionOfAFamilyOnTori
import YangMills.Construction.ColdStepAtMirrorFrames.MirrorTorusAndFrames
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
open YangMills.Construction.BlockAverages
namespace YangMills.Construction
namespace ColdStepAtMirrorFrames
def IsTreeBondOffset (L : ℕ) (o : Fin 4 → ℤ) (i : Fin 4) : Prop :=
  ¬ o i = ((L : ℤ) - 1) / 2 ∧ ∀ l, i < l → o l = 0
def TorusOffsetsAboutCell : Prop :=
  ∀ (F : BlockFrame) (r : ℕ) (Y : F.Cell), Odd F.blockSide → (∀ i, 2 * r + 2 < F.extent i) →
    (∀ (h o : Fin 4 → ℤ) (i : Fin 4), o ∈ centredCube F.blockSide →
      enclosingCell (fineBondAt Y h o i).1 = Y + siteOfCoords F.top h ∧ cellOffset (fineBondAt Y h o i).1 = o) ∧
    (∀ (h h₁ o o₁ : Fin 4 → ℤ) (i i₁ : Fin 4), WithinRadius r h → WithinRadius r h₁ →
      o ∈ centredCube F.blockSide → o₁ ∈ centredCube F.blockSide →
      (fineBondAt Y h o i).1 = (fineBondAt Y h₁ o₁ i₁).1 → h = h₁ ∧ o = o₁) ∧
    (∀ h : Fin 4 → ℤ, WithinRadius r h →
      cellSupDist (Y + siteOfCoords F.top h) Y = (Finset.univ.sup fun i => (h i).natAbs) ∧
      cellSupDist Y (Y + siteOfCoords F.top h) = (Finset.univ.sup fun i => (h i).natAbs)) ∧
    (∀ (x : F.Site F.depth) (i : Fin 4),
      (x, i) ∈ chordBonds (finiteCells F) ↔ ¬ IsTreeBondOffset F.blockSide (cellOffset x) i) ∧
    (∀ x : F.Site F.depth, cellSupDist (enclosingCell x) Y ≤ r → ∃ h o : Fin 4 → ℤ, WithinRadius r h ∧
      o ∈ centredCube F.blockSide ∧ ∀ i, fineBondAt Y h o i = (x, i)) ∧
    (∀ (x : F.Site F.depth) (i : Fin 4),
      cellSupDist (enclosingCell (x + unitStep F.depth i)) Y ≤ cellSupDist (enclosingCell x) Y + 1) ∧
    (∀ y z : F.Cell, cellSupDist y z = cellSupDist z y) ∧
    (∀ y z : F.Cell, cellSupDist y z ≤ cellSupDist y Y + cellSupDist z Y) ∧
    (∀ x y : F.Site F.depth, F.blockSide * cellSupDist (enclosingCell y) (enclosingCell x) ≤ siteSupDist y x + F.blockSide)
end ColdStepAtMirrorFrames
end YangMills.Construction
end
