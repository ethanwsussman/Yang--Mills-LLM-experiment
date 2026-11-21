import YangMills.Construction.ColdStepAtMirrorFrames.MeansFrozenOnCommonBondsFormForm
import YangMills.Construction.ColdStepAtMirrorFrames.MirrorTorusAndFrames
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages
namespace YangMills.Construction.ColdStepAtMirrorFrames
variable {F F' : BlockFrame}
def chordBondCell (F : BlockFrame) (b : ↥(chordBonds (finiteCells F))) : F.Cell := enclosingCell b.1.1
def cellDistReal (F : BlockFrame) (y z : F.Cell) : ℝ := cellSupDist y z
open Classical in
def commonBondOffsets (Y : F.Cell) (Y' : F'.Cell) (R : ℕ) :
    Finset ((Fin 4 → ℤ) × (Fin 4 → ℤ) × Fin 4) :=
  (centredCube (2 * R + 1) ×ˢ centredCube F.blockSide ×ˢ (Finset.univ : Finset (Fin 4))).filter fun q =>
    fineBondAt Y q.1 q.2.1 q.2.2 ∈ chordBonds (finiteCells F) ∧
      fineBondAt Y' q.1 q.2.1 q.2.2 ∈ chordBonds (finiteCells F')
def commonBondLeft (Y : F.Cell) (Y' : F'.Cell) (R : ℕ) (q : ↥(commonBondOffsets Y Y' R)) :
    ↥(chordBonds (finiteCells F)) :=
  ⟨fineBondAt Y q.1.1 q.1.2.1 q.1.2.2, (Finset.mem_filter.mp q.2).2.1⟩
def commonBondRight (Y : F.Cell) (Y' : F'.Cell) (R : ℕ) (q : ↥(commonBondOffsets Y Y' R)) :
    ↥(chordBonds (finiteCells F')) :=
  ⟨fineBondAt Y' q.1.1 q.1.2.1 q.1.2.2, (Finset.mem_filter.mp q.2).2.2⟩
def offsetCell (Y : F.Cell) (Q : ℕ) (c : ↥(centredCube (2 * Q + 1))) : F.Cell := Y + siteOfCoords F.top c.1
structure HasCommonBonds (Y : F.Cell) (Y' : F'.Cell) (r : ℕ) : Prop where
  injective_left : Function.Injective (commonBondLeft Y Y' (r / 2))
  injective_right : Function.Injective (commonBondRight Y Y' (r / 2))
  injective_offset : Function.Injective (offsetCell Y (r / 8))
  injective_offset' : Function.Injective (offsetCell Y' (r / 8))
  dist_eq : ∀ q q', cellDistReal F (chordBondCell F (commonBondLeft Y Y' (r / 2) q))
      (chordBondCell F (commonBondLeft Y Y' (r / 2) q')) =
    cellDistReal F' (chordBondCell F' (commonBondRight Y Y' (r / 2) q))
      (chordBondCell F' (commonBondRight Y Y' (r / 2) q'))
  dist_centre_eq : ∀ q, cellDistReal F Y (chordBondCell F (commonBondLeft Y Y' (r / 2) q)) =
    cellDistReal F' Y' (chordBondCell F' (commonBondRight Y Y' (r / 2) q))
  far_of_not_common : ∀ b, b ∉ Set.range (commonBondLeft Y Y' (r / 2)) →
    (r : ℝ) / 2 ≤ cellDistReal F Y (chordBondCell F b)
  far_of_not_common' : ∀ b, b ∉ Set.range (commonBondRight Y Y' (r / 2)) →
    (r : ℝ) / 2 ≤ cellDistReal F' Y' (chordBondCell F' b)
  offset_near : ∀ c, cellDistReal F Y (offsetCell Y (r / 8) c) ≤ (r : ℝ) / 8
  far_of_not_offset : ∀ Z, Z ∉ Set.range (offsetCell Y (r / 8)) → (r : ℝ) / 8 ≤ cellDistReal F Y Z
  far_of_not_offset' : ∀ Z, Z ∉ Set.range (offsetCell Y' (r / 8)) → (r : ℝ) / 8 ≤ cellDistReal F' Y' Z
def commonBondsOfTwoTori : Prop :=
  ∀ L : ℕ, Odd L → (∀ κ : ℝ, 0 < κ → ∃ S : ℝ, ∀ (F : BlockFrame) (n : ℕ) [Fintype F.Cell], F.blockSide = L → 2 ≤ n →
      (∀ i, F.extent i = n) → IsDecayingPlacement κ S (chordBondCell F) (cellDistReal F)) ∧
    ∀ (F F' : BlockFrame) (Y : F.Cell) (Y' : F'.Cell) (r n n' : ℕ), F.blockSide = L → F'.blockSide = L →
      (∀ i, F.extent i = n) → (∀ i, F'.extent i = n') → 2 * r + 2 < n → 2 * r + 2 < n' →
      HasCommonBonds Y Y' r
end YangMills.Construction.ColdStepAtMirrorFrames
end
