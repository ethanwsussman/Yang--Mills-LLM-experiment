import YangMills.Construction.ColdChainAtEveryLevel.ComparisonOfAgreeingPairsProof
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BlockAverages.SiteOffsets
open Offsets TwistedTops
variable {F F' : BlockFrame} {S : Finset F.Cell} {S' : Finset F'.Cell} {Y : F.Cell} {Y' : F'.Cell}
theorem translateSite_siteAtOffset (hL : 0 < F.blockSide) {j : ℕ} (hj : j ≤ F.top) (Y : F.Cell) (Y' : F'.Cell)
    {ρ : ℕ} (hs : ∀ i, F.extent i = 0 ∨ 2 * ρ + 2 < F.extent i) {p : Fin 4 → ℤ}
    (hp : WithinCellRadius F.blockSide F.top ρ j p) :
    translateSite Y Y' (siteAtOffset j Y p) = siteAtOffset j Y' p := by apply _root_.YangMills.Construction.BlockAverages.AgreeingPairs.translateSite_siteAtOffset <;> assumption
theorem withinCellRadius_add_single (hL : 0 < F.blockSide) {j ρ : ℕ} (hj : j ≤ F.top) {p : Fin 4 → ℤ}
    (hp : WithinCellRadius F.blockSide F.top ρ j p) (i : Fin 4) :
    WithinCellRadius F.blockSide F.top (ρ + 1) j (p + Pi.single i 1) := by apply _root_.YangMills.Construction.BlockAverages.AgreeingPairs.withinCellRadius_add_single <;> assumption
theorem translateSite_mem_innerBonds (hodd : Odd F.blockSide) (hL' : F'.blockSide = F.blockSide)
    (ht' : F'.depth = F.depth) {j : ℕ} (hj : j ≤ F.top) {d : ℕ}
    (hside : ∀ i, F.extent i = 0 ∨ 2 * (d + 2) + 2 < F.extent i)
    (hS : ∀ q : Fin 4 → ℤ, WithinCellRadius F.blockSide F.top (d + 2) j q →
      (siteAtOffset j Y q ∈ sitesOfCells S j ↔ siteAtOffset j Y' q ∈ sitesOfCells S' j))
    {x : F.Site j × Fin 4} (hx : x ∈ innerBonds S j) (hd : cellSupDist (enclosingCell x.1) Y ≤ d) :
    (translateSite Y Y' x.1, x.2) ∈ innerBonds S' j := by apply _root_.YangMills.Construction.BlockAverages.AgreeingPairs.translate_mem_innerBonds <;> assumption
end YangMills.Construction.BlockAverages.SiteOffsets
end
