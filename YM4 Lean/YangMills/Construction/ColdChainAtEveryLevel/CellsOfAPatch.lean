import YangMills.Construction.ColdStepAtMirrorFrames.MeansOverContoursOfAFormForm
import YangMills.Construction.ColdChainAtEveryLevel.BoundsOfTheReferenceProof
import YangMills.Construction.ColdChainAtEveryLevel.SitesOfAPatch
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BlockAverages
open YangMills.Construction.BlockAverages.PatchLocality YangMills.Construction.LatticePaths
variable {F : BlockFrame} {S : Finset F.Cell} {z : F.Cell}
open Classical in
def patchCells (S : Finset F.Cell) (z : F.Cell) : Finset F.Cell :=
  S.filter fun y => baseSite y ∈ patchBaseSites S z
theorem baseSite_eq_cellCentre_zero (y : F.Cell) : baseSite y = cellCentre 0 y := by apply _root_.YangMills.Construction.ReferenceBounds.baseSite_cell <;> assumption
theorem zero_mem_centredCube {M : ℕ} (hM : Odd M) :
    (0 : YangMills.Construction.LatticeFractionalIntegration.Lattice4) ∈ centredCube M := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.zero_mem_centredCube <;> assumption
theorem mem_sitesOfCells_patchCells_iff (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    (hsign : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1) {j : ℕ} (hj : j ≤ F.top)
    {x : F.Site j} :
    x ∈ sitesOfCells (patchCells S z) j ↔ x ∈ sitesOfCells S j ∧ baseSite x ∈ patchBaseSites S z := by
  classical
  have h0 : (0 : YangMills.Construction.LatticeFractionalIntegration.Lattice4) ∈ centredCube (F.blockSide ^ j) :=
    zero_mem_centredCube hodd.pow
  have h0top : (0 : YangMills.Construction.LatticeFractionalIntegration.Lattice4) ∈
      centredCube (F.blockSide ^ F.top) := zero_mem_centredCube hodd.pow
  constructor
  · intro hx
    obtain ⟨y, hy, h, hh, rfl⟩ := mem_sitesOfCells.1 hx
    obtain ⟨hyS, hyP⟩ := Finset.mem_filter.1 hy
    refine ⟨mem_sitesOfCells.2 ⟨y, hyS, h, hh, rfl⟩, ?_⟩
    have hxy : cellCentre j y + siteOfCoords j h ∈ sitesOfCells ({y} : Finset F.Cell) j :=
      mem_sitesOfCells.2 ⟨y, Finset.mem_singleton_self y, h, hh, rfl⟩
    obtain ⟨y', hy', h', hh', e⟩ := exists_cell_of_mem_sitesOfCells hodd hj hxy h0
    rw [Finset.mem_singleton.1 hy'] at e
    rw [siteOfCoords_zero, add_zero] at e
    rw [e]
    have hc : cellCentre 0 y + siteOfCoords 0
        (0 : YangMills.Construction.LatticeFractionalIntegration.Lattice4) ∈ patchBaseSites S z := by
      rw [siteOfCoords_zero, add_zero, ← baseSite_eq_cellCentre_zero]
      exact hyP
    exact mem_patchBaseSites_of_same_cell hamb hodd hsign h0top hh' hc
  · rintro ⟨hx, hb⟩
    obtain ⟨y, hy, h, hh, rfl⟩ := mem_sitesOfCells.1 hx
    have hxy : cellCentre j y + siteOfCoords j h ∈ sitesOfCells ({y} : Finset F.Cell) j :=
      mem_sitesOfCells.2 ⟨y, Finset.mem_singleton_self y, h, hh, rfl⟩
    obtain ⟨y', hy', h', hh', e⟩ := exists_cell_of_mem_sitesOfCells hodd hj hxy h0
    rw [Finset.mem_singleton.1 hy'] at e
    rw [siteOfCoords_zero, add_zero] at e
    rw [e] at hb
    have hc := mem_patchBaseSites_of_same_cell hamb hodd hsign hh' h0top hb
    rw [siteOfCoords_zero, add_zero, ← baseSite_eq_cellCentre_zero] at hc
    exact mem_sitesOfCells.2 ⟨y, Finset.mem_filter.2 ⟨hy, hc⟩, h, hh, rfl⟩
theorem innerBonds_patchCells (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    (hsign : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1) {j : ℕ} (hj : j ≤ F.top) :
    innerBonds (patchCells S z) j = patchInnerBonds S z j := by
  classical
  ext b
  simp only [innerBonds, patchInnerBonds, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true,
    mem_sitesOfCells_patchCells_iff hamb hodd hsign hj]
  tauto
theorem mem_patchFitBonds_of_mem_innerBonds (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    (hsign : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1) {j : ℕ} (hj : j + 1 ≤ F.top)
    {c : F.Site (j + 1) × Fin 4} (hc : c ∈ innerBonds (patchCells S z) (j + 1)) :
    c ∈ patchFitBonds S z j := by
  classical
  have h1 := (Finset.mem_product.1 (Finset.mem_filter.1 hc).1).1
  have h2 := (Finset.mem_filter.1 hc).2
  have hb : c ∈ innerBonds S (j + 1) := by
    have e := innerBonds_patchCells hamb hodd hsign hj
    rw [e] at hc
    exact (Finset.mem_filter.1 hc).1
  have key : ∀ x : F.Site (j + 1), x ∈ sitesOfCells (patchCells S z) (j + 1) →
      ∀ h ∈ centredCube (F.blockSide ^ (j + 1)), baseSite x + siteOfCoords 0 h ∈ patchBaseSites S z := by
    intro x hx h hh
    obtain ⟨y, hy, h', hh', e⟩ := exists_cell_of_mem_sitesOfCells hodd hj hx hh
    rw [e]
    have hyP := (Finset.mem_filter.1 hy).2
    have hc0 : cellCentre 0 y + siteOfCoords 0
        (0 : YangMills.Construction.LatticeFractionalIntegration.Lattice4) ∈ patchBaseSites S z := by
      rw [siteOfCoords_zero, add_zero, ← baseSite_eq_cellCentre_zero]
      exact hyP
    exact mem_patchBaseSites_of_same_cell hamb hodd hsign (zero_mem_centredCube hodd.pow) hh' hc0
  exact Finset.mem_filter.2 ⟨hb, fun h hh => ⟨key _ h1 h hh, key _ h2 h hh⟩⟩
theorem card_patchCells_le (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    (hsign : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1) : (patchCells S z).card ≤ 47 ^ 4 := by
  classical
  have := card_le_of_cellSupDist_le z 23 (patchCells S z) (fun y hy => by
    have hb := (Finset.mem_filter.1 hy).2
    rw [baseSite_eq_cellCentre_zero] at hb
    exact cellSupDist_le_of_mem_patchBaseSites hamb hodd hsign hb (zero_mem_centredCube hodd.pow)
      (by rw [siteOfCoords_zero, add_zero]))
  simpa using this
end YangMills.Construction.BlockAverages
end
