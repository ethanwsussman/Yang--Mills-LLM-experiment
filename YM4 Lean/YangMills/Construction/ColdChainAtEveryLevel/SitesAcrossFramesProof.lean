import YangMills.Construction.ColdChainAtEveryLevel.SeminormsOfCoordinates
import YangMills.Construction.ColdChainAtEveryLevel.SitesAcrossFrames
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.FrameComparison
open BlockAverages BlockAverages.Offsets
variable {F F' : BlockFrame}
theorem siteAtOffset_mem_sitesOfCells_of_agree (hodd : Odd F.blockSide) (hL' : F'.blockSide = F.blockSide)
    (ht : F'.depth = F.depth) {S : Finset F.Cell} {S' : Finset F'.Cell}
    {Y : F.Cell} {Y' : F'.Cell} {r ρ j : ℕ} (hj : j ≤ F.top) (hρ : ρ + 2 ≤ r)
    (hbox : ∀ h, WithinRadius r h → Y + siteOfCoords F.top h ∈ S → Y' + siteOfCoords F'.top h ∈ S')
    {p : Fin 4 → ℤ} (hp : WithinCellRadius F.blockSide F.top ρ j p)
    (hx : siteAtOffset j Y p ∈ sitesOfCells S j) : siteAtOffset j Y' p ∈ sitesOfCells S' j := by
  have hn : F'.top = F.top := by
    show F'.depth + 1 = F.depth + 1
    rw [ht]
  set N : ℤ := (F.blockSide : ℤ) ^ (F.top - j) with hN
  have hL0 : (0 : ℤ) < F.blockSide := by exact_mod_cast hodd.pos
  have hN0 : 0 < N := pow_pos hL0 _
  have hNodd : Odd N := by
    have : Odd (F.blockSide : ℤ) := by exact_mod_cast hodd
    exact this.pow
  set a : Fin 4 → ℤ := fun i => (p i + (N - 1) / 2) / N with ha
  set h : Fin 4 → ℤ := fun i => p i - N * a i with hh
  have hN2 : 2 * ((N - 1) / 2) = N - 1 := by
    obtain ⟨q, hq⟩ := hNodd
    rw [hq]
    omega
  have hrange : ∀ i, -((N - 1) / 2) ≤ h i ∧ h i ≤ (N - 1) / 2 := by
    intro i
    have e1 := Int.emod_add_mul_ediv (p i + (N - 1) / 2) N
    have e2 := Int.emod_nonneg (p i + (N - 1) / 2) hN0.ne'
    have e3 := Int.emod_lt_of_pos (p i + (N - 1) / 2) hN0
    simp only [hh, ha]
    constructor <;> omega
  have hcube : h ∈ centredCube (F.blockSide ^ (F.top - j)) := by
    rw [LatticePaths.mem_centredCube_iff]
    intro i
    have e : ((F.blockSide ^ (F.top - j) : ℕ) : ℤ) = N := by
      simp [hN]
    rw [e]
    exact hrange i
  have hpe : (fun i => (F.blockSide : ℤ) ^ (F.top - j) * a i) + h = p := by
    funext i
    simp [hh, hN]
  have hx1 : siteAtOffset j Y p = cellCentre j (Y + siteOfCoords F.top a) + siteOfCoords j h := by
    unfold YangMills.Construction.BlockAverages.Offsets.siteAtOffset
    rw [cellCentre_add j hj, add_assoc, ← siteOfCoords_add, hpe]
  have hcell : enclosingCell (siteAtOffset j Y p) = Y + siteOfCoords F.top a := by
    rw [hx1]
    exact CoordinateSeminorms.enclosingCell_cellCentre_add hodd _ h hcube
  have hmem : Y + siteOfCoords F.top a ∈ S := by
    rw [← hcell]
    exact CoordinateSeminorms.enclosingCell_mem hodd hx
  have hpb : ∀ i, |p i| ≤ (ρ : ℤ) * N := by
    intro i
    have h1 := hp i
    have e : (F.blockSide : ℤ) ^ F.top = (F.blockSide : ℤ) ^ j * N := by
      rw [hN, ← pow_add]
      congr 1
      omega
    rw [e] at h1
    have h0 : (0 : ℤ) < (F.blockSide : ℤ) ^ j := pow_pos hL0 _
    have h2 : (F.blockSide : ℤ) ^ j * |p i| ≤ (F.blockSide : ℤ) ^ j * ((ρ : ℤ) * N) := by
      refine h1.trans (le_of_eq ?_)
      ring
    exact le_of_mul_le_mul_left h2 h0
  have hab : WithinRadius r a := by
    intro i
    have h1 := hpb i
    have h2 := hrange i
    have e : N * a i = p i - h i := by
      simp only [hh]
      ring
    have h3 : |N * a i| ≤ |p i| + |h i| := by
      rw [e]
      exact abs_sub _ _
    have h5 : |h i| ≤ N := by
      rw [abs_le]
      constructor <;> omega
    rw [abs_mul, abs_of_pos hN0] at h3
    have h6 : N * |a i| ≤ N * ((ρ : ℤ) + 2) := by nlinarith
    have h7 := le_of_mul_le_mul_left h6 hN0
    have h8 : ((ρ + 2 : ℕ) : ℤ) ≤ (r : ℤ) := by exact_mod_cast hρ
    push_cast at h8
    omega
  have hmem' := hbox a hab hmem
  have hhc' : h ∈ centredCube (F'.blockSide ^ (F'.top - j)) := by
    rw [hL', hn]
    exact hcube
  have hx2 : siteAtOffset j Y' p = cellCentre j (Y' + siteOfCoords F'.top a) + siteOfCoords j h := by
    unfold YangMills.Construction.BlockAverages.Offsets.siteAtOffset
    rw [cellCentre_add j (hn ▸ hj), add_assoc, ← siteOfCoords_add]
    have e : (fun i => (F'.blockSide : ℤ) ^ (F'.top - j) * a i) + h = p := by
      rw [hL', hn]
      exact hpe
    rw [e]
  rw [hx2]
  exact mem_sitesOfCells.2 ⟨_, hmem', h, hhc', rfl⟩
theorem sitesOfCellsAcrossFrames_holds : sitesOfCellsAcrossFramesStatement := by
  intro F F' S S' V V' Y Y' r ρ j hL ht hodd hj hagree hρ p hp
  obtain ⟨-, -, hS, -⟩ := hagree
  have hn : F'.top = F.top := by
    show F'.depth + 1 = F.depth + 1
    rw [ht]
  have hodd' : Odd F'.blockSide := hL ▸ hodd
  constructor
  · exact siteAtOffset_mem_sitesOfCells_of_agree hodd hL ht hj hρ (fun h hb => (hS h hb).1) hp
  · refine siteAtOffset_mem_sitesOfCells_of_agree hodd' hL.symm ht.symm (hn ▸ hj) hρ
      (fun h hb => (hS h hb).2) ?_
    rw [hL, hn]
    exact hp
end YangMills.Construction.FrameComparison
end
