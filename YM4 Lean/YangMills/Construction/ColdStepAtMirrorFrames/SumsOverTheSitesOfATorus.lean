import YangMills.Construction.ColdStepAtMirrorFrames.ComponentsOfAFieldAlongAnElement
import YangMills.Construction.ColdStepAtMirrorFrames.EnergyOfAFlatChainNearACellProof
import YangMills.Construction.HoleBesideASecondHole.SitesOfBlocksAndCells
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages
namespace ColdStepAtMirrorFrames
variable {F : BlockFrame}
abbrev allSites (F : BlockFrame) (j : ℕ) : Finset (F.Site j) := sitesOfCells (finiteCells F) j
def refineSite (j l : ℕ) (y : F.Site l) : F.Site j :=
  siteOfCoords j fun i => (F.blockSide : ℤ) ^ (l - j) * siteCoords y i
theorem siteOfCoords_add (j : ℕ) (a b : Fin 4 → ℤ) :
    (siteOfCoords j (a + b) : F.Site j) = siteOfCoords j a + siteOfCoords j b := by apply _root_.YangMills.Construction.GaugeFixing.siteOfCoords_add <;> assumption
theorem siteOfCoords_zero (j : ℕ) : (siteOfCoords j 0 : F.Site j) = 0 := by apply _root_.YangMills.Construction.GaugeFixing.siteOfCoords_zero <;> assumption
theorem siteOfCoords_neg (j : ℕ) (a : Fin 4 → ℤ) :
    (siteOfCoords j (-a) : F.Site j) = - siteOfCoords j a := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.siteOfCoords_map_neg <;> assumption
theorem siteOfCoords_siteCoords {j : ℕ} (x : F.Site j) : siteOfCoords j (siteCoords x) = x := by apply _root_.YangMills.Construction.BlockAverages.siteOfCoords_siteCoords <;> assumption
theorem siteOfCoords_eq_iff {j : ℕ} {a b : Fin 4 → ℤ} :
    (siteOfCoords j a : F.Site j) = siteOfCoords j b ↔ ∀ i, (F.period j i : ℤ) ∣ b i - a i := by apply _root_.YangMills.Construction.BlockSites.siteOfCoords_eq_iff <;> assumption
theorem siteCoords_siteOfCoords {j : ℕ} (a : Fin 4 → ℤ) (i : Fin 4) :
    siteCoords (siteOfCoords j a : F.Site j) i = a i % (F.period j i : ℤ) := by apply _root_.YangMills.Construction.BlockLines.siteCoords_siteOfCoords <;> assumption
theorem period_pos (hL : 0 < F.blockSide) (hs : ∀ i, 0 < F.extent i) (j : ℕ) (i : Fin 4) :
    0 < F.period j i := by apply _root_.YangMills.Construction.LumpContours.period_pos <;> assumption
theorem period_eq_pow_mul {j l : ℕ} (hjl : j ≤ l) (hl : l ≤ F.top) (i : Fin 4) :
    F.period j i = F.blockSide ^ (l - j) * F.period l i := by apply _root_.YangMills.Construction.LumpContours.BlockLevels.period_eq_pow_mul <;> assumption
theorem period_eq_pow_mul_int {j l : ℕ} (hjl : j ≤ l) (hl : l ≤ F.top) (i : Fin 4) :
    (F.period j i : ℤ) = (F.blockSide : ℤ) ^ (l - j) * (F.period l i : ℤ) := by
  rw [period_eq_pow_mul hjl hl i]
  push_cast
  ring
theorem refineSite_siteOfCoords {j l : ℕ} (hjl : j ≤ l) (hl : l ≤ F.top) (q : Fin 4 → ℤ) :
    refineSite j l (siteOfCoords l q : F.Site l) =
      siteOfCoords j fun i => (F.blockSide : ℤ) ^ (l - j) * q i := by
  unfold refineSite
  rw [siteOfCoords_eq_iff]
  intro i
  rw [siteCoords_siteOfCoords, period_eq_pow_mul_int hjl hl i]
  have e := Int.emod_add_mul_ediv (q i) (F.period l i : ℤ)
  refine ⟨q i / (F.period l i : ℤ), ?_⟩
  linear_combination ((F.blockSide : ℤ) ^ (l - j)) * (-e)
theorem mem_centredCube_iff {M k : ℕ} (hM : M = 2 * k + 1) (h : Fin 4 → ℤ) :
    h ∈ centredCube M ↔ ∀ i, - (k : ℤ) ≤ h i ∧ h i ≤ k := by
  have e : ((M : ℤ) - 1) / 2 = k := by
    rw [hM]
    push_cast
    omega
  unfold centredCube
  rw [Fintype.mem_piFinset]
  simp only [Finset.mem_Icc, e]
theorem exists_refineSite_add (hL : Odd F.blockSide) {j l : ℕ} (hjl : j ≤ l) (hl : l ≤ F.top)
    (x : F.Site j) :
    ∃ (q h : Fin 4 → ℤ), h ∈ centredCube (F.blockSide ^ (l - j)) ∧
      x = refineSite j l (siteOfCoords l q : F.Site l) + siteOfCoords j h := by
  obtain ⟨k, hk⟩ := hL.pow (n := l - j)
  have hMpos : (0 : ℤ) < ((F.blockSide ^ (l - j) : ℕ) : ℤ) := by
    have : 0 < F.blockSide ^ (l - j) := by omega
    exact_mod_cast this
  set M : ℤ := ((F.blockSide ^ (l - j) : ℕ) : ℤ) with hMdef
  have hMk : M = 2 * k + 1 := by
    rw [hMdef, hk]
    push_cast
    ring
  refine ⟨fun i => (siteCoords x i + k) / M,
    fun i => siteCoords x i - M * ((siteCoords x i + k) / M), ?_, ?_⟩
  · rw [mem_centredCube_iff hk]
    intro i
    have e1 := Int.emod_add_mul_ediv (siteCoords x i + k) M
    have e2 := Int.emod_nonneg (siteCoords x i + k) hMpos.ne'
    have e3 := Int.emod_lt_of_pos (siteCoords x i + k) hMpos
    constructor <;> nlinarith
  · rw [refineSite_siteOfCoords hjl hl, ← siteOfCoords_add]
    conv_lhs => rw [← siteOfCoords_siteCoords x]
    congr 1
    funext i
    simp only [Pi.add_apply, hMdef]
    push_cast
    ring
theorem mem_finiteCells (hL : 0 < F.blockSide) (hs : ∀ i, 0 < F.extent i) (z : F.Cell) :
    z ∈ finiteCells F := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.FlatChainEnergy.mem_finiteCells <;> assumption
theorem mem_allSites (hL : Odd F.blockSide) (hs : ∀ i, 0 < F.extent i) {j : ℕ} (hj : j ≤ F.top)
    (x : F.Site j) : x ∈ allSites F j := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.mem_sitesOfCells_finiteCells <;> assumption
theorem sum_allSites_add_right (hL : Odd F.blockSide) (hs : ∀ i, 0 < F.extent i) {j : ℕ}
    (hj : j ≤ F.top) (u : F.Site j) (g : F.Site j → ℝ) :
    ∑ x ∈ allSites F j, g (x + u) = ∑ x ∈ allSites F j, g x := by
  refine Finset.sum_nbij (fun x => x + u) (fun _ _ => mem_allSites hL hs hj _) ?_ ?_ (fun _ _ => rfl)
  · intro a _ b _ h
    exact add_right_cancel h
  · intro x _
    exact ⟨x - u, mem_allSites hL hs hj _, by simp⟩
theorem sum_allSites_eq_sum_blocks (hL : Odd F.blockSide) (hs : ∀ i, 0 < F.extent i) {j l : ℕ}
    (hjl : j ≤ l) (hl : l ≤ F.top) (g : F.Site j → ℝ) :
    ∑ x ∈ allSites F j, g x =
      ∑ y ∈ allSites F l, ∑ h ∈ centredCube (F.blockSide ^ (l - j)),
        g (refineSite j l y + siteOfCoords j h) := by
  rw [← Finset.sum_product']
  symm
  refine Finset.sum_nbij (fun p => refineSite j l p.1 + siteOfCoords j p.2)
    (fun _ _ => mem_allSites hL hs (hjl.trans hl) _) ?_ ?_ (fun _ _ => rfl)
  · rintro ⟨y, h⟩ hp ⟨y', h'⟩ hp' he
    obtain ⟨k, hk⟩ := hL.pow (n := l - j)
    have hh := (mem_centredCube_iff hk h).1 (Finset.mem_product.1 hp).2
    have hh' := (mem_centredCube_iff hk h').1 (Finset.mem_product.1 hp').2
    simp only at he
    unfold refineSite at he
    rw [← siteOfCoords_add, ← siteOfCoords_add, siteOfCoords_eq_iff] at he
    have hMz : (F.blockSide : ℤ) ^ (l - j) = 2 * k + 1 := by exact_mod_cast hk
    have hhe : h = h' := by
      funext i
      have d := he i
      rw [period_eq_pow_mul_int hjl hl i] at d
      simp only [Pi.add_apply] at d
      have d1 : (F.blockSide : ℤ) ^ (l - j) ∣ h' i - h i := by
        have d2 := dvd_trans (Dvd.intro _ rfl) d
        have : h' i - h i = ((F.blockSide : ℤ) ^ (l - j) * siteCoords y' i + h' i -
            ((F.blockSide : ℤ) ^ (l - j) * siteCoords y i + h i)) -
            (F.blockSide : ℤ) ^ (l - j) * (siteCoords y' i - siteCoords y i) := by ring
        rw [this]
        exact dvd_sub d2 (Dvd.intro _ rfl)
      have h0 : h' i - h i = 0 := by
        apply Int.eq_zero_of_abs_lt_dvd d1
        rw [hMz, abs_lt]
        have := hh i
        have := hh' i
        constructor <;> omega
      omega
    have hye : y = y' := by
      rw [← siteOfCoords_siteCoords y, ← siteOfCoords_siteCoords y', siteOfCoords_eq_iff]
      intro i
      have d := he i
      rw [period_eq_pow_mul_int hjl hl i, hhe] at d
      simp only [Pi.add_apply] at d
      have hMne : (F.blockSide : ℤ) ^ (l - j) ≠ 0 := by
        rw [hMz]
        omega
      have : (F.blockSide : ℤ) ^ (l - j) * (F.period l i : ℤ) ∣
          (F.blockSide : ℤ) ^ (l - j) * (siteCoords y' i - siteCoords y i) := by
        have e : (F.blockSide : ℤ) ^ (l - j) * (siteCoords y' i - siteCoords y i) =
            (F.blockSide : ℤ) ^ (l - j) * siteCoords y' i + h' i -
              ((F.blockSide : ℤ) ^ (l - j) * siteCoords y i + h' i) := by ring
        rw [e]
        exact d
      exact (mul_dvd_mul_iff_left hMne).1 this
    rw [hye, hhe]
  · intro x _
    obtain ⟨q, h, hh, hx⟩ := exists_refineSite_add hL hjl hl x
    refine ⟨(siteOfCoords l q, h), ?_, hx.symm⟩
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe]
    exact ⟨mem_allSites hL hs hl _, hh⟩
end ColdStepAtMirrorFrames
end YangMills.Construction
end
