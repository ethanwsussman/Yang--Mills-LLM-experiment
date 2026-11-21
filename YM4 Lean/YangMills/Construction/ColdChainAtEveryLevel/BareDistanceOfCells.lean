import YangMills.Construction.ColdChainAtEveryLevel.PlaquettesNearACell
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BlockAverages.CellDistances
variable {F : BlockFrame}
theorem eq_siteOfCoords_valMinAbs (x : F.Site 0) : x = siteOfCoords 0 fun i => (x i).valMinAbs := by
  funext i
  exact (ZMod.coe_valMinAbs (x i)).symm
theorem cellSupDist_mul_le_baseDistance_add (hodd : Odd F.blockSide) (x : F.Site 0) (Y : F.Cell) :
    (cellSupDist (enclosingCell x) Y : ℤ) * (F.blockSide : ℤ) ^ F.top ≤
      baseDistance x (cellCentre 0 Y) + (F.blockSide : ℤ) ^ F.top := by
  set N : ℤ := (F.blockSide : ℤ) ^ F.top with hN
  have hNodd : Odd N := by
    have : Odd (F.blockSide : ℤ) := by exact_mod_cast hodd
    exact this.pow
  have hN0 : 0 < N := by
    have : (0 : ℤ) < F.blockSide := by exact_mod_cast hodd.pos
    positivity
  set t : Fin 4 → ℤ := fun i => (((x - cellCentre 0 Y : F.Site 0)) i).valMinAbs with ht
  have hx : x = cellCentre 0 Y + siteOfCoords 0 t := by
    have h1 : siteOfCoords 0 t = x - cellCentre 0 Y :=
      (eq_siteOfCoords_valMinAbs (x - cellCentre 0 Y : F.Site 0)).symm
    rw [h1]
    abel
  set a : Fin 4 → ℤ := fun i => (t i + (N - 1) / 2) / N with ha
  set h : Fin 4 → ℤ := fun i => t i - N * a i with hh
  have hN2 : 2 * ((N - 1) / 2) = N - 1 := by
    obtain ⟨q, hq⟩ := hNodd
    rw [hq]
    omega
  have hrange : ∀ i, -((N - 1) / 2) ≤ h i ∧ h i ≤ (N - 1) / 2 := by
    intro i
    have e1 := Int.emod_add_mul_ediv (t i + (N - 1) / 2) N
    have e2 := Int.emod_nonneg (t i + (N - 1) / 2) hN0.ne'
    have e3 := Int.emod_lt_of_pos (t i + (N - 1) / 2) hN0
    simp only [hh, ha]
    constructor <;> omega
  have hcube : h ∈ centredCube (F.blockSide ^ (F.top - 0)) := by
    rw [LatticePaths.mem_centredCube_iff]
    intro i
    have e : ((F.blockSide ^ (F.top - 0) : ℕ) : ℤ) = N := by
      simp [hN]
    rw [e]
    exact hrange i
  have hxc : x = cellCentre 0 (Y + siteOfCoords F.top a) + siteOfCoords 0 h := by
    rw [cellCentre_add 0 (Nat.zero_le _), add_assoc, ← siteOfCoords_add]
    have e : (fun i => (F.blockSide : ℤ) ^ (F.top - 0) * a i) + h = t := by
      funext i
      simp [hh, hN]
    rw [e]
    exact hx
  have hcell : enclosingCell x = Y + siteOfCoords F.top a := by
    rw [hxc]
    exact CoordinateSeminorms.enclosingCell_cellCentre_add hodd _ h hcube
  have hbound : ∀ i, ((a i).natAbs : ℤ) * N ≤ baseDistance x (cellCentre 0 Y) + N := by
    intro i
    have h1 : ((t i).natAbs : ℤ) ≤ baseDistance x (cellCentre 0 Y) := by
      have := WeightedAverages.Chains.natAbs_le_baseDistance x (cellCentre 0 Y) i
      rw [PlaquettesNearCell.baseSite_zero] at this
      exact_mod_cast this
    have h2 := hrange i
    have e : t i = N * a i + h i := by
      simp only [hh]
      ring
    have h3 : ((a i).natAbs : ℤ) * N = |N * a i| := by
      rw [abs_mul, abs_of_pos hN0, Int.abs_eq_natAbs]
      ring
    rw [h3]
    have h4 : |N * a i| ≤ |t i| + |h i| := by
      have : N * a i = t i - h i := by linarith
      rw [this]
      exact abs_sub _ _
    have h5 : |h i| ≤ N := by
      rw [abs_le]
      constructor <;> omega
    have h6 : |t i| = ((t i).natAbs : ℤ) := Int.abs_eq_natAbs _
    omega
  rw [hcell]
  have hsup : cellSupDist (Y + siteOfCoords F.top a) Y ≤ Finset.univ.sup fun i => (a i).natAbs := by
    refine Finset.sup_mono_fun fun i _ => ?_
    have e : (Y + siteOfCoords F.top a : F.Cell) i - Y i = ((a i : ℤ) : ZMod (F.period F.top i)) := by
      simp [siteOfCoords]
    rw [e]
    exact WeightedAverages.Chains.natAbs_valMinAbs_intCast_le _ _
  have hne : (Finset.univ : Finset (Fin 4)).Nonempty := ⟨0, Finset.mem_univ _⟩
  obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup Finset.univ hne (fun i => (a i).natAbs)
  rw [hi] at hsup
  have h7 : (cellSupDist (Y + siteOfCoords F.top a) Y : ℤ) ≤ ((a i).natAbs : ℤ) := by exact_mod_cast hsup
  exact (mul_le_mul_of_nonneg_right h7 hN0.le).trans (hbound i)
theorem baseDistance_le_cellSupDist_add_one_mul (hodd : Odd F.blockSide) {S : Finset F.Cell} {x : F.Site 0}
    (hx : x ∈ sitesOfCells S 0) (Y : F.Cell) :
    (baseDistance x (cellCentre 0 Y) : ℤ) ≤ (cellSupDist (enclosingCell x) Y + 1 : ℕ) * (F.blockSide : ℤ) ^ F.top := by
  classical
  set N : ℤ := (F.blockSide : ℤ) ^ F.top with hN
  have hN0 : 0 < N := by
    have : (0 : ℤ) < F.blockSide := by exact_mod_cast hodd.pos
    positivity
  obtain ⟨z, hz, hx'⟩ := Finset.mem_biUnion.1 hx
  obtain ⟨h, hh, rfl⟩ := Finset.mem_image.1 hx'
  have hcell : enclosingCell (cellCentre 0 z + siteOfCoords 0 h : F.Site 0) = z :=
    CoordinateSeminorms.enclosingCell_cellCentre_add hodd z h hh
  rw [hcell]
  set o : Fin 4 → ℤ := fun i => ((z i - Y i)).valMinAbs with ho
  have hzY : z = Y + siteOfCoords F.top o := by
    funext i
    simp only [Pi.add_apply, siteOfCoords, ho, ZMod.coe_valMinAbs]
    abel
  have hle : ∀ i, |o i| ≤ cellSupDist z Y := by
    intro i
    have := Finset.le_sup (f := fun i => ((z i - Y i).valMinAbs).natAbs) (Finset.mem_univ i)
    rw [Int.abs_eq_natAbs]
    exact_mod_cast this
  have hcube := (LatticePaths.mem_centredCube_iff _ _).1 hh
  have hbase : (baseDistance (cellCentre 0 z + siteOfCoords 0 h : F.Site 0) (cellCentre 0 Y) : ℕ) ≤
      (cellSupDist z Y + 1) * N.toNat := by
    refine Finset.sup_le fun i _ => ?_
    have e1 : cellCentre 0 z = cellCentre 0 Y + siteOfCoords 0 (fun i => (F.blockSide : ℤ) ^ (F.top - 0) * o i) := by
      rw [hzY, cellCentre_add 0 (Nat.zero_le _)]
    have e2 : (baseSite (cellCentre 0 z + siteOfCoords 0 h : F.Site 0) - cellCentre 0 Y : F.Site 0) i =
        (((N * o i + h i : ℤ)) : ZMod (F.period 0 i)) := by
      rw [PlaquettesNearCell.baseSite_zero, e1]
      simp [siteOfCoords, hN]
      ring
    rw [e2]
    refine (WeightedAverages.Chains.natAbs_valMinAbs_intCast_le _ _).trans ?_
    have h1 := hcube i
    have e3 : ((F.blockSide ^ (F.top - 0) : ℕ) : ℤ) = N := by
      simp [hN]
    rw [e3] at h1
    have h2 : |h i| ≤ N := by
      rw [abs_le]
      constructor <;> omega
    have h3 : |N * o i + h i| ≤ N * (cellSupDist z Y) + N := by
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_of_pos hN0]
      have := mul_le_mul_of_nonneg_left (hle i) hN0.le
      linarith
    have h4 : ((N * o i + h i).natAbs : ℤ) ≤ ((cellSupDist z Y + 1) * N.toNat : ℕ) := by
      rw [← Int.abs_eq_natAbs]
      push_cast
      rw [Int.toNat_of_nonneg hN0.le]
      linarith
    exact_mod_cast h4
  have h5 : (baseDistance (cellCentre 0 z + siteOfCoords 0 h : F.Site 0) (cellCentre 0 Y) : ℤ) ≤
      (((cellSupDist z Y + 1) * N.toNat : ℕ) : ℤ) := by
    exact_mod_cast hbase
  push_cast at h5 ⊢
  rwa [Int.toNat_of_nonneg hN0.le] at h5
end YangMills.Construction.BlockAverages.CellDistances
end
