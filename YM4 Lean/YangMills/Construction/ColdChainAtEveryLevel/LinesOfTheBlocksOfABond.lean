import YangMills.Construction.ColdChainAtEveryLevel.ChartsOfCellsAndSites
import YangMills.Construction.ColdChainAtEveryLevel.PathsOnTheLattice
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
namespace BlockLines
open BlockAverages LatticePaths FlatPairing LatticeFractionalIntegration FiniteDifferences
variable {F : BlockFrame}
theorem siteOfCoords_add_fun {j : ℕ} (a b : Fin 4 → ℤ) :
    siteOfCoords (F := F) j a + siteOfCoords j b = siteOfCoords j fun i => a i + b i := by
  funext i
  simp [siteOfCoords]
theorem siteCoords_siteOfCoords {j : ℕ} (a : Fin 4 → ℤ) (i : Fin 4) :
    siteCoords (siteOfCoords (F := F) j a) i = a i % (F.period j i : ℤ) := by
  simp [siteCoords, siteOfCoords, ZMod.coe_intCast]
theorem period_eq {j : ℕ} (i : Fin 4) :
    (F.period j i : ℤ) = (F.extent i : ℤ) * (F.blockSide : ℤ) ^ (F.top - j) := by
  simp [BlockFrame.period]
theorem blockSide_pow_sub_eq {j : ℕ} (hj : j < F.top) :
    (F.blockSide : ℤ) ^ (F.top - j) = F.blockSide * (F.blockSide : ℤ) ^ (F.top - (j + 1)) := by
  obtain ⟨e, he⟩ : ∃ e, F.top - j = e + 1 := ⟨F.top - (j + 1), by omega⟩
  have he' : F.top - (j + 1) = e := by omega
  rw [he, he', pow_succ]
  ring
theorem period_eq_mul_succ {j : ℕ} (hj : j < F.top) (i : Fin 4) :
    (F.period j i : ℤ) = F.blockSide * (F.period (j + 1) i : ℤ) := by
  rw [period_eq, period_eq, blockSide_pow_sub_eq hj]
  ring
theorem refineSite_siteOfCoords {j : ℕ} (hj : j < F.top) (a : Fin 4 → ℤ) :
    refineSite (siteOfCoords (F := F) (j + 1) a) = siteOfCoords j fun i => (F.blockSide : ℤ) * a i := by
  funext i
  simp only [refineSite]
  change (((F.blockSide : ℤ) * siteCoords (siteOfCoords (F := F) (j + 1) a) i : ℤ) : ZMod (F.period j i)) =
    (((F.blockSide : ℤ) * a i : ℤ) : ZMod (F.period j i))
  rw [siteCoords_siteOfCoords]
  refine (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).2 ?_
  rw [period_eq_mul_succ hj]
  refine ⟨a i / (F.period (j + 1) i : ℤ), ?_⟩
  have := Int.emod_add_mul_ediv (a i) (F.period (j + 1) i : ℤ)
  nlinarith
theorem odd_pow_eq_two_mul_add_one (hodd : Odd F.blockSide) (e : ℕ) : ∃ k : ℕ, F.blockSide ^ e = 2 * k + 1 ∧
    (((F.blockSide ^ e : ℕ) : ℤ) - 1) / 2 = k ∧ (F.blockSide : ℤ) ^ e = 2 * (k : ℤ) + 1 := by
  obtain ⟨k, hk⟩ := Odd.pow (n := e) hodd
  refine ⟨k, hk, ?_, ?_⟩
  · rw [hk]; push_cast; omega
  · have : (((F.blockSide ^ e : ℕ) : ℤ)) = 2 * (k : ℤ) + 1 := by rw [hk]; push_cast; ring
    rw [← this]; push_cast; rfl
theorem refineSite_add_mem_sitesOfCells {B : Finset F.Cell} {j : ℕ} (hj : j < F.top) (hodd : Odd F.blockSide)
    (y : F.Site (j + 1)) (hy : y ∈ sitesOfCells B (j + 1)) (g : Fin 4 → ℤ) (hg : g ∈ centredCube F.blockSide) :
    refineSite y + siteOfCoords j g ∈ sitesOfCells B j := by
  simp only [sitesOfCells, Finset.mem_biUnion, Finset.mem_image] at hy ⊢
  obtain ⟨z, hz, h', hh', rfl⟩ := hy
  refine ⟨z, hz, fun i => (F.blockSide : ℤ) * h' i + g i, ?_, ?_⟩
  · obtain ⟨k, hk1, hk2, hk3⟩ := odd_pow_eq_two_mul_add_one hodd 1
    obtain ⟨k', hk1', hk2', hk3'⟩ := odd_pow_eq_two_mul_add_one hodd (F.top - (j + 1))
    obtain ⟨K, hK1, hK2, hK3⟩ := odd_pow_eq_two_mul_add_one hodd (F.top - j)
    rw [pow_one] at hk1 hk2 hk3
    rw [mem_centredCube_iff] at hg hh' ⊢
    rw [hk2] at hg
    rw [hk2'] at hh'
    rw [hK2]
    have hrel : (K : ℤ) = (F.blockSide : ℤ) * k' + k := by
      have e := blockSide_pow_sub_eq (F := F) hj
      rw [hK3, hk3', hk3] at e
      rw [hk3]
      have : 2 * (K : ℤ) = 2 * ((2 * (k : ℤ) + 1) * k' + k) := by nlinarith
      omega
    intro i
    have h1 := hg i
    have h2 := hh' i
    have hLpos : (0 : ℤ) ≤ F.blockSide := by positivity
    rw [hrel]
    constructor
    · nlinarith [h1.1, h2.1]
    · nlinarith [h1.2, h2.2]
  · have e1 : cellCentre (j + 1) z + siteOfCoords (j + 1) h' =
        siteOfCoords (F := F) (j + 1)
          (fun i => (F.blockSide : ℤ) ^ (F.top - (j + 1)) * siteCoords z i + h' i) := by
      simp only [cellCentre]
      rw [siteOfCoords_add_fun]
    rw [e1, refineSite_siteOfCoords hj]
    simp only [cellCentre]
    rw [siteOfCoords_add_fun, siteOfCoords_add_fun]
    congr 1
    funext i
    rw [blockSide_pow_sub_eq hj]
    ring
theorem refineSite_add_unitStep {j : ℕ} (hj : j < F.top) (y : F.Site (j + 1)) (i : Fin 4) :
    refineSite (y + unitStep (j + 1) i) = refineSite y + siteOfCoords j ((F.blockSide : ℤ) • basisVector i) := by
  rw [unitStep_eq, refineSite_add j (by omega)]
  rfl
theorem refineSite_add_mem_of_mem_twoBlockHull {B : Finset F.Cell} {j : ℕ} (hj : j < F.top)
    (hodd : Odd F.blockSide) (y : F.Site (j + 1)) (i : Fin 4) (hy : y ∈ sitesOfCells B (j + 1))
    (hy' : y + unitStep (j + 1) i ∈ sitesOfCells B (j + 1)) (a : Lattice4)
    (ha : a ∈ twoBlockHull F.blockSide i) :
    refineSite y + siteOfCoords j a ∈ sitesOfCells B j := by
  obtain ⟨k, hk1, hk2, hk3⟩ := odd_pow_eq_two_mul_add_one hodd 1
  rw [pow_one] at hk1 hk2 hk3
  by_cases hc : a i ≤ k
  · refine refineSite_add_mem_sitesOfCells hj hodd y hy a ((mem_centredCube_iff _ _).2 fun l => ?_)
    have h1 := ha l
    rw [hk2] at h1 ⊢
    by_cases hl : l = i
    · subst hl
      exact ⟨h1.1, hc⟩
    · simpa [hl] using h1
  · have e : refineSite y + siteOfCoords j a =
        refineSite (y + unitStep (j + 1) i) + siteOfCoords j (a - (F.blockSide : ℤ) • basisVector i) := by
      rw [refineSite_add_unitStep hj, add_assoc, ← siteOfCoords_add]
      congr 2
      abel
    rw [e]
    refine refineSite_add_mem_sitesOfCells hj hodd _ hy' _ ((mem_centredCube_iff _ _).2 fun l => ?_)
    have h1 := ha l
    rw [hk2] at h1 ⊢
    by_cases hl : l = i
    · subst hl
      simp only [if_true] at h1
      simp only [Pi.sub_apply, Pi.smul_apply, basisVector, Pi.single_eq_same, smul_eq_mul, mul_one]
      omega
    · simp only [if_neg hl, add_zero] at h1
      simpa [basisVector, Pi.single_eq_of_ne hl] using h1
theorem bond_mem_innerBonds_of_mem_twoBlockHull {B : Finset F.Cell} {j : ℕ} (hj : j < F.top)
    (hodd : Odd F.blockSide) (c : F.Site (j + 1) × Fin 4) (hc : c ∈ innerBonds B (j + 1)) (a : Lattice4)
    (k : Fin 4) (ha : a ∈ twoBlockHull F.blockSide c.2) (ha' : a + basisVector k ∈ twoBlockHull F.blockSide c.2) :
    (refineSite c.1 + siteOfCoords j a, k) ∈ innerBonds B j := by
  simp only [innerBonds, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true] at hc ⊢
  refine ⟨refineSite_add_mem_of_mem_twoBlockHull hj hodd c.1 c.2 hc.1 hc.2 a ha, ?_⟩
  have e : refineSite c.1 + siteOfCoords j a + unitStep j k = refineSite c.1 + siteOfCoords j (a + basisVector k) := by
    rw [unitStep_eq, add_assoc, ← siteOfCoords_add]
  rw [e]
  exact refineSite_add_mem_of_mem_twoBlockHull hj hodd c.1 c.2 hc.1 hc.2 _ ha'
theorem refineSite_add_injective {j : ℕ} (hj : j < F.top) (hodd : Odd F.blockSide) (y y' : F.Site (j + 1))
    (h h' : Fin 4 → ℤ) (hh : h ∈ centredCube F.blockSide) (hh' : h' ∈ centredCube F.blockSide)
    (e : refineSite y + siteOfCoords j h = refineSite y' + siteOfCoords j h') :
    y = y' ∧ h = h' := by
  obtain ⟨k, hk1, hk2, hk3⟩ := odd_pow_eq_two_mul_add_one hodd 1
  rw [pow_one] at hk1 hk2 hk3
  rw [mem_centredCube_iff, hk2] at hh hh'
  have hc : ∀ l, (F.period j l : ℤ) ∣
      ((F.blockSide : ℤ) * siteCoords y' l + h' l) - ((F.blockSide : ℤ) * siteCoords y l + h l) := by
    intro l
    have e2 := congrFun e l
    apply (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1
    simp only [refineSite, Pi.add_apply, siteOfCoords] at e2
    push_cast at e2 ⊢
    exact e2
  have hhh : h = h' := by
    funext l
    obtain ⟨m, hm⟩ := hc l
    rw [period_eq_mul_succ hj] at hm
    have hd : (F.blockSide : ℤ) ∣ h l - h' l := by
      refine ⟨siteCoords y' l - siteCoords y l - (F.period (j + 1) l : ℤ) * m, ?_⟩
      linear_combination (-1 : ℤ) * hm
    have hb1 := hh l
    have hb2 := hh' l
    have habs : |h l - h' l| < F.blockSide := by
      rw [abs_lt, hk3]
      constructor <;> omega
    have := Int.eq_zero_of_abs_lt_dvd hd habs
    omega
  refine ⟨?_, hhh⟩
  funext l
  obtain ⟨m, hm⟩ := hc l
  rw [period_eq_mul_succ hj, hhh] at hm
  have hLne : (F.blockSide : ℤ) ≠ 0 := by
    have : (0 : ℤ) < F.blockSide := by exact_mod_cast hodd.pos
    omega
  have hm2 : siteCoords y' l - siteCoords y l = (F.period (j + 1) l : ℤ) * m := by
    apply mul_left_cancel₀ hLne
    linear_combination hm
  have hcast := (ZMod.intCast_eq_intCast_iff_dvd_sub (siteCoords y l) (siteCoords y' l)
    (F.period (j + 1) l)).2 ⟨m, hm2⟩
  have h1 : ((siteCoords y l : ℤ) : ZMod (F.period (j + 1) l)) = y l := ZMod.intCast_zmod_cast (y l)
  have h2 : ((siteCoords y' l : ℤ) : ZMod (F.period (j + 1) l)) = y' l := ZMod.intCast_zmod_cast (y' l)
  rw [← h1, ← h2, hcast]
section Cells
theorem enclosingCell_cellCentre_add (hL : Odd F.blockSide) {j : ℕ} (z : F.Cell) (h : Fin 4 → ℤ)
    (hh : h ∈ centredCube (F.blockSide ^ (F.top - j))) :
    enclosingCell (cellCentre j z + siteOfCoords j h : F.Site j) = z := by
  funext i
  set k : ℤ := (F.blockSide : ℤ) ^ (F.top - j) with hk
  have hkodd : Odd k := by
    rw [hk]
    exact Odd.pow (by exact_mod_cast hL)
  have hkpos : 0 < k := by
    rw [hk]
    have : 0 < F.blockSide := hL.pos
    positivity
  obtain ⟨m, hm⟩ := hkodd
  have hmdiv : (k - 1) / 2 = m := by omega
  have hhi := Fintype.mem_piFinset.1 hh i
  have hcast : (((F.blockSide ^ (F.top - j) : ℕ) : ℤ)) = k := by
    rw [hk]
    push_cast
    rfl
  rw [Finset.mem_Icc, hcast, hmdiv] at hhi
  set x : F.Site j := cellCentre j z + siteOfCoords j h with hx
  set c : ℤ := siteCoords z i with hc
  have hxi : ((siteCoords x i : ℤ) : ZMod (F.period j i)) = ((k * c + h i : ℤ) : ZMod (F.period j i)) := by
    have h1 : ((siteCoords x i : ℤ) : ZMod (F.period j i)) = x i := by
      unfold siteCoords
      exact ZMod.intCast_zmod_cast (x i)
    rw [h1, hx]
    simp [cellCentre, siteOfCoords, hk, hc]
  have hdvd := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1 hxi
  obtain ⟨e, he⟩ := hdvd
  have hper : ((F.period j i : ℕ) : ℤ) = (F.extent i : ℤ) * k := by
    simp [BlockFrame.period, hk]
  rw [hper] at he
  have hv : siteCoords x i + m = (h i + m) + k * (c - F.extent i * e) := by
    have : siteCoords x i = k * c + h i - F.extent i * k * e := by linarith
    rw [this]
    ring
  have hfl : (siteCoords x i + m) / k = c - F.extent i * e := by
    rw [hv, Int.add_mul_ediv_left _ _ hkpos.ne']
    have : (h i + m) / k = 0 := Int.ediv_eq_zero_of_lt (by linarith [hhi.1]) (by linarith [hhi.2])
    rw [this, zero_add]
  show ((((siteCoords x i + (((F.blockSide : ℤ) ^ (F.top - j) - 1) / 2)) / (F.blockSide : ℤ) ^ (F.top - j) : ℤ)) :
    ZMod (F.period F.top i)) = z i
  rw [← hk, hmdiv, hfl]
  have hper2 : ((F.period F.top i : ℕ) : ℤ) = (F.extent i : ℤ) := by
    simp [BlockFrame.period]
  have hs : ((F.extent i * e : ℤ) : ZMod (F.period F.top i)) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd, hper2]
    exact dvd_mul_right _ _
  rw [Int.cast_sub, hs, sub_zero, hc]
  unfold siteCoords
  exact ZMod.intCast_zmod_cast (z i)
theorem enclosingCell_mem {S : Finset F.Cell} (hL : Odd F.blockSide) {j : ℕ} {x : F.Site j}
    (hx : x ∈ sitesOfCells S j) : enclosingCell x ∈ S := by
  obtain ⟨z, hz, hxz⟩ := Finset.mem_biUnion.1 hx
  obtain ⟨h, hh, rfl⟩ := Finset.mem_image.1 hxz
  rw [enclosingCell_cellCentre_add hL z h hh]
  exact hz
theorem mem_sitesOfCells_of_enclosingCell_mem {S B : Finset F.Cell} (hL : Odd F.blockSide) {j : ℕ}
    {x : F.Site j} (hx : x ∈ sitesOfCells S j) (hB : enclosingCell x ∈ B) : x ∈ sitesOfCells B j := by
  obtain ⟨y, hy, h, hh, rfl⟩ := mem_sitesOfCells.1 hx
  rw [enclosingCell_cellCentre_add hL y h hh] at hB
  exact mem_sitesOfCells.2 ⟨y, hB, h, hh, rfl⟩
theorem sitesOfCells_mono {B S : Finset F.Cell} (h : B ⊆ S) (j : ℕ) : sitesOfCells B j ⊆ sitesOfCells S j := by
  intro x hx
  obtain ⟨y, hy, g, hg, rfl⟩ := mem_sitesOfCells.1 hx
  exact mem_sitesOfCells.2 ⟨y, h hy, g, hg, rfl⟩
theorem innerBonds_mono {B S : Finset F.Cell} (h : B ⊆ S) (j : ℕ) : innerBonds B j ⊆ innerBonds S j := by
  intro b hb
  simp only [innerBonds, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true] at hb ⊢
  exact ⟨sitesOfCells_mono h j hb.1, sitesOfCells_mono h j hb.2⟩
theorem cellBall_subset (S : Finset F.Cell) (z : F.Cell) (r : ℕ) : cellBall S z r ⊆ S := by
  classical
  exact Finset.filter_subset _ _
theorem cellBall_mono (S : Finset F.Cell) (z : F.Cell) {r r' : ℕ} (h : r ≤ r') :
    cellBall S z r ⊆ cellBall S z r' := by
  classical
  intro y hy
  exact Finset.mem_filter.2 ⟨(Finset.mem_filter.1 hy).1, (Finset.mem_filter.1 hy).2.trans h⟩
theorem cellSupDist_self (z : F.Cell) : cellSupDist z z = 0 := by
  simp [cellSupDist]
theorem cellSupDist_comm (y z : F.Cell) : cellSupDist y z = cellSupDist z y := by
  unfold cellSupDist
  congr 1
  funext i
  rw [← neg_sub (z i) (y i), ZMod.natAbs_valMinAbs_neg]
theorem mem_bondsOver_of_mem_innerBonds_cellBall (hL : Odd F.blockSide) (S : Finset F.Cell) (z : F.Cell) (j : ℕ)
    {b : F.Site j × Fin 4} (hb : b ∈ innerBonds (cellBall S z 1) j) : b ∈ bondsOver S (cellBall S z 3) j := by
  classical
  have h1 : b ∈ innerBonds S j := innerBonds_mono (cellBall_subset S z 1) j hb
  have h2 : b.1 ∈ sitesOfCells (cellBall S z 1) j := by
    simp only [innerBonds, Finset.mem_filter, Finset.mem_product] at hb
    exact hb.1.1
  exact Finset.mem_filter.2 ⟨h1, cellBall_mono S z (by norm_num) (enclosingCell_mem hL h2)⟩
theorem mem_innerBonds_cellBall_of_mem_bondsOver (hamb : IsAdmissibleAmbient F) (hL : Odd F.blockSide)
    (S : Finset F.Cell) (z : F.Cell) {j : ℕ} (hj : j ≤ F.top)
    {b : F.Site j × Fin 4} (hb : b ∈ bondsOver S {z} j) : b ∈ innerBonds (cellBall S z 1) j := by
  classical
  obtain ⟨hbS, hcell⟩ := Finset.mem_filter.1 hb
  have hcz : enclosingCell b.1 = z := Finset.mem_singleton.1 hcell
  simp only [innerBonds, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true] at hbS ⊢
  have hzS : z ∈ S := hcz ▸ enclosingCell_mem hL hbS.1
  have hzB : z ∈ cellBall S z 1 := Finset.mem_filter.2 ⟨hzS, by rw [cellSupDist_self]; omega⟩
  refine ⟨mem_sitesOfCells_of_enclosingCell_mem hL hbS.1 (hcz ▸ hzB),
    mem_sitesOfCells_of_enclosingCell_mem hL hbS.2 ?_⟩
  have hmem := enclosingCell_mem hL hbS.2
  refine Finset.mem_filter.2 ⟨hmem, ?_⟩
  obtain ⟨y, hy, h, hh, hx⟩ := mem_sitesOfCells.1 hbS.1
  have hyz : y = z := by
    rw [← hcz, hx, enclosingCell_cellCentre_add hL y h hh]
  subst hyz
  obtain ⟨K, hK1, hK2, hK3⟩ := odd_pow_eq_two_mul_add_one hL (F.top - j)
  have hc := (mem_centredCube_iff _ _).1 hh
  rw [hK2] at hc
  by_cases hedge : h b.2 = K
  · have e : b.1 + unitStep j b.2 =
        cellCentre j (y + siteOfCoords F.top (basisVector b.2)) +
          siteOfCoords j (h + basisVector b.2 - ((F.blockSide : ℤ) ^ (F.top - j)) • basisVector b.2) := by
      rw [hx, cellCentre_add j hj, add_assoc, unitStep_eq, ← siteOfCoords_add, add_assoc, ← siteOfCoords_add]
      congr 2
      funext l
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring
    have hcube : h + basisVector b.2 - ((F.blockSide : ℤ) ^ (F.top - j)) • basisVector b.2 ∈
        centredCube (F.blockSide ^ (F.top - j)) := by
      refine (mem_centredCube_iff _ _).2 fun l => ?_
      rw [hK2, hK3]
      by_cases hl : l = b.2
      · subst hl
        simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, basisVector, Pi.single_eq_same, smul_eq_mul,
          mul_one]
        omega
      · simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, basisVector, Pi.single_eq_of_ne hl, smul_eq_mul,
          mul_zero, add_zero, sub_zero]
        exact hc l
    rw [e, enclosingCell_cellCentre_add hL _ _ hcube, cellSupDist_comm]
    refine cellSupDist_add_le hamb y (by norm_num) fun l => ?_
    by_cases hl : l = b.2
    · subst hl
      simp [basisVector]
    · simp [basisVector, Pi.single_eq_of_ne hl]
  · have e : b.1 + unitStep j b.2 = cellCentre j y + siteOfCoords j (h + basisVector b.2) := by
      rw [hx, unitStep_eq, add_assoc, ← siteOfCoords_add]
    have hcube : h + basisVector b.2 ∈ centredCube (F.blockSide ^ (F.top - j)) := by
      refine (mem_centredCube_iff _ _).2 fun l => ?_
      rw [hK2]
      have h1 := hc l
      by_cases hl : l = b.2
      · subst hl
        simp only [Pi.add_apply, basisVector, Pi.single_eq_same]
        omega
      · simpa [basisVector, Pi.single_eq_of_ne hl] using h1
    rw [e, enclosingCell_cellCentre_add hL _ _ hcube, cellSupDist_self]
    omega
theorem card_cellBall_one_le (S : Finset F.Cell) (z : F.Cell) : (cellBall S z 1).card ≤ 81 := by
  classical
  have hc : (centredCube 3).card = 81 := by
    rw [card_centredCube (by decide : Odd 3)]
    norm_num
  rw [← hc]
  apply Finset.card_le_card_of_injOn (fun y i => ((z - y : F.Cell) i).valMinAbs)
  · intro y hy
    have hy' := (Finset.mem_filter.1 (Finset.mem_coe.1 hy)).2
    refine Finset.mem_coe.2 ((mem_centredCube_iff _ _).2 fun i => ?_)
    have h1 : (((z - y : F.Cell) i).valMinAbs).natAbs ≤ cellSupDist z y :=
      Finset.le_sup (f := fun i => (((z - y : F.Cell) i).valMinAbs).natAbs) (Finset.mem_univ i)
    norm_num
    change -1 ≤ ((z - y : F.Cell) i).valMinAbs ∧ ((z - y : F.Cell) i).valMinAbs ≤ 1
    omega
  · intro y _ y' _ e
    funext i
    have h1 := congrFun e i
    have h2 := ZMod.injective_valMinAbs h1
    have h3 : (z - y : F.Cell) i = (z - y' : F.Cell) i := h2
    simpa using h3
theorem card_sitesOfCells_le (hL : Odd F.blockSide) (B : Finset F.Cell) (j : ℕ) :
    (sitesOfCells B j).card ≤ B.card * (F.blockSide ^ (F.top - j)) ^ 4 := by
  classical
  unfold sitesOfCells
  refine Finset.card_biUnion_le.trans ?_
  have : ∀ z ∈ B, ((centredCube (F.blockSide ^ (F.top - j))).image
      fun h => cellCentre j z + siteOfCoords j h).card ≤ (F.blockSide ^ (F.top - j)) ^ 4 := by
    intro z _
    refine Finset.card_image_le.trans (le_of_eq ?_)
    exact card_centredCube (Odd.pow hL)
  refine (Finset.sum_le_sum this).trans (le_of_eq ?_)
  rw [Finset.sum_const, smul_eq_mul]
theorem card_innerBonds_le (hL : Odd F.blockSide) (B : Finset F.Cell) (j : ℕ) :
    (innerBonds B j).card ≤ 4 * (B.card * (F.blockSide ^ (F.top - j)) ^ 4) := by
  classical
  unfold innerBonds
  refine (Finset.card_filter_le _ _).trans ?_
  rw [Finset.card_product, Finset.card_univ, Fintype.card_fin, mul_comm]
  exact Nat.mul_le_mul_left 4 (card_sitesOfCells_le hL B j)
end Cells
section Lines
variable {j : ℕ}
theorem norm_adjointAction (g : UnitQuaternion) (w : ℍ[ℝ]) : ‖adjointAction g w‖ = ‖w‖ := by
  simp only [adjointAction, norm_mul, norm_coe_unitQuaternion, one_mul, mul_one]
def lineBond (c : F.Site (j + 1) × Fin 4) (h : Fin 4 → ℤ) (r : ℕ) : F.Site j × Fin 4 :=
  (refineSite c.1 + siteOfCoords j h + (r : ℤ) • unitStep j c.2, c.2)
theorem lineBond_fst (c : F.Site (j + 1) × Fin 4) (h : Fin 4 → ℤ) (r : ℕ) :
    (lineBond c h r).1 = refineSite c.1 + siteOfCoords j (h + (r : ℤ) • basisVector c.2) := by
  simp only [lineBond]
  rw [add_assoc, siteOfCoords_add]
  congr 2
  funext l
  simp [unitStep, siteOfCoords, basisVector, Pi.single_apply]
theorem add_smul_basisVector_mem_twoBlockHull {L : ℕ} {h : Lattice4} (hh : h ∈ centredCube L) (i : Fin 4)
    {r : ℕ} (hr : r ≤ L) : h + (r : ℤ) • basisVector i ∈ twoBlockHull L i := by
  have hc := (mem_centredCube_iff L h).1 hh
  intro μ
  have h1 := hc μ
  by_cases hμ : μ = i
  · subst hμ
    simp only [Pi.add_apply, Pi.smul_apply, basisVector, Pi.single_eq_same, smul_eq_mul, mul_one, if_true]
    constructor <;> omega
  · simp only [Pi.add_apply, Pi.smul_apply, basisVector, Pi.single_eq_of_ne hμ, smul_eq_mul, mul_zero, add_zero,
      if_neg hμ]
    exact h1
theorem lineBond_mem_innerBonds {B : Finset F.Cell} (hj : j < F.top) (hodd : Odd F.blockSide)
    (c : F.Site (j + 1) × Fin 4) (hc : c ∈ innerBonds B (j + 1)) (h : Fin 4 → ℤ)
    (hh : h ∈ centredCube F.blockSide) (r : ℕ) (hr : r < F.blockSide) :
    lineBond c h r ∈ innerBonds B j := by
  have e : lineBond c h r = (refineSite c.1 + siteOfCoords j (h + (r : ℤ) • basisVector c.2), c.2) :=
    Prod.ext (lineBond_fst c h r) rfl
  rw [e]
  refine bond_mem_innerBonds_of_mem_twoBlockHull hj hodd c hc _ c.2
    (add_smul_basisVector_mem_twoBlockHull hh c.2 hr.le) ?_
  have e2 : h + (r : ℤ) • basisVector c.2 + basisVector c.2 = h + ((r + 1 : ℕ) : ℤ) • basisVector c.2 := by
    push_cast
    rw [add_smul, one_smul]
    abel
  rw [e2]
  exact add_smul_basisVector_mem_twoBlockHull hh c.2 hr
theorem lineBond_injective (hj : j < F.top) (hodd : Odd F.blockSide) {c c' : F.Site (j + 1) × Fin 4}
    {h h' : Fin 4 → ℤ} (hh : h ∈ centredCube F.blockSide) (hh' : h' ∈ centredCube F.blockSide) {r : ℕ}
    (e : lineBond c h r = lineBond c' h' r) : c = c' ∧ h = h' := by
  have e2 : (lineBond c h r).2 = (lineBond c' h' r).2 := by rw [e]
  have e1 : (lineBond c h r).1 = (lineBond c' h' r).1 := by rw [e]
  change c.2 = c'.2 at e2
  change refineSite c.1 + siteOfCoords j h + (r : ℤ) • unitStep j c.2 =
    refineSite c'.1 + siteOfCoords j h' + (r : ℤ) • unitStep j c'.2 at e1
  rw [← e2] at e1
  obtain ⟨a, b⟩ := refineSite_add_injective hj hodd c.1 c'.1 h h' hh hh' (add_right_cancel e1)
  exact ⟨Prod.ext a e2, b⟩
theorem norm_parallelAverage_le (hodd : Odd F.blockSide) (R : F.GaugeField j) (f : F.Site j → Fin 4 → ℍ[ℝ])
    (c : F.Site (j + 1) × Fin 4) :
    ‖parallelAverage R f c‖ ≤
      (1 / (F.blockSide : ℝ) ^ 4) * ∑ h ∈ centredCube F.blockSide, ∑ r ∈ Finset.range F.blockSide,
        ‖f (lineBond c h r).1 (lineBond c h r).2‖ := by
  have hLR : (0 : ℝ) < F.blockSide := by exact_mod_cast hodd.pos
  simp only [parallelAverage, norm_smul]
  have h1 : ‖∑ h ∈ centredCube F.blockSide, ∑ π : Equiv.Perm (Fin 4), ∑ r ∈ Finset.range F.blockSide,
      adjointAction (pathHolonomy R (refineSite c.1) (axisPath h π ++ List.replicate r (c.2, true)))
        (f (refineSite c.1 + siteOfCoords j h + (r : ℤ) • unitStep j c.2) c.2)‖ ≤
      24 * ∑ h ∈ centredCube F.blockSide, ∑ r ∈ Finset.range F.blockSide,
        ‖f (lineBond c h r).1 (lineBond c h r).2‖ := by
    refine le_trans (norm_sum_le _ _) ?_
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro h _
    refine le_trans (norm_sum_le _ _) ?_
    have h2 : ∀ π : Equiv.Perm (Fin 4), ‖∑ r ∈ Finset.range F.blockSide,
        adjointAction (pathHolonomy R (refineSite c.1) (axisPath h π ++ List.replicate r (c.2, true)))
          (f (refineSite c.1 + siteOfCoords j h + (r : ℤ) • unitStep j c.2) c.2)‖ ≤
        ∑ r ∈ Finset.range F.blockSide, ‖f (lineBond c h r).1 (lineBond c h r).2‖ := by
      intro π
      refine le_trans (norm_sum_le _ _) (le_of_eq ?_)
      apply Finset.sum_congr rfl
      intro r _
      rw [norm_adjointAction]
      rfl
    refine le_trans (Finset.sum_le_sum fun π _ => h2 π) (le_of_eq ?_)
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
    simp [Nat.factorial]
  have h3 : ‖(1 / (24 * (F.blockSide : ℝ) ^ 4))‖ = 1 / (24 * (F.blockSide : ℝ) ^ 4) := by
    rw [Real.norm_of_nonneg (by positivity)]
  rw [h3]
  calc 1 / (24 * (F.blockSide : ℝ) ^ 4) * _ ≤ 1 / (24 * (F.blockSide : ℝ) ^ 4) *
        (24 * ∑ h ∈ centredCube F.blockSide, ∑ r ∈ Finset.range F.blockSide,
          ‖f (lineBond c h r).1 (lineBond c h r).2‖) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = _ := by field_simp
theorem sum_lineBond_le {B : Finset F.Cell} (hj : j < F.top) (hodd : Odd F.blockSide)
    (Y : Finset (F.Site (j + 1) × Fin 4)) (hY : Y ⊆ innerBonds B (j + 1)) (g : F.Site j × Fin 4 → ℝ)
    (hg : ∀ b, 0 ≤ g b) (r : ℕ) (hr : r < F.blockSide) :
    ∑ c ∈ Y, ∑ h ∈ centredCube F.blockSide, g (lineBond c h r) ≤ ∑ b ∈ innerBonds B j, g b := by
  classical
  rw [← Finset.sum_product']
  have hinj : Set.InjOn (fun p : (F.Site (j + 1) × Fin 4) × (Fin 4 → ℤ) => lineBond p.1 p.2 r)
      (Y ×ˢ centredCube F.blockSide : Finset _) := by
    intro p hp q hq e
    have hp' := Finset.mem_product.1 (Finset.mem_coe.1 hp)
    have hq' := Finset.mem_product.1 (Finset.mem_coe.1 hq)
    obtain ⟨a, b⟩ := lineBond_injective hj hodd hp'.2 hq'.2 e
    exact Prod.ext a b
  have := Finset.sum_image (f := g) hinj
  rw [← this]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun b _ _ => hg b
  intro b hb
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hb
  have hp' := Finset.mem_product.1 hp
  exact lineBond_mem_innerBonds hj hodd p.1 (hY hp'.1) p.2 hp'.2 r hr
theorem sum_norm_parallelAverage_pow_le {B : Finset F.Cell} (hj : j < F.top) (hodd : Odd F.blockSide)
    (Y : Finset (F.Site (j + 1) × Fin 4)) (hY : Y ⊆ innerBonds B (j + 1)) (R : F.GaugeField j)
    (f : F.Site j → Fin 4 → ℍ[ℝ]) (n : ℕ) :
    ∑ c ∈ Y, ‖parallelAverage R f c‖ ^ (n + 1) ≤
      ((1 / (F.blockSide : ℝ) ^ 4) ^ (n + 1) * ((F.blockSide : ℝ) ^ 5) ^ n * F.blockSide) *
        ∑ b ∈ innerBonds B j, ‖f b.1 b.2‖ ^ (n + 1) := by
  classical
  have hLR : (0 : ℝ) < F.blockSide := by exact_mod_cast hodd.pos
  set s : Finset ((Fin 4 → ℤ) × ℕ) := centredCube F.blockSide ×ˢ Finset.range F.blockSide with hs
  have hcard : (s.card : ℝ) = (F.blockSide : ℝ) ^ 5 := by
    rw [hs, Finset.card_product, card_centredCube hodd, Finset.card_range]
    push_cast
    ring
  have hcard0 : (0 : ℝ) < (s.card : ℝ) := by
    rw [hcard]
    positivity
  set φ : (F.Site (j + 1) × Fin 4) → (Fin 4 → ℤ) × ℕ → ℝ := fun c p =>
    ‖f (lineBond c p.1 p.2).1 (lineBond c p.1 p.2).2‖ with hφ
  have hone : ∀ c, ‖parallelAverage R f c‖ ^ (n + 1) ≤
      (1 / (F.blockSide : ℝ) ^ 4) ^ (n + 1) * ((F.blockSide : ℝ) ^ 5) ^ n * ∑ p ∈ s, φ c p ^ (n + 1) := by
    intro c
    have h1 := norm_parallelAverage_le hodd R f c
    have h2 : ∑ h ∈ centredCube F.blockSide, ∑ r ∈ Finset.range F.blockSide,
        ‖f (lineBond c h r).1 (lineBond c h r).2‖ = ∑ p ∈ s, φ c p := by
      rw [hs, Finset.sum_product]
    rw [h2] at h1
    have h3 : (∑ p ∈ s, φ c p) ^ (n + 1) / (s.card : ℝ) ^ n ≤ ∑ p ∈ s, φ c p ^ (n + 1) :=
      pow_sum_div_card_le_sum_pow (fun _ _ => norm_nonneg _) n
    rw [div_le_iff₀ (by positivity), hcard] at h3
    calc ‖parallelAverage R f c‖ ^ (n + 1) ≤ ((1 / (F.blockSide : ℝ) ^ 4) * ∑ p ∈ s, φ c p) ^ (n + 1) :=
          pow_le_pow_left₀ (norm_nonneg _) h1 _
      _ = (1 / (F.blockSide : ℝ) ^ 4) ^ (n + 1) * (∑ p ∈ s, φ c p) ^ (n + 1) := by rw [mul_pow]
      _ ≤ (1 / (F.blockSide : ℝ) ^ 4) ^ (n + 1) *
            ((∑ p ∈ s, φ c p ^ (n + 1)) * ((F.blockSide : ℝ) ^ 5) ^ n) :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = _ := by ring
  have hsum : ∑ c ∈ Y, ∑ p ∈ s, φ c p ^ (n + 1) ≤
      F.blockSide * ∑ b ∈ innerBonds B j, ‖f b.1 b.2‖ ^ (n + 1) := by
    have e : ∑ c ∈ Y, ∑ p ∈ s, φ c p ^ (n + 1) = ∑ r ∈ Finset.range F.blockSide, ∑ c ∈ Y,
        ∑ h ∈ centredCube F.blockSide, ‖f (lineBond c h r).1 (lineBond c h r).2‖ ^ (n + 1) := by
      calc ∑ c ∈ Y, ∑ p ∈ s, φ c p ^ (n + 1)
          = ∑ c ∈ Y, ∑ r ∈ Finset.range F.blockSide, ∑ h ∈ centredCube F.blockSide,
              ‖f (lineBond c h r).1 (lineBond c h r).2‖ ^ (n + 1) :=
            Finset.sum_congr rfl fun c _ => by
              rw [hs, Finset.sum_product, Finset.sum_comm]
        _ = _ := Finset.sum_comm
    rw [e]
    have hb : ∀ r ∈ Finset.range F.blockSide, ∑ c ∈ Y, ∑ h ∈ centredCube F.blockSide,
        ‖f (lineBond c h r).1 (lineBond c h r).2‖ ^ (n + 1) ≤ ∑ b ∈ innerBonds B j, ‖f b.1 b.2‖ ^ (n + 1) :=
      fun r hr => sum_lineBond_le hj hodd Y hY (fun b => ‖f b.1 b.2‖ ^ (n + 1)) (fun _ => by positivity) r
        (Finset.mem_range.1 hr)
    refine (Finset.sum_le_sum hb).trans (le_of_eq ?_)
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  calc ∑ c ∈ Y, ‖parallelAverage R f c‖ ^ (n + 1)
      ≤ ∑ c ∈ Y, (1 / (F.blockSide : ℝ) ^ 4) ^ (n + 1) * ((F.blockSide : ℝ) ^ 5) ^ n *
          ∑ p ∈ s, φ c p ^ (n + 1) :=
        Finset.sum_le_sum fun c _ => hone c
    _ = (1 / (F.blockSide : ℝ) ^ 4) ^ (n + 1) * ((F.blockSide : ℝ) ^ 5) ^ n *
          ∑ c ∈ Y, ∑ p ∈ s, φ c p ^ (n + 1) := by
        rw [Finset.mul_sum]
    _ ≤ (1 / (F.blockSide : ℝ) ^ 4) ^ (n + 1) * ((F.blockSide : ℝ) ^ 5) ^ n *
          (F.blockSide * ∑ b ∈ innerBonds B j, ‖f b.1 b.2‖ ^ (n + 1)) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by ring
theorem sum_norm_parallelAverage_pow_four_le {B : Finset F.Cell} (hj : j < F.top) (hodd : Odd F.blockSide)
    (Y : Finset (F.Site (j + 1) × Fin 4)) (hY : Y ⊆ innerBonds B (j + 1)) (R : F.GaugeField j)
    (f : F.Site j → Fin 4 → ℍ[ℝ]) :
    ∑ c ∈ Y, ‖parallelAverage R f c‖ ^ 4 ≤ ∑ b ∈ innerBonds B j, ‖f b.1 b.2‖ ^ 4 := by
  have hLR : (0 : ℝ) < F.blockSide := by exact_mod_cast hodd.pos
  have h := sum_norm_parallelAverage_pow_le hj hodd Y hY R f 3
  have e : (1 / (F.blockSide : ℝ) ^ 4) ^ (3 + 1) * ((F.blockSide : ℝ) ^ 5) ^ 3 * F.blockSide = 1 := by
    rw [div_pow, one_pow, ← pow_mul, ← pow_mul]
    field_simp
    ring
  rw [e, one_mul] at h
  exact h
theorem sum_norm_parallelAverage_sq_le {B : Finset F.Cell} (hj : j < F.top) (hodd : Odd F.blockSide)
    (Y : Finset (F.Site (j + 1) × Fin 4)) (hY : Y ⊆ innerBonds B (j + 1)) (R : F.GaugeField j)
    (f : F.Site j → Fin 4 → ℍ[ℝ]) :
    ∑ c ∈ Y, ‖parallelAverage R f c‖ ^ 2 ≤
      (1 / (F.blockSide : ℝ) ^ 2) * ∑ b ∈ innerBonds B j, ‖f b.1 b.2‖ ^ 2 := by
  have hLR : (0 : ℝ) < F.blockSide := by exact_mod_cast hodd.pos
  have h := sum_norm_parallelAverage_pow_le hj hodd Y hY R f 1
  have e : (1 / (F.blockSide : ℝ) ^ 4) ^ (1 + 1) * ((F.blockSide : ℝ) ^ 5) ^ 1 * F.blockSide =
      1 / (F.blockSide : ℝ) ^ 2 := by
    rw [div_pow, one_pow, ← pow_mul, ← pow_mul]
    field_simp
    ring
  rw [e] at h
  exact h
def hullBox (L : ℕ) : Finset Lattice4 := Fintype.piFinset fun _ => Finset.Icc (-(L : ℤ)) (2 * L)
theorem mem_hullBox {L : ℕ} {i : Fin 4} {a : Lattice4} (ha : a ∈ twoBlockHull L i) (hL : 1 ≤ L) :
    a ∈ hullBox L := by
  refine Fintype.mem_piFinset.2 fun μ => Finset.mem_Icc.2 ?_
  have h := ha μ
  have h2 : (if μ = i then (L : ℤ) else 0) ≤ L := by split_ifs <;> omega
  constructor <;> omega
open Classical in
def hullSum (g : F.Site j × Fin 4 → ℝ) (c : F.Site (j + 1) × Fin 4) : ℝ :=
  ∑ a ∈ hullBox F.blockSide, ∑ k : Fin 4,
    if a ∈ twoBlockHull F.blockSide c.2 ∧ a + basisVector k ∈ twoBlockHull F.blockSide c.2 then
      g (refineSite c.1 + siteOfCoords j a, k) else 0
theorem le_hullSum (hL : 1 ≤ F.blockSide) (g : F.Site j × Fin 4 → ℝ) (hg : ∀ b, 0 ≤ g b)
    (c : F.Site (j + 1) × Fin 4) {a : Lattice4} (k : Fin 4) (ha : a ∈ twoBlockHull F.blockSide c.2)
    (ha' : a + basisVector k ∈ twoBlockHull F.blockSide c.2) :
    g (refineSite c.1 + siteOfCoords j a, k) ≤ hullSum g c := by
  classical
  unfold hullSum
  have hnn : ∀ a' ∈ hullBox F.blockSide, ∀ k' ∈ (Finset.univ : Finset (Fin 4)), 0 ≤
      (if a' ∈ twoBlockHull F.blockSide c.2 ∧ a' + basisVector k' ∈ twoBlockHull F.blockSide c.2 then
        g (refineSite c.1 + siteOfCoords j a', k') else 0) := by
    intro a' _ k' _
    split_ifs
    · exact hg _
    · exact le_rfl
  have h1 := Finset.single_le_sum (f := fun a' => ∑ k' : Fin 4,
      if a' ∈ twoBlockHull F.blockSide c.2 ∧ a' + basisVector k' ∈ twoBlockHull F.blockSide c.2 then
        g (refineSite c.1 + siteOfCoords j a', k') else 0)
    (fun a' ha'' => Finset.sum_nonneg (hnn a' ha'')) (mem_hullBox ha hL)
  have h2 := Finset.single_le_sum (f := fun k' => if a ∈ twoBlockHull F.blockSide c.2 ∧
      a + basisVector k' ∈ twoBlockHull F.blockSide c.2 then g (refineSite c.1 + siteOfCoords j a, k') else 0)
    (hnn a (mem_hullBox ha hL)) (Finset.mem_univ k)
  simp only [if_pos (And.intro ha ha')] at h2
  exact h2.trans h1
theorem sum_hullSum_le {B : Finset F.Cell} (hj : j < F.top) (hodd : Odd F.blockSide)
    (Y : Finset (F.Site (j + 1) × Fin 4)) (hY : Y ⊆ innerBonds B (j + 1)) (g : F.Site j × Fin 4 → ℝ)
    (hg : ∀ b, 0 ≤ g b) :
    ∑ c ∈ Y, hullSum g c ≤ (16 * (hullBox F.blockSide).card : ℝ) * ∑ b ∈ innerBonds B j, g b := by
  classical
  have hone : ∀ (a : Lattice4) (k i : Fin 4), ∑ c ∈ Y.filter (fun c => c.2 = i),
      (if a ∈ twoBlockHull F.blockSide c.2 ∧ a + basisVector k ∈ twoBlockHull F.blockSide c.2 then
        g (refineSite c.1 + siteOfCoords j a, k) else 0) ≤ ∑ b ∈ innerBonds B j, g b := by
    intro a k i
    rw [← Finset.sum_filter]
    have hinj : Set.InjOn
        (fun c : F.Site (j + 1) × Fin 4 => ((refineSite c.1 + siteOfCoords j a, k) : F.Site j × Fin 4))
        (((Y.filter fun c => c.2 = i).filter fun c => a ∈ twoBlockHull F.blockSide c.2 ∧
          a + basisVector k ∈ twoBlockHull F.blockSide c.2 : Finset _) : Set _) := by
      intro c hc c' hc' e
      have h1 := Finset.mem_filter.1 (Finset.mem_filter.1 (Finset.mem_coe.1 hc)).1
      have h2 := Finset.mem_filter.1 (Finset.mem_filter.1 (Finset.mem_coe.1 hc')).1
      have e1 : refineSite c.1 + siteOfCoords j a = refineSite c'.1 + siteOfCoords j a := congrArg Prod.fst e
      have hd : refineSite c.1 + siteOfCoords j (0 : Lattice4) = refineSite c'.1 + siteOfCoords j (0 : Lattice4) := by
        rw [siteOfCoords_zero, add_zero, add_zero]
        exact add_right_cancel e1
      have h0 : (0 : Lattice4) ∈ centredCube F.blockSide := (mem_centredCube_iff _ _).2 fun l => by
        have := hodd.pos
        simp only [Pi.zero_apply]
        omega
      exact Prod.ext (refineSite_add_injective hj hodd c.1 c'.1 0 0 h0 h0 hd).1 (h1.2.trans h2.2.symm)
    have := Finset.sum_image (f := g) hinj
    rw [← this]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun b _ _ => hg b
    intro b hb
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 hb
    have h1 := Finset.mem_filter.1 hc
    have h2 := Finset.mem_filter.1 h1.1
    exact bond_mem_innerBonds_of_mem_twoBlockHull hj hodd c (hY h2.1) a k h1.2.1 h1.2.2
  have hfib : ∀ (a : Lattice4) (k : Fin 4), ∑ c ∈ Y,
      (if a ∈ twoBlockHull F.blockSide c.2 ∧ a + basisVector k ∈ twoBlockHull F.blockSide c.2 then
        g (refineSite c.1 + siteOfCoords j a, k) else 0) ≤ 4 * ∑ b ∈ innerBonds B j, g b := by
    intro a k
    rw [← Finset.sum_fiberwise Y (fun c => c.2)]
    refine (Finset.sum_le_sum fun i _ => hone a k i).trans (le_of_eq ?_)
    simp
  unfold hullSum
  rw [Finset.sum_comm]
  have h1 : ∀ a ∈ hullBox F.blockSide, ∑ c ∈ Y, ∑ k : Fin 4,
      (if a ∈ twoBlockHull F.blockSide c.2 ∧ a + basisVector k ∈ twoBlockHull F.blockSide c.2 then
        g (refineSite c.1 + siteOfCoords j a, k) else 0) ≤ 16 * ∑ b ∈ innerBonds B j, g b := by
    intro a _
    rw [Finset.sum_comm]
    refine (Finset.sum_le_sum fun k _ => hfib a k).trans (le_of_eq ?_)
    simp
    ring
  refine (Finset.sum_le_sum h1).trans (le_of_eq ?_)
  simp
  ring
end Lines
section Units
theorem coe_unitQuaternion_mul (a b : UnitQuaternion) :
    ((a * b : UnitQuaternion) : ℍ[ℝ]) = (a : ℍ[ℝ]) * (b : ℍ[ℝ]) := rfl
theorem polarUnit_coe (g : UnitQuaternion) : polarUnit (g : ℍ[ℝ]) = g := by
  apply Subtype.ext
  rw [coe_polarUnit (coe_unitQuaternion_ne_zero g), norm_coe_unitQuaternion]
  simp
theorem adjointAction_sub (g : UnitQuaternion) (x y : ℍ[ℝ]) :
    adjointAction g (x - y) = adjointAction g x - adjointAction g y := by
  simp only [adjointAction, mul_sub, sub_mul]
theorem pureComponent_adjointAction (g : UnitQuaternion) (q : ℍ[ℝ]) :
    pureComponent (adjointAction g q) = adjointAction g (pureComponent q) := by
  have hs : star (adjointAction g q) = adjointAction g (star q) := by
    simp only [adjointAction, star_mul, coe_unitQuaternion_inv, star_star, mul_assoc]
  simp only [pureComponent, hs, ← adjointAction_sub]
  simp only [adjointAction, Algebra.mul_smul_comm, Algebra.smul_mul_assoc]
theorem norm_pureComponent_coe_le (g : UnitQuaternion) :
    ‖pureComponent (g : ℍ[ℝ])‖ ≤ ‖(g : ℍ[ℝ]) - 1‖ := by
  have : pureComponent (g : ℍ[ℝ]) = pureComponent ((g : ℍ[ℝ]) - 1) := by
    rw [pureComponent_sub, pureComponent_one, sub_zero]
  rw [this]
  exact norm_pureComponent_le _
theorem norm_pureComponent_mul_sub_le (g w : UnitQuaternion) :
    ‖pureComponent ((g * w : UnitQuaternion) : ℍ[ℝ]) - pureComponent (g : ℍ[ℝ]) - pureComponent (w : ℍ[ℝ])‖ ≤
      ‖(g : ℍ[ℝ]) - 1‖ * ‖(w : ℍ[ℝ]) - 1‖ := by
  have e : ((g * w : UnitQuaternion) : ℍ[ℝ]) =
      (g : ℍ[ℝ]) + (w : ℍ[ℝ]) - 1 + ((g : ℍ[ℝ]) - 1) * ((w : ℍ[ℝ]) - 1) := by
    rw [coe_unitQuaternion_mul]
    noncomm_ring
  rw [e, pureComponent_add, pureComponent_sub, pureComponent_add, pureComponent_one, sub_zero]
  have : pureComponent (g : ℍ[ℝ]) + pureComponent (w : ℍ[ℝ]) +
      pureComponent (((g : ℍ[ℝ]) - 1) * ((w : ℍ[ℝ]) - 1)) -
      pureComponent (g : ℍ[ℝ]) - pureComponent (w : ℍ[ℝ]) =
      pureComponent (((g : ℍ[ℝ]) - 1) * ((w : ℍ[ℝ]) - 1)) := by
    abel
  rw [this]
  exact (norm_pureComponent_le _).trans (norm_mul_le _ _)
theorem norm_sub_one_le_two_mul_pureComponent (g : UnitQuaternion) (h : 0 ≤ ((g : ℍ[ℝ])).re) :
    ‖(g : ℍ[ℝ]) - 1‖ ≤ 2 * ‖pureComponent (g : ℍ[ℝ])‖ := by
  have := norm_polarUnit_sub_one_le h (coe_unitQuaternion_ne_zero g)
  rw [polarUnit_coe, norm_coe_unitQuaternion, div_one] at this
  exact this
theorem re_nonneg_of_norm_sub_one_le (g : UnitQuaternion) (h : ‖(g : ℍ[ℝ]) - 1‖ ≤ 1) :
    0 ≤ ((g : ℍ[ℝ])).re := by
  have h2 := quaternion_re_le_norm (1 - (g : ℍ[ℝ]))
  have h3 : (1 - (g : ℍ[ℝ])).re = 1 - ((g : ℍ[ℝ])).re := by simp
  rw [h3, norm_sub_rev] at h2
  linarith
theorem norm_adjointAction_sub_le (m : UnitQuaternion) (x : ℍ[ℝ]) :
    ‖adjointAction m x - x‖ ≤ 2 * ‖(m : ℍ[ℝ]) - 1‖ * ‖x‖ := by
  have e : adjointAction m x - x = ((m : ℍ[ℝ]) - 1) * x * ((m⁻¹ : UnitQuaternion) : ℍ[ℝ]) +
      x * (((m⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1) := by
    simp only [adjointAction]
    noncomm_ring
  rw [e]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul, norm_mul, norm_coe_unitQuaternion, mul_one, norm_coe_inv_sub_one]
  nlinarith [mul_nonneg (norm_nonneg ((m : ℍ[ℝ]) - 1)) (norm_nonneg x)]
end Units
end BlockLines
end YangMills.Construction
end
