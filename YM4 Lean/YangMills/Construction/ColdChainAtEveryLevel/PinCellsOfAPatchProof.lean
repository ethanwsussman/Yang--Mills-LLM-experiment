import YangMills.Construction.ColdChainAtEveryLevel.GaugeFixedCellsOfAPatchForm
import YangMills.Construction.ColdChainAtEveryLevel.MeansOfAPotential
import YangMills.Construction.ColdChainAtEveryLevel.PathsBetweenTheCellsOfAPatch
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
namespace PatchCellConditions
open BlockAverages GaugeMap LatticeFractionalIntegration
variable {F : BlockFrame} {S : Finset F.Cell} {z : F.Cell}
theorem iteratedBlockAverage_eq_nestedAverage (f : F.Site 0 → Fin 4 → ℍ[ℝ]) :
    ∀ j, iteratedBlockAverage f j = nestedAverage f j := by
  intro j
  induction j with
  | zero => rfl
  | succ j ih =>
    funext y i
    show _ = bondLineAverage (nestedAverage f j) (y, i)
    simp only [iteratedBlockAverage, bondLineAverage, ih]
theorem iteratedBlockAverage_top_eq_sum (hodd : Odd F.blockSide) (f : F.Site 0 → Fin 4 → ℍ[ℝ]) (y : F.Cell)
    (i : Fin 4) :
    iteratedBlockAverage f F.top y i = (1 / (cellSideLength F : ℝ) ^ 4) •
      ∑ h ∈ centredCube (F.blockSide ^ F.top), ∑ r ∈ Finset.range (F.blockSide ^ F.top),
        f (cellCentre 0 y + siteOfCoords 0 h + (r : ℤ) • unitStep 0 i) i := by
  rw [iteratedBlockAverage_eq_nestedAverage]
  exact PotentialMeans.nestedAverage_top_eq hodd f y i
def patchBondOf (S : Finset F.Cell) (z : F.Cell) (t : F.Site 0) (i : Fin 4) : Lattice4 × Fin 4 :=
  if closedOrthant S z i = 1 then (patchChart S z t, i) else (patchChart S z (t + unitStep 0 i), i)
theorem patchBondOf_spec (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    (he : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1)
    {t : F.Site 0} {i : Fin 4} (ht : t ∈ patchBaseSites S z) (ht' : t + unitStep 0 i ∈ patchBaseSites S z) :
    patchBondOf S z t i ∈ bondsOf (patchDomain S z) ∧
      (closedOrthant S z i = 1 → patchChart S z (t + unitStep 0 i) = patchChart S z t + basisVector i) ∧
      (closedOrthant S z i = -1 → patchChart S z t = patchChart S z (t + unitStep 0 i) + basisVector i) := by
  obtain ⟨a, ha, ha', hc⟩ := PatchForms.exists_bond_in_patchChart hamb hodd he (S := S) (z := z) ht ht'
  have hco : ∀ {b : Lattice4}, b ∈ patchDomain S z → patchChart S z (patchSite S z b) = b := fun hb =>
    PatchPoints.patchChart_patchSite hamb hodd he (PatchPoints.patchDomain_coord_bounds hb)
  have hmem : (a, i) ∈ bondsOf (patchDomain S z) :=
    Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨ha, Finset.mem_univ _⟩, ha'⟩
  rcases hc with ⟨hs, e1, e2⟩ | ⟨hs, e1, e2⟩
  · have c1 : patchChart S z t = a := by rw [← e1, hco ha]
    have c2 : patchChart S z (t + unitStep 0 i) = a + basisVector i := by rw [← e2, hco ha']
    refine ⟨?_, fun _ => by rw [c1, c2], fun h => ?_⟩
    · simp only [patchBondOf, hs, if_true, c1]
      exact hmem
    · rw [hs] at h
      norm_num at h
  · have c1 : patchChart S z (t + unitStep 0 i) = a := by rw [← e1, hco ha]
    have c2 : patchChart S z t = a + basisVector i := by rw [← e2, hco ha']
    have hne : closedOrthant S z i ≠ 1 := by rw [hs]; norm_num
    refine ⟨?_, fun h => absurd h hne, fun _ => by rw [c1, c2]⟩
    simp only [patchBondOf, if_neg hne, c1]
    exact hmem
theorem norm_latticeFormAtSites (ν : Lattice4 → Fin 4 → ℍ[ℝ]) (t : F.Site 0) (i : Fin 4) :
    ‖latticeFormAtSites S z ν t i‖ = ‖ν (patchBondOf S z t i).1 (patchBondOf S z t i).2‖ := by
  unfold latticeFormAtSites patchBondOf
  split_ifs
  · rfl
  · rw [norm_neg]
theorem latticeFormAtSites_congr {ν ν' : Lattice4 → Fin 4 → ℍ[ℝ]} {t : F.Site 0} {i : Fin 4}
    (h : ν (patchBondOf S z t i).1 (patchBondOf S z t i).2 = ν' (patchBondOf S z t i).1 (patchBondOf S z t i).2) :
    latticeFormAtSites S z ν t i = latticeFormAtSites S z ν' t i := by
  unfold latticeFormAtSites
  unfold patchBondOf at h
  split_ifs at h ⊢
  · exact h
  · rw [show ν (patchChart S z (t + unitStep 0 i)) i = ν' (patchChart S z (t + unitStep 0 i)) i from h]
theorem latticeFormAtSites_latticeDifference (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    (he : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1)
    (φ : Lattice4 → ℍ[ℝ]) {t : F.Site 0} {i : Fin 4} (ht : t ∈ patchBaseSites S z)
    (ht' : t + unitStep 0 i ∈ patchBaseSites S z) :
    latticeFormAtSites S z (latticeDifference φ) t i =
      φ (patchChart S z (t + unitStep 0 i)) - φ (patchChart S z t) := by
  obtain ⟨-, k1, k2⟩ := patchBondOf_spec hamb hodd he ht ht'
  unfold latticeFormAtSites latticeDifference
  rcases he i with h | h
  · rw [if_pos h, k1 h]
  · have hne : closedOrthant S z i ≠ 1 := by rw [h]; norm_num
    rw [if_neg hne, ← k2 h]
    abel
theorem cellCentre_add_mem_patchBaseSites (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    (he : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1)
    {y : F.Cell} (hy : y ∈ patchCells S z) {h : Lattice4} (hh : h ∈ centredCube (F.blockSide ^ F.top)) :
    cellCentre 0 y + siteOfCoords 0 h ∈ patchBaseSites S z := by
  classical
  have hyP := (Finset.mem_filter.1 hy).2
  rw [baseSite_eq_cellCentre_zero] at hyP
  refine PatchLocality.mem_patchBaseSites_of_same_cell hamb hodd he (zero_mem_centredCube hodd.pow) hh ?_
  rw [siteOfCoords_zero, add_zero]
  exact hyP
theorem line_mem_patchBaseSites (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    (he : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1)
    {y : F.Cell} {i : Fin 4} (hy : y ∈ patchCells S z) (hy' : y + unitStep F.top i ∈ patchCells S z)
    {h : Lattice4} (hh : h ∈ centredCube (F.blockSide ^ F.top)) {r : ℕ} (hr : r ≤ F.blockSide ^ F.top) :
    cellCentre 0 y + siteOfCoords 0 h + (r : ℤ) • unitStep 0 i ∈ patchBaseSites S z := by
  classical
  have h1 := PotentialMeans.mem_cellSites_union_of_line hodd hy hy' hh hr
  have key : ∀ {w : F.Cell}, ∀ {t : F.Site 0}, t ∈ cellSites (patchCells S z) w → t ∈ patchBaseSites S z := by
    intro w t ht
    have h2 := (Finset.mem_filter.1 ht).1
    have h3 := ((mem_sitesOfCells_patchCells_iff hamb hodd he (Nat.zero_le _)).1 h2).2
    rwa [PatchLatticeChart.Framing.baseSite_eq_self] at h3
  rcases Finset.mem_union.1 h1 with h2 | h2
  · exact key h2
  · exact key h2
theorem line_mem_sitesOfCells (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    (he : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1)
    {y : F.Cell} {i : Fin 4} (hy : y ∈ patchCells S z) (hy' : y + unitStep F.top i ∈ patchCells S z)
    {h : Lattice4} (hh : h ∈ centredCube (F.blockSide ^ F.top)) {r : ℕ} (hr : r ≤ F.blockSide ^ F.top) :
    cellCentre 0 y + siteOfCoords 0 h + (r : ℤ) • unitStep 0 i ∈ sitesOfCells (patchCells S z) 0 := by
  classical
  rcases Finset.mem_union.1 (PotentialMeans.mem_cellSites_union_of_line hodd hy hy' hh hr) with h2 | h2
  · exact (Finset.mem_filter.1 h2).1
  · exact (Finset.mem_filter.1 h2).1
theorem add_nsmul_unitStep_succ (t : F.Site 0) (i : Fin 4) (r : ℕ) :
    t + (r : ℤ) • unitStep 0 i + unitStep 0 i = t + ((r + 1 : ℕ) : ℤ) • unitStep 0 i := by
  push_cast
  rw [add_smul, one_smul, add_assoc]
theorem line_bond_mem_innerBonds (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    (he : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1)
    {y : F.Cell} {i : Fin 4} (hy : y ∈ patchCells S z) (hy' : y + unitStep F.top i ∈ patchCells S z)
    {h : Lattice4} (hh : h ∈ centredCube (F.blockSide ^ F.top)) {r : ℕ} (hr : r < F.blockSide ^ F.top) :
    (cellCentre 0 y + siteOfCoords 0 h + (r : ℤ) • unitStep 0 i, i) ∈ innerBonds (patchCells S z) 0 := by
  refine Finset.mem_filter.2
    ⟨Finset.mem_product.2 ⟨line_mem_sitesOfCells hamb hodd he hy hy' hh hr.le, Finset.mem_univ _⟩, ?_⟩
  show cellCentre 0 y + siteOfCoords 0 h + (r : ℤ) • unitStep 0 i + unitStep 0 i ∈ _
  rw [add_nsmul_unitStep_succ]
  exact line_mem_sitesOfCells hamb hodd he hy hy' hh (Nat.succ_le_of_lt hr)
theorem patchChart_injective (he : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1)
    {t t' : F.Site 0} (e : patchChart S z t = patchChart S z t') : t = t' := by
  have h1 := PatchPoints.patchSite_patchChart (S := S) (z := z) he t
  have h2 := PatchPoints.patchSite_patchChart (S := S) (z := z) he t'
  rw [← h1, ← h2, e]
theorem cellMean_eq_siteMean (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    (he : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1)
    (V : F.GaugeField F.top) (W : F.FieldChain) (kW : F.SiteGauge) (X : F.FieldChain) (k : F.SiteGauge)
    (y : F.Cell) (φ : Lattice4 → ℍ[ℝ]) :
    (pinnedGaugeDataOfPatch S V z W kW X k).cellMean y φ =
      PotentialMeans.siteMean (fun t => φ (patchChart S z t)) y := by
  classical
  have hinj : Set.InjOn (fun h : Lattice4 => patchChart S z (cellCentre 0 y + siteOfCoords 0 h))
      (centredCube (F.blockSide ^ F.top) : Set Lattice4) := by
    intro h hh h' hh' e
    exact PatchPotentials.siteOfCoords_injOn_centredCube hamb hodd hh hh'
      (add_left_cancel (patchChart_injective he e))
  unfold PinnedGauge.PinnedGaugeData.cellMean PotentialMeans.siteMean
  have e1 : (((pinnedGaugeDataOfPatch S V z W kW X k).cellSide : ℕ) : ℝ) = (cellSideLength F : ℝ) :=
    PotentialMeans.cellSideLength_natCast F
  rw [e1]
  congr 1
  exact Finset.sum_image (f := φ) hinj
theorem sum_norm_latticeFormAtSites_le (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    (he : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1)
    (f : Lattice4 → Fin 4 → ℍ[ℝ]) (i : Fin 4) (A : Finset (F.Site 0)) [DecidablePred fun t : F.Site 0 =>
      t ∈ patchBaseSites S z ∧ t + unitStep 0 i ∈ patchBaseSites S z] :
    ∑ t ∈ A, (if t ∈ patchBaseSites S z ∧ t + unitStep 0 i ∈ patchBaseSites S z then
        ‖latticeFormAtSites S z f t i‖ ^ 4 else 0) ≤
      ∑ b ∈ bondsOf (patchDomain S z), ‖f b.1 b.2‖ ^ 4 := by
  classical
  rw [← Finset.sum_filter]
  set A' := A.filter fun t => t ∈ patchBaseSites S z ∧ t + unitStep 0 i ∈ patchBaseSites S z with hA'
  have hinj : Set.InjOn (fun t => patchBondOf S z t i) (A' : Set (F.Site 0)) := by
    intro t _ t' _ e
    simp only [patchBondOf] at e
    split_ifs at e
    · exact patchChart_injective he (congrArg Prod.fst e)
    · exact add_right_cancel (patchChart_injective he (congrArg Prod.fst e))
  have e1 : ∑ t ∈ A', ‖latticeFormAtSites S z f t i‖ ^ 4 =
      ∑ b ∈ A'.image (fun t => patchBondOf S z t i), ‖f b.1 b.2‖ ^ 4 := by
    rw [Finset.sum_image hinj]
    exact Finset.sum_congr rfl fun t _ => by rw [norm_latticeFormAtSites]
  rw [e1]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => by positivity
  intro b hb
  obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hb
  obtain ⟨-, h1, h2⟩ := Finset.mem_filter.1 ht
  exact (patchBondOf_spec hamb hodd he h1 h2).1
theorem norm_iteratedBlockAverage_pow_le (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    (he : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1)
    {y : F.Cell} {i : Fin 4} (hy : y ∈ patchCells S z) (hy' : y + unitStep F.top i ∈ patchCells S z)
    (f : Lattice4 → Fin 4 → ℍ[ℝ]) :
    ‖iteratedBlockAverage (latticeFormAtSites S z f) F.top y i‖ ^ 4 ≤
      2 * ∑ b ∈ bondsOf (patchDomain S z), ‖f b.1 b.2‖ ^ 4 := by
  classical
  set N : ℕ := F.blockSide ^ F.top with hNdef
  have hNpos : 0 < N := pow_pos hodd.pos _
  set Nr : ℝ := (cellSideLength F : ℝ) with hNr
  have hNN : (N : ℝ) = Nr := PotentialMeans.cellSideLength_natCast F
  have hNrp : 0 < Nr := by rw [← hNN]; exact_mod_cast hNpos
  set T : Lattice4 → ℕ → F.Site 0 := fun h r => cellCentre 0 y + siteOfCoords 0 h + (r : ℤ) • unitStep 0 i
    with hT
  set a : Lattice4 × ℕ → ℝ := fun p => ‖latticeFormAtSites S z f (T p.1 p.2) i‖ with ha
  set I := centredCube N ×ˢ Finset.range N with hI
  have hcard : ((I.card : ℕ) : ℝ) = Nr ^ 5 := by
    have hc1 : (centredCube N).card = N ^ 4 := LatticePaths.card_centredCube hodd.pow
    rw [hI, Finset.card_product, hc1, Finset.card_range, Nat.cast_mul, Nat.cast_pow, hNN]
    ring
  have h1 : ‖iteratedBlockAverage (latticeFormAtSites S z f) F.top y i‖ ≤ (1 / Nr ^ 4) * ∑ p ∈ I, a p := by
    rw [iteratedBlockAverage_top_eq_sum hodd, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [hI, Finset.sum_product]
    exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun h _ => norm_sum_le _ _)
  have ha0 : ∀ p, 0 ≤ a p := fun p => norm_nonneg _
  have h2 := pow_sum_div_card_le_sum_pow (s := I) (f := a) (fun p _ => ha0 p) 3
  rw [hcard, div_le_iff₀ (by positivity)] at h2
  have h3 : ‖iteratedBlockAverage (latticeFormAtSites S z f) F.top y i‖ ^ 4 ≤ (1 / Nr) * ∑ p ∈ I, a p ^ 4 := by
    calc ‖iteratedBlockAverage (latticeFormAtSites S z f) F.top y i‖ ^ 4 ≤ ((1 / Nr ^ 4) * ∑ p ∈ I, a p) ^ 4 :=
          pow_le_pow_left₀ (norm_nonneg _) h1 4
      _ = (1 / Nr ^ 4) ^ 4 * (∑ p ∈ I, a p) ^ (3 + 1) := by ring
      _ ≤ (1 / Nr ^ 4) ^ 4 * ((∑ p ∈ I, a p ^ (3 + 1)) * (Nr ^ 5) ^ 3) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = (1 / Nr) * ∑ p ∈ I, a p ^ 4 := by
          field_simp
  set B := ∑ b ∈ bondsOf (patchDomain S z), ‖f b.1 b.2‖ ^ 4 with hB
  have hline : ∀ r ∈ Finset.range N, ∑ h ∈ centredCube N, a (h, r) ^ 4 ≤ 2 * B := by
    intro r hr
    have hr' : r < N := Finset.mem_range.1 hr
    set g : F.Site 0 → ℝ := fun t =>
      if t ∈ patchBaseSites S z ∧ t + unitStep 0 i ∈ patchBaseSites S z then
        ‖latticeFormAtSites S z f t i‖ ^ 4 else 0 with hg
    have hg0 : ∀ t, 0 ≤ g t := by
      intro t
      simp only [hg]
      split_ifs
      · positivity
      · exact le_rfl
    have h4 := PotentialMeans.sum_line_le hamb hodd hy hy' g hg0 hr'.le
    have h5 : ∑ h ∈ centredCube N, a (h, r) ^ 4 = ∑ h ∈ centredCube N, g (T h r) := by
      refine Finset.sum_congr rfl fun h hh => ?_
      have t1 := line_mem_patchBaseSites hamb hodd he hy hy' hh hr'.le
      have t2 := line_mem_patchBaseSites hamb hodd he hy hy' hh (Nat.succ_le_of_lt hr')
      rw [← add_nsmul_unitStep_succ] at t2
      simp only [hg]
      rw [if_pos ⟨t1, t2⟩]
    rw [h5]
    have h6 := sum_norm_latticeFormAtSites_le hamb hodd he f i (cellSites (patchCells S z) y)
    have h7 := sum_norm_latticeFormAtSites_le hamb hodd he f i (cellSites (patchCells S z) (y + unitStep F.top i))
    refine h4.trans ?_
    simp only [hg]
    linarith
  have h8 : ∑ p ∈ I, a p ^ 4 ≤ Nr * (2 * B) := by
    rw [hI, Finset.sum_product, Finset.sum_comm]
    refine (Finset.sum_le_sum hline).trans ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, hNN]
  calc _ ≤ (1 / Nr) * ∑ p ∈ I, a p ^ 4 := h3
    _ ≤ (1 / Nr) * (Nr * (2 * B)) := mul_le_mul_of_nonneg_left h8 (by positivity)
    _ = 2 * B := by field_simp
end PatchCellConditions
set_option maxHeartbeats 800000 in
open PatchCellConditions BlockAverages GaugeMap LatticeFractionalIntegration in
theorem BlockAverages.patchCellConditions_holds : BlockAverages.patchCellConditionsStatement := by
  refine ⟨2, 344 ^ 4, by norm_num, by positivity, ?_⟩
  intro F m S hodd hamb hm hreg V z W kW X k hz
  classical
  obtain ⟨he, -⟩ := closedOrthant_spec hreg (by omega) z
  have hN := cellSideLength_pos (F := F) hodd.pos
  have htn : (((cellSideLength F).toNat : ℕ) : ℤ) = ((F.blockSide ^ F.top : ℕ) : ℤ) := by
    rw [Int.toNat_of_nonneg hN.le]
    simp [cellSideLength]
  have htn' : (cellSideLength F).toNat = F.blockSide ^ F.top := by exact_mod_cast htn
  have hzP : z ∈ patchCells S z := by
    refine Finset.mem_filter.2 ⟨hz, ?_⟩
    rw [baseSite_eq_cellCentre_zero]
    have := PatchLocality.mem_patchBaseSites_of_cellSupDist_le hamb hodd he hz
      (by rw [PatchLocality.cellSupDist_self]; omega) (zero_mem_centredCube hodd.pow)
    rwa [siteOfCoords_zero, add_zero] at this
  have hbig : ∀ {y y' : F.Cell}, y' ∈ patchCells S z → (hadj : ∃ i, y' = y + unitStep F.top i) →
      y + unitStep F.top hadj.choose ∈ patchCells S z := by
    intro y y' hy' hadj
    rw [← hadj.choose_spec]
    exact hy'
  have add_ : ∀ (y y' : F.Cell), (∃ i, y' = y + unitStep F.top i) → ∀ f g : Lattice4 → Fin 4 → ℍ[ℝ],
      lineAverage S z y y' (f + g) = lineAverage S z y y' f + lineAverage S z y y' g := by
    intro y y' hadj f g
    unfold lineAverage
    rw [dif_pos hadj, dif_pos hadj, dif_pos hadj, iteratedBlockAverage_top_eq_sum hodd,
      iteratedBlockAverage_top_eq_sum hodd, iteratedBlockAverage_top_eq_sum hodd, ← smul_add,
      ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun r _ => ?_
    unfold latticeFormAtSites
    split_ifs
    · rfl
    · simp only [Pi.add_apply]
      abel
  have congr_ : ∀ (y y' : F.Cell), y ∈ patchCells S z → y' ∈ patchCells S z →
      (∃ i, y' = y + unitStep F.top i) →
      ∀ f g : Lattice4 → Fin 4 → ℍ[ℝ], (∀ b ∈ bondsOf (patchDomain S z), f b.1 b.2 = g b.1 b.2) →
      lineAverage S z y y' f = lineAverage S z y y' g := by
    intro y y' hy hy' hadj f g hfg
    unfold lineAverage
    rw [dif_pos hadj, dif_pos hadj, iteratedBlockAverage_top_eq_sum hodd, iteratedBlockAverage_top_eq_sum hodd]
    congr 1
    refine Finset.sum_congr rfl fun h hh => Finset.sum_congr rfl fun r hr => ?_
    have hr' := Finset.mem_range.1 hr
    have t1 := line_mem_patchBaseSites hamb hodd he hy (hbig hy' hadj) hh hr'.le
    have t2 := line_mem_patchBaseSites hamb hodd he hy (hbig hy' hadj) hh (Nat.succ_le_of_lt hr')
    rw [← add_nsmul_unitStep_succ] at t2
    exact latticeFormAtSites_congr (hfg _ (patchBondOf_spec hamb hodd he t1 t2).1)
  have diff_ : ∀ (y y' : F.Cell), y ∈ patchCells S z → y' ∈ patchCells S z →
      (∃ i, y' = y + unitStep F.top i) →
      ∀ φ : Lattice4 → ℍ[ℝ], lineAverage S z y y' (latticeDifference φ) =
        PotentialMeans.siteMean (fun t => φ (patchChart S z t)) y' -
          PotentialMeans.siteMean (fun t => φ (patchChart S z t)) y := by
    intro y y' hy hy' hadj φ
    unfold lineAverage
    rw [dif_pos hadj, iteratedBlockAverage_top_eq_sum hodd]
    have hi := hadj.choose_spec
    set i := hadj.choose with hidef
    rw [hi, ← PotentialMeans.sum_lines_eq_siteMean_sub]
    congr 1
    refine Finset.sum_congr rfl fun h hh => Finset.sum_congr rfl fun r hr => ?_
    have hr' := Finset.mem_range.1 hr
    have hyn : y + unitStep F.top i ∈ patchCells S z := hi ▸ hy'
    have t1 := line_mem_patchBaseSites hamb hodd he hy hyn hh hr'.le
    have t2 := line_mem_patchBaseSites hamb hodd he hy hyn hh (Nat.succ_le_of_lt hr')
    rw [← add_nsmul_unitStep_succ] at t2
    exact latticeFormAtSites_latticeDifference hamb hodd he φ t1 t2
  have le_ : ∀ (y y' : F.Cell), y ∈ patchCells S z → y' ∈ patchCells S z →
      (∃ i, y' = y + unitStep F.top i) →
      ∀ f : Lattice4 → Fin 4 → ℍ[ℝ],
        ‖lineAverage S z y y' f‖ ^ 4 ≤ 2 * ∑ b ∈ bondsOf (patchDomain S z), ‖f b.1 b.2‖ ^ 4 := by
    intro y y' hy hy' hadj f
    unfold lineAverage
    rw [dif_pos hadj]
    exact norm_iteratedBlockAverage_pow_le hamb hodd he hy (hbig hy' hadj) f
  refine ⟨⟨BondShares.patchDomain_isFilledToward hz he hodd.pos, ?_, pow_pos hodd.pos _, ?_, ?_, ?_, hzP, ?_,
    fun y _ y' _ hadj f g => add_ y y' hadj f g,
    fun y hy y' hy' hadj f g hfg => congr_ y y' hy hy' hadj f g hfg,
    fun y hy y' hy' hadj φ => ?_,
    fun y hy y' hy' hadj f => le_ y y' hy hy' hadj f, ?_⟩, ?_⟩
  · show 1 ≤ 9 * (cellSideLength F).toNat
    omega
  · show ((9 * (cellSideLength F).toNat : ℕ) : ℝ) ≤ 9 * ((F.blockSide ^ F.top : ℕ) : ℝ)
    rw [htn']
    push_cast
    exact le_rfl
  · intro y hy x hx
    obtain ⟨h, hh, rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨a, ha, e⟩ := Finset.mem_image.1 (cellCentre_add_mem_patchBaseSites hamb hodd he hy hh)
    rw [← e, PatchPoints.patchChart_patchSite hamb hodd he (PatchPoints.patchDomain_coord_bounds ha)]
    exact ha
  · intro y _
    have hinj : Set.InjOn (fun h : Lattice4 => patchChart S z (cellCentre 0 y + siteOfCoords 0 h))
        (centredCube (F.blockSide ^ F.top) : Set Lattice4) := by
      intro h hh h' hh' e
      exact PatchPotentials.siteOfCoords_injOn_centredCube hamb hodd hh hh'
        (add_left_cancel (patchChart_injective he e))
    exact (Finset.card_image_of_injOn hinj).trans (LatticePaths.card_centredCube hodd.pow)
  · exact_mod_cast card_patchCells_le hamb hodd he
  · have e1 := cellMean_eq_siteMean (S := S) (z := z) hamb hodd he V W kW X k y' φ
    have e2 := cellMean_eq_siteMean (S := S) (z := z) hamb hodd he V W kW X k y φ
    rw [e1, e2]
    exact diff_ y y' hy hy' hadj φ
  · intro κ T hT hκ hκz y hy
    set η : ℝ := Real.sqrt (Real.sqrt T) with hη
    have hη0 : 0 ≤ η := Real.sqrt_nonneg _
    have hη4 : η ^ 4 = T := by
      have e : η ^ 4 = (η ^ 2) ^ 2 := by ring
      rw [e, hη, Real.sq_sqrt (Real.sqrt_nonneg _), Real.sq_sqrt hT]
    have hΦ : ∀ c ∈ innerBonds (patchCells S z) F.top, |‖κ c.1‖ - ‖κ (c.1 + unitStep F.top c.2)‖| ≤ η := by
      intro c hc
      have h1 : c.1 ∈ patchCells S z :=
        mem_sitesOfCells_top.1 (Finset.mem_product.1 (Finset.mem_filter.1 hc).1).1
      have h2 : c.1 + unitStep F.top c.2 ∈ patchCells S z := mem_sitesOfCells_top.1 (Finset.mem_filter.1 hc).2
      have h3 := hκ c.1 h1 _ h2 ⟨c.2, rfl⟩
      have h4 : ‖κ c.1 - κ (c.1 + unitStep F.top c.2)‖ ≤ η := by
        rw [← hη4] at h3
        exact le_of_pow_le_pow_left₀ (by norm_num) hη0 h3
      exact (abs_norm_sub_norm_le _ _).trans h4
    have h1 := PatchPaths.abs_sub_le_of_mem_patchCells hamb hodd hreg (by omega) he (fun y => ‖κ y‖) η hη0 hΦ hzP hy
    have hz0 : κ z = 0 := hκz
    simp only [hz0, norm_zero, sub_zero, abs_norm] at h1
    calc ‖κ y‖ ^ 4 ≤ (344 * η) ^ 4 := pow_le_pow_left₀ (norm_nonneg _) h1 4
      _ = 344 ^ 4 * T := by rw [mul_pow, hη4]
  · intro f g hfg c hc
    have hc' : c ∈ innerBonds (patchCells S z) F.top := by
      rw [innerBonds_patchCells hamb hodd he (le_refl _)]
      exact hc
    have h1 : c.1 ∈ patchCells S z :=
      mem_sitesOfCells_top.1 (Finset.mem_product.1 (Finset.mem_filter.1 hc').1).1
    have h2 : c.1 + unitStep F.top c.2 ∈ patchCells S z := mem_sitesOfCells_top.1 (Finset.mem_filter.1 hc').2
    rw [iteratedBlockAverage_top_eq_sum hodd, iteratedBlockAverage_top_eq_sum hodd]
    congr 1
    refine Finset.sum_congr rfl fun h hh => Finset.sum_congr rfl fun r hr => ?_
    have hr' := Finset.mem_range.1 hr
    refine hfg (_, c.2) ?_
    rw [← innerBonds_patchCells hamb hodd he (Nat.zero_le _)]
    exact line_bond_mem_innerBonds hamb hodd he h1 h2 hh hr'
end YangMills.Construction
end
