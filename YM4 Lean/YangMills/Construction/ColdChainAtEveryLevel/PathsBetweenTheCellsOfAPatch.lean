import YangMills.Construction.ColdChainAtEveryLevel.CellsOfAPatch
import YangMills.Construction.ColdChainAtEveryLevel.PointsOfAPatchForm
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.PatchPaths
open BlockAverages GaugeMap PatchPoints LatticeFractionalIntegration FiniteDifferences BlockAverages.PatchLocality
variable {F : BlockFrame} {S : Finset F.Cell} {z : F.Cell}
def patchHeight (S : Finset F.Cell) (z y : F.Cell) (i : Fin 4) : ℤ :=
  closedOrthant S z i * cellDisplacement z y i
theorem exists_patchDomain_cellCentre (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    (hsg : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1)
    {y : F.Cell} (hy : y ∈ patchCells S z) :
    ∃ x' ∈ patchDomain S z, patchSite S z x' = cellCentre 0 y ∧
      ∀ i, x' i = cellSideLength F * patchHeight S z y i + (cellSideLength F - 1) / 2 := by
  classical
  have hyP := (Finset.mem_filter.1 hy).2
  rw [baseSite_eq_cellCentre_zero] at hyP
  obtain ⟨x', hx', e⟩ := Finset.mem_image.1 hyP
  refine ⟨x', hx', e, fun i => ?_⟩
  have hr := Fintype.mem_piFinset.1 (Finset.mem_filter.1 hx').1
  have hL : 0 < F.blockSide := hodd.pos
  obtain ⟨hc0, hc1⟩ := cellSideLength_half (F := F) hodd
  set m := (cellSideLength F - 1) / 2 with hm
  set σ := closedOrthant S z with hσ
  have hAb : ∀ i, |σ i * (x' i - m)| ≤ ((22 : ℕ) : ℤ) * cellSideLength F := by
    intro i
    have h1 := Finset.mem_Icc.1 (hr i)
    rcases hsg i with h2 | h2 <;> rw [h2] <;> rw [abs_le] <;> push_cast <;> constructor <;> omega
  have e' : cellCentre 0 z + siteOfCoords 0 (fun i => σ i * (x' i - m)) =
      cellCentre 0 y + siteOfCoords 0 (0 : Lattice4) := by
    rw [siteOfCoords_zero, add_zero]
    exact e
  have hoff := cellSideLength_mul_cellDisplacement (y := y) (A := fun i => σ i * (x' i - m)) (h := 0)
    hamb hodd (R := 22) (by norm_num) hAb (zero_mem_centredCube hodd.pow) e' i
  have hss : σ i * σ i = 1 := closedOrthant_mul_self hsg i
  have h2 : cellSideLength F * patchHeight S z y i = x' i - m := by
    unfold patchHeight
    have h3 : cellSideLength F * cellDisplacement z y i = σ i * (x' i - m) := by simpa using hoff
    calc cellSideLength F * (closedOrthant S z i * cellDisplacement z y i)
          = σ i * (cellSideLength F * cellDisplacement z y i) := by
          rw [hσ]
          ring
      _ = σ i * (σ i * (x' i - m)) := by rw [h3]
      _ = (σ i * σ i) * (x' i - m) := by ring
      _ = x' i - m := by rw [hss, one_mul]
  linarith
theorem patchHeight_le (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    (hsg : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1)
    {y : F.Cell} (hy : y ∈ patchCells S z) (i : Fin 4) : patchHeight S z y i ≤ 20 := by
  obtain ⟨x', hx', -, h⟩ := exists_patchDomain_cellCentre hamb hodd hsg hy
  have hr := Finset.mem_Icc.1 (Fintype.mem_piFinset.1 (Finset.mem_filter.1 hx').1 i)
  obtain ⟨hc0, hc1⟩ := cellSideLength_half (F := F) hodd
  by_contra hc
  have h1 : 21 ≤ patchHeight S z y i := by omega
  have h2 : cellSideLength F * 21 ≤ cellSideLength F * patchHeight S z y i :=
    mul_le_mul_of_nonneg_left h1 (by omega)
  have h3 := h i
  omega
theorem neg_le_patchHeight (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    (hsg : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1)
    {y : F.Cell} (hy : y ∈ patchCells S z) (i : Fin 4) : -23 ≤ patchHeight S z y i := by
  classical
  have hyP := (Finset.mem_filter.1 hy).2
  rw [baseSite_eq_cellCentre_zero] at hyP
  have h1 : cellSupDist y z ≤ 23 := cellSupDist_le_of_mem_patchBaseSites hamb hodd hsg hyP
    (zero_mem_centredCube hodd.pow) (by rw [siteOfCoords_zero, add_zero])
  have h2 := abs_cellDisplacement_le (z := z) (y := y) i
  have h3 : |cellDisplacement z y i| ≤ 23 := h2.trans (by exact_mod_cast h1)
  have h4 := abs_le.1 h3
  unfold patchHeight
  rcases hsg i with h5 | h5 <;> rw [h5] <;> omega
theorem step_mem_patchCells (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide) {m : ℕ}
    (hreg : IsOrthantRegular S m) (hm : 32 ≤ m)
    (hsg : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1) {y : F.Cell}
    (hy : y ∈ patchCells S z) (i : Fin 4) (hv : patchHeight S z y i < 20) :
    y + siteOfCoords F.top (Pi.single i (closedOrthant S z i)) ∈ patchCells S z ∧
      ∀ μ, patchHeight S z (y + siteOfCoords F.top (Pi.single i (closedOrthant S z i))) μ =
        patchHeight S z y μ + if μ = i then 1 else 0 := by
  classical
  obtain ⟨x', hx', e, hxv⟩ := exists_patchDomain_cellCentre hamb hodd hsg hy
  obtain ⟨hc0, hc1⟩ := cellSideLength_half (F := F) hodd
  set N := cellSideLength F with hNd
  set mm := (N - 1) / 2 with hmm
  set σ := closedOrthant S z with hσ
  have hss : ∀ μ, σ μ * σ μ = 1 := closedOrthant_mul_self hsg
  set y' := y + siteOfCoords F.top (Pi.single i (σ i)) with hy'
  set x'' : Lattice4 := x' + Pi.single i N with hx''
  have hr := Fintype.mem_piFinset.1 (Finset.mem_filter.1 hx').1
  obtain ⟨a, ha, hax⟩ := (Finset.mem_filter.1 hx').2
  have hxi : x'' ∈ patchDomain S z := by
    refine Finset.mem_filter.2 ⟨Fintype.mem_piFinset.2 fun μ => ?_, a, ha, fun μ => ?_⟩
    · have h1 := Finset.mem_Icc.1 (hr μ)
      rw [Finset.mem_Icc]
      by_cases hμ : μ = i
      · subst hμ
        have h2 := hxv μ
        have h3 : patchHeight S z y μ ≤ 19 := by omega
        have h4 : N * patchHeight S z y μ ≤ N * 19 := mul_le_mul_of_nonneg_left h3 (by omega)
        simp only [hx'', Pi.add_apply, Pi.single_eq_same]
        constructor <;> omega
      · simp only [hx'', Pi.add_apply, Pi.single_eq_of_ne hμ, add_zero]
        exact h1
    · have h1 := hax μ
      by_cases hμ : μ = i
      · subst hμ
        simp only [hx'', Pi.add_apply, Pi.single_eq_same]
        omega
      · simp only [hx'', Pi.add_apply, Pi.single_eq_of_ne hμ, add_zero]
        exact h1
  have hsite : patchSite S z x'' = cellCentre 0 y' := by
    have e1 : cellCentre 0 y' = cellCentre 0 y +
        siteOfCoords 0 (fun μ => (F.blockSide : ℤ) ^ F.top * (Pi.single i (σ i) : Lattice4) μ) := by
      rw [← baseSite_eq_cellCentre_zero, hy', baseSite_add F.top (le_refl _), baseSite_eq_cellCentre_zero]
    rw [e1, ← e]
    unfold patchSite
    rw [add_assoc, ← siteOfCoords_add]
    congr 2
    funext μ
    by_cases hμ : μ = i
    · subst hμ
      have hNc : (F.blockSide : ℤ) ^ F.top = N := rfl
      simp only [hx'', Pi.add_apply, Pi.single_eq_same, hNc]
      have := hss μ
      ring
    · simp only [hx'', Pi.add_apply, Pi.single_eq_of_ne hμ, add_zero, mul_zero]
  have hcell : enclosingCell (patchSite S z x'') = y' := by
    rw [hsite]
    have := enclosingCell_cellCentre_add (j := 0) hodd y' 0 (by simpa using zero_mem_centredCube hodd.pow)
    rwa [siteOfCoords_zero, add_zero] at this
  have hyS : y' ∈ S := by
    have := (enclosingCell_patchSite hamb hodd hreg hm hxi).1
    rwa [hcell] at this
  refine ⟨Finset.mem_filter.2 ⟨hyS, ?_⟩, ?_⟩
  · rw [baseSite_eq_cellCentre_zero, ← hsite]
    exact Finset.mem_image_of_mem _ hxi
  · intro μ
    have hr2 := Fintype.mem_piFinset.1 (Finset.mem_filter.1 hxi).1
    have hAb : ∀ i, |σ i * (x'' i - mm)| ≤ ((22 : ℕ) : ℤ) * N := by
      intro i
      have h1 := Finset.mem_Icc.1 (hr2 i)
      rcases hsg i with h2 | h2 <;> rw [h2] <;> rw [abs_le] <;> push_cast <;> constructor <;> omega
    have e' : cellCentre 0 z + siteOfCoords 0 (fun i => σ i * (x'' i - mm)) =
        cellCentre 0 y' + siteOfCoords 0 (0 : Lattice4) := by
      rw [siteOfCoords_zero, add_zero]
      exact hsite
    have hoff := cellSideLength_mul_cellDisplacement (y := y') (A := fun i => σ i * (x'' i - mm)) (h := 0)
      hamb hodd (R := 22) (by norm_num) hAb (zero_mem_centredCube hodd.pow) e' μ
    have h3 : N * cellDisplacement z y' μ = σ μ * (x'' μ - mm) := by simpa using hoff
    have h2 : N * patchHeight S z y' μ = x'' μ - mm := by
      unfold patchHeight
      calc N * (closedOrthant S z μ * cellDisplacement z y' μ) = σ μ * (N * cellDisplacement z y' μ) := by
            rw [hσ]
            ring
        _ = σ μ * (σ μ * (x'' μ - mm)) := by rw [h3]
        _ = (σ μ * σ μ) * (x'' μ - mm) := by ring
        _ = x'' μ - mm := by rw [hss, one_mul]
    have h4 := hxv μ
    have hN0 : N ≠ 0 := by omega
    refine mul_left_cancel₀ hN0 ?_
    rw [h2, mul_add]
    by_cases hμ : μ = i
    · subst hμ
      simp only [hx'', Pi.add_apply, Pi.single_eq_same, if_true]
      rw [h4]
      ring
    · simp only [hx'', Pi.add_apply, Pi.single_eq_of_ne hμ, add_zero, if_neg hμ]
      rw [h4]
      ring
theorem abs_sub_step_le (hodd : Odd F.blockSide)
    (hsg : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1) (Φ : F.Cell → ℝ) (η : ℝ)
    (hΦ : ∀ c ∈ innerBonds (patchCells S z) F.top, |Φ c.1 - Φ (c.1 + unitStep F.top c.2)| ≤ η)
    {y : F.Cell} (i : Fin 4) (hy : y ∈ patchCells S z)
    (hy' : y + siteOfCoords F.top (Pi.single i (closedOrthant S z i)) ∈ patchCells S z) :
    |Φ y - Φ (y + siteOfCoords F.top (Pi.single i (closedOrthant S z i)))| ≤ η := by
  classical
  rcases hsg i with h | h
  · rw [h] at hy' ⊢
    have hc : ((y, i) : F.Site F.top × Fin 4) ∈ innerBonds (patchCells S z) F.top :=
      Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨mem_sitesOfCells_top.2 hy, Finset.mem_univ _⟩,
        mem_sitesOfCells_top.2 hy'⟩
    exact hΦ _ hc
  · rw [h] at hy' ⊢
    have e1 : y + siteOfCoords F.top (Pi.single i (-1 : ℤ)) + unitStep F.top i = y := by
      rw [unitStep_eq, add_assoc, ← siteOfCoords_add]
      have : (Pi.single i (-1 : ℤ) : Lattice4) + basisVector i = 0 := by
        funext μ
        by_cases hμ : μ = i
        · subst hμ
          simp [basisVector]
        · simp [basisVector, hμ]
      rw [this, siteOfCoords_zero, add_zero]
    have hc : ((y + siteOfCoords F.top (Pi.single i (-1 : ℤ)), i) : F.Site F.top × Fin 4) ∈
        innerBonds (patchCells S z) F.top := by
      refine Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨mem_sitesOfCells_top.2 hy', Finset.mem_univ _⟩, ?_⟩
      show y + siteOfCoords F.top (Pi.single i (-1 : ℤ)) + unitStep F.top i ∈ _
      rw [e1]
      exact mem_sitesOfCells_top.2 hy
    have := hΦ _ hc
    simp only [e1] at this
    rw [abs_sub_comm]
    exact this
def heightDeficit (S : Finset F.Cell) (z y : F.Cell) : ℕ := ∑ i : Fin 4, (20 - patchHeight S z y i).toNat
def farCorner (S : Finset F.Cell) (z : F.Cell) : F.Cell :=
  z + siteOfCoords F.top fun i => 20 * closedOrthant S z i
theorem abs_sub_farCorner_le (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide) {m : ℕ}
    (hreg : IsOrthantRegular S m) (hm : 32 ≤ m)
    (hsg : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1) (Φ : F.Cell → ℝ) (η : ℝ) (hη : 0 ≤ η)
    (hΦ : ∀ c ∈ innerBonds (patchCells S z) F.top, |Φ c.1 - Φ (c.1 + unitStep F.top c.2)| ≤ η) (k : ℕ) :
    ∀ y ∈ patchCells S z, heightDeficit S z y = k → |Φ y - Φ (farCorner S z)| ≤ k * η := by
  induction k with
  | zero =>
    intro y hy h0
    have hall : ∀ i, patchHeight S z y i = 20 := by
      intro i
      have h1 : (20 - patchHeight S z y i).toNat = 0 := by
        have := Finset.single_le_sum (f := fun i => (20 - patchHeight S z y i).toNat)
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
        simp only [heightDeficit] at h0
        omega
      have h2 := patchHeight_le hamb hodd hsg hy i
      omega
    have hy' : y = farCorner S z := by
      unfold farCorner
      conv_lhs => rw [← add_siteOfCoords_cellDisplacement z y]
      congr 2
      funext i
      have h1 := hall i
      unfold patchHeight at h1
      have h2 := closedOrthant_mul_self hsg i
      calc cellDisplacement z y i = (closedOrthant S z i * closedOrthant S z i) * cellDisplacement z y i := by
            rw [h2, one_mul]
        _ = closedOrthant S z i * (closedOrthant S z i * cellDisplacement z y i) := by ring
        _ = 20 * closedOrthant S z i := by rw [h1]; ring
    rw [hy']
    simp
  | succ k ih =>
    intro y hy hk
    have hex : ∃ i, patchHeight S z y i < 20 := by
      by_contra hc
      push_neg at hc
      have : heightDeficit S z y = 0 := by
        unfold heightDeficit
        refine Finset.sum_eq_zero fun i _ => ?_
        have := hc i
        omega
      omega
    obtain ⟨i, hi⟩ := hex
    obtain ⟨hy', hv⟩ := step_mem_patchCells hamb hodd hreg hm hsg hy i hi
    have hk' : heightDeficit S z (y + siteOfCoords F.top (Pi.single i (closedOrthant S z i))) = k := by
      have hsplit : ∀ (g : Fin 4 → ℕ), ∑ μ, g μ = g i + ∑ μ ∈ Finset.univ.erase i, g μ := fun g =>
        (Finset.add_sum_erase _ _ (Finset.mem_univ i)).symm
      unfold heightDeficit at hk ⊢
      rw [hsplit] at hk ⊢
      have h1 : ∑ μ ∈ Finset.univ.erase i,
            (20 - patchHeight S z (y + siteOfCoords F.top (Pi.single i (closedOrthant S z i))) μ).toNat =
          ∑ μ ∈ Finset.univ.erase i, (20 - patchHeight S z y μ).toNat := by
        refine Finset.sum_congr rfl fun μ hμ => ?_
        rw [hv μ, if_neg (Finset.ne_of_mem_erase hμ), add_zero]
      rw [h1, hv i, if_pos rfl]
      omega
    have h1 := ih _ hy' hk'
    have h2 := abs_sub_step_le hodd hsg Φ η hΦ i hy hy'
    have h3 := abs_sub_le (Φ y) (Φ (y + siteOfCoords F.top (Pi.single i (closedOrthant S z i))))
      (Φ (farCorner S z))
    push_cast
    nlinarith
theorem heightDeficit_le (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide)
    (hsg : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1)
    {y : F.Cell} (hy : y ∈ patchCells S z) : heightDeficit S z y ≤ 172 := by
  unfold heightDeficit
  have h : ∀ i ∈ (Finset.univ : Finset (Fin 4)), (20 - patchHeight S z y i).toNat ≤ 43 := by
    intro i _
    have := neg_le_patchHeight hamb hodd hsg hy i
    omega
  calc ∑ i : Fin 4, (20 - patchHeight S z y i).toNat ≤ ∑ _i : Fin 4, 43 := Finset.sum_le_sum h
    _ = 172 := by simp
theorem abs_sub_le_of_mem_patchCells (hamb : IsAdmissibleAmbient F) (hodd : Odd F.blockSide) {m : ℕ}
    (hreg : IsOrthantRegular S m) (hm : 32 ≤ m)
    (hsg : ∀ i, closedOrthant S z i = 1 ∨ closedOrthant S z i = -1) (Φ : F.Cell → ℝ) (η : ℝ) (hη : 0 ≤ η)
    (hΦ : ∀ c ∈ innerBonds (patchCells S z) F.top, |Φ c.1 - Φ (c.1 + unitStep F.top c.2)| ≤ η)
    (hz : z ∈ patchCells S z) {y : F.Cell} (hy : y ∈ patchCells S z) : |Φ y - Φ z| ≤ 344 * η := by
  have h1 := abs_sub_farCorner_le hamb hodd hreg hm hsg Φ η hη hΦ _ y hy rfl
  have h2 := abs_sub_farCorner_le hamb hodd hreg hm hsg Φ η hη hΦ _ z hz rfl
  have h3 : ((heightDeficit S z y : ℕ) : ℝ) ≤ 172 := by exact_mod_cast heightDeficit_le hamb hodd hsg hy
  have h4 : ((heightDeficit S z z : ℕ) : ℝ) ≤ 172 := by exact_mod_cast heightDeficit_le hamb hodd hsg hz
  have h5 := abs_sub_le (Φ y) (Φ (farCorner S z)) (Φ z)
  have h6 : |Φ (farCorner S z) - Φ z| = |Φ z - Φ (farCorner S z)| := abs_sub_comm _ _
  nlinarith
end YangMills.Construction.PatchPaths
end
