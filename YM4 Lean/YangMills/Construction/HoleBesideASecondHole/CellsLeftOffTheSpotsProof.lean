import YangMills.Construction.HoleBesideASecondHole.CellsLeftOffTheSpots
import YangMills.Construction.HoleBesideASecondHole.CoreAndHolesAsSites
import YangMills.Construction.HoleBesideASecondHole.TopHotPlaquettesPayProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.HoleSavings
open BlockAverages LumpContours HoleBounds
variable {F : BlockFrame}
theorem mem_centredCube_odd {r : ℕ} {h : Fin 4 → ℤ} : h ∈ centredCube (2 * r + 1) ↔ ∀ i, |h i| ≤ r := by
  have hw : (((2 * r + 1 : ℕ) : ℤ) - 1) / 2 = r := by
    push_cast
    omega
  simp only [centredCube, Fintype.mem_piFinset, Finset.mem_Icc, hw, abs_le]
theorem card_centredCube_odd (r : ℕ) : (centredCube (2 * r + 1)).card = (2 * r + 1) ^ 4 := by
  have hw : (((2 * r + 1 : ℕ) : ℤ) - 1) / 2 = r := by
    push_cast
    omega
  simp only [centredCube, hw, Fintype.card_piFinset, Int.card_Icc, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  congr 1
  omega
theorem card_thicken_le_mul {j : ℕ} (r : ℕ) (X : Finset (F.Site j)) :
    (thicken r X).card ≤ X.card * (2 * r + 1) ^ 4 := by
  unfold thicken
  refine (Finset.card_biUnion_le_card_mul X _ ((2 * r + 1) ^ 4) fun x _ => ?_)
  refine Finset.card_image_le.trans (card_centredCube_odd r).le
theorem mem_thicken_iff_exists_offset {j : ℕ} {r : ℕ} {X : Finset (F.Site j)} {z : F.Site j} :
    z ∈ thicken r X ↔ ∃ x ∈ X, ∃ h : Fin 4 → ℤ, (∀ i, |h i| ≤ r) ∧ z = x + siteOfCoords j h := by apply _root_.YangMills.Construction.HoleSites.mem_thicken_iff <;> assumption
theorem exists_offset_of_cellSupDist_le {y z : F.Cell} {m : ℕ} (hd : cellSupDist y z ≤ m) :
    ∃ h : Fin 4 → ℤ, (∀ i, |h i| ≤ m) ∧ y = z + siteOfCoords F.top h := by
  refine ⟨fun i => ((y i - z i).valMinAbs), fun i => ?_, ?_⟩
  · have h1 : ((y i - z i).valMinAbs).natAbs ≤ cellSupDist y z :=
      Finset.le_sup (f := fun i => ((y i - z i).valMinAbs).natAbs) (Finset.mem_univ i)
    have h2 : ((y i - z i).valMinAbs).natAbs ≤ m := h1.trans hd
    show |(y i - z i).valMinAbs| ≤ (m : ℤ)
    rw [Int.abs_eq_natAbs]
    exact_mod_cast h2
  · funext i
    simp [siteOfCoords, ZMod.coe_valMinAbs]
def IsLumpCover (assign : F.Cell → Finset F.Cell) : Prop :=
  ∀ x, x ∈ assign x ∧ ∀ v ∈ assign x, ∃ δ : Fin 4 → ℤ, v = x + siteOfCoords F.top δ ∧ ∀ i, |δ i| < 2 ^ 15
theorem boxSites_cover (x : F.Cell) (lo hi : Fin 4 → ℤ) (h1 : ∀ i, lo i ≤ siteCoords x i)
    (h2 : ∀ i, siteCoords x i ≤ hi i) (h3 : ∀ i, hi i - lo i + 1 < 2 ^ 15) :
    x ∈ boxSites F.top lo hi ∧ ∀ v ∈ boxSites F.top lo hi, ∃ δ : Fin 4 → ℤ, v = x + siteOfCoords F.top δ ∧
      ∀ i, |δ i| < 2 ^ 15 := by
  refine ⟨?_, ?_⟩
  · simp only [boxSites, Finset.mem_image, Fintype.mem_piFinset, Finset.mem_Icc]
    exact ⟨siteCoords x, fun i => ⟨h1 i, h2 i⟩, siteOfCoords_siteCoords x⟩
  · intro v hv
    simp only [boxSites, Finset.mem_image, Fintype.mem_piFinset, Finset.mem_Icc] at hv
    obtain ⟨w, hw, rfl⟩ := hv
    refine ⟨w - siteCoords x, ?_, fun i => ?_⟩
    · rw [siteOfCoords_sub, siteOfCoords_siteCoords]
      abel
    · have := hw i
      have a1 := h1 i
      have a2 := h2 i
      have a3 := h3 i
      simp only [Pi.sub_apply]
      rw [abs_lt]
      constructor <;> omega
theorem abs_offsetFromCentre_le {L : ℕ} (hL : Odd L) (c : ℤ) : |offsetFromCentre L c| ≤ ((L : ℤ) - 1) / 2 := by apply _root_.YangMills.Construction.HoleSavings.TopHotPlaquetteCost.abs_offsetFromCentre_le <;> assumption
theorem lumpOf_isLumpCover {L : ℕ} (hL : Odd L) (g : LumpGrid L) : IsLumpCover (F := F) (lumpOf g) := by
  intro x
  have hb := fun i => g.mem_interval _ (abs_offsetFromCentre_le hL (siteCoords x i))
  have hs := fun i => g.interval_length _ (abs_offsetFromCentre_le hL (siteCoords x i))
  refine boxSites_cover x _ _ (fun i => ?_) (fun i => ?_) (fun i => ?_)
  · have := (hb i).2.1
    linarith
  · have := (hb i).2.2.1
    linarith
  · have := (hs i).2
    linarith
theorem gridBox_isLumpCover (G : (i : Fin 4) → PeriodicLineGrid (F.extent i)) :
    IsLumpCover (F := F) fun x => gridBox G (siteCoords x) := by
  intro x
  refine boxSites_cover x _ _ (fun i => (G i).left_le _) (fun i => (G i).le_right _)
    (fun i => ((G i).interval_length _).2)
theorem sub_emod_add_emod {p : ℤ} (c r : ℤ) (h0 : 0 ≤ r) (h1 : r < p) : (c - c % p + r) % p = r := by
  have e : c - c % p = p * (c / p) := by
    have := Int.emod_add_mul_ediv c p
    linarith
  rw [e, add_comm, Int.add_mul_emod_self_left, Int.emod_eq_of_lt h0 h1]
def blockLeftEnd (p r : ℤ) : ℤ := min (r / 16384) (p / 16384 - 1) * 16384
def blockRightEnd (p r : ℤ) : ℤ := if r / 16384 < p / 16384 - 1 then (r / 16384 + 1) * 16384 - 1 else p - 1
theorem blockEnds_bounds {p r : ℤ} (hp : 16384 ≤ p) (h0 : 0 ≤ r) (h1 : r < p) :
    0 ≤ blockLeftEnd p r ∧ blockLeftEnd p r ≤ r ∧ r ≤ blockRightEnd p r ∧ blockRightEnd p r < p ∧
      16384 ≤ blockRightEnd p r - blockLeftEnd p r + 1 ∧ blockRightEnd p r - blockLeftEnd p r + 1 < 32768 := by
  unfold blockLeftEnd blockRightEnd
  split_ifs <;> omega
theorem blockEnds_eq_of_mem {p r r' : ℤ} (h2 : blockLeftEnd p r ≤ r')
    (h3 : r' ≤ blockRightEnd p r) : blockLeftEnd p r' = blockLeftEnd p r ∧ blockRightEnd p r' = blockRightEnd p r := by
  unfold blockLeftEnd blockRightEnd at *
  split_ifs at * <;> omega
def blockLineGrid (p : ℕ) (hp : 2 ^ 14 ≤ p) : PeriodicLineGrid p where
  left := fun c => c - c % p + blockLeftEnd p (c % p)
  right := fun c => c - c % p + blockRightEnd p (c % p)
  left_le := fun c => by
    have hp' : (16384 : ℤ) ≤ p := by exact_mod_cast hp
    have h := blockEnds_bounds hp' (Int.emod_nonneg c (by omega)) (Int.emod_lt_of_pos c (by omega))
    have := h.2.1
    omega
  le_right := fun c => by
    have hp' : (16384 : ℤ) ≤ p := by exact_mod_cast hp
    have h := blockEnds_bounds hp' (Int.emod_nonneg c (by omega)) (Int.emod_lt_of_pos c (by omega))
    have := h.2.2.1
    omega
  interval_eq := fun c c' h1 h2 => by
    have hp' : (16384 : ℤ) ≤ p := by exact_mod_cast hp
    have hr0 := Int.emod_nonneg c (show (p : ℤ) ≠ 0 by omega)
    have hr1 := Int.emod_lt_of_pos c (show (0 : ℤ) < p by omega)
    have h := blockEnds_bounds hp' hr0 hr1
    obtain ⟨f1, f2, f3, f4, -, -⟩ := h
    set r' := c' - (c - c % p) with hr'
    have e0 : 0 ≤ r' := by omega
    have e1 : r' < p := by omega
    have e2 : c' = c - c % p + r' := by omega
    have e3 : c' % p = r' := by
      rw [e2]
      exact sub_emod_add_emod c r' e0 e1
    have e4 : c' - c' % p = c - c % p := by omega
    have hs := blockEnds_eq_of_mem (show blockLeftEnd p (c % p) ≤ r' by omega)
      (show r' ≤ blockRightEnd p (c % p) by omega)
    rw [e4, e3, hs.1, hs.2]
    exact ⟨rfl, rfl⟩
  interval_length := fun c => by
    have hp' : (16384 : ℤ) ≤ p := by exact_mod_cast hp
    have h := blockEnds_bounds hp' (Int.emod_nonneg c (by omega)) (Int.emod_lt_of_pos c (by omega))
    obtain ⟨-, -, -, -, h5, h6⟩ := h
    constructor <;> norm_num <;> omega
  periodic := fun c => by
    have e : (c + p) % (p : ℤ) = c % p := Int.add_emod_right c p
    rw [e]
    constructor <;> ring
section WithHoleData
variable {L : ℕ} {g : LumpGrid L} {a s θ : ℝ} {J₀ : ℕ} (D : HoleData F g a s θ J₀) (C : ℝ)
theorem le_cellSupDist_of_mem_keptOffBadLumps {assign : F.Cell → Finset F.Cell} (hl : IsLumpCover assign)
    {y z : F.Cell} (hy : y ∈ D.keptOffBadLumps C assign) (hz : z ∈ D.badCells C) : 11 ≤ cellSupDist y z := by
  by_contra hcon
  have hd : cellSupDist y z ≤ 10 := by omega
  obtain ⟨h, hh, e⟩ := exists_offset_of_cellSupDist_le hd
  have hy' := Finset.mem_sdiff.1 hy
  apply hy'.2
  have hye : y ∈ thicken 10 (D.badCells C) := mem_thicken_iff_exists_offset.2 ⟨z, hz, h, by simpa using hh, e⟩
  simp only [lumpsNeighbourhood, Finset.mem_biUnion]
  refine ⟨assign y, Finset.mem_image_of_mem _ hye, ?_⟩
  exact mem_thicken_iff_exists_offset.2 ⟨y, (hl y).1, 0, by simp, by simp [siteOfCoords_zero]⟩
theorem card_thickening_le {assign : F.Cell → Finset F.Cell} (hl : IsLumpCover assign) (m : ℕ) :
    (thickening D.keptCells (D.keptCells \ D.keptOffBadLumps C assign) m).card ≤
      (2 ^ 17 + 2 * m) ^ 4 * (D.badCells C).card := by
  have hsub : thickening D.keptCells (D.keptCells \ D.keptOffBadLumps C assign) m ⊆
      thicken (m + 36874) (D.badCells C) := by
    intro z hz
    unfold thickening at hz
    obtain ⟨-, d, hd, hzd⟩ := Finset.mem_filter.1 hz
    obtain ⟨e, he, ez⟩ := exists_offset_of_cellSupDist_le hzd
    have hdN : d ∈ lumpsNeighbourhood (D.lumpsAtBadCells C assign) := by
      by_contra hno
      have hd' := Finset.mem_sdiff.1 hd
      exact hd'.2 (Finset.mem_sdiff.2 ⟨hd'.1, hno⟩)
    simp only [lumpsNeighbourhood, Finset.mem_biUnion] at hdN
    obtain ⟨l, hl1, hl2⟩ := hdN
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 hl1
    obtain ⟨y0, hy0, h0, hh0, eu⟩ := mem_thicken_iff_exists_offset.1 hu
    obtain ⟨v, hv, h1, hh1, ed⟩ := mem_thicken_iff_exists_offset.1 hl2
    obtain ⟨δ, ev, hδ⟩ := (hl u).2 v hv
    refine mem_thicken_iff_exists_offset.2 ⟨y0, hy0, h0 + δ + h1 + e, fun i => ?_, ?_⟩
    · have a0 := abs_le.1 (hh0 i)
      have a1 := abs_lt.1 (hδ i)
      have a2 := abs_le.1 (hh1 i)
      have a3 := abs_le.1 (he i)
      have hw : ((lumpRange : ℕ) : ℤ) = 4096 := by norm_num [lumpRange]
      rw [hw] at a2
      simp only [Pi.add_apply]
      rw [abs_le]
      push_cast at a0 a1 ⊢
      constructor <;> omega
    · rw [ez, ed, ev, eu, siteOfCoords_add, siteOfCoords_add, siteOfCoords_add]
      abel
  calc _ ≤ (thicken (m + 36874) (D.badCells C)).card := Finset.card_le_card hsub
    _ ≤ (D.badCells C).card * (2 * (m + 36874) + 1) ^ 4 := card_thicken_le_mul _ _
    _ ≤ (D.badCells C).card * (2 ^ 17 + 2 * m) ^ 4 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 4)
    _ = _ := Nat.mul_comm _ _
theorem card_badCells_le : (D.badCells C).card ≤ (D.excitedCells C).card + (D.crowdedCells).card :=
  Finset.card_union_le _ _
theorem isOrthantRegular_mono {S : Finset F.Cell} {m m' : ℕ} (h : m' ≤ m) (hr : IsOrthantRegular S m) :
    IsOrthantRegular S m' := by
  intro z
  obtain ⟨e, he, hk⟩ := hr z
  exact ⟨e, he, fun q hq hd k hs hb => hk q hq (hd.trans h) k hs fun i => (hb i).trans (by exact_mod_cast h)⟩
theorem mem_innerPlaquettes_top_iff {S : Finset F.Cell} {p : F.Cell × Fin 4 × Fin 4} :
    p ∈ innerPlaquettes S F.top ↔ p ∈ cutPlaquettes S := by
  have e : ∀ X : Finset F.Cell, X ⊆ sitesOfCells S F.top ↔ X ⊆ S := fun X =>
    ⟨fun h x hx => mem_sitesOfCells_top.1 (h hx), fun h x hx => mem_sitesOfCells_top.2 (h hx)⟩
  simp only [innerPlaquettes, cutPlaquettes, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true,
    mem_sitesOfCells_top, e]
theorem isLump_of_mem_hotTopLumps : ∀ l ∈ D.hotTopLumps, IsLump g l := by
  intro l hl
  simp only [HoleData.hotTopLumps, hotLumps, Finset.mem_biUnion, Finset.mem_image] at hl
  obtain ⟨p, -, x, -, rfl⟩ := hl
  exact ⟨x, rfl⟩
theorem keptCells_isCold (hL : Odd L) : IsCold D.keptCells F.top θ D.topField := by
  intro p hp
  by_contra hcon
  have hp' := mem_innerPlaquettes_top_iff.1 hp
  simp only [cutPlaquettes, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true] at hp'
  have hsub : D.keptCells ⊆ D.cells := Finset.sdiff_subset
  have hx : p.1 ∈ plaquetteCorners p := by simp [plaquetteCorners]
  have hin : lumpOf g p.1 ∈ D.hotTopLumps := by
    simp only [HoleData.hotTopLumps, hotLumps, Finset.mem_biUnion, Finset.mem_image, Finset.mem_filter]
    refine ⟨p, ⟨?_, not_lt.1 hcon⟩, p.1, hx, rfl⟩
    simp only [cutPlaquettes, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true]
    exact ⟨hsub hp'.1, hp'.2.1, hp'.2.2.trans hsub⟩
  have hk := Finset.mem_sdiff.1 hp'.1
  apply hk.2
  simp only [lumpsNeighbourhood, Finset.mem_biUnion]
  refine ⟨_, hin, ?_⟩
  exact mem_thicken_iff_exists_offset.2 ⟨p.1, ((lumpOf_isLumpCover hL g) p.1).1, 0, by simp, by simp [siteOfCoords_zero]⟩
theorem hotTopLumps_eq_empty (hc : IsCold D.cells F.top θ D.topField) : D.hotTopLumps = ∅ := by
  have e : (cutPlaquettes D.cells).filter (fun p => θ ≤ plaquetteDefect D.topField p) = ∅ := by
    apply Finset.filter_eq_empty_iff.2
    intro p hp
    exact not_le.2 (hc p (mem_innerPlaquettes_top_iff.2 hp))
  simp only [HoleData.hotTopLumps, hotLumps, e, Finset.biUnion_empty]
end WithHoleData
theorem mem_torusCells (hs : ∀ i, 0 < F.extent i) (x : F.Cell) : x ∈ torusCells F := by apply _root_.YangMills.Construction.HoleSavings.TopHotPlaquetteCost.mem_torusCells <;> assumption
theorem card_torusCells_le (F : BlockFrame) (m : ℕ) (hm : ∀ i, F.extent i ≤ m) : (torusCells F).card ≤ m ^ 4 := by
  unfold torusCells boxSites
  refine Finset.card_image_le.trans ?_
  simp only [Fintype.card_piFinset, Int.card_Icc, Pi.zero_apply]
  calc ∏ i : Fin 4, ((F.extent i : ℤ) - 1 + 1 - 0).toNat ≤ ∏ _i : Fin 4, m :=
        Finset.prod_le_prod' fun i _ => by have := hm i; omega
    _ = m ^ 4 := by simp
theorem torusCells_isOrthantRegular (hs : ∀ i, 0 < F.extent i) : IsOrthantRegular (torusCells F) 1024 := by
  intro z
  exact ⟨fun _ => 1, fun _ => Or.inl rfl, fun q _ _ h _ _ => mem_torusCells hs _⟩
theorem keptOffBadLumpsStatement_holds (h0 : ComplementOfThickenedLumpsRegular) : keptOffBadLumpsStatement := by
  intro F L g a s θ C J₀ D hFL hL hc hth
  have hs : ∀ i, 0 < F.extent i := fun i => by
    have h1 := hc.1 i
    have h2 := hc.2
    omega
  have hcold := keptCells_isCold D hL
  have hoff : L ∣ F.extent 0 → ∃ H : Finset (Finset F.Cell), (∀ l ∈ H, IsLump g l) ∧ D.cells = cellsOffLumps F H := by
    intro hdv
    rcases hth with ⟨H, hH, -, hS⟩ | ⟨hS, -⟩
    · exact ⟨H, hH, hS⟩
    · exact ⟨∅, by simp, by simp [cellsOffLumps, lumpsNeighbourhood, hS]⟩
  have hall : L ∣ F.extent 0 → ∀ i, L ∣ F.extent i := fun hdv i => by rw [hc.1 i]; exact hdv
  have hkept : ∀ H : Finset (Finset F.Cell), D.cells = cellsOffLumps F H →
      D.keptCells = cellsOffLumps F (H ∪ D.hotTopLumps) := by
    intro H hS
    ext x
    simp only [HoleData.keptCells, hS, cellsOffLumps, lumpsNeighbourhood, Finset.union_biUnion, Finset.mem_sdiff,
      Finset.mem_union]
    tauto
  have hkr : IsOrthantRegular D.keptCells 1024 := by
    rcases hth with ⟨H, hH, hdv, hS⟩ | ⟨hS, hcd⟩
    · rw [hkept H hS]
      refine isOrthantRegular_mono (by norm_num) (h0.2 L g F _ hL hs (hall hdv) fun l hl => ?_)
      rcases Finset.mem_union.1 hl with h | h
      · exact hH l h
      · exact isLump_of_mem_hotTopLumps D l h
    · have e : D.keptCells = torusCells F := by
        simp [HoleData.keptCells, hotTopLumps_eq_empty D hcd, lumpsNeighbourhood, hS]
      rw [e]
      exact torusCells_isOrthantRegular hs
  refine ⟨?_, hkr, hcold, fun S₁ hS₁ => ?_⟩
  · rcases hth with ⟨H, hH, hdv, hS⟩ | ⟨hS, hcd⟩
    · exact ⟨_, Or.inl ⟨hdv, rfl⟩⟩
    · by_cases hbig : 2 ^ 18 ≤ F.extent 0
      · refine ⟨_, Or.inr ⟨hS, hcd, Or.inl ⟨hbig, fun i => blockLineGrid (F.extent i) ?_, rfl⟩⟩⟩
        rw [hc.1 i]
        omega
      · exact ⟨_, Or.inr ⟨hS, hcd, Or.inr ⟨by omega, rfl⟩⟩⟩
  have hgen : ∀ assign : F.Cell → Finset F.Cell, IsLumpCover assign →
      D.keptOffBadLumps C assign ⊆ D.keptCells ∧ D.keptOffBadLumps C assign ⊆ D.coreCells C 11 ∧
      ∀ m : ℕ, (thickening D.keptCells (D.keptCells \ D.keptOffBadLumps C assign) m).card ≤
        max ((2 ^ 17 + 2 * m) ^ 4) (2 ^ 72) * ((D.excitedCells C).card + (D.crowdedCells).card) := by
    intro assign hl
    refine ⟨Finset.sdiff_subset, fun y hy => ?_, fun m => ?_⟩
    · have hyS : y ∈ D.cells := Finset.sdiff_subset (Finset.sdiff_subset hy)
      exact Finset.mem_filter.2 ⟨hyS, fun z hz => le_cellSupDist_of_mem_keptOffBadLumps D C hl hy hz⟩
    · calc _ ≤ (2 ^ 17 + 2 * m) ^ 4 * (D.badCells C).card := card_thickening_le D C hl m
        _ ≤ max ((2 ^ 17 + 2 * m) ^ 4) (2 ^ 72) * ((D.excitedCells C).card + (D.crowdedCells).card) :=
          Nat.mul_le_mul (le_max_left _ _) (card_badCells_le D C)
  rcases hS₁ with ⟨hdv, rfl⟩ | ⟨hS, hcd, ⟨hbig, G, rfl⟩ | ⟨hsmall, rfl⟩⟩
  · obtain ⟨g1, g2, g3⟩ := hgen _ (lumpOf_isLumpCover hL g)
    refine ⟨g1, g2, ?_, g3⟩
    obtain ⟨H, hH, hS⟩ := hoff hdv
    have e : D.keptOffBadLumps C (lumpOf g) =
        cellsOffLumps F ((H ∪ D.hotTopLumps) ∪ D.lumpsAtBadCells C (lumpOf g)) := by
      have := hkept H hS
      ext x
      simp only [HoleData.keptOffBadLumps, this, cellsOffLumps, lumpsNeighbourhood, Finset.union_biUnion,
        Finset.mem_sdiff, Finset.mem_union]
      tauto
    rw [e]
    refine isOrthantRegular_mono (by norm_num) (h0.2 L g F _ hL hs (hall hdv) fun l hl => ?_)
    rcases Finset.mem_union.1 hl with h | h
    · rcases Finset.mem_union.1 h with h | h
      · exact hH l h
      · exact isLump_of_mem_hotTopLumps D l h
    · obtain ⟨u, -, rfl⟩ := Finset.mem_image.1 h
      exact ⟨u, rfl⟩
  · obtain ⟨g1, g2, g3⟩ := hgen _ (gridBox_isLumpCover G)
    refine ⟨g1, g2, ?_, g3⟩
    have e : D.keptOffBadLumps C (fun x => gridBox G (siteCoords x)) =
        cellsOffLumps F (D.lumpsAtBadCells C fun x => gridBox G (siteCoords x)) := by
      simp [HoleData.keptOffBadLumps, HoleData.keptCells, hotTopLumps_eq_empty D hcd, lumpsNeighbourhood, hS,
        cellsOffLumps]
    rw [e]
    refine isOrthantRegular_mono (by norm_num) (h0.1 F G _ hs fun l hl => ?_)
    obtain ⟨u, -, rfl⟩ := Finset.mem_image.1 hl
    exact ⟨siteCoords u, rfl⟩
  · by_cases hne : (D.badCells C).Nonempty
    · rw [if_pos hne]
      refine ⟨Finset.empty_subset _, Finset.empty_subset _, ?_, fun m => ?_⟩
      · intro z
        exact ⟨fun _ => 1, fun _ => Or.inl rfl, fun q hq => absurd hq (Finset.notMem_empty q)⟩
      · have h1 : (thickening D.keptCells (D.keptCells \ ∅) m).card ≤ 2 ^ 72 := by
          calc _ ≤ (torusCells F).card := Finset.card_le_card fun z _ => mem_torusCells hs z
            _ ≤ (2 ^ 18) ^ 4 := card_torusCells_le F _ fun i => by rw [hc.1 i]; omega
            _ = 2 ^ 72 := by norm_num
        have h2 : 1 ≤ (D.excitedCells C).card + (D.crowdedCells).card :=
          Nat.le_trans (Finset.card_pos.2 hne) (card_badCells_le D C)
        calc _ ≤ 2 ^ 72 * 1 := by simpa using h1
          _ ≤ _ := Nat.mul_le_mul (le_max_right _ _) h2
    · rw [if_neg hne]
      rw [Finset.not_nonempty_iff_eq_empty] at hne
      refine ⟨subset_rfl, fun y hy => ?_, hkr, fun m => ?_⟩
      · refine Finset.mem_filter.2 ⟨Finset.sdiff_subset hy, fun z hz => ?_⟩
        rw [hne] at hz
        exact absurd hz (Finset.notMem_empty z)
      · have : thickening D.keptCells (D.keptCells \ D.keptCells) m = ∅ := by
          unfold thickening
          simp
        rw [this]
        simp
end YangMills.Construction.HoleSavings
end
