import YangMills.Construction.HoleBesideASecondHole.BoxesAtACellClose
import YangMills.Construction.HoleBesideASecondHole.BoxesOfNeighboursAgree
import YangMills.Construction.HoleBesideASecondHole.SitesOfBlocksAndCells
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.LumpContours
open BlockAverages BlockSites CornerBoxes
namespace NeighbourBoxes
attribute [local irreducible] cellBall
variable {F : BlockFrame}
theorem exists_offset_of_mem_boxSites {lo hi : Fin 4 → ℤ} {m : ℤ} (hwidth : ∀ i, hi i - lo i + 1 ≤ m)
    {x z : F.Site F.depth} (hx : x ∈ boxSites F.depth lo hi) (hz : z ∈ boxSites F.depth lo hi) :
    ∃ d : Fin 4 → ℤ, (∀ i, |d i| ≤ m) ∧ x = z + siteOfCoords F.depth d := by
  obtain ⟨a, ha, rfl⟩ := (mem_boxOfCorners (q := (lo, hi))).mp hx
  obtain ⟨b, hb, rfl⟩ := (mem_boxOfCorners (q := (lo, hi))).mp hz
  refine ⟨a - b, fun i => ?_, ?_⟩
  · have h1 := ha i
    have h2 := hb i
    have h3 := hwidth i
    simp only at h1 h2
    simp only [Pi.sub_apply]
    rw [abs_le]
    constructor <;> omega
  · rw [← _root_.YangMills.Construction.BlockSites.siteOfCoords_add]
    congr 1
    abel
theorem mem_cellBall_two_of_mem_cellBall_one [∀ i, NeZero (F.period F.top i)] {u w v : F.Cell}
    (hv : v ∈ cellBall u 1) (hu : cellSupDist w u ≤ 1) :
    v ∈ cellBall w 2 := by
  obtain ⟨c, hc, rfl⟩ := mem_cellBall_iff.mp hv
  obtain ⟨c', hc', rfl⟩ := exists_offset_of_supDist_le hu
  refine mem_cellBall_iff.mpr ⟨c' + c, fun i => ?_, ?_⟩
  · have h1 := hc i
    have h2 := hc' i
    rw [abs_le] at h1 h2 ⊢
    simp only [Pi.add_apply]
    push_cast at h1 h2 ⊢
    constructor <;> linarith
  · rw [_root_.YangMills.Construction.BlockSites.siteOfCoords_add, add_assoc]
theorem mem_cutBelow_cellBall_of_mem_box (hodd : Odd F.blockSide) {m r : ℕ} (hm : m ≤ F.blockSide * r)
    {Z : Finset (F.Site F.depth)}
    (hbox : ∃ lo hi : Fin 4 → ℤ, Z = boxSites F.depth lo hi ∧ ∀ i, lo i ≤ hi i ∧ hi i - lo i + 1 ≤ m)
    {u : F.Cell} {z₀ x : F.Site F.depth} (hz₀ : z₀ ∈ Z) (hu : z₀ ∈ sitesBelow F.depth u) (hx : x ∈ Z) :
    x ∈ cutBelow F.depth (cellBall u r) := by
  obtain ⟨lo, hi, rfl, hwidth⟩ := hbox
  obtain ⟨d, hd, rfl⟩ := exists_offset_of_mem_boxSites (m := (m : ℤ)) (fun i => (hwidth i).2) hx hz₀
  refine add_mem_cutBelow_cellBall hodd hu d r fun i => ?_
  have h1 := hd i
  linarith
theorem mem_cutBelow_cellBall_of_near_boxes [∀ i, NeZero (F.period F.depth i)] (hodd : Odd F.blockSide)
    {m r : ℕ} (hm : 2 * m + 2 ≤ F.blockSide * r) {Z Z' : Finset (F.Site F.depth)}
    (hbox : ∃ lo hi : Fin 4 → ℤ, Z = boxSites F.depth lo hi ∧ ∀ i, lo i ≤ hi i ∧ hi i - lo i + 1 ≤ m)
    (hbox' : ∃ lo hi : Fin 4 → ℤ, Z' = boxSites F.depth lo hi ∧ ∀ i, lo i ≤ hi i ∧ hi i - lo i + 1 ≤ m)
    {y : F.Cell} {z₀ z' x x' : F.Site F.depth} (hz₀ : z₀ ∈ Z) (hy : z₀ ∈ sitesBelow F.depth y)
    (hz' : z' ∈ Z') (hx : x ∈ Z) (hx' : x' ∈ Z') (hd : supDist x x' ≤ 2) :
    z' ∈ cutBelow F.depth (cellBall y r) := by
  obtain ⟨lo, hi, rfl, hw₁⟩ := hbox
  obtain ⟨lo', hi', rfl, hw₂⟩ := hbox'
  obtain ⟨d₁, hd₁, e₁⟩ := exists_offset_of_mem_boxSites (m := (m : ℤ)) (fun i => (hw₁ i).2) hx hz₀
  obtain ⟨d₃, hd₃, e₃⟩ := exists_offset_of_mem_boxSites (m := (m : ℤ)) (fun i => (hw₂ i).2) hz' hx'
  obtain ⟨d₂, hd₂, e₂⟩ := exists_offset_of_supDist_le hd
  have ez : z' = z₀ + siteOfCoords F.depth (d₁ + d₂ + d₃) := by
    rw [e₃, e₂, e₁, _root_.YangMills.Construction.BlockSites.siteOfCoords_add, _root_.YangMills.Construction.BlockSites.siteOfCoords_add]
    abel
  rw [ez]
  refine add_mem_cutBelow_cellBall hodd hy _ r fun i => ?_
  have h1 := hd₁ i
  have h2 := hd₂ i
  have h3 := hd₃ i
  rw [abs_le] at h1 h2 h3 ⊢
  simp only [Pi.add_apply]
  push_cast at h2 ⊢
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]
theorem excludedBoxes_agree_and_separated [∀ i, NeZero (F.period F.depth i)]
    [∀ i, NeZero (F.period F.top i)] {J₀ m : ℕ} {h : Finset (Finset (F.Site F.depth))}
    (hodd : Odd F.blockSide) (hextent : ∀ i, 4 ≤ F.extent i) (hsmall : 4 * m < F.blockSide)
    (hpos : ∀ y, ¬ IsCrowded J₀ h y → 1 ≤ m)
    (hleast : ∀ y, ¬ IsCrowded J₀ h y → IsLeastSeparatedCover (lumpSeeds h y) (excludedBoxes J₀ h y))
    (hboxes : ∀ y, ¬ IsCrowded J₀ h y → ∀ Z ∈ excludedBoxes J₀ h y, ∃ lo hi : Fin 4 → ℤ,
      Z = boxSites F.depth lo hi ∧ ∀ i, lo i ≤ hi i ∧ hi i - lo i + 1 ≤ (m : ℤ))
    (hinside : ∀ y, ¬ IsCrowded J₀ h y → ∀ Z ∈ excludedBoxes J₀ h y, ∀ Z',
      IsSeparatedCover ((lumpSeeds h y).filter fun l => l ⊆ Z) Z' → ∃ B ∈ Z', Z ⊆ B) :
    (∀ y y', ¬ IsCrowded J₀ h y → ¬ IsCrowded J₀ h y' → cellSupDist y y' ≤ 1 →
      ∀ Z ∈ excludedBoxes J₀ h y,
      ((Z ∩ sitesBelow F.depth y).Nonempty ∨ (Z ∩ sitesBelow F.depth y').Nonempty) →
        Z ∈ excludedBoxes J₀ h y') ∧
    ∀ y y', ¬ IsCrowded J₀ h y → ¬ IsCrowded J₀ h y' → ∀ Z ∈ excludedBoxes J₀ h y,
      ∀ Z' ∈ excludedBoxes J₀ h y',
      (Z ∩ sitesBelow F.depth y).Nonempty → (Z' ∩ sitesBelow F.depth y').Nonempty → Z ≠ Z' →
        ¬ AreWithin 2 Z Z' := by
  classical
  have hs : ∀ i, 0 < F.extent i := fun i => by have := hextent i; omega
  have near : ∀ y, ¬ IsCrowded J₀ h y → ∀ Z ∈ excludedBoxes J₀ h y, ∀ (u : F.Cell) (z₀ : F.Site F.depth),
      z₀ ∈ Z → z₀ ∈ sitesBelow F.depth u → ∀ x ∈ Z, x ∈ cutBelow F.depth (cellBall u 1) := by
    intro y hc Z hZ u z₀ hz₀ hu x hx
    exact mem_cutBelow_cellBall_of_mem_box hodd (by omega : m ≤ F.blockSide * 1) (hboxes y hc Z hZ) hz₀ hu hx
  have inNbr : ∀ y y', ¬ IsCrowded J₀ h y → ¬ IsCrowded J₀ h y' → cellSupDist y y' ≤ 1 →
      ∀ Z ∈ excludedBoxes J₀ h y,
      ((Z ∩ sitesBelow F.depth y).Nonempty ∨ (Z ∩ sitesBelow F.depth y').Nonempty) →
        ∃ B ∈ excludedBoxes J₀ h y', Z ⊆ B := by
    intro y y' hc hc' hd Z hZ hm
    have cc := hleast y' hc'
    refine hinside y hc Z hZ _ ⟨cc.1.1, fun s hs' => cc.1.2.1 s ?_, cc.1.2.2⟩
    obtain ⟨hs₁, hs₂⟩ := Finset.mem_filter.mp hs'
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hs₁
    refine Finset.mem_image_of_mem lumpCollar (Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hl).1, ?_⟩)
    intro x hx
    have hxZ : x ∈ Z := hs₂ (subset_thicken _ _ hx)
    have hself : cellSupDist y' y' ≤ 1 := by simp [cellSupDist]
    have hyy : cellSupDist y' y ≤ 1 := by
      have e : cellSupDist y' y = cellSupDist y y' := supDist_comm y' y
      omega
    rcases hm with ⟨z₀, hz₀⟩ | ⟨z₀, hz₀⟩
    · obtain ⟨m₁, m₂⟩ := Finset.mem_inter.mp hz₀
      obtain ⟨v, hv, hxv⟩ := Finset.mem_biUnion.mp (near y hc Z hZ y z₀ m₁ m₂ x hxZ)
      exact Finset.mem_biUnion.mpr ⟨v, mem_cellBall_two_of_mem_cellBall_one hv hyy, hxv⟩
    · obtain ⟨m₁, m₂⟩ := Finset.mem_inter.mp hz₀
      obtain ⟨v, hv, hxv⟩ := Finset.mem_biUnion.mp (near y hc Z hZ y' z₀ m₁ m₂ x hxZ)
      exact Finset.mem_biUnion.mpr ⟨v, mem_cellBall_two_of_mem_cellBall_one hv hself, hxv⟩
  have first : ∀ y y', ¬ IsCrowded J₀ h y → ¬ IsCrowded J₀ h y' → cellSupDist y y' ≤ 1 →
      ∀ Z ∈ excludedBoxes J₀ h y,
      ((Z ∩ sitesBelow F.depth y).Nonempty ∨ (Z ∩ sitesBelow F.depth y').Nonempty) →
        Z ∈ excludedBoxes J₀ h y' := by
    intro y y' hc hc' hd Z hZ hm
    obtain ⟨B, hB, hZB⟩ := inNbr y y' hc hc' hd Z hZ hm
    have hm' : (B ∩ sitesBelow F.depth y').Nonempty ∨ (B ∩ sitesBelow F.depth y).Nonempty := by
      rcases hm with ⟨z, hz⟩ | ⟨z, hz⟩
      · exact Or.inr ⟨z, Finset.mem_inter.mpr ⟨hZB (Finset.mem_inter.mp hz).1, (Finset.mem_inter.mp hz).2⟩⟩
      · exact Or.inl ⟨z, Finset.mem_inter.mpr ⟨hZB (Finset.mem_inter.mp hz).1, (Finset.mem_inter.mp hz).2⟩⟩
    obtain ⟨Z₂, hZ₂, hBZ⟩ := inNbr y' y hc' hc (by
      have e : cellSupDist y' y = cellSupDist y y' := supDist_comm y' y
      omega) B hB hm'
    have cc := hleast y hc
    have hne : Z.Nonempty := by
      rcases hm with ⟨z, hz⟩ | ⟨z, hz⟩ <;> exact ⟨z, (Finset.mem_inter.mp hz).1⟩
    have hZZ : Z = Z₂ := by
      by_contra hn
      obtain ⟨z, hz⟩ := hne
      refine cc.1.2.2 Z hZ Z₂ hZ₂ hn ⟨z, hz, z, hBZ (hZB hz), ?_⟩
      simp [supDist]
    have : Z = B := le_antisymm hZB (hZZ ▸ hBZ)
    rwa [this]
  refine ⟨first, fun y y' hc hc' Z hZ Z' hZ' hm hm' hne hw => ?_⟩
  obtain ⟨z₀, hz₀⟩ := hm
  obtain ⟨z', hz'⟩ := hm'
  obtain ⟨m₁, m₂⟩ := Finset.mem_inter.mp hz₀
  obtain ⟨m₁', m₂'⟩ := Finset.mem_inter.mp hz'
  obtain ⟨x, hx, x', hx', hdd⟩ := hw
  have hnear : z' ∈ cutBelow F.depth (cellBall y 1) :=
    mem_cutBelow_cellBall_of_near_boxes hodd (by have := hpos y hc; omega : 2 * m + 2 ≤ F.blockSide * 1)
      (hboxes y hc Z hZ) (hboxes y' hc' Z' hZ') m₁ m₂ m₁' hx hx' hdd
  obtain ⟨v, hv, hzv⟩ := Finset.mem_biUnion.mp hnear
  have hvy : v = y' := eq_of_mem_sitesBelow hodd hs hzv m₂'
  subst hvy
  obtain ⟨c, hc₁, rfl⟩ := mem_cellBall_iff.mp hv
  have hdist : cellSupDist y (y + siteOfCoords F.top c) ≤ 1 := cellSupDist_add_le hc₁ fun i => by
    rw [period_top]
    have := hextent i
    push_cast
    omega
  have hZ2 := first y _ hc hc' hdist Z hZ (Or.inl ⟨z₀, hz₀⟩)
  exact (hleast _ hc').1.2.2 Z hZ2 Z' hZ' hne ⟨x, hx, x', hx', hdd⟩
end NeighbourBoxes
open NeighbourBoxes in
theorem excludedBoxesOfNeighboursAgree_holds (hcell : ExcludedBoxesAtUncrowdedCell) :
    ExcludedBoxesOfNeighboursAgree := by
  intro F g J₀ h hodd hextent hsmall hlump
  have hLpos := hodd.pos
  haveI : ∀ i, NeZero (F.period F.depth i) := fun i => ⟨by
    rw [period_depth]
    exact Nat.mul_ne_zero (by have := hextent i; omega) hLpos.ne'⟩
  haveI : ∀ i, NeZero (F.period F.top i) := fun i => ⟨by
    rw [period_top]
    have := hextent i
    omega⟩
  have hextent2 : ∀ i, 2 ≤ F.extent i := fun i => by have := hextent i; omega
  have hsmall2 : 11 * 2 ^ 12 * J₀ < F.blockSide := by omega
  exact excludedBoxes_agree_and_separated hodd hextent hsmall (fun y hc => by
      have h0 : ¬ J₀ ≤ (nearbyLumps h y).card := hc
      omega) (fun y hc => (hcell F g J₀ h y hodd hextent2 hsmall2 hlump hc).1)
    (fun y hc Z hZ => by
      have := (hcell F g J₀ h y hodd hextent2 hsmall2 hlump hc).2.2.1 Z hZ
      push_cast
      exact this)
    (fun y hc => (hcell F g J₀ h y hodd hextent2 hsmall2 hlump hc).2.2.2)
end YangMills.Construction.LumpContours
end
