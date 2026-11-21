import YangMills.Construction.HoleBesideASecondHole.HolesAtGrowingScales
import YangMills.Construction.HoleBesideASecondHole.PlacesOfAHole
import YangMills.Construction.HoleBesideASecondHole.SitesOfBlocksAndCells
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages LumpContours Holes HoleSavings CornerBoxes BlockSites
namespace HoleSites
variable {F : BlockFrame}
theorem cellSupDist_self (y : F.Cell) : cellSupDist y y = 0 := by simp [cellSupDist]
theorem supDist_triangle {j : ℕ} [∀ i, NeZero (F.period j i)] (x y z : F.Site j) :
    supDist x z ≤ supDist x y + supDist y z := by
  refine Finset.sup_le fun i _ => ?_
  have hsplit : x i - z i = (x i - y i) + (y i - z i) := by abel
  have hadd := ZMod.natAbs_valMinAbs_add_le (x i - y i) (y i - z i)
  have hxy : ((x i - y i).valMinAbs).natAbs ≤ supDist x y :=
    Finset.le_sup (f := fun i => ((x i - y i).valMinAbs).natAbs) (Finset.mem_univ i)
  have hyz : ((y i - z i).valMinAbs).natAbs ≤ supDist y z :=
    Finset.le_sup (f := fun i => ((y i - z i).valMinAbs).natAbs) (Finset.mem_univ i)
  rw [hsplit]
  omega
theorem mem_lumpOf {L : ℕ} (hL : 0 < L) (hodd : Odd L) (g : LumpGrid L) {j : ℕ} (x : F.Site j) :
    x ∈ lumpOf g x := by
  refine (mem_boxOfCorners (q := lumpCornerPair g x)).mpr ⟨siteCoords x, fun i => ?_, _root_.YangMills.Construction.BlockSites.siteOfCoords_siteCoords x⟩
  obtain ⟨_, hb⟩ := offsetFromCentre_spec hL hodd (siteCoords x i)
  obtain ⟨b1, b2, b3, b4⟩ := g.mem_interval _ hb
  simp only [lumpCornerPair]
  constructor <;> omega
theorem boxSites_coords_self {j : ℕ} (c : F.Site j) :
    boxSites j (siteCoords c) (siteCoords c) = {c} := by
  ext x
  rw [Finset.mem_singleton]
  constructor
  · intro hx
    obtain ⟨a, ha, rfl⟩ := (mem_boxOfCorners (q := (siteCoords c, siteCoords c))).mp hx
    have hac : a = siteCoords c := funext fun i => le_antisymm (ha i).2 (ha i).1
    rw [hac, _root_.YangMills.Construction.BlockSites.siteOfCoords_siteCoords]
  · rintro rfl
    exact (mem_boxOfCorners (q := (siteCoords x, siteCoords x))).mpr
      ⟨siteCoords x, fun i => ⟨le_rfl, le_rfl⟩, _root_.YangMills.Construction.BlockSites.siteOfCoords_siteCoords x⟩
theorem thicken_singleton {j : ℕ} (m : ℕ) (c : F.Site j) :
    thicken m ({c} : Finset (F.Site j)) =
      boxSites j (fun i => siteCoords c i - m) (fun i => siteCoords c i + m) := by
  rw [← boxSites_coords_self c]
  exact thicken_boxSites m _ _ fun _ => le_rfl
theorem innerBox_subset_outerBox (H : Hole F) : H.innerBox ⊆ H.outerBox := by
  simp only [Hole.innerBox, Hole.outerBox]
  rw [thicken_singleton, thicken_singleton]
  intro x hx
  obtain ⟨a, ha, rfl⟩ := (mem_boxOfCorners (q := ((fun i => siteCoords H.centre i - (H.radius : ℤ)),
    (fun i => siteCoords H.centre i + (H.radius : ℤ))))).mp hx
  refine (mem_boxOfCorners (q := ((fun i => siteCoords H.centre i - ((2 * H.radius : ℕ) : ℤ)),
    (fun i => siteCoords H.centre i + ((2 * H.radius : ℕ) : ℤ))))).mpr ⟨a, fun i => ?_, rfl⟩
  have hai := ha i
  simp only at hai ⊢
  push_cast
  constructor <;> omega
theorem exists_offset_of_mem_boxSites {j : ℕ} {lo hi : Fin 4 → ℤ} {m : ℤ}
    (hw : ∀ i, hi i - lo i + 1 ≤ m) {x z : F.Site j}
    (hx : x ∈ boxSites j lo hi) (hz : z ∈ boxSites j lo hi) :
    ∃ d : Fin 4 → ℤ, (∀ i, |d i| ≤ m) ∧ x = z + siteOfCoords j d := by
  obtain ⟨a, ha, rfl⟩ := (mem_boxOfCorners (q := (lo, hi))).mp hx
  obtain ⟨b, hb, rfl⟩ := (mem_boxOfCorners (q := (lo, hi))).mp hz
  refine ⟨a - b, fun i => ?_, ?_⟩
  · have h1 := ha i
    have h2 := hb i
    have h3 := hw i
    simp only at h1 h2
    simp only [Pi.sub_apply]
    rw [abs_le]
    constructor <;> omega
  · rw [← _root_.YangMills.Construction.BlockSites.siteOfCoords_add]
    congr 1
    abel
theorem mem_thicken_iff {j : ℕ} {m : ℕ} {X : Finset (F.Site j)} {x : F.Site j} :
    x ∈ thicken m X ↔ ∃ z ∈ X, ∃ d : Fin 4 → ℤ, (∀ i, |d i| ≤ m) ∧ x = z + siteOfCoords j d := by
  have hm : (((2 * m + 1 : ℕ) : ℤ) - 1) / 2 = m := by
    push_cast
    omega
  simp only [thicken, centredCube, hm, Finset.mem_biUnion, Finset.mem_image, Fintype.mem_piFinset,
    Finset.mem_Icc, abs_le]
  constructor
  · rintro ⟨z, hz, d, hd, rfl⟩
    exact ⟨z, hz, d, hd, rfl⟩
  · rintro ⟨z, hz, d, hd, rfl⟩
    exact ⟨z, hz, d, hd, rfl⟩
theorem mem_cutBelow_cellBall_of_boxSites (hodd : Odd F.blockSide) {m r : ℕ} (hm : m ≤ F.blockSide * r)
    {Z : Finset (F.Site F.depth)}
    (hc : ∃ lo hi : Fin 4 → ℤ, Z = boxSites F.depth lo hi ∧ ∀ i, lo i ≤ hi i ∧ hi i - lo i + 1 ≤ m)
    {u : F.Cell} {z₀ x : F.Site F.depth} (hz₀ : z₀ ∈ Z) (hu : z₀ ∈ sitesBelow F.depth u) (hx : x ∈ Z) :
    x ∈ cutBelow F.depth (cellBall u r) := by
  obtain ⟨lo, hi, rfl, hw⟩ := hc
  obtain ⟨d, hd, rfl⟩ := exists_offset_of_mem_boxSites (m := (m : ℤ)) (fun i => (hw i).2) hx hz₀
  refine add_mem_cutBelow_cellBall hodd hu d r fun i => ?_
  have h1 := hd i
  linarith
theorem mem_cellBall_add [∀ i, NeZero (F.period F.top i)] {u y' v : F.Cell} {r r' : ℕ}
    (hv : v ∈ cellBall u r) (hu : cellSupDist y' u ≤ r') : v ∈ cellBall y' (r + r') := by
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
theorem cellSupDist_le_one_of_mem_cellBall [∀ i, NeZero (F.period F.top i)] (hside : ∀ i, 2 < F.extent i)
    {y v : F.Cell} (hv : v ∈ cellBall y 1) : cellSupDist y v ≤ 1 := by
  obtain ⟨c, hc, rfl⟩ := mem_cellBall_iff.mp hv
  exact cellSupDist_add_le hc fun i => by
    rw [period_top]
    have hi := hside i
    push_cast
    omega
theorem exists_offset_of_mem_plaquetteCorners {j : ℕ} {p : F.Site j × Fin 4 × Fin 4} (hp : p.2.1 ≠ p.2.2)
    {x : F.Site j} (hx : x ∈ plaquetteCorners p) :
    ∃ c : Fin 4 → ℤ, (∀ i, 0 ≤ c i ∧ c i ≤ 1) ∧ x = p.1 + siteOfCoords j c := by
  have hstep : ∀ μ : Fin 4, (siteOfCoords j (Pi.single μ 1) : F.Site j) = unitStep j μ := fun _ => rfl
  simp only [plaquetteCorners, Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · refine ⟨0, fun i => by simp, ?_⟩
    have hzero : (siteOfCoords j (0 : Fin 4 → ℤ) : F.Site j) = 0 := by
      funext i
      simp [siteOfCoords]
    rw [hzero, add_zero]
  · refine ⟨Pi.single p.2.1 1, fun i => ?_, by rw [hstep]⟩
    by_cases h : i = p.2.1
    · subst h
      simp
    · simp [h]
  · refine ⟨Pi.single p.2.2 1, fun i => ?_, by rw [hstep]⟩
    by_cases h : i = p.2.2
    · subst h
      simp
    · simp [h]
  · refine ⟨Pi.single p.2.1 1 + Pi.single p.2.2 1, fun i => ?_, ?_⟩
    · by_cases h : i = p.2.1
      · subst h
        simp [hp]
      · by_cases h' : i = p.2.2
        · subst h'
          simp [Ne.symm hp]
        · simp [h, h']
    · rw [_root_.YangMills.Construction.BlockSites.siteOfCoords_add, hstep, hstep, add_assoc]
theorem exists_step_of_mem_plaquetteCorners {j : ℕ} {p : F.Site j × Fin 4 × Fin 4} (hp : p.2.1 ≠ p.2.2)
    {x z : F.Site j} (hx : x ∈ plaquetteCorners p) (hz : z ∈ plaquetteCorners p) :
    ∃ e : Fin 4 → ℤ, (∀ i, |e i| ≤ 1) ∧ z = x + siteOfCoords j e := by
  obtain ⟨c, hc, rfl⟩ := exists_offset_of_mem_plaquetteCorners hp hx
  obtain ⟨c', hc', rfl⟩ := exists_offset_of_mem_plaquetteCorners hp hz
  refine ⟨c' - c, fun i => ?_, ?_⟩
  · have h1 := hc i
    have h2 := hc' i
    simp only [Pi.sub_apply]
    rw [abs_le]
    constructor <;> omega
  · have hcc : c' = c + (c' - c) := by abel
    rw [add_assoc, ← _root_.YangMills.Construction.BlockSites.siteOfCoords_add, ← hcc]
end HoleSites
namespace HoleSavings.HoleData
open HoleSites
variable {F : BlockFrame} {g : LumpGrid F.blockSide} {a s θ : ℝ} {J₀ : ℕ} (D : HoleData F g a s θ J₀)
theorem mem_coreCells {C : ℝ} {k : ℕ} {y : F.Cell} :
    y ∈ D.coreCells C k ↔ y ∈ D.cells ∧ ∀ z ∈ D.badCells C, k ≤ cellSupDist y z := by
  simp [coreCells]
theorem not_mem_badCells_of_mem_coreCells {C : ℝ} {k : ℕ} (hk : 1 ≤ k) {y : F.Cell}
    (hy : y ∈ D.coreCells C k) : y ∉ D.badCells C := by
  intro hs
  have hle := ((D.mem_coreCells).mp hy).2 y hs
  rw [cellSupDist_self] at hle
  omega
theorem not_isCrowded_of_mem_coreCells {C : ℝ} {k : ℕ} (hk : 1 ≤ k) {y : F.Cell}
    (hy : y ∈ D.coreCells C k) : ¬ IsCrowded J₀ D.hotFineLumps y := by
  classical
  exact fun hc =>
    D.not_mem_badCells_of_mem_coreCells hk hy
      (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨((D.mem_coreCells).mp hy).1, hc⟩))
theorem coreCells_antitone {C : ℝ} {k k' : ℕ} (h : k ≤ k') : D.coreCells C k' ⊆ D.coreCells C k := by
  intro y hy
  obtain ⟨h₁, h₂⟩ := (D.mem_coreCells).mp hy
  exact (D.mem_coreCells).mpr ⟨h₁, fun z hz => h.trans (h₂ z hz)⟩
theorem mem_coreCells_of_supDist_le_one [∀ i, NeZero (F.period F.top i)] {C : ℝ} {k : ℕ} {y u : F.Cell}
    (hy : y ∈ D.coreCells C (k + 1)) (hu : u ∈ D.cells) (hd : cellSupDist y u ≤ 1) :
    u ∈ D.coreCells C k := by
  refine (D.mem_coreCells).mpr ⟨hu, fun z hz => ?_⟩
  have h1 := ((D.mem_coreCells).mp hy).2 z hz
  have h2 : cellSupDist y z ≤ cellSupDist y u + cellSupDist u z := supDist_triangle y u z
  omega
theorem exists_eq_lumpOf_of_mem_hotFineLumps {l : Finset (F.Site F.depth)} (hl : l ∈ D.hotFineLumps) :
    ∃ x ∈ cutBelow F.depth D.cells, l = lumpOf g x := by
  classical
  obtain ⟨p, hp, hlp⟩ := Finset.mem_biUnion.mp hl
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hlp
  exact ⟨x, (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2.2 hx, rfl⟩
theorem isLump_of_mem_hotFineLumps : ∀ l ∈ D.hotFineLumps, IsLump g l := fun l hl => by
  obtain ⟨x, -, rfl⟩ := D.exists_eq_lumpOf_of_mem_hotFineLumps hl
  exact ⟨x, rfl⟩
theorem exists_subset_sitesBelow_of_mem_hotFineLumps (hodd : Odd F.blockSide) (hs : ∀ i, 0 < F.extent i)
    {l : Finset (F.Site F.depth)} (hl : l ∈ D.hotFineLumps) :
    ∃ u ∈ D.cells, l ⊆ sitesBelow F.depth u ∧ l.Nonempty := by
  obtain ⟨x, hx, rfl⟩ := D.exists_eq_lumpOf_of_mem_hotFineLumps hl
  obtain ⟨u, hu, hxu⟩ := Finset.mem_biUnion.mp hx
  exact ⟨u, hu, lumpOf_subset_sitesBelow hodd hs g hxu, x, mem_lumpOf hodd.pos hodd g x⟩
end HoleSavings.HoleData
end YangMills.Construction
end
