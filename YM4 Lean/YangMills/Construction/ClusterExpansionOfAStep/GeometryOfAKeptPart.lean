import YangMills.Construction.ClusterExpansionOfAStep.BallsAndBlocksOfATorusForm
import YangMills.Construction.ClusterExpansionOfAStep.CountsOfAClassAtAStep
import YangMills.Construction.ClusterExpansionOfAStep.NearAClassOfASetting
import YangMills.Construction.ClusterExpansionOfAStep.OffsetsOfABlock
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open TorusFields TorusLumps StepSettings BlockOffsets TorusBalls BlockAverages LumpContours
namespace KeptRegion
variable {n L : ℕ} [NeZero n] [NeZero L]
open Classical in
def clusterSites (L : ℕ) [NeZero L] (bad : Finset (TorusBond (n * L))) (Yt : Finset (TorusSite (n * L)))
    (C : Finset (TorusSite n)) : Finset (TorusSite (n * L)) :=
  bad.image Prod.fst ∪ Yt ∪ sitesInBlocks L C
theorem div_side_add_one_le_div (hL : 2 ^ 16 ≤ L) {r m : ℕ} (hr : 2 ^ 16 ≤ r) (hm : m ≤ 11 * r) :
    m / L + 1 ≤ r / 64 := by
  have h1 : m / L ≤ m / 2 ^ 16 := Nat.div_le_div_left hL (by norm_num)
  omega
theorem supDist_le_of_parentBlock_eq (hodd : Odd L) {y w : TorusSite (n * L)}
    (h : parentBlock L y = parentBlock L w) : supDist y w ≤ L := by
  have hne : NeZero (n * L) := ⟨mul_ne_zero (NeZero.ne n) (NeZero.ne L)⟩
  obtain ⟨o, ho, e⟩ := exists_fineSite_of_parentBlock hodd (parentBlock L y) y rfl
  obtain ⟨o', ho', e'⟩ := exists_fineSite_of_parentBlock hodd (parentBlock L y) w h.symm
  have hw : w = y + siteOfInt (o' - o) := by
    calc w = fineSite L (parentBlock L y) 0 o' := e'
      _ = fineSite L (parentBlock L y) 0 o + siteOfInt (o' - o) := by
        funext i
        simp [fineSite, siteOfInt]
      _ = y + siteOfInt (o' - o) := by rw [← e]
  rw [hw]
  refine supDist_add_siteOfInt_le _ _ _ fun i => ?_
  have h1 := (mem_centredCube_iff o).mp ho i
  have h2 := (mem_centredCube_iff o').mp ho' i
  simp only [Pi.sub_apply]
  omega
section
variable {r r' : ℕ} {bad : Finset (TorusBond (n * L))} {Yt : Finset (TorusSite (n * L))}
  {C : Finset (TorusSite n)} {P : Finset (Finset (TorusSite n))}
structure KeptPartData (L r r' : ℕ) [NeZero L] (bad : Finset (TorusBond (n * L)))
    (Yt : Finset (TorusSite (n * L))) (C : Finset (TorusSite n)) (P : Finset (Finset (TorusSite n))) : Prop where
  attached_eq : attachedSites L r bad Yt C = clusterSites L bad Yt C
  subset_components : P ⊆ chainComponents r' (coarseHull L r r' bad Yt C)
  side_ge : 2 ^ 16 ≤ L
  side_odd : Odd L
  range_ge : 8 * L ≤ r
  range_floor : 2 ^ 16 ≤ r
  range_le : r ≤ r' + 1
variable (d : KeptPartData L r r' bad Yt C P)
include d
theorem div_side_add_one_le_nextRange (m : ℕ) (hm : m ≤ 11 * r) : m / L + 1 ≤ r' := by
  have := div_side_add_one_le_div d.side_ge d.range_floor hm
  have h1 := d.range_le
  have h2 := d.range_floor
  omega
theorem storedBlocks_subset_coarseHull : storedBlocks L r bad Yt C ⊆ coarseHull L r r' bad Yt C := by
  intro z hz
  unfold coarseHull
  rw [mem_thickening]
  exact ⟨z, hz, by simp [supDist_self]⟩
theorem mem_biUnion_of_supDist_le {a b : TorusSite n} (ha : a ∈ P.biUnion id)
    (hb : b ∈ coarseHull L r r' bad Yt C) (h : supDist a b ≤ r') : b ∈ P.biUnion id := by
  classical
  obtain ⟨X, hX, haX⟩ := Finset.mem_biUnion.mp ha
  have hXc := d.subset_components hX
  have haY := subset_of_mem_chainComponents hXc haX
  exact Finset.mem_biUnion.mpr ⟨X, hX, mem_of_chainConnected_of_mem_chainComponents hXc haX hb
    (chainConnected_of_supDist_le haY hb h)⟩
theorem parentBlock_mem_storedBlocks {u : TorusSite (n * L)} (hu : u ∈ clusterSites L bad Yt C) :
    parentBlock L u ∈ storedBlocks L r bad Yt C := by
  classical
  unfold storedBlocks
  refine Finset.mem_union_right _ ?_
  unfold coreBlocks
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨u, Finset.mem_inter.mpr ⟨?_, ?_⟩⟩
  · simp [sitesInBlocks]
  · rw [mem_thickening]
    exact ⟨u, d.attached_eq ▸ hu, by simp [supDist_self]⟩
theorem parentBlock_mem_of_supDist_le {u v : TorusSite (n * L)} (hu : u ∈ clusterSites L bad Yt C)
    (hv : v ∈ clusterSites L bad Yt C) (h : supDist u v ≤ 11 * r) (hb : parentBlock L u ∈ P.biUnion id) :
    parentBlock L v ∈ P.biUnion id := by
  refine mem_biUnion_of_supDist_le d hb (storedBlocks_subset_coarseHull d (parentBlock_mem_storedBlocks d hv)) ?_
  exact (supDist_parentBlock_le_div_add_one L u v).trans (div_side_add_one_le_nextRange d _ h)
theorem parentBlock_mem_of_chainConnected {u v : TorusSite (n * L)}
    (h : ChainConnected (10 * r) (clusterSites L bad Yt C) u v)
    (hu : u ∈ clusterSites L bad Yt C) (hb : parentBlock L u ∈ P.biUnion id) :
    parentBlock L v ∈ P.biUnion id := by
  induction h with
  | refl => exact hb
  | tail _ hs ih => exact parentBlock_mem_of_supDist_le d hs.1 hs.2.1 (by have := hs.2.2; omega) ih
theorem mem_attachedInBlocks_iff {u : TorusSite (n * L)} :
    u ∈ attachedInBlocks L r bad Yt C (P.biUnion id) ↔
      u ∈ clusterSites L bad Yt C ∧ parentBlock L u ∈ P.biUnion id := by
  classical
  unfold attachedInBlocks
  rw [d.attached_eq]
  simp [sitesInBlocks]
theorem exists_clusters_eq_attachedInBlocks :
    ∃ K' ⊆ clusterComponents L r bad Yt C, K'.biUnion id = attachedInBlocks L r bad Yt C (P.biUnion id) := by
  classical
  refine ⟨(clusterComponents L r bad Yt C).filter (· ⊆ attachedInBlocks L r bad Yt C (P.biUnion id)),
    Finset.filter_subset _ _, ?_⟩
  ext x
  simp only [Finset.mem_biUnion, Finset.mem_filter, id]
  constructor
  · rintro ⟨X, ⟨_, hsub⟩, hx⟩
    exact hsub hx
  · intro hx
    obtain ⟨hxU, hxb⟩ := (mem_attachedInBlocks_iff d).mp hx
    obtain ⟨X, hX, hxX⟩ := exists_mem_chainComponents (r := 10 * r) hxU
    refine ⟨X, ⟨hX, fun v hv => ?_⟩, hxX⟩
    have hvU : v ∈ clusterSites L bad Yt C := subset_of_mem_chainComponents hX hv
    exact (mem_attachedInBlocks_iff d).mpr
      ⟨hvU, parentBlock_mem_of_chainConnected d (chainConnected_of_mem_chainComponents hX hxX hv) hxU hxb⟩
theorem mem_clusterSites_of_mem_support {z : TorusSite (n * L)} (hz : z ∈ Yt) : z ∈ clusterSites L bad Yt C := by
  classical
  unfold clusterSites
  exact Finset.mem_union_left _ (Finset.mem_union_right _ hz)
theorem chainConnected_clusterSites {z v : TorusSite (n * L)} (h : ChainConnected r Yt z v) :
    ChainConnected (10 * r) (clusterSites L bad Yt C) z v := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hs ih =>
    exact ih.tail ⟨mem_clusterSites_of_mem_support d hs.1, mem_clusterSites_of_mem_support d hs.2.1,
      by have := hs.2.2; omega⟩
theorem mem_componentsWithin {z : TorusSite (n * L)} (hz : z ∈ Yt) (hb : parentBlock L z ∈ P.biUnion id) :
    z ∈ componentsWithin L r Yt (attachedInBlocks L r bad Yt C (P.biUnion id)) := by
  classical
  obtain ⟨X, hX, hzX⟩ := exists_mem_chainComponents (r := r) hz
  unfold componentsWithin
  refine Finset.mem_biUnion.mpr ⟨X, Finset.mem_filter.mpr ⟨hX, fun v hv => ?_⟩, hzX⟩
  have hvY := subset_of_mem_chainComponents hX hv
  exact (mem_attachedInBlocks_iff d).mpr ⟨mem_clusterSites_of_mem_support d hvY,
    parentBlock_mem_of_chainConnected d (chainConnected_clusterSites d (chainConnected_of_mem_chainComponents hX hzX hv))
      (mem_clusterSites_of_mem_support d hz) hb⟩
theorem componentsWithin_subset_attached : componentsWithin L r Yt (attachedInBlocks L r bad Yt C (P.biUnion id)) ⊆
    attachedInBlocks L r bad Yt C (P.biUnion id) := by
  classical
  intro z hz
  obtain ⟨X, hX, hzX⟩ := Finset.mem_biUnion.mp hz
  exact (Finset.mem_filter.mp hX).2 hzX
theorem componentsWithin_subset_support :
    componentsWithin L r Yt (attachedInBlocks L r bad Yt C (P.biUnion id)) ⊆ Yt := by
  classical
  intro z hz
  obtain ⟨X, hX, hzX⟩ := Finset.mem_biUnion.mp hz
  exact subset_of_mem_chainComponents (Finset.mem_filter.mp hX).1 hzX
theorem exists_attached_near {y : TorusSite (n * L)}
    (hy : parentBlock L y ∈ blocksNear L r (attachedInBlocks L r bad Yt C (P.biUnion id))) :
    ∃ u ∈ attachedInBlocks L r bad Yt C (P.biUnion id), supDist y u ≤ 5 * r + L := by
  classical
  obtain ⟨w, hw⟩ := (Finset.mem_filter.mp hy).2
  obtain ⟨hw1, hw2⟩ := Finset.mem_inter.mp hw
  obtain ⟨u, hu, hwu⟩ := (mem_thickening _ _ _).mp hw2
  refine ⟨u, hu, ?_⟩
  have hb : parentBlock L y = parentBlock L w :=
    (Finset.mem_singleton.mp (Finset.mem_filter.mp hw1).2).symm
  have := supDist_le_of_parentBlock_eq d.side_odd hb
  have h2 := supDist_triangle y w u
  omega
theorem quarter_le_supDist {z y : TorusSite (n * L)} (hz : z ∈ Yt)
    (hnot : z ∉ componentsWithin L r Yt (attachedInBlocks L r bad Yt C (P.biUnion id)))
    (hy : y ∈ sitesInBlocks L (blocksNear L r (attachedInBlocks L r bad Yt C (P.biUnion id)))) :
    (r : ℝ) / 4 ≤ supDist y z := by
  classical
  by_contra hlt
  push Not at hlt
  have hlt' : 4 * supDist y z < r := by
    have : (4 * supDist y z : ℝ) < r := by linarith
    exact_mod_cast this
  have hyN : parentBlock L y ∈ blocksNear L r (attachedInBlocks L r bad Yt C (P.biUnion id)) := by
    simpa [sitesInBlocks] using hy
  obtain ⟨u, hu, hyu⟩ := exists_attached_near d hyN
  obtain ⟨huU, hub⟩ := (mem_attachedInBlocks_iff d).mp hu
  have h1 : supDist u z ≤ 11 * r := by
    have h2 := supDist_triangle u y z
    rw [supDist_comm u y] at h2
    have := d.range_ge
    omega
  exact hnot (mem_componentsWithin d hz
    (parentBlock_mem_of_supDist_le d huU (mem_clusterSites_of_mem_support d hz) h1 hub))
theorem mem_nearSites_of_mem_blocksNear {Y : TorusSite n}
    (hY : Y ∈ blocksNear L r (attachedInBlocks L r bad Yt C (P.biUnion id))) :
    Y ∈ nearSites r' (P.biUnion id) := by
  classical
  obtain ⟨w, hw⟩ := (Finset.mem_filter.mp hY).2
  obtain ⟨hw1, hw2⟩ := Finset.mem_inter.mp hw
  obtain ⟨u, hu, hwu⟩ := (mem_thickening _ _ _).mp hw2
  obtain ⟨huU, hub⟩ := (mem_attachedInBlocks_iff d).mp hu
  have hb : parentBlock L w = Y := Finset.mem_singleton.mp (Finset.mem_filter.mp hw1).2
  have h1 : supDist Y (parentBlock L u) ≤ r / 64 := by
    rw [← hb]
    refine (supDist_parentBlock_le_div_add_one L w u).trans (div_side_add_one_le_div d.side_ge d.range_floor ?_)
    have := Nat.div_le_self (supDist w u) 1
    omega
  simp only [nearSites, Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨_, hub, ?_⟩
  have h2 := d.range_le
  have h3 := d.range_floor
  have h4 : 4 * supDist Y (parentBlock L u) < r' := by omega
  have : (4 * supDist Y (parentBlock L u) : ℝ) < r' := by exact_mod_cast h4
  linarith
theorem eighth_lt_supDist {Y Z : TorusSite n} (hY : Y ∈ nearSites r' (P.biUnion id))
    (hN : Y ∉ blocksNear L r (attachedInBlocks L r bad Yt C (P.biUnion id)))
    (hZ : Z ∈ storedBlocks L r bad Yt C) {y z : TorusSite (n * L)} (hy : y ∈ sitesInBlocks L {Y})
    (hz : z ∈ sitesInBlocks L {Z}) : (r : ℝ) / 8 < supDist y z := by
  classical
  by_contra hle
  push Not at hle
  have hle' : 8 * supDist y z ≤ r := by
    have : (8 * supDist y z : ℝ) ≤ r := by linarith
    exact_mod_cast this
  have hby : parentBlock L y = Y := Finset.mem_singleton.mp (Finset.mem_filter.mp hy).2
  have hbz : parentBlock L z = Z := Finset.mem_singleton.mp (Finset.mem_filter.mp hz).2
  obtain ⟨z', hz', hYz⟩ : ∃ z' ∈ P.biUnion id, (supDist Y z' : ℝ) < (r' : ℝ) / 4 := by
    simpa [nearSites] using hY
  have hYz' : 4 * supDist Y z' < r' := by
    have : (4 * supDist Y z' : ℝ) < r' := by linarith
    exact_mod_cast this
  have hYZ : supDist Y Z ≤ r / 64 := by
    rw [← hby, ← hbz]
    exact (supDist_parentBlock_le_div_add_one L y z).trans
      (div_side_add_one_le_div d.side_ge d.range_floor (by omega))
  have hZP : Z ∈ P.biUnion id := by
    refine mem_biUnion_of_supDist_le d hz' (storedBlocks_subset_coarseHull d hZ) ?_
    have h2 := supDist_triangle z' Y Z
    rw [supDist_comm z' Y] at h2
    have h3 := d.range_le
    have h4 := d.range_floor
    omega
  have hnear : ∀ u ∈ attachedInBlocks L r bad Yt C (P.biUnion id), supDist y u ≤ 5 * r → False := by
    intro u hu hyu
    refine hN ?_
    unfold blocksNear
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨y, Finset.mem_inter.mpr ⟨hy, (mem_thickening _ _ _).mpr ⟨u, hu, hyu⟩⟩⟩
  rcases Finset.mem_union.mp hZ with hC | hcore
  · have hzU : z ∈ clusterSites L bad Yt C := by
      unfold clusterSites
      refine Finset.mem_union_right _ ?_
      simpa [sitesInBlocks, hbz] using hC
    exact hnear z ((mem_attachedInBlocks_iff d).mpr ⟨hzU, hbz ▸ hZP⟩) (by omega)
  · obtain ⟨w, hw⟩ := (Finset.mem_filter.mp hcore).2
    obtain ⟨hw1, hw2⟩ := Finset.mem_inter.mp hw
    obtain ⟨u, hu, hwu⟩ := (mem_thickening _ _ _).mp hw2
    have huU : u ∈ clusterSites L bad Yt C := d.attached_eq ▸ hu
    have hbw : parentBlock L w = Z := Finset.mem_singleton.mp (Finset.mem_filter.mp hw1).2
    have huP : parentBlock L u ∈ P.biUnion id := by
      refine mem_biUnion_of_supDist_le d hZP (storedBlocks_subset_coarseHull d (parentBlock_mem_storedBlocks d huU)) ?_
      rw [← hbw]
      exact (supDist_parentBlock_le_div_add_one L w u).trans (div_side_add_one_le_nextRange d _ (by omega))
    have hzw := supDist_le_of_parentBlock_eq d.side_odd (hbz.trans hbw.symm)
    have h2 := supDist_triangle y z u
    have h3 := supDist_triangle z w u
    have h4 := d.range_ge
    exact hnear u ((mem_attachedInBlocks_iff d).mpr ⟨huU, huP⟩) (by omega)
end
end KeptRegion
end YangMills.Construction
end
