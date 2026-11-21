import YangMills.Construction.Lattice.BlockPartition
import YangMills.Construction.Lattice.CubesLayersAndTopsOfADecreasingSequence
import YangMills.Construction.Lattice.InwardBondsAndSetsInForce
import YangMills.Construction.Lattice.BondEndpointsAndFiniteness
import YangMills.Construction.Lattice.ExpansionsSpacesAndLocalNormsOfASequence
import YangMills.Construction.Lattice.FrameOfASeparatedSequence
import Mathlib
import YangMills.Construction.Lattice.SupDistanceLatticesCubesBlocksAndComplements
import YangMills.Construction.Lattice.WeightedDistanceOfASeparatedSequence
set_option autoImplicit false

section
open Set
noncomputable section
namespace YangMills.Construction.SeparatedFrame.FrameProperties
open PeriodicLattice SeparatedSequences
variable {L m : ℕ}
variable (F : SeparatedFrame L m)
abbrev nextMember (n : ℕ) : Set (FourTorus L m) := chainWithEmptyTail F.t F.Ω (n + 1)
abbrev memberComplement (n : ℕ) : Set (FourTorus L m) :=
  complementRegion (F.scaleData.blockPartitionIndex n) (F.Ω n)
def LayerDecomposition : Prop :=
  (∀ n ≤ F.t, F.layerAt n ⊆ F.Ω n ∧
    F.layerAt n = ⋃ y ∈ F.layerSitesAt n, siteBlock F.scaleData y) ∧
  (∀ y y' : F.Centre, y ≠ y' → Disjoint (interior y.cell) (interior y'.cell)) ∧
  (⋃ y : F.Centre, y.cell) = F.Ω 0 ∧
  (∀ n ≤ F.t, ∀ y ∈ F.layerSitesAt n, ∀ x ∈ interior (siteBlock F.scaleData y),
    x ∉ nextMember F n ∧ ∀ j ≤ F.t, j ≠ n → x ∉ F.layerAt j) ∧
  (∀ n ≤ F.t, ∀ y : SiteAtLevel L m F.K n,
    y ∈ F.layerSitesAt n ↔ (y : FourTorus L m) ∈ F.Ω n ∧ (y : FourTorus L m) ∉ nextMember F n) ∧
  (∀ n ≤ F.t, ∀ n' ≤ F.t, n ≠ n' → ∀ y ∈ F.layerSitesAt n, ∀ y' ∈ F.layerSitesAt n',
    (y : FourTorus L m) ≠ y') ∧
  (∀ n ≤ F.t, F.Ω n ≠ ∅ → ∀ x : FourTorus L m, x ∈ F.Ω n ∨ x ∈ memberComplement F n) ∧
  ∀ n q, n < q → q ≤ F.t → F.Ω q ≠ ∅ → F.layerAt n ⊆ memberComplement F q
end YangMills.Construction.SeparatedFrame.FrameProperties
end
end

open Set
open scoped Matrix.Norms.L2Operator ENNReal
noncomputable section
namespace YangMills.Construction
open PeriodicLattice SeparatedSequences TorusMetric
namespace SeparatedFrame.FrameProperties
variable {L m : ℕ}
section Chain
variable (F : SeparatedFrame L m)
theorem zero_lt_L (F : SeparatedFrame L m) : 0 < L := by
  have := F.thirteen_le_L
  omega
theorem neg_m_le_levelDepth {n : ℕ} (hn : n ≤ F.t) : -(m : ℤ) ≤ levelDepth F.K n := by
  have := F.t_le
  simp only [levelDepth]
  omega
def cutoffParameters : SeparatedSequence.Parameters L m where
  K := F.K
  k := F.K
  blockExp := 1
  gapExp := 1
  odd_L := F.L_odd
  thirteen_le_L := F.thirteen_le_L
  L_le_gapFactor := by simp
  sq_le_gapSize := by simp [pow_two]
  m_pos := F.m_pos
  one_le_k := F.K_pos
  k_le_K := le_rfl
theorem blockUnionGeometry (hc : AntitoneBlockUnionGeometry) :
    MembersAreFinerRegions F.scaleData F.Ω ∧
      LayersAreBlockUnions F.scaleData F.Ω ∧
      LayerDistIsPseudometric F.scaleData F.Ω := by
  have h := hc L m F.L_odd F.thirteen_le_L F.m_pos F.scaleData F.K_pos
  exact h.1 F.Ω (h.2.1 _ _ F.isSeparated)
theorem Ω_antitone {p q : ℕ} (hpq : p ≤ q) (hq : q ≤ F.t) : F.Ω q ⊆ F.Ω p := by
  induction q, hpq using Nat.le_induction with
  | base => exact subset_rfl
  | succ q hpq ih =>
    exact ((F.isSeparated.2 q (by omega : q < F.t)).1).trans (ih (by omega))
theorem nextMember_eq_truncatedMember {n : ℕ} (hn : n ≤ F.t) :
    nextMember F n = SeparatedSequences.truncatedMember F.scaleData F.Ω (n + 1) := by
  by_cases h : n = F.t
  · subst h
    simp [nextMember, chainWithEmptyTail, SeparatedSequences.truncatedMember]
  · have h1 : n + 1 ≤ F.scaleData.top := by
      have : n < F.t := lt_of_le_of_ne hn h
      exact this
    have h2 : n + 1 ≠ F.t + 1 := by omega
    simp only [nextMember, chainWithEmptyTail, SeparatedSequences.truncatedMember, if_pos h1,
      Function.update_of_ne h2]
theorem blockPartitionIndex_bounds {n : ℕ} (hn : n ≤ F.t) (hne : F.Ω n ≠ ∅) :
    -(m : ℤ) ≤ F.scaleData.blockPartitionIndex n ∧ F.scaleData.blockPartitionIndex n ≤ F.K := by
  rcases F.isSeparated.1 n hn with h | ⟨h, -⟩
  · exact absurd h hne
  · refine ⟨h, ?_⟩
    simp only [SeparatedSequences.ScaleData.blockPartitionIndex, scaledCubeIndex, levelDepth]
    omega
end Chain
section Centres
variable {F : SeparatedFrame L m}
theorem exists_layerSite_of_centre (y : F.Centre) :
    y.level ≤ F.t ∧ ∃ z : SiteAtLevel L m F.K y.level, z ∈ F.layerSitesAt y.level ∧
      (z : FourTorus L m) = y.1 := by
  have hne : {n | n ≤ F.t ∧ ∃ x : SiteAtLevel L m F.K n, x ∈ F.layerSitesAt n ∧
      (x : FourTorus L m) = y.1}.Nonempty := by
    obtain ⟨y, hy⟩ := y
    simp only [layerPoints, mem_iUnion, mem_image] at hy
    obtain ⟨n, hn, x, hx, rfl⟩ := hy
    exact ⟨n, hn, x, hx, rfl⟩
  exact Nat.sInf_mem hne
def centreOf {n : ℕ} (hn : n ≤ F.t) (z : SiteAtLevel L m F.K n) (hz : z ∈ F.layerSitesAt n) :
    F.Centre :=
  ⟨(z : FourTorus L m), by
    simp only [layerPoints, mem_iUnion, mem_image]
    exact ⟨n, hn, z, hz, rfl⟩⟩
theorem centre_level_eq (hc : AntitoneBlockUnionGeometry) (y : F.Centre) {n : ℕ}
    (hn : n ≤ F.t) (x : SiteAtLevel L m F.K n) (hx : x ∈ F.layerSitesAt n)
    (hxy : (x : FourTorus L m) = y.1) : y.level = n := by
  obtain ⟨h1, z, hz, hzy⟩ := exists_layerSite_of_centre y
  by_contra hne
  exact (blockUnionGeometry F hc).2.1.2.2.2.1 _ h1 _ hn hne z hz x hx (hzy.trans hxy.symm)
theorem centre_cell_eq (y : F.Centre) {n : ℕ} (z : SiteAtLevel L m F.K n) (hn : y.level = n)
    (hz : (z : FourTorus L m) = y.1) : y.cell = siteBlock F.scaleData z := by
  subst hn
  simp only [Centre.cell, closedSupCube, siteBlock, cubeAround, hz]
theorem cubeAround_subset_closure_interior (hF : SupDistance.SupDistLatticeFacts)
    {n : ℕ} (hn : n ≤ F.K) (z : SiteAtLevel L m F.K n) :
    cubeAround z ⊆ closure (interior (cubeAround z)) := by
  obtain ⟨-, hL, -, -, -⟩ := hF L m (cutoffParameters F) 0 n (Nat.zero_le _) (by
    show n ≤ F.K + m
    omega)
  obtain ⟨-, ho, -, hcl⟩ := hL.2.2 z
  have hsub : SupDistance.openLevelCube z ⊆ cubeAround z :=
    fun u hu => (Set.ext_iff.1 hcl u).2 (subset_closure hu)
  have hint := interior_maximal hsub ho
  exact fun u hu => closure_mono hint ((Set.ext_iff.1 hcl u).1 hu)
end Centres
section Decomposition
variable (F : SeparatedFrame L m)
theorem layerDecomposition (hc : AntitoneBlockUnionGeometry)
    (hF : SupDistance.SupDistLatticeFacts) : LayerDecomposition F := by
  obtain ⟨hA, ⟨hB1, hB2, hB3, hB4, hB5, hB6, hB7⟩, -⟩ := blockUnionGeometry F hc
  have hsub : ∀ n ≤ F.t, F.layerAt n ⊆ F.Ω n := by
    intro n hn x hx
    obtain ⟨y, hy, -⟩ := mem_iUnion₂.1 ((Set.ext_iff.1 (hB1 n hn) x).1 hx)
    exact ((hB2 n hn y hy).2.1 hx).1
  refine ⟨fun n hn => ⟨hsub n hn, hB1 n hn⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro y y' hne
    obtain ⟨h1, z, hz, hzy⟩ := exists_layerSite_of_centre y
    obtain ⟨h1', z', hz', hzy'⟩ := exists_layerSite_of_centre y'
    rw [centre_cell_eq y z rfl hzy, centre_cell_eq y' z' rfl hzy']
    refine hB5 _ h1 _ h1' z hz z' hz' ?_
    rw [hzy, hzy']
    exact fun h => hne (Subtype.ext h)
  · rw [← hB6]
    apply subset_antisymm
    · refine iUnion_subset fun y => ?_
      obtain ⟨h1, z, hz, hzy⟩ := exists_layerSite_of_centre y
      rw [centre_cell_eq y z rfl hzy]
      exact fun x hx => mem_iUnion₂.2 ⟨y.level, h1, mem_iUnion₂.2 ⟨z, hz, hx⟩⟩
    · refine iUnion₂_subset fun j hj => iUnion₂_subset fun z hz => ?_
      have hj' : j ≤ F.t := hj
      let y : F.Centre := centreOf hj' z hz
      have hl : y.level = j := centre_level_eq hc y hj' z hz rfl
      have : siteBlock F.scaleData z = y.cell := (centre_cell_eq y z hl rfl).symm
      rw [this]
      exact subset_iUnion (fun y : F.Centre => y.cell) y
  · intro n hn y hy x hx
    rw [nextMember_eq_truncatedMember F hn]
    refine ⟨fun h => ?_, fun j hj hne h => ?_⟩
    · exact disjoint_left.1 (hB2 n hn y hy).2.2 hx h
    · exact hne ((hB7 n hn y hy x hx).2 j hj h)
  · intro n hn y
    rw [nextMember_eq_truncatedMember F hn]
    exact hB3 n hn y
  · intro n hn n' hn' hne y hy y' hy'
    exact hB4 n hn n' hn' hne y hy y' hy'
  · intro n hn hne x
    obtain ⟨h1, h2⟩ := blockPartitionIndex_bounds F hn hne
    by_cases hx : x ∈ memberComplement F n
    · exact Or.inr hx
    · exact Or.inl (((hA n hn).2 _ le_rfl h2 h1).2 x hx)
  · intro n q hnq hq hne x hx
    obtain ⟨h1, h2⟩ := blockPartitionIndex_bounds F hq hne
    have hcompl : memberComplement F q = closure (F.Ω q)ᶜ :=
      ((hA q hq).2 _ le_rfl h2 h1).1
    rw [hcompl]
    have hn : n ≤ F.t := by omega
    obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.1 ((Set.ext_iff.1 (hB1 n hn) x).1 hx)
    have hK : n ≤ F.K := hn.trans F.t_le
    have hcl := cubeAround_subset_closure_interior (F := F) hF hK y hxy
    refine closure_mono ?_ hcl
    intro u hu huq
    have hmem : SeparatedSequences.truncatedMember F.scaleData F.Ω (n + 1) = F.Ω (n + 1) := by
      have : n + 1 ≤ F.scaleData.top := by
        show n + 1 ≤ F.t
        omega
      simp only [SeparatedSequences.truncatedMember, if_pos this]
    have h3 := (hB2 n hn y hy).2.2
    rw [hmem] at h3
    exact disjoint_left.1 h3 hu (Ω_antitone F (by omega) hq huq)
end Decomposition
section Placement
variable (F : SeparatedFrame L m)
theorem finite_siteAtLevel (F : SeparatedFrame L m) {j : ℤ} (hj : -(m : ℤ) ≤ j) :
    Finite (PeriodicLattice.Site L m j) :=
  (SeparatedSequence.sublattice_finite (zero_lt_L F) hj).to_subtype
variable {F}
end Placement
section DeterminingBonds
variable (F : SeparatedFrame L m)
variable {F}
def incidentBonds {n : ℕ} (z : SiteAtLevel L m F.K n) (q : Fin 4 × Bool) :
    Σ k : ℕ, BondAtLevel L m F.K k :=
  ⟨n, if q.2 then Bond.forwardFrom z q.1 else (Bond.backwardFrom z q.1).opposite⟩
end DeterminingBonds
section Norms
variable {F : SeparatedFrame L m}
end Norms
section Distance
end Distance
end SeparatedFrame.FrameProperties
end YangMills.Construction
