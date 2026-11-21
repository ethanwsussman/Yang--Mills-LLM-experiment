import YangMills.Construction.Lattice.LevelsPresentOnTheTorus
import YangMills.Construction.Lattice.LatticesCubesOfAStandardPartitionAndEnlargements
import YangMills.Construction.Lattice.LocalisationDomainsThroughACubeProof
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction
open Set PeriodicLattice
open CubePartitions
namespace TorusBound.CubeSides
open Setup
theorem meshSize_ne_zero (D : Setup) (i : ℤ) : meshSize D.L i ≠ 0 := by
  have hL : (0 : ℝ) < (D.L : ℝ) := by
    have := D.isAdmissible.2
    exact_mod_cast (by omega : 0 < D.L)
  exact (zpow_pos hL _).ne'
theorem neg_m_le_cubeScaleIndex {D : Setup} {j : ℕ} (h : D.LevelFits j) :
    -((D.m : ℕ) : ℤ) ≤ D.cubeScaleIndex j := by
  have h' := levelFits_iff.1 h
  simp only [cubeScaleIndex, coarseCubeIndex, scaledCubeIndex, levelDepth]
  omega
theorem levelCubeSide_eq_meshSize {D : Setup} (j : ℕ) :
    D.levelCubeSide j = meshSize D.L (D.cubeScaleIndex j) := by apply _root_.YangMills.Construction.TorusBound.Setup.cubeSide_mul_meshSize <;> assumption
theorem isPartitionRegion_of_mem_regionsBy {D : Setup} {d : DomainKind} {j : ℕ} {X : Set D.Torus}
    (h : X ∈ D.regionsBy d j) : IsPartitionRegion (D.cubeScaleIndex j) X := by apply _root_.YangMills.Construction.TorusBound.RegionsThroughCube.isPartitionRegion_of_mem_regionsBy <;> assumption
theorem finite_setOf_isPartitionRegion {D : Setup} {j : ℕ} (hf : (D.cubesAt j).Finite) :
    {X : Set D.Torus | IsPartitionRegion (D.cubeScaleIndex j) X}.Finite := by
  refine (hf.finite_subsets.image fun C : Set (Set D.Torus) => ⋃₀ C).subset ?_
  rintro X ⟨C, hC, rfl⟩
  exact ⟨C, hC, rfl⟩
theorem countsAtFittingLevel
    (h₁ : CubePartitionFacts)
    (D : Setup) {j : ℕ} (h : D.LevelFits j) : D.CountsAtFittingLevel j := by
  have hi := neg_m_le_cubeScaleIndex h
  obtain ⟨hcard, -, -, -, hbij, hfin, -, hside⟩ :=
    (h₁ D.toStandingParameters (D.cubeScaleIndex j) hi 1 (Or.inl rfl)).1
  have hratio : D.side / D.levelCubeSide j = sitesPerAxis D.L D.m (D.cubeScaleIndex j) := by
    rw [levelCubeSide_eq_meshSize, div_eq_iff (meshSize_ne_zero D _)]
    simpa [Conventions.StandingParameters.side] using hside
  refine ⟨?_, ?_, hfin, ?_, ?_⟩
  · obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ ((D.m : ℕ) : ℤ) + D.cubeScaleIndex j)
    refine ⟨2 * (D.L : ℤ) ^ k, even_two_mul _, ?_⟩
    rw [hratio, sitesPerAxis, hk]
    push_cast
    rw [zpow_natCast]
  · rintro Q ⟨y, rfl⟩
    refine ⟨y, ?_⟩
    rw [levelCubeSide_eq_meshSize]
    rfl
  · have hn : (D.cubesAt j).ncard = Nat.card (Site D.L D.m (D.cubeScaleIndex j)) := by
      change (standardCubePartition D.L D.m (D.cubeScaleIndex j)).ncard = _
      rw [← hbij.image_eq, hbij.injOn.ncard_image, ncard_univ]
    rw [hratio, ← hcard, hn]
  · intro d
    exact (finite_setOf_isPartitionRegion hfin).subset fun X hX =>
      isPartitionRegion_of_mem_regionsBy hX
theorem isLevelDomain_of_mem_regionsBy {D : Setup} {d : DomainKind} {j : ℕ} (hj : j ≤ D.K)
    (h : D.LevelFits j) {X : Set D.Torus} (hX : X ∈ D.regionsBy d j) :
    (D.levelUnitPartition hj h).IsLevelDomain X := by
  cases d
  · exact Or.inl hX.2
  · exact Or.inr hX.2
theorem spanningTreeEdgeCounts_eq (D : Setup) {j : ℕ} (hj : j ≤ D.K)
    (h : D.LevelFits j) (X : Set D.Torus) :
    D.spanningTreeEdgeCounts hj h X =
      (D.levelUnitPartition hj h).spanningTreeEdgeCounts X
        (partitionCubesIn (D.levelUnitPartition hj h).index X) := by
  ext E
  constructor
  · rintro ⟨Γ, ⟨ht, hn⟩, hm⟩
    exact ⟨Γ, ⟨ht, hm⟩, hn⟩
  · rintro ⟨Γ, ⟨ht, hm⟩, hn⟩
    exact ⟨Γ, ⟨ht, hn⟩, hm⟩
theorem standardCube_nonempty {L m : ℕ} {i : ℤ} {Q : Set (FourTorus L m)}
    (hQ : Q ∈ standardCubePartition L m i) : Q.Nonempty := by
  obtain ⟨y, rfl⟩ := hQ
  refine ⟨(y : FourTorus L m), ?_⟩
  have hz : TorusMetric.supNormVec 0 = 0 := by simp [TorusMetric.supNormVec]
  have hb : BddBelow (TorusMetric.supNormVec ''
      (TorusMetric.torusProj (torusSide L m) ⁻¹' {(0 : FourTorus L m)})) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨v, _, rfl⟩
    exact (abs_nonneg (v 0)).trans (Finset.le_sup' (fun μ => |v μ|) (Finset.mem_univ 0))
  have hm : (0 : ℝ) ∈ TorusMetric.supNormVec ''
      (TorusMetric.torusProj (torusSide L m) ⁻¹' {(0 : FourTorus L m)}) :=
    ⟨0, by funext μ; simp [TorusMetric.torusProj], hz⟩
  have hs : 0 ≤ meshSize L i := zpow_nonneg (Nat.cast_nonneg L) _
  have hsup : TorusMetric.torusSupNorm (0 : FourTorus L m) ≤ 0 := csInf_le hb hm
  change TorusMetric.torusSupNorm ((y : FourTorus L m) - (y : FourTorus L m)) ≤ meshSize L i / 2
  rw [sub_self]
  linarith
theorem allEdgesTreeAndSize (h₂ : MinimalTreeSizes)
    (D : Setup) {j : ℕ} (hj : j ≤ D.K) (h : D.LevelFits j) {d : DomainKind}
    {X : Set D.Torus} (hX : X ∈ D.regionsBy d j)
    (hne : (partitionCubesIn (D.cubeScaleIndex j) X).Nonempty) :
    D.AllEdgesTreeAndSize hj h X := by
  obtain ⟨htree, -, hsizes, -, -⟩ :=
    h₂ (D.levelUnitPartition hj h) X (isLevelDomain_of_mem_regionsBy hj h hX) hne
  obtain ⟨-, ht, -, hmeet, -⟩ := htree
  obtain ⟨⟨n, hn, hl⟩, -⟩ := hsizes
  have hl' : IsLeast (D.spanningTreeEdgeCounts hj h X) n := by
    rw [spanningTreeEdgeCounts_eq]
    exact hl
  refine ⟨ht.2, ht, ?_, ⟨n, hl'.1⟩, n, hn, hl'⟩
  intro Q hQ
  exact hmeet Q ⟨{Q}, singleton_subset_iff.2 hQ.1, (sUnion_singleton Q).symm⟩ hQ.2
    (standardCube_nonempty hQ.1)
theorem cubeSidesAndLinearSize_holds (h₁ : CubePartitionFacts)
    (h₂ : MinimalTreeSizes) : CubeSidesAndLinearSize := by
  intro D j hj
  refine ⟨⟨rfl, meshSize_le_cubeSide_mul_meshSize j⟩,
    fun h => ⟨countsAtFittingLevel h₁ D h, fun d X hX =>
      ⟨allEdgesTreeAndSize h₂ D hj h hX, ?_⟩⟩⟩
  rintro ⟨p, c, hc, hcX⟩
  obtain ⟨Q, ⟨-, Q', hQ', -⟩, -⟩ := hcX
  exact ⟨Q', hQ'⟩
end TorusBound.CubeSides
end YangMills.Construction
