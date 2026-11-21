import YangMills.Construction.Lattice.BlockFieldsOnTheWholeLattice
import YangMills.Construction.Lattice.ContinuationsUnderIsometriesLieInOneComplexOrbitProof
import YangMills.Construction.Lattice.CovarianceOfComplexAveragingOfDeterminingSetsProof
import YangMills.Construction.Lattice.CubesSitesTestCubesAndLayers
import YangMills.Construction.Lattice.GaugeOnBlocksUnderIsometriesProof
import YangMills.Construction.Lattice.GluedDataUnderIsometries
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.PeriodicLattice
variable {L m : ℕ}
private theorem exists_partitionCube (hC : PartitionGeometryStatement)
    (hS : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) {c I : ℤ} (hc : -(m : ℤ) ≤ c)
    (hcI : c ≤ I) (x : Site L m I) :
    ∃ Q ∈ standardCubePartition L m c, (x : FourTorus L m) ∈ Q ∧
      (∀ Q' ∈ standardCubePartition L m c, (x : FourTorus L m) ∈ Q' → Q' = Q) ∧
      (∀ X : Set (FourTorus L m), IsPartitionRegion c X →
        ((x : FourTorus L m) ∈ X ↔ Q ∈ partitionCubesIn c X)) ∧
      cubeAround x ⊆ Q ∧ ∀ n' : ℕ, refinedBlock n' x ⊆ Q := by
  obtain ⟨d, rfl⟩ : ∃ d : ℕ, I = c + d := ⟨(I - c).toNat, by omega⟩
  obtain ⟨-, Q, hQ, ⟨hx, hu⟩, -, hr, hcube, hb⟩ := hC.2.1 L m hS hm c d hc x
  exact ⟨Q, hQ, hx, hu, hr, hcube, hb⟩
private theorem isPartitionRegion_mono (hC : PartitionGeometryStatement)
    (hS : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) {c c' : ℤ}
    (hc : -(m : ℤ) ≤ c) (h : c ≤ c') {X : Set (FourTorus L m)} (hX : IsPartitionRegion c X) :
    IsPartitionRegion c' X :=
  (hC.1 L m hS hm c c' hc h).2.2 X hX
private theorem isPartitionRegion_peel (c : ℤ) (X : Set (FourTorus L m)) :
    IsPartitionRegion c (peelCubeLayer c X) :=
  ⟨_, fun _ hQ => hQ.1.1, rfl⟩
private theorem peelCubeLayer_subset (c : ℤ) (X : Set (FourTorus L m)) :
    peelCubeLayer c X ⊆ X :=
  sUnion_subset fun _ hQ => hQ.1.2
private theorem doubleInterior_eq (K n j : ℕ) (W : Set (FourTorus L m)) :
    doubleInterior K n j W =
      peelCubeLayer (scaledCubeIndex K j n) (peelCubeLayer (scaledCubeIndex K j n) W) := rfl
private theorem isPartitionRegion_doubleInterior (K n j : ℕ) (W : Set (FourTorus L m)) :
    IsPartitionRegion (scaledCubeIndex K j n) (doubleInterior K n j W) := by
  rw [doubleInterior_eq]; exact isPartitionRegion_peel _ _
private theorem doubleInterior_subset (K n j : ℕ) (W : Set (FourTorus L m)) :
    doubleInterior K n j W ⊆ W := by
  rw [doubleInterior_eq]
  exact (peelCubeLayer_subset _ _).trans (peelCubeLayer_subset _ _)
private theorem mem_cubeMeet_iff (hC : PartitionGeometryStatement)
    (hS : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) {K : ℕ}
    {A B : Set (FourTorus L m)} (hA : IsPartitionRegion (levelDepth K 0) A)
    (hB : IsPartitionRegion (levelDepth K 0) B) (x : SiteAtLevel L m K 0) :
    (x : FourTorus L m) ∈ cubeMeet K A B ↔
      (x : FourTorus L m) ∈ A ∧ (x : FourTorus L m) ∈ B := by
  have hK : -(m : ℤ) ≤ levelDepth K 0 := by simp only [levelDepth]; omega
  obtain ⟨Q, -, hxQ, -, hr, -, -⟩ := exists_partitionCube hC hS hm hK le_rfl x
  constructor
  · rintro ⟨Q', ⟨hQA, hQB⟩, hxQ'⟩
    exact ⟨hQA.2 hxQ', hQB.2 hxQ'⟩
  · rintro ⟨hxA, hxB⟩
    exact ⟨Q, ⟨(hr A hA).1 hxA, (hr B hB).1 hxB⟩, hxQ⟩
private theorem mem_cubeDiff_iff (hC : PartitionGeometryStatement)
    (hS : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) {K : ℕ} {c : ℤ}
    (hc : -(m : ℤ) ≤ c) (hcK : c ≤ levelDepth K 0) {A B : Set (FourTorus L m)}
    (hA : IsPartitionRegion c A) (hB : IsPartitionRegion c B) (x : SiteAtLevel L m K 0) :
    (x : FourTorus L m) ∈ cubeDiff c A B ↔
      (x : FourTorus L m) ∈ A ∧ (x : FourTorus L m) ∉ B := by
  obtain ⟨Q, -, hxQ, hu, hr, -, -⟩ := exists_partitionCube hC hS hm hc hcK x
  constructor
  · rintro ⟨Q', ⟨hQ'A, hnot⟩, hxQ'⟩
    obtain rfl : Q' = Q := hu Q' hQ'A.1 hxQ'
    exact ⟨hQ'A.2 hxQ', fun hxB => hnot ((hr B hB).1 hxB).2⟩
  · rintro ⟨hxA, hxB⟩
    exact ⟨Q, ⟨(hr A hA).1 hxA, fun hsub => hxB (hsub hxQ)⟩, hxQ⟩
private theorem mem_region_iff_of_mem_block (hC : PartitionGeometryStatement)
    (hS : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) {c I J : ℤ}
    (hc : -(m : ℤ) ≤ c) (hcI : c ≤ I) (hcJ : c ≤ J) {X : Set (FourTorus L m)}
    (hX : IsPartitionRegion c X) (y : Site L m J) (r : ℕ) (x : Site L m I)
    (hxy : (x : FourTorus L m) ∈ refinedBlock r y) :
    (x : FourTorus L m) ∈ X ↔ (y : FourTorus L m) ∈ X := by
  obtain ⟨Q, hQ, hyQ, -, hry, -, hby⟩ := exists_partitionCube hC hS hm hc hcJ y
  obtain ⟨Q', -, -, hux, hrx, -, -⟩ := exists_partitionCube hC hS hm hc hcI x
  obtain rfl : Q = Q' := hux Q hQ (hby r hxy)
  exact ⟨fun h => ((hrx X hX).1 h).2 hyQ, fun h => ((hry X hX).1 h).2 (hby r hxy)⟩
private theorem cubeAround_subset_of_mem (hC : PartitionGeometryStatement)
    (hS : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) {J I : ℤ}
    (hJ : -(m : ℤ) ≤ J) (hJI : J ≤ I) (y : Site L m J) (z : Site L m I)
    (hz : (z : FourTorus L m) ∈ cubeAround y) : cubeAround z ⊆ cubeAround y := by
  obtain ⟨Q, -, -, hu, -, hc, -⟩ := exists_partitionCube hC hS hm hJ hJI z
  have h : cubeAround y = Q := hu _ ⟨y, rfl⟩ hz
  rw [h]; exact hc
private theorem mem_blockAtLevel_of_mem_unitBlock (hC : PartitionGeometryStatement)
    (hS : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) {K j l : ℕ} (hj : j ≤ K)
    (hl : l + 1 ≤ j) (y : SiteAtLevel L m K j) (z : SiteAtLevel L m K (l + 1))
    (hz : (z : FourTorus L m) ∈ blockAtLevel (l + 1) y) (x : SiteAtLevel L m K l)
    (hx : (x : FourTorus L m) ∈ unitBlock z) : (x : FourTorus L m) ∈ blockAtLevel l y := by
  have hJ : -(m : ℤ) ≤ levelDepth K j := by simp only [levelDepth]; omega
  have hJI : levelDepth K j ≤ levelDepth K (l + 1) := by simp only [levelDepth]; omega
  refine ⟨cubeAround_subset_of_mem hC hS hm hJ hJI y z hz.1 hx.1, ?_⟩
  have e : levelDepth K j + ((j - l : ℕ) : ℤ) = levelDepth K l := by
    simp only [levelDepth]; omega
  show (x : FourTorus L m) ∈ sublattice L m (levelDepth K j + ((j - l : ℕ) : ℤ))
  rw [e]
  exact x.2
private theorem insideOrCovering (hLift : LiftConsistentWithAverages)
    (hS : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) {K j i : ℕ} (hK : 0 < K)
    (hj : j ≤ K) (hi : i ≤ j) (b : BondAtLevel L m K i) : InsideOrCoveringDichotomy i j b :=
  ((hLift L m K hS hm hK j hj (∅ : Set (BondAtLevel L m K j)) (fun _ hb => hb.elim) (fun _ => 1)
    (Or.inl ⟨fun _ hb => hb.elim, fun _ hb => hb.elim⟩)).1 i hi).2 b
private theorem coveredBond_eq (hLift : LiftConsistentWithAverages)
    (hS : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) {K j i : ℕ} (hK : 0 < K)
    (hj : j ≤ K) (hi : i ≤ j) (b : BondAtLevel L m K i) {c : BondAtLevel L m K j}
    (hc : CoversBond c b) : coveredBond j b = c := by
  obtain ⟨h1, h2, -⟩ := insideOrCovering hLift hS hm hK hj hi b
  have hspec : CoversBond (coveredBond j b) b :=
    Classical.epsilon_spec (p := fun c' => CoversBond c' b) ⟨c, hc⟩
  rcases h1 with h | ⟨c', -, hu⟩
  · exact (h2 ⟨h, c, hc⟩).elim
  · rw [hu _ hspec, hu _ hc]
private theorem blockFieldAtLevel_congr (hC : PartitionGeometryStatement)
    (hLift : LiftConsistentWithAverages) (hRead : BlockAverageDependsOnDoubleBlock)
    (hS : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) {K j : ℕ} (hK : 0 < K)
    (hj : j ≤ K) (U U' : BondAtLevel L m K j → Matrices.ComplexMatrix2)
    (A : Set (BondAtLevel L m K j)) (hA : ∀ c ∈ A, U c = U' c)
    (hrev : ∀ c ∈ A, c.opposite ∈ A) :
    ∀ l, l ≤ j → ∀ a : BondAtLevel L m K l, (EndsInOneBlock j a ∨ ∃ c ∈ A, CoversBond c a) →
      blockFieldAtLevel (Averaging.smoothingRadius L) l (bareLift U) a =
        blockFieldAtLevel (Averaging.smoothingRadius L) l (bareLift U') a := by
  intro l
  induction l with
  | zero =>
    intro _ a ha
    show liftToFinerLevel 0 U a = liftToFinerLevel 0 U' a
    by_cases h : EndsInOneBlock j a
    · simp only [liftToFinerLevel, if_pos h]
    · obtain ⟨c, hcA, hc⟩ := ha.resolve_left h
      simp only [liftToFinerLevel, if_neg h]
      rw [coveredBond_eq hLift hS hm hK hj (Nat.zero_le j) a hc]
      exact hA c hcA
  | succ l ih =>
    intro hl a ha
    show blockAverage (Averaging.smoothingRadius L)
        (blockFieldAtLevel (Averaging.smoothingRadius L) l (bareLift U)) a =
      blockAverage (Averaging.smoothingRadius L)
        (blockFieldAtLevel (Averaging.smoothingRadius L) l (bareLift U')) a
    refine hRead L m K l hS hm (by omega) _ a _ _ fun b hb => ih (by omega) b ?_
    have hstep := fun (y : SiteAtLevel L m K j) (z : SiteAtLevel L m K (l + 1))
      (hz : (z : FourTorus L m) ∈ blockAtLevel (l + 1) y) (x : SiteAtLevel L m K l)
      (hx : (x : FourTorus L m) ∈ unitBlock z) =>
        mem_blockAtLevel_of_mem_unitBlock hC hS hm hj hl y z hz x hx
    rcases ha with ⟨y, hyt, hyh⟩ | ⟨c, hcA, hct, hch⟩
    · left
      have key : ∀ x : SiteAtLevel L m K l, (x : FourTorus L m) ∈ bondDoubleBlock a →
          (x : FourTorus L m) ∈ blockAtLevel l y := by
        rintro x (hx | hx)
        · exact hstep y _ hyt x hx
        · exact hstep y _ hyh x hx
      exact ⟨y, key _ hb.1, key _ hb.2⟩
    · have key : ∀ x : SiteAtLevel L m K l, (x : FourTorus L m) ∈ bondDoubleBlock a →
          (x : FourTorus L m) ∈ blockAtLevel l c.source ∨
            (x : FourTorus L m) ∈ blockAtLevel l c.target := by
        rintro x (hx | hx)
        · exact Or.inl (hstep _ _ hct x hx)
        · exact Or.inr (hstep _ _ hch x hx)
      rcases key _ hb.1 with h1 | h1 <;> rcases key _ hb.2 with h2 | h2
      · exact Or.inl ⟨_, h1, h2⟩
      · exact Or.inr ⟨c, hcA, h1, h2⟩
      · exact Or.inr ⟨c.opposite, hrev c hcA, h1, h2⟩
      · exact Or.inl ⟨_, h1, h2⟩
private theorem blockFieldAtLevel_values (hC : PartitionGeometryStatement)
    (hLift : LiftConsistentWithAverages) (hRead : BlockAverageDependsOnDoubleBlock)
    (hB : BlockFieldLifts.Statement)
    (hS : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) {K j l : ℕ} (hK : 0 < K)
    (hj1 : 1 ≤ j) (hj : j ≤ K) (hl : l ≤ j) (A : Set (BondAtLevel L m K j))
    (U : BondAtLevel L m K j → Matrices.ComplexMatrix2)
    (hrev : IsReversalClosed A) (hU : IsGaugeField compactGaugeGroup A U)
    (a : BondAtLevel L m K l) :
    (EndsInOneBlock j a →
        blockFieldAtLevel (Averaging.smoothingRadius L) l (bareLift U) a = 1) ∧
      ∀ c ∈ A, CoversBond c a →
        blockFieldAtLevel (Averaging.smoothingRadius L) l (bareLift U) a = U c := by
  have hE := extendByOne_mem_compactGaugeFields hrev hU
  have hagree : ∀ c ∈ A, U c = extendByOne A U c := fun c hc => by
    simp only [extendByOne, if_pos hc]
  have hread := blockFieldAtLevel_congr hC hLift hRead hS hm hK hj U (extendByOne A U) A hagree
    hrev l hl a
  obtain ⟨p, rfl⟩ : ∃ p, j = p + 1 := ⟨j - 1, by omega⟩
  obtain ⟨heq, -, h1, h2⟩ := ((hB L m K hS hm hK).1 p hj _ hE).2.1 l hl
  constructor
  · intro h
    rw [hread (Or.inl h), ← heq]
    exact h1 a h
  · intro c hc h
    rw [hread (Or.inr ⟨c, hc, h⟩), ← heq, h2 c a h, ← hagree c hc]
section Glued
variable {K k n j : ℕ} {Ω : ℕ → Set (FourTorus L m)} {W : Set (FourTorus L m)}
private theorem gluedChain_zero (hC : PartitionGeometryStatement)
    (hS : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m)
    (hJ : IsGluableRegion K k n j Ω W) : gluedChain K n j Ω W 0 = W := by
  obtain ⟨-, -, ⟨hform, hWr⟩, hWΩ, -, -⟩ := hJ
  have h1 : -(m : ℤ) ≤ scaledCubeIndex K j n := by
    simp only [scaledCubeIndex, levelDepth]; omega
  have hW0 : IsPartitionRegion (scaledCubeIndex K 0 n) W :=
    isPartitionRegion_mono hC hS hm h1 (by simp only [scaledCubeIndex, levelDepth]; omega) hWr
  have hBK : IsPartitionRegion (levelDepth K 0) (doubleInterior K n j W) :=
    isPartitionRegion_mono hC hS hm h1 (by simp only [scaledCubeIndex, levelDepth]; omega)
      (isPartitionRegion_doubleInterior K n j W)
  have hBW := doubleInterior_subset K n j W
  unfold gluedChain
  rw [if_pos (Nat.zero_le j)]
  apply Subset.antisymm
  · apply union_subset
    · rintro p ⟨Q, ⟨-, hQ⟩, hp⟩
      exact hBW (hQ.2 hp)
    · rintro p ⟨Q, ⟨hQ, -⟩, hp⟩
      exact hQ.2 hp
  · intro p hp
    obtain ⟨C, hCsub, hWC⟩ := hW0
    rw [hWC] at hp
    obtain ⟨Q, hQC, hpQ⟩ := hp
    have hQW : Q ⊆ W := by rw [hWC]; exact subset_sUnion_of_mem hQC
    by_cases hQB : Q ⊆ doubleInterior K n j W
    · left
      obtain ⟨D, hD, hBD⟩ := hBK
      have hpB := hQB hpQ
      rw [hBD] at hpB
      obtain ⟨Q', hQ'D, hpQ'⟩ := hpB
      have hQ'B : Q' ⊆ doubleInterior K n j W := by rw [hBD]; exact subset_sUnion_of_mem hQ'D
      exact ⟨Q', ⟨⟨hD hQ'D, (hQ'B.trans hBW).trans hWΩ⟩, ⟨hD hQ'D, hQ'B⟩⟩, hpQ'⟩
    · right
      exact ⟨Q, ⟨⟨hCsub hQC, hQW⟩, hQB⟩, hpQ⟩
private theorem shrinkingTower_isPartitionRegion {W : Set (FourTorus L m)}
    (hW : IsPartitionRegion (scaledCubeIndex K 0 n) W) (i : ℕ) :
    IsPartitionRegion (scaledCubeIndex K i n) (shrinkingTower K n 0 W i) := by
  cases i with
  | zero => exact hW
  | succ p =>
    refine ⟨_, ?_, rfl⟩
    rintro Q ⟨⟨-, hQ⟩, -⟩
    simpa using hQ
private theorem mem_gluedChain_iff (hC : PartitionGeometryStatement)
    (hS : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m)
    (hJ : IsGluableRegion K k n j Ω W) {i : ℕ} (hi : i ≤ k) (x : SiteAtLevel L m K 0) :
    (x : FourTorus L m) ∈ gluedChain K n j Ω W i ↔
      ((x : FourTorus L m) ∈ Ω i ∧ (x : FourTorus L m) ∈ doubleInterior K n j W) ∨
      (i ≤ j ∧ (x : FourTorus L m) ∈ shrinkingTower K n 0 W i ∧
        (x : FourTorus L m) ∉ doubleInterior K n j W) := by
  obtain ⟨⟨hkK, -, hdet⟩, -, ⟨hform, hWr⟩, -, -, -⟩ := hJ
  have h1 : -(m : ℤ) ≤ scaledCubeIndex K j n := by
    simp only [scaledCubeIndex, levelDepth]; omega
  have hBK : IsPartitionRegion (levelDepth K 0) (doubleInterior K n j W) :=
    isPartitionRegion_mono hC hS hm h1 (by simp only [scaledCubeIndex, levelDepth]; omega)
      (isPartitionRegion_doubleInterior K n j W)
  have hΩK : IsPartitionRegion (levelDepth K 0) (Ω i) := by
    obtain ⟨c', hc', hc'i, hr⟩ := hdet i hi
    exact isPartitionRegion_mono hC hS hm hc' (hc'i.trans (by simp only [levelDepth]; omega)) hr
  unfold gluedChain
  by_cases hij : i ≤ j
  · have hi1 : -(m : ℤ) ≤ scaledCubeIndex K i n := by
      simp only [scaledCubeIndex, levelDepth]; omega
    have hiK : scaledCubeIndex K i n ≤ levelDepth K 0 := by
      simp only [scaledCubeIndex, levelDepth]; omega
    have hW0 : IsPartitionRegion (scaledCubeIndex K 0 n) W :=
      isPartitionRegion_mono hC hS hm h1 (by simp only [scaledCubeIndex, levelDepth]; omega) hWr
    have hT := shrinkingTower_isPartitionRegion hW0 i
    have hBi : IsPartitionRegion (scaledCubeIndex K i n) (doubleInterior K n j W) :=
      isPartitionRegion_mono hC hS hm h1 (by simp only [scaledCubeIndex, levelDepth]; omega)
        (isPartitionRegion_doubleInterior K n j W)
    rw [if_pos hij, mem_union, mem_cubeMeet_iff hC hS hm hΩK hBK x,
      mem_cubeDiff_iff hC hS hm hi1 hiK hT hBi x]
    tauto
  · rw [if_neg hij, mem_cubeMeet_iff hC hS hm hΩK hBK x]
    tauto
private def siteAtZero (hL : 0 < L) {q : ℕ} (x : SiteAtLevel L m K q) : SiteAtLevel L m K 0 :=
  ⟨x, sublattice_mono hL m (by simp only [levelDepth]; omega) x.2⟩
private theorem chain_antitone (hdec : ∀ q < k, Ω (q + 1) ⊆ Ω q) {p q : ℕ} (hpq : p ≤ q)
    (hq : q ≤ k) : Ω q ⊆ Ω p := by
  induction q, hpq using Nat.le_induction with
  | base => exact Subset.rfl
  | succ q hpq ih => exact (hdec q (by omega)).trans (ih (by omega))
private theorem mem_annulusSites {i : ℕ} (hik : i ≤ k) (e : SiteAtLevel L m K i)
    (h1 : (e : FourTorus L m) ∈ Ω i) (h2 : i < k → (e : FourTorus L m) ∉ Ω (i + 1)) :
    e ∈ annulusSites K k Ω i := by
  by_cases hlt : i < k
  · simp only [annulusSites, if_pos hlt]
    exact ⟨h1, h2 hlt⟩
  · obtain rfl : i = k := by omega
    simp only [annulusSites, lt_irrefl, if_false]
    exact h1
private theorem mem_of_mem_annulusSites {i : ℕ} (hik : i ≤ k) {e : SiteAtLevel L m K i}
    (he : e ∈ annulusSites K k Ω i) : (e : FourTorus L m) ∈ Ω i := by apply _root_.YangMills.Construction.PeriodicLattice.BlockwiseGauge.mem_of_mem_annulusSites <;> assumption
private theorem inactive_glued_bond (hC : PartitionGeometryStatement)
    (hLift : LiftConsistentWithAverages)
    (hS : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) (hK : 0 < K)
    (hJ : IsGluableRegion K k n j Ω W) {i : ℕ} (hik : i ≤ k) {b : BondAtLevel L m K i}
    (hb : b ∈ activeBondsAt K k (gluedChain K n j Ω W) i)
    (hnot : b ∉ activeBondsAt K k Ω i) :
    i < j ∧ (EndsInOneBlock j b ∨ ∃ c ∈ activeBondsAt K k Ω j, CoversBond c b) := by
  have hL : 0 < L := by have := hS.2; omega
  have h0 := gluedChain_zero hC hS hm hJ
  obtain ⟨⟨hkK, hdec, hdet⟩, hjk, ⟨hform, hWr⟩, hWΩ, hmeet, hlast⟩ := hJ
  have hJ' : IsGluableRegion K k n j Ω W :=
    ⟨⟨hkK, hdec, hdet⟩, hjk, ⟨hform, hWr⟩, hWΩ, hmeet, hlast⟩
  have hjK : j ≤ K := hjk.trans hkK
  have h1 : -(m : ℤ) ≤ scaledCubeIndex K j n := by
    simp only [scaledCubeIndex, levelDepth]; omega
  obtain ⟨hΓ', hnotin⟩ := hb
  have hin : b ∈ (bondsInside (gluedChain K n j Ω W 0) : Set (BondAtLevel L m K i)) := hΓ'.2
  rw [h0] at hin
  have htW : (b.source : FourTorus L m) ∈ W := hin.1
  have hhW : (b.target : FourTorus L m) ∈ W := hin.2
  have hmem : ∀ {q : ℕ}, q ≤ k → ∀ e : SiteAtLevel L m K i,
      ((e : FourTorus L m) ∈ gluedChain K n j Ω W q ↔
        ((e : FourTorus L m) ∈ Ω q ∧ (e : FourTorus L m) ∈ doubleInterior K n j W) ∨
        (q ≤ j ∧ (e : FourTorus L m) ∈ shrinkingTower K n 0 W q ∧
          (e : FourTorus L m) ∉ doubleInterior K n j W)) :=
    fun hq e => mem_gluedChain_iff hC hS hm hJ' hq (siteAtZero hL e)
  have hF1 : ∀ e : SiteAtLevel L m K i, (e : FourTorus L m) ∈ W → j < k →
      (e : FourTorus L m) ∈ Ω (j + 1) → (e : FourTorus L m) ∈ doubleInterior K n j W := by
    intro e heW hlt heΩ
    have hWK : IsPartitionRegion (levelDepth K 0) W :=
      isPartitionRegion_mono hC hS hm h1 (by simp only [scaledCubeIndex, levelDepth]; omega) hWr
    have hΩK : IsPartitionRegion (levelDepth K 0) (nextMember k Ω j) := by
      obtain ⟨c', hc', hc'i, hr⟩ := hdet (j + 1) hlt
      simp only [nextMember, if_pos hlt]
      exact isPartitionRegion_mono hC hS hm hc' (hc'i.trans (by simp only [levelDepth]; omega)) hr
    refine hmeet ((mem_cubeMeet_iff hC hS hm hWK hΩK (siteAtZero hL e)).2 ⟨heW, ?_⟩)
    show (e : FourTorus L m) ∈ nextMember k Ω j
    simp only [nextMember, if_pos hlt]
    exact heΩ
  have hnext : i < k → (b.source : FourTorus L m) ∉ gluedChain K n j Ω W (i + 1) ∧
      (b.target : FourTorus L m) ∉ gluedChain K n j Ω W (i + 1) := fun hlt =>
    ⟨fun h => hnotin ⟨hlt, hΓ', Or.inl h⟩, fun h => hnotin ⟨hlt, hΓ', Or.inr h⟩⟩
  have hforce : (b.source ∈ annulusSites K k Ω i ∨ b.target ∈ annulusSites K k Ω i) →
      (i < k → (b.source : FourTorus L m) ∉ Ω (i + 1) ∧
        (b.target : FourTorus L m) ∉ Ω (i + 1)) → False := by
    intro hs hn
    refine hnot ⟨⟨hs, hWΩ htW, hWΩ hhW⟩, ?_⟩
    rintro ⟨hlt, -, h | h⟩
    · exact (hn hlt).1 h
    · exact (hn hlt).2 h
  have hij : i ≤ j := by
    by_contra hji
    have hji : j < i := by omega
    have hsite : ∀ e : SiteAtLevel L m K i, e ∈ annulusSites K k (gluedChain K n j Ω W) i →
        e ∈ annulusSites K k Ω i := by
      intro e he
      have ha := mem_of_mem_annulusSites hik he
      rcases (hmem hik e).1 ha with ⟨a1, -⟩ | ⟨h, -⟩
      · refine mem_annulusSites hik e a1 fun hlt a2 => ?_
        have hN : (e : FourTorus L m) ∉ gluedChain K n j Ω W (i + 1) := by
          simp only [annulusSites, if_pos hlt] at he
          exact he.2
        have hjk' : j < k := by omega
        have hW2 := (hmem hik e).1 ha
        rcases hW2 with ⟨-, a3⟩ | ⟨h, -⟩
        · exact hN ((hmem hlt e).2 (Or.inl ⟨a2, a3⟩))
        · omega
      · omega
    refine hforce (hΓ'.1.imp (hsite _) (hsite _)) fun hlt => ?_
    have hjk' : j < k := by omega
    have hsub : Ω (i + 1) ⊆ Ω (j + 1) := chain_antitone hdec (by omega) hlt
    exact ⟨fun h => (hnext hlt).1 ((hmem hlt _).2
        (Or.inl ⟨h, hF1 _ htW hjk' (hsub h)⟩)),
      fun h => (hnext hlt).2 ((hmem hlt _).2 (Or.inl ⟨h, hF1 _ hhW hjk' (hsub h)⟩))⟩
  have hC1 : ∀ e : SiteAtLevel L m K i, (e : FourTorus L m) ∈ W →
      (i < k → (e : FourTorus L m) ∉ gluedChain K n j Ω W (i + 1)) →
      j < k → (e : FourTorus L m) ∉ Ω (j + 1) := by
    intro e heW hN hlt heΩ
    have hik' : i < k := by omega
    exact hN hik' ((hmem hik' e).2
      (Or.inl ⟨chain_antitone hdec (by omega) hlt heΩ, hF1 e heW hlt heΩ⟩))
  have hC1t := hC1 _ htW fun hlt => (hnext hlt).1
  have hC1h := hC1 _ hhW fun hlt => (hnext hlt).2
  have hC2 : (b.source : FourTorus L m) ∈ Ω j ∨ (b.target : FourTorus L m) ∈ Ω j := by
    by_contra hcon
    rw [not_or] at hcon
    have hW2 : ∀ e : SiteAtLevel L m K i, (e : FourTorus L m) ∈ W →
        (e : FourTorus L m) ∉ Ω j → (e : FourTorus L m) ∈ doubleInterior K n j W :=
      fun e heW he => (hlast heW).resolve_left he
    have ht2 := hW2 _ htW hcon.1
    have hh2 := hW2 _ hhW hcon.2
    have hout : i < k → (b.source : FourTorus L m) ∉ Ω (i + 1) ∧
        (b.target : FourTorus L m) ∉ Ω (i + 1) :=
      fun hlt => ⟨fun h => (hnext hlt).1 ((hmem hlt _).2 (Or.inl ⟨h, ht2⟩)),
        fun h => (hnext hlt).2 ((hmem hlt _).2 (Or.inl ⟨h, hh2⟩))⟩
    have hΩi : ∀ e : SiteAtLevel L m K i, (e : FourTorus L m) ∈ doubleInterior K n j W →
        e ∈ annulusSites K k (gluedChain K n j Ω W) i → (e : FourTorus L m) ∈ Ω i := by
      intro e he2 he
      rcases (hmem hik e).1 (mem_of_mem_annulusSites hik he) with ⟨a1, -⟩ | ⟨-, -, a3⟩
      · exact a1
      · exact (a3 he2).elim
    refine hforce ?_ hout
    rcases hΓ'.1 with h | h
    · exact Or.inl (mem_annulusSites hik _ (hΩi _ ht2 h) fun hlt => (hout hlt).1)
    · exact Or.inr (mem_annulusSites hik _ (hΩi _ hh2 h) fun hlt => (hout hlt).2)
  rcases hij.eq_or_lt with rfl | hlt
  · exfalso
    refine hforce ?_ fun hlt => ⟨hC1t hlt, hC1h hlt⟩
    rcases hC2 with h | h
    · exact Or.inl (mem_annulusSites hik _ h hC1t)
    · exact Or.inr (mem_annulusSites hik _ h hC1h)
  refine ⟨hlt, ?_⟩
  rcases (insideOrCovering hLift hS hm hK hjK hij b).1 with hblk | ⟨c, hc, -⟩
  · exact Or.inl hblk
  refine Or.inr ⟨c, ?_, hc⟩
  have hdi : levelDepth K j ≤ levelDepth K i := by simp only [levelDepth]; omega
  have hend : ∀ {X : Set (FourTorus L m)} {a : ℤ}, -(m : ℤ) ≤ a → a ≤ levelDepth K j →
      IsPartitionRegion a X →
      ((b.source : FourTorus L m) ∈ X ↔ (c.source : FourTorus L m) ∈ X) ∧
      ((b.target : FourTorus L m) ∈ X ↔ (c.target : FourTorus L m) ∈ X) := fun ha haj hX =>
    ⟨mem_region_iff_of_mem_block hC hS hm ha (haj.trans hdi) haj hX c.source _ b.source hc.1,
      mem_region_iff_of_mem_block hC hS hm ha (haj.trans hdi) haj hX c.target _ b.target hc.2⟩
  have hW := hend h1 (by simp only [scaledCubeIndex, levelDepth]; omega) hWr
  obtain ⟨a, ha, haj, hra⟩ := hdet j hjk
  have hΩj := hend ha haj hra
  have hnext' : j < k → (c.source : FourTorus L m) ∉ Ω (j + 1) ∧
      (c.target : FourTorus L m) ∉ Ω (j + 1) := by
    intro hlt'
    obtain ⟨a', ha', haj', hra'⟩ := hdet (j + 1) hlt'
    have hΩn := hend ha' (haj'.trans (by simp only [levelDepth]; omega)) hra'
    exact ⟨fun h => hC1t hlt' (hΩn.1.2 h), fun h => hC1h hlt' (hΩn.2.2 h)⟩
  refine ⟨⟨?_, hWΩ (hW.1.1 htW), hWΩ (hW.2.1 hhW)⟩, ?_⟩
  · rcases hC2 with h | h
    · exact Or.inl (mem_annulusSites hjk _ (hΩj.1.1 h) fun hlt' => (hnext' hlt').1)
    · exact Or.inr (mem_annulusSites hjk _ (hΩj.2.1 h) fun hlt' => (hnext' hlt').2)
  · rintro ⟨hlt', -, h | h⟩
    · exact (hnext' hlt').1 h
    · exact (hnext' hlt').2 h
end Glued
private theorem bondPreimage_bondImage {j : ℤ} {σ : FourTorus L m ≃ FourTorus L m}
    (h : PreservesCells σ j) (b : Bond L m j) :
    bondPreimage σ (bondImage σ b) = b := by apply _root_.YangMills.Construction.PeriodicLattice.ComplexDeterminingAveragingCovariance.bondPreimage_bondImage <;> assumption
private theorem siteImage_mem_blockAtLevel {K j q : ℕ} {σ : FourTorus L m ≃ FourTorus L m}
    (hsq : PreservesCells σ (levelDepth K q))
    (hblk : IsometryInvariance.MapsBlocks σ (levelDepth K j))
    (x : SiteAtLevel L m K q) (y : SiteAtLevel L m K j)
    (h : (x : FourTorus L m) ∈ blockAtLevel q y) :
    ((siteImage σ x : SiteAtLevel L m K q) : FourTorus L m) ∈
      blockAtLevel q (siteImage σ y : SiteAtLevel L m K j) := by
  show _ ∈ refinedBlock (j - q) (sitePreimage σ.symm y)
  rw [← hblk (j - q) y, hsq.1 x]
  exact ⟨x, h, rfl⟩
private theorem endsInOneBlock_bondImage {K j q : ℕ} {σ : FourTorus L m ≃ FourTorus L m}
    (hsq : PreservesCells σ (levelDepth K q))
    (hblk : IsometryInvariance.MapsBlocks σ (levelDepth K j))
    {b : BondAtLevel L m K q} (h : EndsInOneBlock j b) : EndsInOneBlock j (bondImage σ b) := by
  obtain ⟨y, h1, h2⟩ := h
  refine ⟨siteImage σ y, ?_, ?_⟩
  · rw [(hsq.2.2.2.1 b).1]
    exact siteImage_mem_blockAtLevel hsq hblk _ y h1
  · rw [(hsq.2.2.2.1 b).2]
    exact siteImage_mem_blockAtLevel hsq hblk _ y h2
private theorem coversBond_bondImage {K j q : ℕ} {σ : FourTorus L m ≃ FourTorus L m}
    (hsq : PreservesCells σ (levelDepth K q))
    (hsj : PreservesCells σ (levelDepth K j))
    (hblk : IsometryInvariance.MapsBlocks σ (levelDepth K j))
    {b : BondAtLevel L m K q} {c : BondAtLevel L m K j} (h : CoversBond c b) :
    CoversBond (bondImage σ c) (bondImage σ b) := by
  constructor
  · rw [(hsq.2.2.2.1 b).1, (hsj.2.2.2.1 c).1]
    exact siteImage_mem_blockAtLevel hsq hblk _ _ h.1
  · rw [(hsq.2.2.2.1 b).2, (hsj.2.2.2.1 c).2]
    exact siteImage_mem_blockAtLevel hsq hblk _ _ h.2
private theorem activeBondsAt_reversalClosed (K k : ℕ) (Ω : ℕ → Set (FourTorus L m)) (j : ℕ) :
    IsReversalClosed (activeBondsAt K k Ω j) := by apply _root_.YangMills.Construction.PeriodicLattice.ContinuationOrbits.activeBondsAt_reversalClosed <;> assumption
theorem gluedDataEquivariant_holds (hC : PartitionGeometryStatement)
    (hLift : LiftConsistentWithAverages)
    (hRead : BlockAverageDependsOnDoubleBlock)
    (hB : BlockFieldLifts.Statement)
    (hBl : IsometryInvariance.InvariantUnderIsometries)
    (hObj : IsometryPreservesChainObjects)
    (hSites : IsometriesPreserveCells) :
    GluedDataEquivariant := by
  intro L m K k n j i σ Ω W U hS hm hi hσ hΩ hij hset
  obtain ⟨hk1, hJ, hU⟩ := hset
  refine ⟨gluedChain_zero hC hS hm hJ, ?_⟩
  rintro ⟨q, b⟩ hq
  have hkK : k ≤ K := hJ.1.1
  have hjk : j ≤ k := hJ.2.1
  have hK : 0 < K := by omega
  have hqk : q ≤ k := hq.1.1
  have hdepth : ∀ p ≤ k, i ≤ levelDepth K p := fun p hp => by
    obtain ⟨a, h1, h2, -⟩ := hΩ.2.2 p hp
    exact h1.trans h2
  obtain ⟨-, -, -, -, -, -, -, -, hforce, -⟩ :=
    hObj L m i σ hS hm hi hσ K k Ω (imageChain σ Ω) hdepth (fun _ _ => rfl)
  have hsq := hSites L m i (levelDepth K q) σ hS hm hi hσ (hdepth q hqk)
  have hinj : Function.Injective (bondImage σ : BondAtLevel L m K q → BondAtLevel L m K q) :=
    hsq.2.2.1.1
  show gluedBoundaryData K k j (imageChain σ Ω) (datumImage σ U) q (bondImage σ b) =
    gluedBoundaryData K k j Ω U q b
  by_cases hb : b ∈ activeBondsAt K k Ω q
  · have hb' : bondImage σ b ∈ activeBondsAt K k (imageChain σ Ω) q := by
      rw [hforce q hqk]
      exact ⟨b, hb, rfl⟩
    simp only [gluedBoundaryData, if_pos hb, if_pos hb']
    show U q (bondPreimage σ (bondImage σ b)) = U q b
    rw [bondPreimage_bondImage hsq]
  · have hb' : bondImage σ b ∉ activeBondsAt K k (imageChain σ Ω) q := by
      rw [hforce q hqk]
      rintro ⟨b', hb'', he⟩
      exact hb (hinj he ▸ hb'')
    obtain ⟨hlt, hdom⟩ := inactive_glued_bond hC hLift hS hm hK hJ hqk (b := b)
      ⟨hq.1.2, hq.2⟩ hb
    have hsj := hSites L m i (levelDepth K j) σ hS hm hi hσ (hdepth j hjk)
    have hblk : IsometryInvariance.MapsBlocks σ (levelDepth K j) :=
      ((hBl L m hS hm i hi σ hσ).1 (levelDepth K j) (hdepth j hjk)).1
    have hpull := bondPreimage_bondImage hsj
    have hjK : j ≤ K := hjk.trans hkK
    have hcfg : IsGaugeField compactGaugeGroup (activeBondsAt K k Ω j) (U j) := by
      have hin : ∀ c ∈ activeBondsAt K k Ω j,
          (⟨j, c⟩ : Σ q : ℕ, BondAtLevel L m K q) ∈ activeBondSet K k Ω :=
        fun c hc => ⟨⟨hjk, hc.1⟩, hc.2⟩
      exact ⟨fun c hc => (hU _ (hin c hc)).1,
        fun c hc => (hU _ (hin c hc)).2 (hin _ (activeBondsAt_reversalClosed K k Ω j c hc))⟩
    have hcfg' : IsGaugeField compactGaugeGroup (activeBondsAt K k (imageChain σ Ω) j)
        (datumImage σ U j) := by
      rw [hforce j hjk]
      constructor
      · rintro _ ⟨c, hc, rfl⟩
        show U j (bondPreimage σ (bondImage σ c)) ∈ compactGaugeGroup
        rw [hpull]
        exact hcfg.1 c hc
      · rintro _ ⟨c, hc, rfl⟩
        show U j (bondPreimage σ (bondImage σ c).opposite) =
          (U j (bondPreimage σ (bondImage σ c)))⁻¹
        rw [← hsj.2.2.2.2.1 c, hpull, hpull]
        exact hcfg.2 c hc
    have hv := blockFieldAtLevel_values hC hLift hRead hB hS hm hK (by omega) hjK hlt.le _ (U j)
      (activeBondsAt_reversalClosed K k Ω j) hcfg b
    have hv' := blockFieldAtLevel_values hC hLift hRead hB hS hm hK (by omega) hjK hlt.le _
      (datumImage σ U j) (activeBondsAt_reversalClosed K k (imageChain σ Ω) j) hcfg'
      (bondImage σ b)
    simp only [gluedBoundaryData, if_neg hb, if_neg hb', familyMemberLift, averagedLift]
    rcases hdom with hin | ⟨c, hc, hover⟩
    · rw [hv.1 hin, hv'.1 (endsInOneBlock_bondImage hsq hblk hin)]
    · have hc' : bondImage σ c ∈ activeBondsAt K k (imageChain σ Ω) j := by
        rw [hforce j hjk]
        exact ⟨c, hc, rfl⟩
      rw [hv.2 c hc hover, hv'.2 _ hc' (coversBond_bondImage hsq hsj hblk hover)]
      show U j (bondPreimage σ (bondImage σ c)) = U j c
      rw [hpull]
end YangMills.Construction.PeriodicLattice
