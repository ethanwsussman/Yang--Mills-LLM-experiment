import YangMills.Construction.Lattice.GluedSequencesAndSetsUnderIsometriesProof
import YangMills.Construction.Lattice.LayeredGluedSequencesAndSetsUnderIsometries
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.PeriodicLattice.GluingUnderIsometries
variable {L m : ℕ} {σ : FourTorus L m ≃ FourTorus L m}
theorem setImage_injective : Function.Injective (fun X : Set (FourTorus L m) => σ '' X) :=
  Set.image_injective.2 σ.injective
theorem image_sUnion_eq (F : Set (Set (FourTorus L m))) :
    σ '' ⋃₀ F = ⋃₀ ((fun X => σ '' X) '' F) :=
  Set.image_sUnion
theorem partitionCubesIn_image {j : ℤ}
    (hcubes : (fun Q => σ '' Q) '' standardCubePartition L m j = standardCubePartition L m j)
    (X : Set (FourTorus L m)) :
    (fun Q => σ '' Q) '' partitionCubesIn j X = partitionCubesIn j (σ '' X) := by
  ext Q'
  constructor
  · rintro ⟨Q, ⟨hQ, hQX⟩, rfl⟩
    exact ⟨by rw [← hcubes]; exact mem_image_of_mem _ hQ, image_mono hQX⟩
  · rintro ⟨hQ', hsub⟩
    rw [← hcubes] at hQ'
    obtain ⟨Q, hQ, rfl⟩ := hQ'
    exact ⟨Q, ⟨hQ, (image_subset_image_iff σ.injective).1 hsub⟩, rfl⟩
theorem cubeMeet_image {K : ℕ}
    (hcubes : (fun Q => σ '' Q) '' standardCubePartition L m (levelDepth K 0) =
      standardCubePartition L m (levelDepth K 0))
    (X Y : Set (FourTorus L m)) :
    cubeMeet K (σ '' X) (σ '' Y) = σ '' cubeMeet K X Y := by apply _root_.YangMills.Construction.PeriodicLattice.GluedChainIsometries.cubeMeet_image <;> assumption
theorem regionDiff_image {j : ℤ}
    (hcubes : (fun Q => σ '' Q) '' standardCubePartition L m j = standardCubePartition L m j)
    (X Y : Set (FourTorus L m)) :
    regionDiff j (σ '' X) (σ '' Y) = σ '' regionDiff j X Y := by
  unfold regionDiff
  rw [← partitionCubesIn_image hcubes, ← partitionCubesIn_image hcubes,
    ← image_sdiff setImage_injective, image_sUnion_eq]
theorem isPartitionRegion_regionDiff (j : ℤ) (X Y : Set (FourTorus L m)) :
    IsPartitionRegion j (regionDiff j X Y) :=
  ⟨partitionCubesIn j X \ partitionCubesIn j Y, fun _ hQ => hQ.1.1, rfl⟩
theorem nextMember_imageChain (k : ℕ) (Ω : ℕ → Set (FourTorus L m)) (l : ℕ) :
    nextMember k (imageChain σ Ω) l = σ '' nextMember k Ω l := by apply _root_.YangMills.Construction.PeriodicLattice.GluedChainIsometries.nextMember_imageChain <;> assumption
theorem partsMeet_image {K n : ℕ}
    (hcubes : (fun Q => σ '' Q) '' standardCubePartition L m (scaledCubeIndex K 0 n) =
      standardCubePartition L m (scaledCubeIndex K 0 n))
    (S : Finset ℕ) (A : ℕ → Set (FourTorus L m)) :
    partsMeet K n S (fun l => σ '' A l) = σ '' partsMeet K n S A := by
  unfold partsMeet
  rw [image_sUnion_eq]
  congr 1
  ext Q'
  constructor
  · rintro ⟨hQ', hsub⟩
    have hQ'' := hQ'
    rw [← hcubes] at hQ''
    obtain ⟨Q, hQ, rfl⟩ := hQ''
    exact ⟨Q, ⟨hQ, fun l hl => (image_subset_image_iff σ.injective).1 (hsub l hl)⟩, rfl⟩
  · rintro ⟨Q, ⟨hQ, hsub⟩, rfl⟩
    exact ⟨by rw [← hcubes]; exact mem_image_of_mem _ hQ, fun l hl => image_mono (hsub l hl)⟩
theorem partsMeet_congr {K n : ℕ} {S : Finset ℕ} {A B : ℕ → Set (FourTorus L m)}
    (h : ∀ l ∈ S, A l = B l) : partsMeet K n S A = partsMeet K n S B := by
  unfold partsMeet
  congr 1
  ext Q
  simp only [mem_ofPred_eq]
  exact and_congr_right fun _ => forall₂_congr fun l hl => by rw [h l hl]
theorem doubleInterior_image {K n l : ℕ} (hmaps : MapsRegions σ (scaledCubeIndex K l n))
    {X : Set (FourTorus L m)} (hX : IsPartitionRegion (scaledCubeIndex K l n) X) :
    doubleInterior K n l (σ '' X) = σ '' doubleInterior K n l X :=
  ((hmaps.2.2.2.2.1 X hX).2.2.1 (-2)).symm
theorem partsDoubleInterior_image {K n : ℕ} {S : Finset ℕ} {A : ℕ → Set (FourTorus L m)}
    (hcubes : (fun Q => σ '' Q) '' standardCubePartition L m (scaledCubeIndex K 0 n) =
      standardCubePartition L m (scaledCubeIndex K 0 n))
    (hA : ∀ l ∈ S, MapsRegions σ (scaledCubeIndex K l n) ∧
      IsPartitionRegion (scaledCubeIndex K l n) (A l)) :
    partsDoubleInterior K n S (fun l => σ '' A l) = σ '' partsDoubleInterior K n S A := by
  unfold partsDoubleInterior
  rw [← partsMeet_image hcubes]
  exact partsMeet_congr fun l hl => doubleInterior_image (hA l hl).1 (hA l hl).2
theorem partsCollar_image {K n : ℕ} {S : Finset ℕ} {A : ℕ → Set (FourTorus L m)}
    (hdepth : (fun Q => σ '' Q) '' standardCubePartition L m (levelDepth K 0) =
      standardCubePartition L m (levelDepth K 0))
    (hcubes : (fun Q => σ '' Q) '' standardCubePartition L m (scaledCubeIndex K 0 n) =
      standardCubePartition L m (scaledCubeIndex K 0 n))
    (hA : ∀ l ∈ S, MapsRegions σ (scaledCubeIndex K l n) ∧
      IsPartitionRegion (scaledCubeIndex K l n) (A l)) :
    partsCollar K n S (fun l => σ '' A l) = σ '' partsCollar K n S A := by
  unfold partsCollar
  rw [partsDoubleInterior_image hcubes hA, partsMeet_image hcubes, regionDiff_image hdepth]
theorem isCollarComponentInShell_image {K k n : ℕ} {Ω : ℕ → Set (FourTorus L m)}
    {S : Finset ℕ} {A : ℕ → Set (FourTorus L m)}
    (hdepth : (fun Q => σ '' Q) '' standardCubePartition L m (levelDepth K 0) =
      standardCubePartition L m (levelDepth K 0))
    (hcomp : (fun C => σ '' C) '' regionComponents (levelDepth K 0) (partsCollar K n S A) =
      regionComponents (levelDepth K 0) (partsCollar K n S fun l => σ '' A l))
    (C : Set (FourTorus L m)) (l : ℕ) :
    IsCollarComponentInShell K k n (imageChain σ Ω) S (fun l => σ '' A l) (σ '' C) l ↔
      IsCollarComponentInShell K k n Ω S A C l := by
  have hmem : σ '' C ∈ (fun C => σ '' C) '' regionComponents (levelDepth K 0)
      (partsCollar K n S A) ↔ C ∈ regionComponents (levelDepth K 0) (partsCollar K n S A) :=
    setImage_injective.mem_set_image
  have hdiff : regionDiff (levelDepth K 0) (imageChain σ Ω l)
      (nextMember k (imageChain σ Ω) l) =
      σ '' regionDiff (levelDepth K 0) (Ω l) (nextMember k Ω l) := by
    rw [nextMember_imageChain]
    exact regionDiff_image hdepth _ _
  unfold IsCollarComponentInShell
  rw [← hcomp, hmem, hdiff, image_subset_image_iff σ.injective]
theorem isometriesPreserveMultiShellGluing_of
    (hgroups : LatticeIsometryGroupActionStatement)
    (htowers : IsometriesPreserveTowers)
    (hobjects : IsometryPreservesChainObjects) : IsometriesPreserveMultiShellGluing := by
  intro L m i σ hL hm hi hσ K k n Ω S A hchain hglue hidx
  have hc := fun (j : ℤ) (hj : i ≤ j) => (hgroups L m i hL hm hi).2.2.2.2 σ hσ j hj
  have hpart : ∀ j : ℤ, i ≤ j →
      (fun Q => σ '' Q) '' standardCubePartition L m j = standardCubePartition L m j :=
    fun j hj => (hc j hj).1.2.2.2.2.2.2.2.2.2
  have hmaps : ∀ j : ℤ, i ≤ j → MapsRegions σ j := fun j hj => (hc j hj).2
  obtain ⟨hkK, hdet, hwit⟩ := hchain
  obtain ⟨-, ⟨l₀, hl₀⟩, hsub, hparts, hcomps⟩ := hglue
  have hdepthLe : ∀ q ≤ k, i ≤ levelDepth K q := fun q hq => by
    obtain ⟨a, h1, h2, -⟩ := hwit q hq
    exact h1.trans h2
  have hdepth0 : i ≤ levelDepth K 0 := hdepthLe 0 (Nat.zero_le _)
  have hindex0 : i ≤ scaledCubeIndex K 0 n := by
    have h := hidx l₀ hl₀
    simp only [scaledCubeIndex, levelDepth] at h ⊢
    omega
  have hdepth := hpart _ hdepth0
  have hcubes := hpart _ hindex0
  have hA : ∀ l ∈ S, MapsRegions σ (scaledCubeIndex K l n) ∧
      IsPartitionRegion (scaledCubeIndex K l n) (A l) :=
    fun l hl => ⟨hmaps _ (hidx l hl), (hparts l hl).2.1.2⟩
  have hmeet := partsMeet_image hcubes S A
  have hinner := partsDoubleInterior_image hcubes hA
  have hcomp : (fun C => σ '' C) '' regionComponents (levelDepth K 0) (partsCollar K n S A) =
      regionComponents (levelDepth K 0) (partsCollar K n S fun l => σ '' A l) := by
    rw [partsCollar_image hdepth hcubes hA]
    exact ((hmaps _ hdepth0).2.2.2.2.1 _ (isPartitionRegion_regionDiff _ _ _)).2.1
  have hshell := fun C l =>
    isCollarComponentInShell_image (k := k) (Ω := Ω) hdepth hcomp C l
  have hsetting : IsActiveSetSetting K k (imageChain σ Ω) := by
    refine ⟨hkK, fun j hj => image_mono (hdet.1 j hj), fun j hj => ?_⟩
    obtain ⟨a, h1, h2, h3⟩ := hwit j hj
    exact ⟨a, hi.trans h1, h2, ((hmaps a h1).1 _).2 h3⟩
  have hgluable : IsMultiShellGluableRegion K k n (imageChain σ Ω) S (fun l => σ '' A l) := by
    refine ⟨hsetting, ⟨l₀, hl₀⟩, ?_, ?_, ?_⟩
    · rw [hmeet]
      exact image_mono hsub
    · intro l hl
      obtain ⟨hlk, ⟨hnl, hreg⟩, hm1, hm2⟩ := hparts l hl
      have hint := doubleInterior_image (hA l hl).1 hreg
      refine ⟨hlk, ⟨hnl, ((hA l hl).1.1 _).2 hreg⟩, ?_, ?_⟩
      · rw [hmeet, nextMember_imageChain, cubeMeet_image hdepth, hint]
        exact image_mono hm1
      · rw [hmeet, hint]
        show σ '' _ ⊆ σ '' Ω l ∪ σ '' _
        rw [← image_union]
        exact image_mono hm2
    · intro C' hC'
      rw [← hcomp] at hC'
      obtain ⟨C, hC, rfl⟩ := hC'
      obtain ⟨l, hl, hCl⟩ := hcomps C hC
      exact ⟨l, hl, (hshell C l).2 hCl⟩
  have htower : ∀ q ≤ k, i ≤ scaledCubeIndex K q n →
      shrinkingTower K n 0 (σ '' partsMeet K n S A) q =
        σ '' shrinkingTower K n 0 (partsMeet K n S A) q := by
    intro q hq hj
    have hlev : IsLevelRegionFrom K n 0 i (partsMeet K n S A) :=
      ⟨scaledCubeIndex K 0 n, hindex0, le_rfl, ⟨_, fun Q hQ => hQ.1, rfl⟩⟩
    have h := ((htowers L m i σ hL hm hi hσ) K k n 0 0 0 q _ hkK (by omega) (by omega) hlev).2.2
    exact h (by rwa [Nat.zero_add]) q le_rfl
  have hindex : ∀ {q l : ℕ}, l ∈ S → q ≤ l → i ≤ scaledCubeIndex K q n := by
    intro q l hl hql
    have h := hidx l hl
    simp only [scaledCubeIndex, levelDepth] at h ⊢
    omega
  have hglued : ∀ q ≤ k, multiShellGluedChain K k n (imageChain σ Ω) S (fun l => σ '' A l) q =
      σ '' multiShellGluedChain K k n Ω S A q := by
    intro q hq
    unfold multiShellGluedChain
    rw [hinner, hmeet, image_union, image_sUnion_eq]
    have hΩ : imageChain σ Ω q = σ '' Ω q := rfl
    rw [hΩ, cubeMeet_image hdepth]
    congr 2
    ext Q'
    constructor
    · rintro ⟨hQ', hnot, C', l, hl, hql, hC', hne⟩
      have hj := hindex hl hql
      rw [htower q hq hj, ← partitionCubesIn_image (hpart _ hj)] at hQ'
      obtain ⟨Q, hQ, rfl⟩ := hQ'
      have hC'' := hC'.1
      rw [← hcomp] at hC''
      obtain ⟨C, -, rfl⟩ := hC''
      refine ⟨Q, ⟨hQ, fun h => hnot (image_mono h), C, l, hl, hql, (hshell C l).1 hC', ?_⟩, rfl⟩
      rw [← image_sdiff σ.injective, ← image_inter σ.injective, image_nonempty] at hne
      exact hne
    · rintro ⟨Q, ⟨hQ, hnot, C, l, hl, hql, hCl, hne⟩, rfl⟩
      have hj := hindex hl hql
      refine ⟨?_, fun h => hnot ((image_subset_image_iff σ.injective).1 h), σ '' C, l, hl, hql,
        (hshell C l).2 hCl, ?_⟩
      · rw [htower q hq hj, ← partitionCubesIn_image (hpart _ hj)]
        exact mem_image_of_mem _ hQ
      · rw [← image_sdiff σ.injective, ← image_inter σ.injective, image_nonempty]
        exact hne
  have hobj := hobjects L m i σ hL hm hi hσ K k (multiShellGluedChain K k n Ω S A)
    (multiShellGluedChain K k n (imageChain σ Ω) S fun l => σ '' A l) hdepthLe hglued
  exact ⟨hmeet, hgluable, hglued, hobj.2.2.2.2.2.2.2.1, hobj.1⟩
end YangMills.Construction.PeriodicLattice.GluingUnderIsometries
