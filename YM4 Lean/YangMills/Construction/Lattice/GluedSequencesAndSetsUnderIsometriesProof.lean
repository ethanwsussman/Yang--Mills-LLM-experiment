import YangMills.Construction.Lattice.GluedSequencesAndSetsUnderIsometries
import YangMills.Construction.Lattice.IsometryGroupsAndTheirActionOnRegions
import YangMills.Construction.Lattice.ObjectsOfSequencesUnderIsometries
import YangMills.Construction.Lattice.TowersOfRegionsUnderIsometries
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.PeriodicLattice.GluedChainIsometries
variable {L m : ℕ}
def PreservesPartition (σ : FourTorus L m ≃ FourTorus L m) (c : ℤ) : Prop :=
  (fun Q => σ '' Q) '' standardCubePartition L m c = standardCubePartition L m c
theorem PreservesPartition.image_mem {σ : FourTorus L m ≃ FourTorus L m} {c : ℤ}
    (h : PreservesPartition σ c) {Q : Set (FourTorus L m)}
    (hQ : Q ∈ standardCubePartition L m c) :
    σ '' Q ∈ standardCubePartition L m c := by
  rw [← h]
  exact ⟨Q, hQ, rfl⟩
theorem PreservesPartition.exists_preimage {σ : FourTorus L m ≃ FourTorus L m} {c : ℤ}
    (h : PreservesPartition σ c) {Q : Set (FourTorus L m)}
    (hQ : Q ∈ standardCubePartition L m c) :
    ∃ Q' ∈ standardCubePartition L m c, σ '' Q' = Q := by
  rw [← h] at hQ
  exact hQ
theorem image_subset_image_iff_of_equiv (σ : FourTorus L m ≃ FourTorus L m)
    (A B : Set (FourTorus L m)) : σ '' A ⊆ σ '' B ↔ A ⊆ B :=
  Set.image_subset_image_iff σ.injective
theorem cubeMeet_image {σ : FourTorus L m ≃ FourTorus L m} {K : ℕ}
    (h : PreservesPartition σ (levelDepth K 0)) (X Y : Set (FourTorus L m)) :
    cubeMeet K (σ '' X) (σ '' Y) = σ '' cubeMeet K X Y := by
  ext x
  simp only [cubeMeet, partitionCubesIn, mem_sUnion, mem_inter_iff, mem_image]
  constructor
  · rintro ⟨Q, ⟨⟨hQ, hX⟩, ⟨-, hY⟩⟩, hx⟩
    obtain ⟨Q', hQ', rfl⟩ := h.exists_preimage hQ
    obtain ⟨y, hy, rfl⟩ := hx
    exact ⟨y, ⟨Q', ⟨⟨hQ', (image_subset_image_iff_of_equiv σ _ _).1 hX⟩,
      ⟨hQ', (image_subset_image_iff_of_equiv σ _ _).1 hY⟩⟩, hy⟩, rfl⟩
  · rintro ⟨y, ⟨Q, ⟨⟨hQ, hX⟩, ⟨-, hY⟩⟩, hy⟩, rfl⟩
    exact ⟨σ '' Q, ⟨⟨h.image_mem hQ, (image_subset_image_iff_of_equiv σ _ _).2 hX⟩,
      ⟨h.image_mem hQ, (image_subset_image_iff_of_equiv σ _ _).2 hY⟩⟩, mem_image_of_mem σ hy⟩
theorem cubeDiff_image {σ : FourTorus L m ≃ FourTorus L m} {c : ℤ}
    (h : PreservesPartition σ c) (A B : Set (FourTorus L m)) :
    cubeDiff c (σ '' A) (σ '' B) = σ '' cubeDiff c A B := by
  ext x
  simp only [cubeDiff, partitionCubesIn, mem_sUnion, mem_image]
  constructor
  · rintro ⟨Q, ⟨⟨hQ, hA⟩, hB⟩, hx⟩
    obtain ⟨Q', hQ', rfl⟩ := h.exists_preimage hQ
    obtain ⟨y, hy, rfl⟩ := hx
    exact ⟨y, ⟨Q', ⟨⟨hQ', (image_subset_image_iff_of_equiv σ _ _).1 hA⟩,
      fun hs => hB ((image_subset_image_iff_of_equiv σ _ _).2 hs)⟩, hy⟩, rfl⟩
  · rintro ⟨y, ⟨Q, ⟨⟨hQ, hA⟩, hB⟩, hy⟩, rfl⟩
    exact ⟨σ '' Q, ⟨⟨h.image_mem hQ, (image_subset_image_iff_of_equiv σ _ _).2 hA⟩,
      fun hs => hB ((image_subset_image_iff_of_equiv σ _ _).1 hs)⟩, mem_image_of_mem σ hy⟩
theorem nextMember_imageChain (σ : FourTorus L m ≃ FourTorus L m) (k : ℕ)
    (Ω : ℕ → Set (FourTorus L m)) (j : ℕ) :
    nextMember k (imageChain σ Ω) j = σ '' nextMember k Ω j := by
  unfold nextMember
  split_ifs
  · rfl
  · simp
theorem isometriesPreserveGluing_holds (hG : LatticeIsometryGroupActionStatement)
    (hT : IsometriesPreserveTowers)
    (hO : IsometryPreservesChainObjects) :
    IsometriesPreserveGluing := by
  intro L m i σ hL hm hi hσ K k n j Ω W hΩ hW hij
  have hc : ∀ c : ℤ, i ≤ c → MapsCellsAndCubes σ c ∧ MapsRegions σ c :=
    fun c h => (hG L m i hL hm hi).2.2.2.2 σ hσ c h
  have hp : ∀ c : ℤ, i ≤ c → PreservesPartition σ c :=
    fun c h => (hc c h).1.2.2.2.2.2.2.2.2.2
  obtain ⟨-, hjk, ⟨hnj, hWreg⟩, hW0, hmeet, hcover⟩ := hW
  obtain ⟨hkK, hdet, hreg⟩ := hΩ
  have hdepth : ∀ q ≤ k, i ≤ levelDepth K q := fun q hq => by
    obtain ⟨a, h1, h2, -⟩ := hreg q hq
    exact h1.trans h2
  have hlev : ∀ q ≤ j, i ≤ scaledCubeIndex K q n := fun q hq => by
    refine hij.trans ?_
    simp only [scaledCubeIndex, levelDepth]
    omega
  have hmeetImage : ∀ X Y : Set (FourTorus L m),
      cubeMeet K (σ '' X) (σ '' Y) = σ '' cubeMeet K X Y :=
    cubeMeet_image (hp _ (hdepth 0 (Nat.zero_le _)))
  obtain ⟨hregIff, -, -, -, hregs, -⟩ := (hc _ hij).2
  have hinterior : doubleInterior K n j (σ '' W) = σ '' doubleInterior K n j W :=
    ((hregs W hWreg).2.2.1 (-2)).symm
  have htower : ∀ q ≤ j, shrinkingTower K n 0 (σ '' W) q = σ '' shrinkingTower K n 0 W q := by
    have hlies : IsLevelRegionFrom K n 0 i W :=
      ⟨scaledCubeIndex K j n, hij, by simp only [scaledCubeIndex, levelDepth]; omega, hWreg⟩
    have := (hT L m i σ hL hm hi hσ K k n 0 0 0 j W hkK (by omega) (by omega) hlies).2.2
      (by simpa using hij)
    exact this
  have hglued : ∀ q ≤ k, gluedChain K n j (imageChain σ Ω) (σ '' W) q =
      σ '' gluedChain K n j Ω W q := by
    intro q _
    unfold gluedChain
    split_ifs with hq
    · rw [image_union, ← hmeetImage, ← cubeDiff_image (hp _ (hlev q hq)), ← htower q hq,
        hinterior]
      rfl
    · rw [← hmeetImage, hinterior]
      rfl
  obtain ⟨hd, -, -, -, -, -, -, hf, -⟩ := hO L m i σ hL hm hi hσ K k
    (gluedChain K n j Ω W) (gluedChain K n j (imageChain σ Ω) (σ '' W)) hdepth hglued
  refine ⟨⟨⟨hkK, fun q hq => image_mono (hdet.1 q hq), fun q hq => ?_⟩, hjk,
    ⟨hnj, (hregIff W).2 hWreg⟩, image_mono hW0, ?_, ?_⟩, hglued, hf, hd⟩
  · obtain ⟨a, h1, h2, h3⟩ := hreg q hq
    exact ⟨a, hi.trans h1, h2, ((hc a h1).2.1 _).2 h3⟩
  · rw [nextMember_imageChain, hmeetImage, hinterior]
    exact image_mono hmeet
  · rw [hinterior]
    show σ '' W ⊆ σ '' Ω j ∪ σ '' doubleInterior K n j W
    rw [← image_union]
    exact image_mono hcover
end YangMills.Construction.PeriodicLattice.GluedChainIsometries
