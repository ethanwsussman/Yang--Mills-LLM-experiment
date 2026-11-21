import YangMills.Construction.Lattice.CubesAndSetsOfAStepUnderIsometriesProof
import YangMills.Construction.Lattice.IsometryGroupsAndTheirActionOnRegionsProof
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.PeriodicLattice.IsometryInvariance
variable {L m : ℕ} {j : ℤ} {σ : FourTorus L m ≃ FourTorus L m}
theorem image_sUnion_eq_sUnion_familyImage (σ : FourTorus L m ≃ FourTorus L m)
    (S : Set (Set (FourTorus L m))) :
    σ '' ⋃₀ S = ⋃₀ familyImage σ S := by apply _root_.YangMills.Construction.PeriodicLattice.StepIsometry.sUnion_image_eq_familyImage <;> assumption
theorem familyImage_sdiff (σ : FourTorus L m ≃ FourTorus L m) (A B : Set (Set (FourTorus L m))) :
    familyImage σ (A \ B) = familyImage σ A \ familyImage σ B :=
  Set.image_sdiff σ.injective.image_injective A B
theorem cubesMeet_image_iff (σ : FourTorus L m ≃ FourTorus L m) (Q Q' : Set (FourTorus L m)) :
    CubesMeet (σ '' Q) (σ '' Q') ↔ CubesMeet Q Q' := by apply _root_.YangMills.Construction.PeriodicLattice.IsometryAction.cubesMeet_image_iff <;> assumption
theorem familyImage_partitionCubesIn
    (hP : familyImage σ (standardCubePartition L m j) = standardCubePartition L m j)
    (X : Set (FourTorus L m)) :
    familyImage σ (partitionCubesIn j X) = partitionCubesIn j (σ '' X) := by
  ext Q'
  constructor
  · rintro ⟨Q, ⟨hQ, hQX⟩, rfl⟩
    refine ⟨?_, image_mono hQX⟩
    rw [← hP]
    exact ⟨Q, hQ, rfl⟩
  · rintro ⟨hQ', hsub⟩
    rw [← hP] at hQ'
    obtain ⟨Q, hQ, rfl⟩ := hQ'
    exact ⟨Q, ⟨hQ, (image_subset_image_iff σ.injective).1 hsub⟩, rfl⟩
theorem image_complementRegion
    (hP : familyImage σ (standardCubePartition L m j) = standardCubePartition L m j)
    (X : Set (FourTorus L m)) : σ '' complementRegion j X = complementRegion j (σ '' X) := by
  rw [complementRegion, complementRegion, image_sUnion_eq_sUnion_familyImage, familyImage_sdiff,
    hP, familyImage_partitionCubesIn hP]
theorem image_regionDiff
    (hP : familyImage σ (standardCubePartition L m j) = standardCubePartition L m j)
    (X Y : Set (FourTorus L m)) :
    σ '' regionDiff j X Y = regionDiff j (σ '' X) (σ '' Y) := by
  rw [regionDiff, regionDiff, image_sUnion_eq_sUnion_familyImage, familyImage_sdiff,
    familyImage_partitionCubesIn hP, familyImage_partitionCubesIn hP]
theorem image_addCubeLayer
    (hP : familyImage σ (standardCubePartition L m j) = standardCubePartition L m j)
    (X : Set (FourTorus L m)) : σ '' addCubeLayer j X = addCubeLayer j (σ '' X) := by
  rw [addCubeLayer, addCubeLayer, image_sUnion_eq_sUnion_familyImage]
  congr 1
  ext Q'
  constructor
  · rintro ⟨Q, ⟨hQ, Q₀, hQ₀, ht⟩, rfl⟩
    refine ⟨?_, σ '' Q₀, ?_, (cubesMeet_image_iff σ Q Q₀).2 ht⟩
    · rw [← hP]
      exact ⟨Q, hQ, rfl⟩
    · rw [← familyImage_partitionCubesIn hP]
      exact ⟨Q₀, hQ₀, rfl⟩
  · rintro ⟨hQ', Q₁, hQ₁, ht⟩
    rw [← hP] at hQ'
    rw [← familyImage_partitionCubesIn hP] at hQ₁
    obtain ⟨Q, hQ, rfl⟩ := hQ'
    obtain ⟨Q₀, hQ₀, rfl⟩ := hQ₁
    exact ⟨Q, ⟨hQ, Q₀, hQ₀, (cubesMeet_image_iff σ Q Q₀).1 ht⟩, rfl⟩
theorem image_peelCubeLayer
    (hP : familyImage σ (standardCubePartition L m j) = standardCubePartition L m j)
    (X : Set (FourTorus L m)) : σ '' peelCubeLayer j X = peelCubeLayer j (σ '' X) := by
  rw [peelCubeLayer, peelCubeLayer, image_sUnion_eq_sUnion_familyImage]
  congr 1
  ext Q'
  constructor
  · rintro ⟨Q, ⟨hQ, hn⟩, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [← familyImage_partitionCubesIn hP]
      exact ⟨Q, hQ, rfl⟩
    · rintro ⟨Q₁, hQ₁, ht⟩
      rw [← image_complementRegion hP, ← familyImage_partitionCubesIn hP] at hQ₁
      obtain ⟨Q₂, hQ₂, rfl⟩ := hQ₁
      exact hn ⟨Q₂, hQ₂, (cubesMeet_image_iff σ Q Q₂).1 ht⟩
  · rintro ⟨hQ', hn⟩
    rw [← familyImage_partitionCubesIn hP] at hQ'
    obtain ⟨Q, hQ, rfl⟩ := hQ'
    refine ⟨Q, ⟨hQ, ?_⟩, rfl⟩
    rintro ⟨Q₂, hQ₂, ht⟩
    refine hn ⟨σ '' Q₂, ?_, (cubesMeet_image_iff σ Q Q₂).2 ht⟩
    rw [← image_complementRegion hP, ← familyImage_partitionCubesIn hP]
    exact ⟨Q₂, hQ₂, rfl⟩
theorem image_layerEnlargement
    (hP : familyImage σ (standardCubePartition L m j) = standardCubePartition L m j)
    (X : Set (FourTorus L m)) (n : ℤ) :
    σ '' layerEnlargement j X n = layerEnlargement j (σ '' X) n := by
  have hadd : Function.Semiconj (fun A : Set (FourTorus L m) => σ '' A) (addCubeLayer j)
      (addCubeLayer j) := image_addCubeLayer hP
  have hrem : Function.Semiconj (fun A : Set (FourTorus L m) => σ '' A) (peelCubeLayer j)
      (peelCubeLayer j) := image_peelCubeLayer hP
  cases n with
  | ofNat n => exact hadd.iterate_right n X
  | negSucc n => exact hrem.iterate_right (n + 1) X
theorem isometriesPreservePartitions_holds (h : LatticeIsometryGroupActionStatement) :
    IsometriesPreservePartitions := by
  intro L m i σ hL hm hi hσ j hj X
  have hP : familyImage σ (standardCubePartition L m j) = standardCubePartition L m j :=
    ((h L m i hL hm hi).2.2.2.2 σ hσ j hj).1.2.2.2.2.2.2.2.2.2
  exact ⟨familyImage_partitionCubesIn hP X, image_complementRegion hP X, image_regionDiff hP X,
    image_layerEnlargement hP X⟩
end YangMills.Construction.PeriodicLattice.IsometryInvariance
