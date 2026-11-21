import YangMills.Construction.Lattice.BlocksAndLinearSizesUnderIsometries
import YangMills.Construction.Lattice.CubesAndSetsOfAStepUnderIsometries
import YangMills.Construction.Lattice.CubesOfSetsUnderIsometries
import YangMills.Construction.Lattice.IsometryGroupsAndTheirActionOnRegions
import YangMills.Construction.Lattice.SitesBondsAndPlaquettesOfSetsUnderIsometries
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.PeriodicLattice
namespace StepIsometry
open CubesOfStep
variable {L m : ℕ}
theorem sUnion_image_eq_familyImage (σ : FourTorus L m ≃ FourTorus L m)
    (C : Set (Set (FourTorus L m))) :
    σ '' ⋃₀ C = ⋃₀ familyImage σ C := by
  ext y
  simp only [familyImage, mem_image, mem_sUnion, exists_exists_and_eq_and]
  constructor
  · rintro ⟨p, ⟨Q, hQ, hp⟩, rfl⟩
    exact ⟨Q, hQ, p, hp, rfl⟩
  · rintro ⟨Q, hQ, p, hp, rfl⟩
    exact ⟨p, ⟨Q, hQ, hp⟩, rfl⟩
theorem nonPivotBonds_image (σ : FourTorus L m ≃ FourTorus L m) {K k : ℕ}
    (h₀ : PreservesCells σ (levelDepth K k))
    (h₁ : PreservesCells σ (levelDepth K (k + 1)))
    (hP : IsometryInvariance.MapsBondObjects σ K k)
    (X : Set (FourTorus L m)) :
    nonPivotBonds K k (σ '' X) = bondImage σ '' nonPivotBonds K k X := by
  obtain ⟨-, -, hinj, -, -, -, hX⟩ := h₀
  obtain ⟨-, -, -, -, -, -, hX₁⟩ := h₁
  have hb : (bondsMeeting (σ '' X) : Set (BondAtLevel L m K k)) = bondImage σ '' bondsMeeting X :=
    (hX X).2.1
  have hb₁ : (bondsMeeting (σ '' X) : Set (BondAtLevel L m K (k + 1))) =
      bondImage σ '' bondsMeeting X :=
    (hX₁ X).2.1
  ext b
  constructor
  · rintro ⟨hbX, hno⟩
    rw [hb] at hbX
    obtain ⟨b₀, hb₀, rfl⟩ := hbX
    refine ⟨b₀, ⟨hb₀, ?_⟩, rfl⟩
    rintro ⟨e, he, rfl⟩
    refine hno ⟨bondImage σ e, ?_, (hP e).2.2.1⟩
    rw [hb₁]
    exact mem_image_of_mem _ he
  · rintro ⟨b₀, ⟨hb₀, hno⟩, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [hb]
      exact mem_image_of_mem _ hb₀
    · rintro ⟨e, he, heq⟩
      rw [hb₁] at he
      obtain ⟨e₀, he₀, rfl⟩ := he
      exact hno ⟨e₀, he₀, hinj.1 (heq.trans (hP e₀).2.2.1.symm)⟩
section Step
variable (c : ParameterChoice.ChoiceUpToDegreeConstants) {m : ℕ} {K : ℕ} (x : ℕ → ℝ) {k : ℕ}
  (σ : FourTorus c.L m ≃ FourTorus c.L m) (D : StepData c.L m K k)
theorem shrunkDomain_stepDataImage (hC : PreservesPartitionOperations σ (coarsePartitionIndex c K x k)) :
    shrunkDomain c x (stepDataImage σ D) = σ '' shrunkDomain c x D := by
  simp only [shrunkDomain, coarseCollar]
  exact ((hC D.region).2.2.2 (-1)).symm
theorem shrunkDomainCubes_stepDataImage
    (hC : PreservesPartitionOperations σ (coarsePartitionIndex c K x k)) :
    shrunkDomainCubes c x (stepDataImage σ D) = familyImage σ (shrunkDomainCubes c x D) := by
  simp only [shrunkDomainCubes]
  rw [shrunkDomain_stepDataImage c x σ D hC, (hC _).1]
structure BondImageFacts (σ : FourTorus c.L m ≃ FourTorus c.L m) (K k : ℕ) : Prop where
  nonPivot : ∀ X : Set (FourTorus c.L m),
    nonPivotBonds K k (σ '' X) = bondImage σ '' nonPivotBonds K k X
  injective : Function.Injective (bondImage σ : BondAtLevel c.L m K k → BondAtLevel c.L m K k)
  source : ∀ b : BondAtLevel c.L m K k, ((bondImage σ b).source : FourTorus c.L m) = σ b.source
  target : ∀ b : BondAtLevel c.L m K k, ((bondImage σ b).target : FourTorus c.L m) = σ b.target
  inside : ∀ X : Set (FourTorus c.L m),
    (bondsInside (σ '' X) : Set (BondAtLevel c.L m K k)) = bondImage σ '' bondsInside X
  dist : ∀ b b' : BondAtLevel c.L m K k,
    bondSupDist K k (bondImage σ b) (bondImage σ b') = bondSupDist K k b b'
variable {c x σ}
theorem freeVariableBonds_stepDataImage (h : BondImageFacts c σ K k) :
    freeVariableBonds c (stepDataImage σ D) = bondImage σ '' freeVariableBonds c D :=
  h.nonPivot D.region
theorem freeBondsWithin_stepDataImage (h : BondImageFacts c σ K k) (Y : Set (FourTorus c.L m)) :
    freeBondsWithin c (stepDataImage σ D) (σ '' Y) =
      bondImage σ '' freeBondsWithin c D Y := by
  simp only [freeBondsWithin]
  rw [freeVariableBonds_stepDataImage D h, h.inside, image_inter h.injective]
theorem mem_freeBondsCrossing_stepDataImage (h : BondImageFacts c σ K k)
    (Y : Set (FourTorus c.L m)) (b : BondAtLevel c.L m K k) :
    bondImage σ b ∈ freeBondsCrossing c (stepDataImage σ D) (σ '' Y) ↔
      b ∈ freeBondsCrossing c D Y := by
  simp only [freeBondsCrossing, mem_ofPred_eq, freeVariableBonds_stepDataImage D h, h.source,
    h.target, σ.injective.mem_set_image, h.injective.mem_set_image]
theorem freeBondsCrossing_stepDataImage (h : BondImageFacts c σ K k) (Y : Set (FourTorus c.L m)) :
    freeBondsCrossing c (stepDataImage σ D) (σ '' Y) = bondImage σ '' freeBondsCrossing c D Y := by
  ext b
  constructor
  · intro hb
    have hf : b ∈ freeVariableBonds c (stepDataImage σ D) := hb.1
    rw [freeVariableBonds_stepDataImage D h] at hf
    obtain ⟨b₀, -, rfl⟩ := hf
    exact ⟨b₀, (mem_freeBondsCrossing_stepDataImage D h Y b₀).1 hb, rfl⟩
  · rintro ⟨b₀, hb₀, rfl⟩
    exact (mem_freeBondsCrossing_stepDataImage D h Y b₀).2 hb₀
theorem freeBondsOutside_stepDataImage (h : BondImageFacts c σ K k) (Y : Set (FourTorus c.L m)) :
    freeBondsOutside c (stepDataImage σ D) (σ '' Y) = bondImage σ '' freeBondsOutside c D Y := by
  simp only [freeBondsOutside]
  rw [freeVariableBonds_stepDataImage D h, freeBondsWithin_stepDataImage D h,
    image_sdiff h.injective]
theorem distToFreeBondsWithin_stepDataImage (h : BondImageFacts c σ K k)
    (Y : Set (FourTorus c.L m)) (b : BondAtLevel c.L m K k) :
    distToFreeBondsWithin c (stepDataImage σ D) (bondImage σ b) (σ '' Y) =
      distToFreeBondsWithin c D b Y := by
  simp only [distToFreeBondsWithin]
  rw [freeBondsWithin_stepDataImage D h, iInf_image]
  simp only [h.dist]
theorem bondCollar_stepDataImage (h : BondImageFacts c σ K k) (Y : Set (FourTorus c.L m)) :
    bondCollar c (stepDataImage σ D) (σ '' Y) = bondImage σ '' bondCollar c D Y := by
  have hset : freeBondsOutside c (stepDataImage σ D) (σ '' Y) \
      freeBondsCrossing c (stepDataImage σ D) (σ '' Y) =
      bondImage σ '' (freeBondsOutside c D Y \ freeBondsCrossing c D Y) := by
    rw [freeBondsOutside_stepDataImage D h, freeBondsCrossing_stepDataImage D h,
      image_sdiff h.injective]
  ext b
  simp only [bondCollar, mem_ofPred_eq, hset]
  constructor
  · rintro ⟨⟨b₀, hb₀, rfl⟩, hd⟩
    exact ⟨b₀, ⟨hb₀, by rwa [distToFreeBondsWithin_stepDataImage D h] at hd⟩, rfl⟩
  · rintro ⟨b₀, ⟨hb₀, hd⟩, rfl⟩
    exact ⟨⟨b₀, hb₀, rfl⟩, by rwa [distToFreeBondsWithin_stepDataImage D h]⟩
theorem rimCubes_stepDataImage (hC : PreservesPartitionOperations σ (coarsePartitionIndex c K x k))
    (Z : Set (FourTorus c.L m)) :
    rimCubes c x (stepDataImage σ D) (σ '' Z) = familyImage σ (rimCubes c x D Z) := by
  have hcube : partitionCubesIn (coarsePartitionIndex c K x k)
      (complementRegion (coarsePartitionIndex c K x k) (σ '' Z)) =
      familyImage σ
        (partitionCubesIn (coarsePartitionIndex c K x k)
          (complementRegion (coarsePartitionIndex c K x k) Z)) := by
    rw [← (hC Z).2.1, (hC _).1]
  ext Q
  simp only [rimCubes, mem_ofPred_eq, shrunkDomainCubes_stepDataImage c x σ D hC, hcube]
  constructor
  · rintro ⟨⟨Q₀, hQ₀, rfl⟩, hZ, ⟨Q', ⟨Q₁, hQ₁, rfl⟩, ht⟩⟩
    refine ⟨Q₀, ⟨hQ₀, (image_subset_image_iff σ.injective).1 hZ, Q₁, hQ₁, ?_⟩, rfl⟩
    have : σ '' Q₀ ∩ σ '' Q₁ = σ '' (Q₀ ∩ Q₁) := (image_inter σ.injective).symm
    simp only [CubesMeet, this, image_nonempty] at ht
    exact ht
  · rintro ⟨Q₀, ⟨hQ₀, hZ, Q₁, hQ₁, ht⟩, rfl⟩
    refine ⟨⟨Q₀, hQ₀, rfl⟩, image_mono hZ, σ '' Q₁, ⟨Q₁, hQ₁, rfl⟩, ?_⟩
    have : σ '' Q₀ ∩ σ '' Q₁ = σ '' (Q₀ ∩ Q₁) := (image_inter σ.injective).symm
    simp only [CubesMeet, this, image_nonempty]
    exact ht
theorem cubesMeetingBonds_stepDataImage
    (hC : PreservesPartitionOperations σ (coarsePartitionIndex c K x k))
    (h : BondImageFacts c σ K k) (J : Set (BondAtLevel c.L m K k)) :
    cubesMeetingBonds c x (stepDataImage σ D) (bondImage σ '' J) =
      familyImage σ (cubesMeetingBonds c x D J) := by
  ext Q
  simp only [cubesMeetingBonds, mem_ofPred_eq, shrunkDomainCubes_stepDataImage c x σ D hC]
  constructor
  · rintro ⟨⟨Q₀, hQ₀, rfl⟩, b', ⟨b, hb, rfl⟩, ht⟩
    refine ⟨Q₀, ⟨hQ₀, b, hb, ?_⟩, rfl⟩
    simpa only [h.source, h.target, σ.injective.mem_set_image] using ht
  · rintro ⟨Q₀, ⟨hQ₀, b, hb, ht⟩, rfl⟩
    refine ⟨⟨Q₀, hQ₀, rfl⟩, bondImage σ b, mem_image_of_mem _ hb, ?_⟩
    simpa only [h.source, h.target, σ.injective.mem_set_image] using ht
theorem enlargedLargeFieldRegion_stepDataImage
    (hC : PreservesPartitionOperations σ (coarsePartitionIndex c K x k))
    (C : Set (Set (FourTorus c.L m))) :
    enlargedLargeFieldRegion c x (stepDataImage σ D) (familyImage σ C) =
      σ '' enlargedLargeFieldRegion c x D C := by
  simp only [enlargedLargeFieldRegion, coarseCollar, image_union]
  have hD : (stepDataImage σ D).region = σ '' D.region := rfl
  rw [(hC _).2.2.2 2, (hC _).2.2.2 1, (hC D.region).2.1, sUnion_image_eq_familyImage, hD]
theorem mem_largeFieldCandidates_stepDataImage
    (hC : PreservesPartitionOperations σ (coarsePartitionIndex c K x k))
    (hT : PreservesPartitionOperations σ (testPartitionIndex c K x k)) (R : Set (FourTorus c.L m))
    (hR : R ∈ largeFieldCandidates c x D) :
    σ '' R ∈ largeFieldCandidates c x (stepDataImage σ D) := by
  obtain ⟨C, hC', rfl⟩ := hR
  refine ⟨familyImage σ C, ?_, sUnion_image_eq_familyImage σ C⟩
  rw [shrunkDomain_stepDataImage c x σ D hC, ← (hT _).1]
  exact image_mono hC'
theorem checkedBonds_stepDataImage
    (hC : PreservesPartitionOperations σ (coarsePartitionIndex c K x k))
    (hT : PreservesPartitionOperations σ (testPartitionIndex c K x k))
    (hE : PreservesPartitionOperations σ (testCollarIndex c K x k)) (h : BondImageFacts c σ K k)
    (R : Set (FourTorus c.L m)) :
    checkedBonds c x (stepDataImage σ D) (σ '' R) = bondImage σ '' checkedBonds c x D R := by
  have hcomp : complementInShrunk c x (stepDataImage σ D) (σ '' R) =
      σ '' complementInShrunk c x D R := by
    simp only [complementInShrunk]
    rw [shrunkDomain_stepDataImage c x σ D hC, (hT _).2.2.1]
  simp only [checkedBonds]
  rw [hcomp, ← (hT _).1, image_iUnion₂]
  simp only [familyImage, biUnion_image, testCollar]
  refine iUnion₂_congr fun Q _ => ?_
  rw [← (hE Q).2.2.2 2, h.nonPivot]
end Step
end StepIsometry
open StepIsometry CubesOfStep
theorem stepCubesAndSetsIsometryInvariant_of
    (hG : LatticeIsometryGroupActionStatement)
    (hB : IsometryInvariance.InvariantUnderIsometries)
    (hS : IsometriesPreserveCells)
    (hQ : IsometriesPreservePartitions) :
    StepCubesAndSetsIsometryInvariant := by
  intro c m K x i σ hL hm hi hσ
  obtain ⟨-, hdist, -, -, hcar⟩ := hG c.L m i hL hm hi
  have hpart : ∀ j : ℤ, i ≤ j → familyImage σ (standardCubePartition c.L m j) =
      standardCubePartition c.L m j := fun j hj => (hcar σ hσ j hj).1.2.2.2.2.2.2.2.2.2
  refine ⟨fun k _ => ⟨fun h => hpart _ h, fun h => hpart _ h, fun h => hpart _ h⟩, ?_⟩
  intro k D hk hd hco
  have hdk : levelDepth K k = levelDepth K (k + 1) + 1 := by
    simp only [levelDepth]
    push_cast
    ring
  have hd₀ : i ≤ levelDepth K k := by omega
  have hS₀ := hS c.L m i _ σ hL hm hi hσ hd₀
  have hS₁ := hS c.L m i _ σ hL hm hi hσ hd
  have hP := (hB c.L m hL hm i hi σ hσ).2.1 K k hk hd
  have hcar₀ := (hcar σ hσ _ hd₀).1
  have hfacts : BondImageFacts c σ K k :=
    { nonPivot := nonPivotBonds_image σ hS₀ hS₁ hP
      injective := hS₀.2.2.1.1
      source := fun b => (hcar₀.2.2.2.1 b).1
      target := fun b => (hcar₀.2.2.2.1 b).2
      inside := fun X => ((hS₀.2.2.2.2.2.2) X).2.2
      dist := fun b b' => by
        have hseg := hcar₀.2.2.2.2.1 (by omega)
        simp only [bondSupDist, setSupDistInLevelUnits, hseg]
        rw [(hdist σ hσ).1.2.2.2.1] }
  have hC := hQ c.L m i σ hL hm hi hσ _ hco
  refine ⟨fun Y _ => ⟨freeBondsWithin_stepDataImage D hfacts Y,
    freeBondsCrossing_stepDataImage D hfacts Y, bondCollar_stepDataImage D hfacts Y⟩,
    fun Z _ => rimCubes_stepDataImage D hC Z, cubesMeetingBonds_stepDataImage D hC hfacts,
    fun C _ => enlargedLargeFieldRegion_stepDataImage D hC C, fun ht hl R hR => ?_⟩
  have hT := hQ c.L m i σ hL hm hi hσ _ ht
  have hE := hQ c.L m i σ hL hm hi hσ _ hl
  exact ⟨mem_largeFieldCandidates_stepDataImage D hC hT R hR,
    checkedBonds_stepDataImage D hC hT hE hfacts R⟩
end YangMills.Construction.PeriodicLattice
