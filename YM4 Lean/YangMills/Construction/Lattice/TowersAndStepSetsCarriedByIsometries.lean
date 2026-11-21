import YangMills.Construction.Lattice.ActionsOnFamiliesLabelsHistoriesAndOperators
import YangMills.Construction.Lattice.BackgroundAndRecursionOfAStep
import YangMills.Construction.Lattice.CovarianceOfTheAveragingMaps
import YangMills.Construction.Lattice.LocalisedBackgroundsOfSetsInForce
import Mathlib
set_option autoImplicit false
open Set YangMills.Construction.ParameterChoice
noncomputable section
namespace YangMills.Construction
namespace PeriodicLattice
variable {L m : ℕ}
def siteImage {j : ℤ} (σ : FourTorus L m ≃ FourTorus L m) (y : Site L m j) : Site L m j :=
  sitePreimage σ.symm y
def IsLevelRegionFrom (K n l : ℕ) (i : ℤ) (Ω : Set (FourTorus L m)) : Prop :=
  ∃ c : ℤ, i ≤ c ∧ c ≤ scaledCubeIndex K l n ∧ IsPartitionRegion c Ω
def PreservesTowers (i : ℤ) (σ : FourTorus L m ≃ FourTorus L m) : Prop :=
  ∀ (K k n e r l d : ℕ) (Ω : Set (FourTorus L m)), k ≤ K → r + e ≤ n → l + d ≤ k →
    IsLevelRegionFrom K n l i Ω →
      IsLevelRegionFrom K n l i (σ '' Ω) ∧
      (i ≤ scaledCubeIndex K (l + d) e →
        ∀ p ≤ d, separatedTower K e r l (σ '' Ω) p = σ '' separatedTower K e r l Ω p) ∧
      (i ≤ scaledCubeIndex K (l + d) n →
        ∀ p ≤ d, shrinkingTower K n l (σ '' Ω) p = σ '' shrinkingTower K n l Ω p)
def PreservesDeterminingSets (i : ℤ) (σ : FourTorus L m ≃ FourTorus L m) : Prop :=
  ∀ (K k : ℕ) (Ω : ℕ → Set (FourTorus L m)), IsDeterminingChainFrom K k i Ω →
    IsDeterminingChainFrom K k i (imageChain σ Ω) ∧
    determiningBondSet K k (imageChain σ Ω) = bondSetImage σ (determiningBondSet K k Ω) ∧
    (∀ q ≤ k, determiningBondsAt K k (imageChain σ Ω) q =
      bondImage σ '' determiningBondsAt K k Ω q) ∧
    (∀ q ≤ k, annulusSites K k (imageChain σ Ω) q =
      siteImage σ '' annulusSites K k Ω q) ∧
    (∀ x, IsDeterminingNode K k (imageChain σ Ω) (σ x) ↔ IsDeterminingNode K k Ω x) ∧
    (∀ b ∈ (bondsMeeting (Ω 0) : Set (BondAtLevel L m K 0)),
      localScale L k (imageChain σ Ω)
          {((bondImage σ b).source : FourTorus L m), ((bondImage σ b).target : FourTorus L m)} =
        localScale L k Ω {(b.source : FourTorus L m), (b.target : FourTorus L m)}) ∧
    ∀ p ∈ (plaquettesMeeting (Ω 0) : Set (PlaquetteAtLevel L m K 0)),
      localScale L k (imageChain σ Ω)
          ((fun x : SiteAtLevel L m K 0 => (x : FourTorus L m)) '' (plaquetteImage σ p).vertices) =
        localScale L k Ω ((fun x : SiteAtLevel L m K 0 => (x : FourTorus L m)) '' p.vertices)
def PreservesActiveSets (i : ℤ) (σ : FourTorus L m ≃ FourTorus L m) : Prop :=
  ∀ (K k : ℕ) (Ω : ℕ → Set (FourTorus L m)), IsDeterminingChainFrom K k i Ω →
    inwardPointingBonds K k (imageChain σ Ω) = bondSetImage σ (inwardPointingBonds K k Ω) ∧
    activeBondSet K k (imageChain σ Ω) = bondSetImage σ (activeBondSet K k Ω) ∧
    (∀ q ≤ k, activeBondsAt K k (imageChain σ Ω) q = bondImage σ '' activeBondsAt K k Ω q) ∧
    (∀ x, IsEndpointOf (activeBondSet K k (imageChain σ Ω)) (σ x) ↔
      IsEndpointOf (activeBondSet K k Ω) x) ∧
    ∀ F, IsReverseClosedInwardFamily K k Ω F →
      IsReverseClosedInwardFamily K k (imageChain σ Ω) (bondSetImage σ F) ∧
      determiningBondSetDiff K k (imageChain σ Ω) (bondSetImage σ F) =
        bondSetImage σ (determiningBondSetDiff K k Ω F) ∧
      (∀ q ≤ k, determiningBondsAtDiff K k (imageChain σ Ω) (bondSetImage σ F) q =
        bondImage σ '' determiningBondsAtDiff K k Ω F q) ∧
      ∀ x, IsEndpointOf (determiningBondSetDiff K k (imageChain σ Ω) (bondSetImage σ F)) (σ x) ↔
        IsEndpointOf (determiningBondSetDiff K k Ω F) x
def PreservesMinimalSets (i : ℤ) (σ : FourTorus L m ≃ FourTorus L m) : Prop :=
  ∀ (K j n : ℕ) (Ω : Set (FourTorus L m)), 1 ≤ j → j ≤ K → IsLevelRegionFrom K n 0 i Ω →
    i ≤ scaledCubeIndex K j n →
      minimalBondSet K n j (σ '' Ω) = bondSetImage σ (minimalBondSet K n j Ω) ∧
      minimalDeterminingSet K j n (σ '' Ω) =
        bondSetImage σ (minimalDeterminingSet K j n Ω)
def PreservesGluing (i : ℤ) (σ : FourTorus L m ≃ FourTorus L m) : Prop :=
  ∀ (K k n j : ℕ) (Ω : ℕ → Set (FourTorus L m)) (W : Set (FourTorus L m)),
    IsDeterminingChainFrom K k i Ω → IsGluableRegion K k n j Ω W →
    i ≤ scaledCubeIndex K j n →
      IsGluableRegion K k n j (imageChain σ Ω) (σ '' W) ∧
      (∀ q ≤ k, gluedChain K n j (imageChain σ Ω) (σ '' W) q =
        σ '' gluedChain K n j Ω W q) ∧
      gluedActiveSet K k n j (imageChain σ Ω) (σ '' W) =
        bondSetImage σ (gluedActiveSet K k n j Ω W) ∧
      determiningBondSet K k (gluedChain K n j (imageChain σ Ω) (σ '' W)) =
        bondSetImage σ (determiningBondSet K k (gluedChain K n j Ω W))
def PreservesMultiShellGluing (i : ℤ) (σ : FourTorus L m ≃ FourTorus L m) : Prop :=
  ∀ (K k n : ℕ) (Ω : ℕ → Set (FourTorus L m)) (S : Finset ℕ) (A : ℕ → Set (FourTorus L m)),
    IsDeterminingChainFrom K k i Ω → IsMultiShellGluableRegion K k n Ω S A →
    (∀ l ∈ S, i ≤ scaledCubeIndex K l n) →
      partsMeet K n S (fun l => σ '' A l) = σ '' partsMeet K n S A ∧
      IsMultiShellGluableRegion K k n (imageChain σ Ω) S (fun l => σ '' A l) ∧
      (∀ q ≤ k, multiShellGluedChain K k n (imageChain σ Ω) S (fun l => σ '' A l) q =
        σ '' multiShellGluedChain K k n Ω S A q) ∧
      multiShellGluedActiveSet K k n (imageChain σ Ω) S (fun l => σ '' A l) =
        bondSetImage σ (multiShellGluedActiveSet K k n Ω S A) ∧
      determiningBondSet K k
          (multiShellGluedChain K k n (imageChain σ Ω) S (fun l => σ '' A l)) =
        bondSetImage σ (determiningBondSet K k (multiShellGluedChain K k n Ω S A))
def PreservesCells (σ : FourTorus L m ≃ FourTorus L m) (j : ℤ) : Prop :=
  (∀ y : Site L m j, ((siteImage σ y : Site L m j) : FourTorus L m) = σ y) ∧
  Function.Bijective (siteImage σ : Site L m j → Site L m j) ∧
  Function.Bijective (bondImage σ : Bond L m j → Bond L m j) ∧
  (∀ b : Bond L m j, (bondImage σ b).source = siteImage σ b.source ∧
    (bondImage σ b).target = siteImage σ b.target) ∧
  (∀ b : Bond L m j, bondImage σ b.opposite = (bondImage σ b).opposite) ∧
  (∀ p : Plaquette L m j,
    (fun x : Site L m j => (x : FourTorus L m)) '' (plaquetteImage σ p).vertices =
      σ '' ((fun x : Site L m j => (x : FourTorus L m)) '' p.vertices)) ∧
  ∀ X : Set (FourTorus L m),
    (sitesIn (σ '' X) : Set (Site L m j)) = siteImage σ '' sitesIn X ∧
    (bondsMeeting (σ '' X) : Set (Bond L m j)) = bondImage σ '' bondsMeeting X ∧
    (bondsInside (σ '' X) : Set (Bond L m j)) = bondImage σ '' bondsInside X
def PreservesPartitionOperations (σ : FourTorus L m ≃ FourTorus L m) (j : ℤ) : Prop :=
  ∀ X : Set (FourTorus L m),
    familyImage σ (partitionCubesIn j X) = partitionCubesIn j (σ '' X) ∧
    σ '' complementRegion j X = complementRegion j (σ '' X) ∧
    (∀ Y, σ '' regionDiff j X Y = regionDiff j (σ '' X) (σ '' Y)) ∧
    ∀ n : ℤ, σ '' layerEnlargement j X n = layerEnlargement j (σ '' X) n
def PreservesChainObjects (i : ℤ) (σ : FourTorus L m ≃ FourTorus L m) : Prop :=
  ∀ (K k : ℕ) (Ω Ω' : ℕ → Set (FourTorus L m)), (∀ q ≤ k, i ≤ levelDepth K q) →
    (∀ q ≤ k, Ω' q = σ '' Ω q) →
    determiningBondSet K k Ω' = bondSetImage σ (determiningBondSet K k Ω) ∧
    (∀ q ≤ k, determiningBondsAt K k Ω' q = bondImage σ '' determiningBondsAt K k Ω q) ∧
    (∀ q ≤ k, annulusSites K k Ω' q = siteImage σ '' annulusSites K k Ω q) ∧
    (∀ x, IsDeterminingNode K k Ω' (σ x) ↔ IsDeterminingNode K k Ω x) ∧
    (∀ b : BondAtLevel L m K 0,
      localScale L k Ω'
          {((bondImage σ b).source : FourTorus L m), ((bondImage σ b).target : FourTorus L m)} =
        localScale L k Ω {(b.source : FourTorus L m), (b.target : FourTorus L m)}) ∧
    (∀ p : PlaquetteAtLevel L m K 0,
      localScale L k Ω'
          ((fun x : SiteAtLevel L m K 0 => (x : FourTorus L m)) '' (plaquetteImage σ p).vertices) =
        localScale L k Ω ((fun x : SiteAtLevel L m K 0 => (x : FourTorus L m)) '' p.vertices)) ∧
    inwardPointingBonds K k Ω' = bondSetImage σ (inwardPointingBonds K k Ω) ∧
    activeBondSet K k Ω' = bondSetImage σ (activeBondSet K k Ω) ∧
    (∀ q ≤ k, activeBondsAt K k Ω' q = bondImage σ '' activeBondsAt K k Ω q) ∧
    (∀ x, IsEndpointOf (activeBondSet K k Ω') (σ x) ↔ IsEndpointOf (activeBondSet K k Ω) x) ∧
    ∀ F, IsReverseClosedInwardFamily K k Ω F →
      IsReverseClosedInwardFamily K k Ω' (bondSetImage σ F) ∧
      determiningBondSetDiff K k Ω' (bondSetImage σ F) =
        bondSetImage σ (determiningBondSetDiff K k Ω F) ∧
      (∀ q ≤ k, determiningBondsAtDiff K k Ω' (bondSetImage σ F) q =
        bondImage σ '' determiningBondsAtDiff K k Ω F q) ∧
      ∀ x, IsEndpointOf (determiningBondSetDiff K k Ω' (bondSetImage σ F)) (σ x) ↔
        IsEndpointOf (determiningBondSetDiff K k Ω F) x
namespace CubesOfStep
def stepDataImage {K k : ℕ} (σ : FourTorus L m ≃ FourTorus L m) (D : StepData L m K k) :
    StepData L m K k :=
  ⟨imageChain σ D.domains, σ '' D.region, datumImage σ D.lowerFields,
    transportGaugeField σ D.current, transportGaugeField σ D.next⟩
variable (c : ChoiceUpToDegreeConstants) {m : ℕ} (K : ℕ) (x : ℕ → ℝ)
def PreservesStepPartitions (i : ℤ) (σ : FourTorus c.L m ≃ FourTorus c.L m) : Prop :=
  ∀ k, k < K →
    (i ≤ coarsePartitionIndex c K x k →
      familyImage σ (coarsePartition c K x k) = coarsePartition c K x k) ∧
    (i ≤ testPartitionIndex c K x k →
      familyImage σ (testPartition c K x k) = testPartition c K x k) ∧
    (i ≤ densityPartitionIndex c K x k →
      familyImage σ (densityPartition c K x k) = densityPartition c K x k)
def PreservesStepSets (i : ℤ) (σ : FourTorus c.L m ≃ FourTorus c.L m) : Prop :=
  ∀ (k : ℕ) (D : StepData c.L m K k), k < K → i ≤ levelDepth K (k + 1) →
    i ≤ coarsePartitionIndex c K x k →
    (∀ Y, IsPartitionRegion (coarsePartitionIndex c K x k) Y →
      freeBondsWithin c (stepDataImage σ D) (σ '' Y) = bondImage σ '' freeBondsWithin c D Y ∧
      freeBondsCrossing c (stepDataImage σ D) (σ '' Y) =
        bondImage σ '' freeBondsCrossing c D Y ∧
      bondCollar c (stepDataImage σ D) (σ '' Y) = bondImage σ '' bondCollar c D Y) ∧
    (∀ Z, IsPartitionRegion (coarsePartitionIndex c K x k) Z →
      rimCubes c x (stepDataImage σ D) (σ '' Z) = familyImage σ (rimCubes c x D Z)) ∧
    (∀ J, cubesMeetingBonds c x (stepDataImage σ D) (bondImage σ '' J) =
      familyImage σ (cubesMeetingBonds c x D J)) ∧
    (∀ C ⊆ coarsePartition c K x k,
      enlargedLargeFieldRegion c x (stepDataImage σ D) (familyImage σ C) =
        σ '' enlargedLargeFieldRegion c x D C) ∧
    (i ≤ testPartitionIndex c K x k → i ≤ testCollarIndex c K x k →
      ∀ R ∈ largeFieldCandidates c x D,
        σ '' R ∈ largeFieldCandidates c x (stepDataImage σ D) ∧
        checkedBonds c x (stepDataImage σ D) (σ '' R) = bondImage σ '' checkedBonds c x D R)
end CubesOfStep
end PeriodicLattice
end YangMills.Construction
