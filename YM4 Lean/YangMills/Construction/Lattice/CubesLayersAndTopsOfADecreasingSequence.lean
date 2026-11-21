import YangMills.Construction.Lattice.SeparatedSequencesIndexSetsPositionsAndSeminorms
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Set PeriodicLattice
namespace SeparatedSequences
variable {L m : ℕ}
structure IsAntitoneBlockUnion (S : ScaleData) (Ω : ℕ → Set (FourTorus L m)) : Prop where
  isBlockUnion : ∀ n ≤ S.top, IsBlockUnion S n (Ω n)
  antitone : ∀ n < S.top, Ω (n + 1) ⊆ Ω n
def MembersAreFinerRegions (S : ScaleData) (Ω : ℕ → Set (FourTorus L m)) : Prop :=
  ∀ n ≤ S.top, (∀ i ≤ n, IsPartitionRegion (levelDepth S.levels i) (Ω n)) ∧
    ∀ j : ℤ, S.blockPartitionIndex n ≤ j → j ≤ S.levels → -(m : ℤ) ≤ j →
      complementRegion j (Ω n) = closure (Ω n)ᶜ ∧ ∀ x, x ∉ complementRegion j (Ω n) → x ∈ Ω n
def LayersAreBlockUnions (S : ScaleData) (Ω : ℕ → Set (FourTorus L m)) : Prop :=
  (∀ j ≤ S.top, layerSet S Ω j = ⋃ y ∈ layerLatticeSites S Ω j, siteBlock S y) ∧
  (∀ j ≤ S.top, ∀ y ∈ layerLatticeSites S Ω j, siteBlock S y ⊆ layerSet S Ω j ∧
    layerSet S Ω j ⊆ Ω j ∩ complementRegion (levelDepth S.levels j) (truncatedMember S Ω (j + 1)) ∧
    Disjoint (interior (siteBlock S y)) (truncatedMember S Ω (j + 1))) ∧
  (∀ j ≤ S.top, ∀ y : SiteAtLevel L m S.levels j,
    y ∈ layerLatticeSites S Ω j ↔
      (y : FourTorus L m) ∈ Ω j ∧ (y : FourTorus L m) ∉ truncatedMember S Ω (j + 1)) ∧
  (∀ j ≤ S.top, ∀ j' ≤ S.top, j ≠ j' → ∀ y ∈ layerLatticeSites S Ω j,
    ∀ y' ∈ layerLatticeSites S Ω j', (y : FourTorus L m) ≠ y') ∧
  (∀ j ≤ S.top, ∀ j' ≤ S.top, ∀ y ∈ layerLatticeSites S Ω j, ∀ y' ∈ layerLatticeSites S Ω j',
    (y : FourTorus L m) ≠ y' → Disjoint (interior (siteBlock S y)) (interior (siteBlock S y'))) ∧
  (⋃ j ∈ Iic S.top, ⋃ y ∈ layerLatticeSites S Ω j, siteBlock S y) = Ω 0 ∧
  ∀ j ≤ S.top, ∀ y ∈ layerLatticeSites S Ω j, ∀ x ∈ interior (siteBlock S y),
    (∀ j' ≤ S.top, ∀ y' ∈ layerLatticeSites S Ω j', x ∈ siteBlock S y' →
      (y' : FourTorus L m) = y) ∧
    ∀ j' ≤ S.top, x ∈ layerSet S Ω j' → j' = j
def LayerDistIsPseudometric (S : ScaleData) (Ω : ℕ → Set (FourTorus L m)) : Prop :=
  (∀ p, layerWeightedDist S Ω p p = 0) ∧
    ∀ p q q', layerWeightedDist S Ω p q' ≤ layerWeightedDist S Ω p q + layerWeightedDist S Ω q q'
def AntitoneBlockUnionGeometry : Prop :=
  ∀ L m : ℕ, Odd L → 13 ≤ L → 0 < m → ∀ S : ScaleData, 0 < S.levels →
    (∀ Ω : ℕ → Set (FourTorus L m), IsAntitoneBlockUnion S Ω →
      MembersAreFinerRegions S Ω ∧ LayersAreBlockUnions S Ω ∧
        LayerDistIsPseudometric S Ω) ∧
    (∀ (R : ℝ) (Ω : ℕ → Set (FourTorus L m)), IsSeparatedSequence S R Ω →
      IsAntitoneBlockUnion S Ω) ∧
    ∀ (g : ℝ) (Ω : ℕ → Set (FourTorus L m)), SeparatedRegions.IsSeparatedWithGap S g Ω →
      IsAntitoneBlockUnion S Ω
end SeparatedSequences
end YangMills.Construction
end
