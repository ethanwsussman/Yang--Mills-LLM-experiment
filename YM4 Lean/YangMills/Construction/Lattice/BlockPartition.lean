import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Lattice.SiteCoordinates
import Mathlib
open Set
noncomputable section
namespace YangMills.Construction.PeriodicLattice
def RefinedBlockEqOffsetImage (L m : ℕ) (j : ℤ) (n : ℕ) (y : Site L m j) : Prop :=
  refinedBlock n y = (fun p => (refinedOffsetSite n y p : FourTorus L m)) '' blockOffsets L n ∧
    InjOn (fun p => (refinedOffsetSite n y p : FourTorus L m)) (blockOffsets L n) ∧
    (refinedBlock n y).ncard = L ^ (4 * n)
def RefinedBlocksPartition (L m : ℕ) (j : ℤ) (n : ℕ) : Prop :=
  (∀ y : Site L m j, (y : FourTorus L m) ∈ refinedBlock n y) ∧
    sublattice L m j ≤ sublattice L m (j + n) ∧
    Pairwise (Function.onFun Disjoint fun y : Site L m j => refinedBlock n y) ∧
    ⋃ y : Site L m j, refinedBlock n y = (sublattice L m (j + n) : Set (FourTorus L m))
def RefinedBlockOfSumOrder (L m : ℕ) (j : ℤ) (n n' : ℕ) (y : Site L m j) : Prop :=
  refinedBlock (n + n') y =
    ⋃ x : Site L m (j + n), ⋃ _ : (x : FourTorus L m) ∈ refinedBlock n y, refinedBlock n' x
def StepFromRefinedBlockSite (L m : ℕ) (j : ℤ) (n : ℕ) (y : Site L m j) : Prop :=
  ∀ p ∈ blockOffsets L n, ∀ μ : Fin 4,
    (2 * p μ < (L : ℤ) ^ n - 1 →
      ((refinedOffsetSite n y p + unitStep L m (j + n) μ : Site L m (j + n)) : FourTorus L m) ∈
        refinedBlock n y) ∧
    (2 * p μ = (L : ℤ) ^ n - 1 →
      ((refinedOffsetSite n y p + unitStep L m (j + n) μ : Site L m (j + n)) : FourTorus L m) ∈
        refinedBlock n (y + unitStep L m j μ))
def BondJoinsEndpointBlocks {L m : ℕ} {j : ℤ} (n : ℕ) (b : Bond L m (j + n)) (c : Bond L m j) :
    Prop :=
  (b.source : FourTorus L m) ∈ refinedBlock n c.source ∧
    (b.target : FourTorus L m) ∈ refinedBlock n c.target
def HasAxisAndOrientationOf {L m : ℕ} {j : ℤ} (n : ℕ) (c : Bond L m j)
    (b : Bond L m (j + n)) : Prop :=
  ∀ μ : Fin 4,
    (b.target - b.source = unitStep L m (j + n) μ → c.target - c.source = unitStep L m j μ) ∧
    (b.target - b.source = -unitStep L m (j + n) μ → c.target - c.source = -unitStep L m j μ)
def BondEndpointsInBlocks (L m : ℕ) (j : ℤ) (n : ℕ) : Prop :=
  ∀ b : Bond L m (j + n),
    (∃ y : Site L m j, (b.source : FourTorus L m) ∈ refinedBlock n y ∧
      (b.target : FourTorus L m) ∈ refinedBlock n y) ∨
    ∃ c : Bond L m j, BondJoinsEndpointBlocks n b c ∧ HasAxisAndOrientationOf n c b ∧
      ∀ c' : Bond L m j, BondJoinsEndpointBlocks n b c' → c' = c
def BlockPartition.Properties : Prop :=
  ∀ L m : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < m →
  ∀ (j : ℤ) (n n' : ℕ), -(m : ℤ) ≤ j →
    (∀ y : Site L m j, RefinedBlockEqOffsetImage L m j n y) ∧
    RefinedBlocksPartition L m j n ∧
    (∀ y : Site L m j, RefinedBlockOfSumOrder L m j n n' y) ∧
    (∀ y : Site L m j, StepFromRefinedBlockSite L m j n y) ∧
    BondEndpointsInBlocks L m j n
end YangMills.Construction.PeriodicLattice
