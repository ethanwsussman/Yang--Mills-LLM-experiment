import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Lattice.CubePartitionsAndRegions
import YangMills.Construction.Lattice.LevelCoordinates
import YangMills.Construction.Lattice.LevelCubesAndBlocks
import Mathlib
open Set
noncomputable section
namespace YangMills.Construction.PeriodicLattice
variable {L m K : ℕ}
def IsBlockDisplacement (j k : ℕ) (x : SiteAtLevel L m K j) (y : SiteAtLevel L m K k)
    (r : Fin 4 → ℤ) : Prop :=
  supNormVec (fun μ => (r μ : ℝ)) ≤ halfWidth L (k - j) ∧
    (x : FourTorus L m) = shiftBy L m K j y fun μ => (r μ : ℝ)
def coarseCentre (j k : ℕ) (x : SiteAtLevel L m K j) : SiteAtLevel L m K k :=
  Classical.epsilon fun y => ∃ r, IsBlockDisplacement j k x y r
def CoarseCentreProperties : Prop :=
  ∀ L m K : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < m → 0 < K →
  ∀ j k : ℕ, j ≤ k → k ≤ K →
    (∀ x : SiteAtLevel L m K j,
      (∃! p : SiteAtLevel L m K k × (Fin 4 → ℤ), IsBlockDisplacement j k x p.1 p.2) ∧
      ∀ y' : SiteAtLevel L m K k, (x : FourTorus L m) ∈ cubeAtLevel y' ↔ y' = coarseCentre j k x) ∧
    (∀ y : SiteAtLevel L m K k,
      blockAtLevel j y =
          {z | ∃ x : SiteAtLevel L m K j, (x : FourTorus L m) = z ∧ coarseCentre j k x = y} ∧
      blockAtLevel j y =
          {z | ∃ r : Fin 4 → ℤ, supNormVec (fun μ => (r μ : ℝ)) ≤ halfWidth L (k - j) ∧
            z = shiftBy L m K j y fun μ => (r μ : ℝ)}) ∧
    (∀ x : SiteAtLevel L m K j,
      ∃! y : SiteAtLevel L m K k, (x : FourTorus L m) ∈ blockAtLevel j y) ∧
    (∀ i : ℕ, j ≤ i → i ≤ k →
      (∀ x : SiteAtLevel L m K j, coarseCentre i k (coarseCentre j i x) = coarseCentre j k x) ∧
      ∀ y' : SiteAtLevel L m K i, blockAtLevel j y' ⊆ blockAtLevel j (coarseCentre i k y')) ∧
    (∀ (b : BondAtLevel L m K j) (σ : ℝ) (μ : Fin 4), (σ = 1 ∨ σ = -1) →
      (b.target : FourTorus L m) = shiftBy L m K j b.source (σ • coordVec μ) →
      coarseCentre j k b.target = coarseCentre j k b.source ∨
        ((coarseCentre j k b.target : FourTorus L m) =
            shiftBy L m K j (coarseCentre j k b.source)
              ((σ * (L : ℝ) ^ (k - j)) • coordVec μ) ∧
          coarseCentre j k b.target ≠ coarseCentre j k b.source ∧
          ∃ c : BondAtLevel L m K k, c.source = coarseCentre j k b.source ∧
            c.target = coarseCentre j k b.target ∧
            (c.IsPositivelyOriented ↔ b.IsPositivelyOriented) ∧
            ∀ c' : BondAtLevel L m K k, (b.source : FourTorus L m) ∈ blockAtLevel j c'.source →
              (b.target : FourTorus L m) ∈ blockAtLevel j c'.target → c' = c)) ∧
    ∀ X : Set (FourTorus L m), IsPartitionRegion (levelDepth K k) X →
      ∀ x : SiteAtLevel L m K j, (x : FourTorus L m) ∈ X →
        cubeAtLevel (coarseCentre j k x) ⊆ X ∧ (coarseCentre j k x : FourTorus L m) ∈ X ∧
          blockAtLevel j (coarseCentre j k x) ⊆ X
end YangMills.Construction.PeriodicLattice
