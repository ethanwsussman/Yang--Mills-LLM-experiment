import YangMills.Construction.Lattice.AnnulusSites
import YangMills.Construction.Lattice.BlockAveraging
import YangMills.Construction.Lattice.CoordinateCombs
import YangMills.Construction.Lattice.CovariantSiteOperators
import Mathlib
open Set Filter Topology
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction
namespace PeriodicLattice
open YangMills.Construction.Matrices
variable {L m : ℕ} {j j' : ℤ}
def combHolonomy (W : Bond L m j' → ComplexMatrix2) (z : Site L m j) (x : Site L m j') :
    ComplexMatrix2 :=
  pathHolonomy W (coordinateComb (z.toSublattice j') x)
def averagingLogArgument (W : Bond L m j' → ComplexMatrix2) (g : Site L m j' → ComplexMatrix2)
    (z : Site L m j) (x : Site L m j') : ComplexMatrix2 :=
  (g (z.toSublattice j'))⁻¹ * ComplexMatrix2.conjugateBy (combHolonomy W z x) (g x)
def SingleStepAverageDefinedAt (W : Bond L m j' → ComplexMatrix2)
    (g : Site L m j' → ComplexMatrix2) (z : Site L m j) : Prop :=
  ∀ x ∈ sitesInBlock j' z, averagingLogArgument W g z x ∈ ComplexMatrix2.logBall
def singleStepGaugeAverage (W : Bond L m j' → ComplexMatrix2) (g : Site L m j' → ComplexMatrix2) :
    Site L m j → ComplexMatrix2 :=
  fun z => g (z.toSublattice j') * ComplexMatrix2.matExp (inverseFourthPowerWeight L •
    ∑ᶠ x ∈ sitesInBlock j' z, ComplexMatrix2.logSeries (averagingLogArgument W g z x))
def singleStepLinearizedAverage (W : Bond L m j' → ComplexMatrix2)
    (f : Site L m j' → ComplexMatrix2) : Site L m j → ComplexMatrix2 :=
  fun z => inverseFourthPowerWeight L •
    ∑ᶠ x ∈ sitesInBlock j' z, ComplexMatrix2.conjugateBy (combHolonomy W z x) (f x)
section Iterates
variable {K : ℕ}
structure BlockingIterates (L m K : ℕ) where
  value : ∀ n : ℕ, (BondAtLevel L m K 0 → ComplexMatrix2) → BondAtLevel L m K n → ComplexMatrix2
  IsDefinedAt : ∀ n : ℕ, (BondAtLevel L m K 0 → ComplexMatrix2) → BondAtLevel L m K n → Prop
def realBlockingIterates (ω : ℝ) : BlockingIterates L m K where
  value n U := blockFieldAtLevel ω n U
  IsDefinedAt _ _ _ := True
def iteratedGaugeAverage (I : BlockingIterates L m K) (U : BondAtLevel L m K 0 → ComplexMatrix2) :
    (n : ℕ) → (SiteAtLevel L m K 0 → ComplexMatrix2) → SiteAtLevel L m K n → ComplexMatrix2
  | 0, g => g
  | n + 1, g => singleStepGaugeAverage (I.value n U) (iteratedGaugeAverage I U n g)
def IteratedGaugeAverageDefinedAt (I : BlockingIterates L m K)
    (U : BondAtLevel L m K 0 → ComplexMatrix2) :
    (n : ℕ) → (SiteAtLevel L m K 0 → ComplexMatrix2) → SiteAtLevel L m K n → Prop
  | 0, _, _ => True
  | n + 1, g, z =>
    (∀ x ∈ sitesInBlock (levelDepth K n) z, IteratedGaugeAverageDefinedAt I U n g x) ∧
      SingleStepAverageDefinedAt (I.value n U) (iteratedGaugeAverage I U n g) z
def IsAverageNormalized (I : BlockingIterates L m K) (k : ℕ) (Ω : ℕ → Set (FourTorus L m))
    (U : BondAtLevel L m K 0 → ComplexMatrix2) (g : SiteAtLevel L m K 0 → ComplexMatrix2) : Prop :=
  ∀ i ≤ k, ∀ y ∈ annulusSites K k Ω i,
    IteratedGaugeAverageDefinedAt I U i g y ∧ iteratedGaugeAverage I U i g y = 1
def iteratedLinearizedAverage (I : BlockingIterates L m K)
    (U : BondAtLevel L m K 0 → ComplexMatrix2) :
    (n : ℕ) → (SiteAtLevel L m K 0 → ComplexMatrix2) → SiteAtLevel L m K n → ComplexMatrix2
  | 0, f => f
  | n + 1, f => singleStepLinearizedAverage (I.value n U) (iteratedLinearizedAverage I U n f)
def admissibleInfinitesimalGauges (I : BlockingIterates L m K) (k : ℕ)
    (Ω : ℕ → Set (FourTorus L m)) (U : BondAtLevel L m K 0 → ComplexMatrix2) :
    Set (SiteAtLevel L m K 0 → ComplexMatrix2) :=
  {f | IsSiteField complexLieAlgebra f ∧ zeroExtendSiteField (Ω 0) f = f ∧
    ∀ i ≤ k, ∀ y ∈ annulusSites K k Ω i, iteratedLinearizedAverage I U i f y = 0}
def EndpointBlocksSubset (X : Set (FourTorus L m)) (i : ℕ) (c : BondAtLevel L m K i) : Prop :=
  refinedBlock i c.source ∪ refinedBlock i c.target ⊆ X
end Iterates
end PeriodicLattice
end YangMills.Construction
