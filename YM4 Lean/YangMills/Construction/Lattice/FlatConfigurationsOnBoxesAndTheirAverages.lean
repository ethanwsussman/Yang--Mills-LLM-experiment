import YangMills.Construction.Averaging.SmoothingRadius
import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Lattice.BareDoubleBlocks
import YangMills.Construction.Lattice.FlatGaugeFields
import YangMills.Construction.Lattice.SiteBoxes
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicLattice
def FlatBoxHolonomyPathIndependent (L m K : ℕ) : Prop :=
  ∀ (Y : Set (SiteAtLevel L m K 0)) (U : BondAtLevel L m K 0 → Matrices.ComplexMatrix2),
    IsSiteBox (levelDepth K 0) Y → IsGaugeField compactGaugeGroup (bondsAmong Y) U →
    IsFlatOver U Y →
    ∀ (γ₁ γ₂ : List (BondAtLevel L m K 0)) (z z' : SiteAtLevel L m K 0),
      IsBondPathFromTo γ₁ z z' → IsBondPathFromTo γ₂ z z' →
      (∀ b ∈ γ₁, b.LiesIn Y) → (∀ b ∈ γ₂, b.LiesIn Y) →
      pathHolonomy U γ₁ = pathHolonomy U γ₂
def BlockFieldTrivial (L m K q : ℕ) : Prop :=
  blockFieldAtLevel (Averaging.smoothingRadius L) q
      (trivialGaugeField : BondAtLevel L m K 0 → Matrices.ComplexMatrix2) =
    (trivialGaugeField : BondAtLevel L m K q → Matrices.ComplexMatrix2)
def FlatBlockAverageEqTransport (L m K q : ℕ) : Prop :=
  ∀ (c : BondAtLevel L m K q) (U : BondAtLevel L m K 0 → Matrices.ComplexMatrix2),
    IsGaugeField compactGaugeGroup (bareBondsInBlockPair c) U →
    IsFlatOver U (sitesIn (bareBlockPair c)) →
    partialBareBlockField (Averaging.smoothingRadius L) U c = bareParallelTransport U c
def FlatFieldsAndTheirAverages : Prop :=
  ∀ L m K : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < m → 0 < K →
    FlatBoxHolonomyPathIndependent L m K ∧
      ∀ q : ℕ, q ≤ K →
        BlockFieldTrivial L m K q ∧ FlatBlockAverageEqTransport L m K q
end YangMills.Construction.PeriodicLattice
