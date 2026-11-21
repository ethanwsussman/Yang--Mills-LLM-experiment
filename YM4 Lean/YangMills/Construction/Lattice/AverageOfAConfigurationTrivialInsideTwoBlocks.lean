import YangMills.Construction.Averaging.SmoothingRadius
import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Lattice.BondwiseAverage
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
namespace PeriodicLattice
variable {L m : ℕ} {j : ℤ}
def twoBlockFieldValues (k : ℤ) (c : Bond L m j) (X : Matrices.ComplexMatrix2) (b : Bond L m k) :
    Matrices.ComplexMatrix2 :=
  open Classical in
  if b ∈ (bondsInside (unitBlock c.source) : Set (Bond L m k)) ∨
      b ∈ (bondsInside (unitBlock c.target) : Set (Bond L m k)) then 1
  else if b ∈ (bondCorridor c : Set (Bond L m k)) then X
  else if b.opposite ∈ (bondCorridor c : Set (Bond L m k)) then X⁻¹
  else 1
def twoBlockField (k : ℤ) (c : Bond L m j) (X : Matrices.ComplexMatrix2) :
    PartialGaugeField L m k where
  support := bondsInDoubleBlock c
  field := twoBlockFieldValues k c X
def HasComplexContourMean {k : ℤ} (U : Bond L m k → Matrices.ComplexMatrix2) (y : Site L m j)
    (x : Site L m k) : Prop :=
  IsGaugeField complexGaugeGroup (bondsInside (unitBlock y)) U ∧
    Matrices.ComplexMatrix2.familyDiameter (contourHolonomies U y x) <
      Averaging.centreOfMassDiameter
def TwoBlockFieldTransports (k : ℤ) (c : Bond L m j) (X : Matrices.ComplexMatrix2) : Prop :=
  IsGaugeField complexGaugeGroup (bondsInDoubleBlock c) (twoBlockFieldValues k c X) ∧
    (X ∈ compactGaugeGroup →
      IsGaugeField compactGaugeGroup (bondsInDoubleBlock c) (twoBlockFieldValues k c X)) ∧
    twoBlockField k c.opposite X⁻¹ = twoBlockField k c X ∧
    ∀ (γ : List (Bond L m k)) (z w : Site L m k), IsBondPathFromTo γ z w →
      (∀ b ∈ γ, b ∈ (bondsInDoubleBlock c : Set (Bond L m k))) →
      (((z ∈ sitesInBlock k c.source ∧ w ∈ sitesInBlock k c.source) ∨
          (z ∈ sitesInBlock k c.target ∧ w ∈ sitesInBlock k c.target)) →
        pathHolonomy (twoBlockFieldValues k c X) γ = 1) ∧
      (z ∈ sitesInBlock k c.source → w ∈ sitesInBlock k c.target →
        pathHolonomy (twoBlockFieldValues k c X) γ = X)
def TwoBlockPlaquetteHolonomyTrivial (k : ℤ) (c : Bond L m j) (X : Matrices.ComplexMatrix2) :
    Prop :=
  ∀ p ∈ (doubleBlockPlaquettes c : Set (Plaquette L m k)),
    plaquetteHolonomy (twoBlockFieldValues k c X) p = 1
def TwoBlockContourHolonomyTrivial (k : ℤ) (c : Bond L m j) (X : Matrices.ComplexMatrix2) :
    Prop :=
  ∀ y ∈ ({c.source, c.target} : Set (Site L m j)), ∀ x ∈ sitesInBlock k y,
    (∀ γ ∈ contourSet y x, pathHolonomy (twoBlockFieldValues k c X) γ = 1) ∧
      HasComplexContourMean (twoBlockFieldValues k c X) y x ∧
      complexMeanContourHolonomy (twoBlockFieldValues k c X) y x = 1 ∧
      (X ∈ compactGaugeGroup → HasContourMean (twoBlockFieldValues k c X) y x ∧
        meanContourHolonomy (twoBlockFieldValues k c X) y x = 1)
def TwoBlockCrossingHolonomy (k : ℤ) (c : Bond L m j) (X : Matrices.ComplexMatrix2) : Prop :=
  ∀ x ∈ sitesInBlock k c.source,
    pathHolonomy (twoBlockFieldValues k c X) (crossingPath c x) = X ∧
      parallelTransport (twoBlockFieldValues k c X) c = X ∧
      complexCrossingDefect (twoBlockFieldValues k c X) c x = 1
def TwoBlockComplexMean (k : ℤ) (c : Bond L m j) (X : Matrices.ComplexMatrix2) : Prop :=
  onSetElseOne (bondsInDoubleBlock c) (twoBlockFieldValues k c X) ∈
      complexAveragingDomainNearOne c.positivelyOriented ∧
    c ∈ (complexPartialBlockAverage (twoBlockField k c X)).support ∧
    (complexPartialBlockAverage (twoBlockField k c X)).field c = X
def TwoBlockCompactMean (ω : ℝ) (k : ℤ) (c : Bond L m j) (X : Matrices.ComplexMatrix2) : Prop :=
  (∀ U ∈ compactGaugeFields L m k,
      (∀ b ∈ (bondsInDoubleBlock c : Set (Bond L m k)), U b = twoBlockFieldValues k c X b) →
      U ∈ smallPlaquetteFields ω c) ∧
    partialBlockAverageCase ω (twoBlockFieldValues k c X) c = .logarithmOfMeans ∧
    c ∈ (realPartialBlockAverage ω (twoBlockField k c X)).support ∧
    (realPartialBlockAverage ω (twoBlockField k c X)).field c = X
def TwoBlockFieldMeanProperties : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ m K q : ℕ, 0 < m → q < K →
    ∀ c : BondAtLevel L m K (q + 1), ∀ X ∈ complexGaugeGroup,
      TwoBlockFieldTransports (levelDepth K q) c X ∧
      TwoBlockPlaquetteHolonomyTrivial (levelDepth K q) c X ∧
      TwoBlockContourHolonomyTrivial (levelDepth K q) c X ∧
      TwoBlockCrossingHolonomy (levelDepth K q) c X ∧
      TwoBlockComplexMean (levelDepth K q) c X ∧
      (X ∈ compactGaugeGroup →
        TwoBlockCompactMean (Averaging.smoothingRadius L) (levelDepth K q) c X)
end PeriodicLattice
end YangMills.Construction
