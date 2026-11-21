import YangMills.Construction.Averaging.CentreOfMassDiameter
import YangMills.Construction.Lattice.BlocksAndCorridors
import YangMills.Construction.Lattice.ContourPaths
import YangMills.Construction.Matrices.LogMeanOfFamily
import Mathlib
open Set
noncomputable section
namespace YangMills.Construction
namespace PeriodicLattice
open Matrices
variable {L m : ℕ} {j j' : ℤ}
def DoubleBlockPlaquettesNear (ω : ℝ) (c : Bond L m j) (U : Bond L m j' → ComplexMatrix2) : Prop :=
  ∀ p ∈ (doubleBlockPlaquettes c : Set (Plaquette L m j')),
    ComplexMatrix2.operatorNorm (plaquetteHolonomy U p - 1) < ω
def smallPlaquetteFields (ω : ℝ) (c : Bond L m j) : Set (Bond L m j' → ComplexMatrix2) :=
  {U | U ∈ compactGaugeFields L m j' ∧ DoubleBlockPlaquettesNear ω c U}
def sitesInBlock (j' : ℤ) (y : Site L m j) : Set (Site L m j') :=
  {x | (x : FourTorus L m) ∈ unitBlock y}
def contourHolonomies (U : Bond L m j' → ComplexMatrix2) (y : Site L m j) (x : Site L m j') :
    AxisOrdering y x → ComplexMatrix2 :=
  fun σ => pathHolonomy U (orderedContour y x σ)
def HasContourMean (U : Bond L m j' → ComplexMatrix2) (y : Site L m j) (x : Site L m j') : Prop :=
  ComplexMatrix2.HasUniqueLogMean compactGaugeGroup (contourHolonomies U y x)
def meanContourHolonomy (U : Bond L m j' → ComplexMatrix2) (y : Site L m j) (x : Site L m j') :
    ComplexMatrix2 :=
  ComplexMatrix2.logMean compactGaugeGroup (contourHolonomies U y x)
def crossingDefect (U : Bond L m j' → ComplexMatrix2) (c : Bond L m j) (x : Site L m j') :
    ComplexMatrix2 :=
  meanContourHolonomy U c.source x * pathHolonomy U (crossingPath c x) *
    (meanContourHolonomy U c.target (shiftAcross c x))⁻¹ * (parallelTransport U c)⁻¹
def inverseFourthPowerWeight (L : ℕ) : ℂ := (((L : ℝ) ^ (-4 : ℤ) : ℝ) : ℂ)
def IsRegularAveragingCase (ω : ℝ) (U : Bond L m j' → ComplexMatrix2) (c : Bond L m j) : Prop :=
  DoubleBlockPlaquettesNear ω c U ∧
    (∀ x ∈ sitesInBlock j' c.source, HasContourMean U c.source x) ∧
    (∀ x ∈ sitesInBlock j' c.target, HasContourMean U c.target x) ∧
    ∀ x ∈ sitesInBlock j' c.source, ComplexMatrix2.operatorNorm (crossingDefect U c x - 1) < 1
def contourCrossingDefect (U : Bond L m j' → ComplexMatrix2) (c : Bond L m j) (x : Site L m j')
    (σ : AxisOrdering c.source x) (τ : AxisOrdering c.target (shiftAcross c x)) : ComplexMatrix2 :=
  pathHolonomy U (orderedContour c.source x σ) * pathHolonomy U (crossingPath c x) *
    (pathHolonomy U (orderedContour c.target (shiftAcross c x) τ))⁻¹ * (parallelTransport U c)⁻¹
def regularAverageValue (U : Bond L m j' → ComplexMatrix2) (c : Bond L m j) : ComplexMatrix2 :=
  ComplexMatrix2.matExp (inverseFourthPowerWeight L • ∑ᶠ x ∈ sitesInBlock j' c.source,
    ComplexMatrix2.logSeries (crossingDefect U c x)) * parallelTransport U c
def logAverageValue (U : Bond L m j' → ComplexMatrix2) (c : Bond L m j) : ComplexMatrix2 :=
  ComplexMatrix2.matExp (inverseFourthPowerWeight L • ∑ᶠ x ∈ sitesInBlock j' c.source,
    (((Fintype.card (AxisOrdering c.source x) : ℝ)⁻¹ : ℝ) : ℂ) • ∑ σ : AxisOrdering c.source x,
      (((Fintype.card (AxisOrdering c.target (shiftAcross c x)) : ℝ)⁻¹ : ℝ) : ℂ) •
        ∑ τ : AxisOrdering c.target (shiftAcross c x),
          ComplexMatrix2.unitaryLog (contourCrossingDefect U c x σ τ)) * parallelTransport U c
def blockAverageOnPositive (ω : ℝ) (U : Bond L m j' → ComplexMatrix2) (c : Bond L m j) :
    ComplexMatrix2 :=
  open Classical in
  if IsRegularAveragingCase ω U c then regularAverageValue U c
  else if ∀ x ∈ sitesInBlock j' c.source, ∀ σ τ, contourCrossingDefect U c x σ τ ≠ -1 then
    logAverageValue U c
  else parallelTransport U c
def blockAverage (ω : ℝ) (U : Bond L m j' → ComplexMatrix2) : Bond L m j → ComplexMatrix2 :=
  open Classical in
  fun c => if c.IsPositivelyOriented then blockAverageOnPositive ω U c
    else (blockAverageOnPositive ω U c.opposite)⁻¹
section Iterates
variable {K : ℕ}
def iterateFromLevel
    (f : ∀ k, (BondAtLevel L m K k → ComplexMatrix2) → BondAtLevel L m K (k + 1) → ComplexMatrix2)
    (k : ℕ) :
    (n : ℕ) → (BondAtLevel L m K k → ComplexMatrix2) → BondAtLevel L m K (k + n) → ComplexMatrix2
  | 0, U => U
  | n + 1, U => f (k + n) (iterateFromLevel f k n U)
def iterateFromBare
    (f : ∀ k, (BondAtLevel L m K k → ComplexMatrix2) → BondAtLevel L m K (k + 1) → ComplexMatrix2) :
    (k : ℕ) → (BondAtLevel L m K 0 → ComplexMatrix2) → BondAtLevel L m K k → ComplexMatrix2
  | 0, U => U
  | k + 1, U => f k (iterateFromBare f k U)
def blockAverageStep (ω : ℝ) (k : ℕ) (U : BondAtLevel L m K k → ComplexMatrix2) :
    BondAtLevel L m K (k + 1) → ComplexMatrix2 :=
  blockAverage ω U
def blockFieldAtLevel (ω : ℝ) (k : ℕ) (U : BondAtLevel L m K 0 → ComplexMatrix2) :
    BondAtLevel L m K k → ComplexMatrix2 :=
  iterateFromBare (blockAverageStep ω) k U
end Iterates
def contourFormAverage (A : Bond L m j' → ComplexMatrix2) (y : Site L m j) (x : Site L m j') :
    ComplexMatrix2 :=
  (((Fintype.card (AxisOrdering y x) : ℝ)⁻¹ : ℝ) : ℂ) •
    ∑ σ : AxisOrdering y x, bondFormSumAlong A (orderedContour y x σ)
def linearBlockSum (A : Bond L m j' → ComplexMatrix2) (c : Bond L m j) : ComplexMatrix2 :=
  ∑ᶠ x ∈ sitesInBlock j' c.source, (contourFormAverage A c.source x +
    bondFormSumAlong A (crossingPath c x) - contourFormAverage A c.target (shiftAcross c x))
def linearBlockAverage (A : Bond L m j' → ComplexMatrix2) : Bond L m j → ComplexMatrix2 :=
  fun c => (((L : ℝ) ^ (-5 : ℤ) : ℝ) : ℂ) • linearBlockSum A c
def scaledLinearBlockAverage (A : Bond L m j' → ComplexMatrix2) : Bond L m j → ComplexMatrix2 :=
  fun c => inverseFourthPowerWeight L • linearBlockSum A c
section LinearIterates
variable {K : ℕ}
def linearBlockStep (k : ℕ) (A : BondAtLevel L m K k → ComplexMatrix2) :
    BondAtLevel L m K (k + 1) → ComplexMatrix2 :=
  linearBlockAverage A
def scaledLinearBlockStep (k : ℕ) (A : BondAtLevel L m K k → ComplexMatrix2) :
    BondAtLevel L m K (k + 1) → ComplexMatrix2 :=
  scaledLinearBlockAverage A
def linearBlockIterateBetween (k n : ℕ) :
    (BondAtLevel L m K k → ComplexMatrix2) → BondAtLevel L m K (k + n) → ComplexMatrix2 :=
  iterateFromLevel linearBlockStep k n
def scaledLinearBlockIterateFrom (k n : ℕ) :
    (BondAtLevel L m K k → ComplexMatrix2) → BondAtLevel L m K (k + n) → ComplexMatrix2 :=
  iterateFromLevel scaledLinearBlockStep k n
end LinearIterates
def complexMeanTolerance : ℝ := 1 / 10
def complexLogMean {ι : Type*} [Fintype ι] (V : ι → ComplexMatrix2) : ComplexMatrix2 :=
  Classical.epsilon fun W => ComplexMatrix2.IsLogMean complexGaugeGroup V W ∧
    ∃ i, ComplexMatrix2.operatorNorm (V i * W⁻¹ - 1) ≤ complexMeanTolerance
def complexMeanContourHolonomy (U : Bond L m j' → ComplexMatrix2) (y : Site L m j)
    (x : Site L m j') : ComplexMatrix2 :=
  complexLogMean (contourHolonomies U y x)
def bondsInDoubleBlock (c : Bond L m j) : Set (Bond L m j') := bondsInside (bondDoubleBlock c)
def complexAveragingDomain (c : Bond L m j) : Set (Bond L m j' → ComplexMatrix2) :=
  {U | IsGaugeField complexGaugeGroup (bondsInDoubleBlock c) U ∧
    (∀ x ∈ sitesInBlock j' c.source,
      ComplexMatrix2.familyDiameter (contourHolonomies U c.source x) <
        Averaging.centreOfMassDiameter) ∧
    ∀ x ∈ sitesInBlock j' c.target,
      ComplexMatrix2.familyDiameter (contourHolonomies U c.target x) <
        Averaging.centreOfMassDiameter}
def complexCrossingDefect (U : Bond L m j' → ComplexMatrix2) (c : Bond L m j) (x : Site L m j') :
    ComplexMatrix2 :=
  complexMeanContourHolonomy U c.source x * pathHolonomy U (crossingPath c x) *
    (complexMeanContourHolonomy U c.target (shiftAcross c x))⁻¹ * (parallelTransport U c)⁻¹
def complexAveragingDomainNearOne (c : Bond L m j) : Set (Bond L m j' → ComplexMatrix2) :=
  {U | U ∈ complexAveragingDomain c ∧
    ∀ x ∈ sitesInBlock j' c.source,
      ComplexMatrix2.operatorNorm (complexCrossingDefect U c x - 1) < 1}
def complexBlockAverageOnPositive (U : Bond L m j' → ComplexMatrix2) (c : Bond L m j) :
    ComplexMatrix2 :=
  ComplexMatrix2.matExp (inverseFourthPowerWeight L • ∑ᶠ x ∈ sitesInBlock j' c.source,
    ComplexMatrix2.logSeries (complexCrossingDefect U c x)) * parallelTransport U c
def complexBlockAverage (U : Bond L m j' → ComplexMatrix2) : Bond L m j → ComplexMatrix2 :=
  open Classical in
  fun c => if c.IsPositivelyOriented then complexBlockAverageOnPositive U c
    else (complexBlockAverageOnPositive U c.opposite)⁻¹
section ComplexIterates
variable {K : ℕ}
def complexBlockAverageStep (k : ℕ) (U : BondAtLevel L m K k → ComplexMatrix2) :
    BondAtLevel L m K (k + 1) → ComplexMatrix2 :=
  complexBlockAverage U
def complexBlockFieldAtLevel (k : ℕ) (U : BondAtLevel L m K 0 → ComplexMatrix2) :
    BondAtLevel L m K k → ComplexMatrix2 :=
  iterateFromBare complexBlockAverageStep k U
def complexBlockFieldDomain : (k : ℕ) → Set (BondAtLevel L m K 0 → ComplexMatrix2)
  | 0 => Set.univ
  | k + 1 => {U | U ∈ complexBlockFieldDomain k ∧
      ∀ c : BondAtLevel L m K (k + 1), c.IsPositivelyOriented →
        complexBlockFieldAtLevel k U ∈ complexAveragingDomainNearOne c}
end ComplexIterates
end PeriodicLattice
end YangMills.Construction
