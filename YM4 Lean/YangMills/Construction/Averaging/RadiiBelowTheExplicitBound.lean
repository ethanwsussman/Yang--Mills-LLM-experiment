import YangMills.Construction.Averaging.DomainOfTheSymmetrisedAverage
import YangMills.Construction.Averaging.MeanInTheComplexGroup
import Mathlib
set_option autoImplicit false
open Set YangMills.Construction.PeriodicLattice
noncomputable section
namespace YangMills.Construction
namespace Averaging
namespace ExplicitRadii
def ConstantsGiveMeans : Prop :=
  0 < 4 * (1 / 40 : ℝ) ∧ 4 * (1 / 40 : ℝ) ≤ 1 / 10 ∧ (1 / 10 : ℝ) < 1 ∧
  centreOfMassDiameter = 1 / 40 ∧ complexMeanTolerance = 1 / 10 ∧
  ∀ n : ℕ, 1 ≤ n → ComplexLogMeanProperties n
def RadiusCapDependsOnlyOnL : Prop :=
  ∀ s t : Conventions.StandingParameters, s.L = t.L →
    averagingRadiusCap s.L = averagingRadiusCap t.L
def ContourDiameterBounds {L m K : ℕ} (ω : ℝ) (k : ℕ) (c : BondAtLevel L m K (k + 1)) : Prop :=
  ∀ U ∈ (smallPlaquetteFields ω c : Set (BondAtLevel L m K k → Matrices.ComplexMatrix2)),
    ∀ y ∈ ({c.source, c.target} : Set (SiteAtLevel L m K (k + 1))),
      ∀ x ∈ sitesInBlock (levelDepth K k) y,
        Matrices.ComplexMatrix2.familyDiameter (contourHolonomies U y x) ≤
            3 / 2 * ((L : ℝ) - 1) ^ 2 * ω ∧
        3 / 2 * ((L : ℝ) - 1) ^ 2 * ω < 3 / 400 ∧
        Matrices.ComplexMatrix2.familyDiameter (contourHolonomies U y x) < 1 / 40
def isOpen_smallPlaquetteFields {L m K : ℕ} (ω : ℝ) (k : ℕ)
    (c : BondAtLevel L m K (k + 1)) : Prop :=
  IsOpen (((↑) : gaugeFieldsAtLevel L m K k → BondAtLevel L m K k → Matrices.ComplexMatrix2) ⁻¹'
    (smallPlaquetteFields ω c : Set (BondAtLevel L m K k → Matrices.ComplexMatrix2)))
def HolonomiesNearMean {L m K : ℕ} (ω : ℝ) (k : ℕ) (c : BondAtLevel L m K (k + 1)) : Prop :=
  ∀ U ∈ (smallPlaquetteFields ω c : Set (BondAtLevel L m K k → Matrices.ComplexMatrix2)),
    ∀ y ∈ ({c.source, c.target} : Set (SiteAtLevel L m K (k + 1))),
      ∀ x ∈ sitesInBlock (levelDepth K k) y, ∀ σ : AxisOrdering y x,
        Matrices.ComplexMatrix2.operatorNorm
            (pathHolonomy U (orderedContour y x σ) * (meanContourHolonomy U y x)⁻¹ - 1) ≤
          6 * ((L : ℝ) - 1) ^ 2 * ω
def DefectsNearOne {L m K : ℕ} (ω : ℝ) (k : ℕ) (c : BondAtLevel L m K (k + 1)) : Prop :=
  c.IsPositivelyOriented →
    ∀ U ∈ (smallPlaquetteFields ω c : Set (BondAtLevel L m K k → Matrices.ComplexMatrix2)),
      ∀ x ∈ sitesInBlock (levelDepth K k) c.source,
        Matrices.ComplexMatrix2.operatorNorm (crossingDefect U c x - 1) < 27 / 400
structure SmallSetPropertiesAtBond {L m K : ℕ} (ω : ℝ) (k : ℕ)
    (c : BondAtLevel L m K (k + 1)) : Prop where
  domain : SymmetrisedDomainPropertiesAtBond ω k c
  isOpen : isOpen_smallPlaquetteFields ω k c
  analytic : ∀ _ : Fintype (PositivelyOrientedBond L m (levelDepth K k)),
    ContourMeansAnalyticOn ({c.source, c.target} : Set (SiteAtLevel L m K (k + 1)))
      (smallPlaquetteFields ω c : Set (BondAtLevel L m K k → Matrices.ComplexMatrix2))
  nearMean : HolonomiesNearMean ω k c
  nearOne : DefectsNearOne ω k c
def RegularCaseOnSmallSet {L m K : ℕ} (ω : ℝ) (k : ℕ) (c : BondAtLevel L m K (k + 1)) : Prop :=
  ∀ U ∈ (smallPlaquetteFields ω c : Set (BondAtLevel L m K k → Matrices.ComplexMatrix2)),
    IsRegularAveragingCase ω U c
def SmallSetInComplexDomain {L m K : ℕ} (ω : ℝ) (k : ℕ)
    (c : BondAtLevel L m K (k + 1)) : Prop :=
  ∀ U ∈ (smallPlaquetteFields ω c : Set (BondAtLevel L m K k → Matrices.ComplexMatrix2)),
    U ∈ (complexAveragingDomainNearOne c : Set (BondAtLevel L m K k → Matrices.ComplexMatrix2)) ∧
      complexBlockAverageOnPositive U c = regularAverageValue U c
def BlockAverageAnalyticOnSmallSet {L m K : ℕ} (ω : ℝ) (k : ℕ)
    (c : BondAtLevel L m K (k + 1)) : Prop :=
  ∀ _ : Fintype (PositivelyOrientedBond L m (levelDepth K k)),
    Matrices.ComplexMatrix2.IsRealAnalyticBetween
      (fun _ : PositivelyOrientedBond L m (levelDepth K k) =>
        Matrices.ComplexMatrix2.FactorKind.group)
      (fun _ : Fin 1 => Matrices.ComplexMatrix2.FactorKind.group)
      (valuesOnPositiveBonds ''
        (smallPlaquetteFields ω c : Set (BondAtLevel L m K k → Matrices.ComplexMatrix2)))
      fun v _ => blockAverage ω (fieldOfPositiveValues v) c
structure RadiiBelowCap (s : Conventions.StandingParameters) : Prop where
  cap_mem : averagingRadiusCap s.L ∈ Ioc (0 : ℝ) 1
  diameters : ∀ ω ∈ Ioc (0 : ℝ) (averagingRadiusCap s.L), ∀ k, k < (s.K : ℕ) →
    ∀ c : BondAtLevel s.L s.m s.K (k + 1), ContourDiameterBounds ω k c
  contoursSmall : ContourHolonomiesAreSmall s.L s.m s.K (averagingRadiusCap s.L)
  smallSet : ∀ ω ∈ Ioc (0 : ℝ) (averagingRadiusCap s.L), ∀ k, k < (s.K : ℕ) →
    ∀ c : BondAtLevel s.L s.m s.K (k + 1), SmallSetPropertiesAtBond ω k c
  regular : ∀ ω ∈ Ioc (0 : ℝ) (averagingRadiusCap s.L), ∀ k, k < (s.K : ℕ) →
    ∀ c : BondAtLevel s.L s.m s.K (k + 1), c.IsPositivelyOriented → RegularCaseOnSmallSet ω k c
  complexDomain : ∀ ω ∈ Ioc (0 : ℝ) (averagingRadiusCap s.L), ∀ k, k < (s.K : ℕ) →
    ∀ c : BondAtLevel s.L s.m s.K (k + 1), c.IsPositivelyOriented →
      SmallSetInComplexDomain ω k c
  analytic : ∀ ω ∈ Ioc (0 : ℝ) (averagingRadiusCap s.L), ∀ k, k < (s.K : ℕ) →
    ∀ c : BondAtLevel s.L s.m s.K (k + 1), c.IsPositivelyOriented →
      BlockAverageAnalyticOnSmallSet ω k c
def RadiiOfLHaveDomainProperties : Prop :=
  ∀ ω : ℕ → ℝ, ∀ s : Conventions.StandingParameters,
    ω s.L ∈ Ioc (0 : ℝ) (averagingRadiusCap s.L) →
      ω s.L ∈ Ioc (0 : ℝ) 1 ∧ ω s.L ≤ averagingRadiusCap s.L ∧
        SymmetrisedDomainProperties s.L s.m s.K (ω s.L)
def Holds : Prop :=
  ConstantsGiveMeans ∧ RadiusCapDependsOnlyOnL ∧
    (∀ s : Conventions.StandingParameters, RadiiBelowCap s) ∧ RadiiOfLHaveDomainProperties
end ExplicitRadii
end Averaging
end YangMills.Construction
end
