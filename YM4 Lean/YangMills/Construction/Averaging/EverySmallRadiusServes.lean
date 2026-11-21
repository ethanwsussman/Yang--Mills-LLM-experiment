import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Lattice.InvertibleContourVariables
import Mathlib
set_option autoImplicit false
open Set
open YangMills.Construction.PeriodicLattice YangMills.Construction.Matrices
open YangMills.Construction.Coordinates YangMills.Construction.Conventions
open scoped Topology
noncomputable section
namespace YangMills.Construction.Averaging.SmallRadius
variable {L m : ℕ} {j j' : ℤ}
def doubleBlockEquiv (c : Bond L m j) {n : ℕ}
    (e : positiveBondsInDoubleBlock (j' := j') c ≃ Fin n) :
    (positiveBondsInDoubleBlock (j' := j') c → ComplexMatrix2) ≃
      ComplexCoordinates (ComplexCoordinates.productDim
        fun _ : Fin n => ComplexCoordinates.Component.matrix) :=
  (Equiv.arrowCongr e (Equiv.refl ComplexMatrix2)).trans (SmallDiameterMean.familyEquiv n)
structure PropertiesAtBond {L m K : ℕ} (ω : ℝ) (k : ℕ) (c : BondAtLevel L m K (k + 1)) :
    Prop where
  isOpen_smallPlaquetteFields : ∀ ω' ∈ Ioc (0 : ℝ) 1,
    IsOpen[gaugeFieldsAtLevelTopology L m K k]
      (Subtype.val ⁻¹' (smallPlaquetteFields ω' c : Set (BondAtLevel L m K k → ComplexMatrix2)))
  holonomy_ratio_le : ∀ U ∈ (smallPlaquetteFields ω c : Set (BondAtLevel L m K k → ComplexMatrix2)),
    ∀ y ∈ ({c.source, c.target} : Set (SiteAtLevel L m K (k + 1))),
      ∀ x ∈ sitesInBlock (levelDepth K k) y, ∀ γ ∈ contourSet y x, ∀ γ' ∈ contourSet y x,
        ComplexMatrix2.operatorNorm (pathHolonomy U γ' * (pathHolonomy U γ)⁻¹ - 1) ≤
            (1 + ω) ^ (2 * L ^ 2) - 1 ∧
        (1 + ω) ^ (2 * L ^ 2) - 1 ≤ Real.exp (2 * (L : ℝ) ^ 2 * ω) - 1 ∧
        Real.exp (2 * (L : ℝ) ^ 2 * ω) - 1 ≤ Real.exp (1 / 100) - 1 ∧
        Real.exp (1 / 100) - 1 ≤ 1 / 50
  familyDiameter_le : ∀ U ∈ (smallPlaquetteFields ω c : Set (BondAtLevel L m K k → ComplexMatrix2)),
    ∀ y ∈ ({c.source, c.target} : Set (SiteAtLevel L m K (k + 1))),
      ∀ x ∈ sitesInBlock (levelDepth K k) y,
        ComplexMatrix2.unitFamilyDiameter (configurationContourFamily c U y x) ≤ 1 / 50
  contourMean_spec : ∀ U ∈ (smallPlaquetteFields ω c : Set (BondAtLevel L m K k → ComplexMatrix2)),
    ∀ y ∈ ({c.source, c.target} : Set (SiteAtLevel L m K (k + 1))),
      ∀ x ∈ sitesInBlock (levelDepth K k) y,
        HasContourMean U y x ∧
        meanContourHolonomy U y x =
          ComplexMatrix2.logMean compactGaugeGroup (configurationContourFamily c U y x) ∧
        meanContourHolonomy U y x =
          SmallDiameterMean.average (configurationContourFamily c U y x) ∧
        meanContourHolonomy U y x ∈ compactGaugeGroup ∧
        (∀ γ ∈ contourSet y x,
          ComplexMatrix2.operatorNorm (pathHolonomy U γ * (meanContourHolonomy U y x)⁻¹ - 1) ≤
            4 * ComplexMatrix2.unitFamilyDiameter (configurationContourFamily c U y x)) ∧
        4 * ComplexMatrix2.unitFamilyDiameter (configurationContourFamily c U y x) ≤ 2 / 25
  isOpen_invertibleContourSet : IsOpen (invertibleContourSet (j' := levelDepth K k) c)
  image_restrict_subset : restrictToPositiveDoubleBlock c ''
      (smallPlaquetteFields ω c : Set (BondAtLevel L m K k → ComplexMatrix2)) ⊆
    invertibleContourSet (j' := levelDepth K k) c
  holomorphic_contourVariable : ∀ y ∈ ({c.source, c.target} : Set (SiteAtLevel L m K (k + 1))),
    ∀ x ∈ sitesInBlock (levelDepth K k) y, ∀ (n : ℕ)
      (e : positiveBondsInDoubleBlock (j' := levelDepth K k) c ≃ Fin n),
      ComplexCoordinates.IsHolomorphicVia (doubleBlockEquiv c e)
        ComplexCoordinates.matrixEquiv (invertibleContourSet (j' := levelDepth K k) c)
        (fun V => contourVariable c V y x) ∧
      ComplexCoordinates.IsHolomorphicVia (doubleBlockEquiv c e)
        ComplexCoordinates.matrixEquiv (invertibleContourSet (j' := levelDepth K k) c)
        (fun V => contourVariableInverse c V y x)
  contourVariable_values : ∀ y ∈ ({c.source, c.target} : Set (SiteAtLevel L m K (k + 1))),
    ∀ x ∈ sitesInBlock (levelDepth K k) y, ∀ V ∈ invertibleContourSet (j' := levelDepth K k) c,
      IsUnit (contourVariable c V y x) ∧
      IsUnit (contourVariableInverse c V y x) ∧
      ((∀ b, V b ∈ complexGaugeGroup) →
        contourVariable c V y x ∈ complexGaugeGroup ∧
        contourVariableInverse c V y x ∈ complexGaugeGroup)
  contourVariable_extends : ∀ U ∈ (smallPlaquetteFields ω c : Set (BondAtLevel L m K k → ComplexMatrix2)),
    ∀ y ∈ ({c.source, c.target} : Set (SiteAtLevel L m K (k + 1))),
      ∀ x ∈ sitesInBlock (levelDepth K k) y,
        meanContourHolonomy U y x = contourVariable c (restrictToPositiveDoubleBlock c U) y x ∧
        (meanContourHolonomy U y x)⁻¹ =
          contourVariableInverse c (restrictToPositiveDoubleBlock c U) y x
  realAnalytic_contourMean : ∀ _ : Fintype (PositivelyOrientedBond L m (levelDepth K k)),
    ∀ y ∈ ({c.source, c.target} : Set (SiteAtLevel L m K (k + 1))),
      ∀ x ∈ sitesInBlock (levelDepth K k) y,
        ComplexMatrix2.IsRealAnalyticBetween
          (fun _ : PositivelyOrientedBond L m (levelDepth K k) => ComplexMatrix2.FactorKind.group)
          (fun _ : Fin 1 => ComplexMatrix2.FactorKind.group)
          (valuesOnPositiveBonds ''
            (smallPlaquetteFields ω c : Set (BondAtLevel L m K k → ComplexMatrix2)))
          (fun v _ => meanContourHolonomy (fieldOfPositiveValues v) y x) ∧
        ComplexMatrix2.IsRealAnalyticBetween
          (fun _ : PositivelyOrientedBond L m (levelDepth K k) => ComplexMatrix2.FactorKind.group)
          (fun _ : Fin 1 => ComplexMatrix2.FactorKind.group)
          (valuesOnPositiveBonds ''
            (smallPlaquetteFields ω c : Set (BondAtLevel L m K k → ComplexMatrix2)))
          (fun v _ => (meanContourHolonomy (fieldOfPositiveValues v) y x)⁻¹)
  crossingDefect_near : c.IsPositivelyOriented →
    ∀ U ∈ (smallPlaquetteFields ω c : Set (BondAtLevel L m K k → ComplexMatrix2)),
      ∀ x ∈ sitesInBlock (levelDepth K k) c.source,
        crossingDefect U c x ∈ compactGaugeGroup ∧
          ComplexMatrix2.operatorNorm (crossingDefect U c x - 1) < 1 / 5
def EverySmallRadiusSuffices : Prop :=
  ∀ s : StandingParameters, ∀ ω ∈ Ioc (0 : ℝ) (averagingRadiusCap s.L), ∀ k : ℕ, k < (s.K : ℕ) →
    ∀ c : BondAtLevel s.L (s.m : ℕ) (s.K : ℕ) (k + 1), PropertiesAtBond ω k c
end YangMills.Construction.Averaging.SmallRadius
end
