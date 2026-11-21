import YangMills.Construction.Averaging.SmoothingRadius
import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Lattice.AveragesOnPartOfTheBareLattice
import YangMills.Construction.Lattice.GaugeFieldSpacesAndRealAnalyticMaps
import YangMills.Construction.Lattice.SiteBoxes
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
namespace PeriodicLattice
section Vocabulary
variable {L m : ℕ} {j : ℤ}
def IsLowestSite (P : Set (Site L m j)) (x : Site L m j) : Prop :=
  x ∈ P ∧ ∀ z ∈ P, ∃ d, IsChartOffset x z d ∧ ∀ μ, 0 ≤ d μ
def pathTranslate (γ : List (Bond L m j)) (a : Site L m j) : List (Bond L m j) :=
  γ.map fun e => ⟨e.source + a, e.target + a, by
    obtain ⟨μ, hμ⟩ := e.isNeighbour
    exact ⟨μ, by simpa only [add_sub_add_right_eq_sub] using hμ⟩⟩
def IsPathWithin (X : Set (FourTorus L m)) (x₀ : Site L m j) (γ : List (Bond L m j)) : Prop :=
  (x₀ : FourTorus L m) ∈ X ∧
    ∀ e ∈ γ, (e.source : FourTorus L m) ∈ X ∧ (e.target : FourTorus L m) ∈ X
def IsOpenAmongFields (B : Set (Bond L m j)) (O : Set (Bond L m j → Matrices.ComplexMatrix2)) :
    Prop :=
  Matrices.ComplexMatrix2.IsRelativelyOpen
    (Matrices.ComplexMatrix2.complexifiedProduct
      fun _ : PositiveBondOf B => Matrices.ComplexMatrix2.FactorKind.group)
    (restrictToPositive B '' O)
def IsHolomorphicOnFields (B : Set (Bond L m j)) (O : Set (Bond L m j → Matrices.ComplexMatrix2))
    (F : (Bond L m j → Matrices.ComplexMatrix2) → Matrices.ComplexMatrix2) : Prop :=
  (∃ _ : Fintype (PositiveBondOf B),
    Matrices.ComplexMatrix2.IsHolomorphicBetween
      (fun _ : PositiveBondOf B => Matrices.ComplexMatrix2.FactorKind.group)
      (fun _ : Unit => Matrices.ComplexMatrix2.FactorKind.group) (restrictToPositive B '' O)
      fun v _ => F (extendFromPositive B v)) ∧
    ∀ (N : ℕ) (e : PositiveBondOf B ≃ Fin N)
      (β : Module.Basis (Fin 3) ℂ Matrices.ComplexMatrix2.traceless),
      Coordinates.ComplexCoordinates.IsHolomorphicOnSL2Power β
        ((fun v => v ∘ e.symm) '' (restrictToPositive B '' O))
        fun X => F (extendFromPositive B (X ∘ e))
def imaginaryLieAlgebra : Set Matrices.ComplexMatrix2 :=
  {X | ∃ Y ∈ Matrices.ComplexMatrix2.hermitianTraceless, X = Complex.I • Y}
end Vocabulary
variable {L m K n : ℕ}
def schemeHolomorphyDomain (s : AveragingScheme) (c : BondAtLevel L m K (n + 1)) :
    Set (BondAtLevel L m K n → Matrices.ComplexMatrix2) :=
  {W | IsSchemeAverageDefined s W c}
structure BlockPathProperties (y : SiteAtLevel L m K (n + 1)) (x : SiteAtLevel L m K n) :
    Prop where
  lowest : IsLowestSite (sitesInBlock (levelDepth K n) y)
    (schemeBaseSite .cornered (levelDepth K n) y)
  comb_in_box : ∃ P, IsSiteBox (levelDepth K n) P ∧
    schemeBaseSite .cornered (levelDepth K n) y ∈ P ∧ x ∈ P
  comb_count_le : ∀ ν : Fin 4,
    (coordinateComb (schemeBaseSite .cornered (levelDepth K n) y) x).countP
      (fun e => decide (e.axis = ν)) ≤ L - 1
  comb_translate : ∀ ν : Fin 4,
    pathTranslate (coordinateComb (schemeBaseSite .cornered (levelDepth K n) y) x)
        ((L : ℤ) • unitStep L m (levelDepth K n) ν) =
      coordinateComb
        (schemeBaseSite .cornered (levelDepth K n) (y + unitStep L m (levelDepth K (n + 1)) ν))
        (x + (L : ℤ) • unitStep L m (levelDepth K n) ν)
  comb_within : IsPathWithin (unitBlock y) (schemeBaseSite .cornered (levelDepth K n) y)
    (coordinateComb (schemeBaseSite .cornered (levelDepth K n) y) x)
  contour_within : ∀ σ : AxisOrdering y x,
    IsPathWithin (unitBlock y) (y.toSublattice (levelDepth K n)) (orderedContour y x σ)
structure DoubleBlockStraightPaths (s : AveragingScheme) (c : BondAtLevel L m K (n + 1)) :
    Prop where
  crossing_within : ∀ x ∈ sitesInBlock (levelDepth K n) c.source,
    IsPathWithin (bondDoubleBlock c) x (crossingPath c x)
  base_within : IsPathWithin (bondDoubleBlock c) (schemeBaseSite s (levelDepth K n) c.source)
    (axialPath (schemeBaseSite s (levelDepth K n) c.source)
      (schemeBaseSite s (levelDepth K n) c.target))
structure SchemeDomainProperties (s : AveragingScheme) (c : BondAtLevel L m K (n + 1)) :
    Prop where
  isOpen : IsOpenAmongFields (bondsInDoubleBlock c) (schemeHolomorphyDomain s c)
  contour_holomorphic : ∀ y ∈ ({c.source, c.target} : Set (SiteAtLevel L m K (n + 1))),
    ∀ x ∈ sitesInBlock (levelDepth K n) y,
      IsHolomorphicOnFields (bondsInDoubleBlock c) (schemeHolomorphyDomain s c)
        fun W => contourHolonomy s W y x
  average_holomorphic : IsHolomorphicOnFields (bondsInDoubleBlock c)
    (schemeHolomorphyDomain s c) fun W => schemeBlockAverage s W c
structure CentredDomainAgreement (c : BondAtLevel L m K (n + 1)) : Prop where
  domain_eq : schemeHolomorphyDomain .centred c =
    (complexAveragingDomainNearOne c : Set (BondAtLevel L m K n → Matrices.ComplexMatrix2))
  defect_eq : ∀ W ∈ (schemeHolomorphyDomain .centred c :
      Set (BondAtLevel L m K n → Matrices.ComplexMatrix2)),
    ∀ x ∈ sitesInBlock (levelDepth K n) c.source,
      localDefect .centred W c x = complexCrossingDefect W c x
  average_eq : ∀ W ∈ (schemeHolomorphyDomain .centred c :
      Set (BondAtLevel L m K n → Matrices.ComplexMatrix2)),
    schemeBlockAverage .centred W c = complexBlockAverage W c
structure SchemeValuesCompact (s : AveragingScheme) (W : BondAtLevel L m K n → Matrices.ComplexMatrix2)
    (c : BondAtLevel L m K (n + 1)) : Prop where
  contour_mem : ∀ y ∈ ({c.source, c.target} : Set (SiteAtLevel L m K (n + 1))),
    ∀ x ∈ sitesInBlock (levelDepth K n) y, contourHolonomy s W y x ∈ compactGaugeGroup
  defect_mem : ∀ x ∈ sitesInBlock (levelDepth K n) c.source,
    localDefect s W c x ∈ compactGaugeGroup
  exponent_mem : (inverseFourthPowerWeight L • ∑ᶠ x ∈ sitesInBlock (levelDepth K n) c.source,
    Matrices.ComplexMatrix2.logSeries (localDefect s W c x)) ∈ imaginaryLieAlgebra
  average_mem : schemeBlockAverage s W c ∈ compactGaugeGroup
structure CentredSchemeAgreesWithAverage (W : BondAtLevel L m K n → Matrices.ComplexMatrix2)
    (c : BondAtLevel L m K (n + 1)) : Prop where
  mem_domain : W ∈ schemeHolomorphyDomain .centred c
  unique_mean : ∀ y ∈ ({c.source, c.target} : Set (SiteAtLevel L m K (n + 1))),
    ∀ x ∈ sitesInBlock (levelDepth K n) y, HasContourMean W y x
  contour_eq : ∀ y ∈ ({c.source, c.target} : Set (SiteAtLevel L m K (n + 1))),
    ∀ x ∈ sitesInBlock (levelDepth K n) y,
      contourHolonomy .centred W y x = meanContourHolonomy W y x
  regular_case : IsRegularAveragingCase (Averaging.smoothingRadius L) W c
  average_eq : schemeBlockAverage .centred W c = blockAverage (Averaging.smoothingRadius L) W c
structure SchemeGaugeCovariance (s : AveragingScheme) (g : SiteAtLevel L m K n → Matrices.ComplexMatrix2)
    (W : BondAtLevel L m K n → Matrices.ComplexMatrix2) (c : BondAtLevel L m K (n + 1)) : Prop where
  contour_defined_iff : ∀ y ∈ ({c.source, c.target} : Set (SiteAtLevel L m K (n + 1))),
    ∀ x ∈ sitesInBlock (levelDepth K n) y,
      (IsContourHolonomyDefined s (gaugeTransform g W) y x ↔ IsContourHolonomyDefined s W y x)
  contour_eq : ∀ y ∈ ({c.source, c.target} : Set (SiteAtLevel L m K (n + 1))),
    ∀ x ∈ sitesInBlock (levelDepth K n) y, IsContourHolonomyDefined s W y x →
      contourHolonomy s (gaugeTransform g W) y x =
        g (schemeBaseSite s (levelDepth K n) y) * contourHolonomy s W y x * (g x)⁻¹
  average_defined_iff :
    IsSchemeAverageDefined s (gaugeTransform g W) c ↔ IsSchemeAverageDefined s W c
  average_eq : IsSchemeAverageDefined s W c →
    schemeBlockAverage s (gaugeTransform g W) c =
      g (schemeBaseSite s (levelDepth K n) c.source) * schemeBlockAverage s W c *
        (g (schemeBaseSite s (levelDepth K n) c.target))⁻¹
  defect_eq : AreContourHolonomiesDefined s W c → ∀ x ∈ sitesInBlock (levelDepth K n) c.source,
    localDefect s (gaugeTransform g W) c x =
      g (schemeBaseSite s (levelDepth K n) c.source) * localDefect s W c x *
        (g (schemeBaseSite s (levelDepth K n) c.source))⁻¹
def ContourHolonomyIsLocal (s : AveragingScheme) (y : SiteAtLevel L m K (n + 1))
    (x : SiteAtLevel L m K n) : Prop :=
  ∀ W W' : BondAtLevel L m K n → Matrices.ComplexMatrix2,
    (∀ e ∈ bondsInside (unitBlock y), W e = W' e) →
    (IsContourHolonomyDefined s W y x ↔ IsContourHolonomyDefined s W' y x) ∧
      (IsContourHolonomyDefined s W y x → contourHolonomy s W y x = contourHolonomy s W' y x)
structure IteratedAverageProperties (L m K : ℕ) (s : AveragingScheme) (j : ℕ) : Prop where
  lowest : ∀ y : SiteAtLevel L m K j,
    IsLowestSite (sitesIn (refinedBlock j y)) (finestBaseSite .cornered K j y)
  gauge_defined_iff : ∀ U ∈ gaugeFieldsAtLevel L m K 0, ∀ u : SiteAtLevel L m K 0 → Matrices.ComplexMatrix2,
    IsGaugeMap compactGaugeGroup u →
      (gaugeTransform u U ∈ iteratedAverageDomain s j ↔ U ∈ iteratedAverageDomain s j)
  gauge_eq : ∀ U ∈ gaugeFieldsAtLevel L m K 0, ∀ u : SiteAtLevel L m K 0 → Matrices.ComplexMatrix2,
    IsGaugeMap compactGaugeGroup u → U ∈ iteratedAverageDomain s j →
      iteratedAverage s j (gaugeTransform u U) =
        gaugeTransform (fun y => u (finestBaseSite s K j y)) (iteratedAverage s j U)
  gauge_defined_at_iff : ∀ U ∈ gaugeFieldsAtLevel L m K 0,
    ∀ u : SiteAtLevel L m K 0 → Matrices.ComplexMatrix2,
    IsGaugeMap compactGaugeGroup u → ∀ c : BondAtLevel L m K j,
      (IsBareIterateDefined s (gaugeTransform u U) j c ↔ IsBareIterateDefined s U j c)
  gauge_eq_at : ∀ U ∈ gaugeFieldsAtLevel L m K 0, ∀ u : SiteAtLevel L m K 0 → Matrices.ComplexMatrix2,
    IsGaugeMap compactGaugeGroup u → ∀ c : BondAtLevel L m K j,
      IsBareIterateDefined s U j c →
        iteratedAverage s j (gaugeTransform u U) c =
          gaugeTransform (fun y => u (finestBaseSite s K j y)) (iteratedAverage s j U) c
  local_at : ∀ U ∈ gaugeFieldsAtLevel L m K 0, ∀ U' ∈ gaugeFieldsAtLevel L m K 0,
    ∀ c : BondAtLevel L m K j,
      (∀ e ∈ bondsInside (refinedBlock j c.source ∪ refinedBlock j c.target), U e = U' e) →
        (IsBareIterateDefined s U j c ↔ IsBareIterateDefined s U' j c) ∧
          (IsBareIterateDefined s U j c → iteratedAverage s j U c = iteratedAverage s j U' c)
def AveragingSchemeProperties : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ m K n : ℕ, 0 < m → n < K →
    ∀ s : AveragingScheme,
    (∀ y : SiteAtLevel L m K (n + 1), ∀ x ∈ sitesInBlock (levelDepth K n) y,
      BlockPathProperties y x ∧ ContourHolonomyIsLocal s y x) ∧
    (∀ c : BondAtLevel L m K (n + 1), c.IsPositivelyOriented →
      DoubleBlockStraightPaths s c ∧ SchemeDomainProperties s c ∧ CentredDomainAgreement c ∧
      (∀ W ∈ (schemeHolomorphyDomain s c : Set (BondAtLevel L m K n → Matrices.ComplexMatrix2)),
        IsGaugeField compactGaugeGroup (bondsInDoubleBlock c) W → SchemeValuesCompact s W c) ∧
      (∀ W : BondAtLevel L m K n → Matrices.ComplexMatrix2,
        IsGaugeField compactGaugeGroup (bondsInDoubleBlock c) W →
        doubleBlockCurvature W c < Averaging.smoothingRadius L →
        CentredSchemeAgreesWithAverage W c) ∧
      ∀ (g : SiteAtLevel L m K n → Matrices.ComplexMatrix2)
        (W : BondAtLevel L m K n → Matrices.ComplexMatrix2),
        (∀ x : SiteAtLevel L m K n, (x : FourTorus L m) ∈ bondDoubleBlock c →
          g x ∈ compactGaugeGroup) →
        IsGaugeField complexGaugeGroup (bondsInDoubleBlock c) W → SchemeGaugeCovariance s g W c) ∧
    ∀ j : ℕ, j ≤ K → IteratedAverageProperties L m K s j
end PeriodicLattice
end YangMills.Construction
