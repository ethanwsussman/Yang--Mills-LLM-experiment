import YangMills.Construction.Lattice.BlockAveraging
import YangMills.Construction.Lattice.CoordinateCombs
import Mathlib
noncomputable section
namespace YangMills.Construction
namespace PeriodicLattice
inductive AveragingScheme
  | centred
  | cornered
variable {L m : ℕ} {j j' : ℤ}
def centreToFaceSteps (L : ℕ) : ℤ := ((L : ℤ) - 1) / 2
def schemeBaseSite (s : AveragingScheme) (j' : ℤ) (y : Site L m j) : Site L m j' :=
  match s with
  | .centred => y.toSublattice j'
  | .cornered => y.toSublattice j' - centreToFaceSteps L • ∑ μ, unitStep L m j' μ
def finestBaseSite (s : AveragingScheme) (K : ℕ) : (j : ℕ) → SiteAtLevel L m K j → SiteAtLevel L m K 0
  | 0, y => y
  | j + 1, y => finestBaseSite s K j (schemeBaseSite s (levelDepth K j) y)
def contourHolonomy (s : AveragingScheme) (W : Bond L m j' → Matrices.ComplexMatrix2)
    (y : Site L m j) (x : Site L m j') : Matrices.ComplexMatrix2 :=
  match s with
  | .centred => complexMeanContourHolonomy W y x
  | .cornered => pathHolonomy W (coordinateComb (schemeBaseSite .cornered j' y) x)
def IsContourHolonomyDefined (s : AveragingScheme) (W : Bond L m j' → Matrices.ComplexMatrix2)
    (y : Site L m j) (x : Site L m j') : Prop :=
  x ∈ sitesInBlock j' y ∧ IsGaugeField complexGaugeGroup (bondsInside (unitBlock y)) W ∧
    match s with
    | .centred => Matrices.ComplexMatrix2.familyDiameter (contourHolonomies W y x) <
        Averaging.centreOfMassDiameter
    | .cornered => True
def contourFormMean (s : AveragingScheme) (a : Bond L m j' → Matrices.ComplexMatrix2)
    (y : Site L m j) (x : Site L m j') : Matrices.ComplexMatrix2 :=
  match s with
  | .centred => contourFormAverage a y x
  | .cornered => bondFormSumAlong a (coordinateComb (schemeBaseSite .cornered j' y) x)
def baseTransport (s : AveragingScheme) (W : Bond L m j' → Matrices.ComplexMatrix2)
    (c : Bond L m j) : Matrices.ComplexMatrix2 :=
  pathHolonomy W (axialPath (schemeBaseSite s j' c.source) (schemeBaseSite s j' c.target))
def localDefect (s : AveragingScheme) (W : Bond L m j' → Matrices.ComplexMatrix2) (c : Bond L m j)
    (x : Site L m j') : Matrices.ComplexMatrix2 :=
  contourHolonomy s W c.source x * pathHolonomy W (crossingPath c x) *
    (contourHolonomy s W c.target (shiftAcross c x))⁻¹ * (baseTransport s W c)⁻¹
def AreContourHolonomiesDefined (s : AveragingScheme) (W : Bond L m j' → Matrices.ComplexMatrix2)
    (c : Bond L m j) : Prop :=
  (∀ x ∈ sitesInBlock j' c.source, IsContourHolonomyDefined s W c.source x) ∧
    ∀ x ∈ sitesInBlock j' c.target, IsContourHolonomyDefined s W c.target x
def IsSchemeAverageDefined (s : AveragingScheme) (W : Bond L m j' → Matrices.ComplexMatrix2)
    (c : Bond L m j) : Prop :=
  IsGaugeField complexGaugeGroup (bondsInDoubleBlock c) W ∧ AreContourHolonomiesDefined s W c ∧
    ∀ x ∈ sitesInBlock j' c.source,
      Matrices.ComplexMatrix2.operatorNorm (localDefect s W c x - 1) < 1
def positiveBondAverage (s : AveragingScheme) (W : Bond L m j' → Matrices.ComplexMatrix2)
    (c : Bond L m j) : Matrices.ComplexMatrix2 :=
  Matrices.ComplexMatrix2.matExp (inverseFourthPowerWeight L •
      ∑ᶠ x ∈ sitesInBlock j' c.source, Matrices.ComplexMatrix2.logSeries (localDefect s W c x)) *
    baseTransport s W c
def schemeBlockAverage (s : AveragingScheme) (W : Bond L m j' → Matrices.ComplexMatrix2) :
    Bond L m j → Matrices.ComplexMatrix2 :=
  open Classical in
  fun c => if c.IsPositivelyOriented then positiveBondAverage s W c
    else (positiveBondAverage s W c.opposite)⁻¹
section Iterates
variable {K : ℕ}
def levelAverage (s : AveragingScheme) (k : ℕ) (W : BondAtLevel L m K k → Matrices.ComplexMatrix2) :
    BondAtLevel L m K (k + 1) → Matrices.ComplexMatrix2 :=
  schemeBlockAverage s W
def iteratedAverage (s : AveragingScheme) (k : ℕ) (U : BondAtLevel L m K 0 → Matrices.ComplexMatrix2) :
    BondAtLevel L m K k → Matrices.ComplexMatrix2 :=
  iterateFromBare (levelAverage s) k U
def iteratedAverageDomain (s : AveragingScheme) :
    (k : ℕ) → Set (BondAtLevel L m K 0 → Matrices.ComplexMatrix2)
  | 0 => Set.univ
  | k + 1 => {U | U ∈ iteratedAverageDomain s k ∧ ∀ c : BondAtLevel L m K (k + 1),
      c.IsPositivelyOriented → IsSchemeAverageDefined s (iteratedAverage s k U) c}
end Iterates
def doubleBlockCurvature (W : Bond L m j' → Matrices.ComplexMatrix2) (c : Bond L m j) : ℝ :=
  ⨆ p : ↥(doubleBlockPlaquettes c : Set (Plaquette L m j')),
    Matrices.ComplexMatrix2.operatorNorm (plaquetteHolonomy W p.1 - 1)
def maxCurvature (W : Bond L m j' → Matrices.ComplexMatrix2) : ℝ :=
  ⨆ p : Plaquette L m j', Matrices.ComplexMatrix2.operatorNorm (plaquetteHolonomy W p - 1)
end PeriodicLattice
end YangMills.Construction
