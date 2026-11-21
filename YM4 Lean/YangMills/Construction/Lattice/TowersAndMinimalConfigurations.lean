import YangMills.Construction.Lattice.AnnulusSites
import YangMills.Construction.Lattice.AveragingOnPart
import YangMills.Construction.Lattice.CubePartitionsAndRegions
import YangMills.Construction.Lattice.LiftOfBlockFields
import YangMills.Construction.Lattice.WilsonGibbsMeasure
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.PeriodicLattice
variable {L m : ℕ}
def IsDeterminingChain (K k : ℕ) (Ω : ℕ → Set (FourTorus L m)) : Prop :=
  (∀ j < k, Ω (j + 1) ⊆ Ω j) ∧
    ∀ j ≤ k, ∃ i : ℤ, -(m : ℤ) ≤ i ∧ i ≤ levelDepth K j ∧ IsPartitionRegion i (Ω j)
def determiningBondsAt (K k : ℕ) (Ω : ℕ → Set (FourTorus L m)) (j : ℕ) :
    Set (BondAtLevel L m K j) :=
  {b | (b.source ∈ annulusSites K k Ω j ∨ b.target ∈ annulusSites K k Ω j) ∧
    b ∈ bondsInside (Ω 0)}
def determiningBondSet (K k : ℕ) (Ω : ℕ → Set (FourTorus L m)) :
    Set (Σ j : ℕ, BondAtLevel L m K j) :=
  {q | q.1 ≤ k ∧ q.2 ∈ determiningBondsAt K k Ω q.1}
def determiningSetSupport (Ω : ℕ → Set (FourTorus L m)) : Set (FourTorus L m) := Ω 1
def IsDeterminingDatum (K k : ℕ) (Ω : ℕ → Set (FourTorus L m))
    (V : ∀ j : ℕ, BondAtLevel L m K j → Matrices.ComplexMatrix2) : Prop :=
  ∀ j ≤ k, IsGaugeField compactGaugeGroup (determiningBondsAt K k Ω j) (V j)
def averagingOnDeterminingSet (ω : ℝ) (K : ℕ) (X : Set (FourTorus L m))
    (U : BondAtLevel L m K 0 → Matrices.ComplexMatrix2) (j : ℕ) :
    BondAtLevel L m K j → Matrices.ComplexMatrix2 :=
  blockFieldAtLevel ω j (extendByOne (bondsInside X) U)
def IsDeterminingNode (K k : ℕ) (Ω : ℕ → Set (FourTorus L m)) (x : FourTorus L m) : Prop :=
  x ∈ Ω 0 ∧ ∃ q ∈ determiningBondSet K k Ω,
    (q.2.source : FourTorus L m) = x ∨ (q.2.target : FourTorus L m) = x
def cubesOfIndex (c : ℤ) : Set (Set (FourTorus L m)) :=
  {Q | -(m : ℤ) ≤ c ∧ Q ∈ standardCubePartition L m c}
def IsUnionOfCubesOfIndex (c : ℤ) (X : Set (FourTorus L m)) : Prop :=
  ∃ C ⊆ cubesOfIndex c, X = ⋃₀ C
def IsRegionAtLevel (K n i : ℕ) (Ω : Set (FourTorus L m)) : Prop :=
  ∃ c : ℤ, -(m : ℤ) ≤ c ∧ c ≤ scaledCubeIndex K i n ∧ IsPartitionRegion c Ω
def supDistInLevelUnits (K i : ℕ) (A B : Set (FourTorus L m)) : ℝ≥0∞ :=
  ENNReal.ofReal ((L : ℝ) ^ levelDepth K i) * TorusMetric.setSupDist A B
def separationGap (L e r i q : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal ((L : ℝ) ^ r * (L : ℝ) ^ e * (L : ℝ) ^ ((q : ℤ) - (i : ℤ)))
def shrinkingGap (L n i q : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal ((L : ℝ) ^ n * (L : ℝ) ^ ((q : ℤ) + 1 - (i : ℤ)))
def separatedTowerStep (K e r i q : ℕ) (X : Set (FourTorus L m)) : Set (FourTorus L m) :=
  ⋃₀ {Q | Q ∈ cubesOfIndex (scaledCubeIndex K (q + 1) e) ∧ Q ⊆ X ∧
    separationGap L e r i q <
      supDistInLevelUnits K i Q (complementRegion (scaledCubeIndex K q e) X)}
def shrinkingTowerStep (K n i q : ℕ) (X : Set (FourTorus L m)) : Set (FourTorus L m) :=
  ⋃₀ {Q | Q ∈ cubesOfIndex (scaledCubeIndex K (q + 1) n) ∧ Q ⊆ X ∧
    shrinkingGap L n i q ≤
      supDistInLevelUnits K i Q (complementRegion (scaledCubeIndex K q n) X)}
def towerByRule (rule : ℕ → Set (FourTorus L m) → Set (FourTorus L m)) (i : ℕ)
    (Ω : Set (FourTorus L m)) : ℕ → Set (FourTorus L m)
  | 0 => Ω
  | p + 1 => rule (i + p) (towerByRule rule i Ω p)
def separatedTower (K e r i : ℕ) (Ω : Set (FourTorus L m)) : ℕ → Set (FourTorus L m) :=
  towerByRule (separatedTowerStep K e r i) i Ω
def shrinkingTower (K n i : ℕ) (Ω : Set (FourTorus L m)) : ℕ → Set (FourTorus L m) :=
  towerByRule (shrinkingTowerStep K n i) i Ω
def IsSeparatedChain (K e r i n : ℕ) (Ω : ℕ → Set (FourTorus L m)) : Prop :=
  (∀ q, i ≤ q → q ≤ i + n → IsUnionOfCubesOfIndex (scaledCubeIndex K q e) (Ω q)) ∧
    ∀ q, i ≤ q → q < i + n → Ω (q + 1) ⊆ Ω q ∧
      separationGap L e r i q <
        supDistInLevelUnits K i (complementRegion (scaledCubeIndex K q e) (Ω q)) (Ω (q + 1))
def minimalBondSet (K n j : ℕ) (Ω : Set (FourTorus L m)) :
    Set (Σ q : ℕ, BondAtLevel L m K q) :=
  determiningBondSet K j (shrinkingTower K n 0 Ω)
def gaugeFieldsInside (K : ℕ) (X : Set (FourTorus L m)) :
    Set (BondAtLevel L m K 0 → Matrices.ComplexMatrix2) :=
  {U | IsGaugeField compactGaugeGroup (bondsInside X) U ∧ ∀ b ∉ bondsInside X, U b = 1}
def constrainedFields (ω : ℝ) (K k : ℕ) (Ω : ℕ → Set (FourTorus L m))
    (V : ∀ j : ℕ, BondAtLevel L m K j → Matrices.ComplexMatrix2) :
    Set (BondAtLevel L m K 0 → Matrices.ComplexMatrix2) :=
  {U | U ∈ gaugeFieldsInside K (Ω 0) ∧
    ∀ j ≤ k, ∀ b ∈ determiningBondsAt K k Ω j,
      averagingOnDeterminingSet ω K (Ω 0) U j b = V j b}
def actionInside (K : ℕ) (X : Set (FourTorus L m))
    (U : BondAtLevel L m K 0 → Matrices.ComplexMatrix2) : ℝ :=
  ∑ᶠ p ∈ (plaquettesInside X : Set (PlaquetteAtLevel L m K 0)), plaquetteCost U p
def residualGauge (K k : ℕ) (Ω : ℕ → Set (FourTorus L m)) :
    Set (SiteAtLevel L m K 0 → Matrices.ComplexMatrix2) :=
  {u | (∀ x ∈ (sitesIn (Ω 0) : Set (SiteAtLevel L m K 0)), u x ∈ compactGaugeGroup) ∧
    (∀ x ∉ (sitesIn (Ω 0) : Set (SiteAtLevel L m K 0)), u x = 1) ∧
    ∀ x : SiteAtLevel L m K 0, IsDeterminingNode K k Ω (x : FourTorus L m) → u x = 1}
def residualGaugeOrbit (K k : ℕ) (Ω : ℕ → Set (FourTorus L m))
    (U : BondAtLevel L m K 0 → Matrices.ComplexMatrix2) :
    Set (BondAtLevel L m K 0 → Matrices.ComplexMatrix2) :=
  {W | ∃ u ∈ residualGauge K k Ω, W = extendByOne (bondsInside (Ω 0)) (gaugeTransform u U)}
def IsCriticalForAction (ω : ℝ) (K k : ℕ) (Ω : ℕ → Set (FourTorus L m))
    (V : ∀ j : ℕ, BondAtLevel L m K j → Matrices.ComplexMatrix2)
    (U : BondAtLevel L m K 0 → Matrices.ComplexMatrix2) : Prop :=
  U ∈ constrainedFields ω K k Ω V ∧
    ∀ (δ : ℝ) (γ : ℝ → BondAtLevel L m K 0 → Matrices.ComplexMatrix2), 0 < δ →
      (∀ t ∈ Ioo (-δ) δ, γ t ∈ constrainedFields ω K k Ω V) →
      (∀ b r s, DifferentiableOn ℝ (fun t => γ t b r s) (Ioo (-δ) δ)) → γ 0 = U →
      deriv (fun t => actionInside K (Ω 0) (γ t)) 0 = 0
def localScale (L k : ℕ) (Ω : ℕ → Set (FourTorus L m)) (C : Set (FourTorus L m)) : ℝ :=
  (L : ℝ) ^ (((sSup {j | j ≤ k ∧ (C ∩ Ω j).Nonempty} : ℕ) : ℤ) - (k : ℤ))
def HasCurrentAt (K : ℕ) (X : Set (FourTorus L m)) (b : BondAtLevel L m K 0) : Prop :=
  ∀ p : PlaquetteAtLevel L m K 0, (b ∈ p.boundaryBonds ∨ b.opposite ∈ p.boundaryBonds) →
    p ∈ (plaquettesInside X : Set (PlaquetteAtLevel L m K 0))
def IsRegularField (ε : ℝ) (K k : ℕ) (Ω : ℕ → Set (FourTorus L m))
    (U : BondAtLevel L m K 0 → Matrices.ComplexMatrix2) : Prop :=
  (∀ p ∈ (plaquettesInside (Ω 0) : Set (PlaquetteAtLevel L m K 0)),
    Matrices.ComplexMatrix2.operatorNorm (plaquetteHolonomy U p - 1) <
      ε * finestMeshInLevelUnits L k ^ 2 *
        (localScale L k Ω
          ((fun x : SiteAtLevel L m K 0 => (x : FourTorus L m)) '' p.vertices))⁻¹ ^ 2) ∧
    ∀ b ∈ (bondsMeeting (Ω 0) : Set (BondAtLevel L m K 0)), HasCurrentAt K (Ω 0) b →
      Matrices.ComplexMatrix2.operatorNorm (yangMillsCurrent (finestMeshInLevelUnits L k) U b) <
        ε * (localScale L k Ω {(b.source : FourTorus L m), (b.target : FourTorus L m)})⁻¹ ^ 3
def regularCriticalFields (ω ε : ℝ) (K k : ℕ) (Ω : ℕ → Set (FourTorus L m))
    (V : ∀ j : ℕ, BondAtLevel L m K j → Matrices.ComplexMatrix2) :
    Set (BondAtLevel L m K 0 → Matrices.ComplexMatrix2) :=
  {U | IsCriticalForAction ω K k Ω V U ∧ IsRegularField ε K k Ω U}
def CriticalFieldsFormOneOrbit (ω ε : ℝ) (K k : ℕ) (Ω : ℕ → Set (FourTorus L m))
    (V : ∀ j : ℕ, BondAtLevel L m K j → Matrices.ComplexMatrix2) : Prop :=
  ∃ U ∈ regularCriticalFields ω ε K k Ω V,
    regularCriticalFields ω ε K k Ω V = residualGaugeOrbit K k Ω U
def minimizingField (ω ε : ℝ) (K k : ℕ) (Ω : ℕ → Set (FourTorus L m))
    (V : ∀ j : ℕ, BondAtLevel L m K j → Matrices.ComplexMatrix2) :
    BondAtLevel L m K 0 → Matrices.ComplexMatrix2 :=
  Classical.epsilon fun U => U ∈ regularCriticalFields ω ε K k Ω V
def datumOnLevel (K k : ℕ) (V : BondAtLevel L m K k → Matrices.ComplexMatrix2) (j : ℕ) :
    BondAtLevel L m K j → Matrices.ComplexMatrix2 :=
  open Classical in
  if h : j = k then h ▸ V else fun _ => 1
def backgroundField (ω ε : ℝ) (K k : ℕ) (V : BondAtLevel L m K k → Matrices.ComplexMatrix2) :
    BondAtLevel L m K 0 → Matrices.ComplexMatrix2 :=
  minimizingField ω ε K k (fun _ => univ) (datumOnLevel K k V)
def domainChain (Ω : ℕ → Set (FourTorus L m)) : ℕ → Set (FourTorus L m)
  | 0 => univ
  | j + 1 => Ω (j + 1)
def domainBackground (ω ε : ℝ) (K k : ℕ) (Ω : ℕ → Set (FourTorus L m))
    (V : ∀ j : ℕ, BondAtLevel L m K j → Matrices.ComplexMatrix2) :
    BondAtLevel L m K 0 → Matrices.ComplexMatrix2 :=
  minimizingField ω ε K k (domainChain Ω) V
def localizedBackground (ω ε : ℝ) (K k n : ℕ) (Ω : Set (FourTorus L m))
    (V : BondAtLevel L m K k → Matrices.ComplexMatrix2) :
    BondAtLevel L m K 0 → Matrices.ComplexMatrix2 :=
  minimizingField ω ε K k (shrinkingTower K n 0 Ω)
    (averagingOnDeterminingSet ω K Ω (bareLift V))
end YangMills.Construction.PeriodicLattice
