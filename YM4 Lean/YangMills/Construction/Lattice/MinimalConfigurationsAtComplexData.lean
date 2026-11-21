import YangMills.Construction.Averaging.SmoothingRadius
import YangMills.Construction.Lattice.BlockAxialGaugeOutsideTheNodes
import YangMills.Construction.Lattice.ExponentialActionAndComplexData
import YangMills.Construction.Lattice.RegularRealData
import YangMills.Construction.Matrices.GroupLieProducts
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
namespace PeriodicLattice
variable {L m : ℕ}
def IsActiveComplexDatum (K k : ℕ) (Ω : ℕ → Set (FourTorus L m))
    (X : ∀ j : ℕ, BondAtLevel L m K j → Matrices.ComplexMatrix2) : Prop :=
  IsComplexCutDatum K k Ω (inwardPointingBonds K k Ω) X
abbrev PositiveBondIn {K : ℕ} (S : Set (Σ j : ℕ, BondAtLevel L m K j)) : Type :=
  {q : Σ j : ℕ, BondAtLevel L m K j // q ∈ S ∧ q.2.IsPositivelyOriented}
def familyAtLevel {K : ℕ} {S : Set (Σ j : ℕ, BondAtLevel L m K j)}
    (B : PositiveBondIn S → Matrices.ComplexMatrix2) (j : ℕ) :
    BondAtLevel L m K j → Matrices.ComplexMatrix2 :=
  open Classical in
  fun b => if h : (⟨j, b⟩ : Σ j : ℕ, BondAtLevel L m K j) ∈ S ∧ b.IsPositivelyOriented then
    B ⟨⟨j, b⟩, h⟩ else 0
def expTwistedDatum {K : ℕ} {S : Set (Σ j : ℕ, BondAtLevel L m K j)}
    (B : PositiveBondIn S → Matrices.ComplexMatrix2)
    (V₀ : ∀ j : ℕ, BondAtLevel L m K j → Matrices.ComplexMatrix2) :
    ∀ j : ℕ, BondAtLevel L m K j → Matrices.ComplexMatrix2 :=
  fun j => expTwist (familyAtLevel B j) (V₀ j)
def complexFamilyBall {K : ℕ} (S : Set (Σ j : ℕ, BondAtLevel L m K j)) (r : ℝ) :
    Set (PositiveBondIn S → Matrices.ComplexMatrix2) :=
  Matrices.GroupLieProduct.supBall (PositiveBondIn S) r
def IsRealFamily {K : ℕ} {S : Set (Σ j : ℕ, BondAtLevel L m K j)}
    (B : PositiveBondIn S → Matrices.ComplexMatrix2) : Prop :=
  ∀ q, B q ∈ compactLieAlgebra
def activeRegularRealFields (εBar : ℝ) (K k : ℕ) (Ω : ℕ → Set (FourTorus L m)) :
    Set (∀ j : ℕ, BondAtLevel L m K j → Matrices.ComplexMatrix2) :=
  regularRealFields (Averaging.smoothingRadius L) εBar K k Ω (activeBondsAt K k Ω)
def towerAxialGaugeAwayFromEndpoints (K k : ℕ) (Ω : ℕ → Set (FourTorus L m))
    (S : Set (Σ j : ℕ, BondAtLevel L m K j)) :
    Set (BondAtLevel L m K 0 → Matrices.ComplexMatrix2) :=
  {U | U ∈ gaugeFieldsInside K (Ω 0) ∧
    ∀ i, 1 ≤ i → i ≤ k → ∀ xᵢ ∈ annulusSites K k Ω i, ∀ n < i,
      ∀ z : SiteAtLevel L m K (n + 1), (z : FourTorus L m) ∈ refinedBlock (i - n - 1) xᵢ →
        ∀ x ∈ sitesInBlock (levelDepth K n) z, ¬IsEndpointOf S (x : FourTorus L m) →
          pathHolonomy (averagingOnDeterminingSet (Averaging.smoothingRadius L) K (Ω 0) U n)
            (combToBlockSite z x) = 1}
def IsActiveGaugeRepresentative (ε : ℝ) (K k : ℕ) (Ω : ℕ → Set (FourTorus L m))
    (V : ∀ j : ℕ, BondAtLevel L m K j → Matrices.ComplexMatrix2)
    (U : BondAtLevel L m K 0 → Matrices.ComplexMatrix2) : Prop :=
  U ∈ regularConstrainedCriticalSet (Averaging.smoothingRadius L) ε K k Ω (activeBondSet K k Ω) V ∧
    U ∈ towerAxialGaugeAwayFromEndpoints K k Ω (activeBondSet K k Ω)
def HasActiveCriticalOrbit (ε : ℝ) (K k : ℕ) (Ω : ℕ → Set (FourTorus L m))
    (V : ∀ j : ℕ, BondAtLevel L m K j → Matrices.ComplexMatrix2) : Prop :=
  HasUniqueCriticalOrbit (Averaging.smoothingRadius L) ε K k Ω (activeBondSet K k Ω) V
def HasActiveGaugeRepresentative (ε : ℝ) (K k : ℕ) (Ω : ℕ → Set (FourTorus L m))
    (V : ∀ j : ℕ, BondAtLevel L m K j → Matrices.ComplexMatrix2) : Prop :=
  HasActiveCriticalOrbit ε K k Ω V ∧ ∃! U, IsActiveGaugeRepresentative ε K k Ω V U
def activeGaugeRepresentative (ε : ℝ) (K k : ℕ) (Ω : ℕ → Set (FourTorus L m))
    (V : ∀ j : ℕ, BondAtLevel L m K j → Matrices.ComplexMatrix2) :
    BondAtLevel L m K 0 → Matrices.ComplexMatrix2 :=
  Classical.epsilon (IsActiveGaugeRepresentative ε K k Ω V)
abbrev ActiveFamily (L m K k : ℕ) (Ω : ℕ → Set (FourTorus L m)) : Type :=
  PositiveBondIn (activeBondSet K k Ω) → Matrices.ComplexMatrix2
def IsHolomorphicContinuation (ε rB : ℝ) (K k : ℕ) (Ω : ℕ → Set (FourTorus L m))
    (V₀ : ∀ j : ℕ, BondAtLevel L m K j → Matrices.ComplexMatrix2)
    (Φ : ActiveFamily L m K k Ω → BondAtLevel L m K 0 → Matrices.ComplexMatrix2) : Prop :=
  (∃ _ : Fintype (PositiveBondIn (activeBondSet K k Ω)),
    ∀ (b : Module.Basis (Fin 3) ℂ Matrices.ComplexMatrix2.traceless),
      ∀ c ∈ (bondsInside (Ω 0) : Set (BondAtLevel L m K 0)),
        Matrices.GroupLieProduct.IsHolomorphicOnTraceless b
          Coordinates.ComplexCoordinates.matrixEquiv
          (complexFamilyBall (activeBondSet K k Ω) rB) fun B => Φ B c) ∧
    (∀ B ∈ complexFamilyBall (activeBondSet K k Ω) rB,
      IsGaugeField complexGaugeGroup (bondsInside (Ω 0)) (Φ B) ∧
        ∀ c ∉ (bondsInside (Ω 0) : Set (BondAtLevel L m K 0)), Φ B c = 1) ∧
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ rB ∧ ∀ B : ActiveFamily L m K k Ω, IsRealFamily B →
      Matrices.GroupLieProduct.supNorm B < ρ →
        HasActiveCriticalOrbit ε K k Ω (expTwistedDatum B V₀) →
        Φ B = activeGaugeRepresentative ε K k Ω (expTwistedDatum B V₀)
def holomorphicContinuation (ε rB : ℝ) (K k : ℕ) (Ω : ℕ → Set (FourTorus L m))
    (V₀ : ∀ j : ℕ, BondAtLevel L m K j → Matrices.ComplexMatrix2) :
    ActiveFamily L m K k Ω → BondAtLevel L m K 0 → Matrices.ComplexMatrix2 :=
  Classical.epsilon (IsHolomorphicContinuation ε rB K k Ω V₀)
def criticalFieldAtComplexDatum (ε rB : ℝ) (K k : ℕ) (Ω : ℕ → Set (FourTorus L m))
    (V₀ : ∀ j : ℕ, BondAtLevel L m K j → Matrices.ComplexMatrix2) (B : ActiveFamily L m K k Ω) :
    BondAtLevel L m K 0 → Matrices.ComplexMatrix2 :=
  holomorphicContinuation ε rB K k Ω V₀ B
def blockwiseGauge (K k : ℕ) (Ω : ℕ → Set (FourTorus L m))
    (v : SiteAtLevel L m K 0 → Matrices.ComplexMatrix2) :
    SiteAtLevel L m K 0 → Matrices.ComplexMatrix2 :=
  open Classical in
  fun x =>
    if h : ∃ j, j ≤ k ∧ ∃ y ∈ annulusSites K k Ω j, (x : FourTorus L m) ∈ refinedBlock j y then
      v (h.choose_spec.2.choose.toSublattice (levelDepth K 0))
    else 1
def ComplexAverageIsDefined (K : ℕ) (ℬ : Set (BondAtLevel L m K 0))
    (U : BondAtLevel L m K 0 → Matrices.ComplexMatrix2) :
    ∀ j : ℕ, BondAtLevel L m K j → Prop
  | 0, b => b ∈ ℬ
  | j + 1, c => ∀ c' : BondAtLevel L m K (j + 1), (c' = c ∨ c' = c.opposite) →
      c'.IsPositivelyOriented →
      (∀ b ∈ (bondsInDoubleBlock c' : Set (BondAtLevel L m K j)),
        ComplexAverageIsDefined K ℬ U j b) ∧
        complexBlockFieldAtLevel j U ∈ complexAveragingDomainNearOne c'
def complexBlockDatum (K : ℕ) (X : Set (FourTorus L m))
    (U : BondAtLevel L m K 0 → Matrices.ComplexMatrix2) (j : ℕ) :
    BondAtLevel L m K j → Matrices.ComplexMatrix2 :=
  complexBlockFieldAtLevel j (extendByOne (bondsInside X) U)
def HasComplexBlockDatum (K n : ℕ) (Ω' : ℕ → Set (FourTorus L m)) (X : Set (FourTorus L m))
    (U : BondAtLevel L m K 0 → Matrices.ComplexMatrix2) : Prop :=
  ∀ q ∈ activeBondSet K n Ω',
    ComplexAverageIsDefined K (bondsInside X) (extendByOne (bondsInside X) U) q.1 q.2
def IsPolarDecomposition (ξ : ℝ) (K : ℕ) (X : Set (FourTorus L m))
    (W U : BondAtLevel L m K 0 → Matrices.ComplexMatrix2) : Prop :=
  U ∈ gaugeFieldsInside K X ∧ IsGaugeField complexGaugeGroup (bondsInside X) W ∧
    ∃ A' : BondAtLevel L m K 0 → Matrices.ComplexMatrix2, IsBondForm complexLieAlgebra A' ∧
      W = extendByOne (bondsInside X) (expTwist ((ξ : ℂ) • A') U)
def logRatioFamily (K n : ℕ) (Ω' : ℕ → Set (FourTorus L m)) (X : Set (FourTorus L m))
    (W U : BondAtLevel L m K 0 → Matrices.ComplexMatrix2) : ActiveFamily L m K n Ω' :=
  fun q => (Complex.I)⁻¹ • Matrices.ComplexMatrix2.logSeries (complexBlockDatum K X W q.1.1 q.1.2 *
    (averagingOnDeterminingSet (Averaging.smoothingRadius L) K X U q.1.1 q.1.2)⁻¹)
def HasTowerField (ε εBar rB ξ : ℝ) (K n : ℕ) (Ω' : ℕ → Set (FourTorus L m))
    (X : Set (FourTorus L m)) (W U : BondAtLevel L m K 0 → Matrices.ComplexMatrix2) : Prop :=
  IsPolarDecomposition ξ K X W U ∧ HasComplexBlockDatum K n Ω' X W ∧
    averagingOnDeterminingSet (Averaging.smoothingRadius L) K X U ∈
      activeRegularRealFields εBar K n Ω' ∧
    HasActiveGaugeRepresentative ε K n Ω'
      (averagingOnDeterminingSet (Averaging.smoothingRadius L) K X U) ∧
    (∀ q ∈ activeBondSet K n Ω',
      Matrices.ComplexMatrix2.operatorNorm (complexBlockDatum K X W q.1 q.2 *
        (averagingOnDeterminingSet (Averaging.smoothingRadius L) K X U q.1 q.2)⁻¹ - 1) < 1) ∧
    logRatioFamily K n Ω' X W U ∈ complexFamilyBall (activeBondSet K n Ω') rB
def towerField (ε rB : ℝ) (K n : ℕ) (Ω' : ℕ → Set (FourTorus L m)) (X : Set (FourTorus L m))
    (W U : BondAtLevel L m K 0 → Matrices.ComplexMatrix2) :
    BondAtLevel L m K 0 → Matrices.ComplexMatrix2 :=
  criticalFieldAtComplexDatum ε rB K n Ω'
    (averagingOnDeterminingSet (Averaging.smoothingRadius L) K X U)
    (logRatioFamily K n Ω' X W U)
def towerFieldCurrent (ε rB : ℝ) (K n : ℕ) (Ω' : ℕ → Set (FourTorus L m))
    (X : Set (FourTorus L m)) (W U : BondAtLevel L m K 0 → Matrices.ComplexMatrix2) :
    BondAtLevel L m K 0 → Matrices.ComplexMatrix2 :=
  yangMillsCurrent (finestMeshInLevelUnits L n) (towerField ε rB K n Ω' X W U)
end PeriodicLattice
end YangMills.Construction
