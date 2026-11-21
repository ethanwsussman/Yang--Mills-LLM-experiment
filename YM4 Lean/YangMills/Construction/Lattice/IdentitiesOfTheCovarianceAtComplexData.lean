import YangMills.Construction.Lattice.ContinuationsFromRealData
import YangMills.Construction.Lattice.SetsOfBondsOfASequenceOfRegions
import Mathlib
set_option autoImplicit false
open Set Filter
open scoped Topology Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.PeriodicLattice
variable {L m : ℕ}
def fieldGaugePoint {j : ℤ} {S : Type} (ℬ : Set (Bond L m j))
    (U : Bond L m j → Matrices.ComplexMatrix2) (u : S → Matrices.ComplexMatrix2) :
    ↥ℬ ⊕ S → Matrices.ComplexMatrix2 :=
  Sum.elim (fun b => U b) u
def IsHolomorphicInFieldAndGauge {j : ℤ} {S : Type} (ℬ : Set (Bond L m j))
    (f : (Bond L m j → Matrices.ComplexMatrix2) → (S → Matrices.ComplexMatrix2) →
      Matrices.ComplexMatrix2) : Prop :=
  ∃ (_ : Fintype ↥ℬ) (_ : Fintype S), ∀ U ∈ complexGaugeFields ℬ,
    ∀ u : S → Matrices.ComplexMatrix2, (∀ x, u x ∈ complexGaugeGroup) →
      ∃ F : (↥ℬ ⊕ S → Matrices.ComplexMatrix2) → Matrices.ComplexMatrix2,
        AnalyticAt ℂ F (fieldGaugePoint ℬ U u) ∧
        ∀ᶠ w in 𝓝 (fieldGaugePoint ℬ U u), ∀ U' ∈ complexGaugeFields ℬ,
          ∀ u' : S → Matrices.ComplexMatrix2, (∀ x, u' x ∈ complexGaugeGroup) →
            fieldGaugePoint ℬ U' u' = w → f U' u' = F w
def complexInteriorFields (K : ℕ) (X : Set (FourTorus L m)) :
    Set (BondAtLevel L m K 0 → Matrices.ComplexMatrix2) :=
  {W | IsGaugeField complexGaugeGroup (bondsInside X) W ∧ ∀ b ∉ bondsInside X, W b = 1}
def complexStabilizerGroup {K : ℕ} (Ω : ℕ → Set (FourTorus L m))
    (B : Set (Σ j : ℕ, BondAtLevel L m K j)) :
    Set (SiteAtLevel L m K 0 → Matrices.ComplexMatrix2) :=
  {u | (∀ x ∈ (sitesIn (Ω 0) : Set (SiteAtLevel L m K 0)), u x ∈ complexGaugeGroup) ∧
    (∀ x ∉ (sitesIn (Ω 0) : Set (SiteAtLevel L m K 0)), u x = 1) ∧
    ∀ x : SiteAtLevel L m K 0, IsEndpointOf B (x : FourTorus L m) → u x = 1}
def InComplexStabilizerOrbit {K : ℕ} (Ω : ℕ → Set (FourTorus L m))
    (B : Set (Σ j : ℕ, BondAtLevel L m K j))
    (W₁ W₂ : BondAtLevel L m K 0 → Matrices.ComplexMatrix2) : Prop :=
  ∃ u ∈ complexStabilizerGroup Ω B,
    W₁ = extendByOne (bondsInside (Ω 0)) (gaugeTransform u W₂)
def complexConstraintSet (K k : ℕ) (Ω : ℕ → Set (FourTorus L m))
    (X : ∀ j : ℕ, BondAtLevel L m K j → Matrices.ComplexMatrix2) :
    Set (BondAtLevel L m K 0 → Matrices.ComplexMatrix2) :=
  {W | W ∈ complexInteriorFields K (Ω 0) ∧ HasComplexBlockDatum K k Ω (Ω 0) W ∧
    ∀ q ∈ activeBondSet K k Ω, complexBlockDatum K (Ω 0) W q.1 q.2 = X q.1 q.2}
def IsComplexBlockAxialGauge (K k : ℕ) (P'' : Set (SiteAtLevel L m K (k + 1)))
    (V : BondAtLevel L m K k → Matrices.ComplexMatrix2) : Prop :=
  k < K ∧ IsGaugeField complexGaugeGroup (blockBonds (levelDepth K k) P'') V ∧
    ∀ y ∈ P'', ∀ x ∈ sitesInBlock (levelDepth K k) y,
      Matrices.ComplexMatrix2.familyDiameter (contourHolonomies V y x) <
          Averaging.centreOfMassDiameter ∧
        ((x : FourTorus L m) ≠ y → complexMeanContourHolonomy V y x = 1)
def twistedActiveFamily (σ : FourTorus L m ≃ FourTorus L m) {K k : ℕ}
    {Ω : ℕ → Set (FourTorus L m)}
    (V₀ : ∀ j : ℕ, BondAtLevel L m K j → Matrices.ComplexMatrix2) (B : ActiveFamily L m K k Ω) :
    ActiveFamily L m K k (imageChain σ Ω) :=
  fun p => twistedFormValue σ (V₀ p.1.1) (familyAtLevel B p.1.1) p.1.2
def constraintSites (K k : ℕ) (Ω : ℕ → Set (FourTorus L m)) : Set (SiteAtLevel L m K 0) :=
  {x | ∃ j ≤ k, ∃ y ∈ annulusSites K k Ω j, (x : FourTorus L m) = y}
def continuedGaugeExtendedField (ε εBar rB : ℝ) (K k : ℕ)
    (Ω : ℕ → Set (FourTorus L m)) (V₀ : ∀ j : ℕ, BondAtLevel L m K j → Matrices.ComplexMatrix2)
    (B : ActiveFamily L m K k Ω) (v : SiteAtLevel L m K 0 → Matrices.ComplexMatrix2) :
    BondAtLevel L m K 0 → Matrices.ComplexMatrix2 :=
  extendByOne (bondsInside (Ω 0))
    (gaugeTransform (blockwiseGauge K k Ω v) (continuedMinimalField ε εBar rB K k Ω V₀ B))
def ComplexGaugeTransformCovariant (σ : FourTorus L m ≃ FourTorus L m) (j : ℤ) : Prop :=
  ∀ ℬ : Set (Bond L m j), ∀ b ∈ ℬ,
    IsHolomorphicInFieldAndGauge ℬ
      (fun U u => transportGaugeField σ (gaugeTransform u U) (bondImage σ b)) ∧
    IsHolomorphicInFieldAndGauge ℬ
      (fun U u => gaugeTransform (transportSiteFunction σ u) (transportGaugeField σ U)
        (bondImage σ b)) ∧
    ∀ U ∈ complexGaugeFields ℬ, ∀ u, IsGaugeMap complexGaugeGroup u →
      transportGaugeField σ (gaugeTransform u U) (bondImage σ b) =
        gaugeTransform (transportSiteFunction σ u) (transportGaugeField σ U) (bondImage σ b)
def ComplexDatumGaugeCovariant (σ : FourTorus L m ≃ FourTorus L m) (K k : ℕ)
    (Ω : ℕ → Set (FourTorus L m)) : Prop :=
  ∀ q ∈ activeBondSet K k Ω,
    IsHolomorphicInFieldAndGauge (activeBondsAt K k Ω q.1)
      (fun Y (v : SiteAtLevel L m K 0 → Matrices.ComplexMatrix2) =>
        transportGaugeField σ (gaugeTransform (restrictGaugeMap q.1 v) Y)
        (bondImage σ q.2)) ∧
    IsHolomorphicInFieldAndGauge (activeBondsAt K k Ω q.1)
      (fun Y (v : SiteAtLevel L m K 0 → Matrices.ComplexMatrix2) =>
        gaugeTransform (restrictGaugeMap q.1 (transportSiteFunction σ v))
        (transportGaugeField σ Y) (bondImage σ q.2)) ∧
    ∀ X, IsActiveComplexDatum K k Ω X → ∀ v : SiteAtLevel L m K 0 → Matrices.ComplexMatrix2,
      IsGaugeMap complexGaugeGroup v →
        datumImage σ (gaugeTransformDatum v X) q.1 (bondImage σ q.2) =
          gaugeTransformDatum (transportSiteFunction σ v) (datumImage σ X) q.1 (bondImage σ q.2)
def ComplexStabilizerCovariant (σ : FourTorus L m ≃ FourTorus L m) (K k : ℕ)
    (Ω : ℕ → Set (FourTorus L m)) : Prop :=
  complexStabilizerGroup (imageChain σ Ω) (activeBondSet K k (imageChain σ Ω)) =
    transportSiteFunction σ '' complexStabilizerGroup Ω (activeBondSet K k Ω)
def ComplexConstraintSetCovariant (σ : FourTorus L m ≃ FourTorus L m) (K k : ℕ)
    (Ω : ℕ → Set (FourTorus L m)) : Prop :=
  Matrices.ComplexMatrix2.IsRelativelyOpen (complexInteriorFields K (Ω 0))
      {W | W ∈ complexInteriorFields K (Ω 0) ∧ HasComplexBlockDatum K k Ω (Ω 0) W ∧
        HasComplexBlockDatum K k (imageChain σ Ω) (imageChain σ Ω 0)
          (transportGaugeField σ W)} ∧
    (∀ X, IsActiveComplexDatum K k Ω X → ∀ W ∈ complexInteriorFields K (Ω 0),
      HasComplexBlockDatum K k Ω (Ω 0) W →
      HasComplexBlockDatum K k (imageChain σ Ω) (imageChain σ Ω 0)
        (transportGaugeField σ W) →
      (W ∈ complexConstraintSet K k Ω X ↔
        transportGaugeField σ W ∈
          complexConstraintSet K k (imageChain σ Ω) (datumImage σ X))) ∧
    (IsTorusTranslation σ → ∀ X, IsActiveComplexDatum K k Ω X →
      transportGaugeField σ '' complexConstraintSet K k Ω X =
        complexConstraintSet K k (imageChain σ Ω) (datumImage σ X))
def ContinuedMinimalFieldCovariant (σ : FourTorus L m ≃ FourTorus L m) (ε εBar rB : ℝ)
    (K k : ℕ) (Ω : ℕ → Set (FourTorus L m))
    (V₀ : ∀ j : ℕ, BondAtLevel L m K j → Matrices.ComplexMatrix2) : Prop :=
  HasUniqueMinimizerContinuation ε εBar rB K k Ω V₀ →
  HasUniqueMinimizerContinuation ε εBar rB K k (imageChain σ Ω) (datumImage σ V₀) →
    (∃ (_ : Fintype (PositiveBondIn (activeBondSet K k Ω)))
      (_ : Fintype (bondsInside (imageChain σ Ω 0) : Set (BondAtLevel L m K 0))),
      IsHolomorphicMatrixValued (complexFamilyBall (activeBondSet K k Ω) rB)
        (fun (B : ActiveFamily L m K k Ω)
            (c : (bondsInside (imageChain σ Ω 0) : Set (BondAtLevel L m K 0))) =>
          continuedMinimalField ε εBar rB K k (imageChain σ Ω)
            (datumImage σ V₀) (twistedActiveFamily σ V₀ B) c) ∧
      IsHolomorphicMatrixValued (complexFamilyBall (activeBondSet K k Ω) rB)
        (fun (B : ActiveFamily L m K k Ω)
            (c : (bondsInside (imageChain σ Ω 0) : Set (BondAtLevel L m K 0))) =>
          transportGaugeField σ
            (continuedMinimalField ε εBar rB K k Ω V₀ B) c)) ∧
    ∀ B ∈ complexFamilyBall (activeBondSet K k Ω) rB,
      twistedActiveFamily σ V₀ B ∈
          complexFamilyBall (activeBondSet K k (imageChain σ Ω)) rB ∧
      InComplexStabilizerOrbit (imageChain σ Ω) (activeBondSet K k (imageChain σ Ω))
        (continuedMinimalField ε εBar rB K k (imageChain σ Ω)
          (datumImage σ V₀) (twistedActiveFamily σ V₀ B))
        (transportGaugeField σ
          (continuedMinimalField ε εBar rB K k Ω V₀ B)) ∧
      (∀ (E : Type) (f : (BondAtLevel L m K 0 → Matrices.ComplexMatrix2) → E),
        (∀ u ∈ complexStabilizerGroup Ω (activeBondSet K k Ω),
          f (extendByOne (bondsInside (Ω 0)) (gaugeTransform u
            (continuedMinimalField ε εBar rB K k Ω V₀ B))) =
          f (continuedMinimalField ε εBar rB K k Ω V₀ B)) →
        transportObservable σ f
            (continuedMinimalField ε εBar rB K k (imageChain σ Ω)
              (datumImage σ V₀) (twistedActiveFamily σ V₀ B)) =
          f (continuedMinimalField ε εBar rB K k Ω V₀ B)) ∧
      ∀ v : SiteAtLevel L m K 0 → Matrices.ComplexMatrix2,
        IsComplexSiteMap (constraintSites K k Ω) v →
        InComplexStabilizerOrbit (imageChain σ Ω) (activeBondSet K k (imageChain σ Ω))
          (continuedGaugeExtendedField ε εBar rB K k (imageChain σ Ω)
            (datumImage σ V₀) (twistedActiveFamily σ V₀ B) (transportSiteFunction σ v))
          (transportGaugeField σ
            (continuedGaugeExtendedField ε εBar rB K k Ω V₀ B v))
def ContinuedTowerFieldCovariant (σ : FourTorus L m ≃ FourTorus L m) (ε εBar rB ξ : ℝ)
    (K n : ℕ) (Ω' : ℕ → Set (FourTorus L m)) (X : Set (FourTorus L m))
    (W U : BondAtLevel L m K 0 → Matrices.ComplexMatrix2) : Prop :=
  HasContinuedTowerField ε εBar rB ξ K n Ω' X W U →
  HasContinuedTowerField ε εBar rB ξ K n (imageChain σ Ω') (σ '' X)
      (transportGaugeField σ W) (transportGaugeField σ U) →
    InComplexStabilizerOrbit (imageChain σ Ω') (activeBondSet K n (imageChain σ Ω'))
      (continuedTowerField ε εBar rB K n (imageChain σ Ω') (σ '' X)
        (transportGaugeField σ W) (transportGaugeField σ U))
      (transportGaugeField σ (continuedTowerField ε εBar rB K n Ω' X W U))
end YangMills.Construction.PeriodicLattice
