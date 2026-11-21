import YangMills.Construction.Lattice.PairsOfAConfiguration
import YangMills.Construction.Lattice.ScalingAndGaugeConstantOfAStep
import YangMills.Construction.PolymerActivities.CompleteRegularPartOfAStep
import YangMills.Construction.Towers.GaugeFixingFunctionsAndHessians
import Mathlib
set_option autoImplicit false
open Set YangMills.Construction.ParameterChoice YangMills.Construction.Matrices
open scoped ENNReal
noncomputable section
namespace YangMills.Construction
namespace PeriodicLattice
variable {L m K : ℕ}
inductive ActivityPart : Type
  | unmarked
  | marked
inductive VertexLabel (L m K : ℕ) : Type
  | term (𝔠 : ActivityPart) (i : ℕ) (X : Set (FourTorus L m)) (z : SiteAtLevel L m K i)
  | counter (𝔠 : ActivityPart) (i : ℕ)
  | aged (i : ℕ) (X : Set (FourTorus L m))
namespace CompletedSteps
variable (P : CompletedSteps L m K)
def partFamily : (𝔠 : ActivityPart) → (i : ℕ) → RootedLocalActivities L m K i
  | .unmarked, i => P.unmarked i
  | .marked, i => P.marked i
def partShift : ActivityPart → ℕ → ℝ
  | .unmarked, i => P.unmarkedShift i
  | .marked, i => P.markedShift i
def vertex : VertexLabel L m K → (BondAtLevel L m K 0 → ComplexMatrix2) → ℂ
  | .term 𝔠 i X z, U =>
      P.partFamily 𝔠 i X z (restrictPairTo X (configurationPair i U)) -
        P.partFamily 𝔠 i X z (restrictPairTo X (configurationPair i trivialGaugeField))
  | .counter 𝔠 i, U => -(P.partShift 𝔠 i : ℂ) * totalEnergy U
  | .aged i X, U =>
      P.remainder i X (restrictPairTo X (configurationPair i U)) -
        P.remainder i X (restrictPairTo X (configurationPair i trivialGaugeField))
def vertexAction (𝒥 : Set (VertexLabel L m K)) (U : BondAtLevel L m K 0 → ComplexMatrix2) : ℂ :=
  ∑ᶠ ι ∈ 𝒥, P.vertex ι U
end CompletedSteps
def vertexLabels (r : ℕ) (x : ℕ → ℝ) (K m' k : ℕ) : Set (VertexLabel L m K) :=
  {ι | match ι with
    | .term _ i X z => i ∈ Finset.Icc 1 k ∧ X ∈ connectedRegions L m (coarseCubeIndex K m' i) ∧
        z ∈ (sitesIn X : Set (SiteAtLevel L m K i))
    | .counter _ i => i ∈ Finset.Icc 1 k
    | .aged i X => i ∈ Finset.Icc 1 (lastAgedLevel L r x m' k) ∧
        X ∈ (coarseCubeDomains r x K m' i : Set (Set (FourTorus L m)))}
def VertexLabel.IsMarked : VertexLabel L m K → Prop
  | .term 𝔠 _ _ _ => 𝔠 = .marked
  | .counter 𝔠 _ => 𝔠 = .marked
  | .aged _ _ => True
def markedLabels (r : ℕ) (x : ℕ → ℝ) (K m' k : ℕ) : Set (VertexLabel L m K) :=
  {ι | ι ∈ vertexLabels r x K m' k ∧ ι.IsMarked}
namespace AnalyticityConstants
variable (N : AnalyticityConstants) (C : Fin 2 → ℝ) (q : ℕ) (x : ℕ → ℝ)
def VertexIsDefined (s : ActivityDomainKind) (K : ℕ) :
    VertexLabel L m K → (BondAtLevel L m K 0 → ComplexMatrix2) → Prop
  | .term _ i X _, U =>
      restrictPairTo X (configurationPair i U) ∈ N.activityDomain C q x s K i X
  | .counter _ _, _ => True
  | .aged i X, U =>
      restrictPairTo X (configurationPair i U) ∈ N.activityDomain C q x s K i X
def VerticesAreDefined (s : ActivityDomainKind) (K : ℕ) (𝒥 : Set (VertexLabel L m K))
    (U : BondAtLevel L m K 0 → ComplexMatrix2) : Prop :=
  ∀ ι ∈ 𝒥, N.VertexIsDefined C q x s K ι U ∧ N.VertexIsDefined C q x s K ι trivialGaugeField
end AnalyticityConstants
def pairsSupportedOn (K : ℕ) (X : Set (FourTorus L m)) : Set (FieldCurrentPair L m K) :=
  {P | IsGaugeField complexGaugeGroup (bondsMeeting X) P.1 ∧
    (∀ b ∉ (bondsMeeting X : Set (BondAtLevel L m K 0)), P.1 b = 1) ∧
    IsBondForm complexLieAlgebra P.2 ∧
    ∀ b ∉ (bondsMeeting X : Set (BondAtLevel L m K 0)), P.2 b = 0}
def pairCoords (K : ℕ) (X : Set (FourTorus L m)) (P : FieldCurrentPair L m K) :
    PositiveFinestBondOf K X ⊕ PositiveFinestBondOf K X → ComplexMatrix2 :=
  pairOf (restrictToPositive (finestBondsMeeting K X) P.1)
    (restrictToPositive (finestBondsMeeting K X) P.2)
def IsOpenPairSet (K : ℕ) (X : Set (FourTorus L m)) (𝒩 : Set (FieldCurrentPair L m K)) : Prop :=
  𝒩 ⊆ pairsSupportedOn K X ∧
    ComplexMatrix2.IsRelativelyOpen (fieldCurrentPairs K X) (pairCoords K X '' 𝒩)
def IsHolomorphicPairFunction (K : ℕ) (X : Set (FourTorus L m)) (𝒩 : Set (FieldCurrentPair L m K))
    (f : FieldCurrentPair L m K → ℂ) : Prop :=
  IsOpenPairSet K X 𝒩 ∧ ∃ _ : Fintype (PositiveFinestBondOf K X),
    ∀ β : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless,
      ∃ Φ : (PositiveFinestBondOf K X ⊕ PositiveFinestBondOf K X → ComplexMatrix2) → ℂ,
        (∀ P ∈ 𝒩, Φ (pairCoords K X P) = f P) ∧
          GroupLieProduct.IsHolomorphicToCoords β (Equiv.funUnique (Fin 1) ℂ).symm
            (pairCoords K X '' 𝒩) Φ
namespace CubesOfStep
variable (c : ChoiceUpToDegreeConstants) (x : ℕ → ℝ) {m K k : ℕ}
  (N : ChoiceConstants c) (C : Fin 2 → ℝ) (s : ActivityDomainKind)
  (P : CompletedSteps c.L m K) (α₀ α₁ : ℝ)
def IsAdmissibleField (W : BondAtLevel c.L m K (k + 1) → ComplexMatrix2) : Prop :=
  W ∈ gaugeFieldsAtLevel c.L m K (k + 1) ∧ HasTorusBackground c W ∧
    ∀ X ∈ connectedRegions c.L m (coarseCubeIndex K N.cubeExp (k + 1)),
      backgroundPairRestrict c W X ∈ N.singleScaleDomainEqualRadii K (k + 1) X α₀ α₁
def vertexRegularPart (𝒥 : Set (VertexLabel c.L m K))
    (W : BondAtLevel c.L m K (k + 1) → ComplexMatrix2) : ℂ :=
  regularPartOf c x (P.vertexAction 𝒥) (N.VerticesAreDefined C c.q x s K 𝒥) W
def vertexRegularPartDomain (𝒥 : Set (VertexLabel c.L m K)) :
    Set (BondAtLevel c.L m K (k + 1) → ComplexMatrix2) :=
  regularPartDomainOf c x (P.vertexAction 𝒥) (N.VerticesAreDefined C c.q x s K 𝒥)
def stepCount (m K k : ℕ) : ℝ :=
  stepScalingGaugeConstant c.A₀ c.𝔭₀ x K k (univ : Set (FourTorus c.L m)) +
    ComplexMatrix2.logGaussianIntegral *
      (positiveFreeBondCount K k (univ : Set (FourTorus c.L m)) : ℝ)
structure VertexTerms where
  Term : Type
  countable : Countable Term
  gaussianTerms : Set Term
  nhd : Set (FourTorus c.L m) → Set (FieldCurrentPair c.L m K)
  nhd_open : ∀ X ∈ connectedRegions c.L m (coarseCubeIndex K N.cubeExp (k + 1)),
    IsOpenPairSet K X (nhd X)
  domain_subset_nhd : ∀ X ∈ connectedRegions c.L m (coarseCubeIndex K N.cubeExp (k + 1)),
    N.singleScaleDomainEqualRadii K (k + 1) X α₀ α₁ ⊆ nhd X
  region : Term → Set (FourTorus c.L m)
  region_mem : ∀ τ, region τ ∈ connectedRegions c.L m (coarseCubeIndex K N.cubeExp (k + 1))
  root : Term → SiteAtLevel c.L m K (k + 1)
  root_mem : ∀ τ, root τ ∈ (sitesIn (region τ) : Set (SiteAtLevel c.L m K (k + 1)))
  vertexSet : Term → Set (VertexLabel c.L m K)
  vertexSet_subset : ∀ τ, vertexSet τ ⊆ vertexLabels c.r x K N.cubeExp k
  vertexSet_eq_empty : ∀ τ ∈ gaussianTerms, vertexSet τ = ∅
  value : Term → FieldCurrentPair c.L m K → ℂ
  value_holomorphic : ∀ τ, IsHolomorphicPairFunction K (region τ) (nhd (region τ)) (value τ)
  value_bdd : ∀ τ, pairSetSupremum (nhd (region τ)) (value τ) ≠ ∞
  value_invariant : ∀ τ, IsComplexGaugeInvariantAt (region τ)
    (N.singleScaleDomainEqualRadii K (k + 1) (region τ) α₀ α₁) (value τ)
namespace VertexTerms
variable {c x N α₀ α₁}
variable (T : VertexTerms c x (m := m) (K := K) (k := k) N α₀ α₁)
def termNorm (τ : T.Term) : ℝ≥0∞ :=
  pairSetSupremum (T.nhd (T.region τ)) (T.value τ)
def AbsConvergent (𝔗' : Set T.Term) : Prop :=
  ∑' τ : 𝔗', T.termNorm τ ≠ ∞
def termsWithin (𝒥 : Set (VertexLabel c.L m K)) : Set T.Term :=
  {τ | T.vertexSet τ ⊆ 𝒥}
def sumAt (𝔗' : Set T.Term) (W : BondAtLevel c.L m K (k + 1) → ComplexMatrix2) : ℂ :=
  ∑' τ : 𝔗', T.value τ (backgroundPairRestrict c W (T.region τ))
def CountedSumRuleOn (𝒲 : Set (BondAtLevel c.L m K (k + 1) → ComplexMatrix2)) : Prop :=
  ∀ 𝒥 ⊆ vertexLabels c.r x K N.cubeExp k, T.AbsConvergent (T.termsWithin 𝒥) →
    ∀ W ∈ 𝒲, IsAdmissibleField c N α₀ α₁ W → W ∈ vertexRegularPartDomain c x N C s P 𝒥 →
      T.sumAt (T.termsWithin 𝒥) W =
        vertexRegularPart c x N C s P 𝒥 W - (stepCount c x m K k : ℂ)
variable {C s P T}
end VertexTerms
structure VertexExpansion (ℰ₀ : (BondAtLevel c.L m K (k + 1) → ComplexMatrix2) → ℂ)
    (𝒟₀ : Set (BondAtLevel c.L m K (k + 1) → ComplexMatrix2)) extends
    VertexTerms c x (m := m) (K := K) (k := k) N α₀ α₁ where
  nearOne : Set (BondAtLevel c.L m K (k + 1) → ComplexMatrix2)
  nearOne_open : 0 < m → Tower.IsOpenNhdOfOne nearOne
  sum_rule : toVertexTerms.CountedSumRuleOn C s P nearOne
  gaussian_sum_rule : toVertexTerms.AbsConvergent gaussianTerms →
    ∀ W ∈ nearOne, IsAdmissibleField c N α₀ α₁ W → W ∈ 𝒟₀ →
      toVertexTerms.sumAt gaussianTerms W = ℰ₀ W
namespace VertexTerms
variable {c x N α₀ α₁}
variable (T : VertexTerms c x (m := m) (K := K) (k := k) N α₀ α₁)
def resum (𝔗' : Set T.Term) : RootedLocalActivities c.L m K (k + 1) :=
  fun X z Q => ∑' τ : {τ // τ ∈ 𝔗' ∧ T.region τ = X ∧ T.root τ = z}, T.value τ.1 Q
def markedTerms : Set T.Term :=
  {τ | (T.vertexSet τ ∩ (markedLabels c.r x K N.cubeExp k : Set (VertexLabel c.L m K))).Nonempty}
def fullFamily : RootedLocalActivities c.L m K (k + 1) := T.resum univ
def markedFamily : RootedLocalActivities c.L m K (k + 1) := T.resum T.markedTerms
def unmarkedFamily : RootedLocalActivities c.L m K (k + 1) :=
  fun X z Q => T.fullFamily X z Q - T.markedFamily X z Q
end VertexTerms
end CubesOfStep
end PeriodicLattice
end YangMills.Construction
