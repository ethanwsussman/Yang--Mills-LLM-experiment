import YangMills.Construction.Geometry.TorusCubes
import YangMills.Construction.Lattice.BareCubesRegionsAndIndices
import YangMills.Construction.Lattice.CovariantSiteOperators
import YangMills.Construction.Lattice.LocalizationDomainsAndEdgeTrees
import YangMills.Construction.Lattice.MinimalConfigurationsAtComplexData
import YangMills.Construction.Lattice.TwoLayerInterior
import YangMills.Construction.Parameters.ConstructionParameters
import YangMills.Construction.Thresholds.DegreeFunctions
import Mathlib
set_option autoImplicit false
open Set
open YangMills.Construction.Matrices
noncomputable section
namespace YangMills.Construction.PeriodicLattice
variable {L m : ℕ}
structure AnalyticityConstants where
  regRadius : ℝ
  regThreshold : ℝ
  towerRadius : ℝ
  blockExp : ℕ
  gapExp : ℕ
  sizeExp : ℕ
  cubeExp : ℕ
  cubeConst : ℝ
  gaugeBound : ℝ
  layerGaugeBound : ℝ
  cubeFactor : ℕ
  layerDecay : ℝ
def AnalyticityConstants.ofChoice (T : ParameterChoice.DerivedConstants)
    (c : ParameterChoice.FullChoice) : AnalyticityConstants where
  regRadius := c.εv
  regThreshold := c.εBar
  towerRadius := T.rB c.L c.blockNumber c.gapNumber
  blockExp := Nat.log c.L c.blockNumber
  gapExp := Nat.log c.L c.gapNumber
  sizeExp := Nat.log c.L c.M₁
  cubeExp := Nat.log c.L c.M
  cubeConst := T.o
  gaugeBound := c.cubeSizeConst
  layerGaugeBound := T.flowConstB
  cubeFactor := c.Cg
  layerDecay := c.βs
def PlaquettesNearOne {K : ℕ} (P : Set (PlaquetteAtLevel L m K 0))
    (W : BondAtLevel L m K 0 → ComplexMatrix2) (a : ℝ) : Prop :=
  ∀ p ∈ P, ComplexMatrix2.operatorNorm (plaquetteHolonomy W p - 1) < a
def BondNormLt {K : ℕ} (ℬ : Set (BondAtLevel L m K 0)) (A : BondAtLevel L m K 0 → ComplexMatrix2)
    (a : ℝ) : Prop :=
  ∀ b ∈ ℬ, ComplexMatrix2.operatorNorm (A b) < a
def CovDerivNormLt {K : ℕ} (ξ : ℝ) (V A : BondAtLevel L m K 0 → ComplexMatrix2)
    (S : Set (FourTorus L m)) (ℬ : Set (BondAtLevel L m K 0)) (a : ℝ) : Prop :=
  ∀ (x : SiteAtLevel L m K 0) (μ ν : Fin 4), (x : FourTorus L m) ∈ S → Bond.forwardFrom x μ ∈ ℬ →
    Bond.forwardFrom x ν ∈ ℬ → Bond.forwardFrom (x + unitStep L m (levelDepth K 0) μ) ν ∈ ℬ →
      ComplexMatrix2.operatorNorm (covDeriv ξ V μ (bondFormComponent A ν) x) < a
def fullPlaquettes (K : ℕ) (X : Set (FourTorus L m)) : Set (PlaquetteAtLevel L m K 0) :=
  {p | p ∈ plaquettesMeeting X ∧
    ∀ b ∈ p.boundaryBonds, b ∈ (bondsMeeting X : Set (BondAtLevel L m K 0))}
def IsDecompositionData (K : ℕ) (X : Set (FourTorus L m))
    (U A' J : BondAtLevel L m K 0 → ComplexMatrix2) : Prop :=
  IsGaugeField compactGaugeGroup (bondsMeeting X) U ∧
    (∀ b ∉ (bondsMeeting X : Set (BondAtLevel L m K 0)), U b = 1) ∧
    IsBondForm complexLieAlgebra A' ∧
    (∀ b ∉ (bondsMeeting X : Set (BondAtLevel L m K 0)), A' b = 0) ∧
    IsBondForm complexLieAlgebra J ∧
    ∀ b ∉ (bondsMeeting X : Set (BondAtLevel L m K 0)), J b = 0
def recomposedField (ξ : ℝ) (K : ℕ) (X : Set (FourTorus L m))
    (U A' : BondAtLevel L m K 0 → ComplexMatrix2) : BondAtLevel L m K 0 → ComplexMatrix2 :=
  extendByOne (bondsMeeting X) (expTwist ((ξ : ℂ) • A') U)
def restrictInner (K : ℕ) (X : Set (FourTorus L m)) (W : BondAtLevel L m K 0 → ComplexMatrix2) :
    BondAtLevel L m K 0 → ComplexMatrix2 :=
  extendByOne (bondsInside X) W
def ContinuationUnique (ε rB : ℝ) (K n : ℕ) (Ω : ℕ → Set (FourTorus L m))
    (V₀ : ∀ j : ℕ, BondAtLevel L m K j → ComplexMatrix2) : Prop :=
  ∀ Φ Φ', IsHolomorphicContinuation ε rB K n Ω V₀ Φ → IsHolomorphicContinuation ε rB K n Ω V₀ Φ' →
    EqOn Φ Φ' (complexFamilyBall (activeBondSet K n Ω) rB)
namespace AnalyticityConstants
variable (N : AnalyticityConstants)
def SmallGaugeOnCubes (K j : ℕ) (X : Set (FourTorus L m)) (α₀ : ℝ)
    (U : BondAtLevel L m K 0 → ComplexMatrix2) : Prop :=
  ∀ (t : ℝ) (Q : Set (FourTorus L m)), TorusCubes.IsTorusCube (torusSide L m) t Q → Q ⊆ X →
    toLevelUnits L K j t ≤ N.cubeConst * (L : ℝ) * (L : ℝ) ^ N.cubeExp →
    ∃ (u : SiteAtLevel L m K 0 → ComplexMatrix2) (A : BondAtLevel L m K 0 → ComplexMatrix2),
      (∀ x, u x ∈ compactGaugeGroup) ∧ IsBondForm complexLieAlgebra A ∧
      (∀ b ∈ (bondsInside Q : Set (BondAtLevel L m K 0)),
        gaugeTransform u U b = expGaugeField (((finestMeshInLevelUnits L j : ℝ) : ℂ) • A) b) ∧
      BondNormLt (bondsInside Q) A
        (N.cubeConst * (L : ℝ) * (L : ℝ) ^ N.cubeExp * N.gaugeBound * α₀) ∧
      CovDerivNormLt (finestMeshInLevelUnits L j) trivialGaugeField A Q (bondsInside Q)
        (N.cubeConst * (L : ℝ) * (L : ℝ) ^ N.cubeExp * N.gaugeBound * α₀)
def BasicConditions (K j : ℕ) (X : Set (FourTorus L m)) (α₀ α₁ γ₀ : ℝ)
    (U A' J : BondAtLevel L m K 0 → ComplexMatrix2) : Prop :=
  PlaquettesNearOne (fullPlaquettes K X) U (α₀ * finestMeshInLevelUnits L j ^ 2) ∧
    N.SmallGaugeOnCubes K j X α₀ U ∧
    BondNormLt (bondsMeeting X) A' α₁ ∧
    CovDerivNormLt (finestMeshInLevelUnits L j) U A' univ (bondsMeeting X) α₁ ∧
    PlaquettesNearOne (fullPlaquettes K X)
      (recomposedField (finestMeshInLevelUnits L j) K X U A')
      (α₀ * finestMeshInLevelUnits L j ^ 2) ∧
    BondNormLt (bondsMeeting X) J γ₀
def towerOf (K : ℕ) (first : Bool) (Z : Set (FourTorus L m)) : ℕ → Set (FourTorus L m) :=
  if first then separatedTower K N.blockExp N.gapExp 0 Z else shrinkingTower K N.sizeExp 0 Z
def TowerDataExists (ξ : ℝ) (K n : ℕ) (Ω' : ℕ → Set (FourTorus L m)) (X : Set (FourTorus L m))
    (W U : BondAtLevel L m K 0 → ComplexMatrix2) : Prop :=
  HasTowerField N.regRadius N.regThreshold N.towerRadius ξ K n Ω' X W U ∧
    (∃ Φ, IsHolomorphicContinuation N.regRadius N.towerRadius K n Ω'
      (averagingOnDeterminingSet (Averaging.smoothingRadius L) K X U) Φ) ∧
    ContinuationUnique N.regRadius N.towerRadius K n Ω'
      (averagingOnDeterminingSet (Averaging.smoothingRadius L) K X U)
def TowerDataSmall (K n : ℕ) (Ω' : ℕ → Set (FourTorus L m)) (X : Set (FourTorus L m))
    (W U : BondAtLevel L m K 0 → ComplexMatrix2) (P : Set (PlaquetteAtLevel L m K 0))
    (ℬ : Set (BondAtLevel L m K 0)) (a a' : ℝ) : Prop :=
  PlaquettesNearOne P (towerField N.regRadius N.towerRadius K n Ω' X W U) a ∧
    BondNormLt ℬ (towerFieldCurrent N.regRadius N.towerRadius K n Ω' X W U) a'
def RepresentativeExists (ξ : ℝ) (K n : ℕ) (Ω' : ℕ → Set (FourTorus L m))
    (X : Set (FourTorus L m)) (U : BondAtLevel L m K 0 → ComplexMatrix2) : Prop :=
  IsPolarDecomposition ξ K X U U ∧
    averagingOnDeterminingSet (Averaging.smoothingRadius L) K X U ∈
      activeRegularRealFields N.regThreshold K n Ω' ∧
    HasActiveGaugeRepresentative N.regRadius K n Ω'
      (averagingOnDeterminingSet (Averaging.smoothingRadius L) K X U)
def realDatumRepresentative (K n : ℕ) (Ω' : ℕ → Set (FourTorus L m)) (X : Set (FourTorus L m))
    (U : BondAtLevel L m K 0 → ComplexMatrix2) : BondAtLevel L m K 0 → ComplexMatrix2 :=
  activeGaugeRepresentative N.regRadius K n Ω'
    (averagingOnDeterminingSet (Averaging.smoothingRadius L) K X U)
def RepresentativeSmall (K n : ℕ) (Ω' : ℕ → Set (FourTorus L m)) (X : Set (FourTorus L m))
    (U : BondAtLevel L m K 0 → ComplexMatrix2) (P : Set (PlaquetteAtLevel L m K 0))
    (ℬ : Set (BondAtLevel L m K 0)) (a a' : ℝ) : Prop :=
  PlaquettesNearOne P (N.realDatumRepresentative K n Ω' X U) a ∧
    BondNormLt ℬ
      (yangMillsCurrent (finestMeshInLevelUnits L n) (N.realDatumRepresentative K n Ω' X U)) a'
def PairTowerBounds (ξ : ℝ) (K n : ℕ) (Ω' : ℕ → Set (FourTorus L m)) (X : Set (FourTorus L m))
    (W U : BondAtLevel L m K 0 → ComplexMatrix2) (P : Set (PlaquetteAtLevel L m K 0))
    (ℬ : Set (BondAtLevel L m K 0)) (a a' : ℝ) : Prop :=
  (N.TowerDataExists ξ K n Ω' X (restrictInner K X W) (restrictInner K X U) ∧
      N.TowerDataSmall K n Ω' X (restrictInner K X W) (restrictInner K X U) P ℬ a a') ∧
    N.RepresentativeExists ξ K n Ω' X (restrictInner K X U) ∧
      N.RepresentativeSmall K n Ω' X (restrictInner K X U) P ℬ a a'
def TowerCondition (K j : ℕ) (X : Set (FourTorus L m)) (α₀ : ℝ)
    (W U : BondAtLevel L m K 0 → ComplexMatrix2) : Prop :=
  ∀ n, 1 ≤ n → n ≤ j →
    N.PairTowerBounds (finestMeshInLevelUnits L j) K n (N.towerOf K true X) X W U
      (plaquettesMeeting (layerEnlargement (coarseCubeIndex K N.cubeExp j) X (-2)))
      (bondsMeeting (layerEnlargement (coarseCubeIndex K N.cubeExp j) X (-2)))
      (α₀ * finestMeshInLevelUnits L j ^ 2)
      (α₀ * ((L : ℝ) ^ n * finestMeshInLevelUnits L j) ^ 2)
def TowerRequirement (ξ : ℝ) (K p : ℕ) (first : Bool) (Z : Set (FourTorus L m)) (c : ℝ)
    (W U : BondAtLevel L m K 0 → ComplexMatrix2) : Prop :=
  ∀ n, 1 ≤ n → n ≤ p →
    N.PairTowerBounds ξ K n (N.towerOf K first Z) Z W U
      (plaquettesMeeting (doubleLayerInterior K N.cubeExp p Z))
      (bondsMeeting (doubleLayerInterior K N.cubeExp p Z))
      (c * (L : ℝ) ^ (-(2 * (p : ℤ)))) (c * (L : ℝ) ^ (2 * ((n : ℤ) - (p : ℤ))))
def towerIndexSet (K j : ℕ) (X : Set (FourTorus L m)) : Set (ℕ × Set (FourTorus L m)) :=
  {q | 1 ≤ q.1 ∧ q.1 ≤ j ∧ q.2 ∈ connectedRegions L m (coarseCubeIndex K N.cubeExp (q.1 - 1)) ∧
    q.2 ⊆ X}
def AllTowerConditions (K j : ℕ) (X : Set (FourTorus L m)) (b : ℝ)
    (W U : BondAtLevel L m K 0 → ComplexMatrix2) : Prop :=
  ∀ q ∈ N.towerIndexSet K j X, ∀ first : Bool,
    N.TowerRequirement (finestMeshInLevelUnits L j) K q.1 first q.2
      (b * (L : ℝ) ^ (-((j : ℤ) - (q.1 : ℤ)))) W U
end AnalyticityConstants
abbrev FieldCurrentPair (L m K : ℕ) : Type :=
  (BondAtLevel L m K 0 → ComplexMatrix2) × (BondAtLevel L m K 0 → ComplexMatrix2)
def pairGaugeTransform {K : ℕ} (X : Set (FourTorus L m)) (u : SiteAtLevel L m K 0 → ComplexMatrix2)
    (P : FieldCurrentPair L m K) : FieldCurrentPair L m K :=
  (extendByOne (bondsMeeting X) (gaugeTransform u P.1), conjugateBondForm u P.2)
def complexOrbits {K : ℕ} (X : Set (FourTorus L m)) (S : Set (FieldCurrentPair L m K)) :
    Set (FieldCurrentPair L m K) :=
  {P | ∃ u : SiteAtLevel L m K 0 → ComplexMatrix2, (∀ x, u x ∈ complexGaugeGroup) ∧
    ∃ Q ∈ S, P = pairGaugeTransform X u Q}
namespace AnalyticityConstants
variable (N : AnalyticityConstants)
def singleScaleDomain (K j : ℕ) (X : Set (FourTorus L m)) (α₀ α₁ γ₀ : ℝ) :
    Set (FieldCurrentPair L m K) :=
  complexOrbits X {P | ∃ U A', IsDecompositionData K X U A' P.2 ∧
    P.1 = recomposedField (finestMeshInLevelUnits L j) K X U A' ∧
    N.BasicConditions K j X α₀ α₁ γ₀ U A' P.2 ∧
    N.TowerCondition K j X α₀ P.1 U}
def singleScaleDomainEqualRadii (K j : ℕ) (X : Set (FourTorus L m)) (α₀ α₁ : ℝ) :
    Set (FieldCurrentPair L m K) :=
  N.singleScaleDomain K j X α₀ α₁ α₀
def hereditaryDomain (K j : ℕ) (X : Set (FourTorus L m)) (α₀ α₁ γ₀ : ℝ) :
    Set (FieldCurrentPair L m K) :=
  complexOrbits X {P | ∃ U A', IsDecompositionData K X U A' P.2 ∧
    P.1 = recomposedField (finestMeshInLevelUnits L j) K X U A' ∧
    N.BasicConditions K j X α₀ α₁ γ₀ U A' P.2 ∧
    N.AllTowerConditions K j X α₀ P.1 U}
def layerShrink (j n : ℕ) : ℝ := 1 - N.layerDecay * (1 - (2 : ℝ) ^ (-((j : ℤ) - (n : ℤ))))
def connectingChain (K : ℕ) (Ω : ℕ → Set (FourTorus L m)) (X : Set (FourTorus L m)) (i : ℕ) :
    Set (FourTorus L m) :=
  CubeRegions.regionInf (levelDepth K 0) (N.towerOf K false X i) (domainChain Ω i)
def layerSlice (j : ℕ) (Ω : ℕ → Set (FourTorus L m)) (X : Set (FourTorus L m)) (n : ℕ) :
    Set (FourTorus L m) :=
  if n < j then X ∩ (Ω n \ Ω (n + 1)) else X ∩ Ω j
def IsLayerCube (K j : ℕ) (Ω : ℕ → Set (FourTorus L m)) (n : ℕ) (t : ℝ) (Q : Set (FourTorus L m)) :
    Prop :=
  TorusCubes.IsTorusCube (torusSide L m) t Q ∧
    toLevelUnits L K j t =
      (N.cubeFactor : ℝ) * (L : ℝ) ^ N.cubeExp * ((L : ℝ) ^ n * finestMeshInLevelUnits L j) ∧
    if n < j then
      Q ⊆ Ω n \ (if n + 1 < j then Ω (n + 2) else ∅) ∧ (Q ∩ closure ((Ω (n + 1))ᶜ)).Nonempty
    else Q ⊆ Ω j
def LayerConditions (C : Fin 2 → ℝ) (q : ℕ) (x : ℕ → ℝ) (K j : ℕ)
    (Ω : ℕ → Set (FourTorus L m)) (X : Set (FourTorus L m))
    (U A' J : BondAtLevel L m K 0 → ComplexMatrix2) (n : ℕ) : Prop :=
  let ξ : ℝ := finestMeshInLevelUnits L j
  let ξₙ : ℝ := (L : ℝ) ^ n * ξ
  let f : ℝ := N.layerShrink j n
  let α₀ₙ : ℝ := Thresholds.couplingRadius C q x 0 n
  let α₁ₙ : ℝ := Thresholds.couplingRadius C q x 1 n
  let E : Set (FourTorus L m) := layerSlice j Ω X n
  let W : BondAtLevel L m K 0 → ComplexMatrix2 := recomposedField ξ K X U A'
  let P : Set (PlaquetteAtLevel L m K 0) := plaquettesMeeting E ∩ fullPlaquettes K X
  PlaquettesNearOne P U (f * α₀ₙ * ξ ^ 2 * ξₙ⁻¹ ^ 2) ∧
    PlaquettesNearOne P W (f * α₀ₙ * ξ ^ 2 * ξₙ⁻¹ ^ 2) ∧
    BondNormLt (bondsMeeting E) J (f * α₀ₙ * ξₙ⁻¹ ^ 3) ∧
    (∀ p, 1 ≤ p → p ≤ j →
      IsSeparatedChain K N.blockExp N.gapExp 0 p (N.connectingChain K Ω X) ∧
        N.TowerDataExists ξ K p (N.connectingChain K Ω X) X
          (restrictInner K X W) (restrictInner K X U) ∧
        N.TowerDataSmall K p (N.connectingChain K Ω X) X
          (restrictInner K X W) (restrictInner K X U)
          (plaquettesMeeting E ∩ plaquettesInside X)
          {b | b ∈ (bondsMeeting E : Set (BondAtLevel L m K 0)) ∧ HasCurrentAt K X b}
          (f * α₀ₙ * (L : ℝ) ^ (-(2 * (p : ℤ))) * ((L : ℝ) ^ ((n : ℤ) - (p : ℤ)))⁻¹ ^ 2)
          (f * α₀ₙ * (L : ℝ) ^ (n - min p n) * ((L : ℝ) ^ ((n : ℤ) - (p : ℤ)))⁻¹ ^ 3)) ∧
    (∀ (t : ℝ) (Q : Set (FourTorus L m)), N.IsLayerCube K j Ω n t Q →
      ∃ (u : SiteAtLevel L m K 0 → ComplexMatrix2) (A : BondAtLevel L m K 0 → ComplexMatrix2),
        (∀ y, u y ∈ compactGaugeGroup) ∧ IsBondForm complexLieAlgebra A ∧
        (∀ b ∈ (bondsInside (Q ∩ X) : Set (BondAtLevel L m K 0)),
          gaugeTransform u U b = expGaugeField ((ξ : ℂ) • A) b) ∧
        BondNormLt (bondsInside (Q ∩ X)) A
          (N.layerGaugeBound * (N.cubeFactor : ℝ) * (L : ℝ) ^ N.cubeExp * α₀ₙ * ξₙ⁻¹) ∧
        CovDerivNormLt ξ trivialGaugeField A (Q ∩ X) (bondsInside (Q ∩ X))
          (N.layerGaugeBound * (N.cubeFactor : ℝ) * (L : ℝ) ^ N.cubeExp * α₀ₙ * ξₙ⁻¹ ^ 2)) ∧
    BondNormLt (bondsMeeting E) A' (f * α₁ₙ * ξₙ⁻¹) ∧
    CovDerivNormLt ξ U A' E (bondsMeeting X) (f * α₁ₙ * ξₙ⁻¹ ^ 2)
def layeredDomain (C : Fin 2 → ℝ) (q : ℕ) (x : ℕ → ℝ) (K j : ℕ) (Ω : ℕ → Set (FourTorus L m))
    (X : Set (FourTorus L m)) : Set (FieldCurrentPair L m K) :=
  {P | ∃ U A', IsDecompositionData K X U A' P.2 ∧
    P.1 = recomposedField (finestMeshInLevelUnits L j) K X U A' ∧
    ∀ n, 1 ≤ n → n ≤ j → N.LayerConditions C q x K j Ω X U A' P.2 n}
end AnalyticityConstants
end YangMills.Construction.PeriodicLattice
