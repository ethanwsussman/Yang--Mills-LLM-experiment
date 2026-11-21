import YangMills.Construction.Lattice.ContinuationsOfTheMinimiserAndOfTheLandauPair
import YangMills.Construction.Lattice.NewLabelBackgroundAndCouplingOfALargeFieldOperation
import YangMills.Construction.Lattice.ReferenceLawOfAClassComponent
import YangMills.Construction.Lattice.StageSequences
import YangMills.Construction.PolymerActivities.EffectiveActionOfALabel
import Mathlib
set_option autoImplicit false
open Set MeasureTheory
noncomputable section
namespace YangMills.Construction
open ParameterChoice Matrices
namespace PeriodicLattice
section ActiveLandau
variable {L m : ℕ}
def activeLandauCurve (ε ξ α : ℝ) (K k : ℕ) (Ω : ℕ → Set (FourTorus L m))
    (V₀ : ∀ j : ℕ, BondAtLevel L m K j → ComplexMatrix2) (B : ActiveFamily L m K k Ω)
    (b : BondAtLevel L m K 0) : ℝ → ComplexMatrix2 :=
  fun t => activeLandauPotential ξ α ε K k Ω V₀ (((t : ℝ) : ℂ) • B) b
def activeLandauLinearization (ε ξ α : ℝ) (K k : ℕ) (Ω : ℕ → Set (FourTorus L m))
    (V₀ : ∀ j : ℕ, BondAtLevel L m K j → ComplexMatrix2) (B : ActiveFamily L m K k Ω) :
    BondAtLevel L m K 0 → ComplexMatrix2 :=
  fun b => deriv (activeLandauCurve ε ξ α K k Ω V₀ B b) 0
end ActiveLandau
namespace LargeFieldCompletion
open CentralBlock ComponentReferenceLaw CubesOfStep
section CompletionDataSection
variable {L m K k : ℕ}
structure CompletionData (N : AnalyticityConstants) (cf : ℕ → ℕ) (L m K k h : ℕ) where
  scaleLabel : ScaleLabel L m K N.cubeExp cf k
  storedBonds : StoredBonds L m K k
  actionData : AnalyticityConstants.EffectiveActionData L m K storedBonds
  storedFieldsOf : (∀ j : ℕ, BondAtLevel L m K j → ComplexMatrix2) → storedBonds.FieldSystem
  vacuumPiece : Set (FourTorus L m) → ℂ
  resummedPiece : Set (FourTorus L m) → FieldCurrentPair L m K →
    (∀ j : ℕ, BondAtLevel L m K j → ComplexMatrix2) →
    (BondAtLevel L m K h → ComplexMatrix2) → ℂ
variable (N : AnalyticityConstants) {cf : ℕ → ℕ} {h : ℕ}
def CompletionData.VacuumLocalizes (T : CompletionData N cf L m K k h) : Prop :=
  ∑ᶠ X : Set (FourTorus L m), T.vacuumPiece X = T.actionData.vacuumEnergy
def SharesCube (K : ℕ) (X Y : Set (FourTorus L m)) : Prop :=
  (cubeMeet K X Y).Nonempty
def normalizationMeeting (v : ℕ → ℕ) (T : CompletionData N cf L m K k h)
    (Y : Set (FourTorus L m)) : ℂ :=
  ∑ j ∈ Finset.Icc 1 k,
    ((∑ᶠ z ∈ (sitesIn (smoothedRegionInterior K N.cubeExp (v j) j
          (T.scaleLabel.smallFieldSeq j)) : Set (SiteAtLevel L m K j)),
        ∑ᶠ X ∈ {X ∈ regularPolymerDomains K N.cubeExp j (T.scaleLabel.smallFieldSeq j) |
            (z : FourTorus L m) ∈ X ∧ SharesCube K X Y},
          T.actionData.regularActs j X z
            (restrictPairTo X (configurationPair j trivialGaugeField))) +
      ∑ᶠ X ∈ {X ∈ remainderPolymerDomains K N.cubeExp (v j) j (T.scaleLabel.smallFieldSeq j) |
          SharesCube K X Y},
        T.actionData.remainderActs j X
          (restrictPairTo X (configurationPair j trivialGaugeField)))
def constantTermsMeeting (v : ℕ → ℕ) (T : CompletionData N cf L m K k h)
    (Y : Set (FourTorus L m)) : ℂ :=
  normalizationMeeting N v T Y + ∑ᶠ X ∈ {X | SharesCube K X Y}, T.vacuumPiece X
def completedEnergy (b : ℕ → ℝ) (v : ℕ → ℕ) (T : CompletionData N cf L m K k h)
    (y : FourTorus L m → ℝ) (U : BondAtLevel L m K 0 → ComplexMatrix2)
    (𝔣 : T.storedBonds.FieldSystem) : ℂ :=
  -variableCouplingEnergy y U + N.regularPart b v T.scaleLabel T.actionData U +
    N.remainderPart v T.scaleLabel T.actionData U +
    N.boundaryPart T.scaleLabel T.actionData U 𝔣 -
    T.actionData.vacuumEnergy
def resummationRegions (K m' k : ℕ) (Q : Set (Set (FourTorus L m))) :
    Set (Set (FourTorus L m)) :=
  {Y | Y ∈ connectedRegions L m (coarseCubeIndex K m' k) ∧
    ∃ C ⊆ regionComponents (coarseCubeIndex K m' k) (unionThickened K m' k Q), C.Nonempty ∧
      cubeMeet K Y (unionThickened K m' k Q) = ⋃₀ C}
def resummedPieceAt (T : CompletionData N cf L m K k h) (Y : Set (FourTorus L m))
    (U : BondAtLevel L m K 0 → ComplexMatrix2)
    (B : ∀ j : ℕ, BondAtLevel L m K j → ComplexMatrix2)
    (W : BondAtLevel L m K h → ComplexMatrix2) : ℂ :=
  T.resummedPiece Y (restrictPairTo Y (configurationPair k U))
    (fun j => (bondsMeeting Y : Set (BondAtLevel L m K j)).indicator (B j))
    (restrictToRegion Y W)
def resummedTotal (T : CompletionData N cf L m K k h) (Q : Set (Set (FourTorus L m)))
    (U : BondAtLevel L m K 0 → ComplexMatrix2)
    (B : ∀ j : ℕ, BondAtLevel L m K j → ComplexMatrix2)
    (W : BondAtLevel L m K h → ComplexMatrix2) : ℂ :=
  ∑ᶠ Y ∈ resummationRegions K N.cubeExp k Q, resummedPieceAt N T Y U B W
end CompletionDataSection
section Objects
def componentwiseCutoff (c : ChoiceUpToRadii) {m : ℕ} (K : ℕ) (x : ℕ → ℝ) (k : ℕ)
    (Q : Set (Set (FourTorus c.L m))) (y : FourTorus c.L m) : ℝ :=
  ∑ᶠ X ∈ Q, X.indicator (componentCutoff c X K x k) y
variable (c : ChoiceUpToRadii) {m K : ℕ} {x : ℕ → ℝ} {k : ℕ}
  (S : LabelAtLevel c.toChoiceUpToDegreeConstants m K x k) (Q : Set (Set (FourTorus c.L m)))
def innerShellCutoff (y : FourTorus c.L m) : ℝ :=
  regionCutoffFn (levelDepth K (outerShellLevel c.toChoiceUpToDegreeConstants x k)) 2
    (S.trimmedRegion c.r x Q (ScaleLabel.nestBaseLevel c.L c.r x k)) y
def combinedCutoff (y : FourTorus c.L m) : ℝ :=
  componentwiseCutoff c K x k Q y * (1 - innerShellCutoff c S Q y)
def finalStageChain : ℕ → Set (FourTorus c.L m) :=
  S.stagedDomain c.r x Q (Thresholds.delayDepth c.L c.r x k)
def gluedTrimmedChain (X : Set (FourTorus c.L m)) : ℕ → Set (FourTorus c.L m) :=
  gluedChain K (Nat.log c.L c.M₁) k (finalStageChain c S Q) X
def basicBackgroundData (U₀ : BondAtLevel c.L m K 0 → ComplexMatrix2)
    (V : AllLevelFields c.L m K) : AllLevelFields c.L m K :=
  open Classical in
  fun j b => if b ∈ (bondsInside (S.trimmedDomainThickened c.r x Q) :
      Set (BondAtLevel c.L m K j))
    then activeAveragingMap U₀ j b else gluedBoundaryData K k k (finalStageChain c S Q) V j b
def basicBackgroundDataOfComponent (X : Set (FourTorus c.L m))
    (U₀ : BondAtLevel c.L m K 0 → ComplexMatrix2) (V : AllLevelFields c.L m K) :
    AllLevelFields c.L m K :=
  open Classical in
  fun j b => if b ∈ (bondsInside (cubeMeet K (S.trimmedDomainThickened c.r x Q) X) :
      Set (BondAtLevel c.L m K j))
    then activeAveragingMap U₀ j b else gluedBoundaryData K k k (finalStageChain c S Q) V j b
def fluctuationVariables (V' : AllLevelFields c.L m K) : AllLevelFields c.L m K :=
  open Classical in
  fun j b => if (⟨j, b⟩ : Σ q : ℕ, BondAtLevel c.L m K q) ∈ S.nestFixedBonds c.r x Q (⋃₀ Q)
    then (((Thresholds.couplingAt x k)⁻¹ : ℝ) : ℂ) •
      (Complex.I⁻¹ • ComplexMatrix2.unitaryLog (V' j b))
    else 0
def familyOnGluedSet (X : Set (FourTorus c.L m)) (B : AllLevelFields c.L m K) :
    ActiveFamily c.L m K k (gluedTrimmedChain c S Q X) :=
  open Classical in
  fun q => if q.1 ∈ S.nestFixedBonds c.r x Q X then B q.1.1 q.1.2 else 0
def trimmedLinearization (α : ℝ) (X : Set (FourTorus c.L m)) (D₀ B : AllLevelFields c.L m K) :
    BondAtLevel c.L m K 0 → ComplexMatrix2 :=
  activeLandauLinearization c.εv (finestMeshInLevelUnits c.L k) α K k
    (gluedTrimmedChain c S Q X) D₀ (familyOnGluedSet c S Q X B)
def componentQuadraticForm (α : ℝ) (X : Set (FourTorus c.L m))
    (D₀ B : AllLevelFields c.L m K) : ℝ :=
  ∑ᶠ p ∈ (plaquettesInside (gluedTrimmedChain c S Q X 0) : Set (PlaquetteAtLevel c.L m K 0)),
    finestMeshInLevelUnits c.L k ^ 4 * combinedCutoff c S Q p.barycenter *
      ComplexMatrix2.operatorNorm (covExteriorDeriv (finestMeshInLevelUnits c.L k)
        (activeGaugeRepresentative c.εv K k (gluedTrimmedChain c S Q X) D₀)
        (trimmedLinearization c S Q α X D₀ B) p.firstAxis p.secondAxis p.origin) ^ 2
def innerRegionOf (X : Set (FourTorus c.L m)) : Set (FourTorus c.L m) :=
  cubeMeet K (S.trimmedRegion c.r x Q (ScaleLabel.nestBaseLevel c.L c.r x k + 1)) X
def innerBoundaryData (X : Set (FourTorus c.L m)) (V' V : AllLevelFields c.L m K) :
    AllLevelFields c.L m K :=
  open Classical in
  fun j b => if (⟨j, b⟩ : Σ q : ℕ, BondAtLevel c.L m K q) ∈ S.nestFixedBonds c.r x Q X
    then V' j b else V j b
def innerBackgroundField (X : Set (FourTorus c.L m)) (V' V : AllLevelFields c.L m K) :
    BondAtLevel c.L m K 0 → ComplexMatrix2 :=
  gluedCriticalConfiguration c.εv K k (Nat.log c.L c.M₁) (ScaleLabel.nestBaseLevel c.L c.r x k)
    (finalStageChain c S Q) (innerRegionOf c S Q X) (innerBoundaryData c S Q X V' V)
def trimmedInvCouplingSq (y : FourTorus c.L m) : ℝ :=
  1 / S.trimmedCoupling c.r x Q y ^ 2
def componentInnerWilson (X : Set (FourTorus c.L m)) (V' V : AllLevelFields c.L m K) : ℂ :=
  variableCouplingEnergy
    (X.indicator fun y => trimmedInvCouplingSq c S Q y * innerShellCutoff c S Q y)
    (innerBackgroundField c S Q X V' V)
def totalInnerWilson (V' V : AllLevelFields c.L m K) : ℂ :=
  ∑ᶠ X ∈ Q, componentInnerWilson c S Q X V' V
def boxTreeOfRotations (ρ : ↥Q → SignedFrame) : Set (IndexedBond c.L m) :=
  ⋃ Y : ↥Q, boxTreeRotated c S Q Y.1 (ρ Y)
def classBoxBonds : Set (Σ q : ℕ, BondAtLevel c.L m K q) :=
  bondsAsSigma (innerBoxBonds c S Q (⋃₀ Q))
def haarScalingCoeff (x : ℕ → ℝ) (k : ℕ) : ℝ :=
  -(1 / 2) * (ComplexMatrix2.realLieDimension : ℝ) * Real.log (x k) +
    Real.log ComplexMatrix2.haarChartDensity
def haarScalingConst (ρ : ↥Q → SignedFrame) : ℝ :=
  haarScalingCoeff x k *
    ((freeBondsOfTree (c := c.toChoiceUpToDegreeConstants) (S.nestFixedBonds c.r x Q (⋃₀ Q))
      (nestTreeOfFrames c.toChoiceUpToDegreeConstants S Q ρ)).ncard : ℝ)
def boxNormalizerConst (ρ : ↥Q → SignedFrame) : ℝ :=
  haarScalingCoeff x k *
    ((freeBondsOfTree (c := c.toChoiceUpToDegreeConstants) (classBoxBonds c S Q)
      (boxTreeOfRotations c S Q ρ)).ncard : ℝ)
def stepConstants (N : AnalyticityConstants) (c : ChoiceUpToDegreeConstants) :
    AnalyticityConstants :=
  { N with cubeExp := Nat.log c.L c.M }
abbrev StepCompletionData (N : AnalyticityConstants) (c : ChoiceUpToRadii) (m K : ℕ)
    (x : ℕ → ℝ) (k : ℕ) : Type :=
  CompletionData (stepConstants N c.toChoiceUpToDegreeConstants)
    (fun j => Nat.log c.L
      (c.L * secondSize c.toChoiceUpToDegreeConstants *
        blockSizeAt c.toChoiceUpToDegreeConstants x j))
    c.L m K k (outerShellLevel c.toChoiceUpToDegreeConstants x k)
variable {N : AnalyticityConstants} (T : StepCompletionData N c m K x k)
def couplingIncrements (x : ℕ → ℝ) (j : ℕ) : ℝ := x (j - 1) - x j
def blockExponents (c : ChoiceUpToRadii) (x : ℕ → ℝ) (j : ℕ) : ℕ :=
  Nat.log c.L (Thresholds.minBlockSize c.L c.r x j)
def termConstants (Y : Set (FourTorus c.L m)) : ℂ :=
  constantTermsMeeting (stepConstants N c.toChoiceUpToDegreeConstants) (blockExponents c x) T Y
structure IsTermCompletionData : Prop where
  isUpdatedLabel : S.IsUpdatedLabelOf c.r x T.scaleLabel Q
  vacuumLocalizes : T.VacuumLocalizes (stepConstants N c.toChoiceUpToDegreeConstants)
def completedBackgroundField (V : AllLevelFields c.L m K)
    (Vb VΛ : BondAtLevel c.L m K k → ComplexMatrix2) :
    BondAtLevel c.L m K 0 → ComplexMatrix2 :=
  S.updatedBackground c.εv c.r x Q V Vb VΛ
def termCompletedEnergy (V : AllLevelFields c.L m K)
    (Vb VΛ : BondAtLevel c.L m K k → ComplexMatrix2) : ℂ :=
  completedEnergy (stepConstants N c.toChoiceUpToDegreeConstants) (couplingIncrements x)
    (blockExponents c x) T (S.updatedInvCoupling c.r x Q)
    (completedBackgroundField c S Q V Vb VΛ) (T.storedFieldsOf V)
def fieldsOnBox (V : AllLevelFields c.L m K) (Vb VΛ : BondAtLevel c.L m K k → ComplexMatrix2) :
    AllLevelFields c.L m K :=
  open Classical in
  Function.update V k fun b => if b ∈ innerBoxBonds c S Q (⋃₀ Q)
    then extendedField (innerBoxBonds c S Q (⋃₀ Q)) Vb VΛ b else V k b
end Objects
end LargeFieldCompletion
end PeriodicLattice
end YangMills.Construction
