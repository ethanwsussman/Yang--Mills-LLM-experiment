import YangMills.Construction.Lattice.ComplexMeasuresWithADensityOnTheBareConfigurations
import YangMills.Construction.Lattice.HistoriesOfOneOutput
import YangMills.Construction.Lattice.MeasureDominatingDensity
import YangMills.Construction.Lattice.MeasuresOfTheFormatOfALevel
import YangMills.Construction.Lattice.TermsFormedByTheConstructionOfTheRange
import YangMills.Construction.PolymerActivities.FlowAtFixedParameters
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction
open MeasureTheory Set ParameterChoice
noncomputable section
namespace PeriodicLattice.RangeConstruction
open CentralBlock LargeFieldCompletion EffectiveDensities FrameAveraging OperationList
  LargeFieldExpansion ComponentReferenceLaw CubesOfStep ClassOperations TermForms
section FramedCompletion
variable (c : ChoiceUpToRadii) {m K : ℕ} {x : ℕ → ℝ} {k : ℕ}
  (S : LabelAtLevel c.toChoiceUpToDegreeConstants m K x k) (Q : Set (Set (FourTorus c.L m)))
  {N : AnalyticityConstants} (T : StepCompletionData N c m K x k)
def framedQuadraticForm (α : ℝ) (𝒱 : Set (FourTorus c.L m) → AllLevelFields c.L m K)
    (ρ : ↥Q → SignedFrame) (B : AllLevelFields c.L m K) : ℝ :=
  ∑ᶠ X : ↥Q, componentQuadFormInFrame c S Q X.1 α (ρ X) (𝒱 X.1) B
def framedFluctuationExponent (α : ℝ) (𝒱 : Set (FourTorus c.L m) → AllLevelFields c.L m K)
    (ρ : ↥Q → SignedFrame) (V : AllLevelFields c.L m K)
    (Vb VΛ : BondAtLevel c.L m K k → Matrices.ComplexMatrix2)
    (V' : AllLevelFields c.L m K) : ℂ :=
  -(1 / 2) * (framedQuadraticForm c S Q α 𝒱 ρ (fluctuationVariables c S Q V') : ℂ) -
    totalInnerWilson c S Q V' V +
    resummedTotal (stepConstants N c.toChoiceUpToDegreeConstants) T Q
      (completedBackgroundField c S Q V Vb VΛ) (fluctuationVariables c S Q V')
      (V (outerShellLevel c.toChoiceUpToDegreeConstants x k))
def framedFluctuationIntegral (α : ℝ) (𝒱 : Set (FourTorus c.L m) → AllLevelFields c.L m K)
    (ρ : ↥Q → SignedFrame) (κ : ℂ) (V : AllLevelFields c.L m K)
    (Vb VΛ : BondAtLevel c.L m K k → Matrices.ComplexMatrix2) : ℂ :=
  gaugeFixedIntegral (c := c.toChoiceUpToDegreeConstants) (S.nestFixedBonds c.r x Q (⋃₀ Q))
    (nestTreeOfFrames c.toChoiceUpToDegreeConstants S Q ρ) fun V' =>
      (fluctuationSmallnessIndicator c.toChoiceUpToDegreeConstants S Q (⋃₀ Q) V' : ℂ) *
        Complex.exp (framedFluctuationExponent c S Q T α 𝒱 ρ V Vb VΛ V' + κ)
def framedIntegrandFactor (α : ℝ) (𝒱 : Set (FourTorus c.L m) → AllLevelFields c.L m K)
    (ρ : ↥Q → SignedFrame) (κ : ℂ) (V : AllLevelFields c.L m K)
    (Vb VΛ : BondAtLevel c.L m K k → Matrices.ComplexMatrix2) : ℂ :=
  (finalDensityIndicator c.toChoiceUpToDegreeConstants x S V : ℂ) *
    ((∏ᶠ X ∈ Q, S.extensionTest c.εv c.A₀ c.𝔭₀ (Nat.log c.L c.M₁) c.r x Q X (V k) : ℝ) : ℂ) *
    ((∏ᶠ X ∈ Q, innerBoxIndicator c S Q X Vb : ℝ) : ℂ) *
    Complex.exp (termCompletedEnergy c S Q T V Vb VΛ) *
    (outerShellIndicator c.toChoiceUpToDegreeConstants S Q
      (V (outerShellLevel c.toChoiceUpToDegreeConstants x k))
      (outerShell c.toChoiceUpToDegreeConstants S Q (⋃₀ Q)) : ℂ) *
    framedFluctuationIntegral c S Q T α 𝒱 ρ κ V Vb VΛ
def framedFormWithConstant (α : ℝ)
    (pair : (↥Q → SignedFrame) → (BondAtLevel c.L m K k → Matrices.ComplexMatrix2) →
      (BondAtLevel c.L m K k → Matrices.ComplexMatrix2) ×
        (BondAtLevel c.L m K 0 → Matrices.ComplexMatrix2))
    (𝒟 : (BondAtLevel c.L m K 0 → Matrices.ComplexMatrix2) → AllLevelFields c.L m K →
      Set (FourTorus c.L m) → AllLevelFields c.L m K)
    (ρ : ↥Q → SignedFrame) (κ : ℂ) : FieldFunctional c.L m K :=
  fun G V => gaugeFixedIntegral (c := c.toChoiceUpToDegreeConstants)
    (classBoxBonds c S Q) (boxTreeOfRotations c S Q ρ) fun V' =>
      let P := pair ρ (V k)
      let F := fieldsOnBox c S Q V (V' k) P.1
      framedIntegrandFactor c S Q T α (𝒟 P.2 F) ρ κ F (V' k) P.1 * G F
def framedCompletedForm (α : ℝ)
    (pair : (↥Q → SignedFrame) → (BondAtLevel c.L m K k → Matrices.ComplexMatrix2) →
      (BondAtLevel c.L m K k → Matrices.ComplexMatrix2) ×
        (BondAtLevel c.L m K 0 → Matrices.ComplexMatrix2))
    (ρ : ↥Q → SignedFrame) : FieldFunctional c.L m K :=
  framedFormWithConstant c S Q T α pair (fun U₀ V _ => basicBackgroundData c S Q U₀ V) ρ
    (termConstants c T (⋃₀ Q) + (haarScalingConst c S Q ρ : ℂ) -
      termConstants c T (S.innerBox c.r x Q))
def framedCompletedFormEffective (α : ℝ)
    (pair : (↥Q → SignedFrame) → (BondAtLevel c.L m K k → Matrices.ComplexMatrix2) →
      (BondAtLevel c.L m K k → Matrices.ComplexMatrix2) ×
        (BondAtLevel c.L m K 0 → Matrices.ComplexMatrix2))
    (ρ : ↥Q → SignedFrame) : FieldFunctional c.L m K :=
  framedFormWithConstant c S Q T α pair
    (fun U₀ V X => basicBackgroundDataOfComponent c S Q X U₀ V) ρ
    (termConstants c T (⋃₀ Q) - (boxNormalizerConst c S Q ρ : ℂ))
end FramedCompletion
section Result
variable {N : AnalyticityConstants} {a : FullChoice} {m K : ℕ} {x : ℕ → ℝ} {E : ℕ → Type}
  {k : ℕ} (𝒯 : Set (ClassedTerm N a m K x E k)) (t₀ : ClassedTerm N a m K x E k)
  (form : DisplayForm) (α : ℝ) (r : Set (FourTorus a.L m) → SignedFrame)
  (evalOnSigma : ConnectionType)
def framedResultTerm : FieldFunctional a.L m K :=
  t₀.otherOps fun G W =>
    frameAverage t₀.remainingComponents fun ρ =>
      let P := t₀.framePair α ρ (W k)
      gaugeFixedIntegral (c := degreeChoice a) (bondsAsSigma t₀.classTwoBoxBonds)
        (t₀.classTwoTrees ρ) fun V' =>
          let W' := Function.update W k (t₀.classTwoField (V' k) P.1 (W k))
          (t₀.newDomainIndicator (W' k) : ℂ) *
            Complex.exp (termCompletedEnergy (radiiChoice a) t₀.stepLabel t₀.remainingComponents
              t₀.completionData W' (relativeVariable t₀.innerBoxBondSet (W' k) P.1) P.1) *
            (t₀.classTwoIndicators (W' k) (V' k) : ℂ) *
            ruleProduct t₀ form α P ρ t₀.secondClass
              (ruleProduct t₀ form α P ρ t₀.firstClass
                (t₀.trailingFunction P.1 G))
              (unsetVariables a.L m K, W')
def framedCompletedFormOfTerm (ρ : ↥t₀.remainingComponents → SignedFrame) :
    FieldFunctional a.L m K :=
  match form with
  | .original =>
    framedCompletedForm (radiiChoice a) t₀.stepLabel t₀.remainingComponents t₀.completionData α
      (t₀.framePair α) ρ
  | .effective =>
    framedCompletedFormEffective (radiiChoice a) t₀.stepLabel t₀.remainingComponents
      t₀.completionData α (t₀.framePair α) ρ
def framedTermAfterCompletion : FieldFunctional a.L m K :=
  fun G W =>
    frameAverage t₀.remainingComponents fun ρ =>
      haarIntegralOn (lowerBondsOffDomain (degreeChoice a) x t₀.stepLabel t₀.remainingComponents
          t₀.unionRegion) W
        fun W₁ => t₀.lowerOp.integral W₁ fun y =>
          t₀.lowerOp.factor y (t₀.lowerOp.down y (t₀.lowerOp.up y W₁)) *
            framedCompletedFormOfTerm t₀ form α ρ G
              (t₀.lowerOp.down y (t₀.lowerOp.up y W₁))
def FramedClusterExpansionConvergesAt (R : FluctuationFieldPair a.L m K) : Prop :=
  ∃ h : (framedPolymerSet 𝒯 t₀ evalOnSigma).Finite,
    letI := h.fintype
    (framedPolymerRelation 𝒯 t₀ evalOnSigma).ClusterSeriesAbsConv fun Z =>
      framedActivity 𝒯 t₀ form α r evalOnSigma Z.1 R
def completedBackgroundPair (VΛ : BondAtLevel a.L m K k → Matrices.ComplexMatrix2)
    (X : Set (FourTorus a.L m)) (R : FluctuationFieldPair a.L m K) : FieldCurrentPair a.L m K :=
  restrictPairTo X (configurationPair k
    (completedBackgroundField (radiiChoice a) t₀.stepLabel t₀.remainingComponents R.2
      (relativeVariable t₀.innerBoxBondSet (R.2 k) VΛ) VΛ))
def CarriesInteriorTerms (ϱ : LocalActivities a.L m K) : Prop :=
  ∀ t₀ ∈ 𝒯, t₀.firstClass = ∅ →
    ∀ (f : ↥t₀.remainingComponents → SignedFrame) (R : FluctuationFieldPair a.L m K),
      FramedClusterExpansionConvergesAt 𝒯 t₀ form α (extendedFrames t₀ f) evalOnSigma R →
        ∀ X ∈ interiorDomains t₀,
          framedClusterSum 𝒯 t₀ form α (extendedFrames t₀ f) evalOnSigma X R =
            ϱ X (completedBackgroundPair t₀ (t₀.framePair α f (R.2 k)).1 X R)
def IsResultTermMeasure (ν : ComplexMeasure (BlockFields a.L m K k)) : Prop :=
  ∀ F : BlockFields a.L m K k → ℂ, IsBoundedMeasurableBlockFunction F →
    Integrable (fun V => framedResultTerm t₀ form α (blockFieldFunction F)
        (datumOnLevel K k V)) (haarMeasureAtLevel a.L m K k) ∧
      ν.integral F (ContinuousLinearMap.mul ℝ ℂ) =
        ∫ V, framedResultTerm t₀ form α (blockFieldFunction F) (datumOnLevel K k V)
          ∂haarMeasureAtLevel a.L m K k
end Result
section Families
variable {N : AnalyticityConstants} {a : FullChoice} {m K : ℕ} {x : ℕ → ℝ} {E : ℕ → Type}
  {s : ActivityDomainKind} {l k : ℕ}
structure ReadsStepFamilies (t : ClassedTerm N a m K x E (k + 1))
    (P : FlowExpansions (degreeChoice a) K ![a.C₀, a.C₁] s l x)
    (ϱ : ℕ → LocalActivities a.L m K) : Prop where
  regular : ∀ i : Fin l, (i : ℕ) ≤ k →
    ∀ X ∈ regularPolymerDomains (L := a.L) K (Nat.log a.L (degreeChoice a).M) ((i : ℕ) + 1)
        (t.stepLabel.smallFieldSeq ((i : ℕ) + 1)),
      t.actionData.regularActs ((i : ℕ) + 1) X = (P i).fullFamilies m X
  remainder : ∀ j ∈ Finset.Icc 1 k,
    ∀ X ∈ remainderPolymerDomains (L := a.L) K (Nat.log a.L (degreeChoice a).M)
        (Nat.log a.L (blockSizeAt (degreeChoice a) x j)) j (t.stepLabel.smallFieldSeq j),
      t.actionData.remainderActs j X = ϱ j X
structure FamiliesReadAndMade (𝒰 : Set (ClassedTerm N a m K x E (k + 1)))
    (𝔗 : Set (Set (ClassedTerm N a m K x E (k + 1))))
    (form : DisplayForm) (α : ℝ) (evalOnSigma : ConnectionType)
    (P : FlowExpansions (degreeChoice a) K ![a.C₀, a.C₁] s l x)
    (ϱ : ℕ → LocalActivities a.L m K) : Prop where
  read : ∀ t ∈ 𝒰, ReadsStepFamilies t P ϱ
  made : ∀ 𝒯 ∈ 𝔗, CarriesInteriorTerms 𝒯 form α evalOnSigma (ϱ (k + 1))
def SameDisplayIndex (t t' : ClassedTerm N a m K x E k) : Prop :=
  t.exteriorData = t'.exteriorData ∧ t.secondClass = t'.secondClass ∧
    t.firstClass = t'.firstClass ∧
      ∀ Y ∈ t.remainingComponents, t.localizedSequence Y = t'.localizedSequence Y
structure IsOperationTrace (𝒪 : RGStepOperation a m K x)
    (h : DecomposedHistory (degreeChoice a) m K x k) (σ : StepTrace (degreeChoice a) m K x k)
    (o : DecomposedOperation (degreeChoice a) m K x k) : Prop where
  produced : 𝒪.Generates h
  step : σ.IsStepOf h.finalLabel
  operation : o.IsOperationOn ⟨h, σ⟩ (𝒪.classing k ⟨h, σ⟩)
  tests : UsesOnlySlotsOf 𝒪.form o
structure IsOperationOutput (𝒪 : RGStepOperation a m K x)
    (h : DecomposedHistory (degreeChoice a) m K x k) (σ : StepTrace (degreeChoice a) m K x k)
    (o : DecomposedOperation (degreeChoice a) m K x k) : Prop extends
    IsOperationTrace 𝒪 h σ o where
  noHealed : NoRepairs h
structure ResultTerms (T : DerivedConstants) (a : FullChoice) (m K : ℕ) (x : ℕ → ℝ) where
  term : ∀ k : ℕ, DecomposedHistory (degreeChoice a) m K x k →
    StepTrace (degreeChoice a) m K x k → DecomposedOperation (degreeChoice a) m K x k →
    ClassedTerm (AnalyticityConstants.ofChoice T a) a m K x
      (LevelDecomposition (degreeChoice a) m x) (k + 1)
  display : ∀ k : ℕ, Set (ClassedTerm (AnalyticityConstants.ofChoice T a) a m K x
    (LevelDecomposition (degreeChoice a) m x) (k + 1))
variable {T : DerivedConstants}
def ResultTerms.retainedTerms (u : ResultTerms T a m K x) (𝒪 : RGStepOperation a m K x) (k : ℕ) :
    Set (ClassedTerm (AnalyticityConstants.ofChoice T a) a m K x
      (LevelDecomposition (degreeChoice a) m x) (k + 1)) :=
  {t | ∃ (h : DecomposedHistory (degreeChoice a) m K x k)
    (σ : StepTrace (degreeChoice a) m K x k) (o : DecomposedOperation (degreeChoice a) m K x k),
    IsOperationOutput 𝒪 h σ o ∧ t = u.term k h σ o}
def ResultTerms.outputTerms (u : ResultTerms T a m K x) (𝒪 : RGStepOperation a m K x) (k : ℕ)
    (g : DecomposedHistory (degreeChoice a) m K x (k + 1)) :
    Set (ClassedTerm (AnalyticityConstants.ofChoice T a) a m K x
      (LevelDecomposition (degreeChoice a) m x) (k + 1)) :=
  {t | ∃ (h : DecomposedHistory (degreeChoice a) m K x k)
    (σ : StepTrace (degreeChoice a) m K x k) (o : DecomposedOperation (degreeChoice a) m K x k),
    IsOperationOutput 𝒪 h σ o ∧ t = u.term k h σ o ∧ SameOutput (LabelHistory.extend h σ o) g}
def ResultTerms.outputs (u : ResultTerms T a m K x) (𝒪 : RGStepOperation a m K x) (k : ℕ) :
    Set (Set (ClassedTerm (AnalyticityConstants.ofChoice T a) a m K x
      (LevelDecomposition (degreeChoice a) m x) (k + 1))) :=
  {𝒯 | ∃ (h : DecomposedHistory (degreeChoice a) m K x k)
    (σ : StepTrace (degreeChoice a) m K x k) (o : DecomposedOperation (degreeChoice a) m K x k),
    IsOperationOutput 𝒪 h σ o ∧ 𝒯 = u.outputTerms 𝒪 k (LabelHistory.extend h σ o)}
def framedSecondClassLower {E : ℕ → Type} (t : ClassedTerm N a m K x E k)
    (form : DisplayForm) (α : ℝ) (Y : Set (FourTorus a.L m)) : LowerOperation a.L m K :=
  { secondClassLower t form α Y with
    factor := fun p V =>
      let P := t.componentPair α Y p.frame (V k)
      let V' := patchVariables (t.stepLabel.nestFixedBonds a.r x t.remainingComponents Y) p.gaugeField
        (unsetVariables a.L m K)
      ((secondKindIndicator (degreeChoice a) K x (Nat.log a.L (degreeChoice a).M) k (V k) Y *
          t.stepLabel.extensionTest (degreeChoice a).εv a.A₀ a.𝔭₀ (Nat.log a.L a.M₁) a.r x
            t.remainingComponents Y (V k) : ℝ) : ℂ) *
        (innerBoxIndicator (radiiChoice a) t.stepLabel t.remainingComponents Y (p.boxField k) : ℂ) *
        (fluctuationSmallnessIndicator (degreeChoice a) t.stepLabel t.remainingComponents Y V' : ℂ) *
        (outerShellIndicator (degreeChoice a) t.stepLabel t.remainingComponents
            (V (outerShellLevel (degreeChoice a) x k))
            (outerShell (degreeChoice a) t.stepLabel t.remainingComponents Y) : ℂ) *
        (t.componentLowerOp Y).factor p.lower V *
        Complex.exp (componentExponentInFrame (radiiChoice a) t.stepLabel t.remainingComponents Y
            t.completionData α p.frame
            (displayDatum (radiiChoice a) t.stepLabel t.remainingComponents Y form P.2 V)
            V (relativeVariable t.innerBoxBondSet (V k) P.1) P.1 V' +
          componentConstants (radiiChoice a) t.stepLabel t.remainingComponents Y p.frame
            t.completionData form) }
def DeterminesFramedCompletedForm {E : ℕ → Type} (t : ClassedTerm N a m K x E k)
    (form : DisplayForm) (α : ℝ) (T₀ : DerivedConstants) (𝒲 : Set (AllLevelFields a.L m K)) :
    Prop :=
  ∀ F : BlockFields a.L m K k → ℂ, IsBoundedMeasurableBlockFunction F → ∀ W ∈ 𝒲,
    ∫ V, termBeforeCompletion t form α T₀ (blockFieldFunction F) (Function.update W k V)
        ∂haarMeasureAtLevel a.L m K k =
      ∫ V, framedTermAfterCompletion t form α (blockFieldFunction F) (Function.update W k V)
        ∂haarMeasureAtLevel a.L m K k
structure IsFramedOperationTerm (τ : BackgroundVariant) (form : DisplayForm) {α : ℝ}
    (ς : PairSelections a m K x α)
    (t : ClassedTerm (AnalyticityConstants.ofChoice T a) a m K x
      (LevelDecomposition (degreeChoice a) m x) (k + 1))
    (h : DecomposedHistory (degreeChoice a) m K x k) (s : StepTrace (degreeChoice a) m K x k)
    (o : DecomposedOperation (degreeChoice a) m K x k) : Prop where
  history_eq : t.hist = TermOfStep.historyBeforeLargeField ⟨h, s⟩
  remaining_eq : t.remainingComponents = OperationTrace.survivors o
  components_eq : ∀ n < t.stageCount, t.componentsAt n = stageComponentsOf o n
  firstClass_eq : t.firstClass = o.outcome.classOne
  pair_eq : ∀ Q ρ V, t.basePair α Q ρ V = (ς k h s).pair Q ρ V
  isDatum : LargeFieldCompletion.IsTermCompletionData (radiiChoice a) t.stepLabel
    t.remainingComponents t.completionData
  families : TermDataInClasses t T
  stageTerms : IsStagesLocalization T a x t.actionData t.componentsAt t.localTerms τ t.hist
    (stageVariantOf form) (stagePoints t form T τ {W | SupportedByHistory h W})
  dependsOnForm : DeterminesFramedCompletedForm t form α T {W | SupportedByHistory h W}
inductive IsLeftOperationAt (u : ResultTerms T a m K x) (τ : BackgroundVariant)
    (form : DisplayForm) {α : ℝ} (ς : PairSelections a m K x α) :
    ∀ {k : ℕ}, DecomposedHistory (degreeChoice a) m K x k → Set (FourTorus a.L m) →
      LowerOperation a.L m K → Prop
  | untouched {k : ℕ} (h : DecomposedHistory (degreeChoice a) m K x k) (X : Set (FourTorus a.L m))
      (hX : ∀ Y ∈ h.actedParts, Disjoint Y X) :
      IsLeftOperationAt u τ form ς h X
        (lowerStepsProductWithin (radiiChoice a) x τ h k le_rfl X)
  | untouchedAtLevel {k : ℕ} (h : DecomposedHistory (degreeChoice a) m K x k)
      (s : StepTrace (degreeChoice a) m K x k) (o : DecomposedOperation (degreeChoice a) m K x k)
      (X : Set (FourTorus a.L m)) (T₀ : LowerOperation a.L m K)
      (hX : ∀ Y ∈ o.actedOn, Disjoint Y X)
      (hT : IsLeftOperationAt u τ form ς h (h.finalLabel.largeFieldOrEmpty k ∩ X) T₀) :
      IsLeftOperationAt u τ form ς (LabelHistory.extend h s o) X
        (stepsAboveWithin (radiiChoice a) x τ (LabelHistory.extend h s o) X k T₀)
  | secondClass {k : ℕ} (h : DecomposedHistory (degreeChoice a) m K x k)
      (s : StepTrace (degreeChoice a) m K x k) (o : DecomposedOperation (degreeChoice a) m K x k)
      (Y : Set (FourTorus a.L m))
      (ht : IsFramedOperationTerm τ form ς (u.term k h s o) h s o)
      (hY : Y ∈ o.outcome.classTwo)
      (hLower : ∀ X ∈ (u.term k h s o).remainingComponents,
        ∀ hf : lowerStep (degreeChoice a) x (k + 1) < k + 1,
          IsLeftOperationAt u τ form ς ((LabelHistory.extend h s o).stepEntry _ hf).prior
            ((u.term k h s o).stepLabel.largeFieldOrEmpty (lowerStep (degreeChoice a) x (k + 1)) ∩ X)
            ((u.term k h s o).componentLowerOp X))
      (hUnion : ∀ hf : lowerStep (degreeChoice a) x (k + 1) < k + 1,
        IsLeftOperationAt u τ form ς ((LabelHistory.extend h s o).stepEntry _ hf).prior
          ((u.term k h s o).stepLabel.largeFieldOrEmpty (lowerStep (degreeChoice a) x (k + 1)) ∩
            (u.term k h s o).unionRegion) (u.term k h s o).lowerOp) :
      IsLeftOperationAt u τ form ς (LabelHistory.extend h s o) Y
        (framedSecondClassLower (u.term k h s o) form α Y)
  | dropped {k : ℕ} (h : DecomposedHistory (degreeChoice a) m K x k)
      (s : StepTrace (degreeChoice a) m K x k) (o : DecomposedOperation (degreeChoice a) m K x k)
      (X : Set (FourTorus a.L m)) (T₀ : LowerOperation a.L m K)
      (hX : X ∈ o.outcome.dropped) : IsLeftOperationAt u τ form ς (LabelHistory.extend h s o) X T₀
  | union {k : ℕ} (h : DecomposedHistory (degreeChoice a) m K x k) (X Y : Set (FourTorus a.L m))
      (A B : LowerOperation a.L m K) (hXY : Disjoint X Y)
      (hXc : IsUnionOfLargeFieldParts (degreeChoice a) h.finalLabel X)
      (hYc : IsUnionOfLargeFieldParts (degreeChoice a) h.finalLabel Y)
      (hA : IsLeftOperationAt u τ form ς h X A) (hB : IsLeftOperationAt u τ form ς h Y B) :
      IsLeftOperationAt u τ form ς h (X ∪ Y) (A.prodDisjoint B)
def IsComponentOperationAt (u : ResultTerms T a m K x) (τ : BackgroundVariant)
    (form : DisplayForm) {α : ℝ} (ς : PairSelections a m K x α) {k : ℕ}
    (h : DecomposedHistory (degreeChoice a) m K x k) (X : Set (FourTorus a.L m))
    (O : FieldFunctional a.L m K → FieldFunctional a.L m K) : Prop :=
  ((∀ Y ∈ h.actedParts, Disjoint Y X) ∧
      O = largeFieldOperationWithin (radiiChoice a) x τ h X) ∨
    ((∃ Y ∈ h.actedParts, ¬Disjoint Y X) ∧
      ∃ T₀, IsLeftOperationAt u τ form ς h X T₀ ∧ O = T₀.applyTo)
def exteriorComponents (t : ClassedTerm N a m K x E k) : Set (Set (FourTorus a.L m)) :=
  regionComponents (coarseCubeIndex K (Nat.log a.L (degreeChoice a).M) k) t.exteriorData.1
structure RestsOnLeftOperations (u : ResultTerms T a m K x) (τ : BackgroundVariant)
    (form : DisplayForm) {α : ℝ} (ς : PairSelections a m K x α)
    (h : DecomposedHistory (degreeChoice a) m K x k) (σ : StepTrace (degreeChoice a) m K x k)
    (o : DecomposedOperation (degreeChoice a) m K x k) : Prop where
  lowerIn : ∀ X ∈ (u.term k h σ o).remainingComponents,
    ∀ hf : lowerStep (degreeChoice a) x (k + 1) < k + 1,
      IsLeftOperationAt u τ form ς ((LabelHistory.extend h σ o).stepEntry _ hf).prior
        ((u.term k h σ o).stepLabel.largeFieldOrEmpty (lowerStep (degreeChoice a) x (k + 1)) ∩ X)
        ((u.term k h σ o).componentLowerOp X)
  lower : ∀ hf : lowerStep (degreeChoice a) x (k + 1) < k + 1,
    IsLeftOperationAt u τ form ς ((LabelHistory.extend h σ o).stepEntry _ hf).prior
      ((u.term k h σ o).stepLabel.largeFieldOrEmpty (lowerStep (degreeChoice a) x (k + 1)) ∩
        (u.term k h σ o).unionRegion) (u.term k h σ o).lowerOp
  others : ∃ O : Set (FourTorus a.L m) → FieldFunctional a.L m K → FieldFunctional a.L m K,
    (∀ X ∈ exteriorComponents (u.term k h σ o),
      IsComponentOperationAt u τ form ς (LabelHistory.extend h σ o) X (O X)) ∧
    (u.term k h σ o).otherOps = composeOperations (exteriorComponents (u.term k h σ o)) O
def stepOutputMeasure (w : FlowTerms a m K x) (𝒪 : RGStepOperation a m K x)
    (h : DecomposedHistory (degreeChoice a) m K x k) (σ : StepTrace (degreeChoice a) m K x k)
    (o : DecomposedOperation (degreeChoice a) m K x k) :
    ComplexMeasure (BlockFields a.L m K (k + 1)) :=
  ∑ᶠ h' ∈ {h' | IsOperationTrace 𝒪 h' σ o ∧ SameOutput h' h},
    (w.atHistory (k + 1) (LabelHistory.extend h' σ o)).blockMeasure
structure AreOperationResultTerms (u : ResultTerms T a m K x) (w : FlowTerms a m K x)
    (τ : BackgroundVariant) (form : DisplayForm) {α : ℝ}
    (ς : PairSelections a m K x α) (𝒪 : RGStepOperation a m K x) (k : ℕ) : Prop where
  term : ∀ (h : DecomposedHistory (degreeChoice a) m K x k)
    (σ : StepTrace (degreeChoice a) m K x k) (o : DecomposedOperation (degreeChoice a) m K x k),
    IsOperationOutput 𝒪 h σ o → IsFramedOperationTerm τ form ς (u.term k h σ o) h σ o
  left : ∀ (h : DecomposedHistory (degreeChoice a) m K x k)
    (σ : StepTrace (degreeChoice a) m K x k) (o : DecomposedOperation (degreeChoice a) m K x k),
    IsOperationOutput 𝒪 h σ o → RestsOnLeftOperations u τ form ς h σ o
  measure : ∀ (h : DecomposedHistory (degreeChoice a) m K x k)
    (σ : StepTrace (degreeChoice a) m K x k) (o : DecomposedOperation (degreeChoice a) m K x k),
    IsOperationOutput 𝒪 h σ o →
      IsResultTermMeasure (u.term k h σ o) form α (stepOutputMeasure w 𝒪 h σ o)
  display_subset : u.display k ⊆ u.retainedTerms 𝒪 k
  display_covers : ∀ t ∈ u.retainedTerms 𝒪 k, ∃ t' ∈ u.display k, SameDisplayIndex t t'
  display_unique : ∀ t ∈ u.display k, ∀ t' ∈ u.display k, SameDisplayIndex t t' → t = t'
end Families
section Construction
variable (T : DerivedConstants) (a : FullChoice) {K : ℕ}
def stepTorusExponents {s : ActivityDomainKind} {l : ℕ} {x : ℕ → ℝ} (m : ℕ)
    (P : FlowExpansions (degreeChoice a) K ![a.C₀, a.C₁] s l x) : Set ℕ :=
  {n | n = m ∨ ∃ k : Fin l, n ∈ (P k).sizes.sizes}
variable [∀ n j, Finite (SiteAtLevel a.L n K j)]
structure IsDefinedThrough (m : ℕ) (s : ActivityDomainKind) (φ : CollarTestForm)
    (τ : BackgroundVariant) (form : DisplayForm) (evalOnSigma : ConnectionType)
    {α : ℝ} (ν₀ : ∀ n : ℕ, ComplexMeasure (BlockFields a.L n K 0)) (l : ℕ) (x : ℕ → ℝ)
    (c : ∀ n : ℕ, CourseChoices a n K x α) (𝒪 : ∀ n : ℕ, RGStepOperation a n K x)
    (t : ∀ n : ℕ, FlowTerms a n K x) (u : ∀ n : ℕ, ResultTerms T a n K x)
    (P : FlowExpansions (degreeChoice a) K ![a.C₀, a.C₁] s l x)
    (ϱ : ∀ n : ℕ, ℕ → LocalActivities a.L n K) : Prop where
  terms : ∀ n ∈ stepTorusExponents a m P, IsRangeGenerated (t n) T φ (c n) (𝒪 n) (ν₀ n) l
  sides : ∀ n ∈ stepTorusExponents a m P, ∀ k : Fin l, n ∈ (P k).sizes.sizes
  params_eq : ∀ k : Fin l, ∀ n ∈ (P k).sizes.sizes,
    (P k).params n = ChoiceConstants.ofFullChoice T a
  performed : ∀ k : Fin l, PriorStepsCompleted (degreeChoice a) K ![a.C₀, a.C₁] s P ϱ a.E₀ k
  result : ∀ n ∈ stepTorusExponents a m P, ∀ k : Fin l,
    AreOperationResultTerms (u n) (t n) τ form (c n).selection (𝒪 n) k
  families : ∀ n ∈ stepTorusExponents a m P, ∀ k : Fin l,
    FamiliesReadAndMade ((u n).retainedTerms (𝒪 n) k) ((u n).outputs (𝒪 n) k) form α evalOnSigma P
      (ϱ n)
  shift_defined : ∀ k : Fin l, (P k).HasRealStiffness (P k).fullFamilies
  next : ∀ k : Fin l, x ((k : ℕ) + 1) = x k - (P k).couplingShift
end Construction
section ScaleFlow
variable (D : FixedParameterFlow) [∀ n j, Finite (SiteAtLevel D.params.L n D.K j)]
structure IsSelfConsistentFlow (φ : CollarTestForm) (τ : BackgroundVariant)
    (form : DisplayForm) (evalOnSigma : ConnectionType) {α : ℝ} (l : ℕ) (x : ℕ → ℝ)
    (c : ∀ n : ℕ, CourseChoices D.params n D.K x α)
    (t : ∀ n : ℕ, FlowTerms D.params n D.K x)
    (u : ∀ n : ℕ, ResultTerms D.derived D.params n D.K x)
    (P : FlowExpansions (degreeChoice D.params) D.K ![D.params.C₀, D.params.C₁]
      D.activityDomain l x)
    (ϱ : ∀ n : ℕ, ℕ → LocalActivities D.params.L n D.K) : Prop where
  bare : x 0 = D.β
  defined : IsDefinedThrough D.derived D.params D.m D.activityDomain φ τ form evalOnSigma
    (fun n => boltzmannMeasure D.params.L n D.K D.β) l x c (fun _ => effectiveOperation D.params x)
    t u P ϱ
  regular : IsRegularFlow (degreeChoice D.params) D.K ![D.params.C₀, D.params.C₁]
    D.activityDomain P (ChoiceConstants.ofFullChoice D.derived D.params) (fun _ => ϱ)
    D.params.E₀ D.β
end ScaleFlow
end PeriodicLattice.RangeConstruction
end
end YangMills.Construction
