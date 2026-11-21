import YangMills.Construction.Lattice.AdmissibleHistoriesAndLabels
import YangMills.Construction.Lattice.FieldsReadOverTheHaarValuesOfAStep
import YangMills.Construction.Lattice.OperationsOfTheStepsReadInTheRegion
import YangMills.Construction.Lattice.PolymerExpansionAndOutputOfTheOperation
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Set MeasureTheory ParameterChoice
namespace PeriodicLattice.CubesOfStep
open ClassOperations LargeFieldExpansion
namespace LowerOperation
variable {L m K : ℕ}
def applyTo (T : LowerOperation L m K) (Φ : FieldFunctional L m K) :
    FieldFunctional L m K :=
  fun G W => T.integral W fun y => Φ (fun V => T.factor y V * G V) (T.down y (T.up y W))
def prodDisjoint (A B : LowerOperation L m K) : LowerOperation L m K where
  Variables := A.Variables × B.Variables
  integral := fun W Ψ => A.integral W fun y => B.integral W fun z => Ψ (y, z)
  up := fun p W => B.up p.2 (A.up p.1 W)
  down := fun p V => A.down p.1 (B.down p.2 V)
  factor := fun p V => A.factor p.1 V * B.factor p.2 V
end LowerOperation
section Above
variable {m K : ℕ} (c : ChoiceUpToRadii) (x : ℕ → ℝ) {E : ℕ → Type} {k : ℕ}
  (τ : BackgroundVariant) (h : LabelHistory c.toChoiceUpToDegreeConstants m K x E k)
  (X : Set (FourTorus c.L m))
def stepsAbove (l : ℕ) (T : LowerOperation c.L m K) :
    LowerOperation c.L m K where
  Variables := T.Variables × AllStepVariables c x h X
  integral := fun W Ψ =>
    iteratedStepIntegralFrom c x h X l W
      (fun A => T.integral (updateHaarAt l A W) fun y => Ψ (y, A)) k le_rfl
      (placeholderVariables c x h X)
  up := fun p W => liftFrom l p.2 (T.up p.1 (updateHaarAt l p.2 W))
  down := fun p V => T.down p.1 (fieldsDownwardFrom c x τ h X l p.2 k le_rfl V)
  factor := fun p V =>
    (∏ i : Fin k, if l ≤ (i : ℕ) then
        operationWeight c x (stepBasePoints c) τ h i.2 X (p.2 i).2 V
      else 1) * T.factor p.1 V
def stepsAboveWithin (l : ℕ) (T : LowerOperation c.L m K) :
    LowerOperation c.L m K :=
  { stepsAbove c x τ h X l T with
    factor := fun p V =>
      (∏ i : Fin k, if l ≤ (i : ℕ) then
          stepWeightWithin c x (stepBasePoints c) τ h i.2 X (p.2 i).2 V
        else 1) * T.factor p.1 V }
end Above
section SecondClass
open CentralBlock LargeFieldCompletion ComponentReferenceLaw TermForms
structure SecondClassVariables {L m K : ℕ} (𝔹 : Set (Σ q : ℕ, BondAtLevel L m K q))
    (T : LowerOperation L m K) where
  frame : SignedFrame
  boxField : AllLevelFields L m K
  gaugeField : AllLevelFields L m K
  shellValues : ↥(positiveBondsIn 𝔹) → Matrices.ComplexMatrix2
  lower : T.Variables
variable {N : AnalyticityConstants} {a : FullChoice} {m K : ℕ} {x : ℕ → ℝ} {E : ℕ → Type}
  {k : ℕ} (t : ClassedTerm N a m K x E k) (form : DisplayForm) (α : ℝ)
  (Y : Set (FourTorus a.L m))
def boxFields (f : SignedFrame) (V' V : AllLevelFields a.L m K) : AllLevelFields a.L m K :=
  Function.update V k (componentField t Y (V' k) (t.componentPair α Y f (V k)).1 (V k))
abbrev shellBondSet : Set (Σ q : ℕ, BondAtLevel a.L m K q) :=
  lowerBondsOffDomain (degreeChoice a) x t.stepLabel t.remainingComponents Y
def secondClassLower : LowerOperation a.L m K where
  Variables := SecondClassVariables (shellBondSet (x := x) t Y) (t.componentLowerOp Y)
  integral := fun W Ψ =>
    ((signedFrameCount : ℂ)⁻¹) * ∑ᶠ f : SignedFrame,
      gaugeFixedIntegral (c := degreeChoice a)
        (bondsAsSigma (innerBoxBonds (radiiChoice a) t.stepLabel t.remainingComponents Y))
        (boxTreeRotated (radiiChoice a) t.stepLabel t.remainingComponents Y f) fun V' =>
          gaugeFixedIntegral (c := degreeChoice a)
            (t.stepLabel.nestFixedBonds a.r x t.remainingComponents Y)
            (nestTreeInFrame (degreeChoice a) t.stepLabel t.remainingComponents Y f) fun V₁ =>
              ∫ w, (t.componentLowerOp Y).integral
                  (fieldsAssignedOn (shellBondSet (x := x) t Y)
                    (fun e => (w e : Matrices.ComplexMatrix2)) (boxFields t α Y f V' W))
                  (fun y => Ψ ⟨f, V', V₁, fun e => (w e : Matrices.ComplexMatrix2), y⟩)
                ∂Matrices.ComplexMatrix2.haarPi ↥(positiveBondsIn (shellBondSet (x := x) t Y))
  up := fun p W =>
    (t.componentLowerOp Y).up p.lower
      (fieldsAssignedOn (shellBondSet (x := x) t Y) p.shellValues
        (boxFields t α Y p.frame p.boxField W))
  down := fun p V => (t.componentLowerOp Y).down p.lower (boxFields t α Y p.frame p.boxField V)
  factor := fun p V =>
    let P := t.componentPair α Y p.frame (V k)
    let V' := patchVariables (t.stepLabel.nestFixedBonds a.r x t.remainingComponents Y)
      p.gaugeField (unsetVariables a.L m K)
    ((secondKindIndicator (degreeChoice a) K x (Nat.log a.L (degreeChoice a).M) k (V k) Y *
        t.stepLabel.extensionTest (degreeChoice a).εv a.A₀ a.𝔭₀ (Nat.log a.L a.M₁) a.r x
          t.remainingComponents Y (V k) : ℝ) : ℂ) *
      (innerBoxIndicator (radiiChoice a) t.stepLabel t.remainingComponents Y (p.boxField k) : ℂ) *
      (fluctuationSmallnessIndicator (degreeChoice a) t.stepLabel t.remainingComponents Y V' : ℂ) *
      (outerShellIndicator (degreeChoice a) t.stepLabel t.remainingComponents
          (V (outerShellLevel (degreeChoice a) x k))
          (CentralBlock.outerShell (degreeChoice a) t.stepLabel t.remainingComponents Y) : ℂ) *
      (t.componentLowerOp Y).factor p.lower V *
      Complex.exp (componentExponent (radiiChoice a) t.stepLabel t.remainingComponents Y
          t.completionData α
          (displayDatum (radiiChoice a) t.stepLabel t.remainingComponents Y form P.2 V) V
          (relativeVariable t.innerBoxBondSet (V k) P.1) P.1 V' +
        componentConstants (radiiChoice a) t.stepLabel t.remainingComponents Y p.frame
          t.completionData form)
end SecondClass
section Carried
variable {a : FullChoice} {m K : ℕ} {x : ℕ → ℝ}
def historyTests : ∀ {k : ℕ}, DecomposedHistory (degreeChoice a) m K x k →
    (BondAtLevel a.L m K k → Matrices.ComplexMatrix2) → ℝ
  | _, .initial, _ => 1
  | _, .extend _ _ o, V => densityWeight (degreeChoice a) K x o.label o.outcome V
def SupportedByHistory : ∀ {k : ℕ}, DecomposedHistory (degreeChoice a) m K x k →
    AllLevelFields a.L m K → Prop
  | _, .initial, _ => True
  | k + 1, .extend h s o, W =>
    historyTests (LabelHistory.extend h s o) (W (k + 1)) ≠ 0 ∧ SupportedByHistory h W
def blockFieldFunction {L k : ℕ} (F : BlockFields L m K k → ℂ) (W : AllLevelFields L m K) : ℂ :=
  open Classical in if h : W k ∈ gaugeFieldsAtLevel L m K k then F ⟨W k, h⟩ else 0
end Carried
section Completion
open CentralBlock LargeFieldCompletion ComponentReferenceLaw TermForms
def stageVariantOf : DisplayForm → StageActionVariant
  | .original => .original
  | .effective => .withWilsonTerm
variable {N : AnalyticityConstants} {a : FullChoice} {m K : ℕ} {x : ℕ → ℝ} {E : ℕ → Type}
  {k : ℕ} (t : ClassedTerm N a m K x E k) (form : DisplayForm) (α : ℝ)
def termBeforeCompletion (T : DerivedConstants) : FieldFunctional a.L m K :=
  fun G W =>
    (t.leadingFactor W : ℂ) * frameAverage t.remainingComponents fun ρ =>
      (t.extensionIndicatorWithin t.unionRegion (W k) : ℂ) * t.lawIntegral α ρ G W *
        t.frameSummand T (stageVariantOf form) α ρ W
def stagePoints (T : DerivedConstants) (τ : BackgroundVariant)
    (𝒲 : Set (AllLevelFields a.L m K)) (n : ℕ) :
    Set (AllLevelFields a.L m K × t.stored.FieldSystem) :=
  {q | q.1 ∈ 𝒲 ∧
    CubesOfStep.prodOverComponents (degreeChoice a) (t.componentsAt n) (fun X =>
      stageIndicator (degreeChoice a) x t.stepLabel (t.componentsAt n) (n + 1) X q.1) ≠ 0 ∧
    q.2 ∈ Set.range t.storedOf ∧
    ∀ hj : stageLevel (degreeChoice a) x k n < k,
      stageCollarIntegral T a x t.actionData t.componentsAt t.localTerms n q.1 q.2 τ t.hist
        (stageVariantOf form) hj ≠ 0}
structure TermDataInClasses (T : DerivedConstants) : Prop where
  completion : ∃ (s : ActivityDomainKind)
      (Φ : (i : ScaleIndex k) → Set (t.completionData.storedBonds.restrictLevel i.2.2).FieldSystem),
    (stepConstants N (degreeChoice a)).ActionDataInClasses (blockExponents (radiiChoice a) x)
        t.completionData.scaleLabel t.completionData.actionData ![a.C₀, a.C₁] a.q x s a.κ a.E₀
        a.κ a.κ₀ Φ ∧
      ∀ (W : AllLevelFields a.L m K) (i : ScaleIndex k),
        t.completionData.storedBonds.restrictLevelSystem i.2.2
          (t.completionData.storedFieldsOf W) ∈ Φ i
  term : ∃ (s : ActivityDomainKind)
      (Φ : (i : ScaleIndex k) → Set (t.stored.restrictLevel i.2.2).FieldSystem),
    (AnalyticityConstants.ofChoice T a).ActionDataInClasses
        (fun i => Nat.log a.L (blockSizeAt (degreeChoice a) x i))
        t.stepLabel t.actionData ![a.C₀, a.C₁] a.q x s a.κ a.E₀ a.κ a.κ₀ Φ ∧
      ∀ (y : t.toFormTerm.lowerOp.Variables) (i : ScaleIndex k),
        t.stored.restrictLevelSystem i.2.2 (t.storedOf y) ∈ Φ i
end Completion
section Left
open OperationList in
abbrev PairSelections (a : FullChoice) (m K : ℕ) (x : ℕ → ℝ) (α : ℝ) : Type :=
  ∀ (k : ℕ) (_ : DecomposedHistory (degreeChoice a) m K x k)
    (s : StepTrace (degreeChoice a) m K x k), BasePairSelection a x s.label α
variable (T : DerivedConstants) (a : FullChoice) {m K : ℕ} (x : ℕ → ℝ)
  (τ : BackgroundVariant) (form : DisplayForm) (α : ℝ)
  (ς : PairSelections a m K x α)
open OperationList in
variable {a x} in
def stageComponentsOf {k : ℕ} (o : DecomposedOperation (degreeChoice a) m K x k) (n : ℕ) :
    Set (Set (FourTorus a.L m)) :=
  {X | X ∈ o.actedOn ∧ ∀ e he hp,
    (∃ i j : ℕ, i < j ∧
      (operationSlots (delayAt (degreeChoice a) x (k + 1)))[i]? =
        some (Slot.split e) ∧
      (operationSlots (delayAt (degreeChoice a) x (k + 1)))[j]? =
        some (Slot.stageIntegration n)) →
    X ∉ o.outcome.complementCarriers (.leaveAt e he hp)}
end Left
end PeriodicLattice.CubesOfStep
end YangMills.Construction
