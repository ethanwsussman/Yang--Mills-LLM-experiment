import YangMills.Construction.Lattice.BasicPairOfAFamilyOfFrames
import YangMills.Construction.Lattice.CollarIntegralAndStageTerm
import YangMills.Construction.Lattice.ProductFormOfTheOperationOnAClassComponent
import YangMills.Construction.Lattice.ReferenceLawOfAClassComponent
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicLattice.TermForms
open Set MeasureTheory ParameterChoice CentralBlock ComponentReferenceLaw CubesOfStep
section SigmaBonds
variable {L m K : ℕ}
def positiveBondsIn (B : Set (Σ q : ℕ, BondAtLevel L m K q)) : Set (Σ q : ℕ, BondAtLevel L m K q) :=
  {e | e ∈ B ∧ e.2.IsPositivelyOriented}
def fieldsAssignedOn (B : Set (Σ q : ℕ, BondAtLevel L m K q))
    (u : ↥(positiveBondsIn B) → Matrices.ComplexMatrix2) (W : AllLevelFields L m K) :
    AllLevelFields L m K :=
  open Classical in
  fun i e =>
    if h : (⟨i, e⟩ : Σ q : ℕ, BondAtLevel L m K q) ∈ positiveBondsIn B then u ⟨_, h⟩
    else if h' : (⟨i, e.opposite⟩ : Σ q : ℕ, BondAtLevel L m K q) ∈ positiveBondsIn B
      then (u ⟨_, h'⟩)⁻¹ else W i e
def haarIntegralOn (B : Set (Σ q : ℕ, BondAtLevel L m K q)) (W : AllLevelFields L m K)
    (F : AllLevelFields L m K → ℂ) : ℂ :=
  ∫ u, F (fieldsAssignedOn B (fun e => (u e : Matrices.ComplexMatrix2)) W)
    ∂Matrices.ComplexMatrix2.haarPi ↥(positiveBondsIn B)
def fieldsTimesDatum (B : Set (Σ q : ℕ, BondAtLevel L m K q)) (V' V₀ W : AllLevelFields L m K) :
    AllLevelFields L m K :=
  open Classical in
  fun i e =>
    if (⟨i, e⟩ : Σ q : ℕ, BondAtLevel L m K q) ∈ B then
      (if e.IsPositivelyOriented then V' i e * V₀ i e
        else (V' i e.opposite * V₀ i e.opposite)⁻¹)
    else W i e
def frameAverage (Q : Set (Set (FourTorus L m))) (F : (↥Q → SignedFrame) → ℂ) : ℂ :=
  ((signedFrameCount : ℂ)⁻¹) ^ Nat.card ↥Q * ∑ᶠ ρ : ↥Q → SignedFrame, F ρ
end SigmaBonds
section FinalSteps
variable (c : ChoiceUpToDegreeConstants) {m K : ℕ} (x : ℕ → ℝ) {k : ℕ}
  (S : LabelAtLevel c m K x k) (Q : Set (Set (FourTorus c.L m))) (X : Set (FourTorus c.L m))
def finalMemberBonds (i : ℕ) : Set (BondAtLevel c.L m K i) :=
  activeBondsAt K k (S.trimmedDomain c.r x Q) i
variable {c x S Q X}
variable (c x S Q X)
end FinalSteps
section BoxBondSets
variable (c : ChoiceUpToDegreeConstants) {m K : ℕ} (x : ℕ → ℝ) {k : ℕ}
  (S : LabelAtLevel c m K x k) (Q : Set (Set (FourTorus c.L m))) (X : Set (FourTorus c.L m))
def lowerBondsOffDomain : Set (Σ q : ℕ, BondAtLevel c.L m K q) :=
  bondsAsSigma ((finalMemberBonds c x S Q (lowerStep c x k) ∩ bondsInside X) \
    bondsInside (S.trimmedDomainThickened c.r x Q))
def boxBondsOfComponents (d : ChoiceUpToRadii) {m K : ℕ} {x : ℕ → ℝ} {k : ℕ}
    (S : LabelAtLevel d.toChoiceUpToDegreeConstants m K x k) (Q : Set (Set (FourTorus d.L m))) :
    Set (Σ q : ℕ, BondAtLevel d.L m K q) :=
  bondsAsSigma (⋃ Y ∈ Q, innerBoxBonds d S Q Y)
end BoxBondSets
section Terms
structure FormTerm (a : FullChoice) (m K : ℕ) (x : ℕ → ℝ) (E : ℕ → Type) (k : ℕ) where
  hist : LabelHistory (degreeChoice a) m K x E k
  stored : StoredBonds a.L m K k
  actionData : AnalyticityConstants.EffectiveActionData a.L m K stored
  componentsAt : ℕ → Set (Set (FourTorus a.L m))
  localTerms : LocalizedStageTerms stored
  lowerOp : LowerOperation a.L m K
  storedOf : lowerOp.Variables → stored.FieldSystem
  otherOps : FieldFunctional a.L m K → FieldFunctional a.L m K
  basePair : (α : ℝ) → (Q : Set (Set (FourTorus a.L m))) → (↥Q → SignedFrame) →
    (BondAtLevel a.L m K k → Matrices.ComplexMatrix2) →
    (BondAtLevel a.L m K k → Matrices.ComplexMatrix2) × (BondAtLevel a.L m K 0 → Matrices.ComplexMatrix2)
  basePair_isFramedBasePair : ∀ (α : ℝ) (Q : Set (Set (FourTorus a.L m))) (ρ : ↥Q → SignedFrame)
    (V W : BondAtLevel a.L m K k → Matrices.ComplexMatrix2)
    (U : BondAtLevel a.L m K 0 → Matrices.ComplexMatrix2),
    IsFramedBasePair (degreeChoice a) hist.finalLabel Q α ρ V W U →
      IsFramedBasePair (degreeChoice a) hist.finalLabel Q α ρ V
        (basePair α Q ρ V).1 (basePair α Q ρ V).2
namespace FormTerm
variable (T : DerivedConstants) {a : FullChoice} {m K : ℕ} {x : ℕ → ℝ} {E : ℕ → Type}
  {k : ℕ} (t : FormTerm a m K x E k)
def stepLabel : LabelAtLevel (degreeChoice a) m K x k := t.hist.finalLabel
def stageCount (_ : FormTerm a m K x E k) : ℕ := Thresholds.delayDepth a.L a.r x k
def remainingComponents : Set (Set (FourTorus a.L m)) := t.componentsAt t.stageCount
def unionRegion : Set (FourTorus a.L m) := ⋃₀ t.remainingComponents
def finalBackgroundAt (V : AllLevelFields a.L m K) :
    BondAtLevel a.L m K 0 → Matrices.ComplexMatrix2 :=
  t.stepLabel.finalBackground (degreeChoice a).εv a.r x t.remainingComponents V
def finalAction (φ : StageActionVariant) (V : AllLevelFields a.L m K)
    (f : t.stored.FieldSystem) : ℂ :=
  stageActionAt T a x t.stepLabel t.actionData t.componentsAt t.localTerms φ t.stageCount
    (t.finalBackgroundAt V) (storedClearedUpTo a x t.stepLabel t.componentsAt V f t.stageCount)
def componentsWithin (X : Set (FourTorus a.L m)) : Set (Set (FourTorus a.L m)) :=
  {Y | Y ∈ t.remainingComponents ∧ Y ⊆ X}
def extensionIndicatorWithin (X : Set (FourTorus a.L m))
    (V : BondAtLevel a.L m K k → Matrices.ComplexMatrix2) : ℝ :=
  ∏ᶠ Y ∈ t.componentsWithin X,
    t.stepLabel.extensionTest (degreeChoice a).εv a.A₀ a.𝔭₀ (Nat.log a.L a.M₁) a.r x
      t.remainingComponents Y V
def leadingFactor (V : AllLevelFields a.L m K) : ℝ :=
  leadingFunction (radiiChoice a) x t.hist V
def framePair (α : ℝ) (ρ : ↥t.remainingComponents → SignedFrame)
    (V : BondAtLevel a.L m K k → Matrices.ComplexMatrix2) :
    (BondAtLevel a.L m K k → Matrices.ComplexMatrix2) × (BondAtLevel a.L m K 0 → Matrices.ComplexMatrix2) :=
  t.basePair α t.remainingComponents ρ V
def fixedBondsOfUnion : Set (Σ q : ℕ, BondAtLevel a.L m K q) :=
  t.stepLabel.nestFixedBonds a.r x t.remainingComponents t.unionRegion
def fluctuationIndicator (V' : AllLevelFields a.L m K) : ℝ :=
  ∏ᶠ Y ∈ t.remainingComponents,
    fluctuationSmallnessIndicator (degreeChoice a) t.stepLabel t.remainingComponents Y V'
def frameSummand (φ : StageActionVariant) (α : ℝ) (ρ : ↥t.remainingComponents → SignedFrame)
    (W : AllLevelFields a.L m K) : ℂ :=
  haarIntegralOn (lowerBondsOffDomain (degreeChoice a) x t.stepLabel t.remainingComponents
      t.unionRegion) W fun W₁ =>
    t.lowerOp.integral W₁ fun y =>
      gaugeFixedIntegral t.fixedBondsOfUnion
        (nestTreeOfFrames (degreeChoice a) t.stepLabel t.remainingComponents ρ) fun V' =>
          let V := t.lowerOp.down y
            (fieldsTimesDatum t.fixedBondsOfUnion V'
              (baseDatum (degreeChoice a) (t.framePair α ρ (W k)).2) (t.lowerOp.up y W₁))
          (outerShellIndicator (degreeChoice a) t.stepLabel t.remainingComponents
              (V (outerShellLevel (degreeChoice a) x k))
              (outerShell (degreeChoice a) t.stepLabel t.remainingComponents t.unionRegion) : ℂ) *
            t.lowerOp.factor y V * (t.fluctuationIndicator V' : ℂ) *
            Complex.exp (t.finalAction T φ V (t.storedOf y))
def fieldWithLawValues (V' VΛ V : BondAtLevel a.L m K k → Matrices.ComplexMatrix2) :
    BondAtLevel a.L m K k → Matrices.ComplexMatrix2 :=
  open Classical in
  fun e =>
    if e ∈ ⋃ Y ∈ t.remainingComponents,
        innerBoxBonds (radiiChoice a) t.stepLabel t.remainingComponents Y then
      extendedField (⋃ Y ∈ t.remainingComponents,
        innerBoxBonds (radiiChoice a) t.stepLabel t.remainingComponents Y) V' VΛ e
    else V e
def lawDensity (ρ : ↥t.remainingComponents → SignedFrame)
    (VΛ V' : BondAtLevel a.L m K k → Matrices.ComplexMatrix2) : ℂ :=
  ∏ᶠ Y : ↥t.remainingComponents,
    componentFactor (radiiChoice a) t.stepLabel t.remainingComponents Y.1 VΛ V' /
      componentNormalizer (radiiChoice a) t.stepLabel t.remainingComponents Y.1 (ρ Y) VΛ
def lawTrees (ρ : ↥t.remainingComponents → SignedFrame) : Set (IndexedBond a.L m) :=
  ⋃ Y : ↥t.remainingComponents,
    boxTreeRotated (radiiChoice a) t.stepLabel t.remainingComponents Y.1 (ρ Y)
def lawIntegral (α : ℝ) (ρ : ↥t.remainingComponents → SignedFrame)
    (G : AllLevelFields a.L m K → ℂ) (W : AllLevelFields a.L m K) : ℂ :=
  gaugeFixedIntegral (c := degreeChoice a)
    (boxBondsOfComponents (radiiChoice a) t.stepLabel t.remainingComponents) (t.lawTrees ρ)
    fun V' =>
      t.lawDensity ρ (t.framePair α ρ (W k)).1 (V' k) *
        G (Function.update W k (t.fieldWithLawValues (V' k) (t.framePair α ρ (W k)).1 (W k)))
def exteriorData :
    Set (FourTorus a.L m) × (ℕ → Set (FourTorus a.L m) × Set (FourTorus a.L m)) :=
  (t.stepLabel.largeFieldOrEmpty k \ t.unionRegion, fun i =>
    (complementRegion (coarseCubeIndex K (Nat.log a.L (degreeChoice a).M) i)
        (t.stepLabel.domainSeq i) \ t.unionRegion,
      t.stepLabel.largeFieldOrEmpty i \ t.unionRegion))
end FormTerm
variable (T : DerivedConstants) {a : FullChoice} {m K : ℕ} {x : ℕ → ℝ} {E : ℕ → Type}
  {k : ℕ} (𝒯 : Set (FormTerm a m K x E k)) (φ : StageActionVariant) (α : ℝ)
end Terms
end YangMills.Construction.PeriodicLattice.TermForms
