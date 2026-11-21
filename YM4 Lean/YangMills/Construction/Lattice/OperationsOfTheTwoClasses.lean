import YangMills.Construction.Lattice.CompletedActionOfTheOperation
import YangMills.Construction.Lattice.WrittenFormsThroughTheReferenceLaws
import Mathlib
set_option autoImplicit false
open Set MeasureTheory
noncomputable section
namespace YangMills.Construction
open ParameterChoice
namespace PeriodicLattice.ClassOperations
open CentralBlock LargeFieldCompletion ComponentReferenceLaw CubesOfStep TermForms
def composeOperations {ι A : Type*} (s : Set ι) (O : ι → A → A) : A → A :=
  open Classical in
  if hs : s.Finite then (hs.toFinset.toList.map O).foldr (· ∘ ·) id else id
abbrev FluctuationFieldPair (L m K : ℕ) : Type := AllLevelFields L m K × AllLevelFields L m K
abbrev PairOperation (L m K : ℕ) : Type :=
  (FluctuationFieldPair L m K → ℂ) → FluctuationFieldPair L m K → ℂ
def patchVariables {L m K : ℕ} (B : Set (Σ q : ℕ, BondAtLevel L m K q))
    (U₁ U₀ : AllLevelFields L m K) : AllLevelFields L m K :=
  open Classical in
  fun n e => if (⟨n, e⟩ : Σ q : ℕ, BondAtLevel L m K q) ∈ B then U₁ n e else U₀ n e
def unsetVariables (L m K : ℕ) : AllLevelFields L m K := fun _ _ => 1
inductive DisplayForm
  | original
  | effective
section Component
variable (c : ChoiceUpToRadii) {m K : ℕ} {x : ℕ → ℝ} {k : ℕ}
  (S : LabelAtLevel c.toChoiceUpToDegreeConstants m K x k) (Q : Set (Set (FourTorus c.L m)))
  (X : Set (FourTorus c.L m)) (f : SignedFrame)
def componentScalingConst : ℝ :=
  haarScalingCoeff x k *
    ((freeBondsOfTree (c := c.toChoiceUpToDegreeConstants) (S.nestFixedBonds c.r x Q X)
      (componentNestTreeRotated c S Q X f)).ncard : ℝ)
def componentBoxConst : ℝ :=
  haarScalingCoeff x k *
    ((freeBondsOfTree (c := c.toChoiceUpToDegreeConstants) (bondsAsSigma (innerBoxBonds c S Q X))
      (boxTreeRotated c S Q X f)).ncard : ℝ)
variable {N : AnalyticityConstants} (T : StepCompletionData N c m K x k)
def componentConstants : DisplayForm → ℂ
  | .original => termConstants c T X + (componentScalingConst c S Q X f : ℂ) -
      termConstants c T (S.innerBoxIn c.r x Q X)
  | .effective => termConstants c T X - (componentBoxConst c S Q X f : ℂ)
def displayDatum : DisplayForm → (BondAtLevel c.L m K 0 → Matrices.ComplexMatrix2) →
    AllLevelFields c.L m K → AllLevelFields c.L m K
  | .original, U₀, U => basicBackgroundData c S Q U₀ U
  | .effective, U₀, U => basicBackgroundDataOfComponent c S Q X U₀ U
def componentExponent (α : ℝ) (D₀ U : AllLevelFields c.L m K)
    (Ub UΛ : BondAtLevel c.L m K k → Matrices.ComplexMatrix2) (U' : AllLevelFields c.L m K) : ℂ :=
  -(1 / 2) * (componentQuadraticForm c S Q α X D₀ (fluctuationVariables c S Q U') : ℂ) -
    componentInnerWilson c S Q X U' U +
    resummedPieceAt (stepConstants N c.toChoiceUpToDegreeConstants) T
      (addCubeLayer (coarseCubeIndex K (Nat.log c.L c.M) k) X)
      (completedBackgroundField c S Q U Ub UΛ)
      (fluctuationVariables c S Q U') (U (outerShellLevel c.toChoiceUpToDegreeConstants x k))
def nonComponentRegions (m' : ℕ) (K k : ℕ) (Q : Set (Set (FourTorus c.L m))) :
    Set (Set (FourTorus c.L m)) :=
  resummationRegions K m' k Q \ regionComponents (coarseCubeIndex K m' k) (unionThickened K m' k Q)
def nonComponentSum (U : AllLevelFields c.L m K) (Ub UΛ : BondAtLevel c.L m K k → Matrices.ComplexMatrix2)
    (U' : AllLevelFields c.L m K) : ℂ :=
  ∑ᶠ Y ∈ nonComponentRegions c (Nat.log c.L c.M) K k Q,
    resummedPieceAt (stepConstants N c.toChoiceUpToDegreeConstants) T Y
      (completedBackgroundField c S Q U Ub UΛ) (fluctuationVariables c S Q U')
      (U (outerShellLevel c.toChoiceUpToDegreeConstants x k))
end Component
section Term
structure ClassedTerm (N : AnalyticityConstants) (a : FullChoice) (m K : ℕ) (x : ℕ → ℝ)
    (E : ℕ → Type) (k : ℕ) extends FormTerm a m K x E k where
  completionData : StepCompletionData N (radiiChoice a) m K x k
  firstClass : Set (Set (FourTorus a.L m))
  firstClass_subset : firstClass ⊆ toFormTerm.remainingComponents
  componentLowerOp : Set (FourTorus a.L m) → LowerOperation a.L m K
namespace ClassedTerm
variable {N : AnalyticityConstants} {a : FullChoice} {m K : ℕ} {x : ℕ → ℝ} {E : ℕ → Type}
  {k : ℕ} (t : ClassedTerm N a m K x E k)
def secondClass : Set (Set (FourTorus a.L m)) := t.remainingComponents \ t.firstClass
def innerBoxBondSet : Set (BondAtLevel a.L m K k) :=
  innerBoxBonds (radiiChoice a) t.stepLabel t.remainingComponents t.unionRegion
def componentPair (α : ℝ) (X : Set (FourTorus a.L m)) (f : SignedFrame)
    (U : BondAtLevel a.L m K k → Matrices.ComplexMatrix2) :
    (BondAtLevel a.L m K k → Matrices.ComplexMatrix2) × (BondAtLevel a.L m K 0 → Matrices.ComplexMatrix2) :=
  t.basePair α {X} (fun _ => f) U
def localizedSequence (X : Set (FourTorus a.L m)) :
    ℕ → Set (FourTorus a.L m) × Set (FourTorus a.L m) :=
  fun n => (complementRegion (coarseCubeIndex K (Nat.log a.L (degreeChoice a).M) n)
      (t.stepLabel.domainSeq n) ∩ X, t.stepLabel.largeFieldOrEmpty n ∩ X)
def newIndicatorRegion : Set (FourTorus a.L m) :=
  let i := nestedCubeIndex a.L a.r x K (Nat.log a.L (degreeChoice a).M) k
  layerEnlargement i (⋃₀ (partitionCubesIn i (t.stepLabel.absorbedDomain a.r x t.remainingComponents k) ∩
    ⋂ Y ∈ t.secondClass, partitionCubesIn i (layerEnlargement i (complementRegion i Y) 2))) 4
def newDomainIndicator (U : BondAtLevel a.L m K k → Matrices.ComplexMatrix2) : ℝ :=
  densityIndicator (degreeChoice a) K x k U t.newIndicatorRegion
def classTwoBoxBonds : Set (BondAtLevel a.L m K k) :=
  ⋃ Y ∈ t.secondClass, innerBoxBonds (radiiChoice a) t.stepLabel t.remainingComponents Y
def classTwoTrees (ρ : ↥t.remainingComponents → SignedFrame) : Set (IndexedBond a.L m) :=
  ⋃ Y ∈ {Y : ↥t.remainingComponents | Y.1 ∈ t.secondClass},
    boxTreeRotated (radiiChoice a) t.stepLabel t.remainingComponents Y.1 (ρ Y)
def classTwoField (U' UΛ U : BondAtLevel a.L m K k → Matrices.ComplexMatrix2) :
    BondAtLevel a.L m K k → Matrices.ComplexMatrix2 :=
  open Classical in
  fun e => if e ∈ t.classTwoBoxBonds then extendedField t.classTwoBoxBonds U' UΛ e
    else U e
def classTwoIndicators (U U' : BondAtLevel a.L m K k → Matrices.ComplexMatrix2) : ℝ :=
  ∏ᶠ Y ∈ t.secondClass,
    secondKindIndicator (degreeChoice a) K x (Nat.log a.L (degreeChoice a).M) k U Y *
      t.stepLabel.extensionTest (degreeChoice a).εv a.A₀ a.𝔭₀ (Nat.log a.L a.M₁) a.r x
        t.remainingComponents Y U *
      innerBoxIndicator (radiiChoice a) t.stepLabel t.remainingComponents Y U'
def trailingFunction (UΛ : BondAtLevel a.L m K k → Matrices.ComplexMatrix2)
    (G : AllLevelFields a.L m K → ℂ) (R : FluctuationFieldPair a.L m K) : ℂ :=
  Complex.exp (nonComponentSum (radiiChoice a) t.stepLabel t.remainingComponents t.completionData R.2
      (relativeVariable t.innerBoxBondSet (R.2 k) UΛ) UΛ R.1) * G R.2
end ClassedTerm
variable {N : AnalyticityConstants} {a : FullChoice} {m K : ℕ} {x : ℕ → ℝ} {E : ℕ → Type}
  {k : ℕ} (𝒯 : Set (ClassedTerm N a m K x E k)) (form : DisplayForm) (α : ℝ)
end Term
end PeriodicLattice.ClassOperations
end YangMills.Construction
