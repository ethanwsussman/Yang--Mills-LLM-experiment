import YangMills.Construction.Lattice.BlockAxialLaw
import YangMills.Construction.Lattice.GaugeConfigSpaces
import YangMills.Construction.Lattice.GaugeTreeOfANestIsARootedTree
import YangMills.Construction.Lattice.KindsOfOperationsAndDropOuts
import YangMills.Construction.Lattice.LargeFieldDecomposition
import YangMills.Construction.Lattice.LayerBondsCoarseSpacesAndAverages
import YangMills.Construction.Lattice.WrittenFormsThroughTheReferenceLaws
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open MeasureTheory Set ParameterChoice
namespace PeriodicLattice.OperationList
open LargeFieldCourse CentralBlock ComponentReferenceLaw CubesOfStep TermForms
inductive Slot where
  | split (e : Lattice.LargeFieldDecomposition)
  | stageGaugeFixing (n : ℕ)
  | stageIndicatorRemoval (n : ℕ)
  | collarShift (n : ℕ)
  | stageIntegration (n : ℕ)
  | boxIntegration
  | frameSum
  | nestGaugeFixing
  | mixedGaugeChange
  | regularityRemoval
  | referenceLaw
  | referenceLawLiteral
  | localization
  | classSplit
  | boxTestRemoval
  | boxTreeRemoval
  | exponentiation
def stageSlots (n : ℕ) : List Slot :=
  (if n = 0 then [.split .regularityOfTheFirstBackground] else []) ++
    [.split (.regularityOfTheNextBackground n), .stageGaugeFixing n,
      .split (.approximateFluctuationTest n),
      .split (.completionOfTheFluctuationTests n), .stageIndicatorRemoval n,
      .collarShift n, .split (.smallFieldTestOfTheFluctuationField n),
      .stageIntegration n]
def finalSlots : List Slot :=
  [.split .extendibilityOfTheExteriorField, .boxIntegration, .frameSum,
    .nestGaugeFixing, .split .smallFieldTestOfTheMainStep, .mixedGaugeChange,
    .split .testAtTheLastShell, .regularityRemoval,
    .split .testOfTheDenominator, .referenceLaw,
    .localization, .classSplit, .boxTestRemoval, .boxTreeRemoval,
    .exponentiation]
def finalSlotsLiteral : List Slot :=
  [.split .extendibilityOfTheExteriorField, .boxIntegration, .frameSum,
    .nestGaugeFixing, .split .smallFieldTestOfTheMainStep, .mixedGaugeChange,
    .split .testAtTheLastShell, .regularityRemoval, .referenceLawLiteral,
    .localization, .classSplit, .boxTestRemoval, .boxTreeRemoval,
    .exponentiation]
def operationSlots (N : ℕ) : List Slot :=
  (List.range N).flatMap stageSlots ++ finalSlots
def operationSlotsLiteral (N : ℕ) : List Slot :=
  (List.range N).flatMap stageSlots ++ finalSlotsLiteral
section Slots
variable {L m K k : ℕ} {B P : Type}
def slotReached (slots : List P) (s : OperationState L m K k B) (X : Set (FourTorus L m)) :
    Option P :=
  slots[(s.performedAt X).length]?
def regionsThrough (slots : List P) (p : P) (s : OperationState L m K k B) :
    Set (Set (FourTorus L m)) :=
  s.remaining ∪ {X | ∃ d ∈ s.dropped, d.region = X ∧
    ∃ i, slots[i]? = some p ∧ i < d.kept.length}
def IsNotAhead (s : OperationState L m K k B) (X : Set (FourTorus L m)) : Prop :=
  ∀ Y ∈ s.remaining, (s.performedAt X).length ≤ (s.performedAt Y).length
def scheduleOfSlots (slots : List P) (isClass : P → Prop)
    (isAt : P → ∀ s : OperationState L m K k B, ∀ X : Set (FourTorus L m),
      TermOperation s.term X → List B → Prop) : OperationSchedule L m K k B where
  isNext s X κ b := IsNotAhead s X ∧ ∃ p, slotReached slots s X = some p ∧ isAt p s X κ b
  isClassPartition s X _ := ∃ p, slotReached slots s X = some p ∧ isClass p
  isFinished s := ∀ X ∈ s.remaining, (s.performedAt X).length = slots.length
def HasClassIndicator (slots : List P) (isClass : P → Prop)
    (s : OperationState L m K k B) (X : Set (FourTorus L m)) : Prop :=
  ∃ (pre post : List (LevelOperation L m K k B)) (o : LevelOperation L m K k B)
    (d : PartitionOfUnity o.source) (p : P),
    s.performed = pre ++ o :: post ∧ o.region = X ∧ o.op = .partition d ∧
      slotReached slots { s with performed := pre } X = some p ∧ isClass p ∧
      ((post.head?.map LevelOperation.source).getD s.term) = d.termχ
end Slots
section Variables
structure RegionFrames (L m : ℕ) where
  frame : Set (FourTorus L m) → SignedFrame
instance RegionFrames.measurableSpace (L m : ℕ) : MeasurableSpace (RegionFrames L m) := ⊤
abbrev StoredVariables (L m K : ℕ) : Type := AllLevelFields L m K × RegionFrames L m
variable {L m K k : ℕ}
abbrev StoredState (L m K k : ℕ) (Y : Type) : Type :=
  LevelStateSpace L m K k (StoredVariables L m K × Y)
abbrev StoredTerm (L m K k : ℕ) (Y : Type) [MeasurableSpace Y] : Type :=
  ComplexStateMeasure L m K k (StoredVariables L m K × Y)
variable {Y : Type}
def stateFields (p : StoredState L m K k Y) : AllLevelFields L m K :=
  Function.update p.2.1.1 k p.1.1
def IsBoundedMeasurableObservable [MeasurableSpace Y] (F : StoredState L m K k Y → ℂ) : Prop :=
  Measurable F ∧ ∃ C : ℝ, ∀ p, ‖F p‖ ≤ C
def AgreeOutside (X : Set (FourTorus L m)) (p p' : StoredState L m K k Y) : Prop :=
  (∀ j, ∀ b : BondAtLevel L m K j, b ∉ (bondsMeeting X : Set (BondAtLevel L m K j)) →
      stateFields p j b = stateFields p' j b ∧ p.2.1.1 j b = p'.2.1.1 j b) ∧
    (∀ j, k < j → p.2.1.1 j = p'.2.1.1 j) ∧
    (∀ R, R ≠ X → p.2.1.2.frame R = p'.2.1.2.frame R) ∧ p.2.2 = p'.2.2
def gaugeStoredField (j : ℕ) (g : SiteAtLevel L m K j → Matrices.ComplexMatrix2)
    (p : StoredState L m K k Y) : StoredState L m K k Y :=
  (p.1, (Function.update p.2.1.1 j (gaugeTransform g (p.2.1.1 j)), p.2.1.2), p.2.2)
def setFrame (X : Set (FourTorus L m)) (r : SignedFrame) (p : StoredState L m K k Y) :
    StoredState L m K k Y :=
  open Classical in (p.1, (p.2.1.1, ⟨Function.update p.2.1.2.frame X r⟩), p.2.2)
def blockFieldOrKeep (p : StoredState L m K k Y) (V : BondAtLevel L m K k → Matrices.ComplexMatrix2) :
    BlockFields L m K k :=
  open Classical in if h : V ∈ gaugeFieldsAtLevel L m K k then ⟨V, h⟩ else p.1
def integrateBlockField (𝔹 : Set (Σ q : ℕ, BondAtLevel L m K q))
    (w : ↥(positiveBondsIn 𝔹) → Matrices.ComplexMatrix2.specialUnitary) (p : StoredState L m K k Y) :
    StoredState L m K k Y :=
  open Classical in
  (blockFieldOrKeep p (fieldsAssignedOn 𝔹 (fun e => (w e : Matrices.ComplexMatrix2)) (stateFields p) k),
    (fun j b => if (⟨j, b⟩ : Σ q : ℕ, BondAtLevel L m K q) ∈ 𝔹 then stateFields p j b
      else p.2.1.1 j b, p.2.1.2), p.2.2)
variable [MeasurableSpace Y]
def IsLocalTo (X : Set (FourTorus L m)) (μ ν : StoredTerm L m K k Y) : Prop :=
  ∀ F : StoredState L m K k Y → ℂ, IsBoundedMeasurableObservable F →
    (∀ p p', AgreeOutside X p p' → F p = F p') →
    ν.integral F (ContinuousLinearMap.mul ℝ ℂ) = μ.integral F (ContinuousLinearMap.mul ℝ ℂ)
def IsFrameAveraging (X : Set (FourTorus L m)) (μ ν : StoredTerm L m K k Y) : Prop :=
  ∀ F : StoredState L m K k Y → ℂ, IsBoundedMeasurableObservable F →
    ν.integral F (ContinuousLinearMap.mul ℝ ℂ) =
      averageOverFrames (fun r : SignedFrame => r) fun r =>
        μ.integral (fun p => F (setFrame X r p)) (ContinuousLinearMap.mul ℝ ℂ)
def IsBondIntegration (𝔹 : Set (Σ q : ℕ, BondAtLevel L m K q))
    (μ ν : StoredTerm L m K k Y) : Prop :=
  ∀ F : StoredState L m K k Y → ℂ, IsBoundedMeasurableObservable F →
    ν.integral F (ContinuousLinearMap.mul ℝ ℂ) =
      μ.integral (fun p => ∫ w, F (integrateBlockField 𝔹 w p)
        ∂Matrices.ComplexMatrix2.haarPi ↥(positiveBondsIn 𝔹)) (ContinuousLinearMap.mul ℝ ℂ)
end Variables
section TreeLaw
variable {L m K : ℕ}
def setToFinset {α : Type} (A : Set α) : Finset α :=
  open Classical in if h : A.Finite then h.toFinset else ∅
def treeBondsByLevel (K : ℕ) (T : Set (IndexedBond L m)) : Set (Σ q : ℕ, BondAtLevel L m K q) :=
  {t | (⟨levelDepth K t.1, t.2⟩ : IndexedBond L m) ∈ T ∨
    (⟨levelDepth K t.1, t.2.opposite⟩ : IndexedBond L m) ∈ T}
def holonomyAlong (W : AllLevelFields L m K) (Γ : List (Σ q : ℕ, BondAtLevel L m K q)) :
    Matrices.ComplexMatrix2 :=
  (Γ.map fun t => W t.1 t.2).prod
def treeGauge (𝔖 : Set (FourTorus L m)) (T : Finset (Σ q : ℕ, BondAtLevel L m K q))
    (p₀ : FourTorus L m) (V₀ V'' : AllLevelFields L m K) (p : FourTorus L m) :
    Matrices.ComplexMatrix2 :=
  open Classical in
  if p ∈ 𝔖 then
    (holonomyAlong V₀ (FaddeevPopov.simpleTreePath T p₀ p))⁻¹ *
      holonomyAlong V'' (FaddeevPopov.simpleTreePath T p₀ p)
  else 1
def gaugeOn (𝔈 : Set (Σ q : ℕ, BondAtLevel L m K q)) (ϖ : FourTorus L m → Matrices.ComplexMatrix2)
    (V'' : AllLevelFields L m K) : AllLevelFields L m K :=
  open Classical in
  fun j b => if (⟨j, b⟩ : Σ q : ℕ, BondAtLevel L m K q) ∈ 𝔈 then
      ϖ (b.source : FourTorus L m) * V'' j b * (ϖ (b.target : FourTorus L m))⁻¹
    else V'' j b
end TreeLaw
section Terms
variable {L m K k : ℕ}
abbrev Observable (L m K : ℕ) : Type := AllLevelFields L m K → StoredVariables L m K → ℝ
inductive IsPartitionBy (f : Observable L m K) :
    (σ : StateTerm L m K k) → PartitionOfUnity σ → Prop
  | mk (μ : StoredTerm L m K k Unit)
      (d : PartitionOfUnity (StateTerm.mk (StoredVariables L m K × Unit) μ))
      (h : ∀ p : StoredState L m K k Unit, d.χ p = f (stateFields p) p.2.1) :
      IsPartitionBy f (StateTerm.mk (StoredVariables L m K × Unit) μ) d
inductive OnStoredVariables
    (R : ∀ (Y : Type) [MeasurableSpace Y], StoredTerm L m K k Y → StoredTerm L m K k Y → Prop) :
    StateTerm L m K k → StateTerm L m K k → Prop
  | mk (μ ν : StoredTerm L m K k Unit) (h : R Unit μ ν) :
      OnStoredVariables R (StateTerm.mk (StoredVariables L m K × Unit) μ)
        (StateTerm.mk (StoredVariables L m K × Unit) ν)
variable {σ : StateTerm L m K k} {X : Set (FourTorus L m)}
def IsPartitionWith (f : Observable L m K) (κ : TermOperation σ X) : Prop :=
  ∃ d, κ = .partition d ∧ IsPartitionBy f σ d
def IsRewrite (kind : IdentityKind) (κ : TermOperation σ X) : Prop :=
  ∃ i : TermIdentity σ, κ = .identity i ∧ i.kind = kind ∧ i.result = σ
def IsIdentityBy (kind : IdentityKind)
    (R : ∀ (Y : Type) [MeasurableSpace Y], StoredTerm L m K k Y → StoredTerm L m K k Y → Prop)
    (κ : TermOperation σ X) : Prop :=
  ∃ i : TermIdentity σ, κ = .identity i ∧ i.kind = kind ∧ OnStoredVariables R σ i.result
def IsEquivalenceBy
    (R : ∀ (Y : Type) [MeasurableSpace Y], StoredTerm L m K k Y → StoredTerm L m K k Y → Prop)
    (κ : TermOperation σ X) : Prop :=
  ∃ e : TermEquivalence σ X, κ = .equivalence e ∧ OnStoredVariables R σ e.result
end Terms
section Operation
inductive CollarTestForm where
  | original
  | localCentreInGauge
variable {L m K k : ℕ}
structure StageOutput (𝔅 : StoredBonds L m K k) where
  stage : ℕ
  domain : Set (FourTorus L m)
  value : (BondAtLevel L m K 0 → Matrices.ComplexMatrix2) → 𝔅.FieldSystem → ℂ
abbrev StageTermsByBranch {L m K k : ℕ} (𝔅 : StoredBonds L m K k) : Type :=
  (ℕ → Set (Set (FourTorus L m))) → LocalizedStageTerms 𝔅
def stageRegions {L m K k : ℕ} {B : Type} (slots : List Slot)
    (s : OperationState L m K k B) : ℕ → Set (Set (FourTorus L m)) :=
  fun n => regionsThrough slots (.stageIntegration n) s
variable (T : DerivedConstants) (a : FullChoice) {m K : ℕ} (x : ℕ → ℝ) {k : ℕ}
  (S : LabelAtLevel (degreeChoice a) m K x k)
def componentFrames (Q : Set (Set (FourTorus a.L m))) (v : StoredVariables a.L m K) :
    ↥Q → SignedFrame :=
  fun Y => v.2.frame Y.1
def HasBasePair (α : ℝ) (Q : Set (Set (FourTorus a.L m))) (ρ : ↥Q → SignedFrame)
    (V : BondAtLevel a.L m K k → Matrices.ComplexMatrix2) : Prop :=
  ∃ W U, IsFramedBasePair (degreeChoice a) S Q α ρ V W U
def IsLargeFieldComponentSet (Q : Set (Set (FourTorus a.L m))) : Prop :=
  Q ⊆ regionComponents (coarseCubeIndex K (Nat.log a.L (degreeChoice a).M) k) (S.largeFieldOrEmpty k)
structure BasePairSelection (α : ℝ) where
  pair : ∀ Q : Set (Set (FourTorus a.L m)), (↥Q → SignedFrame) →
    (BondAtLevel a.L m K k → Matrices.ComplexMatrix2) →
    (BondAtLevel a.L m K k → Matrices.ComplexMatrix2) × (BondAtLevel a.L m K 0 → Matrices.ComplexMatrix2)
  pair_spec : ∀ Q ρ V, HasBasePair a x S α Q ρ V →
    IsFramedBasePair (degreeChoice a) S Q α ρ V (pair Q ρ V).1 (pair Q ρ V).2
  measurableSet_hasBasePair : ∀ Q ρ, MeasurableSet {V | HasBasePair a x S α Q ρ V}
  measurable_pair : ∀ Q ρ, Measurable (pair Q ρ)
  pair_eq_of_exterior : ∀ Q ρ (V V' : BondAtLevel a.L m K k → Matrices.ComplexMatrix2),
    (∀ b ∈ (bondsMeeting (⋃₀ Q) \ innerBoxBonds (radiiChoice a) S Q (⋃₀ Q) :
      Set (BondAtLevel a.L m K k)), V b = V' b) → pair Q ρ V = pair Q ρ V'
  pair_eq_on_component : ∀ (Q Q' : Set (Set (FourTorus a.L m))) (ρ : ↥Q → SignedFrame)
    (ρ' : ↥Q' → SignedFrame)
    (V V' : BondAtLevel a.L m K k → Matrices.ComplexMatrix2) (Y : Set (FourTorus a.L m))
    (hY : Y ∈ Q) (hY' : Y ∈ Q'),
    IsLargeFieldComponentSet a x S Q → IsLargeFieldComponentSet a x S Q' →
    ρ ⟨Y, hY⟩ = ρ' ⟨Y, hY'⟩ → HasBasePair a x S α Q ρ V → HasBasePair a x S α Q' ρ' V' →
    (∀ b ∈ (bondsMeeting Y \ innerBoxBonds (radiiChoice a) S Q Y : Set (BondAtLevel a.L m K k)),
      V b = V' b) →
    (∀ b ∈ (bondsMeeting Y : Set (BondAtLevel a.L m K k)), (pair Q ρ V).1 b = (pair Q' ρ' V').1 b) ∧
      ∀ b ∈ (bondsInside Y : Set (BondAtLevel a.L m K 0)), (pair Q ρ V).2 b = (pair Q' ρ' V').2 b
variable {a x S} {α : ℝ} (ς : BasePairSelection a x S α)
def HasComponentBasePair (α : ℝ) (X : Set (FourTorus a.L m))
    (V : BondAtLevel a.L m K k → Matrices.ComplexMatrix2) (v : StoredVariables a.L m K) : Prop :=
  HasBasePair a x S α {X} (componentFrames a {X} v) V
def componentPair (X : Set (FourTorus a.L m)) (V : BondAtLevel a.L m K k → Matrices.ComplexMatrix2)
    (v : StoredVariables a.L m K) :
    (BondAtLevel a.L m K k → Matrices.ComplexMatrix2) × (BondAtLevel a.L m K 0 → Matrices.ComplexMatrix2) :=
  ς.pair {X} (componentFrames a {X} v) V
def stateFluctuation (Q : Set (Set (FourTorus a.L m))) (X : Set (FourTorus a.L m))
    (V : BondAtLevel a.L m K k → Matrices.ComplexMatrix2) (v : StoredVariables a.L m K) :
    AllLevelFields a.L m K :=
  fluctuationField (degreeChoice a) S Q X v.1
    (baseDatum (degreeChoice a) (componentPair ς X V v).2)
def completedFluctuationIndicator (Q : Set (Set (FourTorus a.L m))) (X : Set (FourTorus a.L m))
    (V : BondAtLevel a.L m K k → Matrices.ComplexMatrix2) (v : StoredVariables a.L m K) : ℝ :=
  open Classical in
  if HasComponentBasePair (a := a) (x := x) (S := S) α X V v then
    fluctuationSmallnessIndicator (degreeChoice a) S Q X (stateFluctuation ς Q X V v)
  else 0
def FactorMeasurable (Q : Set (Set (FourTorus a.L m))) (X : Set (FourTorus a.L m)) (f : SignedFrame)
    (W : BondAtLevel a.L m K k → Matrices.ComplexMatrix2) : Prop :=
  Measurable fun w : ↥(freeBondsOfTree (c := degreeChoice a)
      (bondsAsSigma (innerBoxBonds (radiiChoice a) S Q X))
      (boxTreeRotated (radiiChoice a) S Q X f)) → ↥Matrices.ComplexMatrix2.specialUnitary =>
    componentFactor (radiiChoice a) S Q X W (fieldOffTree (c := degreeChoice a)
      (bondsAsSigma (innerBoxBonds (radiiChoice a) S Q X))
      (boxTreeRotated (radiiChoice a) S Q X f) (fun e => (w e : Matrices.ComplexMatrix2)) k)
def NormalizerAdmissible (Q : Set (Set (FourTorus a.L m))) (X : Set (FourTorus a.L m))
    (V : BondAtLevel a.L m K k → Matrices.ComplexMatrix2) (v : StoredVariables a.L m K) : Prop :=
  HasComponentBasePair (a := a) (x := x) (S := S) α X V v ∧
    ComponentFactorDefined (radiiChoice a) S Q X (componentPair ς X V v).1 ∧
    FactorMeasurable (a := a) (S := S) Q X (v.2.frame X) (componentPair ς X V v).1 ∧
    ∃ d : ℝ, 0 < d ∧ componentNormalizer (radiiChoice a) S Q X (v.2.frame X)
      (componentPair ς X V v).1 = d
def normalizerIndicator (Q : Set (Set (FourTorus a.L m))) (X : Set (FourTorus a.L m))
    (V : BondAtLevel a.L m K k → Matrices.ComplexMatrix2) (v : StoredVariables a.L m K) : ℝ :=
  open Classical in if NormalizerAdmissible ς Q X V v then 1 else 0
variable (a x S)
def splitObservable (φ : CollarTestForm) (ς : BasePairSelection a x S α)
    (Q : Set (Set (FourTorus a.L m))) (X : Set (FourTorus a.L m)) :
    Lattice.LargeFieldDecomposition → Observable a.L m K
  | .regularityOfTheFirstBackground => fun W _ =>
      stageIndicatorOfExists (degreeChoice a) x S Q 0 X W
  | .regularityOfTheNextBackground n => fun W _ =>
      stageIndicatorOfExists (degreeChoice a) x S Q (n + 1) X W
  | .approximateFluctuationTest n => fun W _ =>
      match φ with
      | .original => approxCollarIndicatorOfBackground (degreeChoice a) x S Q n X W
      | .localCentreInGauge => approxCollarIndicatorInGauge (degreeChoice a) x S Q n X W
  | .completionOfTheFluctuationTests n => fun W _ =>
      stripLayerIndicator (degreeChoice a) x
        (stepDataOfFields (degreeChoice a) S (stageLevel (degreeChoice a) x k n) W) X
  | .smallFieldTestOfTheFluctuationField n => fun W _ =>
      match φ with
      | .original => collarSmallIndicator (degreeChoice a) x S Q n X W
      | .localCentreInGauge =>
          collarSmallIndicatorLocal (degreeChoice a) x S Q n X W
  | .extendibilityOfTheExteriorField => fun W _ =>
      S.completedExtensionTest (degreeChoice a).εv a.A₀ a.𝔭₀ (Nat.log a.L a.M₁) a.r x Q X (W k)
  | .smallFieldTestOfTheMainStep => fun W v =>
      completedFluctuationIndicator ς Q X (W k) v
  | .testAtTheLastShell => fun W _ =>
      outerShellIndicator (degreeChoice a) S Q (W (outerShellLevel (degreeChoice a) x k))
        (outerShell (degreeChoice a) S Q X)
  | .testOfTheDenominator => fun W v => normalizerIndicator ς Q X (W k) v
def classObservable (X : Set (FourTorus a.L m)) : Observable a.L m K :=
  fun W _ => firstKindIndicator (degreeChoice a) K x (Nat.log a.L (degreeChoice a).M) k (W k) X
def nestSites (Q : Set (Set (FourTorus a.L m))) (X : Set (FourTorus a.L m)) : Set (FourTorus a.L m) :=
  BoxNest.nestPoints (Thresholds.delayDepth a.L a.r x k + 1) (S.nestShell a.r x Q X)
    (ScaleLabel.shellDepth K k)
def nestRoot (Q : Set (Set (FourTorus a.L m))) (X : Set (FourTorus a.L m)) (f : SignedFrame) :
    FourTorus a.L m :=
  ((BoxNest.rootEntranceBond f (S.nestShell a.r x Q X)
    (ScaleLabel.shellDepth K k)).source : FourTorus a.L m)
def nestTreeBonds (Q : Set (Set (FourTorus a.L m))) (X : Set (FourTorus a.L m)) (f : SignedFrame) :
    Set (Σ q : ℕ, BondAtLevel a.L m K q) :=
  treeBondsByLevel K (nestTreeInFrame (degreeChoice a) S Q X f)
def treeMovedBonds (Q : Set (Set (FourTorus a.L m))) (X : Set (FourTorus a.L m)) :
    Set (Σ q : ℕ, BondAtLevel a.L m K q) :=
  {t | t ∈ activeBondSet K k (S.trimmedDomain a.r x Q) ∧
    ((t.2.source : FourTorus a.L m) ∈ nestSites a x S Q X ∨
      (t.2.target : FourTorus a.L m) ∈ nestSites a x S Q X)}
def stateBaseDatum {Y : Type} (ς : BasePairSelection a x S α)
    (X : Set (FourTorus a.L m)) (p : StoredState a.L m K k Y) : AllLevelFields a.L m K :=
  baseDatum (degreeChoice a) (componentPair ς X p.1.1 p.2.1).2
def HasTreeValues {Y : Type} (ς : BasePairSelection a x S α)
    (Q : Set (Set (FourTorus a.L m))) (X : Set (FourTorus a.L m)) (p : StoredState a.L m K k Y) :
    Prop :=
  HasComponentBasePair (a := a) (x := x) (S := S) α X p.1.1 p.2.1 ∧
    ∀ t ∈ nestTreeBonds a x S Q X (p.2.1.2.frame X),
      stateBaseDatum a x S ς X p t.1 t.2 ∈ Matrices.ComplexMatrix2.specialUnitary ∧
        stateBaseDatum a x S ς X p t.1 t.2.opposite =
          (stateBaseDatum a x S ς X p t.1 t.2)⁻¹
def treeGaugedState {Y : Type} (ς : BasePairSelection a x S α)
    (Q : Set (Set (FourTorus a.L m))) (X : Set (FourTorus a.L m))
    (p : StoredState a.L m K k Y) : StoredState a.L m K k Y :=
  open Classical in
  if HasTreeValues a x S ς Q X p then
    (p.1, (gaugeOn (treeMovedBonds a x S Q X)
      (treeGauge (nestSites a x S Q X)
        (setToFinset (nestTreeBonds a x S Q X (p.2.1.2.frame X)))
        (nestRoot a x S Q X (p.2.1.2.frame X)) (stateBaseDatum a x S ς X p) p.2.1.1)
      p.2.1.1, p.2.1.2), p.2.2)
  else p
def IsTreeGaugeFixing {Y : Type} [MeasurableSpace Y] (ς : BasePairSelection a x S α)
    (Q : Set (Set (FourTorus a.L m))) (X : Set (FourTorus a.L m)) (μ ν : StoredTerm a.L m K k Y) :
    Prop :=
  ∀ F : StoredState a.L m K k Y → ℂ, IsBoundedMeasurableObservable F →
    ν.integral F (ContinuousLinearMap.mul ℝ ℂ) =
      μ.integral (fun p => F (treeGaugedState a x S ς Q X p)) (ContinuousLinearMap.mul ℝ ℂ)
def IsAxialGaugeInsertion {Y : Type} [MeasurableSpace Y] (Q : Set (Set (FourTorus a.L m))) (n : ℕ)
    (X : Set (FourTorus a.L m)) (μ ν : StoredTerm a.L m K k Y) : Prop :=
  ∀ hL : 0 < a.L,
  haveI : Finite (SiteAtLevel a.L m K (stageLevel (degreeChoice a) x k n)) :=
    SeparatedSequences.BaseParameters.site_finite hL m _
  ∀ F : StoredState a.L m K k Y → ℂ, IsBoundedMeasurableObservable F →
    ν.integral F (ContinuousLinearMap.mul ℝ ℂ) =
      μ.integral (fun p => ∫ u, F (gaugeStoredField (stageLevel (degreeChoice a) x k n)
          (axialShellGauge K (stageLevel (degreeChoice a) x k n)
            (newGaugeSites (degreeChoice a) x S Q n X) u) p)
        ∂axialShellLaw (x (stageLevel (degreeChoice a) x k n))
          (Thresholds.epsThreshold (degreeChoice a).A₀ (degreeChoice a).𝔭₀ x
            (stageLevel (degreeChoice a) x k n))
          K (stageLevel (degreeChoice a) x k n)
          (newGaugeSites (degreeChoice a) x S Q n X)
          (p.2.1.1 (stageLevel (degreeChoice a) x k n)))
        (ContinuousLinearMap.mul ℝ ℂ)
def boxSites (Q : Set (Set (FourTorus a.L m))) (X : Set (FourTorus a.L m)) : Finset (FourTorus a.L m) :=
  setToFinset {p | p ∈ sublattice a.L m (levelDepth K k) ∧ p ∈ S.innerBoxIn a.r x Q X}
def IsBoxGaugeAveraging {Y : Type} [MeasurableSpace Y] (Q : Set (Set (FourTorus a.L m)))
    (X : Set (FourTorus a.L m)) (μ ν : StoredTerm a.L m K k Y) : Prop :=
  ∀ F : StoredState a.L m K k Y → ℂ, IsBoundedMeasurableObservable F →
    ν.integral F (ContinuousLinearMap.mul ℝ ℂ) =
      μ.integral (fun p => ∫ u, F (blockFieldOrKeep p (gaugeTransform
          (fun y : SiteAtLevel a.L m K k =>
            (FaddeevPopov.extendByOne u (y : FourTorus a.L m) : Matrices.ComplexMatrix2)) p.1.1), p.2)
        ∂ConfigSpaces.gaugeHaar (boxSites a x S Q X))
        (ContinuousLinearMap.mul ℝ ℂ)
def fieldWithReference (𝔟 : Set (BondAtLevel a.L m K k))
    (V' VΛ V : BondAtLevel a.L m K k → Matrices.ComplexMatrix2) :
    BondAtLevel a.L m K k → Matrices.ComplexMatrix2 :=
  open Classical in fun b => if b ∈ 𝔟 then extendedField 𝔟 V' VΛ b else V b
def stateMinimizer {Y : Type} (ς : BasePairSelection a x S α)
    (X : Set (FourTorus a.L m)) (p : StoredState a.L m K k Y) :
    BondAtLevel a.L m K k → Matrices.ComplexMatrix2 :=
  (componentPair ς X p.1.1 p.2.1).1
def referenceIntegral {Y : Type} (ς : BasePairSelection a x S α)
    (Q : Set (Set (FourTorus a.L m))) (X : Set (FourTorus a.L m)) (F : StoredState a.L m K k Y → ℂ)
    (p : StoredState a.L m K k Y) : ℂ :=
  gaugeFixedIntegral (c := degreeChoice a)
    (bondsAsSigma (innerBoxBonds (radiiChoice a) S Q X))
    (boxTreeRotated (radiiChoice a) S Q X (p.2.1.2.frame X)) fun V' =>
      componentFactor (radiiChoice a) S Q X (stateMinimizer a x S ς X p) (V' k) /
          componentNormalizer (radiiChoice a) S Q X (p.2.1.2.frame X)
            (stateMinimizer a x S ς X p) *
        F (blockFieldOrKeep p (fieldWithReference a (innerBoxBonds (radiiChoice a) S Q X) (V' k)
            (stateMinimizer a x S ς X p) p.1.1), p.2)
def IsReferenceInsertionLiteral {Y : Type} [MeasurableSpace Y]
    (ς : BasePairSelection a x S α) (Q : Set (Set (FourTorus a.L m))) (X : Set (FourTorus a.L m))
    (μ ν : StoredTerm a.L m K k Y) : Prop :=
  ∀ F : StoredState a.L m K k Y → ℂ, IsBoundedMeasurableObservable F →
    ν.integral F (ContinuousLinearMap.mul ℝ ℂ) =
      μ.integral (referenceIntegral a x S ς Q X F) (ContinuousLinearMap.mul ℝ ℂ)
def IsReferenceInsertion {Y : Type} [MeasurableSpace Y]
    (ς : BasePairSelection a x S α) (Q : Set (Set (FourTorus a.L m))) (X : Set (FourTorus a.L m))
    (μ ν : StoredTerm a.L m K k Y) : Prop :=
  ∀ F : StoredState a.L m K k Y → ℂ, IsBoundedMeasurableObservable F →
    ν.integral F (ContinuousLinearMap.mul ℝ ℂ) =
      μ.integral (fun p =>
        open Classical in
        if NormalizerAdmissible ς Q X p.1.1 p.2.1 then
          referenceIntegral a x S ς Q X F p
        else F p)
        (ContinuousLinearMap.mul ℝ ℂ)
variable {𝔅 : StoredBonds a.L m K k}
def IsSlotOperation (slots : List Slot) (C : StageTermsByBranch 𝔅)
    (φ : CollarTestForm) (ς : BasePairSelection a x S α) :
    Slot → ∀ s : OperationState a.L m K k (StageOutput 𝔅),
      ∀ X : Set (FourTorus a.L m), TermOperation s.term X → List (StageOutput 𝔅) → Prop
  | .split e, s, X, κ, b =>
      b = [] ∧ IsPartitionWith (splitObservable a x S φ ς s.remaining X e) κ
  | .stageGaugeFixing n, s, X, κ, b =>
      b = [] ∧ IsIdentityBy .faddeevPopov
        (fun _ _ μ ν => IsAxialGaugeInsertion a x S s.remaining n X μ ν) κ
  | .stageIndicatorRemoval _, _, _, κ, b =>
      b = [] ∧ IsRewrite .indicatorToOne κ
  | .collarShift _, _, _, κ, b => b = [] ∧ IsRewrite .changeOfVariables κ
  | .stageIntegration n, s, X, κ, b =>
      IsRewrite .explicitIntegral κ ∧ b.Nodup ∧
        ∀ t, t ∈ b ↔ ∃ Y, IsStageTermDomain T a x S s.remaining n Y ∧
          (Y ∩ S.collarRegion a.r x s.remaining n ∩ X).Nonempty ∧
            t = ⟨n + 1, Y, C (stageRegions slots s) (n + 1) Y⟩
  | .boxIntegration, s, X, κ, b =>
      b = [] ∧ IsEquivalenceBy (fun _ _ μ ν => IsBondIntegration
        (bondsAsSigma (innerBoxBonds (radiiChoice a) S s.remaining X)) μ ν) κ
  | .frameSum, _, X, κ, b =>
      b = [] ∧ IsIdentityBy .frameAverage (fun _ _ μ ν => IsFrameAveraging X μ ν) κ
  | .nestGaugeFixing, s, X, κ, b =>
      b = [] ∧ IsIdentityBy .faddeevPopov
        (fun _ _ μ ν => IsTreeGaugeFixing a x S ς s.remaining X μ ν) κ
  | .mixedGaugeChange, _, X, κ, b =>
      b = [] ∧ IsIdentityBy .changeOfVariables (fun _ _ μ ν => IsLocalTo X μ ν) κ
  | .regularityRemoval, _, _, κ, b =>
      b = [] ∧ IsRewrite .indicatorToOne κ
  | .referenceLaw, s, X, κ, b =>
      b = [] ∧ IsEquivalenceBy
        (fun _ _ μ ν => IsReferenceInsertion a x S ς s.remaining X μ ν) κ
  | .referenceLawLiteral, s, X, κ, b =>
      b = [] ∧ IsEquivalenceBy
        (fun _ _ μ ν => IsReferenceInsertionLiteral a x S ς s.remaining X μ ν) κ
  | .localization, _, _, κ, b => b = [] ∧ IsRewrite .resummation κ
  | .classSplit, _, X, κ, b => b = [] ∧ IsPartitionWith (classObservable a x (k := k) X) κ
  | .boxTestRemoval, _, _, κ, b =>
      b = [] ∧ IsRewrite .indicatorToOne κ
  | .boxTreeRemoval, s, X, κ, b =>
      b = [] ∧ ∃ e : TermEquivalence s.term X, κ = .equivalence e ∧
        (HasClassIndicator slots (fun p => p = .classSplit) s X →
          OnStoredVariables (fun _ _ μ ν => IsBoxGaugeAveraging a x S s.remaining X μ ν)
            s.term e.result) ∧
        (¬HasClassIndicator slots (fun p => p = .classSplit) s X → e.result = s.term)
  | .exponentiation, _, _, κ, b => b = [] ∧ IsRewrite .resummation κ
end Operation
end PeriodicLattice.OperationList
end YangMills.Construction
