import YangMills.Construction.Lattice.EffectiveDensitiesAndTheirTerms
import YangMills.Construction.Lattice.FrameSumOfTheLargeFieldOperation
import YangMills.Construction.Lattice.StageTreeAndReversedMovesOfGaugeFixing
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open MeasureTheory Set ParameterChoice
namespace PeriodicLattice.RangeConstruction
open BorelKernels CentralBlock EffectiveDensities FrameAveraging LargeFieldGaugeMoves
  OperationList OperationMoves LargeFieldCourse ConfigSpaces CubesOfStep
  TermEvaluation
universe u
abbrev EvaluationCondition (L : ℕ) : Type 1 :=
  ∀ (m K k : ℕ) (Stored : Type) (M : GaugeMoveData.{0} L m K k Stored)
    (_ : ComplexMeasure (BlockFields L m K k)) (Z : Type) [MeasurableSpace Z],
    FiniteComplexMeasure (M.Space Z) → Prop
def trivialCoordinateCondition (L : ℕ) : EvaluationCondition L := fun _ _ _ _ _ _ _ _ _ => True
section EvaluationMaps
variable {L m K k : ℕ} {Stored Lebesgue : Type} {Y : Type} [MeasurableSpace Y]
def fieldValuesOn {v : BondField L m K k Stored} {E : Finset (GradedBond L m K)} {Z W : Type}
    [MeasurableSpace Z] [MeasurableSpace W] :
    StateEvaluation v E Z W Lebesgue → W → Stored → Matrices.ComplexMatrix2.specialUnitary
  | .literal (Named := _) (O := _) (hO := _) _ _ e, w => (e w).1
  | .framed (C := _) (Named := _) (O := _) (hO := _) _ _ e, w => (e w).2.1
def IsConcentratedOn (B : Set (StoredVariables L m K × Y)) (μ : StoredTerm L m K k Y) : Prop :=
  ∀ A, MeasurableSet A → (∀ q ∈ A, q.2 ∉ B) → μ A = 0
def observablePushforward {W : Type} [MeasurableSpace W] (π : StoredVariables L m K × Y → W)
    (μ : StoredTerm L m K k Y) : ComplexStateMeasure L m K k W :=
  μ.map fun q => (q.1, π q.2)
structure CarriesVariables {v : BondField L m K k Stored} {E : Finset (GradedBond L m K)}
    {Z W : Type} [MeasurableSpace Z] [MeasurableSpace W] (ρ : StateEvaluation v E Z W Lebesgue)
    (π : StoredVariables L m K × Y → W) (B : Set (StoredVariables L m K × Y))
    (μ ν : StoredTerm L m K k Y) : Prop where
  measurable : Measurable π
  measurableSet : MeasurableSet B
  injOn : InjOn π B
  concentrated_before : IsConcentratedOn B μ
  concentrated_after : IsConcentratedOn B ν
  stored_eq : ∀ w ∈ B, ∀ (c : v.support) (s : Stored), v.coord c = Sum.inr s →
    ((fieldValuesOn ρ (π w) s : Matrices.ComplexMatrix2.specialUnitary) :
        Matrices.ComplexMatrix2) = w.1.1 c.1.1 c.1.2 ∧
      (((fieldValuesOn ρ (π w) s)⁻¹ : Matrices.ComplexMatrix2.specialUnitary) :
          Matrices.ComplexMatrix2) =
        w.1.1 (OrientedEdgeEnds.flip c.1).1 (OrientedEdgeEnds.flip c.1).2
def IsMoveSpaceRepresentation (M : GaugeMoveData.{0} L m K k Stored) {Z : Type} [MeasurableSpace Z]
    {W : Type} [MeasurableSpace W] :
    StateEvaluation M.moved M.bondSet (M.fixedSpace × Z) W Lebesgue → Prop
  | .literal (Named := _) (O := _) (hO := _) holds object _ =>
      ∃ N, M.IsMoveRepresentation (𝒴' := Z) N holds object
  | .framed (C := _) (Named := _) (O := _) (hO := _) holds object _ =>
      ∃ N, M.IsFramedMoveRepresentation (𝒴' := Z) N holds object
structure IsMoveStep (ℭ : EvaluationCondition L) (M : GaugeMoveData.{0} L m K k Stored)
    {Z W : Type}
    [MeasurableSpace Z] [MeasurableSpace W]
    (ρ : StateEvaluation M.moved M.bondSet (M.fixedSpace × Z) W Lebesgue)
    (π : StoredVariables L m K × Y → W) (B : Set (StoredVariables L m K × Y))
    (μ ν : StoredTerm L m K k Y) : Prop where
  configSpace : M.IsConfigSpace Z
  evalOnSigma : IsMoveSpaceRepresentation M ρ
  carries : CarriesVariables ρ π B μ ν
  presentation : M.IsTermPresentation (pushToBlockFields μ)
    (ρ.pushforward (observablePushforward π μ))
  image_eq : ρ.pushforward (observablePushforward π ν) =
    M.fixGaugeMeasure (ρ.pushforward (observablePushforward π μ))
  presentationAfter : M.IsTermPresentation (pushToBlockFields ν)
    (ρ.pushforward (observablePushforward π ν))
  admissible : ℭ m K k Stored M (pushToBlockFields μ) Z (ρ.pushforward (observablePushforward π μ))
def IsMoveResult (ℭ : EvaluationCondition L)
    (IsMove : ∀ Stored : Type, GaugeMoveData.{0} L m K k Stored → Prop) (Y : Type) [MeasurableSpace Y] (μ ν : StoredTerm L m K k Y) : Prop :=
  ∃ (Stored Lebesgue Z W : Type) (_ : MeasurableSpace Z) (_ : MeasurableSpace W)
    (M : GaugeMoveData.{0} L m K k Stored)
    (ρ : StateEvaluation M.moved M.bondSet (M.fixedSpace × Z) W Lebesgue)
    (π : StoredVariables L m K × Y → W) (B : Set (StoredVariables L m K × Y)),
    IsMove Stored M ∧ IsMoveStep ℭ M ρ π B μ ν
end EvaluationMaps
section Moves
variable (a : FullChoice) {m K : ℕ} (x : ℕ → ℝ) [∀ i, Finite (SiteAtLevel a.L m K i)]
def IsTraceMove : ∀ {k : ℕ}, LabelAtLevel (degreeChoice a) m K x k →
    StepTrace (degreeChoice a) m K x k → ∀ Stored : Type,
    GaugeMoveData.{0} a.L m K k Stored → Prop
  | 0, _, s, Stored, M => ∃ O, M = initialStepMove (degreeChoice a) K x Stored O s.densityRegion
        s.plaquetteRegion ∧ IsInitialStep (degreeChoice a) K x s.densityRegion s.plaquetteRegion
  | k + 1, S, s, Stored, M => ∃ O, M = laterStepMove (degreeChoice a) K x Stored (k + 1) O
        s.plaquetteRegion (incomingRegion (degreeChoice a) K x S) ∧
      IsLaterStep (degreeChoice a) K x (k + 1) s.plaquetteRegion
        (incomingRegion (degreeChoice a) K x S)
variable {k : ℕ} (S : LabelAtLevel (degreeChoice a) m K x k) (Q : Set (Set (FourTorus a.L m)))
def IsStageMove (n : ℕ) (Stored : Type) (M : GaugeMoveData.{0} a.L m K k Stored) : Prop :=
  ∃ (v : BondField a.L m K k Stored)
    (O : BondOrientation a.L m K (stageLevel (degreeChoice a) x k n)),
    M = stageMove (degreeChoice a) x S Q Stored n v O ∧ IsLargeFieldSetting K k Q ∧
      Thresholds.delayDepth a.L a.r x k ≤ k ∧ IsLargeFieldStage (degreeChoice a) x n v
def IsHaarMove (X : Set (FourTorus a.L m)) (Stored : Type)
    (M : GaugeMoveData.{0} a.L m K k Stored) : Prop :=
  ∃ O : BondOrientation a.L m K k,
    M = haarMove (degreeChoice a) x S Q Stored X O ∧ IsLargeFieldSetting K k Q
variable {S Q} {α : ℝ} in
def IsSelectedPairValues (ς : BasePairSelection a x S α) (r : ↥Q → SignedFrame)
    (V : BondAtLevel a.L m K k → Matrices.ComplexMatrix2) {T : Finset (GradedBond a.L m K)}
    {R : Finset (FourTorus a.L m)}
    (w : AxialValues T R) : Prop :=
  HasBasePair a x S α Q r V ∧
    ∀ b : parentBonds T R, ((w b : Matrices.ComplexMatrix2.specialUnitary) :
        Matrices.ComplexMatrix2) =
      baseDatum (degreeChoice a) (ς.pair Q r V).2 b.1.1 b.1.2
variable {α : ℝ} in
def HasSelectedPairValues (ς : BasePairSelection a x S α) {Lebesgue : Type}
    (r : ↥Q → SignedFrame) {Stored : Type} (v : BondField a.L m K k Stored)
    (O : ∀ i, BondOrientation a.L m K i) {Z : Type} {W : Type} [MeasurableSpace Z]
    [MeasurableSpace W]
    (ρ : StateEvaluation v (treeMove (degreeChoice a) x S Q Stored r v O).bondSet
      (TreeMoveFixedSpace (degreeChoice a) x S Q r × Z) W Lebesgue) : Prop :=
  ∀ q : PeriodicLattice.LevelStateSpace a.L m K k W,
    match axialCoordinate (degreeChoice a) x S r Z (ρ.toConfig q).2 with
    | Sum.inl w => IsSelectedPairValues a x ς r q.1.1 w
    | Sum.inr _ => ¬∃ w : AxialValues (treeBonds (degreeChoice a) x S Q r)
        (treeRoots (degreeChoice a) x S Q r), IsSelectedPairValues a x ς r q.1.1 w
variable {α : ℝ} in
def IsTreeMoveStep (ℭ : EvaluationCondition a.L) (ς : BasePairSelection a x S α)
    (r : ↥Q → SignedFrame) (Y : Type) [MeasurableSpace Y] (μ ν : StoredTerm a.L m K k Y) : Prop :=
  ∃ (Stored Lebesgue Z W : Type) (_ : MeasurableSpace Z) (_ : MeasurableSpace W)
    (v : BondField a.L m K k Stored) (O : ∀ i, BondOrientation a.L m K i)
    (ρ : StateEvaluation v (treeMove (degreeChoice a) x S Q Stored r v O).bondSet
      (TreeMoveFixedSpace (degreeChoice a) x S Q r × Z) W Lebesgue)
    (π : StoredVariables a.L m K × Y → W) (B : Set (StoredVariables a.L m K × Y)),
    IsLargeFieldSetting K k Q ∧
    (∀ X : ↥Q, ∃ y : FourTorus a.L m,
      (y = ((LargeFieldGaugeMoves.boxEntranceBond (degreeChoice a) x S Q X.1 (r X)).source : FourTorus a.L m) ∨
        y = ((LargeFieldGaugeMoves.boxEntranceBond (degreeChoice a) x S Q X.1 (r X)).target : FourTorus a.L m)) ∧
      y ∉ S.innerBox a.r x Q) ∧
    IsTreeMoveAdmissible (degreeChoice a) x S Q r ∧
    IsMixedDatum (degreeChoice a) x S Q v ∧
    IsMoveStep ℭ (treeMove (degreeChoice a) x S Q Stored r v O) ρ π B μ ν ∧
    HasSelectedPairValues a x S Q ς r v O ρ
end Moves
section Step
variable (a : FullChoice) {m K : ℕ} (x : ℕ → ℝ)
def preMoveFactor : ∀ {k : ℕ}, LabelAtLevel (degreeChoice a) m K x k →
    StepTrace (degreeChoice a) m K x k → AllLevelFields a.L m K → ℝ
  | 0, _, s, W =>
    initialDensityUnityTerm (degreeChoice a) K x (W 0) s.densityRegion *
      plaquetteUnityTerm (degreeChoice a) K x 0 (blockFieldAt (degreeChoice a) K 0 (W 0))
        (initialPlaquetteRegionOf (degreeChoice a) K x s.densityRegion) s.plaquetteRegion
  | k + 1, S, s, W =>
    plaquetteUnityTerm (degreeChoice a) K x (k + 1)
      (blockFieldAt (degreeChoice a) K (k + 1) (W (k + 1)))
      (plaquetteTestRegion (degreeChoice a) K x (k + 1) (incomingRegion (degreeChoice a) K x S))
      s.plaquetteRegion
def postMoveFactor : ∀ {k : ℕ}, LabelAtLevel (degreeChoice a) m K x k →
    StepTrace (degreeChoice a) m K x k → AllLevelFields a.L m K → ℝ
  | 0, S, s, W =>
    fluctuationUnityTerm (degreeChoice a) K x 0 (W 0) (blockFieldAt (degreeChoice a) K 0 (W 0))
        (fluctuationTestRegion (degreeChoice a) K x 0
          (initialGaugeRegionOf (degreeChoice a) K x s.densityRegion s.plaquetteRegion))
        s.fluctuationRegion *
      partitionTerm (radiiChoice a) x (stepDataAt a x S s W) s.outcome
  | k + 1, S, s, W =>
    fluctuationUnityTerm (degreeChoice a) K x (k + 1) (W (k + 1))
        (blockFieldAt (degreeChoice a) K (k + 1) (W (k + 1)))
        (fluctuationTestRegion (degreeChoice a) K x (k + 1)
          (stepGaugeFixedRegion (degreeChoice a) K x (k + 1) s.plaquetteRegion
            (incomingRegion (degreeChoice a) K x S)))
        s.fluctuationRegion *
      partitionTerm (radiiChoice a) x (stepDataAt a x S s W) s.outcome
variable [∀ i, Finite (SiteAtLevel a.L m K i)]
inductive IsRangeStepTerm (ℭ : EvaluationCondition a.L) {k : ℕ}
    (S : LabelAtLevel (degreeChoice a) m K x k) (s : StepTrace (degreeChoice a) m K x k) :
    StateTerm a.L m K k → StateTerm a.L m K (k + 1) → Prop
  | mk (μ μ₁ μ₂ : StoredTerm a.L m K k Unit) (ν : StoredTerm a.L m K (k + 1) Unit)
      (pre : IsDensityMeasure (fun p => preMoveFactor a x S s (stateFields p)) μ μ₁)
      (moveStep : IsMoveResult ℭ (IsTraceMove a x S s) Unit μ₁ μ₂)
      (image_eq : ∀ F : StoredState a.L m K (k + 1) Unit → ℂ, IsBoundedMeasurableObservable F →
        ν.integral F (ContinuousLinearMap.mul ℝ ℂ) =
          μ₂.integral
            (fun p => (postMoveFactor a x S s (stateFields p) : ℂ) * afterBlocking F p)
            (ContinuousLinearMap.mul ℝ ℂ)) :
      IsRangeStepTerm ℭ S s (StateTerm.mk (StoredVariables a.L m K × Unit) μ)
        (StateTerm.mk (StoredVariables a.L m K × Unit) ν)
end Step
section Operation
variable (T : DerivedConstants) (a : FullChoice) {m K : ℕ} (x : ℕ → ℝ) {k : ℕ}
  (S : LabelAtLevel (degreeChoice a) m K x k) {𝔅 : StoredBonds a.L m K k} {α : ℝ}
def IsLeadingAtSlot {B : Type} (s : OperationState a.L m K k B) (X : Set (FourTorus a.L m)) : Prop :=
  ∀ Y ∈ s.remaining, (s.performedAt Y).length = (s.performedAt X).length
def IsFramedMoveOn (places : List Slot) (n : ℕ)
    (C : StageTermsByBranch 𝔅) (φ : CollarTestForm)
    (ς : BasePairSelection a x S α) (side : Bool)
    (s : OperationState a.L m K k (StageOutput 𝔅)) (X : Set (FourTorus a.L m)) {Y : Type}
    [MeasurableSpace Y] (μ ν : StoredTerm a.L m K k Y) : Prop :=
  let F := frameSumRegions places s
  6 ≤ n ∧ n ≤ 8 ∧ s.term = StateTerm.mk (StoredVariables a.L m K × Y) μ ∧
    ∃ p, slotReached places s X = some p ∧ (moveOfSlot p).major = n ∧
      ∀ r : ↥F → SignedFrame,
        let s' : OperationState a.L m K k (StageOutput 𝔅) :=
          { s with term := StateTerm.mk (StoredVariables a.L m K × Y) (frameSummand F r μ) }
        ∃ (κ : TermOperation s'.term X) (b : List (StageOutput 𝔅)),
          IsSlotOperation T a x S places C φ ς p s' X κ b ∧
            resultTerm side κ = StateTerm.mk (StoredVariables a.L m K × Y) (frameSummand F r ν)
def IsFramedOperation (places : List Slot) (C : StageTermsByBranch 𝔅)
    (φ : CollarTestForm) (ς : BasePairSelection a x S α) (p : Slot)
    (s : OperationState a.L m K k (StageOutput 𝔅)) (X : Set (FourTorus a.L m))
    (κ : TermOperation s.term X) : Prop :=
  ∀ side : Bool, ∃ (Y : Type) (_ : MeasurableSpace Y) (μ ν : StoredTerm a.L m K k Y),
    resultTerm side κ = StateTerm.mk (StoredVariables a.L m K × Y) ν ∧
      IsFramedMoveOn T a x S places (moveOfSlot p).major C φ ς side s X μ ν
variable [∀ i, Finite (SiteAtLevel a.L m K i)]
def IsRangeSlotOperation (ℭ : EvaluationCondition a.L) (places : List Slot)
    (C : StageTermsByBranch 𝔅) (φ : CollarTestForm)
    (ς : BasePairSelection a x S α) :
    Slot → ∀ s : OperationState a.L m K k (StageOutput 𝔅),
      ∀ X : Set (FourTorus a.L m), TermOperation s.term X → List (StageOutput 𝔅) → Prop
  | .stageGaugeFixing n, s, X, κ, b =>
      b = [] ∧
        (IsLeadingAtSlot a s X → IsIdentityBy .faddeevPopov
          (fun Y _ μ ν => IsMoveResult ℭ (IsStageMove a x S s.remaining n) Y μ ν) κ) ∧
        (¬IsLeadingAtSlot a s X → IsRewrite .faddeevPopov κ)
  | .nestGaugeFixing, s, X, κ, b =>
      b = [] ∧
        (IsLeadingAtSlot a s X → IsIdentityBy .faddeevPopov
          (fun Y _ μ ν => ∀ r : ↥s.remaining → SignedFrame,
            IsTreeMoveStep a x S s.remaining ℭ ς r Y (frameSummand s.remaining r μ)
              (frameSummand s.remaining r ν)) κ) ∧
        (¬IsLeadingAtSlot a s X → IsRewrite .faddeevPopov κ)
  | .boxTreeRemoval, s, X, κ, b =>
      b = [] ∧ ∃ e : TermEquivalence s.term X, κ = .equivalence e ∧
        (HasClassIndicator places (fun p => p = .classSplit) s X →
          OnStoredVariables (fun Y _ μ ν =>
            ∀ r : ↥(frameSumRegions places s) → SignedFrame,
              IsMoveResult ℭ (IsHaarMove a x S s.remaining X) Y
                (frameSummand (frameSumRegions places s) r μ)
                (frameSummand (frameSumRegions places s) r ν)) s.term e.result) ∧
        (¬HasClassIndicator places (fun p => p = .classSplit) s X → e.result = s.term)
  | .localization, s, X, κ, b =>
      b = [] ∧ (∃ i : TermIdentity s.term, κ = .identity i ∧ i.kind = .resummation) ∧
        IsFramedOperation T a x S places C φ ς .localization s X κ
  | .classSplit, s, X, κ, b =>
      b = [] ∧ (∃ d, κ = .partition d) ∧ IsFramedOperation T a x S places C φ ς .classSplit s X κ
  | .boxTestRemoval, s, X, κ, b =>
      b = [] ∧ (∃ i : TermIdentity s.term,
        κ = .identity i ∧ i.kind = .indicatorToOne) ∧
        IsFramedOperation T a x S places C φ ς .boxTestRemoval s X κ
  | .exponentiation, s, X, κ, b =>
      b = [] ∧ (∃ i : TermIdentity s.term, κ = .identity i ∧ i.kind = .resummation) ∧
        IsFramedOperation T a x S places C φ ς .exponentiation s X κ
  | p, s, X, κ, b => OperationList.IsSlotOperation T a x S places C φ ς p s X κ b
def rangeSchedule (ℭ : EvaluationCondition a.L)
    (places : List Slot) (C : StageTermsByBranch 𝔅) (φ : CollarTestForm)
    (ς : BasePairSelection a x S α) : OperationSchedule a.L m K k (StageOutput 𝔅) :=
  scheduleOfSlots places (fun p => p = .classSplit) (IsRangeSlotOperation T a x S ℭ places C φ ς)
end Operation
section Terms
variable {a : FullChoice} {m K : ℕ} {x : ℕ → ℝ} [∀ i, Finite (SiteAtLevel a.L m K i)]
structure IsRangeGeneratedWith (ℭ : EvaluationCondition a.L) (t : FlowTerms a m K x)
    (T : DerivedConstants) (φ : CollarTestForm) {α : ℝ} (c : CourseChoices a m K x α)
    (𝒪 : RGStepOperation a m K x) (ν₀ : ComplexMeasure (BlockFields a.L m K 0)) (l : ℕ) :
    Prop where
  level_le : l ≤ K
  initial_eq : t.atHistory 0 .initial = bareTerm ν₀
  step_term : ∀ k < l, ∀ h : DecomposedHistory (degreeChoice a) m K x k, 𝒪.Generates h →
    ∀ s : StepTrace (degreeChoice a) m K x k, s.IsStepOf h.finalLabel →
      IsRangeStepTerm a x ℭ h.finalLabel s (t.atHistory k h) (t.afterStep k ⟨h, s⟩)
  operation_term : ∀ k < l, ∀ h : DecomposedHistory (degreeChoice a) m K x k, 𝒪.Generates h →
    ∀ s : StepTrace (degreeChoice a) m K x k, s.IsStepOf h.finalLabel →
      ∃ (𝔅 : StoredBonds a.L m K (k + 1)) (C : StageTermsByBranch 𝔅)
        (f : List (OperationState a.L m K (k + 1) (StageOutput 𝔅) × BranchData a.L m)),
        IsOperationWithBranches
          (𝒪.form.slots (Thresholds.delayDepth a.L a.r x (k + 1)))
          (rangeSchedule T a x s.label ℭ
            (𝒪.form.slots (Thresholds.delayDepth a.L a.r x (k + 1))) C φ (c.selection k h s))
          (𝒪.classing k ⟨h, s⟩) (t.afterStep k ⟨h, s⟩) f ∧
        ∀ o : DecomposedOperation (degreeChoice a) m K x k,
          o.IsOperationOn ⟨h, s⟩ (𝒪.classing k ⟨h, s⟩) → UsesOnlySlotsOf 𝒪.form o →
            ∃ b ∈ f, MatchesBranch o b.2 ∧ b.2.visited = c.order k h s o ∧
              IsTraceTerm s.label o b.1.term (t.atHistory (k + 1) (.extend h s o))
abbrev IsRangeGenerated (t : FlowTerms a m K x) (T : DerivedConstants)
    (φ : CollarTestForm) {α : ℝ} (c : CourseChoices a m K x α)
    (𝒪 : RGStepOperation a m K x) (ν₀ : ComplexMeasure (BlockFields a.L m K 0)) (l : ℕ) :
    Prop :=
  IsRangeGeneratedWith (trivialCoordinateCondition a.L) t T φ c 𝒪 ν₀ l
end Terms
end PeriodicLattice.RangeConstruction
end YangMills.Construction
end
