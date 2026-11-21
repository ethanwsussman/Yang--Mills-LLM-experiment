import YangMills.Construction.Lattice.AdmissibleHistoriesAndLabels
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
noncomputable section
namespace YangMills.Construction
open ParameterChoice
namespace PeriodicLattice.EffectiveDensities
open LargeFieldCourse OperationList CubesOfStep CentralBlock
section Course
variable {L m K k : ℕ} {B : Type}
structure BranchData (L m : ℕ) where
  exitedAt : Lattice.LargeFieldDecomposition → Set (Set (FourTorus L m))
  classOne : Set (Set (FourTorus L m))
  classTwo : Set (Set (FourTorus L m))
  visited : List (Set (FourTorus L m))
namespace BranchData
def empty (L m : ℕ) : BranchData L m := ⟨fun _ => ∅, ∅, ∅, []⟩
def addVisited (r : BranchData L m) (X : Set (FourTorus L m)) : BranchData L m :=
  { r with visited := r.visited ++ [X] }
def addExit (r : BranchData L m) (X : Set (FourTorus L m)) (e : Lattice.LargeFieldDecomposition) :
    BranchData L m :=
  { r with exitedAt := fun e' => r.exitedAt e' ∪ {Y | Y = X ∧ e' = e} }
def addClassOne (r : BranchData L m) (X : Set (FourTorus L m)) : BranchData L m :=
  { r with classOne := r.classOne ∪ {X} }
def addClassTwo (r : BranchData L m) (X : Set (FourTorus L m)) : BranchData L m :=
  { r with classTwo := r.classTwo ∪ {X} }
end BranchData
inductive YieldsWithBranches (slots : List Slot) (O : OperationSchedule L m K k B) :
    OperationState L m K k B → BranchData L m →
      List (OperationState L m K k B × BranchData L m) → Prop
  | finished (s : OperationState L m K k B) (r : BranchData L m) (h : O.isFinished s) :
      YieldsWithBranches slots O s r [(s, r)]
  | identity (s : OperationState L m K k B) (r : BranchData L m) (X : Set (FourTorus L m))
      (hX : X ∈ s.remaining) (i : TermIdentity s.term) (v : List B)
      (hO : O.isNext s X (.identity i) v)
      {f : List (OperationState L m K k B × BranchData L m)}
      (h : YieldsWithBranches slots O (s.step X (.identity i) v i.result) (r.addVisited X) f) :
      YieldsWithBranches slots O s r f
  | equivalence (s : OperationState L m K k B) (r : BranchData L m) (X : Set (FourTorus L m))
      (hX : X ∈ s.remaining) (e : TermEquivalence s.term X) (v : List B)
      (hO : O.isNext s X (.equivalence e) v)
      {f : List (OperationState L m K k B × BranchData L m)}
      (h : YieldsWithBranches slots O (s.step X (.equivalence e) v e.result) (r.addVisited X) f) :
      YieldsWithBranches slots O s r f
  | partition (s : OperationState L m K k B) (r : BranchData L m) (X : Set (FourTorus L m))
      (hX : X ∈ s.remaining) (d : PartitionOfUnity s.term) (v : List B)
      (hO : O.isNext s X (.partition d) v) (hd : ¬O.isClassPartition s X d)
      (e : Lattice.LargeFieldDecomposition)
      (he : slotReached slots s X = some (.split e))
      {f₁ f₂ : List (OperationState L m K k B × BranchData L m)}
      (h₁ : YieldsWithBranches slots O (s.step X (.partition d) v d.termχ)
        (r.addVisited X) f₁)
      (h₂ : YieldsWithBranches slots O
        ((s.step X (.partition d) v d.termCompl).dropAt X)
        ((r.addVisited X).addExit X e) f₂) :
      YieldsWithBranches slots O s r (f₁ ++ f₂)
  | classPartition (s : OperationState L m K k B) (r : BranchData L m) (X : Set (FourTorus L m))
      (hX : X ∈ s.remaining) (d : PartitionOfUnity s.term) (v : List B)
      (hO : O.isNext s X (.partition d) v) (hd : O.isClassPartition s X d)
      {f₁ f₂ : List (OperationState L m K k B × BranchData L m)}
      (h₁ : YieldsWithBranches slots O (s.step X (.partition d) v d.termχ)
        ((r.addVisited X).addClassOne X) f₁)
      (h₂ : YieldsWithBranches slots O (s.step X (.partition d) v d.termCompl)
        ((r.addVisited X).addClassTwo X) f₂) :
      YieldsWithBranches slots O s r (f₁ ++ f₂)
def IsOperationWithBranches (slots : List Slot) (O : OperationSchedule L m K k B)
    (Q : Set (Set (FourTorus L m))) (σ : StateTerm L m K k)
    (f : List (OperationState L m K k B × BranchData L m)) : Prop :=
  (Q = ∅ ∧ f = [(OperationState.start σ Q, BranchData.empty L m)]) ∨
    (Q.Nonempty ∧ YieldsWithBranches slots O (OperationState.start σ Q)
      (BranchData.empty L m) f)
end Course
section Initial
variable (L m K : ℕ)
def trivialStored : StoredVariables L m K × Unit :=
  ((fun _ _ => 1, ⟨fun _ => 1⟩), ())
variable {L m K}
def bareTerm (ν₀ : ComplexMeasure (BlockFields L m K 0)) : StateTerm L m K 0 :=
  StateTerm.mk (StoredVariables L m K × Unit) (ν₀.map fun V => (V, trivialStored L m K))
end Initial
section Step
variable {L m K k : ℕ} {Y : Type}
def afterBlocking (F : StoredState L m K (k + 1) Y → ℂ) (p : StoredState L m K k Y) : ℂ :=
  open Classical in
  if h : blockAverageStep (Averaging.smoothingRadius L) k p.1.1 ∈ gaugeFieldsAtLevel L m K (k + 1) then
    F (⟨blockAverageStep (Averaging.smoothingRadius L) k p.1.1, h⟩, ((stateFields p, p.2.1.2), p.2.2))
  else 0
end Step
section ScaleFlow
variable (a : FullChoice) {m K : ℕ} (x : ℕ → ℝ)
def stepDataAt {k : ℕ} (S : LabelAtLevel (degreeChoice a) m K x k)
    (s : StepTrace (degreeChoice a) m K x k) (W : AllLevelFields a.L m K) :
    StepData a.L m K k :=
  ⟨S.domainSeq, s.domain, W, W k, blockFieldAt (degreeChoice a) K k (W k)⟩
abbrev TermClassing (m K : ℕ) (x : ℕ → ℝ) : Type :=
  ∀ k, DecomposedTerm (degreeChoice a) m K x k → Set (Set (FourTorus a.L m))
def effectiveClassing : TermClassing a m K x := fun _ σ => σ.actingClass
inductive ScheduleForm where
  | effective
  | literal
def ScheduleForm.slots : ScheduleForm → ℕ → List Slot
  | .effective, N => operationSlots N
  | .literal, N => operationSlotsLiteral N
variable (m K) in
structure RGStepOperation where
  form : ScheduleForm
  classing : TermClassing a m K x
def effectiveOperation : RGStepOperation a m K x := ⟨.effective, effectiveClassing a x⟩
variable (m K) in
structure CourseChoices (α : ℝ) where
  selection : ∀ (k : ℕ) (_ : DecomposedHistory (degreeChoice a) m K x k)
    (s : StepTrace (degreeChoice a) m K x k), BasePairSelection a x s.label α
  order : ∀ (k : ℕ), DecomposedHistory (degreeChoice a) m K x k →
    StepTrace (degreeChoice a) m K x k → DecomposedOperation (degreeChoice a) m K x k →
    List (Set (FourTorus a.L m))
variable {a x}
def UsesOnlySlotsOf (Λ : ScheduleForm) {k : ℕ}
    (o : DecomposedOperation (degreeChoice a) m K x k) : Prop :=
  ∀ e he hp, Slot.split e ∉
      Λ.slots (Thresholds.delayDepth a.L a.r x (k + 1)) →
    o.outcome.complementCarriers (.leaveAt e he hp) = ∅
def HistoryUsesOnlySlotsOf (Λ : ScheduleForm) :
    ∀ {k : ℕ}, DecomposedHistory (degreeChoice a) m K x k → Prop
  | _, .initial => True
  | _, .extend h _ o => HistoryUsesOnlySlotsOf Λ h ∧ UsesOnlySlotsOf Λ o
def RGStepOperation.Generates (𝒪 : RGStepOperation a m K x) {k : ℕ}
    (h : DecomposedHistory (degreeChoice a) m K x k) : Prop :=
  h.IsGeneratedWith 𝒪.classing ∧ HistoryUsesOnlySlotsOf 𝒪.form h
structure MatchesBranch {k : ℕ} (o : DecomposedOperation (degreeChoice a) m K x k)
    (r : BranchData a.L m) : Prop where
  exits_test : ∀ e he hp, o.outcome.complementCarriers (.leaveAt e he hp) = r.exitedAt e
  exits_outerShell : ⋃ (P : Set (FourTorus a.L m)) (hP : P.Nonempty),
    o.outcome.complementCarriers (.shellUnion P hP) = r.exitedAt .testAtTheLastShell
  classOne_eq : o.outcome.classOne = r.classOne
  classTwo_eq : o.outcome.classTwo = r.classTwo
def outerShellPairs {k : ℕ} (o : DecomposedOperation (degreeChoice a) m K x k) :
    Set (Set (FourTorus a.L m) × Set (FourTorus a.L m)) :=
  {q | ∃ hP : q.1.Nonempty, q.2 ∈ o.outcome.complementCarriers (.shellUnion q.1 hP)}
def outerShellWeight {k : ℕ} (S : LabelAtLevel (degreeChoice a) m K x (k + 1))
    (o : DecomposedOperation (degreeChoice a) m K x k) (W : AllLevelFields a.L m K) : ℝ :=
  ∏ᶠ q ∈ outerShellPairs o,
    outerShellTerm (degreeChoice a) S o.survivorsAtOuterShell
      (W (outerShellLevel (degreeChoice a) x (k + 1)))
      (outerShell (degreeChoice a) S o.survivorsAtOuterShell q.2) q.1
def IsTraceTerm {k : ℕ} (S : LabelAtLevel (degreeChoice a) m K x (k + 1))
    (o : DecomposedOperation (degreeChoice a) m K x k) (t σ : StateTerm a.L m K (k + 1)) : Prop :=
  OnStoredVariables (fun _ _ μ ν => IsDensityMeasure
    (fun p => outerShellWeight S o (stateFields p)) μ ν) t σ
end ScaleFlow
section Terms
variable (a : FullChoice) (m K : ℕ) (x : ℕ → ℝ)
structure FlowTerms where
  atHistory : ∀ k, DecomposedHistory (degreeChoice a) m K x k → StateTerm a.L m K k
  afterStep : ∀ k, DecomposedTerm (degreeChoice a) m K x k → StateTerm a.L m K (k + 1)
variable {a m K x}
end Terms
end PeriodicLattice.EffectiveDensities
end YangMills.Construction
