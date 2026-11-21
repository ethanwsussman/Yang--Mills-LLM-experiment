import YangMills.Construction.Lattice.BondGraphs
import YangMills.Construction.Lattice.GaugeFixingMovesOfTheLargeFieldOperation
import YangMills.Construction.Lattice.MoveOfGaugeFixingOfAStep
import YangMills.Construction.Lattice.ReversedProcedureOnAStateSpace
import YangMills.Construction.Lattice.TreeLawOfAForestOfBonds
import Mathlib
set_option autoImplicit false
open MeasureTheory Set YangMills.Construction.ParameterChoice
noncomputable section
namespace YangMills.Construction.PeriodicLattice.OperationMoves
open BorelKernels TermEvaluation ConfigSpaces CubesOfStep CentralBlock LargeFieldGaugeMoves FaddeevPopov
open OperationList (setToFinset)
structure IsLargeFieldSetting {α : Type} (K k : ℕ) (Q : Set α) : Prop where
  one_le : 1 ≤ k
  le_top : k ≤ K
  finite : Q.Finite
section Variables
variable {L m K k : ℕ} {Stored : Type}
structure IsStoredFieldAt (j : ℕ) (v : BondField L m K k Stored) : Prop where
  level_eq : ∀ b ∈ v.support, b.1 = j
  stored : ∀ b : v.support, ∃ s, v.coord b = Sum.inr s
end Variables
variable (c : ChoiceUpToDegreeConstants) {m K : ℕ} (x : ℕ → ℝ) {k : ℕ}
  (S : LabelAtLevel c m K x k) (Q : Set (Set (FourTorus c.L m))) (Stored : Type)
section Stage
variable [∀ j, Finite (SiteAtLevel c.L m K j)]
def stageMove (n : ℕ) (v : BondField c.L m K k Stored)
    (O : BondOrientation c.L m K (stageLevel c x k n)) :
    GaugeMoveData.{0} c.L m K k Stored where
  siteSet := shellPoints K (stageLevel c x k n) (stageSites c x S Q n)
  moved := v
  bondSet := O.incidentBonds (shellPoints K (stageLevel c x k n) (stageSites c x S Q n))
  fixedSpace := BlockFields c.L m K k
  blockMap := Prod.snd
  kernel := fun _ _ => axialLaw K (stageLevel c x k n) (stageSites c x S Q n)
    (x (stageLevel c x k n)) (Thresholds.epsThreshold c.A₀ c.𝔭₀ x (stageLevel c x k n))
variable {Stored} in
structure IsLargeFieldStage (n : ℕ) (v : BondField c.L m K k Stored) : Prop where
  stage_lt : n < Thresholds.delayDepth c.L c.r x k
  inRange : IsAxialLawRange c.A₀ c.𝔭₀ x (stageLevel c x k n)
  isStored : IsStoredFieldAt (stageLevel c x k n) v
end Stage
section Tree
def exitPoints (r : ↥Q → SignedFrame) : Set (FourTorus c.L m) :=
  range fun X : ↥Q => boxEntrancePoint c x S Q X.1 (r X)
def treeRoots (r : ↥Q → SignedFrame) : Finset (FourTorus c.L m) :=
  setToFinset (exitPoints c x S Q r)
def treeBondSet (r : ↥Q → SignedFrame) : Set (GradedBond c.L m K) :=
  {t | t.1 ≤ K ∧ (⟨levelDepth K t.1, t.2⟩ : IndexedBond c.L m) ∈ nestTreeOfFrames c S Q r}
def treeBonds (r : ↥Q → SignedFrame) : Finset (GradedBond c.L m K) :=
  setToFinset (treeBondSet c x S Q r)
def treeOfFrames (r : ↥Q → SignedFrame) : MultiLevelBondSet c.L m K where
  edges := treeBonds c x S Q r
  edges_level_le := fun b hb => by
    unfold treeBonds setToFinset at hb
    split_ifs at hb with h
    · exact ((Set.Finite.mem_toFinset h).1 hb).1
    · simp at hb
structure IsTreeMoveAdmissible (r : ↥Q → SignedFrame) : Prop where
  mem_active : ∀ t ∈ nestTreeOfFrames c S Q r,
    ∃ b ∈ activeBondSet K k (S.trimmedDomain c.r x Q),
      (⟨levelDepth K b.1, b.2⟩ : IndexedBond c.L m) = t
  acyclic : (treeOfFrames c x S Q r).IsAcyclic
  existsUnique_exit : ∀ C ∈ (treeOfFrames c x S Q r).components,
    ∃! y, y ∈ exitPoints c x S Q r ∧ y ∈ C
  mem_innerBox : ∀ y ∈ (treeOfFrames c x S Q r).vertices, y ∉ exitPoints c x S Q r →
    y ∈ S.innerBox c.r x Q
def treeMoveSites (r : ↥Q → SignedFrame) : Finset (FourTorus c.L m) :=
  nonRootVertices (treeBonds c x S Q r) (treeRoots c x S Q r)
def activeIncidentBonds (O : ∀ i, BondOrientation c.L m K i)
    (P : Finset (FourTorus c.L m)) : Finset (GradedBond c.L m K) :=
  setToFinset {t | t ∈ activeBondSet K k (S.trimmedDomain c.r x Q) ∧ t.2 ∈ (O t.1).chosen ∧
    TouchesSites P t.2}
abbrev AxialValueSpace (r : ↥Q → SignedFrame) : Type :=
  AdjoinPoint (AxialValues (treeBonds c x S Q r) (treeRoots c x S Q r))
abbrev TreeMoveFixedSpace (r : ↥Q → SignedFrame) : Type :=
  BlockFields c.L m K k × AxialValueSpace c x S Q r
variable {Q} in
def axialCoordinate (r : ↥Q → SignedFrame) (𝒴' : Type) (ς : TreeMoveFixedSpace c x S Q r × 𝒴') :
    AxialValueSpace c x S Q r :=
  ς.1.2
def treeMove (r : ↥Q → SignedFrame) (v : BondField c.L m K k Stored)
    (O : ∀ i, BondOrientation c.L m K i) : GaugeMoveData.{0} c.L m K k Stored where
  siteSet := treeMoveSites c x S Q r
  moved := v
  bondSet := activeIncidentBonds c x S Q O (treeMoveSites c x S Q r)
  fixedSpace := TreeMoveFixedSpace c x S Q r
  blockMap := fun w => w.2.1
  kernel := fun 𝒴' _ => treeLaw (treeBonds c x S Q r) (treeRoots c x S Q r)
    (axialCoordinate c x S r 𝒴')
end Tree
section Haar
variable [Finite (SiteAtLevel c.L m K k)]
def haarMove (X : Set (FourTorus c.L m)) (O : BondOrientation c.L m K k) :
    GaugeMoveData.{0} c.L m K k Stored :=
  gaugeMoveOnSet Stored O (innerBoxPoints c x S Q X) fun _ _ => haarLaw (innerBoxPoints c x S Q X)
end Haar
end YangMills.Construction.PeriodicLattice.OperationMoves
