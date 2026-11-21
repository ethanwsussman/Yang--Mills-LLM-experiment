import YangMills.Construction.Lattice.CreationListedByAHistory
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.PeriodicLattice.CubesOfStep
variable {c : ParameterChoice.ChoiceUpToDegreeConstants} {m K : ℕ} {x : ℕ → ℝ} {D : ℕ → Type}
def LabelHistory.actedParts : ∀ {k : ℕ}, LabelHistory c m K x D k → Set (Set (FourTorus c.L m))
  | _, .initial => ∅
  | _, .extend h _ o => h.actedParts ∪ o.actedOn
variable (c m K x D) in
structure TermOfStep (k : ℕ) where
  past : LabelHistory c m K x D k
  trace : StepTrace c m K x k
def InCubeOfSide {L m : ℕ} (t : ℝ) (C : Set (FourTorus L m)) : Prop :=
  ∃ y, C ⊆ TorusMetric.torusProj (torusSide L m) '' cornerCube y t
variable (c K x) in
def nestingSide (i : ℕ) : ℝ :=
  100 * (c.M : ℝ) * (blockSizeAt c x i : ℝ) * meshSize c.L (levelDepth K i)
variable (c x) in
def delayAt (j : ℕ) : ℕ := Thresholds.delayDepth c.L c.r x j
variable (c x) in
def HasEnoughScales (j : ℕ) : Prop :=
  Thresholds.DelayDefined c.L c.r x j ∧ delayAt c x j ≤ j ∧
    Thresholds.minDelay c.L c.r x j < delayAt c x j
variable (c K x) in
def stepRegionFrom (k : ℕ) (Y : Set (FourTorus c.L m)) : Set (FourTorus c.L m) :=
  largeFieldRegionAfter c x
    (⟨fun _ => univ, smallFieldRegion c K x k (stepGaugeFixedRegion c K x k ∅ Y) ∅,
      fun _ _ => 1, fun _ => 1, fun _ => 1⟩ : StepData c.L m K k) ⟨∅, ∅, ∅⟩
namespace TermOfStep
variable {k : ℕ} (σ : TermOfStep c m K x D k)
def resultLabel : LabelAtLevel c m K x (k + 1) := σ.trace.label
def creationCubesAt (t : ℕ) : Set (FourTorus c.L m) :=
  if t = k + 1 then σ.trace.creationCubes σ.past.finalLabel else σ.past.creationCubesAt t
def partsAt (i : ℕ) : Set (Set (FourTorus c.L m)) :=
  regionComponents (coarseCubeIndex K (Nat.log c.L c.M) i) (σ.resultLabel.largeFieldOrEmpty i)
def CellDisjointFromCreation (C : Set (FourTorus c.L m)) : Prop :=
  ∀ t : ℕ, k + 1 < t + delayAt c x (k + 1) → t ≤ k + 1 →
    Disjoint (partitionCubesIn (K : ℤ) C) (partitionCubesIn (K : ℤ) (σ.creationCubesAt t))
def LowerPartsSmall (C : Set (FourTorus c.L m)) : Prop :=
  ∀ i : ℕ, k + 1 ≤ i + delayAt c x (k + 1) → i < k + 1 →
    ∀ C' ∈ σ.partsAt i, C' ⊆ C → InCubeOfSide (nestingSide c K x i) C'
def NoLargeFieldPartInside (a : ℕ) (C : Set (FourTorus c.L m)) : Prop :=
  ∀ j' : ℕ, a ≤ j' → j' < k + 1 → ∀ X ∈ σ.past.largeFieldRegionsAt j', ¬ X ⊆ C
def IsNestedTower (C : Set (FourTorus c.L m)) : Prop :=
  (∀ j' : ℕ, k + 1 ≤ j' + delayAt c x (k + 1) → j' ≤ k + 1 →
    C ∩ σ.resultLabel.largeFieldOrEmpty j' ∈ σ.partsAt j' ∧
      IsPartitionBox (coarseCubeIndex K (Nat.log c.L c.M) j') (C ∩ σ.resultLabel.largeFieldOrEmpty j') ∧
      InCubeOfSide (nestingSide c K x j') (C ∩ σ.resultLabel.largeFieldOrEmpty j')) ∧
  ∀ j' : ℕ, k + 1 ≤ j' + delayAt c x (k + 1) → j' < k + 1 →
    C ∩ σ.resultLabel.largeFieldOrEmpty (j' + 1) =
      stepRegionFrom c K x j' (C ∩ σ.resultLabel.largeFieldOrEmpty j')
structure MeetsActingConditions (C : Set (FourTorus c.L m)) : Prop where
  isPart : C ∈ σ.resultLabel.largeFieldParts (lastScale k)
  enough : HasEnoughScales c x (k + 1)
  inCube : InCubeOfSide (nestingSide c K x (k + 1)) C
  disjoint : σ.CellDisjointFromCreation C
  lowerSmall : σ.LowerPartsSmall C
  noLargeField : σ.NoLargeFieldPartInside (k + 1 - delayAt c x (k + 1)) C
  nested : σ.IsNestedTower C
def actingClass : Set (Set (FourTorus c.L m)) := {C | σ.MeetsActingConditions C}
end TermOfStep
end YangMills.Construction.PeriodicLattice.CubesOfStep
