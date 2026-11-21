import YangMills.Construction.Lattice.ComponentsOnWhichTheOperationActs
import YangMills.Construction.Lattice.OneStepAndLargeFieldOperations
import YangMills.Construction.Lattice.OneStepAndLargeFieldOperationsAtAPoint
import Mathlib
set_option autoImplicit false
open Set MeasureTheory
noncomputable section
namespace YangMills.Construction
open ParameterChoice
namespace PeriodicLattice.CubesOfStep
section Term
variable {c : ChoiceUpToDegreeConstants} {m K : ℕ} {x : ℕ → ℝ} {E : ℕ → Type} {k : ℕ}
def emptyOutcome (L m : ℕ) (D : Type) : LargeFieldOutcome D (∅ : Set (Set (FourTorus L m))) where
  complementCarriers := fun _ => ∅
  classOne := ∅
  classTwo := ∅
  complementCarriers_subset := fun _ => Subset.refl _
  classOne_subset := Subset.refl _
  classTwo_subset := Subset.refl _
  disjoint_classOne_classTwo := disjoint_bot_left
  sdiff_subset_classOne_union := by simp
def TermOfStep.historyBeforeLargeField (σ : TermOfStep c m K x E k) :
    LabelHistory c m K x E (k + 1) :=
  .extend σ.past σ.trace ⟨∅, emptyOutcome c.L m (E (k + 1)), σ.trace.label⟩
end Term
section Regions
variable (c : ChoiceUpToDegreeConstants) {m : ℕ} (K : ℕ) (x : ℕ → ℝ) {k : ℕ}
  (S : LabelAtLevel c m K x k) (j : ℕ) (X : Set (FourTorus c.L m))
def lowerStep (k : ℕ) : ℕ := (lowerLevel c.L c.r x k).toNat
def domainEnlarged (i a : ℕ) : Set (FourTorus c.L m) :=
  layerEnlargement (nestedCubeIndex c.L c.r x K (Nat.log c.L c.M) i) (S.domainSeq i) a
end Regions
section Groups
variable {m K : ℕ} (c : ChoiceUpToRadii) (x : ℕ → ℝ) {E : ℕ → Type} {k : ℕ}
  (τ : BackgroundVariant) (h : LabelHistory c.toChoiceUpToDegreeConstants m K x E k) {j : ℕ}
  (hj : j < k) (X : Set (FourTorus c.L m))
def leadingFunction (V : AllLevelFields c.L m K) : ℝ :=
  densityIndicator c.toChoiceUpToDegreeConstants K x k (V k)
    (domainEnlarged c.toChoiceUpToDegreeConstants K x h.finalLabel k 4)
end Groups
section Product
variable {m K : ℕ} (c : ChoiceUpToRadii) (x : ℕ → ℝ) {E : ℕ → Type} {k : ℕ}
  (τ : BackgroundVariant) (h : LabelHistory c.toChoiceUpToDegreeConstants m K x E k)
  (X : Set (FourTorus c.L m))
structure LowerOperation (L m K : ℕ) where
  Variables : Type
  integral : AllLevelFields L m K → (Variables → ℂ) → ℂ
  up : Variables → AllLevelFields L m K → AllLevelFields L m K
  down : Variables → AllLevelFields L m K → AllLevelFields L m K
  factor : Variables → AllLevelFields L m K → ℂ
variable {c x h X}
variable (h X) in
def fieldsUpwardBelow (l : ℕ) (A : AllStepVariables c x h X) (W : AllLevelFields c.L m K) :
    AllLevelFields c.L m K
  | 0 => if 0 < l then fieldsUpward A W 0 else W 0
  | n + 1 =>
    if n + 1 < l then fieldsUpward A W (n + 1)
    else if n + 1 = l then assignAverages h X n (fieldsUpward A W n) (W (n + 1))
    else W (n + 1)
variable (c x h X)
def fieldsDownwardFrom (l : ℕ) (A : AllStepVariables c x h X) :
    ∀ n, n ≤ k → AllLevelFields c.L m K → AllLevelFields c.L m K
  | 0, _, V => V
  | n + 1, hn, V =>
    if n < l then V
    else
      fieldsDownwardFrom l A n (by omega)
        (fieldsReadFromFluctuation c x (stepBasePoints c) τ h (j := n) (by omega) X V
          (A ⟨n, by omega⟩).2)
def iteratedStepIntegralFrom (l : ℕ) (W : AllLevelFields c.L m K) (Ψ : AllStepVariables c x h X → ℂ) :
    ∀ n, n ≤ k → AllStepVariables c x h X → ℂ
  | 0, _, A => Ψ A
  | n + 1, hn, A =>
    if n < l then Ψ A
    else
      ∫ v, complexPairedSpaceIntegral unitBondInner
          (realBondFormsOn (fluctuationBondsWithin c.toChoiceUpToDegreeConstants h.finalLabel
            (stepDataOfFields c.toChoiceUpToDegreeConstants h.finalLabel n W)
            (domainLargeFieldWithin c.toChoiceUpToDegreeConstants h.finalLabel n X)))
          (fun B => iteratedStepIntegralFrom l W Ψ n (by omega)
            (Function.update A ⟨n, by omega⟩ (v, B)))
        ∂Matrices.ComplexMatrix2.haarPi {b : BondAtLevel c.L m K n //
          b ∈ haarIntegratedBonds c.toChoiceUpToDegreeConstants h.finalLabel n X ∧ b.IsPositivelyOriented}
def lowerStepsProduct (l : ℕ) (hl : l ≤ k) (Y : Set (FourTorus c.L m)) :
    LowerOperation c.L m K where
  Variables := AllStepVariables c x h Y
  integral := fun W Ψ => iteratedStepIntegral c x h Y W Ψ l hl (placeholderVariables c x h Y)
  up := fun A W => fieldsUpwardBelow h Y l A W
  down := fun A V => fieldsDownward c x (stepBasePoints c) τ h Y A l hl V
  factor := fun A V => ∏ j : Fin l,
    operationWeight c x (stepBasePoints c) τ h (lt_of_lt_of_le j.2 hl) Y
      (A ⟨j, lt_of_lt_of_le j.2 hl⟩).2 V
end Product
end PeriodicLattice.CubesOfStep
end YangMills.Construction
