import YangMills.Construction.EuclideanFunctionals.BoundsAndContinuityOfTheMoments
import YangMills.Construction.EuclideanFunctionals.RulesOfMotionsConcatenationAndComplexEntries
import YangMills.Construction.EuclideanFunctionals.StandingDataOfTheStudyFromOneInsertionToPlates
import Mathlib
set_option autoImplicit false
open Filter Topology MeasureTheory
open scoped ComplexConjugate Pointwise
noncomputable section
namespace YangMills.Construction.EuclideanFunctionals.InsertionForm
structure FnListSum where
  len : ℕ
  coeff : Fin len → ℂ
  list : Fin len → FnList
def FnListSum.eval (s : FnListSum) : FreeSep :=
  ∑ i, s.coeff i • toFree (s.list i)
def FnListSum.ListsIn (s : FnListSum) (O : Set R4) : Prop :=
  ∀ i, s.list i ∈ sepIn O
theorem exists_fnListSum_eval_eq {O : Set R4} {F : FreeSep} (hF : F ∈ finCombIn O) :
    ∃ s : FnListSum, s.ListsIn O ∧ s.eval = F := by
  classical
  have hmem : ∀ X ∈ F.support, X.1 ∈ sepIn O := fun X hX =>
    (Finsupp.mem_supported ℂ F).1 hF hX
  refine ⟨⟨F.support.card, fun i => F (F.support.equivFin.symm i).1,
    fun i => (F.support.equivFin.symm i).1.1⟩, fun i => hmem _ (F.support.equivFin.symm i).2, ?_⟩
  simp only [FnListSum.eval]
  rw [Equiv.sum_comp F.support.equivFin.symm
    (fun X : F.support => F X.1 • toFree X.1.1), Finset.sum_coe_sort F.support
    (fun X => F X • toFree X.1)]
  conv_rhs => rw [← Finsupp.sum_single F]
  refine Finset.sum_congr rfl fun X _ => ?_
  rw [toFree_of_mem X.2, Finsupp.smul_single, smul_eq_mul, mul_one]
def ofRealFn (f : R4 → ℝ) : R4 → ℂ := fun x => (f x : ℂ)
def termFns (X Y : FnList) (h : R4 → ℂ) : List (R4 → ℂ) :=
  X.map (fun f => ofRealFn (timeFlip.actFn f)) ++ h :: Y.map ofRealFn
def termMoment (S : ConnFamily) (X Y : FnList) (h : R4 → ℂ) : ℂ :=
  Moments.momentAt S (termFns X Y h).get
def IsSlabInsert (c : ℝ) (h : R4 → ℂ) : Prop :=
  h ∈ C1c ℂ ∧ supp h ⊆ timeSlab c
structure TermEntriesSpec (c : ℝ) (X Y : FnList) (h : R4 → ℂ) : Prop where
  complexFamily : ComplexComponents (termFns X Y h).get
  isCompact_supp : ∀ l, IsCompact (supp ((termFns X Y h).get l))
  flipped_supp : ∀ f ∈ X, supp (timeFlip.actFn f) ⊆ lowerHalf (-c)
  insert_supp : supp h ⊆ timeSlab c
  upper_supp : ∀ g ∈ Y, supp g ⊆ upperOpenHalf c
def ExpansionHolds (S : ConnFamily) (c : ℝ) (F A : FreeSep) : Prop :=
  ∀ s t : FnListSum, s.ListsIn (upperOpenHalf c) → t.ListsIn (upperOpenHalf c) →
    s.eval = F → t.eval = A → ∀ h, IsSlabInsert c h →
      insertion S F h A =
        (∑ i, ∑ j, conj (s.coeff i) * t.coeff j *
          termMoment S (s.list i) (t.list j) h) ∧
      (∀ i j, TermEntriesSpec c (s.list i) (t.list j) h) ∧
      ∀ i j, s.list i = [] → t.list j = [] → termMoment S (s.list i) (t.list j) h = 0
def LinearInInsert (S : ConnFamily) (c : ℝ) (F A : FreeSep) : Prop :=
  IsSlabInsert c 0 ∧
    ∀ (a b : ℂ) (h h' : R4 → ℂ), IsSlabInsert c h → IsSlabInsert c h' →
      IsSlabInsert c (a • h + b • h') ∧
        insertion S F (a • h + b • h') A =
          a * insertion S F h A + b * insertion S F h' A
def TranslationCovariance (S : ConnFamily) (c : ℝ) (F A : FreeSep) : Prop :=
  ∀ (x : R4) (c' : ℝ), 0 < c' → c' ≤ c - |x 3| → ∀ k, IsSlabInsert c' k →
    supp (MotionMulRules.shiftFn x k) ⊆ timeSlab c ∧
    MotionMulRules.shiftFree (-timeFlip x) F ∈ finCombIn (upperOpenHalf c') ∧
    MotionMulRules.shiftFree (-x) A ∈ finCombIn (upperOpenHalf c') ∧
    insertion S F (MotionMulRules.shiftFn x k) A =
      insertion S (MotionMulRules.shiftFree (-timeFlip x) F) k (MotionMulRules.shiftFree (-x) A)
def SharpBoundOn (M : SharpScale) (S : ConnFamily) (F A : FreeSep) (Q : Set R4) (B : ℝ) : Prop :=
  ∀ h ∈ C1c ℂ, supp h ⊆ Q → ‖insertion S F h A‖ ≤ B * M.sharpNorm h
def IsUniformBoundConst (M : SharpScale) (C : ℕ → ℝ → ℝ → ℝ) (s t : FnListSum) (Q : Set R4)
    (B : ℝ) : Prop :=
  0 ≤ B ∧
    ∀ (S : ConnFamily) (σ : EuclidFunctionalWithRecon M S), σ.clusterConst = C →
      ∀ c : ℝ, 0 < c → s.ListsIn (upperOpenHalf c) → t.ListsIn (upperOpenHalf c) → IsCompact Q →
        Q ⊆ timeSlab c → SharpBoundOn M S s.eval t.eval Q B
def uniformBoundConst (M : SharpScale) (C : ℕ → ℝ → ℝ → ℝ) (s t : FnListSum) (Q : Set R4) : ℝ :=
  Classical.epsilon (IsUniformBoundConst M C s t Q)
def CompactSetBound {M : SharpScale} {S : ConnFamily} (σ : EuclidFunctionalWithRecon M S)
    (c : ℝ) (F A : FreeSep) : Prop :=
  ∀ s t : FnListSum, s.ListsIn (upperOpenHalf c) → t.ListsIn (upperOpenHalf c) →
    s.eval = F → t.eval = A → ∀ Q : Set R4, IsCompact Q → Q ⊆ timeSlab c →
      IsUniformBoundConst M σ.clusterConst s t Q (uniformBoundConst M σ.clusterConst s t Q)
def ContinuousUnderC1 (S : ConnFamily) (c : ℝ) (F A : FreeSep) : Prop :=
  ∀ Q : Set R4, IsCompact Q → Q ⊆ timeSlab c →
    ∀ (hs : ℕ → R4 → ℂ) (h : R4 → ℂ),
      (∀ j, 1 ≤ j → hs j ∈ C1c ℂ ∧ supp (hs j) ⊆ Q) →
      h ∈ C1c ℂ → supp h ⊆ Q → TendstoC1 hs h →
      Tendsto (fun j => insertion S F (hs j) A) atTop (𝓝 (insertion S F h A))
def SmearingFormula (S : ConnFamily) (c : ℝ) (F A : FreeSep) : Prop :=
  ∀ φ k : R4 → ℂ, Continuous φ → HasCompactSupport φ → k ∈ C1c ℂ →
    supp φ + supp k ⊆ timeSlab c →
    conv φ k ∈ C1c ℂ ∧
    supp (conv φ k) ⊆ supp φ + supp k ∧
    (∀ x ∈ supp φ, IsSlabInsert c (MotionMulRules.shiftFn x k)) ∧
    ContinuousOn (fun x => insertion S F (MotionMulRules.shiftFn x k) A) (supp φ) ∧
    insertion S F (conv φ k) A =
      ∫ x in supp φ, φ x * insertion S F (MotionMulRules.shiftFn x k) A
def InsertionFormTheorem : Prop :=
  ∀ (M : SharpScale) (S : ConnFamily) (σ : EuclidFunctionalWithRecon M S) (c : ℝ), 0 < c →
    ∀ F ∈ finCombIn (upperOpenHalf c), ∀ A ∈ finCombIn (upperOpenHalf c),
      ExpansionHolds S c F A ∧ LinearInInsert S c F A ∧ TranslationCovariance S c F A ∧
        CompactSetBound σ c F A ∧ ContinuousUnderC1 S c F A ∧ SmearingFormula S c F A
end YangMills.Construction.EuclideanFunctionals.InsertionForm
