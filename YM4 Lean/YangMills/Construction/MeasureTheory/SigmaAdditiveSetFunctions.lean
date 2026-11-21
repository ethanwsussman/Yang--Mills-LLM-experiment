import Mathlib
set_option autoImplicit false
open MeasureTheory Filter Topology
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.SetFunctions
variable {X : Type*} [MeasurableSpace X]
abbrev MeasurableSets (X : Type*) [MeasurableSpace X] : Type _ :=
  {A : Set X // MeasurableSet A}
def iUnionSets (A : ℕ → MeasurableSets X) : MeasurableSets X :=
  ⟨⋃ j, (A j : Set X), MeasurableSet.iUnion fun j => (A j).2⟩
def PairwiseDisjointSeq (A : ℕ → MeasurableSets X) : Prop :=
  Pairwise fun i j => Disjoint (A i : Set X) (A j : Set X)
def IsCountablyAdditive (ν : MeasurableSets X → ℂ) : Prop :=
  ∀ A : ℕ → MeasurableSets X, PairwiseDisjointSeq A →
    Tendsto (fun N => ∑ j ∈ Finset.range N, ν (A j)) atTop (𝓝 (ν (iUnionSets A)))
abbrev CountablyAdditiveFn (X : Type*) [MeasurableSpace X] : Type _ :=
  {ν : MeasurableSets X → ℂ // IsCountablyAdditive ν}
def variation (ν : MeasurableSets X → ℂ) (A : MeasurableSets X) : ℝ≥0∞ :=
  ⨆ (B : ℕ → MeasurableSets X) (_ : PairwiseDisjointSeq B) (_ : iUnionSets B = A),
    ∑' j, ‖ν (B j)‖ₑ
def IsNonneg (ν : MeasurableSets X → ℂ) : Prop :=
  ∀ A, (ν A).im = 0 ∧ 0 ≤ (ν A).re
def reFn (ν : MeasurableSets X → ℂ) : MeasurableSets X → ℂ :=
  fun A => ((ν A).re : ℂ)
def imFn (ν : MeasurableSets X → ℂ) : MeasurableSets X → ℂ :=
  fun A => ((ν A).im : ℂ)
def posPart (μ : MeasurableSets X → ℂ) : MeasurableSets X → ℂ :=
  fun A => (1 / 2 : ℂ) * (((variation μ A).toReal : ℂ) + μ A)
def negPart (μ : MeasurableSets X → ℂ) : MeasurableSets X → ℂ :=
  fun A => (1 / 2 : ℂ) * (((variation μ A).toReal : ℂ) - μ A)
open Classical in
def toMeasure (m : MeasurableSets X → ℝ≥0∞) : Measure X :=
  if h : m ⟨∅, MeasurableSet.empty⟩ = 0 ∧
      ∀ A : ℕ → MeasurableSets X, PairwiseDisjointSeq A → m (iUnionSets A) = ∑' j, m (A j) then
    Measure.ofMeasurable (fun s hs => m ⟨s, hs⟩) h.1
      fun f hf hd => h.2 (fun j => ⟨f j, hf j⟩) hd
  else 0
def nonnegToMeasure (m : MeasurableSets X → ℂ) : Measure X :=
  toMeasure fun A => ENNReal.ofReal (m A).re
def integralWith (ν : MeasurableSets X → ℂ) (F : X → ℂ) : ℂ :=
  ∫ x, F x ∂(nonnegToMeasure (posPart (reFn ν)))
    - ∫ x, F x ∂(nonnegToMeasure (negPart (reFn ν)))
    + Complex.I * ∫ x, F x ∂(nonnegToMeasure (posPart (imFn ν)))
    - Complex.I * ∫ x, F x ∂(nonnegToMeasure (negPart (imFn ν)))
end YangMills.Construction.SetFunctions
