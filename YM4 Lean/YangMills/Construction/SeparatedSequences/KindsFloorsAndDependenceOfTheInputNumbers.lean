import YangMills.Construction.Conventions.PositiveConstant
import YangMills.Construction.Dirichlet.ComparedFloorPairs
import YangMills.Construction.SeparatedSequences.NumbersOfTheInputs
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.SeparatedSequences.InputConstants.Properties
structure Params where
  L : ℕ
  odd : Odd L
  thirteen_le : 13 ≤ L
  β : ℝ
  β_nonneg : 0 ≤ β
  β_lt_one : β < 1
  ε : ℝ
  ε_pos : 0 < ε
  ε_le_one : ε ≤ 1
def ValueKinds (L : ℕ) : Prop :=
  (∃ a : ℕ, blockPow L = L ^ a) ∧ (∃ a : ℕ, gapMultiplier L = L ^ a) ∧
    CombinedConstants.blockLower L ≤ (blockPow L : ℝ) ∧
    (L : ℝ) ^ 2 ≤ CombinedConstants.blockLower L ∧
    L ≤ gapMultiplier L ∧
    L ^ 3 ≤ gapLength L ∧
    0 < minimalInputRate L ∧ minimalInputRate L ≤ 1 ∧
    1 ≤ mainBound L ∧
    (∀ β : ℝ, 0 ≤ β → β < 1 → 1 ≤ holderBound L β) ∧
    (∀ ε : ℝ, 0 < ε → ε ≤ 1 → 1 ≤ gradBound L ε) ∧
    ∀ ε β : ℝ, 0 < ε → ε ≤ 1 → 0 ≤ β → β < 1 → 1 ≤ gradHolderBound L ε β
def LowerBounds (L : ℕ) : Prop :=
  CombinedConstants.derivedGapLower L ≤ (gapLength L : ℝ) ∧
    CombinedConstants.gapLower L ≤ CombinedConstants.derivedGapLower L ∧
    16 * (4 * Real.log (L : ℝ) + Real.log 2) ≤ (gapLength L : ℝ) * minimalInputRate L ∧
    Dirichlet.FloorsAtRate 4 (L : ℝ) (Dirichlet.FloorComparison.comparisonRate 4 (L : ℝ))
      (blockPow L : ℝ) (gapMultiplier L : ℝ)
def Dependencies : Prop :=
  Conventions.DependsOnlyThrough (fun x : Params => minimalInputRate x.L) Params.L ∧
    Conventions.DependsOnlyThrough (fun x : Params => blockPow x.L) Params.L ∧
    Conventions.DependsOnlyThrough (fun x : Params => gapMultiplier x.L) Params.L ∧
    Conventions.DependsOnlyThrough (fun x : Params => gapLength x.L) Params.L ∧
    Conventions.DependsOnlyThrough (fun x : Params => mainBound x.L) Params.L ∧
    Conventions.DependsOnlyThrough (fun x : Params => holderBound x.L x.β) (fun x => (x.L, x.β)) ∧
    Conventions.DependsOnlyThrough (fun x : Params => gradBound x.L x.ε) (fun x => (x.L, x.ε)) ∧
    Conventions.DependsOnlyThrough (fun x : Params => gradHolderBound x.L x.ε x.β)
      (fun x => (x.L, x.ε, x.β))
def Statement : Prop :=
  (∀ L : ℕ, Odd L → 13 ≤ L → ValueKinds L ∧ LowerBounds L) ∧ Dependencies
end YangMills.Construction.SeparatedSequences.InputConstants.Properties
