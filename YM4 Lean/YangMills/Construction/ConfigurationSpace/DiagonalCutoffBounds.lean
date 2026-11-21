import YangMills.Construction.ConfigurationSpace.DiagonalCutoffs
import YangMills.Construction.Continuum.WhitneyDyadicScales
import YangMills.Construction.Lattice.ObservablesAndTestNorms
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ConfigurationSpace
open BumpFunctions WhitneyScales
def PairCutoffBounds (j : ℕ) : Prop :=
  ofRealFun (pairCutoff j) ∈ smoothSet (Fin 4 → ℝ) ∧
  (∀ y : Fin 4 → ℝ,
    0 ≤ pairCutoff j y ∧ pairCutoff j y ≤ pairCutoff (j + 1) y ∧ pairCutoff (j + 1) y ≤ 1) ∧
  (∀ y : Fin 4 → ℝ, pairCutoff j y = 0 ↔ maxNorm y ≤ whitneyScale j) ∧
  (∀ y : Fin 4 → ℝ, 2 * whitneyScale j ≤ maxNorm y → pairCutoff j y = 1) ∧
  ∀ γ : MultiIdx (Fin 4), γ ≠ 0 → ∀ y : Fin 4 → ℝ,
    ‖multiDeriv γ (ofRealFun (pairCutoff j)) y‖ ≤
      integralConstBound ^ 4 * (blockConst * 2 ^ j) ^ MultiIdx.order γ *
        ((MultiIdx.order γ).factorial : ℝ) ^ 2
def PairCutoffProdBounds (n j : ℕ) : Prop :=
  ofRealFun (pairCutoffProd (n := n) j) ∈ smoothSet (Config n) ∧
  (∀ x : Config n,
    0 ≤ pairCutoffProd j x ∧ pairCutoffProd j x ≤ pairCutoffProd (j + 1) x ∧
      pairCutoffProd (j + 1) x ≤ 1) ∧
  (∀ x : Config n, minSeparation x ≤ ENNReal.ofReal (whitneyScale j) → pairCutoffProd j x = 0) ∧
  (∀ x : Config n, ENNReal.ofReal (2 * whitneyScale j) ≤ minSeparation x →
    pairCutoffProd j x = 1) ∧
  ∀ (α : MultiIdx (CoordIndex n)) (x : Config n),
    ‖configMultiDeriv α (ofRealFun (pairCutoffProd j)) x‖ ≤
      (pairCutoffConst * n * 2 ^ j) ^ MultiIdx.order α *
        ((MultiIdx.order α).factorial : ℝ) ^ 2
def ShellDiffBounds (n j : ℕ) : Prop :=
  (∀ x : Config n, 0 ≤ shellDiff j x) ∧
  (∀ (J : ℕ) (x : Config n),
    ∑ j' ∈ Finset.range (J + 1), shellDiff j' x = pairCutoffProd J x) ∧
  (∀ x ∈ TestFunctions.injectiveTuples (Fin 4 → ℝ) n,
    {j' : ℕ | shellDiff j' x ≠ 0}.Finite ∧ ∑' j' : ℕ, shellDiff j' x = 1) ∧
  (∀ x : Config n, shellDiff j x ≠ 0 →
    ENNReal.ofReal (whitneyScale j) < minSeparation x) ∧
  (∀ x : Config n, shellDiff j x ≠ 0 → 1 ≤ j →
    minSeparation x < ENNReal.ofReal (4 * whitneyScale j)) ∧
  (1 ≤ j → tsupport (shellDiff (n := n) j) ⊆
    {x | ENNReal.ofReal (whitneyScale j) ≤ minSeparation x ∧
      minSeparation x ≤ ENNReal.ofReal (4 * whitneyScale j)}) ∧
  tsupport (shellDiff (n := n) 0) ⊆ {x | ENNReal.ofReal 1 ≤ minSeparation x} ∧
  (∀ x : Config n, {j' : ℕ | x ∈ tsupport (shellDiff (n := n) j')}.encard ≤ 3) ∧
  ∀ (α : MultiIdx (CoordIndex n)) (x : Config n),
    ‖configMultiDeriv α (ofRealFun (shellDiff j)) x‖ ≤
      2 * (pairCutoffConst * n * 2 ^ j) ^ MultiIdx.order α *
        ((MultiIdx.order α).factorial : ℝ) ^ 2
def DiagonalCutoffProperties : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ j : ℕ,
    PairCutoffBounds j ∧ PairCutoffProdBounds n j ∧ ShellDiffBounds n j
end YangMills.Construction.ConfigurationSpace
end
