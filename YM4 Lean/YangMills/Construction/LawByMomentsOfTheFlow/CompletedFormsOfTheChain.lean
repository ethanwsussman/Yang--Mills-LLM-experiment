import YangMills.Construction.LawByMomentsOfTheFlow.GaussianChainOfTheLaw
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace YangMills.Construction
namespace CompletedForms
section Levels
variable {L : ℕ} [NeZero L]
def truncateTop : (j s n : ℕ) → j ≤ s → MomentLaw.LevelChain L s n → MomentLaw.LevelChain L j n
  | 0, s, n, _, X => MomentLaw.chainTop s n X
  | _ + 1, 0, _, h, _ => absurd h (by omega)
  | j + 1, s + 1, n, h, X => fun e =>
      Sum.elim (truncateTop j s (n * L) (Nat.le_of_succ_le_succ h) (MomentLaw.chainLower X) e)
        (MomentLaw.chainTop (s + 1) n X e)
def levelPair : (d s n : ℕ) → d + 1 ≤ s → MomentLaw.LevelChain L s n →
    MomentLaw.ColourForm (WeightedResponses.fineSide L d n) × MomentLaw.ColourForm (WeightedResponses.fineSide L d n * L)
  | _, 0, _, h, _ => absurd h (by omega)
  | 0, s + 1, n, _, X => (MomentLaw.chainTop (s + 1) n X, MomentLaw.chainTop s (n * L) (MomentLaw.chainLower X))
  | d + 1, s + 1, n, h, X => levelPair d s (n * L) (Nat.le_of_succ_le_succ h) (MomentLaw.chainLower X)
def extendChain (a ρA : ℝ) (u : ℕ) : (j n : ℕ) → [NeZero n] → MomentLaw.LevelChain L j n →
    MomentLaw.StepFluctuation L u (WeightedResponses.fineSide L j n) → MomentLaw.LevelChain L (j + 1) n
  | 0, n, _, Z, η => fun e => Sum.elim
      (fun b => MomentLaw.pushColours a ρA L u (MomentLaw.chainTop 0 n Z) e b + MomentLaw.extendFluctuation η e b) (Z e)
  | j + 1, n, _, Z, η => fun e =>
      Sum.elim (extendChain a ρA u j (n * L) (MomentLaw.chainLower Z) η e) (MomentLaw.chainTop (j + 1) n Z e)
def cumulativeScores (a : ℝ) (τ l : ℕ) (w : ∀ m : ℕ, WeightedResponses.PlaquetteWeight m) :
    (j n : ℕ) → [NeZero n] → MomentLaw.LevelChain L j n → ℝ
  | 0, _, _, _ => 0
  | j + 1, n, _, Z => cumulativeScores a τ l w j (n * L) (MomentLaw.chainLower Z) +
      if l + j + 1 ≤ τ then
        a * ∑ c : TorusFields.TorusBond n, ResponseInTheExpansion.bondBlockMean L (l + j + 1) n (w _) c *
          ((1 / 2) * ∑ e : Fin 3, MomentLaw.chainDefect Z e c ^ 2 - 3 / (2 * a))
      else 0
end Levels
def descendForm (Λ : MomentLaw.MomentParameters) (l m : ℕ) [NeZero m] (Z : MomentLaw.ColourForm m)
    (η : MomentLaw.StepFluctuation Λ.stepParams.side l m) : MomentLaw.ColourForm (m * Λ.stepParams.side) := fun e b =>
  MomentLaw.pushColours Λ.stepParams.coupling Λ.table.ρA Λ.stepParams.side l Z e b + MomentLaw.extendFluctuation η e b
end CompletedForms
namespace MomentLaw.MomentPoint
variable {Λ : MomentLaw.MomentParameters} (S : MomentLaw.MomentPoint Λ)
def completedForm (l j n : ℕ) [NeZero n] (i : Fin Λ.k) (Z : MomentLaw.LevelChain Λ.stepParams.side j n) : ℝ :=
  (1 / 2) * MomentLaw.colourEval (S.supportForm l (WeightedResponses.fineSide Λ.stepParams.side j n) i)
      (MomentLaw.chainBottom j n Z) (MomentLaw.chainBottom j n Z) +
    CompletedForms.cumulativeScores Λ.stepParams.coupling S.lastSeparated l (S.weight i) j n Z
def levelStepValue (l m : ℕ) [NeZero m] (i : Fin Λ.k) (Z : MomentLaw.ColourForm m)
    (X : MomentLaw.ColourForm (m * Λ.stepParams.side)) : ℝ :=
  (1 / 2) * MomentLaw.colourEval (S.supportForm l (m * Λ.stepParams.side) i) X X +
    Λ.stepParams.coupling * ∑ c : TorusFields.TorusBond m,
      ResponseInTheExpansion.bondBlockMean Λ.stepParams.side (l + 1) m (S.weight i _) c *
      ((1 / 2) * ∑ e : Fin 3, (Z e c - MomentLaw.contourAverage Λ.stepParams.side (X e) c) ^ 2 -
        3 / (2 * Λ.stepParams.coupling))
open Classical in
def levelStepGradient (l m : ℕ) [NeZero m] (i : Fin Λ.k) (Z : MomentLaw.ColourForm m)
    (X : MomentLaw.ColourForm (m * Λ.stepParams.side))
    (b : Fin 3 × MomentLaw.ChartBondIndex Λ.stepParams.side l m) : ℝ :=
  (1 / 2) * (MomentLaw.colourEval (S.supportForm l (m * Λ.stepParams.side) i) X
        (MomentLaw.extendFluctuation (EuclideanSpace.single b 1)) +
      MomentLaw.colourEval (S.supportForm l (m * Λ.stepParams.side) i)
        (MomentLaw.extendFluctuation (EuclideanSpace.single b 1)) X) -
    Λ.stepParams.coupling * ∑ c : TorusFields.TorusBond m,
      ResponseInTheExpansion.bondBlockMean Λ.stepParams.side (l + 1) m (S.weight i _) c * ∑ e : Fin 3,
      (Z e c - MomentLaw.contourAverage Λ.stepParams.side (X e) c) *
        MomentLaw.contourAverage Λ.stepParams.side (MomentLaw.extendFluctuation (EuclideanSpace.single b 1) e) c
end MomentLaw.MomentPoint
end YangMills.Construction
end
