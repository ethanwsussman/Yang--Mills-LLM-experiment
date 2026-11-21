import YangMills.Construction.ClusterExpansionOfAStep.ConstantsOfTheColdChain
import YangMills.Construction.ClusterExpansionOfAStep.MarksOfAStep
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
namespace StepFrames
open BlockAverages ColdStepAtMirrorFrames TorusFields TorusLumps StepMarks StepCosts ColdChain
def FrameIsMinimizing (ℓ : StepParameters) (ρA ρ : ℝ) (t m : ℕ) {n : ℕ} (V : TorusField n)
    (b : TorusBond (n * ℓ.side)) : Prop :=
  (4 * m + 5 < n → ∃ w, IsMinimizingChart ℓ.coupling
      (finiteCells (reflectedFrame (torusFrame ℓ.side t n) m))
      (reflectedField m (enclosingCell (torusSiteInFrame (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).depth b.1))
        (readAtLevel (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).top V)) ρ w ∧
      frameCoord ℓ ρA t m V b = w (reflectedBond (F := torusFrame ℓ.side t n) m
        (torusSiteInFrame (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).depth b.1, b.2)).1 b.2) ∧
    (¬ 4 * m + 5 < n → ∃ w, IsMinimizingChart ℓ.coupling (finiteCells (torusFrame ℓ.side t n))
      (readAtLevel (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).top V) ρ w ∧
      frameCoord ℓ ρA t m V b = w (torusSiteInFrame (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).depth b.1) b.2)
def FrameNearMinimizer : Prop :=
  ∀ (ℓ : StepParameters) (δ lam ρA σA cg : ℝ) (N : ℕ → ℝ), ℓ.Admissible →
    ColdChainConstants ℓ.coupling δ ℓ.side lam ρA σA cg N →
    2 * ℓ.threshold ≤ σA →
    IsRangeSuppressed (frameGap (N 0) δ ℓ.threshold) ∧
    ∀ (t r r' n : ℕ) [NeZero n] (V : TorusField n) (S C : Finset (TorusSite n)) (s : ℝ), RangesAdmissible r r' →
      IsStepSituation ℓ r' V S C s → ∀ b ∈ chartBonds ℓ.side n, parentBlock ℓ.side b.1 ∉ C →
        FrameIsMinimizing ℓ ρA (min ρA (N 0 * s)) t (r / 2 ^ 11) V b ∧
        ‖(frameCoord ℓ ρA t (r / 2 ^ 11) V b : ℍ[ℝ]) - (minimizerCoord ℓ.coupling ρA ℓ.side t S V b : ℍ[ℝ])‖ ≤
          N 0 * s * Real.exp (-(δ * ((r / 2 ^ 11 : ℕ) : ℝ)))
end StepFrames
end YangMills.Construction
end
