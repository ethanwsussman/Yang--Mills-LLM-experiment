import YangMills.Construction.ClusterExpansionOfAStep.ParametersOfARenormalizationStep
import YangMills.Construction.LawOnABoxOfTheFlow.BoxDefs
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Quaternion
namespace YangMills.Construction
namespace BoxGaussian
open TorusFields RenormalizationStepParameters BlockAverages ResponseInTheExpansion
def cubeHessianStatement : Prop :=
  ∀ Tb : ParameterAssignment, Tb.Admissible → ∃ (CQ : ℝ) (R₀ : ℕ), 1 ≤ CQ ∧
    ∀ (k n : ℕ) [NeZero n] (o : TorusSite n) (R : ℕ), R₀ ≤ R → 16 * R < n →
      actionAtLevel Tb.coupling Tb.side k (supBall o (2 * R)) (trivialField n) = 0 ∧
      (∀ (j : ℕ) (c : Fin j → TorusBond n) (X : Fin j → imaginaryQuaternions),
        ContDiffAt ℝ 2 (fun t : Fin j → ℝ => actionAtLevel Tb.coupling Tb.side k (supBall o (2 * R)) (perturb c X t (trivialField n))) 0) ∧
      (∀ u v : TorusBond n → imaginaryQuaternions, hessianForm Tb.coupling Tb.side k (supBall o (2 * R)) u v =
        hessianForm Tb.coupling Tb.side k (supBall o (2 * R)) v u) ∧
      (∀ (c : ℝ) (u u' v : TorusBond n → imaginaryQuaternions), hessianForm Tb.coupling Tb.side k (supBall o (2 * R)) (c • u + u') v =
        c * hessianForm Tb.coupling Tb.side k (supBall o (2 * R)) u v + hessianForm Tb.coupling Tb.side k (supBall o (2 * R)) u' v) ∧
      (∀ v : TorusBond n → imaginaryQuaternions,
        2 * Tb.coercivity * curlNormSq (supBall o (2 * R)) v ≤ hessianForm Tb.coupling Tb.side k (supBall o (2 * R)) v v ∧
        hessianForm Tb.coupling Tb.side k (supBall o (2 * R)) v v ≤ CQ * curlNormSq (supBall o (2 * R)) v) ∧
      (∀ (φ : TorusSite n → imaginaryQuaternions) (v : TorusBond n → imaginaryQuaternions),
        hessianForm Tb.coupling Tb.side k (supBall o (2 * R)) (latticeGrad φ) v = 0) ∧
      ∀ u v : TorusBond n → imaginaryQuaternions, hessianForm Tb.coupling Tb.side k (supBall o (2 * R)) u v =
        ∑ e : Fin 3, ∑ b : TorusBond n, ∑ b' : TorusBond n,
          mixedDeriv (actionAtLevel Tb.coupling Tb.side k (supBall o (2 * R))) (trivialField n) ![b, b'] ![imaginaryUnitI, imaginaryUnitI] *
            imaginaryComponent e (u b) * imaginaryComponent e (v b')
end BoxGaussian
end YangMills.Construction
end
