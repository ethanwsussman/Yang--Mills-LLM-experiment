import YangMills.Construction.ClusterExpansionOfAStep.ConstantsOfTheColdChain
import YangMills.Construction.ClusterExpansionOfAStep.MarksOfAStep
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
namespace StepFrames
open BlockAverages ColdStepAtMirrorFrames TorusFields TorusLumps StepMarks StepCosts ColdChain
def FrameCovariance : Prop :=
  ∀ (ℓ : StepParameters) (δ lam ρA σA cg : ℝ) (N : ℕ → ℝ), ℓ.Admissible →
    ColdChainConstants ℓ.coupling δ ℓ.side lam ρA σA cg N →
    2 * ℓ.threshold ≤ σA →
    ∀ (t r r' n : ℕ) [NeZero n] (V : TorusField n) (S C : Finset (TorusSite n)) (s : ℝ), RangesAdmissible r r' →
      IsStepSituation ℓ r' V S C s → ∀ b ∈ chartBonds ℓ.side n, parentBlock ℓ.side b.1 ∉ C →
        (∀ g : TorusSite n → UnitQuaternion, (frameCoord ℓ ρA t (r / 2 ^ 11) (gaugeTransform g V) b : ℍ[ℝ]) =
          (g (parentBlock ℓ.side b.1) : ℍ[ℝ]) * (frameCoord ℓ ρA t (r / 2 ^ 11) V b : ℍ[ℝ]) *
            (((g (parentBlock ℓ.side b.1))⁻¹ : UnitQuaternion) : ℍ[ℝ])) ∧
        ∀ u : Fin 4 → ℤ, frameCoord ℓ ρA t (r / 2 ^ 11) (TorusFields.translate (siteOfInt u) V)
            (b.1 - siteOfInt (fun i => (ℓ.side : ℤ) * u i), b.2) = frameCoord ℓ ρA t (r / 2 ^ 11) V b
end StepFrames
end YangMills.Construction
end
