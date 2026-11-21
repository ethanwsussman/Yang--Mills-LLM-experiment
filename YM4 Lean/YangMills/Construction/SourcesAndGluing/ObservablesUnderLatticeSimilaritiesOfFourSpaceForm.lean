import YangMills.Construction.SourcesAndGluing.PredicatesOfLatticeSimilarities
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.SourcesAndGluing
def ScaledMotionObservablesOfSpaceClaim : Prop :=
  ∀ (S : GluingSetup) (n : ScaleExponent S) (φ : ScaledLatticeMotion n),
    φ.PullsObservablesOfSpace ℝ ∧ φ.PullsObservablesOfSpace ℂ
end YangMills.Construction.SourcesAndGluing
end
