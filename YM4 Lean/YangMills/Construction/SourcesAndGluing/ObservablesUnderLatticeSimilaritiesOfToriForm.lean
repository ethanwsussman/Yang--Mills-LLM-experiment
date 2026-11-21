import YangMills.Construction.SourcesAndGluing.PredicatesOfLatticeSimilarities
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.SourcesAndGluing
def ScaledMotionObservablesOfToriClaim : Prop :=
  ∀ (S : GluingSetup) (n : ScaleExponent S) (φ : ScaledLatticeMotion n),
    φ.PullsObservablesOfTori ℝ ∧ φ.PullsObservablesOfTori ℂ
end YangMills.Construction.SourcesAndGluing
end
