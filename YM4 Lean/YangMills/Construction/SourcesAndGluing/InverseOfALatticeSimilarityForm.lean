import YangMills.Construction.SourcesAndGluing.PredicatesOfLatticeSimilarities
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.SourcesAndGluing
def ScaledMotionInverseClaim : Prop :=
  ∀ (S : GluingSetup) (n : ScaleExponent S) (φ : ScaledLatticeMotion n),
    φ.InvIsScaledMotion
end YangMills.Construction.SourcesAndGluing
end
