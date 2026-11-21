import YangMills.Construction.SourcesAndGluing.PredicatesOfLatticeSimilarities
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.SourcesAndGluing
def ScaledMotionPlaquettesOfSpaceClaim : Prop :=
  ∀ (S : GluingSetup) (n : ScaleExponent S) (φ : ScaledLatticeMotion n),
    φ.MapsPlaquettesOfSpace
end YangMills.Construction.SourcesAndGluing
end
