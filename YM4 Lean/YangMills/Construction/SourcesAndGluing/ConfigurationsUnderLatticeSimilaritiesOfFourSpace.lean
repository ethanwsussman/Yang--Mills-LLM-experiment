import YangMills.Construction.SourcesAndGluing.PredicatesOfLatticeSimilarities
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.SourcesAndGluing
def FieldsUnderScaledMotionsOfSpace.Statement : Prop :=
  ∀ (D : GluingSetup) (e : ScaleExponent D) (Φ : ScaledLatticeMotion e),
    Φ.PullsFieldsOfSpace
end YangMills.Construction.SourcesAndGluing
end
