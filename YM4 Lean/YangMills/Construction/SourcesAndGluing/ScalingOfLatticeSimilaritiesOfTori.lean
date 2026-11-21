import YangMills.Construction.SourcesAndGluing.PredicatesOfLatticeSimilarities
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.SourcesAndGluing
def TorusDilationOfScaledMotions.Statement : Prop :=
  ∀ (S : GluingSetup) (e : ScaleExponent S) (Φ : ScaledLatticeMotion e),
    Φ.IsDilatingBijectionOfTori
end YangMills.Construction.SourcesAndGluing
end
