import YangMills.Construction.SourcesAndGluing.PredicatesOfSimilaritiesOfLattices
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.SourcesAndGluing
def RescalingNormalizesOriginClaim : Prop :=
  ∀ (D : GluingSetup) (g : CubicGrid D) (hg : g.IsMirrorGrid), MovesToNormalizedOrigin g hg
end YangMills.Construction.SourcesAndGluing
end
