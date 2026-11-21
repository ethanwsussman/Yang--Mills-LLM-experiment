import YangMills.Construction.LawByMomentsOfTheFlow.PointOfTheLaw
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.MomentLaw
def scaleCouplingPosStatement : Prop :=
  ForAllParameters fun Λ => ∀ S : MomentPoint Λ, 0 < S.scaleCoupling
end YangMills.Construction.MomentLaw
end
