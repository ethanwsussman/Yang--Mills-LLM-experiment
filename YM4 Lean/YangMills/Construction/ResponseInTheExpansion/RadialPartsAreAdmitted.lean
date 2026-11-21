import YangMills.Construction.ResponseInTheExpansion.AdmittedOnOneTorus
import YangMills.Construction.ResponseInTheExpansion.RadialPartIsMajorised
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ResponseInTheExpansion
open BlockAverages ColdStepAtMirrorFrames WeightedResponses
def radialPartsComparableStatement : Prop :=
  EventuallyInParameters fun T => ∀ (t : ℕ) (x : ℝ) (f : LocalFamily), T.coupling ≤ x →
    IsRegularFamily T.L t T.n₀ T.σ T.decayRate T.E T.energyRatio f →
    IsComparableOnOneTorus T t x f (fun _ Y => (coldHalfLawAt T x f).familyTerm Y) ∧
    IsComparableOnOneTorus T t x f (fun _ Y => (coldHalfLawAt T x f).exponentRadialPart Y)
end YangMills.Construction.ResponseInTheExpansion
end
