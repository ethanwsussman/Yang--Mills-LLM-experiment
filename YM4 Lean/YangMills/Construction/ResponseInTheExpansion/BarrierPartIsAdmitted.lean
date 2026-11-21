import YangMills.Construction.ResponseInTheExpansion.AdmittedOnOneTorus
import YangMills.Construction.ResponseInTheExpansion.DilationOfTheColdLaw
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ResponseInTheExpansion
open ColdStepAtMirrorFrames
def CutoffTermComparable : Prop :=
  EventuallyInParameters fun T => ∀ (t : ℕ) (x : ℝ) (f : LocalFamily), T.coupling ≤ x →
    IsRegularFamily T.L t T.n₀ T.σ T.decayRate T.E T.energyRatio f →
    IsComparableOnOneTorus T t x f fun _ Y => (WeightedResponses.coldHalfLawAt T x f).cutoffTerm Y
end YangMills.Construction.ResponseInTheExpansion
end
