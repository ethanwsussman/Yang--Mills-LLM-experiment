import YangMills.Construction.ResponseInTheExpansion.DilationOfTheColdLaw
import YangMills.Construction.ResponseInTheExpansion.MeanOfASlotOfOrderTwo
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages YangMills.Construction.ColdStepAtMirrorFrames YangMills.Construction.Interpolation
namespace YangMills.Construction.WeightedResponses
def IsFamilyTermSlotAt (T : StepParameters) (Cq : ℕ → ℝ) (C : ℝ) : Prop :=
  ∀ (t : ℕ) (x : ℝ) (f : LocalFamily) (F : BlockFrame) (V : F.GaugeField F.top) (Y : F.Cell),
    IsAdmissibleAt T t x f F V → IsRegularFamily T.L t T.n₀ T.σ T.decayRate T.E T.energyRatio f →
    IsSecondOrderRemainder T x f Cq C (C * x ^ (-(1 / 2) : ℝ)) Y ((coldHalfLawAt T x f).familyTerm Y) V
def familyTermSlotStatement : Prop :=
  ∃ (Cq : StepParameters → ℕ → ℝ) (C : StepParameters → ℝ), (∀ T q, 0 ≤ Cq T q) ∧ (∀ T, 0 < C T) ∧
    EventuallyInParameters fun T => IsFamilyTermSlotAt T (Cq (parametersBeforeSide T)) (C (parametersBeforeSide T))
end YangMills.Construction.WeightedResponses
end
