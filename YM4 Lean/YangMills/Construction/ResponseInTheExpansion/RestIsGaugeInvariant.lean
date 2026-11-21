import YangMills.Construction.ResponseInTheExpansion.DilationOfTheColdLaw
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames WeightedResponses
namespace ResponseInTheExpansion
def DilationRemainderGaugeInvariantAt (T : StepParameters) : Prop :=
  ∀ (t : ℕ) (x : ℝ) (f : LocalFamily) (F : BlockFrame) (V : F.GaugeField F.top) (Y : F.Cell)
    (g : F.Cell → UnitQuaternion),
    IsAdmissibleAt T t x f F V →
      (coldHalfLawAt T x f).dilationRemainder Y (gaugeTransform g V) = (coldHalfLawAt T x f).dilationRemainder Y V
def dilationRemainderGaugeInvariantStatement : Prop := EventuallyInParameters DilationRemainderGaugeInvariantAt
end ResponseInTheExpansion
end YangMills.Construction
end
