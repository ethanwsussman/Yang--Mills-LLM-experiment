import YangMills.Construction.SystemsWithFiveBounds.StatesOfTheWindowForm
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.SystemsWithFiveBounds
def LimitReconstructionProperties : Prop :=
  ∀ {L : ℕ} (hL : YangMills.Construction.Conventions.IsAdmissibleBlockingFactor L)
    (s : YangMills.Construction.Conventions.StandingParameters)
    (T : YangMills.Construction.LimitConventions.ApproxTriple L)
    (σ : YangMills.Construction.SeparatedTuples.TupleFunctional),
    YangMills.Construction.ReflectionPositivity.ApproximatingSequences.LatticeApproximation.IsBoundedForSomeM
      (YangMills.Construction.WindowLimits.unitAxisMirrorData hL) T →
    YangMills.Construction.LimitConventions.ApproxTriple.IsReflPos T →
    YangMills.Construction.LimitConventions.ApproxTriple.ConvergesTo T σ →
    YangMills.Construction.LimitTheorem.ReconstructionProperties σ
end YangMills.Construction.SystemsWithFiveBounds
end
