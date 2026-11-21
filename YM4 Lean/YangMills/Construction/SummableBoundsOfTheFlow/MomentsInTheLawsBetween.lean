import YangMills.Construction.SummableBoundsOfTheFlow.PropertiesOfIntermediateFrames
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames
namespace Interpolation
def momentParameters (P : StepParameters) : StepParameters :=
  { P with Cs := 0, E := 0, n₀ := 0, CE := 0, coupling := 0 }
def intermediateLawMoments : Prop :=
  ∃ (Cq : StepParameters → ℕ → ℝ) (Cr : StepParameters → ℕ → ℕ → ℕ → ℝ),
    EventuallyInParameters fun P => ∀ (t : ℕ) (x : ℝ), P.coupling ≤ x →
      ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (d : ι → ι → ℝ)
        (n : ℕ) (w : Fin n → ℝ) (M : Fin n → LawOnBondVariables ι), IsConvexWeights w →
        (∀ l, (M l).IsAdmissible P.a P.chainParams.ρA P.chainParams.lam x P.σ P.decayRate P.E P.energyRatio
          P.L t P.n₀ (frameRadius x) d) →
        LawMomentBounds P.ballRadius x P.κ P.Cs P.p (Cq (momentParameters P)) (Cr (momentParameters P)) d
          (convexCombinationExponent P.chainParams.lam x w M)
end Interpolation
end YangMills.Construction
end
