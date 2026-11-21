import YangMills.Construction.SummableBoundsOfTheFlow.FromTheMirrorFramesToTheLeastField
import YangMills.Construction.SummableBoundsOfTheFlow.ReferenceAtParameters
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Interpolation
open BlockAverages ColdStepAtMirrorFrames TorusFields
def coldActionWeight (a : ℝ) (L t : ℕ) (x : ℝ) : TorusLumps.TorusFunctional := fun n W =>
  if h : n = 0 then 0 else
    haveI : NeZero n := ⟨h⟩
    Real.exp (-x * actionAtLevel a L t Finset.univ W)
def coldStepIntegral (ℓ : TorusLumps.StepParameters) (t : ℕ) (x : ℝ) (n : ℕ) [NeZero n] (V : TorusField n) : ℝ :=
  ∫ W : TorusField (n * ℓ.side), Set.indicator {W' : TorusField (n * ℓ.side) | IsCold ℓ.threshold W'} (fun W' =>
    coldActionWeight ℓ.coupling ℓ.side t x (n * ℓ.side) W' *
      TorusLumps.averagedKernel ℓ x (readAtLevel (TorusLumps.stepBlockFrame ℓ.side n) 0 W')
        (readAtLevel (TorusLumps.stepBlockFrame ℓ.side n) 1 V)) W
    ∂(fieldHaar (n * ℓ.side))
def ColdStepLaplaceAsymptotics : Prop :=
  EventuallyOrdered fun T => ∀ ℓ : TorusLumps.StepParameters, T.Compatible ℓ → ℓ.Admissible →
    ∀ (t n : ℕ) [NeZero n], T.n₀ ≤ n →
    ∃ c : ℝ → ℝ, ∀ V : TorusField n, IsCold ℓ.threshold V →
      Filter.Tendsto (fun x => Real.log (coldStepIntegral ℓ t x n V) -
          Real.log (interpolatedStepIntegral 0 T.a T.ρA T.ballRadius x 0 T.p (localFamilyOfDensity 0)
            (readAtLevel (torusFrame T.L t n) (torusFrame T.L t n).top V)) - c x)
        Filter.atTop (nhds 0)
end YangMills.Construction.Interpolation
end
