import YangMills.Construction.ClusterExpansionOfAStep.FramesOfAStep
import YangMills.Construction.ClusterExpansionOfAStep.MarksOfAStep
import YangMills.Construction.ClusterExpansionOfAStep.TranslationsCarryTheKernelAtBases
import YangMills.Construction.ResponseInTheExpansion.StatesAlongTheChain
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.CellWindows
open TorusFields TorusLumps StepSettings StepMarks BaseTranslations WeightedResponses
def translateBonds {m : ℕ} [NeZero m] (a : TorusSite m) (B : Finset (TorusBond m)) :
    Finset (TorusBond m) :=
  open Classical in B.image fun c => (c.1 - a, c.2)
def translateOutcome {ℓ : TorusLumps.StepParameters} {n : ℕ} [NeZero n] (v : Fin 4 → ℤ)
    (o : StepOutcome ℓ n) : StepOutcome ℓ n :=
  (translateBases v o.1, TorusFields.translate (siteOfInt v) o.2.1,
    translateBonds (siteOfInt fun i => (ℓ.side : ℤ) * v i) o.2.2)
def translationPreservesOutcomeDensityStatement : Prop :=
  ∀ R : StepSetup, R.params.Admissible → R.ColdChainFits → RangesAdmissible R.range R.nextRange →
    ∀ (n : ℕ) [NeZero n], IsBlockTorusSide R.params n →
    ∀ (w : Fin 4 → ℤ) (W : TorusField (n * R.params.side)) (o : StepOutcome R.params n),
      stepOutcomeDensity R
          (TorusFields.translate (siteOfInt fun i => (R.params.side : ℤ) * ((R.params.side : ℤ) * w i)) W)
          (translateOutcome (fun i => (R.params.side : ℤ) * w i) o) =
        stepOutcomeDensity R W o
end YangMills.Construction.CellWindows
end
