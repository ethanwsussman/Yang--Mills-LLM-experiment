import YangMills.Construction.SummableBoundsOfTheFlow.ScaledVariablesOfTheStep
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames
namespace ScaledVariables
def RescaledTermsEven : Prop :=
  ∀ (F : BlockFrame) (a ρ lam : ℝ) (f : LocalFamily) (p : ℝ → ℝ) (ν l : ℝ) (Y : F.Cell)
    (V : F.GaugeField F.top) (ζ : StepVariable (finiteCells F)),
    rescaledCellTerm a ρ (-l) Y V (-ζ) = rescaledCellTerm a ρ l Y V ζ ∧
    rescaledExponent a ρ f ν (-l) V (-ζ) = rescaledExponent a ρ f ν l V ζ ∧
    rescaledEnergy a ρ p f ν (-l) V (-ζ) = rescaledEnergy a ρ p f ν l V ζ ∧
    rescaledCellRemainder a ρ lam (-l) Y V (-ζ) = rescaledCellRemainder a ρ lam l Y V ζ ∧
    rescaledCellExpansion a ρ f (-l) Y V (-ζ) = rescaledCellExpansion a ρ f l Y V ζ
end ScaledVariables
end YangMills.Construction
end
