import YangMills.Construction.SummableBoundsOfTheFlow.CumulantsWithTheirConstantsForm
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace Cumulants
open ColdStepAtMirrorFrames
variable {ι : Type} [Fintype ι]
def ballThirdCumulant (r : ℝ → ℝ) (Ψ f g h : BondField ι → ℝ) : ℝ :=
  ballExpectation r Ψ (fun η => f η * g η * h η) -
    ballExpectation r Ψ (fun η => f η * g η) * ballExpectation r Ψ h -
    ballExpectation r Ψ (fun η => f η * h η) * ballExpectation r Ψ g -
    ballExpectation r Ψ (fun η => g η * h η) * ballExpectation r Ψ f +
    2 * (ballExpectation r Ψ f * ballExpectation r Ψ g * ballExpectation r Ψ h)
def ballFourthCumulant (r : ℝ → ℝ) (Ψ f g h l : BondField ι → ℝ) : ℝ :=
  ballExpectation r Ψ (fun η => f η * g η * h η * l η) -
    ballExpectation r Ψ (fun η => f η * g η * h η) * ballExpectation r Ψ l -
    ballExpectation r Ψ (fun η => f η * g η * l η) * ballExpectation r Ψ h -
    ballExpectation r Ψ (fun η => f η * h η * l η) * ballExpectation r Ψ g -
    ballExpectation r Ψ (fun η => g η * h η * l η) * ballExpectation r Ψ f -
    ballExpectation r Ψ (fun η => f η * g η) * ballExpectation r Ψ (fun η => h η * l η) -
    ballExpectation r Ψ (fun η => f η * h η) * ballExpectation r Ψ (fun η => g η * l η) -
    ballExpectation r Ψ (fun η => f η * l η) * ballExpectation r Ψ (fun η => g η * h η) +
    2 * (ballExpectation r Ψ (fun η => f η * g η) * ballExpectation r Ψ h * ballExpectation r Ψ l +
      ballExpectation r Ψ (fun η => f η * h η) * ballExpectation r Ψ g * ballExpectation r Ψ l +
      ballExpectation r Ψ (fun η => f η * l η) * ballExpectation r Ψ g * ballExpectation r Ψ h +
      ballExpectation r Ψ (fun η => g η * h η) * ballExpectation r Ψ f * ballExpectation r Ψ l +
      ballExpectation r Ψ (fun η => g η * l η) * ballExpectation r Ψ f * ballExpectation r Ψ h +
      ballExpectation r Ψ (fun η => h η * l η) * ballExpectation r Ψ f * ballExpectation r Ψ g) -
    6 * (ballExpectation r Ψ f * ballExpectation r Ψ g * ballExpectation r Ψ h * ballExpectation r Ψ l)
def lowOrderCumulantFormulas : Prop :=
  ∀ (ι : Type) [Fintype ι] (r : ℝ → ℝ) (Ψ : BondField ι → ℝ),
    (∀ H : Fin 2 → BondField ι → ℝ, cumulantFromMoments r Ψ H = ballCovariance r Ψ (H 0) (H 1)) ∧
    (∀ H : Fin 3 → BondField ι → ℝ,
      cumulantFromMoments r Ψ H = ballThirdCumulant r Ψ (H 0) (H 1) (H 2)) ∧
    ∀ H : Fin 4 → BondField ι → ℝ,
      cumulantFromMoments r Ψ H = ballFourthCumulant r Ψ (H 0) (H 1) (H 2) (H 3)
end Cumulants
end YangMills.Construction
end
