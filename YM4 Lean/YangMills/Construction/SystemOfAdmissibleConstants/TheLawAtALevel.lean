import YangMills.Construction.InfiniteLattice.GeneratingFunctionsAndConnectedFunctionsOfAMeasureAndOfATorus
import YangMills.Construction.SystemOfAdmissibleConstants.AdmissibleSideLengths
import YangMills.Construction.SystemOfAdmissibleConstants.ThresholdsOfTheLaw
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.SystemOfAdmissibleConstants
open InfiniteLattice (periodicGibbsSet smearedEnergyCumulant)
variable {T : RenormalizationStepParameters.ParameterAssignment} {y : ℝ}
def couplingLawAt (D : TrajectoryData.TrajectoryParameters T y) (Kr : WeightedResponses.ResponseParameters)
    (g vt XL CL : ℝ) : Prop :=
  ∀ d : ℝ, 0 < d → d < 1 → ∀ (K : ℕ+) (β : ℝ), AdmissibleConstants.IsDatumAtDistance D g d K β →
    XL ≤ D.coupling β (StateLaws.separationLevel (T.stepParameters y) β K d) →
    (D.coupling β (StateLaws.separationLevel (T.stepParameters y) β K d) ^ ((1 : ℝ) / 27) + 10) * d
      < 1 / 2 →
    ∀ al : ℕ → ℝ, ResponseInTheExpansion.IsChainResponseCoeff (T.stepParameters y) Kr β
        (StateLaws.separationLevel (T.stepParameters y) β K d) al →
      (∀ ν ∈ periodicGibbsSet T.side K β, ∀ p ∈ TestFunctions.separatedPairsR4 d vt,
        ∃ ε : ℝ, |ε| ≤ CL * D.coupling β (StateLaws.separationLevel (T.stepParameters y) β K d) ^
            (-(1 / 200) : ℝ) ∧
          smearedEnergyCumulant ν ![p.1, p.2] =
            ((al (StateLaws.separationLevel (T.stepParameters y) β K d) ^ 2 * (9 / Real.pi ^ 4) *
              (D.coupling β (StateLaws.separationLevel (T.stepParameters y) β K d) ^ 2)⁻¹ *
                TestFunctions.inverseEighthKernel p.1 p.2 * (1 + ε) : ℝ) : ℂ)) ∧
      (∀ m : ℕ, ∀ p ∈ TestFunctions.separatedPairsFourTorus T.side m d vt,
        ∃ ε : ℝ, |ε| ≤ CL * D.coupling β (StateLaws.separationLevel (T.stepParameters y) β K d) ^
            (-(1 / 200) : ℝ) ∧
          PeriodicLattice.torusUrsellFunction T.side m K β ![p.1, p.2] =
            ((al (StateLaws.separationLevel (T.stepParameters y) β K d) ^ 2 * (9 / Real.pi ^ 4) *
              (D.coupling β (StateLaws.separationLevel (T.stepParameters y) β K d) ^ 2)⁻¹ *
                TestFunctions.inverseEighthKernelTorus p.1 p.2 * (1 + ε) : ℝ) : ℂ))
def levelLawStatement : Prop :=
  FreeEnergies.AtResponseParameters fun T Kr y => Kr.Admissible (T.stepParameters y) →
    ∀ D : TrajectoryData.TrajectoryParameters T y, D.Admissible → ∀ g : ℝ, 0 < g →
      inverseCouplingFloor D ≤ g ^ (-2 : ℤ) →
      ∀ vt : ℝ, 0 < vt → vt ≤ 1 → ∃ XL CL : ℝ, 1 ≤ XL ∧ 0 ≤ CL ∧ couplingLawAt D Kr g vt XL CL
end YangMills.Construction.SystemOfAdmissibleConstants
end
