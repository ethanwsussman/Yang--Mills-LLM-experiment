import YangMills.Construction.SystemOfAdmissibleConstants.TheLawAtALevel
import Mathlib
set_option autoImplicit false
open Filter
open scoped Topology
noncomputable section
namespace YangMills.Construction.SystemOfAdmissibleConstants
open RenormalizationStepParameters TrajectoryData WeightedResponses ResponseInTheExpansion AdmissibleConstants
open InfiniteLattice (periodicGibbsSet smearedEnergyCumulant)
variable {T : ParameterAssignment} {y : ℝ}
structure ThresholdEstimates (D : TrajectoryParameters T y) (R : ResponseParameters) (g θ X C : ℝ) : Prop where
  pos : 0 < distanceCutoff D R.Cstar X C g
  lt_one : distanceCutoff D R.Cstar X C g < 1
  modulus_mem : ∀ d ∈ Set.Ioc 0 (distanceCutoff D R.Cstar X C g),
    0 ≤ combinedModulus D R.Cstar g d ∧ combinedModulus D R.Cstar g d ≤ 1 / 3
  modulus_monotoneOn : MonotoneOn (combinedModulus D R.Cstar g) (Set.Ioc 0 (distanceCutoff D R.Cstar X C g))
  modulus_tendsto : Tendsto (combinedModulus D R.Cstar g) (𝓝[>] 0) (𝓝 0)
  twoPoint : ∀ d ∈ Set.Ioc 0 (distanceCutoff D R.Cstar X C g), ∀ (K : ℕ+) (β : ℝ),
    IsDatumAtDistance D g d K β →
    lawError D C g d ≤ 1 / 2 ∧
    |logSlope * (D.coupling β (StateLaws.separationLevel (T.stepParameters y) β K d))⁻¹ * Real.log (1 / d) - 1| ≤
      combinedModulus D R.Cstar g d ∧
    (∃ c : ℕ → ℝ, IsChainResponseCoeff (T.stepParameters y) R β (StateLaws.separationLevel (T.stepParameters y) β K d) c ∧
      |c (StateLaws.separationLevel (T.stepParameters y) β K d) - 1| ≤ combinedModulus D R.Cstar g d ∧
      ∀ ν ∈ periodicGibbsSet T.side K β, ∀ p ∈ TestFunctions.separatedPairsR4 d θ,
        ∃ ε : ℝ, |ε| ≤ lawError D C g d ∧
          smearedEnergyCumulant ν ![p.1, p.2] =
            ((c (StateLaws.separationLevel (T.stepParameters y) β K d) ^ 2 * (9 / Real.pi ^ 4) *
              (D.coupling β (StateLaws.separationLevel (T.stepParameters y) β K d) ^ 2)⁻¹ *
                TestFunctions.inverseEighthKernel p.1 p.2 * (1 + ε) : ℝ) : ℂ)) ∧
    ∀ ν ∈ periodicGibbsSet T.side K β, ∀ p ∈ TestFunctions.separatedPairsR4 d θ,
      ∃ t : ℝ, t ∈ lawInterval (combinedModulus D R.Cstar g d) ∧
        |t - 1| ≤ (1 + lawError D C g d) * (1 + combinedModulus D R.Cstar g d) ^ 4 - 1 ∧
        smearedEnergyCumulant ν ![p.1, p.2] = ((leadingTwoPointTerm d p.1 p.2 * t : ℝ) : ℂ)
def thresholdsStatement : Prop :=
  HoldsOnParameterFamilies fun T y => ∃ R : ResponseParameters, R.Admissible (T.stepParameters y) ∧
    ∀ D : TrajectoryParameters T y, D.Admissible → ∀ g : ℝ, 0 < g → inverseCouplingFloor D ≤ g ^ (-2 : ℤ) →
      ∀ θ : ℝ, 0 < θ → θ ≤ 1 →
        ∃ X C : ℝ, 1 ≤ X ∧ 0 ≤ C ∧ couplingLawAt D R g θ X C ∧
          ThresholdEstimates D R g θ X C
end YangMills.Construction.SystemOfAdmissibleConstants
end
