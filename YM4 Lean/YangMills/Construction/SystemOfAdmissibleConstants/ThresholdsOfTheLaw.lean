import YangMills.Construction.LawInAState.DataOfTheLaw
import YangMills.Construction.ParameterData.FirstExitPathDefs
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.AdmissibleConstants
variable {T : RenormalizationStepParameters.ParameterAssignment} {y : ℝ} (D : TrajectoryData.TrajectoryParameters T y)
def IsDatumAtDistance (g d : ℝ) (K : ℕ) (β : ℝ) : Prop :=
  β ∈ D.passageWindow K g ∧ StateLaws.minimalCutoff (T.stepParameters y) (D.threshold g) d ≤ K
def lowerCouplingEnvelope (g d : ℝ) : ℝ :=
  (g ^ 2)⁻¹ - 2 * D.cH + 3 / 4 * TrajectoryData.logSlope * Real.log (1 / d)
def upperCouplingEnvelope (g d : ℝ) : ℝ :=
  2 * (D.threshold g + 2 * D.cH + 1 +
    5 / 4 * TrajectoryData.logSlope * (Real.log (1 / d) + Real.log (2 ^ 13 * (T.side : ℝ))))
def scaleDepthEnvelope (g d : ℝ) : ℝ :=
  Real.logb T.side
    (2 ^ 13 * (T.side : ℝ) * (TorusLumps.clusterRange (upperCouplingEnvelope D g d) : ℝ) / d)
def driftBound (m : ℝ) : ℝ :=
  2 * D.cH + D.Cr + 8 * D.Md / (3 * D.c₀) *
    Real.log (1 + 3 * D.c₀ * m / (4 * D.X₀))
def heightBound (g d : ℝ) : ℝ :=
  D.threshold g + driftBound D (scaleDepthEnvelope D g d) +
    TrajectoryData.logSlope *
      Real.log (2 ^ 13 * (T.side : ℝ) * (TorusLumps.clusterRange (upperCouplingEnvelope D g d) : ℝ))
def normalizationModulus (Cstar g d : ℝ) : ℝ :=
  6 * Cstar / D.rateBound *
    lowerCouplingEnvelope D g d ^ (-(1 / 2) : ℝ)
def ratioModulus (g d : ℝ) : ℝ :=
  ⨆ d' : Set.Ioc (0 : ℝ) d, heightBound D g d' / lowerCouplingEnvelope D g d'
def combinedModulus (Cstar g d : ℝ) : ℝ :=
  max (normalizationModulus D Cstar g d) (ratioModulus D g d)
def lawError (CL g d : ℝ) : ℝ := CL * lowerCouplingEnvelope D g d ^ (-(1 / 200) : ℝ)
def admissibleDistances (Cstar XL CL g : ℝ) : Set ℝ :=
  {δ | δ ∈ Set.Ioo (0 : ℝ) 1 ∧ ∀ d ∈ Set.Ioc (0 : ℝ) δ,
    combinedModulus D Cstar g d ≤ 1 / 3 ∧ lawError D CL g d ≤ 1 / 2 ∧
      XL ≤ lowerCouplingEnvelope D g d ∧
      (upperCouplingEnvelope D g d ^ ((1 : ℝ) / 27) + 10) * d < 1 / 2}
def distanceCutoff (Cstar XL CL g : ℝ) : ℝ :=
  1 / 2 * sSup (admissibleDistances D Cstar XL CL g)
def leadingTwoPointTerm (d : ℝ) (f h : (Fin 4 → ℝ) → ℝ) : ℝ :=
  3 * (2 ^ 2 - 1) / Real.pi ^ 4 * (12 * Real.pi ^ 2 / (11 * 2 ^ 2)) ^ 2 *
    TestFunctions.inverseEighthKernel f h * (Real.log (1 / d))⁻¹ ^ 2
def lawInterval (η : ℝ) : Set ℝ := Set.Icc (1 / 2 * (1 - η) ^ 4) (3 / 2 * (1 + η) ^ 4)
end YangMills.Construction.AdmissibleConstants
end
