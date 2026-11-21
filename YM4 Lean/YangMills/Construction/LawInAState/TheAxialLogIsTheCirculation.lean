import YangMills.Construction.ClusterExpansionOfAStep.SecondOrderAtAbelianFields
import YangMills.Construction.ColdChainAtEveryLevel.CriticalChainsOfTurnedTops
import YangMills.Construction.LawInAState.AxialFormsOnTheLattice
import YangMills.Construction.ResponseInTheExpansion.CurvatureOfALevelOnTheDraws
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.AxialLogarithm
variable {n : ℕ}
structure IsSmallOnBall [NeZero n] (W : TorusFields.TorusField n) (g : TorusFields.TorusSite n → BlockAverages.UnitQuaternion)
    (v : TorusFields.TorusBond n → BlockAverages.imaginaryQuaternions) (z : TorusFields.TorusSite n) (ρ s t : ℝ) : Prop where
  form_small : ∀ b : TorusFields.TorusBond n, b.1 ∈ ResponseInTheExpansion.supBall z ρ → ‖(v b : ℍ[ℝ])‖ ≤ s ∧
    ‖(v b : ℍ[ℝ]) - (LumpContours.minimalLog (ResponseInTheExpansion.gaugeTransform g W b) : ℍ[ℝ])‖ ≤ s ^ 2
  curvature_le : ∀ x ∈ ResponseInTheExpansion.supBall z ρ, ∀ μ ν : Fin 4, TorusFields.curvature W x μ ν ≤ t
  curl_le : ∀ p ∈ TorusFields.plaquettesIn (ResponseInTheExpansion.supBall z ρ),
    ‖(ResponseInTheExpansion.lieFormCurl v p : ℍ[ℝ])‖ ≤ t
def circulation (z : TorusFields.TorusSite n) (v : TorusFields.TorusBond n → BlockAverages.imaginaryQuaternions) (e : Fin 3) :
    (Fin 4 → ℤ) × Fin 4 → ℝ :=
  AxialForms.axialForm fun a μ ν =>
    BlockAverages.imaginaryComponent e (ResponseInTheExpansion.lieFormCurl v (z + TorusFields.siteOfInt a, μ, ν))
def axialLogEqCirculationStatement : Prop :=
  ∃ K : ℝ, 1 ≤ K ∧ ∀ (n : ℕ) [NeZero n] (z : TorusFields.TorusSite n) (W : TorusFields.TorusField n)
    (g : TorusFields.TorusSite n → BlockAverages.UnitQuaternion)
    (v : TorusFields.TorusBond n → BlockAverages.imaginaryQuaternions) (ρ s t : ℝ),
    1 ≤ ρ → 4 * ρ + 4 ≤ n → 0 ≤ s → s ≤ 1 → 0 ≤ t → t ≤ 1 → IsSmallOnBall W g v z ρ s t →
    ∃ G : TorusFields.TorusSite n → BlockAverages.UnitQuaternion, ∀ c : (Fin 4 → ℤ) × Fin 4,
      (TorusLumps.offsetSupNorm c.1 : ℝ) + 2 ≤ ρ → K * (1 + TorusLumps.offsetSupNorm c.1) * t ≤ 1 →
      ‖(LumpContours.minimalLog (ResponseInTheExpansion.gaugeTransform G W (TorusLumps.bondFrom z c)) : ℍ[ℝ])‖ ≤
          K * (1 + TorusLumps.offsetSupNorm c.1) * t ∧
      ∀ e : Fin 3, |BlockAverages.imaginaryComponent e
          (LumpContours.minimalLog (ResponseInTheExpansion.gaugeTransform G W (TorusLumps.bondFrom z c))) -
          circulation z v e c| ≤ K * (1 + TorusLumps.offsetSupNorm c.1) ^ 2 * s ^ 2
end YangMills.Construction.AxialLogarithm
end
