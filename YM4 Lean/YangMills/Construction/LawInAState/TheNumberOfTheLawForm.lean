import YangMills.Construction.LawInAState.DataOfTheLaw
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.StateLaws
open TorusLumps RenormalizationStepParameters ResponseInTheExpansion
open InfiniteLattice (AmbientSpace)
def covarianceAtSeparationStatement : Prop :=
  HoldsForShapes fun Tb y Kr Xi vt => ∃ C d₀ : ℝ, 0 < d₀ ∧ ∀ d : ℝ, 0 < d → d ≤ d₀ → ∀ (K : ℕ) (β : ℝ),
    IsFlowDatum (Tb.stepParameters y) Xi K β → minimalCutoff (Tb.stepParameters y) Xi d ≤ K →
    ∀ al : ℕ → ℝ, IsChainResponseCoeff (Tb.stepParameters y) Kr β (separationLevel (Tb.stepParameters y) β K d) al →
    ∀ f h : AmbientSpace → ℝ, IsNormalizedTestPair d vt f h →
      ∃ ε : ℝ, |ε| ≤ C * lengthInSites (Tb.stepParameters y).side K (separationLevel (Tb.stepParameters y) β K d) d ^ (-(1 / 2) : ℝ) +
            C * couplingAtSeparation (Tb.stepParameters y) β K d ^ (-(1 / 130) : ℝ) ∧
        unitTorusCovariance (Tb.stepParameters y).side K β f h =
          al (separationLevel (Tb.stepParameters y) β K d) ^ 2 * (9 / Real.pi ^ 4) *
            (couplingAtSeparation (Tb.stepParameters y) β K d ^ 2)⁻¹ * TestFunctions.inverseEighthKernel f h * (1 + ε)
end YangMills.Construction.StateLaws
end
