import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Towers.TermOfTheSecondOrderAndCommutatorTerm
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower
def HessianAlongGaugeDirection : Prop :=
  ∀ L n k : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < n → 1 ≤ k →
    EventuallyNearIdentity (fieldSpace L n k 0) fun U =>
      ∀ B ∈ edgeFormSpace L n k 0, ∀ l ∈ vertexFunctionSpace L n k 0,
        ((leftSecondDeriv (plaquetteAction L n k) U B (covDiff U l) : ℝ) : ℂ) =
          edgeFormPairing
            (leftGradient (fieldSpace L n k 0) (fun V => (plaquetteAction L n k V : ℂ)) U)
            (bracketTerm U l B)
end YangMills.Construction.Tower
end
