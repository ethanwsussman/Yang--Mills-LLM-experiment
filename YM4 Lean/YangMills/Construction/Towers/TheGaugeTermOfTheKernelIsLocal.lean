import YangMills.Construction.Towers.TermsOfTheUnsymmetrisedBackgroundKernel
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.GaugeTermLocality
open PeriodicOperators UnsymmetrisedKernelTerms
def Claim : Prop :=
  ∀ (L : ℕ) (hL : 0 < L), Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ, 1 ≤ k →
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ (c' : Fin 3) (e' : PositiveEdge (Tower.meshAt L k 0)) (c : Fin 3)
      (e : PositiveEdge (Tower.meshAt L k 0)),
      IsLocalTerm L k hL ρ e' e (gaugeFixingPairing L k hL c' e' c e)
end YangMills.Construction.Tower.FullSpace.GaugeTermLocality
end
