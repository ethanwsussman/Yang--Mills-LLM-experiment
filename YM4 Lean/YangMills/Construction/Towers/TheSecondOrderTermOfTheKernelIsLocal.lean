import YangMills.Construction.Towers.TermsOfTheUnsymmetrisedBackgroundKernel
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.QuadraticTermLocality
open YangMills.Construction.PeriodicOperators
open YangMills.Construction.Tower.FullSpace.FieldValueFunctions
open YangMills.Construction.Tower.FullSpace.UnsymmetrisedKernelTerms
def QuadraticTermIsLocal : Prop :=
  ∀ (L : ℕ) (hL : 0 < L), Conventions.IsAdmissibleBlockingFactor L → ∀ j : ℕ, 1 ≤ j →
    ∃ r : ℝ, 0 < r ∧ ∀ (c' : Fin 3) (e' : PositiveEdge (meshAt L j 0)) (c : Fin 3)
      (e : PositiveEdge (meshAt L j 0)),
      IsLocalTerm L j hL r e' e (quadraticCoarseTerm L j hL c' e' c e)
end YangMills.Construction.Tower.FullSpace.QuadraticTermLocality
end
