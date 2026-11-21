import YangMills.Construction.Lattice.AdicGridPoints
import YangMills.Construction.ReflectionPositiveLimits.MirrorsAndReflectionPositivityOfAFunctional
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ReflectionPositivity
open PeriodicLattice (adicGridPoints coordVec)
def posAdicGridPoints (L : ℕ) : Set ℝ := adicGridPoints L ∩ Set.Ioi 0
def halfAdicGridPoints (L : ℕ) : Set ℝ := {c | ∃ d ∈ adicGridPoints L, c = d / 2}
def IsAdicMirror (L : ℕ) (M : NormalMirror) : Prop :=
  ((∃ μ, M.normal = coordVec μ) ∧ M.offset ∈ halfAdicGridPoints L) ∨
    ((∃ μ ν, μ ≠ ν ∧
        (M.normal = coordVec μ + coordVec ν ∨
          M.normal = coordVec μ - coordVec ν)) ∧
      M.offset ∈ adicGridPoints L)
end YangMills.Construction.ReflectionPositivity
