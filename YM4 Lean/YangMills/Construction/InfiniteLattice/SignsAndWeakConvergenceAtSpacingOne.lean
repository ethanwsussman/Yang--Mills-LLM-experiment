import YangMills.Construction.InfiniteLattice.ObservablesOnTheClosedSideOfAMirrorAndStates
import Mathlib
set_option autoImplicit false
open MeasureTheory Filter
open scoped Topology
noncomputable section
namespace YangMills.Construction
namespace InfiniteLattice
def LatticeSymmetry.IsOrthogonalPart (r : LatticeSymmetry 1) (R : Matrix (Fin 4) (Fin 4) ℝ) : Prop :=
  R ∈ Matrix.orthogonalGroup (Fin 4) ℝ ∧ ∀ x : AmbientSpace, r.toFun x = R.mulVec x + r.toFun 0
def LatticeSymmetry.orthogonalPart (r : LatticeSymmetry 1) : Matrix (Fin 4) (Fin 4) ℝ :=
  Classical.epsilon r.IsOrthogonalPart
def WeakConvergesUnitSpacing (ν : ℕ → Measure (GaugeField 1))
    (ν₀ : Measure (GaugeField 1)) : Prop :=
  ∀ F : GaugeField 1 → ℂ, Continuous F →
    Tendsto (fun k => stateEval (ν k) F) atTop (𝓝 (stateEval ν₀ F))
def IsWeakClusterPointUnitSpacing (ν : ℕ → Measure (GaugeField 1))
    (ν₀ : Measure (GaugeField 1)) : Prop :=
  ∀ 𝒞 : Set (GaugeField 1 → ℂ), 𝒞.Finite → (∀ F ∈ 𝒞, Continuous F) →
    ∀ ε : ℝ, 0 < ε → ∀ k₀ : ℕ, 1 ≤ k₀ →
      ∃ k, k₀ ≤ k ∧ ∀ F ∈ 𝒞, ‖stateEval (ν k) F - stateEval ν₀ F‖ ≤ ε
end InfiniteLattice
end YangMills.Construction
end
