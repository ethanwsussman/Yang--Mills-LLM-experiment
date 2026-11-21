import YangMills.Construction.ToriAtArbitraryCouplings.BoundedSequencesOfCutoffsAndTheirLimits
import YangMills.Construction.ToriAtArbitraryCouplings.EquicontinuityByTelescoping
import Mathlib
set_option autoImplicit false
open Filter Set
open scoped ENNReal Topology
noncomputable section
namespace YangMills.Construction.ToriAtArbitraryCouplings
open ReflectionPositivity.AxisMirror (Ambient)
namespace BoundedMultilinearForms
open TorusSide
def Statement : Prop :=
  ∀ (s : TorusSide), 8 * 105 ^ 4 ≤ s.L → ∀ (m' : ℕ) (K : ℕ+ → ℕ+) (β : ℕ+ → ℝ) (C : ℕ → ℝ → ℝ)
    (h : s.IsUniformlyBoundedSeq m' K β C),
    ∀ (j : ℕ+) (n : ℕ), 2 ≤ n → ∀ d : ℝ, 0 < d → ∀ A : Fin n → Set (s.Point .torus),
      (∀ i k, i ≠ k → ENNReal.ofReal d ≤ s.setDist .torus (A i) (A k)) →
      ∃ Ψ : MultilinearMap ℝ (fun l => s.c1Submodule .torus (A l)) ℝ,
        ∀ u : (l : Fin n) → s.c1Submodule .torus (A l),
          (Ψ u : ℂ) = s.cumulantAt (K j) (β j) (s.componentsAsTuple .torus u) ∧
          |Ψ u| ≤ C n d * ∏ l, s.sharpNormAt m' .torus (u l : s.Point .torus → ℝ)
end BoundedMultilinearForms
end YangMills.Construction.ToriAtArbitraryCouplings
end
