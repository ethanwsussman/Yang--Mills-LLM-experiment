import YangMills.Construction.ToriAtArbitraryCouplings.BoundedSequencesOfCutoffsAndTheirLimits
import Mathlib
set_option autoImplicit false
open Filter Set
open scoped ENNReal Topology
noncomputable section
namespace YangMills.Construction.ToriAtArbitraryCouplings
open YangMills.Construction.ReflectionPositivity.AxisMirror (Ambient)
namespace EquicontinuityAlongSequence
open TorusSide
def Holds : Prop :=
  ∀ (s : TorusSide), 8 * 105 ^ 4 ≤ s.L → ∀ (m' : ℕ) (K : ℕ+ → ℕ+) (β : ℕ+ → ℝ) (C : ℕ → ℝ → ℝ)
    (hK : s.IsUniformlyBoundedSeq m' K β C),
    ∀ j, s.IsEquicontinuousBound m' C (s.cumulantFnsAt (K j) (β j))
end EquicontinuityAlongSequence
end YangMills.Construction.ToriAtArbitraryCouplings
end
