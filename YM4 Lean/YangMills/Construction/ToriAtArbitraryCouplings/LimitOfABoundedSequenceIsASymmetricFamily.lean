import YangMills.Construction.ToriAtArbitraryCouplings.BoundedSequencesOfCutoffsAndTheirLimits
import Mathlib
set_option autoImplicit false
open Filter Set
open scoped ENNReal Topology
noncomputable section
namespace YangMills.Construction.ToriAtArbitraryCouplings
open YangMills.Construction.ReflectionPositivity.AxisMirror (Ambient)
namespace SymmetricLimitFamily
open TorusSide
def Statement : Prop :=
  ∀ (s : TorusSide), 8 * 105 ^ 4 ≤ s.L → ∀ (m' : ℕ) (K : ℕ+ → ℕ+) (β : ℕ+ → ℝ) (C : ℕ → ℝ → ℝ)
    (hs : s.IsUniformlyBoundedSeq m' K β C),
    ∀ J : Set ℕ+, J.Infinite → ∀ S : s.ComplexTupleFns, s.TendstoAlong K β J S →
      ∃ F : Ambient.ConnectedFamily s.asMirrorData .torus,
        s.toComplexTupleFns F = S ∧
        s.IsPermInvariantFamily .torus F ∧
        s.ObeysClusterEstimate m' C (s.toComplexTupleFns F) ∧
        s.IsEquicontinuousBound m' C (s.toComplexTupleFns F)
end SymmetricLimitFamily
end YangMills.Construction.ToriAtArbitraryCouplings
end
