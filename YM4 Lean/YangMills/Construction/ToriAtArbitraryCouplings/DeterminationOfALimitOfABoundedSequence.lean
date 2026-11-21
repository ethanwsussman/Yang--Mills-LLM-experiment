import YangMills.Construction.ToriAtArbitraryCouplings.BoundedSequencesOfCutoffsAndTheirLimits
import Mathlib
set_option autoImplicit false
open Filter Set
open scoped ENNReal Topology
noncomputable section
namespace YangMills.Construction.ToriAtArbitraryCouplings
open YangMills.Construction.ReflectionPositivity.AxisMirror (Ambient)
namespace LimitDetermination
open TorusSide
def Holds : Prop :=
  ∀ (s : TorusSide), 8 * 105 ^ 4 ≤ s.L → ∀ (m' : ℕ) (K : ℕ+ → ℕ+) (β : ℕ+ → ℝ) (C : ℕ → ℝ → ℝ)
    (hs : s.IsUniformlyBoundedSeq m' K β C),
    ∀ J : Set ℕ+, J.Infinite → ∀ F : Ambient.ConnectedFamily s.asMirrorData .torus,
      s.TendstoAlong K β J (s.toComplexTupleFns F) → s.IsPermInvariantFamily .torus F →
        s.ObeysClusterEstimate m' C (s.toComplexTupleFns F) →
        s.IsUniquelyDetermined m' K β hs.isClusterConstant J F
end LimitDetermination
end YangMills.Construction.ToriAtArbitraryCouplings
end
