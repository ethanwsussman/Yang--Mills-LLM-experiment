import YangMills.Construction.ToriAtArbitraryCouplings.BoundedSequencesOfCutoffsAndTheirLimits
import Mathlib
set_option autoImplicit false
open Filter Set
open scoped ENNReal Topology
noncomputable section
namespace YangMills.Construction.ToriAtArbitraryCouplings
open ReflectionPositivity.AxisMirror (Ambient)
namespace CenteredMomentsOfLimit
open TorusSide
def Statement : Prop :=
  ∀ (s : TorusSide), 8 * 105 ^ 4 ≤ s.L → ∀ (m' : ℕ) (K : ℕ+ → ℕ+) (β : ℕ+ → ℝ) (C : ℕ → ℝ → ℝ)
    (h : s.IsUniformlyBoundedSeq m' K β C),
    ∀ J : Set ℕ+, J.Infinite → ∀ F : Ambient.ConnectedFamily s.asMirrorData .torus,
      s.TendstoAlong K β J (s.toComplexTupleFns F) → s.IsPermInvariantFamily .torus F →
        s.CenteredMomentsTendsto K β h.β_pos J F
end CenteredMomentsOfLimit
end YangMills.Construction.ToriAtArbitraryCouplings
end
