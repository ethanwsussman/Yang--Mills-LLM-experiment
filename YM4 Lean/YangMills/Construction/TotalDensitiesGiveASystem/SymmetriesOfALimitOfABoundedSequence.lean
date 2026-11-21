import YangMills.Construction.ToriAtArbitraryCouplings.ATorusWithArbitraryFirstPassageData
import YangMills.Construction.ToriAtArbitraryCouplings.BoundedSequencesOfCutoffsAndTheirLimits
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TotalDensities
open ToriAtArbitraryCouplings
namespace BoundedSequenceLimit
def Claim : Prop :=
  ∀ s : TorusSide, 8 * 105 ^ 4 ≤ s.L → ∀ (m' : ℕ) (K : ℕ+ → ℕ+) (β : ℕ+ → ℝ) (C : ℕ → ℝ → ℝ),
    s.IsUniformlyBoundedSeq m' K β C → ∀ J : Set ℕ+, J.Infinite →
    ∀ F : ReflectionPositivity.AxisMirror.Ambient.ConnectedFamily s.asMirrorData .torus,
      s.TendstoAlong K β J (s.toComplexTupleFns F) →
      s.IsEquicontinuousBound m' C (s.toComplexTupleFns F) →
      s.CumulantsInvariant F ∧ ∀ M : ReflectionPositivity.AxisMirror.CoordMirror, s.ReflectionPositiveAt F M
end BoundedSequenceLimit
end YangMills.Construction.TotalDensities
end
