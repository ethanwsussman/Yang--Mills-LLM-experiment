import YangMills.Construction.InfiniteLattice.StatesAtFixedSpacing
import YangMills.Construction.InfiniteLattice.TorusStatesAreTheVolumeLimitPoints
import YangMills.Construction.QuaternionicWilsonModel.TheTorusStatesHaveAMember
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.QuaternionicWilsonModel.TorusLimitSetNonempty
theorem nonemptyStatement_holds (hNonempty : InfiniteLattice.TorusLimitSetsNonempty)
    (hLimits : InfiniteLattice.TorusLimitsAreInfiniteVolumeLimits) : NonemptyStatement := by
  have hall : ∀ L K : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < K → ∀ β : ℝ, 0 < β →
      NonemptyOfLimits L K β := by
    intro L K hL hK β hβ
    have hL2 : 2 ≤ L := by
      have h := hL.2
      omega
    refine ⟨hNonempty L K hL hK β hβ, fun ν hν => ?_⟩
    rw [hLimits L K β hL2] at hν
    exact hν
  refine ⟨hall, fun ℓ hℓ Bs g hBs K β hp => ?_⟩
  have hL : Conventions.IsAdmissibleBlockingFactor ℓ.side := by
    refine ⟨hℓ.side_odd, ?_⟩
    have h := hℓ.side_ge
    norm_num at h
    omega
  have hlevel : SequencePassage.passageThreshold Bs g ≤ β := hp.2.1
  have hg : 0 ≤ g ^ (-2 : ℤ) := by
    rw [zpow_neg]
    positivity
  have hβ : 0 < β := by
    unfold SequencePassage.passageThreshold at hlevel
    linarith
  exact hall ℓ.side K hL K.pos β hβ
end YangMills.Construction.QuaternionicWilsonModel.TorusLimitSetNonempty
end
