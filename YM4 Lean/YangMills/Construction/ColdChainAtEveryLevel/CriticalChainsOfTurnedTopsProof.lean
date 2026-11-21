import YangMills.Construction.ColdChainAtEveryLevel.CriticalChainsOfTurnedTops
import YangMills.Construction.ColdChainAtEveryLevel.CriticalChainsWithTwoRadii
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.BlockAverages
theorem IsRotatedChain.of_twisted {F : BlockFrame} {a θ del Ca rL r' CL s : ℝ} {Ck : ℕ → ℝ} {S : Finset F.Cell}
    {V : F.GaugeField F.top} {k : ℕ} {c : Fin k → F.Site F.top × Fin 4} {X : Fin k → imaginaryQuaternions}
    {U : ChainChart F} {T : (Fin k → ℝ) → ChainChart F}
    (h : TwistedTops.IsTwistedCriticalChain a θ del Ca rL r' CL s Ck S V c X U T) :
    IsRotatedChain a θ del Ca rL r' CL s Ck S V c X U T :=
  ⟨h.eq_zero, h.holo_fine, h.holo_coarse, h.analytic_fine, h.analytic_coarse, h.mem_gaugeSlice, h.norm_le,
    h.isCritical, h.hessian_ge, h.mixedDeriv_decay⟩
theorem IsRotatedChain.toTwisted {F : BlockFrame} {a θ del Ca rL r' CL s : ℝ} {Ck : ℕ → ℝ} {S : Finset F.Cell}
    {V : F.GaugeField F.top} {k : ℕ} {c : Fin k → F.Site F.top × Fin 4} {X : Fin k → imaginaryQuaternions}
    {U : ChainChart F} {T : (Fin k → ℝ) → ChainChart F}
    (h : IsRotatedChain a θ del Ca rL r' CL s Ck S V c X U T) :
    TwistedTops.IsTwistedCriticalChain a θ del Ca rL r' CL s Ck S V c X U T :=
  ⟨h.eq_at_zero, h.holomorphic_fine, h.holomorphic_coarse, h.analyticAt_fine, h.analyticAt_coarse, h.mem_slice,
    h.small, h.critical, h.floor, h.decay⟩
theorem rotatedCriticalChains_of_twoRadii (h : criticalChainsTwoRadiiStatement) :
    rotatedCriticalChainsStatement := by
  intro a ha
  obtain ⟨θ, del, Ca, h1, h2, h3, h4, h5, L₀, hL⟩ := h a ha
  refine ⟨θ, del, Ca, h1, h2, h3, h4, h5, L₀, fun L hodd hLe => ?_⟩
  obtain ⟨rL, r', sL, CL, Ck, g1, g2, g3, g4, g5, g6, hmain, hcomp⟩ := hL L hodd hLe
  refine ⟨rL, r', sL, CL, Ck, g1, g2, g3, g4, g5, g6, ?_, ?_⟩
  · intro F m S hF hamb hm hreg s V hs hsL hcold
    obtain ⟨U, u1, u2, u3⟩ := hmain F m S hF hamb hm hreg s V hs hsL hcold
    refine ⟨U, u1, u2, fun k c X hk hX => ?_⟩
    obtain ⟨T, hT⟩ := u3 k c X hk hX
    exact ⟨T, IsRotatedChain.of_twisted hT⟩
  · intro F F' m S S' hF hF' ht hamb hamb' hm hreg hreg' s V V' Y Y' r hs hsL hcold hcold' hr hagree U U' hU hU'
    obtain ⟨e1, e2⟩ := hcomp F F' m S S' hF hF' ht hamb hamb' hm hreg hreg' s V V' Y Y' r hs hsL hcold hcold' hr hagree U U'
      hU hU'
    exact ⟨e1, fun k h X hk hh hX T T' hT hT' m' e z hm' hz =>
      e2 k h X hk hh hX T T' (IsRotatedChain.toTwisted hT) (IsRotatedChain.toTwisted hT')
        m' e z hm' hz⟩
end YangMills.Construction.BlockAverages
end
