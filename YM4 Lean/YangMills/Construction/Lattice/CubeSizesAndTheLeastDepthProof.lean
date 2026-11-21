import YangMills.Construction.Lattice.CubeSizesAndTheLeastDepth
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open ParameterChoice
namespace PeriodicLattice.CubesOfStep
theorem cubeSizesAndMinimalDelay_holds : CubeSizesAndMinimalDelay := by
  intro c K x hL hr hx
  have hL2 : 2 ≤ c.L := by
    have := hL.2
    omega
  refine ⟨fun k hk => ⟨Thresholds.minBlockSize_eq_pow hL2 c.r x k,
    Thresholds.one_le_minBlockSize hL2 c.r x k, fun hk1 => ?_⟩, ?_⟩
  · exact Thresholds.minBlockSize_antitone hL2 c.r (by omega) (fun n hn => hx n (by omega))
  · intro k hk1 hkK hE
    obtain ⟨hdef, hNk, hN0⟩ := hE
    have hmem : Thresholds.minDelay c.L c.r x k ∈ Thresholds.delayCandidates c.L c.r x k :=
      Nat.sInf_mem hdef
    obtain ⟨h1, h2, h3⟩ := hmem
    intro N₀ h k₀
    have h3' : c.L ^ (N₀ - 1) = Thresholds.minBlockSize c.L c.r x (k + 1 - N₀) := h3
    have hlt : N₀ < delayAt c x k := hN0
    have hk₀ : k₀ = (k : ℤ) - (N₀ : ℤ) := rfl
    have hNR : delayAt c x k = Thresholds.minBlockSize c.L c.r x k := rfl
    have h2N : 2 ≤ N₀ := by
      by_contra hnot
      have hone : N₀ = 1 := by omega
      rw [hone] at h3' hlt
      simp only [Nat.sub_self, pow_zero, Nat.add_sub_cancel] at h3'
      omega
    have hto : (k₀ + 1).toNat = k + 1 - N₀ := by omega
    refine ⟨h2N, by omega, by omega, by omega, ?_, ?_, ?_⟩
    · rw [hto]
      exact h3'.symm
    · exact Nat.le_self_pow (by omega) _
    · intro j hj
      rw [hto]
      exact Thresholds.minBlockSize_antitone hL2 c.r (by omega) (fun n hn => hx n (by omega))
end PeriodicLattice.CubesOfStep
end YangMills.Construction
end
