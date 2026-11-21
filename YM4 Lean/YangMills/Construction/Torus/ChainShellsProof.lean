import YangMills.Construction.Torus.ChainScales
import YangMills.Construction.Torus.ChainShells
import YangMills.Construction.Torus.CubePartitionProperties
import YangMills.Construction.Torus.NestedCubePartitions
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Torus.ChainShells
theorem mul_scaleSpacing_succ {L : ℕ} (hL : L ≠ 0) (ξ : ℝ) (M n : ℕ) :
    (M : ℝ) * scaleSpacing L ξ ((n + 1 : ℕ) : ℤ) =
      (L : ℝ) * ((M : ℝ) * scaleSpacing L ξ (n : ℤ)) := by
  have hL' : (L : ℝ) ≠ 0 := by exact_mod_cast hL
  simp only [scaleSpacing]
  push_cast
  rw [zpow_add₀ hL', zpow_one]
  ring
theorem pow_mul_scaleSpacing {L : ℕ} (hL : L ≠ 0) (ξ : ℝ) (u : ℕ) (i : ℤ) :
    ((L ^ u : ℕ) : ℝ) * scaleSpacing L ξ i = scaleSpacing L ξ (i + (u : ℤ)) := by
  have hL' : (L : ℝ) ≠ 0 := by exact_mod_cast hL
  simp only [scaleSpacing]
  push_cast
  rw [zpow_add₀ hL', zpow_natCast]
  ring
theorem shellsStatement_holds (hscales : ChainScales.ScalesStatement)
    (hpart : CubePartition.PropertiesOfIntegerMultiple)
    (hnest : NestedCubes.PropertiesOfOddRefinement) : ShellsStatement := by
  intro d L S ξ M R₁ t Ω hd hL hodd hchain
  have hs := hscales d L S ξ M R₁ t Ω (by omega) hchain
  have hL0 : L ≠ 0 := by omega
  have hLpos : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
  have hMpos : (0 : ℝ) < M := by
    have := hchain.blockSize_isPowerGe.1
    exact_mod_cast (by omega : 0 < M)
  have hside : ∀ n : ℕ, 0 < (M : ℝ) * scaleSpacing L ξ (n : ℤ) := fun n =>
    mul_pos hMpos (mul_pos (zpow_pos hLpos _) hchain.scale_pos)
  obtain ⟨u, -, hMu, hmul⟩ := hs.side_even_multiple
  have hk : ∀ n ≤ lastNonemptyIndex Ω, ∃ k : ℕ, 2 ≤ k ∧
      S = (k : ℝ) * ((M : ℝ) * scaleSpacing L ξ (n : ℤ)) := by
    intro n hn
    obtain ⟨k, hk0, hSk⟩ := hmul ((n : ℤ) + (u : ℤ)) (by omega)
    refine ⟨2 * k, by omega, ?_⟩
    have hb : (M : ℝ) * scaleSpacing L ξ (n : ℤ) = scaleSpacing L ξ ((n : ℤ) + (u : ℤ)) := by
      rw [← pow_mul_scaleSpacing hL0, hMu]
    rw [hb, hSk]
    push_cast
    ring
  have hnext : ∀ n ≤ lastNonemptyIndex Ω,
      IsCubeUnion ((M : ℝ) * scaleSpacing L ξ (n : ℤ)) (Ω (n + 1)) := by
    intro n hn
    rcases Nat.lt_or_ge n (lastNonemptyIndex Ω) with h | h
    · obtain ⟨k, hk2, hSk⟩ := hk (n + 1) h
      exact (hnest d S _ _ L k hd (hside n) hodd (mul_scaleSpacing_succ hL0 ξ M n) hk2
        hSk).isCubeUnion_of_coarse _ (hchain.isCubeUnion (n + 1) h)
    · rw [hs.eq_empty_of_lt (n + 1) (by omega)]
      exact ⟨∅, empty_subset _, sUnion_empty.symm⟩
  have hshell : ∀ n ≤ lastNonemptyIndex Ω, shell Ω n =
      ⋃₀ {Q ∈ cubePartition d S ((M : ℝ) * scaleSpacing L ξ (n : ℤ)) |
        Q ⊆ Ω n ∧ ¬ Q ⊆ Ω (n + 1)} := by
    intro n hn
    obtain ⟨k, hk2, hSk⟩ := hk n hn
    exact (hpart d S _ k hd (hside n) hk2 hSk).closure_diff_eq _ _ (hchain.isCubeUnion n hn)
      (hnext n hn) (hs.succ_subset n)
  have hsub : ∀ n ≤ lastNonemptyIndex Ω, shell Ω n ⊆
      Ω n ∩ cubeComplement ((M : ℝ) * scaleSpacing L ξ (n : ℤ)) (Ω (n + 1)) := by
    intro n hn p hp
    rw [hshell n hn] at hp
    obtain ⟨Q, ⟨hQ, hQn, hQn'⟩, hpQ⟩ := hp
    exact ⟨hQn hpQ, Q, ⟨hQ, hQn'⟩, hpQ⟩
  have hanti : ∀ n, Ω n ⊆ Ω 0 := by
    intro n
    induction n with
    | zero => exact Subset.rfl
    | succ n ih => exact (hs.succ_subset n).trans ih
  refine ⟨hnext, hshell, hsub, ?_, ?_⟩
  · apply Subset.antisymm
    · intro p hp
      have hex : ∃ n, p ∉ Ω n :=
        ⟨lastNonemptyIndex Ω + 1, by
          rw [hs.eq_empty_of_lt _ (Nat.lt_succ_self _)]; exact notMem_empty p⟩
      classical
      have hne : Nat.find hex ≠ 0 := by
        intro h0
        exact (h0 ▸ Nat.find_spec hex) hp
      obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hne
      have hin : p ∈ Ω m := by
        have := Nat.find_min hex (m := m) (by omega)
        exact not_not.mp this
      have hout : p ∉ Ω (m + 1) := by
        have := Nat.find_spec hex
        rwa [hm] at this
      have hmT : m ≤ lastNonemptyIndex Ω := by
        by_contra h
        rw [hs.eq_empty_of_lt m (by omega)] at hin
        exact hin
      exact mem_iUnion₂.mpr ⟨m, hmT, subset_closure ⟨hin, hout⟩⟩
    · refine iUnion₂_subset fun m hm => ?_
      exact fun p hp => hanti m (hsub m hm hp).1
  · intro m hm _
    simp [shell, hs.eq_empty_of_lt m hm]
end YangMills.Construction.Torus.ChainShells
end
