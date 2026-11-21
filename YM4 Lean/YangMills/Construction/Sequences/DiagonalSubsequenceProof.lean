import YangMills.Construction.Sequences.DiagonalSubsequence
import Mathlib
set_option autoImplicit false
open Filter Topology
noncomputable section
namespace YangMills.Construction.DiagonalSubsequence
theorem exists_strictMono_mem (S : Sequences.PNatIndexSet) :
    ∃ f : ℕ → ℕ+, StrictMono f ∧ ∀ k, f k ∈ S.carrier := by
  have hS : ∀ M : ℕ, ∃ m > M, ∃ q ∈ S.carrier, (q : ℕ) = m := by
    intro M
    obtain ⟨q, hq, hM⟩ := (S.infinite_filter_ge ((M : ℤ) + 1)).nonempty
    exact ⟨q, by omega, q, hq, rfl⟩
  obtain ⟨ψ, hψ, hQ⟩ := Nat.exists_strictMono_subsequence hS
  choose f hf hfψ using hQ
  refine ⟨f, fun a b hab => ?_, hf⟩
  have hlt := hψ hab
  rw [← hfψ a, ← hfψ b] at hlt
  exact hlt
def zeroExtend {m : ℤ} (u : {k : ℤ // m ≤ k} → ℂ) (k : ℕ+) : ℂ :=
  if h : m ≤ ((k : ℕ) : ℤ) then u ⟨((k : ℕ) : ℤ), h⟩ else 0
theorem norm_zeroExtend_le {m : ℤ} {u : {k : ℤ // m ≤ k} → ℂ} {B : ℝ}
    (hB : ∀ k, ‖u k‖ ≤ B) (k : ℕ+) : ‖zeroExtend u k‖ ≤ max B 0 := by
  unfold zeroExtend
  split_ifs with h
  · exact (hB _).trans (le_max_left _ _)
  · simp
theorem countableBoundedFamilyConverges_holds : CountableBoundedFamilyConverges := by
  intro I _ m u hu S
  obtain ⟨f, hf, hfS⟩ := exists_strictMono_mem S
  choose B hB using hu
  let y : ℕ → I → ℂ := fun k i => zeroExtend (u i) (f k)
  have hy : ∀ k, y k ∈ Set.pi Set.univ fun i => Metric.closedBall (0 : ℂ) (max (B i) 0) := by
    intro k i _
    simpa [y] using norm_zeroExtend_le (hB i) (f k)
  obtain ⟨c, -, ψ, hψ, hlim⟩ :=
    (isCompact_univ_pi fun i => isCompact_closedBall (0 : ℂ) (max (B i) 0)).tendsto_subseq hy
  have hmono : StrictMono (f ∘ ψ) := hf.comp hψ
  refine ⟨⟨Set.range (f ∘ ψ), Set.infinite_range_of_injective hmono.injective⟩, ?_, ?_⟩
  · rintro _ ⟨k, rfl⟩
    exact hfS _
  · intro i
    refine ⟨c i, fun ε hε => ?_⟩
    obtain ⟨K, hK⟩ := Metric.tendsto_atTop.mp (tendsto_pi_nhds.mp hlim i) ε hε
    refine ⟨(f ∘ ψ) K, ?_⟩
    rintro ⟨k, ⟨n, rfl⟩, hm⟩ hk
    have hn : K ≤ n := hmono.le_iff_le.mp hk
    have hd := hK n hn
    rw [dist_eq_norm] at hd
    have heq : zeroExtend (u i) ((f ∘ ψ) n) = u i ⟨(((f ∘ ψ) n : ℕ+) : ℕ), hm⟩ :=
      dif_pos hm
    change ‖u i ⟨(((f ∘ ψ) n : ℕ+) : ℕ), hm⟩ - c i‖ < ε
    rw [← heq]
    exact hd
end YangMills.Construction.DiagonalSubsequence
