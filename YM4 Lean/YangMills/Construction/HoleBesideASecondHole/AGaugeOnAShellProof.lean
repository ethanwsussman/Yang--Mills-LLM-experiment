import YangMills.Construction.HoleBesideASecondHole.AGaugeOnAShell
import YangMills.Construction.HoleBesideASecondHole.GaugesOnTwoPartsAreGlued
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.ShellOrthant
theorem shellQuarticGauge_holds (hOrth : orthantQuarticGaugeStatement) (hGlue : orthantGaugeGluingStatement) :
    ShellQuarticGauge := by
  classical
  have key : ∀ n : ℕ, ∃ c K : ℝ, 0 < c ∧ 0 < K ∧ ∀ (l : ℝ) (o : Fin 4 → ℝ) (s : Fin 4 → ℤ)
      (P : Finset LatticeFractionalIntegration.Lattice4), 100 ≤ l → (∀ k, s k = 1 ∨ s k = -1 ∨ s k = 0) →
      (Finset.univ.filter fun k => s k = 0).card = n →
      (∀ x, x ∈ P ↔ IsInShellOrthant o l s x) → HasQuarticGaugeOn c K P := by
    intro n
    induction n with
    | zero =>
      obtain ⟨c, K, hc, hK, h⟩ := hOrth
      refine ⟨c, K, hc, hK, fun l o s P hl hs hn hP => h l o s P hl (fun k => ?_) hP⟩
      rcases hs k with h1 | h1 | h1
      · exact Or.inl h1
      · exact Or.inr h1
      · exfalso
        have : k ∈ Finset.univ.filter fun k => s k = 0 := by simp [h1]
        rw [Finset.card_eq_zero.1 hn] at this
        simp at this
    | succ n ih =>
      obtain ⟨c, K, hc, hK, h⟩ := ih
      obtain ⟨c', K', hc', hK', hglue⟩ := hGlue c K hc hK
      refine ⟨c', K', hc', hK', fun l o s P hl hs hn hP => ?_⟩
      obtain ⟨i, hi⟩ : ∃ i, i ∈ Finset.univ.filter fun k => s k = 0 := by
        apply Finset.card_pos.1
        omega
      have hsi : s i = 0 := by simpa using hi
      have hcount : ∀ e : ℤ, e ≠ 0 →
          (Finset.univ.filter fun k => Function.update s i e k = 0).card = n := by
        intro e he
        have : (Finset.univ.filter fun k => Function.update s i e k = 0) =
            (Finset.univ.filter fun k => s k = 0).erase i := by
          ext k
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
          by_cases hk : k = i
          · subst hk
            simp [he]
          · simp [Function.update_of_ne hk, hk]
        rw [this, Finset.card_erase_of_mem hi, hn]
        rfl
      have hvals : ∀ e : ℤ, (e = 1 ∨ e = -1 ∨ e = 0) → ∀ k, Function.update s i e k = 1 ∨
          Function.update s i e k = -1 ∨ Function.update s i e k = 0 := by
        intro e he k
        by_cases hk : k = i
        · subst hk
          simpa using he
        · simpa [Function.update_of_ne hk] using hs k
      have hfin : ∀ s' : Fin 4 → ℤ, ∃ Q : Finset LatticeFractionalIntegration.Lattice4,
          ∀ x, x ∈ Q ↔ IsInShellOrthant o l s' x := by
        intro s'
        have hl0 : 0 < l := by linarith
        refine ⟨(Fintype.piFinset fun k => Finset.Icc ⌈o k - 1.9 * l⌉ ⌊o k + 1.9 * l⌋).filter
          fun x => IsInShellOrthant o l s' x, fun x => ?_⟩
        simp only [Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_Icc, and_iff_right_iff_imp]
        intro hx k
        have h1 := hx.1 k
        have h2 : -(1.9 * l) ≤ orthantLower l (s' k) ∧ orthantUpper l (s' k) ≤ 1.9 * l := by
          unfold orthantLower orthantUpper
          split_ifs with a b b
          · omega
          · constructor <;> linarith
          · constructor <;> linarith
          · constructor <;> linarith
        exact ⟨Int.ceil_le.2 (by linarith [h1.1, h2.1]), Int.le_floor.2 (by linarith [h1.2, h2.2])⟩
      obtain ⟨Pp, hPp⟩ := hfin (Function.update s i 1)
      obtain ⟨Pm, hPm⟩ := hfin (Function.update s i (-1))
      exact hglue l o s i P Pp Pm hl hs hsi hP hPp hPm
        (h l o _ Pp hl (hvals 1 (Or.inl rfl)) (hcount 1 (by norm_num)) hPp)
        (h l o _ Pm hl (hvals (-1) (Or.inr (Or.inl rfl))) (hcount (-1) (by norm_num)) hPm)
  obtain ⟨c, K, hc, hK, h⟩ := key 4
  refine ⟨c, K, hc, hK, fun l o P hl hP => h l o _ P hl (fun _ => Or.inr (Or.inr rfl)) ?_ hP⟩
  simp
end YangMills.Construction.ShellOrthant
end
