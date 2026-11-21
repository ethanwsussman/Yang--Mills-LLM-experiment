import YangMills.Construction.ColdChainAtEveryLevel.CompositeMeanOfTheGeneratorsProof
import YangMills.Construction.HoleBesideASecondHole.OscillationInAFlatBox
import YangMills.Construction.HoleBesideASecondHole.OscillationOnAPlaneOfAShell
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.ShellSlices
open FlatBoxes ShellOrthant LatticeFractionalIntegration
namespace SlabChain
abbrev Site : Type := LatticeFractionalIntegration.Lattice4
theorem mem_boxBetween_iff {lo hi x : Site} : x ∈ boxBetween lo hi ↔ ∀ j, lo j ≤ x j ∧ x j ≤ hi j := by
  simp [boxBetween, Fintype.mem_piFinset]
theorem add_pow_four_le (a b : ℝ) : (a + b) ^ 4 ≤ 8 * (a ^ 4 + b ^ 4) := by apply _root_.YangMills.Construction.BlockAverages.GeneratorMeans.add_pow_four_le_eight_mul <;> assumption
theorem add_four_pow_four_le (a b c d Q : ℝ) (ha : a ^ 4 ≤ Q) (hb : b ^ 4 ≤ Q) (hc : c ^ 4 ≤ Q) (hd : d ^ 4 ≤ Q) :
    (a + b + c + d) ^ 4 ≤ 256 * Q := by
  have h1 := add_pow_four_le (a + b) (c + d)
  have h2 := add_pow_four_le a b
  have h3 := add_pow_four_le c d
  have e : a + b + c + d = a + b + (c + d) := by ring
  rw [e]
  linarith
theorem oscillation_on_slab (Cosc : ℝ) (hC : 0 < Cosc)
    (hosc : ∀ (i : Fin 4) (n : ℕ) (lo hi : Site) (f : Site → ℍ[ℝ]) (w : Site → ℝ) (E : ℝ),
      2 ≤ n → lo i = hi i → (∀ j, j ≠ i → (n : ℤ) ≤ hi j - lo j + 1 ∧ hi j - lo j + 1 ≤ 8 * n) →
      0 ≤ E → (∀ x, 0 ≤ w x) →
      (∀ x ∈ boxBetween lo hi, ∀ j, x + basisVector j ∈ boxBetween lo hi → ‖f (x + basisVector j) - f x‖ ≤ w x) →
      ∑ x ∈ boxBetween lo hi, w x ^ 4 ≤ E ^ 4 →
      ∀ x ∈ boxBetween lo hi, ∀ y ∈ boxBetween lo hi, ‖f x - f y‖ ^ 4 ≤ Cosc * n * E ^ 4)
    (l : ℝ) (hl : 100 ≤ l) (i : Fin 4) (τ : ℤ) (A B : Fin 4 → ℝ)
    (hlen : ∀ k, k ≠ i → 0.8 * l ≤ B k - A k ∧ B k - A k ≤ 3.8 * l)
    (Y : Finset Site) (hsub : ∀ x : Site, x i = τ → (∀ k, k ≠ i → A k ≤ x k ∧ (x k : ℝ) ≤ B k) → x ∈ Y)
    (f : Site → ℍ[ℝ]) (w : Site → ℝ) (E : ℝ) (hE : 0 ≤ E) (hw : ∀ x, 0 ≤ w x)
    (hb : ∀ x ∈ Y, ∀ j, x + basisVector j ∈ Y → ‖f (x + basisVector j) - f x‖ ≤ w x)
    (hs : ∑ x ∈ Y, w x ^ 4 ≤ E ^ 4) (x y : Site) (hxi : x i = τ) (hyi : y i = τ)
    (hx : ∀ k, k ≠ i → A k ≤ x k ∧ (x k : ℝ) ≤ B k) (hy : ∀ k, k ≠ i → A k ≤ y k ∧ (y k : ℝ) ≤ B k) :
    ‖f x - f y‖ ^ 4 ≤ Cosc * l * E ^ 4 := by
  classical
  obtain ⟨n, hn⟩ : ∃ n : ℕ, ⌊0.8 * l⌋₊ = n + 1 := by
    have : 1 ≤ ⌊0.8 * l⌋₊ := Nat.le_floor (by push_cast; linarith)
    exact ⟨⌊0.8 * l⌋₊ - 1, by omega⟩
  have hl0 : 0 ≤ 0.8 * l := by linarith
  have hn1 : (n : ℝ) + 1 ≤ 0.8 * l := by
    have := Nat.floor_le hl0
    rw [hn] at this
    push_cast at this
    linarith
  have hn2 : 0.8 * l < (n : ℝ) + 2 := by
    have := Nat.lt_floor_add_one (0.8 * l)
    rw [hn] at this
    push_cast at this
    linarith
  have hn3 : 2 ≤ n := by
    have : (2 : ℝ) ≤ n := by linarith
    exact_mod_cast this
  set lo : Site := fun k => if k = i then τ else ⌈A k⌉ with hlo
  set hi : Site := fun k => if k = i then τ else ⌊B k⌋ with hhi
  have hmem : ∀ z : Site, z ∈ boxBetween lo hi ↔ z i = τ ∧ ∀ k, k ≠ i → A k ≤ z k ∧ (z k : ℝ) ≤ B k := by
    intro z
    rw [mem_boxBetween_iff]
    constructor
    · intro h
      refine ⟨?_, fun k hk => ?_⟩
      · have := h i
        simp only [hlo, hhi, if_true] at this
        omega
      · have := h k
        simp only [hlo, hhi, hk, if_false] at this
        exact ⟨Int.ceil_le.1 this.1, Int.le_floor.1 this.2⟩
    · rintro ⟨h1, h2⟩ k
      by_cases hk : k = i
      · subst hk
        simp only [hlo, hhi, if_true]
        omega
      · simp only [hlo, hhi, hk, if_false]
        exact ⟨Int.ceil_le.2 (h2 k hk).1, Int.le_floor.2 (h2 k hk).2⟩
  have hbox : boxBetween lo hi ⊆ Y := by
    intro z hz
    obtain ⟨h1, h2⟩ := (hmem z).1 hz
    exact hsub z h1 h2
  have hres := hosc i n lo hi f w E hn3 (by simp [hlo, hhi]) (by
      intro j hj
      simp only [hlo, hhi, hj, if_false]
      obtain ⟨h1, h2⟩ := hlen j hj
      have a1 := Int.floor_le (B j)
      have a2 := Int.lt_floor_add_one (B j)
      have a3 := Int.le_ceil (A j)
      have a4 := Int.ceil_lt_add_one (A j)
      constructor
      · have : (n : ℝ) < ((⌊B j⌋ - ⌈A j⌉ + 1 : ℤ) : ℝ) := by
          push_cast
          linarith
        have h3 : ((n : ℤ) : ℝ) < ((⌊B j⌋ - ⌈A j⌉ + 1 : ℤ) : ℝ) := by exact_mod_cast this
        have h4 : (n : ℤ) < ⌊B j⌋ - ⌈A j⌉ + 1 := by exact_mod_cast h3
        omega
      · have : ((⌊B j⌋ - ⌈A j⌉ + 1 : ℤ) : ℝ) ≤ ((8 * (n : ℤ) : ℤ) : ℝ) := by
          push_cast
          linarith
        exact_mod_cast this) hE hw
    (fun z hz j hzj => hb z (hbox hz) j (hbox hzj))
    (le_trans (Finset.sum_le_sum_of_subset_of_nonneg hbox fun z _ _ => by have := hw z; positivity) hs)
    x ((hmem x).2 ⟨hxi, hx⟩) y ((hmem y).2 ⟨hyi, hy⟩)
  refine hres.trans ?_
  have hnl : (n : ℝ) ≤ l := by linarith
  have : 0 ≤ E ^ 4 := by positivity
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hnl hC.le) this
theorem orthantLower_orthantUpper_bounds (l : ℝ) (hl : 0 < l) (t : ℤ) :
    -(1.9 * l) ≤ orthantLower l t ∧ orthantUpper l t ≤ 1.9 * l ∧ 2.4 * l ≤ orthantUpper l t - orthantLower l t ∧
      orthantUpper l t - orthantLower l t ≤ 3.8 * l := by
  unfold orthantLower orthantUpper
  split_ifs with h1 h2 h2
  · omega
  · refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith
  · refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith
  · refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith
end SlabChain
open SlabChain in
theorem shellSliceOscillation (hO : flatBoxOscillationStatement) :
    shellSliceOscillationStatement := by
  classical
  have hne1 : ∀ i : Fin 4, ∃ k : Fin 4, k ≠ i := by decide
  have hne2 : ∀ i j : Fin 4, ∃ k : Fin 4, k ≠ i ∧ k ≠ j := by decide
  obtain ⟨Cosc, hC, hosc⟩ := hO
  refine ⟨256 * Cosc, by positivity, ?_⟩
  intro l o s i τ Y f w E hl hs hsi hτ hY hE hw hb hsum
  have hl0 : 0 < l := by linarith
  have hτ' := abs_le.1 hτ
  have hlowi : orthantLower l (s i) = -(1.9 * l) := by simp [orthantLower, hsi]
  have hhighi : orthantUpper l (s i) = 1.9 * l := by simp [orthantUpper, hsi]
  have slab : ∀ (j : Fin 4) (e : ℤ), j ≠ i → (e = 1 ∧ s j ≠ -1 ∨ e = -1 ∧ s j ≠ 1) → ∀ x ∈ Y, ∀ y ∈ Y,
      1.1 * l ≤ (e : ℝ) * ((x j : ℝ) - o j) → 1.1 * l ≤ (e : ℝ) * ((y j : ℝ) - o j) →
      ‖f x - f y‖ ^ 4 ≤ Cosc * l * E ^ 4 := by
    intro j e hj he x hx y hy hxe hye
    set A : Fin 4 → ℝ := fun k => if k = j then (if e = 1 then o j + 1.1 * l else o j - 1.9 * l)
      else o k + orthantLower l (s k) with hA
    set B : Fin 4 → ℝ := fun k => if k = j then (if e = 1 then o j + 1.9 * l else o j - 1.1 * l)
      else o k + orthantUpper l (s k) with hB
    have hpt : ∀ z ∈ Y, 1.1 * l ≤ (e : ℝ) * ((z j : ℝ) - o j) → z i = τ ∧
        ∀ k, k ≠ i → A k ≤ z k ∧ (z k : ℝ) ≤ B k := by
      intro z hz hze
      obtain ⟨⟨h1, -⟩, h2⟩ := (hY z).1 hz
      refine ⟨h2, fun k _ => ?_⟩
      by_cases hk : k = j
      · subst hk
        have h3 := h1 k
        have h4 := orthantLower_orthantUpper_bounds l hl0 (s k)
        simp only [hA, hB, if_true]
        rcases he with ⟨rfl, -⟩ | ⟨rfl, -⟩
        · norm_num at hze ⊢
          constructor <;> linarith [h3.1, h3.2, h4.1, h4.2.1]
        · norm_num at hze ⊢
          constructor <;> linarith [h3.1, h3.2, h4.1, h4.2.1]
      · simp only [hA, hB, hk, if_false]
        have h3 := h1 k
        constructor <;> linarith [h3.1, h3.2]
    obtain ⟨hxi, hxk⟩ := hpt x hx hxe
    obtain ⟨hyi, hyk⟩ := hpt y hy hye
    refine oscillation_on_slab Cosc hC hosc l hl i τ A B ?_ Y ?_ f w E hE hw hb hsum x y hxi hyi hxk hyk
    · intro k _
      by_cases hk : k = j
      · subst hk
        simp only [hA, hB, if_true]
        by_cases h1 : e = 1
        · simp only [h1, if_true]
          constructor <;> linarith
        · simp only [h1, if_false]
          constructor <;> linarith
      · simp only [hA, hB, hk, if_false]
        have := orthantLower_orthantUpper_bounds l hl0 (s k)
        constructor <;> linarith [this.2.2.1, this.2.2.2]
    · intro z hzi hzk
      rw [hY]
      refine ⟨⟨fun k => ?_, j, ?_⟩, hzi⟩
      · by_cases hk : k = i
        · subst hk
          rw [hlowi, hhighi, hzi]
          constructor <;> linarith [hτ'.1, hτ'.2]
        · have h3 := hzk k hk
          by_cases hkj : k = j
          · subst hkj
            simp only [hA, hB, if_true] at h3
            rcases he with ⟨rfl, h4⟩ | ⟨rfl, h4⟩
            · simp only [if_true] at h3
              have h5 : orthantUpper l (s k) = 1.9 * l := by simp [orthantUpper, h4]
              have h6 := orthantLower_orthantUpper_bounds l hl0 (s k)
              have h7 : orthantLower l (s k) ≤ -(l / 2) := by
                unfold orthantLower
                split_ifs <;> linarith
              rw [h5]
              constructor <;> linarith [h3.1, h3.2]
            · norm_num at h3
              have h5 : orthantLower l (s k) = -(1.9 * l) := by simp [orthantLower, h4]
              have h7 : l / 2 ≤ orthantUpper l (s k) := by
                unfold orthantUpper
                split_ifs <;> linarith
              rw [h5]
              constructor <;> linarith [h3.1, h3.2]
          · simp only [hA, hB, hkj, if_false] at h3
            constructor <;> linarith [h3.1, h3.2]
      · have h3 := hzk j hj
        simp only [hA, hB, if_true] at h3
        rcases he with ⟨rfl, -⟩ | ⟨rfl, -⟩
        · simp only [if_true] at h3
          exact le_trans (by linarith [h3.1]) (le_abs_self _)
        · norm_num at h3
          refine le_trans ?_ (neg_le_abs _)
          linarith [h3.2]
  set eh : Fin 4 → ℤ := fun k => if s k = -1 then -1 else 1 with heh
  have hehv : ∀ k, eh k = 1 ∧ s k ≠ -1 ∨ eh k = -1 ∧ s k ≠ 1 := by
    intro k
    by_cases h : s k = -1
    · right
      simp [heh, h]
    · left
      simp [heh, h]
  set hub : Site := fun k => if k = i then τ else if s k = -1 then ⌊o k - 1.1 * l⌋ else ⌈o k + 1.1 * l⌉ with hhub
  have hubk : ∀ k, k ≠ i → 1.1 * l ≤ (eh k : ℝ) * ((hub k : ℝ) - o k) ∧
      (eh k : ℝ) * ((hub k : ℝ) - o k) ≤ 1.9 * l := by
    intro k hk
    by_cases h : s k = -1
    · simp only [heh, hhub, h, hk, if_true, if_false]
      have a1 := Int.floor_le (o k - 1.1 * l)
      have a2 := Int.lt_floor_add_one (o k - 1.1 * l)
      norm_num
      constructor <;> linarith
    · simp only [heh, hhub, h, hk, if_false]
      have a1 := Int.le_ceil (o k + 1.1 * l)
      have a2 := Int.ceil_lt_add_one (o k + 1.1 * l)
      norm_num
      constructor <;> linarith
  have hubi : hub i = τ := by simp [hhub]
  have hinterval : ∀ k (t : ℝ), 1.1 * l ≤ (eh k : ℝ) * t → (eh k : ℝ) * t ≤ 1.9 * l →
      orthantLower l (s k) ≤ t ∧ t ≤ orthantUpper l (s k) := by
    intro k t h1 h2
    by_cases h : s k = -1
    · simp only [heh, h, if_true] at h1 h2
      have e1 : orthantLower l (s k) = -(1.9 * l) := by
        simp [orthantLower, h]
      have e2 : orthantUpper l (s k) = l / 2 := by simp [orthantUpper, h]
      rw [e1, e2]
      norm_num at h1 h2
      constructor <;> linarith
    · simp only [heh, h, if_false] at h1 h2
      have e2 : orthantUpper l (s k) = 1.9 * l := by simp [orthantUpper, h]
      have h7 : orthantLower l (s k) ≤ -(l / 2) := by
        unfold orthantLower
        split_ifs <;> linarith
      rw [e2]
      norm_num at h1 h2
      constructor <;> linarith
  have hubY : hub ∈ Y := by
    rw [hY]
    refine ⟨⟨fun k => ?_, ?_⟩, hubi⟩
    · by_cases hk : k = i
      · subst hk
        rw [hlowi, hhighi, hubi]
        constructor <;> linarith [hτ'.1, hτ'.2]
      · exact hinterval k _ (hubk k hk).1 (hubk k hk).2
    · obtain ⟨k, hk⟩ : ∃ k : Fin 4, k ≠ i := hne1 i
      refine ⟨k, ?_⟩
      have h1 := (hubk k hk).1
      by_cases h : s k = -1
      · simp only [heh, h, if_true] at h1
        norm_num at h1
        refine le_trans ?_ (neg_le_abs _)
        linarith
      · simp only [heh, h, if_false] at h1
        norm_num at h1
        refine le_trans ?_ (le_abs_self _)
        linarith
  have toHub : ∀ x ∈ Y, ∃ z ∈ Y, ‖f x - f z‖ ^ 4 ≤ Cosc * l * E ^ 4 ∧ ‖f z - f hub‖ ^ 4 ≤ Cosc * l * E ^ 4 := by
    intro x hx
    have hQ : 0 ≤ Cosc * l * E ^ 4 := by positivity
    obtain ⟨⟨h1, j, hj⟩, h2⟩ := (hY x).1 hx
    have hji : j ≠ i := by
      rintro rfl
      rw [h2] at hj
      have := abs_le.2 ⟨by linarith [hτ'.1], by linarith [hτ'.2]⟩ |>.trans' hj
      linarith
    obtain ⟨e, he, hxe⟩ : ∃ e : ℤ, (e = 1 ∧ s j ≠ -1 ∨ e = -1 ∧ s j ≠ 1) ∧ 1.1 * l ≤ (e : ℝ) * ((x j : ℝ) - o j) := by
      rcases le_abs'.1 hj with h | h
      · refine ⟨-1, Or.inr ⟨rfl, ?_⟩, by push_cast; linarith⟩
        intro h3
        have := (h1 j).1
        simp only [orthantLower, h3, if_true] at this
        linarith
      · refine ⟨1, Or.inl ⟨rfl, ?_⟩, by push_cast; linarith⟩
        intro h3
        have := (h1 j).2
        simp only [orthantUpper, h3, if_true] at this
        linarith
    by_cases hsame : e = eh j
    · refine ⟨x, hx, by simp; positivity, ?_⟩
      refine slab j e hji he x hx hub hubY hxe ?_
      rw [hsame]
      exact (hubk j hji).1
    · obtain ⟨k, hki, hkj⟩ : ∃ k : Fin 4, k ≠ i ∧ k ≠ j := hne2 i j
      set z : Site := Function.update x k (hub k) with hz
      have hzk : z k = hub k := by simp [hz]
      have hzo : ∀ m, m ≠ k → z m = x m := fun m hm => by simp [hz, Function.update_of_ne hm]
      have hzY : z ∈ Y := by
        rw [hY]
        refine ⟨⟨fun m => ?_, j, ?_⟩, ?_⟩
        · by_cases hm : m = k
          · subst hm
            rw [hzk]
            exact hinterval m _ (hubk m hki).1 (hubk m hki).2
          · rw [hzo m hm]
            exact h1 m
        · rw [hzo j hkj.symm]
          exact hj
        · rw [hzo i hki.symm]
          exact h2
      refine ⟨z, hzY, ?_, ?_⟩
      · refine slab j e hji he x hx z hzY hxe ?_
        rw [hzo j hkj.symm]
        exact hxe
      · refine slab k (eh k) hki (hehv k) z hzY hub hubY ?_ (hubk k hki).1
        rw [hzk]
        exact (hubk k hki).1
  intro x hx y hy
  obtain ⟨z, hz, hz1, hz2⟩ := toHub x hx
  obtain ⟨z', hz', hz1', hz2'⟩ := toHub y hy
  have hb1 : ‖f x - f y‖ ≤ ‖f x - f z‖ + ‖f z - f hub‖ + ‖f z' - f hub‖ + ‖f y - f z'‖ := by
    calc ‖f x - f y‖ = ‖(f x - f z) + (f z - f hub) - (f z' - f hub) - (f y - f z')‖ := by
          congr 1
          abel
      _ ≤ _ := by
          refine (norm_sub_le _ _).trans ?_
          refine add_le_add_left ?_ _
          refine (norm_sub_le _ _).trans ?_
          refine add_le_add_left ?_ _
          exact norm_add_le _ _
  have h4 := add_four_pow_four_le _ _ _ _ _ hz1 hz2 hz2' hz1'
  calc ‖f x - f y‖ ^ 4 ≤ (‖f x - f z‖ + ‖f z - f hub‖ + ‖f z' - f hub‖ + ‖f y - f z'‖) ^ 4 :=
        pow_le_pow_left₀ (norm_nonneg _) hb1 4
    _ ≤ 256 * (Cosc * l * E ^ 4) := h4
    _ = 256 * Cosc * l * E ^ 4 := by ring
end YangMills.Construction.ShellSlices
end
