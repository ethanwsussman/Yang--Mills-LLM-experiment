import YangMills.Construction.Sequences.ConvexNatSequenceLinear
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.ConvexNatSequence
theorem linearOfConvexBoundedDivisible_holds : LinearOfConvexBoundedDivisible := by
  intro m hzero hconvex hbound hdvd
  obtain ⟨C, hC⟩ := hbound
  set a : ℕ → ℤ := fun i => (m (i + 1) : ℤ) - m i with ha
  have hstep : ∀ i, a i ≤ a (i + 1) := by
    intro i
    have h := hconvex (i + 1) (by omega)
    simp only [Nat.add_sub_cancel] at h
    have h' : 2 * (m (i + 1) : ℤ) ≤ m i + m (i + 1 + 1) := by exact_mod_cast h
    simp only [ha]
    linarith
  have hmono : Monotone a := monotone_nat_of_le_succ hstep
  have hlower : ∀ i j : ℕ, (m i : ℤ) + j * a i ≤ m (i + j) := by
    intro i j
    induction j with
    | zero => simp
    | succ j ih =>
      have h1 : a i ≤ a (i + j) := hmono (by omega)
      have h2 : a (i + j) = (m (i + j + 1) : ℤ) - m (i + j) := rfl
      rw [show i + (j + 1) = i + j + 1 by omega]
      push_cast
      linarith
  have hincr : ∀ i, (a i : ℝ) ≤ C := by
    intro i
    by_contra hlt
    have hpos : 0 < (a i : ℝ) - C := by
      have := not_le.mp hlt
      linarith
    obtain ⟨j, hj⟩ := exists_nat_gt ((C * i) / ((a i : ℝ) - C))
    rw [div_lt_iff₀ hpos] at hj
    have h1 : ((m i : ℤ) : ℝ) + (j : ℝ) * (a i : ℝ) ≤ ((m (i + j) : ℤ) : ℝ) := by
      exact_mod_cast hlower i j
    have h2 := hC (i + j)
    have h3 : (0 : ℝ) ≤ (m i : ℝ) := Nat.cast_nonneg _
    push_cast at h1 h2
    nlinarith
  obtain ⟨L, ⟨K, hK⟩, hL⟩ := Int.exists_greatest_of_bdd (P := fun z => ∃ i, a i = z)
    ⟨⌈C⌉, by
      rintro z ⟨i, rfl⟩
      have : ((a i : ℤ) : ℝ) ≤ (⌈C⌉ : ℝ) := (hincr i).trans (Int.le_ceil C)
      exact_mod_cast this⟩
    ⟨a 0, 0, rfl⟩
  have hle : ∀ i, a i ≤ L := fun i => hL _ ⟨i, rfl⟩
  have hupper : ∀ i j : ℕ, (m (i + j) : ℤ) ≤ m i + j * L := by
    intro i j
    induction j with
    | zero => simp
    | succ j ih =>
      have h1 := hle (i + j)
      have h2 : a (i + j) = (m (i + j + 1) : ℤ) - m (i + j) := rfl
      rw [show i + (j + 1) = i + j + 1 by omega]
      push_cast
      linarith
  have hline : ∀ j : ℕ, (m (K + j) : ℤ) = m K + j * L := by
    intro j
    have h := hlower K j
    rw [hK] at h
    exact le_antisymm (hupper K j) h
  have hm0 : (m 0 : ℤ) = 0 := by exact_mod_cast hzero
  have hgap : 0 ≤ (K : ℤ) * L - m K := by
    have h := hupper 0 K
    rw [Nat.zero_add, hm0] at h
    linarith
  obtain ⟨d, hd⟩ := Int.eq_ofNat_of_zero_le hgap
  have hd0 : d = 0 := by
    have hn : 1 ≤ K + (2 * d + 1) := by omega
    have hdiv : ((K + (2 * d + 1) : ℕ) : ℤ) ∣ 2 * (m (K + (2 * d + 1)) : ℤ) := by
      exact_mod_cast hdvd _ hn
    have hval : 2 * (m (K + (2 * d + 1)) : ℤ)
        = ((K + (2 * d + 1) : ℕ) : ℤ) * (2 * L) - 2 * (d : ℤ) := by
      rw [hline]
      push_cast
      linarith
    rw [hval] at hdiv
    have hdiv' : ((K + (2 * d + 1) : ℕ) : ℤ) ∣ 2 * (d : ℤ) :=
      (Int.dvd_iff_dvd_of_dvd_sub hdiv).mp (Dvd.intro _ rfl)
    have hz : 2 * (d : ℤ) = 0 := by
      apply Int.eq_zero_of_abs_lt_dvd hdiv'
      rw [abs_of_nonneg (by positivity)]
      push_cast
      omega
    omega
  have hKL : (m K : ℤ) = K * L := by
    rw [hd0] at hd
    simp only [Nat.cast_zero] at hd
    linarith
  have hall : ∀ k : ℕ, (m k : ℤ) = k * L := by
    intro k
    have h1 := hupper 0 k
    rw [Nat.zero_add, hm0] at h1
    have h2 := hupper k K
    rw [Nat.add_comm k K, hline, hKL] at h2
    linarith
  intro k
  have h1 := hall 1
  have h2 := hall k
  have h3 : (m k : ℤ) = k * m 1 := by
    rw [h2, h1]
    simp
  exact_mod_cast h3
end YangMills.Construction.ConvexNatSequence
