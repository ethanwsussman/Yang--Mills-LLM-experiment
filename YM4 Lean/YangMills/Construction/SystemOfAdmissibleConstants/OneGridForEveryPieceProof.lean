import YangMills.Construction.SystemOfAdmissibleConstants.OneGridForEveryPiece
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.AdmissibleConstants
private lemma card_Ioo_floor_ceil_le (t w : ℝ) (hw : 0 ≤ w) :
    ((Finset.Ioo ⌊t⌋ ⌈t + w⌉).card : ℝ) ≤ w + 1 := by
  rw [Int.card_Ioo]
  have h1 : ((⌈t + w⌉ : ℤ) : ℝ) < t + w + 1 := Int.ceil_lt_add_one _
  have h2 : t < (⌊t⌋ : ℝ) + 1 := Int.lt_floor_add_one t
  rcases le_or_gt (⌈t + w⌉ - ⌊t⌋ - 1) 0 with h | h
  · rw [Int.toNat_of_nonpos h]
    simp only [Nat.cast_zero]
    linarith
  · have hcast : (((⌈t + w⌉ - ⌊t⌋ - 1).toNat : ℕ) : ℤ) = ⌈t + w⌉ - ⌊t⌋ - 1 :=
      Int.toNat_of_nonneg h.le
    have hreal : (((⌈t + w⌉ - ⌊t⌋ - 1).toNat : ℕ) : ℝ) = ((⌈t + w⌉ - ⌊t⌋ - 1 : ℤ) : ℝ) := by
      exact_mod_cast hcast
    rw [hreal]
    push_cast
    linarith
theorem gridOffsetAvoidsPoints_holds : GridOffsetAvoidsPoints := by
  intro a l ε m n ha hε hl hcount α
  classical
  have hw0 : 0 ≤ 6 * ε / a := by positivity
  let t : Fin n → ℝ := fun i => (α i - a / 2 - 3 * ε) / a
  let bad : Fin n → Finset ℤ := fun i =>
    (Finset.Ioo ⌊t i⌋ ⌈t i + 6 * ε / a⌉).image (fun u => u % (m : ℤ))
  let all : Finset ℤ := Finset.univ.biUnion bad
  have hbad : ∀ i, ((bad i).card : ℝ) ≤ 6 * ε / a + 1 := fun i =>
    le_trans (by exact_mod_cast Finset.card_image_le) (card_Ioo_floor_ceil_le (t i) _ hw0)
  have hall : (all.card : ℝ) < m := by
    have h1 : all.card ≤ ∑ i, (bad i).card := Finset.card_biUnion_le
    have h2 : ((∑ i, (bad i).card : ℕ) : ℝ) ≤ n * (6 * ε / a + 1) := by
      push_cast
      calc ∑ i, ((bad i).card : ℝ) ≤ ∑ _i : Fin n, (6 * ε / a + 1) :=
            Finset.sum_le_sum fun i _ => hbad i
        _ = n * (6 * ε / a + 1) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    calc (all.card : ℝ) ≤ ((∑ i, (bad i).card : ℕ) : ℝ) := by exact_mod_cast h1
      _ ≤ n * (6 * ε / a + 1) := h2
      _ < m := hcount
  have hcard : all.card < (Finset.Ico (0 : ℤ) m).card := by
    simp only [Int.card_Ico, sub_zero, Int.toNat_natCast]
    exact_mod_cast hall
  obtain ⟨j, hj, hjall⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  rw [Finset.mem_Ico] at hj
  refine ⟨j, fun i k => ?_⟩
  by_contra hlt
  rw [not_le, abs_lt] at hlt
  obtain ⟨hlow, hhigh⟩ := hlt
  subst hl
  apply hjall
  refine Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, Finset.mem_image.mpr ⟨j + m * k, ?_, ?_⟩⟩
  · have hleft : t i < ((j + m * k : ℤ) : ℝ) := by
      simp only [t]
      rw [div_lt_iff₀ ha]
      push_cast
      linarith
    have hright : ((j + m * k : ℤ) : ℝ) < t i + 6 * ε / a := by
      have hsum : t i + 6 * ε / a = (α i - a / 2 + 3 * ε) / a := by
        simp only [t]
        rw [← add_div]
        congr 1
        ring
      rw [hsum, lt_div_iff₀ ha]
      push_cast
      linarith
    exact Finset.mem_Ioo.mpr ⟨Int.floor_lt.mpr hleft, Int.lt_ceil.mpr hright⟩
  · rw [Int.add_mul_emod_self_left]
    exact Int.emod_eq_of_lt hj.1 hj.2
end YangMills.Construction.AdmissibleConstants
end
