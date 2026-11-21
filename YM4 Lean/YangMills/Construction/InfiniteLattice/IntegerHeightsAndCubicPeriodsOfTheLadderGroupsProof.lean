import YangMills.Construction.InfiniteLattice.IntegerHeightsAndCubicPeriodsOfTheLadderGroups
import YangMills.Construction.InfiniteLattice.OneFamilyOfMirrors
import Mathlib
set_option autoImplicit false
open scoped Matrix
noncomputable section
namespace YangMills.Construction.NormalFamilies
open YangMills.Construction.InfiniteLattice
open YangMills.Construction.PeriodicLattice (coordVec)
namespace IntegerLevelsAndCubicPeriods
theorem firstNonzeroIndex_eq_of_forall_lt {n : AmbientSpace} {i : Fin 4} (hi : n i ≠ 0)
    (hbelow : ∀ j, j < i → n j = 0) : firstNonzeroIndex n = i := by apply _root_.YangMills.Construction.NormalFamilies.firstNonzeroIndex_eq <;> assumption
theorem dotProduct_coordVec (n : AmbientSpace) (i : Fin 4) : n ⬝ᵥ coordVec i = n i := by
  simp [coordVec, dotProduct_single]
theorem normalSet_facts {n : AmbientSpace} (hn : n ∈ normalSet) :
    (∃ e : Fin 4 → ℤ, ∀ i, n i = (e i : ℝ)) ∧ (normSq n = 1 ∨ normSq n = 2) ∧
      n (firstNonzeroIndex n) = 1 := by
  rcases hn with ⟨i, rfl⟩ | ⟨i, j, hij, rfl | rfl⟩
  · refine ⟨⟨Pi.single i 1, fun k => ?_⟩, Or.inl ?_, ?_⟩
    · simp only [coordVec, Pi.single_apply]
      split_ifs <;> simp
    · rw [normSq_eq_dotProduct, dotProduct_coordVec]
      simp [coordVec]
    · have hfirst : firstNonzeroIndex (coordVec i) = i :=
        firstNonzeroIndex_eq_of_forall_lt (by simp [coordVec])
          (fun k hk => by simp [coordVec, hk.ne])
      rw [hfirst]
      simp [coordVec]
  · refine ⟨⟨Pi.single i 1 + Pi.single j 1, fun k => ?_⟩, Or.inr ?_, ?_⟩
    · simp only [coordVec, Pi.add_apply, Pi.single_apply]
      split_ifs <;> norm_num
    · rw [normSq_eq_dotProduct, dotProduct_add, dotProduct_coordVec, dotProduct_coordVec]
      simp [coordVec, hij.ne, hij.ne']
      norm_num
    · have hfirst : firstNonzeroIndex (coordVec i + coordVec j) = i :=
        firstNonzeroIndex_eq_of_forall_lt (by simp [coordVec, hij.ne])
          (fun k hk => by
            simp [coordVec, hk.ne, (hk.trans hij).ne])
      rw [hfirst]
      simp [coordVec, hij.ne]
  · refine ⟨⟨Pi.single i 1 - Pi.single j 1, fun k => ?_⟩, Or.inr ?_, ?_⟩
    · simp only [coordVec, Pi.sub_apply, Pi.single_apply]
      split_ifs <;> simp
    · rw [normSq_eq_dotProduct, dotProduct_sub, dotProduct_coordVec, dotProduct_coordVec]
      simp [coordVec, hij.ne, hij.ne']
      norm_num
    · have hfirst : firstNonzeroIndex (coordVec i - coordVec j) = i :=
        firstNonzeroIndex_eq_of_forall_lt (by simp [coordVec, hij.ne])
          (fun k hk => by
            simp [coordVec, hk.ne, (hk.trans hij).ne])
      rw [hfirst]
      simp [coordVec, hij.ne]
theorem dotProduct_dualVector {n : AmbientSpace} (hq : normSq n = 1 ∨ normSq n = 2) :
    n ⬝ᵥ dualVector n = 1 := by
  have hne : normSq n ≠ 0 := by
    rcases hq with h | h <;> rw [h] <;> norm_num
  rw [dualVector, dotProduct_smul, ← normSq_eq_dotProduct, smul_eq_mul, inv_mul_cancel₀ hne]
theorem two_mul_smul_dualVector_mem {n : AmbientSpace} {e : Fin 4 → ℤ}
    (he : ∀ i, n i = (e i : ℝ)) (hq : normSq n = 1 ∨ normSq n = 2) {h : ℤ} (hh : Even h) :
    (2 * (h : ℝ)) • dualVector n ∈ latticeSubgroup 2 := by
  obtain ⟨g, rfl⟩ := hh
  rcases hq with hq | hq
  · refine ⟨fun i => (g + g) * e i, fun i => ?_⟩
    simp only [dualVector, hq, Pi.smul_apply, smul_eq_mul, he]
    push_cast
    ring
  · refine ⟨fun i => g * e i, fun i => ?_⟩
    simp only [dualVector, hq, Pi.smul_apply, smul_eq_mul, he]
    push_cast
    ring
theorem statement_holds : IntegerLevelsAndCubicPeriods.Statement := by
  intro n hn h hh _
  obtain ⟨⟨e, he⟩, hq, hone⟩ := normalSet_facts hn
  refine ⟨?_, ?_, ?_⟩
  · rw [firstNonzeroBasisVec, dotProduct_coordVec]
    exact hone
  · rintro x ⟨m, hm⟩
    refine ⟨∑ i, e i * m i, ?_⟩
    simp [dotProduct, hm, he]
  · rintro x ⟨m, hm⟩
    have hw := two_mul_smul_dualVector_mem he hq hh
    have hx : x ∈ latticeSubgroup 2 :=
      ⟨fun i => m i * h, fun i => by rw [hm i]; push_cast; ring⟩
    have hdot : n ⬝ᵥ x = ((∑ i, e i * m i : ℤ) : ℝ) * (2 * (h : ℝ)) := by
      simp only [dotProduct, hm, he]
      push_cast
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [mem_normalPeriodLattice_iff]
    refine ⟨x - (∑ i, e i * m i) • ((2 * (h : ℝ)) • dualVector n), ?_, ∑ i, e i * m i, by simp⟩
    refine AddSubgroup.mem_inf.mpr ⟨?_, ?_⟩
    · exact (latticeSubgroup 2).sub_mem hx ((latticeSubgroup 2).zsmul_mem hw _)
    · change n ⬝ᵥ (x - (∑ i, e i * m i) • ((2 * (h : ℝ)) • dualVector n)) = 0
      rw [dotProduct_sub, hdot, ← Int.cast_smul_eq_zsmul ℝ, dotProduct_smul, dotProduct_smul,
        dotProduct_dualVector hq]
      simp
end IntegerLevelsAndCubicPeriods
end YangMills.Construction.NormalFamilies
end
