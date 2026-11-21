import YangMills.Construction.SummableBoundsOfTheFlow.CumulantOfMomentsUnderAShift
import YangMills.Construction.SummableBoundsOfTheFlow.PartitionSumOfTwoIndependentGroups
import Mathlib
set_option autoImplicit false
open Finset
namespace YangMills.Construction.Cumulants
theorem cumulantShiftInvariant_holds (hPart : CumulantOfIndependentGroupsZero) :
    CumulantShiftInvariant := by
  intro p i mo mo' c hp h0 hoff hon
  have hA' : ({i} : Finset (Fin p))ᶜ.Nonempty := by
    obtain ⟨j, hj⟩ : ∃ j : Fin p, j ≠ i := by
      by_contra hcon
      push Not at hcon
      have h1 : i.val = 0 ∨ i.val ≠ 0 := eq_or_ne _ _
      have ha := hcon ⟨0, by omega⟩
      have hb := hcon ⟨1, by omega⟩
      have := ha.trans hb.symm
      simp [Fin.ext_iff] at this
    exact ⟨j, by simpa using hj⟩
  have hzero := hPart p {i} (fun _ => 1) mo' ⟨i, mem_singleton_self i⟩ hA' rfl h0
  have hterm : ∀ π : Finpartition (univ : Finset (Fin p)),
      ∏ J ∈ π.parts, mo J = ∏ J ∈ π.parts, mo' J +
        c * ∏ J ∈ π.parts, ((fun _ : Finset (Fin p) => (1 : ℝ)) (J ∩ {i}) * mo' (J \ {i})) := by
    intro π
    have hB : π.part i ∈ π.parts := π.part_mem.mpr (mem_univ i)
    have hiB : i ∈ π.part i := π.mem_part_self.mpr (mem_univ i)
    have hout : ∀ J ∈ π.parts.erase (π.part i), i ∉ J := by
      intro J hJ hiJ
      exact (mem_erase.mp hJ).1 (π.part_eq_of_mem (mem_erase.mp hJ).2 hiJ).symm
    have e1 : ∏ J ∈ π.parts.erase (π.part i), mo J = ∏ J ∈ π.parts.erase (π.part i), mo' J :=
      prod_congr rfl fun J hJ => hoff J (hout J hJ)
    have e2 : ∏ J ∈ π.parts.erase (π.part i),
        ((fun _ : Finset (Fin p) => (1 : ℝ)) (J ∩ {i}) * mo' (J \ {i})) =
        ∏ J ∈ π.parts.erase (π.part i), mo' J := by
      apply prod_congr rfl
      intro J hJ
      have : J \ {i} = J := by
        rw [sdiff_singleton_eq_erase, erase_eq_of_notMem (hout J hJ)]
      simp only [this, one_mul]
    rw [← mul_prod_erase π.parts _ hB, ← mul_prod_erase π.parts (fun J => mo' J) hB,
      ← mul_prod_erase π.parts (fun J => (fun _ : Finset (Fin p) => (1 : ℝ)) (J ∩ {i}) * mo' (J \ {i})) hB,
      e1, e2, hon _ hiB, sdiff_singleton_eq_erase, one_mul]
    ring
  simp only [hterm, mul_add, sum_add_distrib]
  have hz : ∑ π : Finpartition (univ : Finset (Fin p)),
      (-1 : ℝ) ^ (π.parts.card - 1) * ((π.parts.card - 1).factorial : ℝ) *
        (c * ∏ J ∈ π.parts, ((fun _ : Finset (Fin p) => (1 : ℝ)) (J ∩ {i}) * mo' (J \ {i}))) = 0 := by
    have : ∀ π : Finpartition (univ : Finset (Fin p)),
        (-1 : ℝ) ^ (π.parts.card - 1) * ((π.parts.card - 1).factorial : ℝ) *
          (c * ∏ J ∈ π.parts, ((fun _ : Finset (Fin p) => (1 : ℝ)) (J ∩ {i}) * mo' (J \ {i}))) =
        c * ((-1 : ℝ) ^ (π.parts.card - 1) * ((π.parts.card - 1).factorial : ℝ) *
          ∏ J ∈ π.parts, ((fun _ : Finset (Fin p) => (1 : ℝ)) (J ∩ {i}) * mo' (J \ {i}))) := by
      intro π
      ring
    simp only [this]
    rw [← mul_sum, hzero, mul_zero]
  rw [hz, add_zero]
end YangMills.Construction.Cumulants
