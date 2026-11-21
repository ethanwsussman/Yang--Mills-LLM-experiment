import YangMills.Construction.ColdStepAtMirrorFrames.DerivativeAlongChosenBonds
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages Topology
namespace YangMills.Construction.ColdStepAtMirrorFrames
namespace Subfamily
variable {F : BlockFrame}
def subfamilyMap {k n : ℕ} (l : Fin n → Fin k) : (Fin n → ℝ) →L[ℝ] (Fin k → ℝ) :=
  ∑ i, (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i).smulRight (Pi.single (l i) 1)
theorem subfamilyMap_apply {k n : ℕ} (l : Fin n → Fin k) (τ : Fin n → ℝ) (a : Fin k) :
    subfamilyMap l τ a = ∑ i, if l i = a then τ i else 0 := by
  unfold subfamilyMap
  rw [ContinuousLinearMap.sum_apply, Finset.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.proj_apply, Pi.smul_apply, smul_eq_mul]
  by_cases h : l i = a
  · subst h
    simp
  · simp [h, Pi.single_eq_of_ne (Ne.symm h)]
theorem subfamilyMap_single {k n : ℕ} (l : Fin n → Fin k) (i : Fin n) :
    subfamilyMap l (Pi.single i 1) = Pi.single (l i) 1 := by
  unfold subfamilyMap
  rw [ContinuousLinearMap.sum_apply, Finset.sum_eq_single i]
  · simp
  · intro b _ hb
    simp [Pi.single_eq_of_ne hb]
  · intro h
    exact absurd (Finset.mem_univ i) h
theorem bondSpread_comp {j k n : ℕ} (c : Fin k → F.Site j × Fin 4) (X : Fin k → imaginaryQuaternions)
    (l : Fin n → Fin k) (τ : Fin n → ℝ) :
    bondSpread (c ∘ l) (X ∘ l) τ = bondSpread c X (subfamilyMap l τ) := by
  funext y i
  unfold bondSpread
  have h1 : ∀ a : Fin k, (if c a = (y, i) then subfamilyMap l τ a • X a else 0) =
      ∑ m, if l m = a then (if c a = (y, i) then τ m • X a else 0) else 0 := by
    intro a
    rw [subfamilyMap_apply]
    by_cases h : c a = (y, i)
    · simp only [h, if_true]
      rw [Finset.sum_smul]
      refine Finset.sum_congr rfl fun m _ => ?_
      split_ifs <;> simp
    · simp [h]
  simp_rw [h1]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Finset.sum_eq_single (l m)]
  · simp
  · intro b _ hb
    simp [Ne.symm hb]
  · intro h
    exact absurd (Finset.mem_univ _) h
end Subfamily
open Subfamily in
theorem iteratedDerivAlongSubfamily : IteratedDerivAlongSubfamily := by
  intro F j k n G U c X l h
  set Φ : (Fin k → ℝ) → ℝ := fun τ => G (leftTranslate (bondSpread c X τ) U) with hΦ
  have e : (fun τ : Fin n → ℝ => G (leftTranslate (bondSpread (c ∘ l) (X ∘ l) τ) U)) = Φ ∘ subfamilyMap l := by
    funext τ
    simp only [hΦ, Function.comp, bondSpread_comp]
  unfold bondDeriv
  rw [e]
  obtain ⟨u, hu, huo⟩ : ∃ u : Set (Fin k → ℝ), (0 : Fin k → ℝ) ∈ u ∧ IsOpen u ∧ ContDiffOn ℝ n Φ u := by
    have hev := h.eventually (by simp)
    obtain ⟨t, ht, hto, h0⟩ := mem_nhds_iff.mp hev
    exact ⟨t, h0, hto, fun y hy => ContDiffAt.contDiffWithinAt (ht hy)⟩
  obtain ⟨huo, hcd⟩ := huo
  have hpre : IsOpen ((subfamilyMap l) ⁻¹' u) := huo.preimage (subfamilyMap l).continuous
  have h0' : (0 : Fin n → ℝ) ∈ (subfamilyMap l) ⁻¹' u := by
    simpa using hu
  have hc := ContinuousLinearMap.iteratedFDerivWithin_comp_right (subfamilyMap l) hcd huo.uniqueDiffOn
    hpre.uniqueDiffOn (x := 0) (by simpa using hu) (i := n) le_rfl
  rw [iteratedFDerivWithin_of_isOpen n hpre h0', iteratedFDerivWithin_of_isOpen n huo (by simpa using hu)] at hc
  rw [hc]
  simp only [map_zero, ContinuousMultilinearMap.compContinuousLinearMap_apply]
  congr 1
  funext i
  exact (subfamilyMap_single l i).symm
end YangMills.Construction.ColdStepAtMirrorFrames
end
