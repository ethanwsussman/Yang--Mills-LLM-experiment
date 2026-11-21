import YangMills.Construction.Matrices.HaarExpChartDensity
import YangMills.Construction.Matrices.HaarRelabelInversion
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.Matrices.ComplexMatrix2.HaarRelabel
private theorem zpow_zpow_of_sign {e : ℤ} (he : e = 1 ∨ e = -1) (x : specialUnitary) :
    (x ^ e) ^ e = x := by
  rcases he with rfl | rfl <;> simp
private theorem haarProb_preimage_zpow_sign
    (hinv : Measure.map (fun U : specialUnitary => U⁻¹) haarProb = haarProb)
    {e : ℤ} (he : e = 1 ∨ e = -1) {s : Set specialUnitary} (hs : MeasurableSet s) :
    haarProb ((fun x : specialUnitary => x ^ e) ⁻¹' s) = haarProb s := by
  rcases he with rfl | rfl
  · simp
  · have h := Measure.map_apply (μ := haarProb) (f := fun U : specialUnitary => U⁻¹)
      continuous_inv.measurable hs
    rw [hinv] at h
    simpa using h.symm
theorem relabelInvertPreservesHaar_holds (hF : HaarExpChartProperties) :
    RelabelInvertPreservesHaar := by
  intro M M' _ _ σ ε hσ hε
  obtain ⟨_⟩ := nonempty_fintype M
  obtain ⟨_⟩ := nonempty_fintype M'
  have hinv : Measure.map (fun U : specialUnitary => U⁻¹) haarProb = haarProb := hF.2.2.2
  let e : M ≃ M' := Equiv.ofBijective σ hσ
  have he : ∀ b, e b = σ b := fun _ => rfl
  have hcont : Continuous (relabelInvert σ ε) :=
    continuous_pi fun b => (continuous_apply (σ b)).zpow (ε b)
  have hhomeo : IsHomeomorph (relabelInvert σ ε) := by
    let h : (M' → specialUnitary) ≃ₜ (M → specialUnitary) :=
      { toFun := relabelInvert σ ε
        invFun := fun Y b' => Y (e.symm b') ^ ε (e.symm b')
        left_inv := fun X => by
          funext b'
          simp only [relabelInvert]
          rw [← he, e.apply_symm_apply, zpow_zpow_of_sign (hε _)]
        right_inv := fun Y => by
          funext b
          simp only [relabelInvert]
          rw [← he, e.symm_apply_apply, zpow_zpow_of_sign (hε _)]
        continuous_toFun := hcont
        continuous_invFun :=
          continuous_pi fun b' => (continuous_apply (e.symm b')).zpow (ε (e.symm b')) }
    exact h.isHomeomorph
  have hmeas : Measurable (relabelInvert σ ε) :=
    measurable_pi_lambda _ fun b =>
      ((continuous_zpow (ε b)).measurable).comp (measurable_pi_apply (σ b))
  have hpi : ∀ (ι : Type) [Fintype ι], haarPi ι = Measure.pi fun _ : ι => haarProb := by
    intro ι _
    unfold haarPi
    exact Measure.infinitePi_eq_pi _
  have hmap : Measure.map (relabelInvert σ ε) (haarPi M') = haarPi M := by
    rw [hpi M, hpi M']
    symm
    refine Measure.pi_eq fun s hs => ?_
    rw [Measure.map_apply hmeas (MeasurableSet.univ_pi hs)]
    have hpre : relabelInvert σ ε ⁻¹' Set.pi Set.univ s =
        Set.pi Set.univ fun b' =>
          (fun x : specialUnitary => x ^ ε (e.symm b')) ⁻¹' s (e.symm b') := by
      ext X
      simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_true_left, relabelInvert]
      constructor
      · intro h b'
        have := h (e.symm b')
        rwa [← he, e.apply_symm_apply] at this
      · intro h b
        have := h (e b)
        rwa [e.symm_apply_apply] at this
    rw [hpre, Measure.pi_pi, ← e.prod_comp]
    refine Finset.prod_congr rfl fun b _ => ?_
    rw [e.symm_apply_apply]
    exact haarProb_preimage_zpow_sign hinv (hε b) (hs b)
  refine ⟨hhomeo, fun Φ hΦ _ => ?_⟩
  rw [← hmap]
  exact (integral_map hmeas.aemeasurable hΦ.aestronglyMeasurable).symm
end YangMills.Construction.Matrices.ComplexMatrix2.HaarRelabel
