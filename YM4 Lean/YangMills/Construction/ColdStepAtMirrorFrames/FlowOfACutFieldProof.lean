import YangMills.Construction.ColdStepAtMirrorFrames.FlowOfACutField
import YangMills.Construction.ColdStepAtMirrorFrames.PlaquetteOfACutField
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages
namespace ColdStepAtMirrorFrames
namespace CutoffFlow
open BlockOffsets
variable {F : BlockFrame}
theorem plaquetteHolonomy_leftTranslate_uniform {j : ℕ} (Z : F.Site j → Fin 4 → imaginaryQuaternions)
    (p : F.Site j × Fin 4 × Fin 4) :
    plaquetteHolonomy (leftTranslate Z (uniformField F j)) p =
      fourPlaquette fun l => Z (plaquetteBondList p l).1 (plaquetteBondList p l).2 := by
  obtain ⟨x, μ, ν⟩ := p
  have hμν : x + unitStep j μ + unitStep j ν - unitStep j μ = x + unitStep j ν := by abel
  have hμν' : x + unitStep j μ + unitStep j ν + -unitStep j μ = x + unitStep j ν := by abel
  have hν : x + unitStep j ν - unitStep j ν = x := by abel
  simp only [plaquetteHolonomy, pathHolonomy, linkValue, stepDisplacement, if_true, Bool.false_eq_true,
    if_false, leftTranslate, uniformField, hμν, hμν', hν, mul_one, fourPlaquette, plaquetteBondList]
  simp [mul_assoc]
theorem plaquetteHolonomy_eq_of_expUnit {j : ℕ} (U : F.GaugeField j)
    (A : F.Site j → Fin 4 → imaginaryQuaternions) (p : F.Site j × Fin 4 × Fin 4)
    (h : ∀ l, U (plaquetteBondList p l).1 (plaquetteBondList p l).2 =
      expUnit (A (plaquetteBondList p l).1 (plaquetteBondList p l).2)) :
    plaquetteHolonomy U p = fourPlaquette fun l => A (plaquetteBondList p l).1 (plaquetteBondList p l).2 := by
  obtain ⟨x, μ, ν⟩ := p
  have hμν : x + unitStep j μ + unitStep j ν - unitStep j μ = x + unitStep j ν := by abel
  have hμν' : x + unitStep j μ + unitStep j ν + -unitStep j μ = x + unitStep j ν := by abel
  have hν : x + unitStep j ν - unitStep j ν = x := by abel
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  simp only [plaquetteBondList, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at h0 h1 h2 h3
  simp only [plaquetteHolonomy, pathHolonomy, linkValue, stepDisplacement, if_true, Bool.false_eq_true,
    if_false, hμν, hμν', hν, mul_one, fourPlaquette, plaquetteBondList]
  simp [h0, h1, h2, h3, mul_assoc]
end CutoffFlow
open CutoffFlow
open BlockOffsets
theorem cutoffFlowSmallCurvature_holds (hcut : ScaledPlaquetteBound) : CutoffFlowSmallCurvature := by
  intro F j U A χ σ hσ hχ hp u hu0 hu1 p hpp
  have hexp0 : expUnit 0 = 1 := by
    apply Subtype.ext
    show NormedSpace.exp (((0 : imaginaryQuaternions)) : Quaternion ℝ) = 1
    simp
  have hflow : expFlow (fun y i => χ y i • A y i) (uniformField F j) u =
      leftTranslate (fun y i => (u * χ y i) • A y i) (uniformField F j) := by
    funext y i
    simp [expFlow, leftTranslate, smul_smul]
  rw [hflow]
  show plaquetteDefect _ p < σ
  unfold plaquetteDefect
  rw [plaquetteHolonomy_leftTranslate_uniform]
  rcases hp p hpp with hzero | ⟨hU, hsmall, hbound⟩
  · have : (fun l => (u * χ (plaquetteBondList p l).1 (plaquetteBondList p l).2) •
        A (plaquetteBondList p l).1 (plaquetteBondList p l).2) = fun _ => 0 := by
      funext l
      rw [hzero l]
      simp
    rw [this]
    simp [fourPlaquette, hexp0, hσ]
  · have hc := hcut (fun l => A (plaquetteBondList p l).1 (plaquetteBondList p l).2)
      (fun l => u * χ (plaquetteBondList p l).1 (plaquetteBondList p l).2)
      (fun l => ⟨mul_nonneg hu0 (hχ _ _).1, by nlinarith [(hχ (plaquetteBondList p l).1 (plaquetteBondList p l).2).1,
        (hχ (plaquetteBondList p l).1 (plaquetteBondList p l).2).2]⟩) hsmall
    have hcurv : distFromOne (fourPlaquette fun l => A (plaquetteBondList p l).1 (plaquetteBondList p l).2) =
        plaquetteDefect U p := by
      rw [← plaquetteHolonomy_eq_of_expUnit U A p hU]
      rfl
    rw [hcurv] at hc
    have hK : 0 ≤ plaquetteDefect U p := norm_nonneg _
    have hle : u * χ (plaquetteBondList p 0).1 (plaquetteBondList p 0).2 ≤ 1 := by
      nlinarith [(hχ (plaquetteBondList p 0).1 (plaquetteBondList p 0).2).1,
        (hχ (plaquetteBondList p 0).1 (plaquetteBondList p 0).2).2]
    have hscaled : (u * χ (plaquetteBondList p 0).1 (plaquetteBondList p 0).2) * plaquetteDefect U p ≤
        plaquetteDefect U p := by
      nlinarith
    have hsum : ∑ l, |u * χ (plaquetteBondList p l).1 (plaquetteBondList p l).2 -
          u * χ (plaquetteBondList p 0).1 (plaquetteBondList p 0).2| *
          ‖A (plaquetteBondList p l).1 (plaquetteBondList p l).2‖ ≤
        ∑ l, |χ (plaquetteBondList p l).1 (plaquetteBondList p l).2 - χ p.1 p.2.1| *
          ‖A (plaquetteBondList p l).1 (plaquetteBondList p l).2‖ := by
      refine Finset.sum_le_sum fun l _ => mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      rw [← mul_sub, abs_mul, abs_of_nonneg hu0]
      have : (plaquetteBondList p 0).1 = p.1 ∧ (plaquetteBondList p 0).2 = p.2.1 := ⟨rfl, rfl⟩
      rw [this.1, this.2]
      nlinarith [abs_nonneg (χ (plaquetteBondList p l).1 (plaquetteBondList p l).2 - χ p.1 p.2.1)]
    show distFromOne _ < σ
    linarith
end ColdStepAtMirrorFrames
end YangMills.Construction
end
