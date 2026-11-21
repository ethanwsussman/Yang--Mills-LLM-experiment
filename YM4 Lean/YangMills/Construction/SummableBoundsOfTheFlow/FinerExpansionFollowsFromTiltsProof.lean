import YangMills.Construction.SummableBoundsOfTheFlow.TheFinerExpansionReturnsProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.BlockMeans
open YangMills.Construction.TorusLumps YangMills.Construction.FamilyNorms YangMills.Construction.BlockAverages
private theorem thirdOrderSize_le_of_le {ℓ : StepParameters} (h : ℓ.Admissible) {ε ε' : ℝ} (hε : ε ≤ ε') :
    thirdOrderSize ℓ ε ≤ thirdOrderSize ℓ ε' := by apply _root_.YangMills.SharedProofs.p37405 <;> assumption
private theorem thirdOrderSize_nonneg {ℓ : StepParameters} (h : ℓ.Admissible) {ε : ℝ} (hε : 0 ≤ ε) :
    0 ≤ thirdOrderSize ℓ ε := by
  unfold thirdOrderSize
  exact div_nonneg (mul_nonneg hε h.E₃_pos.le) h.E_pos.le
private theorem thirdOrderSize_half {ℓ : StepParameters} (h : ℓ.Admissible) :
    thirdOrderSize ℓ (ℓ.E / 2) = ℓ.E₃ / 2 := by
  unfold thirdOrderSize
  have hE : ℓ.E ≠ 0 := h.E_pos.ne'
  field_simp
private theorem isCurvatureFreeTilt_mono (hs : normBoundedFamilyClosureStatement) {ℓ : StepParameters}
    (hf : ℓ.Admissible) {t : ℕ} {x : ℝ}
    {D : TorusFunctional} {f h : LocalDensity} {ε ε' : ℝ} (hε : ε ≤ ε')
    (H : IsCurvatureFreeTilt ℓ t x D f h ε) :
    IsCurvatureFreeTilt ℓ t x D f h ε' :=
  ⟨(hs ℓ).1 _ _ _ _ _ hε (thirdOrderSize_le_of_le hf hε) H.normBounded, H.curvatureForm_vanishes,
    H.log_density_eq⟩
theorem refinedExpansionOfTilt_of_closure (hs : normBoundedFamilyClosureStatement) :
    refinedExpansionOfTilt := by
  intro ℓ f b d yp C₁ hadm hret hC hy1 hyB hyl hyE hf htilt t x D hx hD
  obtain ⟨hrow, h, hT⟩ := hD
  have hx1 : 1 ≤ x := hy1.trans hx
  have hx0 : 0 < x := by linarith
  have hyp0 : 0 < yp := by linarith
  set ε : ℝ := 2 * C₁ * x ^ (-(3 / 4 : ℝ)) with hεdef
  have hxp : 0 < x ^ (-(3 / 4 : ℝ)) := Real.rpow_pos_of_pos hx0 _
  have hε : 0 < ε := by positivity
  have hεE : ε ≤ ℓ.E / 2 := by
    refine le_trans ?_ hyE
    have : x ^ (-(3 / 4 : ℝ)) ≤ yp ^ (-(3 / 4 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos hyp0 hx (by norm_num)
    rw [hεdef]
    exact mul_le_mul_of_nonneg_left this (by positivity)
  have hθ : ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 → IsNormBoundedFamily ℓ ℓ.E ℓ.E₃ (f t + θ • h) := by
    intro θ h0 h1
    have a := (hs ℓ).2.2.1 θ _ _ _ hT.normBounded
    have c := (hs ℓ).2.1 _ _ _ _ _ _ (hf t) a
    have e1 : |θ| * ε ≤ ℓ.E / 2 := by
      rw [abs_of_nonneg h0]
      nlinarith
    have e3 : |θ| * thirdOrderSize ℓ ε ≤ ℓ.E₃ / 2 := by
      rw [abs_of_nonneg h0]
      have a1 : thirdOrderSize ℓ ε ≤ ℓ.E₃ / 2 := by
        rw [← thirdOrderSize_half hadm]; exact thirdOrderSize_le_of_le hadm hεE
      have a2 := thirdOrderSize_nonneg hadm hε.le
      nlinarith
    exact (hs ℓ).1 _ _ _ _ _ (by linarith) (by linarith) c
  obtain ⟨x', h', hrow', hT', hb⟩ := htilt t x D ε h hx hε hrow hT hθ
  obtain ⟨x₁, ⟨hr₁, hb₁⟩, hu⟩ := hret t x D (hyl.trans hx) hrow
  have hxx : x' = x₁ := by
    obtain ⟨-, f'', hc, -⟩ := hrow'
    exact hu x' f'' hc
  have hB : 0 < ℓ.B := hadm.B_pos
  have hmove : |x' - x| ≤ 2 * ℓ.B := hxx ▸ hb₁
  have hmove' := abs_le.mp hmove
  have hx'0 : 0 < x' := by linarith [hmove'.1]
  have hx'le : x' ≤ 1.01 * x := by linarith [hmove'.2]
  refine ⟨x', ⟨hrow', h', ?_⟩, ?_⟩
  · refine isCurvatureFreeTilt_mono hs hadm ?_ hT'
    have k1 : (1.01 * x) ^ (-(3 / 4 : ℝ)) ≤ x' ^ (-(3 / 4 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos hx'0 hx'le (by norm_num)
    have k2 : (1.01 * x) ^ (-(3 / 4 : ℝ)) = (1.01 : ℝ) ^ (-(3 / 4 : ℝ)) * x ^ (-(3 / 4 : ℝ)) :=
      Real.mul_rpow (by norm_num) hx0.le
    have k3 : (5 / 8 : ℝ) ≤ (1.01 : ℝ) ^ (-(3 / 4 : ℝ)) := by
      have : (1.01 : ℝ) ^ (-(1 : ℝ)) ≤ (1.01 : ℝ) ^ (-(3 / 4 : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      refine le_trans ?_ this
      rw [Real.rpow_neg_one]
      norm_num
    have k4 : (5 / 8 : ℝ) * x ^ (-(3 / 4 : ℝ)) ≤ x' ^ (-(3 / 4 : ℝ)) := by
      refine le_trans ?_ k1
      rw [k2]
      exact mul_le_mul_of_nonneg_right k3 hxp.le
    rw [hεdef]
    nlinarith
  · refine hb.trans ?_
    have m1 : x ^ (-(1 / 2 : ℝ)) * x ^ (-(3 / 4 : ℝ)) = x ^ (-(5 / 4 : ℝ)) := by
      rw [← Real.rpow_add hx0]; norm_num
    have m2 : x ^ (-(3 / 2 : ℝ)) ≤ x ^ (-(5 / 4 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
    have m3 : x ^ (-(1 / 2 : ℝ)) * ε = 2 * C₁ * x ^ (-(5 / 4 : ℝ)) := by
      rw [hεdef, ← m1]; ring
    rw [m3]
    nlinarith
end YangMills.Construction.BlockMeans
end
