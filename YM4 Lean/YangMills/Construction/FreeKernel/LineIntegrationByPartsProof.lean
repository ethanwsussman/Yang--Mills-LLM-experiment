import YangMills.Construction.FreeKernel.LineIntegrationByParts
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.FreeKernel.LineIntegration
open Complex MeasureTheory Filter Topology
lemma norm_character (ξ θ : ℝ) : ‖Complex.exp (I * (ξ : ℂ) * (θ : ℂ))‖ = 1 := by
  have h : I * (ξ : ℂ) * (θ : ℂ) = ((ξ * θ : ℝ) : ℂ) * I := by
    push_cast
    ring
  rw [h, Complex.norm_exp_ofReal_mul_I]
lemma integrable_character_mul (ξ : ℝ) {g : ℝ → ℂ} (hg : Integrable g) :
    Integrable (fun θ : ℝ => Complex.exp (I * (ξ : ℂ) * (θ : ℂ)) * g θ) := by
  have hc : Continuous (fun θ : ℝ => Complex.exp (I * (ξ : ℂ) * (θ : ℂ))) := by
    fun_prop
  refine hg.mono (hc.aestronglyMeasurable.mul hg.aestronglyMeasurable) (ae_of_all _ fun θ => ?_)
  rw [norm_mul, norm_character, one_mul]
lemma integral_character_mul_eq_deriv {ξ : ℝ} (hξ : ξ ≠ 0) {g g' : ℝ → ℂ}
    (hderiv : ∀ θ, HasDerivAt g (g' θ) θ) (hg : Integrable g) (hg' : Integrable g') :
    ∫ θ : ℝ, Complex.exp (I * (ξ : ℂ) * (θ : ℂ)) * g θ =
      (I / (ξ : ℂ)) * ∫ θ : ℝ, Complex.exp (I * (ξ : ℂ) * (θ : ℂ)) * g' θ := by
  have hexp : ∀ θ : ℝ, HasDerivAt (fun t : ℝ => Complex.exp (I * (ξ : ℂ) * (t : ℂ)))
      (Complex.exp (I * (ξ : ℂ) * (θ : ℂ)) * (I * (ξ : ℂ))) θ := by
    intro θ
    have hlin : HasDerivAt (fun t : ℝ => I * (ξ : ℂ) * (t : ℂ)) (I * (ξ : ℂ)) θ := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := θ)).const_mul (I * (ξ : ℂ))
    exact hlin.cexp
  have hprod : ∀ θ : ℝ, HasDerivAt (fun t : ℝ => Complex.exp (I * (ξ : ℂ) * (t : ℂ)) * g t)
      ((I * (ξ : ℂ)) * (Complex.exp (I * (ξ : ℂ) * (θ : ℂ)) * g θ) +
        Complex.exp (I * (ξ : ℂ) * (θ : ℂ)) * g' θ) θ := by
    intro θ
    have h : HasDerivAt (fun t : ℝ => Complex.exp (I * (ξ : ℂ) * (t : ℂ)) * g t) _ θ :=
      (hexp θ).mul (hderiv θ)
    convert h using 1
    ring
  have hi₁ := integrable_character_mul ξ hg
  have hi₂ := integrable_character_mul ξ hg'
  have hzero := integral_eq_zero_of_hasDerivAt_of_integrable hprod ((hi₁.const_mul _).add hi₂) hi₁
  rw [integral_add (hi₁.const_mul _) hi₂, integral_const_mul] at hzero
  generalize (∫ θ : ℝ, Complex.exp (I * (ξ : ℂ) * (θ : ℂ)) * g θ) = A at hzero ⊢
  generalize (∫ θ : ℝ, Complex.exp (I * (ξ : ℂ) * (θ : ℂ)) * g' θ) = B at hzero ⊢
  have hξc : (ξ : ℂ) ≠ 0 := by exact_mod_cast hξ
  have hB : B = -(I * (ξ : ℂ) * A) := by linear_combination hzero
  have hII : I * I = -1 := Complex.I_mul_I
  rw [hB]
  field_simp
  linear_combination A * hII
theorem lineFourierIntegrationByParts_proof : LineFourierIntegrationByParts := by
  intro n σ ξ hξ hσ hint
  have key : ∀ k : ℕ, k ≤ n →
      ∫ θ : ℝ, Complex.exp (I * (ξ : ℂ) * (θ : ℂ)) * σ θ =
        (I / (ξ : ℂ)) ^ k * ∫ θ : ℝ, Complex.exp (I * (ξ : ℂ) * (θ : ℂ)) * iteratedDeriv k σ θ := by
    intro k
    induction k with
    | zero =>
      intro _
      simp [iteratedDeriv_zero]
    | succ k ih =>
      intro hk
      have hlt : k < n := hk
      have hdiff : Differentiable ℝ (iteratedDeriv k σ) :=
        hσ.differentiable_iteratedDeriv k (by exact_mod_cast hlt)
      have hint' : Integrable (deriv (iteratedDeriv k σ)) := by
        rw [← iteratedDeriv_succ]
        exact (hint (k + 1) hk).1
      have hstep := integral_character_mul_eq_deriv hξ (fun θ => (hdiff θ).hasDerivAt)
        (hint k hlt.le).1 hint'
      rw [ih hlt.le, hstep, iteratedDeriv_succ, pow_succ, mul_assoc]
  exact key n le_rfl
end YangMills.Construction.FreeKernel.LineIntegration
end
