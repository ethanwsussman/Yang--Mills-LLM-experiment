import YangMills.Construction.Towers.ChargedSymbolAtTheOrigin
import YangMills.Construction.Towers.FirstCoefficientOnTheGaugeColumn
import YangMills.Construction.Towers.SumsAndProductsOfSymbols
import Mathlib
set_option autoImplicit false
open Filter Topology
open YangMills.Construction.InfiniteLattice (AmbientSpace)
noncomputable section
namespace YangMills.Construction.Tower.ConstantFieldSymbols
open MagneticWeyl
namespace Origin
def axisPt (ν : Fin 4) (s : ℝ) : AmbientSpace := fun μ => if μ = ν then s else 0
theorem continuous_axisPt (ν : Fin 4) : Continuous (axisPt ν) := by
  refine continuous_pi fun μ => ?_
  by_cases h : μ = ν
  · simpa [axisPt, h] using continuous_id'
  · simpa [axisPt, h] using continuous_const
theorem axisPt_zero (ν : Fin 4) : axisPt ν 0 = 0 := by
  funext μ
  simp [axisPt]
theorem hasDerivAt_exp_I_sub_one :
    HasDerivAt (fun s : ℝ => Complex.exp (Complex.I * (s : ℂ)) - 1) Complex.I 0 := by
  have h1 : HasDerivAt (fun s : ℝ => Complex.I * (s : ℂ)) Complex.I 0 := by
    simpa using (Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).const_mul Complex.I
  simpa using h1.cexp.sub_const 1
theorem entry_mul_I_eq_deriv (A : AmbientSpace → Matrix (Fin 4) (Fin 4) ℂ) (hA : Continuous A)
    (hrel : ∀ q, A q * gaugeSymbolColumn q = rotatedGaugeSymbolColumn q) (ν i : Fin 4) (c : ℂ)
    (hc : HasDerivAt (fun s : ℝ => rotatedGaugeSymbolColumn (axisPt ν s) i 0) c 0) :
    A 0 i ν * Complex.I = c := by
  have hval : ∀ s : ℝ, rotatedGaugeSymbolColumn (axisPt ν s) i 0 =
      A (axisPt ν s) i ν * (Complex.exp (Complex.I * (s : ℂ)) - 1) := by
    intro s
    rw [← hrel, Matrix.mul_apply, Finset.sum_eq_single ν]
    · simp [gaugeSymbolColumn, axisPt]
    · intro μ _ h
      simp [gaugeSymbolColumn, axisPt, h]
    · simp
  have hs1 := hasDerivAt_iff_tendsto_slope_zero.1 hc
  have hs2 := hasDerivAt_iff_tendsto_slope_zero.1 hasDerivAt_exp_I_sub_one
  have hA0 : Tendsto (fun t : ℝ => A (axisPt ν t) i ν) (𝓝[≠] 0) (𝓝 (A 0 i ν)) := by
    have hcont : Continuous fun t : ℝ => A (axisPt ν t) i ν :=
      (hA.comp (continuous_axisPt ν)).matrix_elem i ν
    have := hcont.tendsto 0
    rw [axisPt_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hlim := hA0.mul hs2
  refine tendsto_nhds_unique (hlim.congr fun t => ?_) hs1
  simp only [zero_add, hval, Complex.ofReal_zero, mul_zero, Complex.exp_zero, sub_self, sub_zero,
    Complex.real_smul, Complex.ofReal_inv]
  ring
end Origin
open Origin in
theorem chargedSymbolTraceSqAtZero_holds (hcolumn : FirstCoeffOnGaugeColumn)
    (hsymbols : MagneticWeyl.SymbolAlgebra.Claim) : ChargedSymbolTraceSqAtZero := by
  intro D C σ₁ σ₂ σ σr h
  have hrel := hcolumn D C σ₁ σ₂ σ σr h
  have hcont : Continuous σ₁ :=
    ((hsymbols 4 4 4).2.1.2.2.2 σ₁ h.linear_isFiniteFourierSymbol.1).2.2.2.1
  have hzero : ∀ ν i : Fin 4, ¬(ν = 1 ∧ i = 0) → ¬(ν = 0 ∧ i = 1) → σ₁ 0 i ν = 0 := by
    intro ν i h1 h2
    have hf : (fun s : ℝ => rotatedGaugeSymbolColumn (axisPt ν s) i 0) = fun _ => 0 := by
      funext s
      fin_cases ν <;> fin_cases i <;> simp_all [rotatedGaugeSymbolColumn, axisPt]
    have hd : HasDerivAt (fun s : ℝ => rotatedGaugeSymbolColumn (axisPt ν s) i 0) 0 0 := by
      rw [hf]
      exact hasDerivAt_const _ _
    have := entry_mul_I_eq_deriv σ₁ hcont hrel ν i 0 hd
    simpa using this
  have h01 : σ₁ 0 0 1 = -2 * Complex.I := by
    have hf : (fun s : ℝ => rotatedGaugeSymbolColumn (axisPt 1 s) 0 0) =
        fun s : ℝ => ((2 * Real.sin s : ℝ) : ℂ) := by
      funext s
      simp [rotatedGaugeSymbolColumn, axisPt]
    have hd : HasDerivAt (fun s : ℝ => rotatedGaugeSymbolColumn (axisPt 1 s) 0 0) 2 0 := by
      rw [hf]
      simpa using ((Real.hasDerivAt_sin 0).const_mul 2).ofReal_comp
    have := entry_mul_I_eq_deriv σ₁ hcont hrel 1 0 2 hd
    apply mul_right_cancel₀ Complex.I_ne_zero
    rw [this, mul_assoc, Complex.I_mul_I]
    norm_num
  have h10 : σ₁ 0 1 0 = 2 * Complex.I := by
    have hf : (fun s : ℝ => rotatedGaugeSymbolColumn (axisPt 0 s) 1 0) =
        fun s : ℝ => -((2 * Real.sin s : ℝ) : ℂ) := by
      funext s
      simp [rotatedGaugeSymbolColumn, axisPt]
    have hd : HasDerivAt (fun s : ℝ => rotatedGaugeSymbolColumn (axisPt 0 s) 1 0) (-2) 0 := by
      rw [hf]
      simpa using (((Real.hasDerivAt_sin 0).const_mul 2).ofReal_comp).fun_neg
    have := entry_mul_I_eq_deriv σ₁ hcont hrel 0 1 (-2) hd
    apply mul_right_cancel₀ Complex.I_ne_zero
    rw [this, mul_assoc, Complex.I_mul_I]
    norm_num
  have hz : ∀ i ν : Fin 4, (i, ν) ≠ (0, 1) → (i, ν) ≠ (1, 0) → σ₁ 0 i ν = 0 := by
    intro i ν h1 h2
    refine hzero ν i (fun h => h1 ?_) (fun h => h2 ?_) <;> simp [h.1, h.2]
  simp only [Matrix.trace, pow_two, Matrix.diag, Matrix.mul_apply, Fin.sum_univ_four]
  rw [h01, h10]
  simp only [hz 0 0 (by decide) (by decide), hz 0 2 (by decide) (by decide),
    hz 0 3 (by decide) (by decide), hz 1 1 (by decide) (by decide),
    hz 1 2 (by decide) (by decide), hz 1 3 (by decide) (by decide),
    hz 2 0 (by decide) (by decide), hz 2 1 (by decide) (by decide),
    hz 2 2 (by decide) (by decide), hz 2 3 (by decide) (by decide),
    hz 3 0 (by decide) (by decide), hz 3 1 (by decide) (by decide),
    hz 3 2 (by decide) (by decide), hz 3 3 (by decide) (by decide)]
  ring_nf
  simp
end YangMills.Construction.Tower.ConstantFieldSymbols
end
