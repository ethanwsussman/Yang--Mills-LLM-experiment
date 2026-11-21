import YangMills.Construction.OneLoopLaw.CoefficientOfATemperedFunctional
import YangMills.Construction.Towers.CompositionOfATemperedFunctionalWithAStep
import YangMills.Construction.Towers.CompositionWithAStepIsAFunctional
import YangMills.Construction.Towers.SymbolOfACompositionNearZero
import YangMills.Construction.Towers.TemperingDataOfACompositionWithAStep
import Mathlib
set_option autoImplicit false
open Filter Asymptotics
open scoped Topology
noncomputable section
namespace YangMills.Construction.TemperedComposition
open YangMills.Construction.PeriodicOperators.Tempered
open YangMills.Construction.InfiniteLattice (AmbientSpace)
open YangMills.Construction.PeriodicOperators (toComplexVec)
open YangMills.Construction.TorusMetric (euclidNormVec)
open YangMills.Construction.OneLoopLaw.TemperedStiffness (HasTransverseForm transverseTensor)
def diagSum : AmbientSpace := fun ρ => if ρ = 0 ∨ ρ = 1 then 1 else 0
theorem eq_zero_of_mul_sq_isBigO_cube (c : ℂ)
    (h : (fun θ : ℝ => c * (θ : ℂ) ^ 2) =O[𝓝 0] fun θ : ℝ => θ ^ 3) : c = 0 := by
  have h1 : (fun θ : ℝ => θ ^ 3) =o[𝓝 0] fun θ : ℝ => θ ^ 2 :=
    isLittleO_pow_pow (by norm_num)
  have h2 := h.trans_isLittleO h1
  by_contra hc
  have hn : 0 < ‖c‖ := norm_pos_iff.mpr hc
  have h3 := h2.def (half_pos hn)
  have h4 : ∀ᶠ θ : ℝ in 𝓝[≠] 0, ‖c * (θ : ℂ) ^ 2‖ ≤ ‖c‖ / 2 * ‖θ ^ 2‖ := nhdsWithin_le_nhds h3
  obtain ⟨θ, hθ, hne⟩ := (h4.and self_mem_nhdsWithin).exists
  have hp : 0 < |θ| ^ 2 := by
    have : θ ≠ 0 := hne
    positivity
  simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs] at hθ
  nlinarith
theorem euclidNormVec_smul_diagSum_sq (s : ℝ) : euclidNormVec (s • diagSum) ^ 2 = 2 * s ^ 2 := by
  rw [euclidNormVec, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  simp [Fin.sum_univ_four, diagSum]
  ring
theorem euclidNormVec_smul_diagSum_pow_four (s : ℝ) :
    euclidNormVec (s • diagSum) ^ 4 = 4 * s ^ 4 := by
  calc euclidNormVec (s • diagSum) ^ 4 = (euclidNormVec (s • diagSum) ^ 2) ^ 2 := by ring
    _ = 4 * s ^ 4 := by rw [euclidNormVec_smul_diagSum_sq]; ring
theorem euclidNormVec_smul_diagSum_pow_three_le (s : ℝ) :
    euclidNormVec (s • diagSum) ^ 3 ≤ 8 * |s| ^ 3 := by
  have h0 : 0 ≤ euclidNormVec (s • diagSum) := Real.sqrt_nonneg _
  have h1 : euclidNormVec (s • diagSum) ≤ 2 * |s| := by
    refine (pow_le_pow_iff_left₀ h0 (by positivity) (two_ne_zero)).mp ?_
    rw [euclidNormVec_smul_diagSum_sq, mul_pow, sq_abs]
    nlinarith [sq_nonneg s]
  calc euclidNormVec (s • diagSum) ^ 3 ≤ (2 * |s|) ^ 3 := pow_le_pow_left₀ h0 h1 3
    _ = 8 * |s| ^ 3 := by ring
theorem transverse_at_smul_diagSum (f : (Fin 4 → ℂ) → ℂ) (β s : ℝ) :
    Complex.exp (Complex.I * ((((s • diagSum) 0 - (s • diagSum) 1) / 2 : ℝ) : ℂ)) *
        f (toComplexVec (s • diagSum)) - (transverseTensor β 0 1 (s • diagSum) : ℂ) =
      f (toComplexVec (s • diagSum)) + (β : ℂ) * (s : ℂ) ^ 2 := by
  have e0 : (s • diagSum) 0 = s := by simp [diagSum]
  have e1 : (s • diagSum) 1 = s := by simp [diagSum]
  have h : transverseTensor β 0 1 (s • diagSum) = -(β * s ^ 2) := by
    simp only [transverseTensor, e0, e1, if_neg (show ¬(0 : Fin 4) = 1 by decide)]
    ring
  rw [e0, e1, h]
  simp
theorem pow_four_isBigO_cube_along (c : ℝ) :
    (fun θ : ℝ => euclidNormVec ((c * θ) • diagSum) ^ 4) =O[𝓝 0] fun θ : ℝ => θ ^ 3 := by
  have h1 : (fun θ : ℝ => euclidNormVec ((c * θ) • diagSum) ^ 4) =O[𝓝 0]
      fun θ : ℝ => θ ^ 4 := by
    refine IsBigO.of_bound (4 * c ^ 4) (Eventually.of_forall fun θ => ?_)
    rw [euclidNormVec_smul_diagSum_pow_four, mul_pow, Real.norm_eq_abs, Real.norm_eq_abs]
    rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
    ring_nf
    exact le_refl _
  exact h1.trans (isLittleO_pow_pow (by norm_num)).isBigO
theorem tendsto_smul_diagSum (c : ℝ) :
    Tendsto (fun θ : ℝ => (c * θ) • diagSum) (𝓝 0) (𝓝 0) := by
  have : Continuous fun θ : ℝ => (c * θ) • diagSum := by fun_prop
  simpa using this.tendsto 0
theorem exists_symbol_bound {L : ℕ} {F : FieldFamily L} {δ : ℝ} {π : SymbolArray} {e : ℕ → ℝ}
    (hc : IsTemperedWitness L F δ π e) :
    ∃ C : ℝ, ∀ (ρ σ : Fin 4) (q : AmbientSpace), ‖π ρ σ (toComplexVec q)‖ ≤ C := by
  obtain ⟨O, hO, hol⟩ := hc.analytic
  choose C hC using fun μ ν => (hol μ ν).2
  refine ⟨∑ μ, ∑ ν, |C μ ν|, fun ρ σ q => ?_⟩
  have hq : toComplexVec q ∈ O := hO fun μ => by
    simpa [toComplexVec] using hc.delta_pos.le
  calc ‖π ρ σ (toComplexVec q)‖ ≤ C ρ σ := hC ρ σ _ hq
    _ ≤ |C ρ σ| := le_abs_self _
    _ ≤ ∑ ν, |C ρ ν| :=
      Finset.single_le_sum (f := fun ν => |C ρ ν|) (fun _ _ => abs_nonneg _) (Finset.mem_univ σ)
    _ ≤ ∑ μ, ∑ ν, |C μ ν| :=
      Finset.single_le_sum (f := fun μ => ∑ ν, |C μ ν|)
        (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ ρ)
theorem stiffness_eq_of_rescaled {L : ℕ} (hL : 0 < L) (π π' : SymbolArray) (β β' : ℝ)
    (hT : HasTransverseForm π β) (hT' : HasTransverseForm π' β')
    (hN : (fun p : AmbientSpace => π' 0 1 (toComplexVec p) -
        (L : ℂ) ^ 2 * π 0 1 (toComplexVec ((L : ℝ)⁻¹ • p))) =O[𝓝 0]
      fun p => euclidNormVec p ^ 3) : β' = β := by
  have hL0 : (L : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
  have hA := ((hT' 0 1).comp_tendsto (tendsto_smul_diagSum 1)).trans
    (pow_four_isBigO_cube_along 1)
  have hB := ((hT 0 1).comp_tendsto (tendsto_smul_diagSum (L : ℝ)⁻¹)).trans
    (pow_four_isBigO_cube_along (L : ℝ)⁻¹)
  have hC : (fun θ : ℝ => π' 0 1 (toComplexVec ((1 * θ) • diagSum)) -
      (L : ℂ) ^ 2 * π 0 1 (toComplexVec (((L : ℝ)⁻¹ * θ) • diagSum))) =O[𝓝 0]
      fun θ : ℝ => θ ^ 3 := by
    have h1 := hN.comp_tendsto (tendsto_smul_diagSum 1)
    have h2 : ((fun p : AmbientSpace => euclidNormVec p ^ 3) ∘ fun θ : ℝ => (1 * θ) • diagSum)
        =O[𝓝 0] fun θ : ℝ => θ ^ 3 := by
      refine IsBigO.of_bound 8 (Eventually.of_forall fun θ => ?_)
      have h0 : 0 ≤ euclidNormVec ((1 * θ) • diagSum) := Real.sqrt_nonneg _
      simp only [Function.comp_apply, Real.norm_eq_abs, abs_pow, abs_of_nonneg h0]
      simpa using euclidNormVec_smul_diagSum_pow_three_le (1 * θ)
    refine (h1.trans h2).congr_left fun θ => ?_
    simp only [Function.comp_apply, smul_smul]
    simp
  have hZ : ((β' : ℂ) - β) = 0 := by
    refine eq_zero_of_mul_sq_isBigO_cube _ ?_
    have hB' := hB.const_mul_left ((L : ℂ) ^ 2)
    refine ((hA.sub hC).sub hB').congr_left fun θ => ?_
    simp only [Function.comp_apply]
    rw [transverse_at_smul_diagSum (π' 0 1) β' (1 * θ),
      transverse_at_smul_diagSum (π 0 1) β ((L : ℝ)⁻¹ * θ)]
    push_cast
    field_simp
    ring
  exact_mod_cast sub_eq_zero.mp hZ
theorem temperedCompStep_holds
    (hCoef : YangMills.Construction.OneLoopLaw.TemperedStiffness.TemperedStiffnessClaim)
    (hFun : YangMills.Construction.PeriodicOperators.Tempered.CompStepPreservesFunctionals)
    (hData : YangMills.Construction.Tower.TemperedComposition.CompStepTemperedWitnessExists)
    (hNear : YangMills.Construction.Tower.StepSymbolNearZero.Claim) :
    YangMills.Construction.TemperedComposition.TemperedCompStep := by
  intro L hL hS F i hF
  obtain ⟨hFF, δ, π, e, hc⟩ := hF
  have hG := hFun L hL hS F i hFF
  obtain ⟨δ', C, hc'⟩ := hData L hL hS F δ π e i hFF hc
  refine ⟨⟨hG, δ', _, _, hc'⟩, ?_⟩
  obtain ⟨-, -, -, β, hT, -, hform⟩ := hCoef L hL hS F δ π e hFF hc
  obtain ⟨-, -, -, β', hT', -, hform'⟩ := hCoef L hL hS _ δ' _ _ hG hc'
  have h01 : (0 : Fin 4) ≠ 1 := by decide
  rw [(hform 0 1 h01).eq_coeff, (hform' 0 1 h01).eq_coeff]
  exact stiffness_eq_of_rescaled hL _ _ β β' hT hT'
    (hNear L hS π β i (exists_symbol_bound hc) hT 0 1)
end YangMills.Construction.TemperedComposition
end
