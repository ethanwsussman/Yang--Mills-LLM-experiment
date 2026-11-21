import YangMills.Construction.SpectralTheory.BoundedBorelCalculus
import YangMills.Construction.SpectralTheory.CommutationWithBoundedIntegrals
import Mathlib
set_option autoImplicit false
open MeasureTheory Set Filter Topology
noncomputable section
namespace YangMills.Construction.SpectralTheory.BoundedIntegralCommutation
open BorelSpectral BorelCalculus
variable {n : ℕ} {Y : Set (Fin n → ℝ)} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]
theorem commute_integralOp_simpleFunc {E : SpectralMeasure Y H} (hE : BoundedFunctionalCalculus E)
    {T : H →L[ℂ] H} (hT : ∀ Δ, Commute T (E Δ)) (f : SimpleFunc Y ℂ) :
    Commute T (E.integralOp f) := by
  induction f using SimpleFunc.induction with
  | @const z s hs =>
    have hf : ((SimpleFunc.piecewise s hs (SimpleFunc.const _ z) (SimpleFunc.const _ 0) :
        SimpleFunc Y ℂ) : Y → ℂ) = z • s.indicator 1 := by
      ext y
      by_cases hy : y ∈ s <;> simp [hy]
    have hmeas : Measurable (s.indicator (1 : Y → ℂ)) := measurable_one.indicator hs
    have hbdd : IsBoundedFn (s.indicator (1 : Y → ℂ)) := by
      refine ⟨1, fun y => ?_⟩
      by_cases hy : y ∈ s <;> simp [hy]
    have hval : E.integralOp (s.indicator 1) = E ⟨s, hs⟩ := hE.indicator ⟨s, hs⟩
    rw [hf, hE.smul z _ hmeas hbdd, hval]
    exact (hT ⟨s, hs⟩).smul_right z
  | @add f g _ hf hg =>
    rw [SimpleFunc.coe_add, hE.add _ _ f.measurable f.exists_forall_norm_le g.measurable
      g.exists_forall_norm_le]
    exact hf.add_right hg
theorem tendsto_integralOp_apply {E : SpectralMeasure Y H} (hE : BoundedFunctionalCalculus E)
    {u : ℕ → Y → ℂ} {g : Y → ℂ} {C : ℝ} (hum : ∀ k, Measurable (u k)) (hg : Measurable g)
    (hu : ∀ k y, ‖u k y‖ ≤ C) (hC : ∀ y, ‖g y‖ ≤ C)
    (hlim : ∀ y, Tendsto (fun k => u k y) atTop (𝓝 (g y))) (x : H) :
    Tendsto (fun k => E.integralOp (u k) x) atTop (𝓝 (E.integralOp g x)) := by
  have hgb : IsBoundedFn g := ⟨C, hC⟩
  have hub : ∀ k, IsBoundedFn (u k) := fun k => ⟨C, hu k⟩
  have hnegb : IsBoundedFn ((-1 : ℂ) • g) := ⟨C, fun y => by simpa using hC y⟩
  have hnegm : Measurable ((-1 : ℂ) • g) := hg.const_smul _
  have hnorm : ∀ k, ∫ y, ‖u k y - g y‖ ^ 2 ∂E.diagMeasure x =
      ‖E.integralOp (u k) x - E.integralOp g x‖ ^ 2 := by
    intro k
    have hdiff : u k + (-1 : ℂ) • g = fun y => u k y - g y := by
      ext y
      simp [sub_eq_add_neg]
    have hsm : Measurable (u k + (-1 : ℂ) • g) := (hum k).add hnegm
    have hsb : IsBoundedFn (u k + (-1 : ℂ) • g) := by
      refine ⟨C + C, fun y => ?_⟩
      rw [congrFun hdiff y]
      exact (norm_sub_le _ _).trans (add_le_add (hu k y) (hC y))
    have h := hE.norm_sq _ hsm hsb x
    rw [hE.add _ _ (hum k) (hub k) hnegm hnegb, hE.smul _ _ hg hgb, hdiff] at h
    rw [← h]
    simp [sub_eq_add_neg]
  have hint : Tendsto (fun k => ∫ y, ‖u k y - g y‖ ^ 2 ∂E.diagMeasure x) atTop (𝓝 0) := by
    have h := tendsto_integral_of_dominated_convergence (μ := E.diagMeasure x)
      (F := fun k y => ‖u k y - g y‖ ^ 2) (f := fun _ => (0 : ℝ)) (fun _ => (C + C) ^ 2)
      (fun k => (((hum k).sub hg).norm.pow_const 2).aestronglyMeasurable)
      (integrable_const _)
      (fun k => Eventually.of_forall fun y => by
        rw [Real.norm_of_nonneg (by positivity)]
        exact pow_le_pow_left₀ (norm_nonneg _)
          ((norm_sub_le _ _).trans (add_le_add (hu k y) (hC y))) 2)
      (Eventually.of_forall fun y => by
        have h₁ : Tendsto (fun k => u k y - g y) atTop (𝓝 0) := by
          simpa using (hlim y).sub_const (g y)
        simpa using (h₁.norm).pow 2)
    simpa using h
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have h₂ := (hint.congr hnorm).sqrt
  simpa [Real.sqrt_sq, norm_nonneg] using h₂
theorem commute_integralOp {E : SpectralMeasure Y H} (hE : BoundedFunctionalCalculus E)
    {T : H →L[ℂ] H} (hT : ∀ Δ, Commute T (E Δ)) (g : Y → ℂ) (hg : Measurable g)
    (hbdd : IsBoundedFn g) : Commute T (E.integralOp g) := by
  obtain ⟨C, hC⟩ := hbdd
  let u : ℕ → SimpleFunc Y ℂ := fun k => SimpleFunc.approxOn g hg univ 0 (mem_univ 0) k
  have hu : ∀ k y, ‖u k y‖ ≤ C + C := fun k y =>
    (SimpleFunc.norm_approxOn_zero_le hg (mem_univ 0) y k).trans (add_le_add (hC y) (hC y))
  have hC₂ : ∀ y, ‖g y‖ ≤ C + C := fun y => by
    have := (norm_nonneg _).trans (hC y)
    linarith [hC y]
  have hlim : ∀ y, Tendsto (fun k => u k y) atTop (𝓝 (g y)) := fun y =>
    SimpleFunc.tendsto_approxOn hg (mem_univ 0) (subset_closure (mem_univ _))
  have hstrong := tendsto_integralOp_apply hE (u := fun k => u k) (fun k => (u k).measurable) hg hu
    hC₂ hlim
  refine ContinuousLinearMap.ext fun x => ?_
  have h₁ : Tendsto (fun k => T (E.integralOp (u k) x)) atTop
      (𝓝 (T (E.integralOp g x))) := (T.continuous.tendsto _).comp (hstrong x)
  refine tendsto_nhds_unique h₁ ((hstrong (T x)).congr fun k => ?_)
  exact congrArg (fun S : H →L[ℂ] H => S x) (commute_integralOp_simpleFunc hE hT (u k)).eq.symm
theorem commutesWithBoundedIntegralsHolds_of_boundedBorelCalculus
    (hcalc : SpectralTheory.BoundedBorelCalculus.BoundedBorelCalculusHolds) :
    SpectralTheory.CommutationWithBoundedIntegrals.CommutesWithBoundedIntegralsHolds :=
  fun H _ _ _ n Y E _ hT g hg hbdd => commute_integralOp (hcalc H n Y E) hT g hg hbdd
end YangMills.Construction.SpectralTheory.BoundedIntegralCommutation
