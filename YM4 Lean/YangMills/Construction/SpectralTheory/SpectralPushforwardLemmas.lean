import YangMills.Construction.SpectralTheory.BoundedBorelCalculus
import YangMills.Construction.SpectralTheory.SpectralMeasurePushforwardTheorem
import Mathlib
set_option autoImplicit false
open MeasureTheory Set Filter Topology
open scoped ENNReal InnerProductSpace
noncomputable section
namespace YangMills.Construction.SpectralPushforward
open BorelSpectral BorelCalculus
variable {n n' : ℕ} {Y : Set (Fin n → ℝ)} {Y' : Set (Fin n' → ℝ)} {H : Type}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
omit [CompleteSpace H] in
theorem ext_of_inner_self {T S : H →L[ℂ] H} (h : ∀ ψ, ⟪ψ, T ψ⟫_ℂ = ⟪ψ, S ψ⟫_ℂ) : T = S := by
  have hl : (T : H →ₗ[ℂ] H) = S := by
    refine (ext_inner_map _ _).mp fun x => ?_
    rw [← inner_conj_symm, ContinuousLinearMap.coe_coe, h x, inner_conj_symm]
    rfl
  exact ContinuousLinearMap.coe_injective hl
theorem diagMeasure_pushforward_eq_map (E : SpectralMeasure Y H) (hn' : 1 ≤ n')
    (hY' : MeasurableSet Y') (κ : Y → Y') (hκ : Measurable κ) (ψ : H) :
    (E.pushforward hn' hY' κ hκ).diagMeasure ψ = (E.diagMeasure ψ).map κ := by
  refine Measure.ext fun Δ hΔ => ?_
  rw [Measure.map_apply hκ hΔ, (E.pushforward hn' hY' κ hκ).diagMeasure_apply ψ ⟨Δ, hΔ⟩,
    E.diagMeasure_apply ψ ⟨κ ⁻¹' Δ, hκ hΔ⟩]
  rfl
theorem integralOp_pushforward (E : SpectralMeasure Y H) (hE : BoundedFunctionalCalculus E)
    (hn' : 1 ≤ n') (hY' : MeasurableSet Y') (κ : Y → Y') (hκ : Measurable κ) {f : Y' → ℂ}
    (hf : Measurable f) (hb : IsBoundedFn f) :
    (E.pushforward hn' hY' κ hκ).integralOp f = E.integralOp (f ∘ κ) := by
  have hcb : IsBoundedFn (f ∘ κ) := by
    obtain ⟨c, hc⟩ := hb
    exact ⟨c, fun y => hc (κ y)⟩
  obtain ⟨T, hT, -⟩ := hE.existsUnique_op (f ∘ κ) (hf.comp hκ) hcb
  have hd : ∀ S : H →L[ℂ] H, (E.pushforward hn' hY' κ hκ).IsDiagonalIntegral f S ↔
      E.IsDiagonalIntegral (f ∘ κ) S := by
    intro S
    refine forall_congr' fun ψ => ?_
    rw [diagMeasure_pushforward_eq_map, integral_map hκ.aemeasurable hf.aestronglyMeasurable]
    rfl
  have h₁ : E.IsDiagonalIntegral (f ∘ κ) (E.integralOp (f ∘ κ)) :=
    Classical.epsilon_spec ⟨T, hT⟩
  have h₂ : (E.pushforward hn' hY' κ hκ).IsDiagonalIntegral f
      ((E.pushforward hn' hY' κ hκ).integralOp f) :=
    Classical.epsilon_spec ⟨T, (hd T).mpr hT⟩
  exact ext_of_inner_self fun ψ => ((hd _).mp h₂ ψ).trans (h₁ ψ).symm
theorem measurable_truncate {g : Y' → ℂ} (hg : Measurable g) (r : ℕ) :
    Measurable (truncate g r) :=
  hg.indicator (measurableSet_le hg.norm measurable_const)
theorem isBoundedFn_truncate (g : Y' → ℂ) (r : ℕ) :
    IsBoundedFn (truncate g r) := by
  refine ⟨r, fun y => ?_⟩
  by_cases h : ‖g y‖ ≤ r
  · simp [truncate, h]
  · simp [truncate, h]
theorem truncate_comp (g' : Y' → ℂ) (κ : Y → Y') (r : ℕ) :
    truncate (g' ∘ κ) r = truncate g' r ∘ κ := by
  funext y
  by_cases h : ‖g' (κ y)‖ ≤ r <;> simp [truncate, h]
theorem integralDom_pushforward_and_apply (E : SpectralMeasure Y H)
    (hE : BoundedFunctionalCalculus E) (hn' : 1 ≤ n')
    (hY' : MeasurableSet Y') (κ : Y → Y') (hκ : Measurable κ) (g' : Y' → ℂ) (hg : Measurable g') :
    (E.pushforward hn' hY' κ hκ).integralDom g' = E.integralDom (g' ∘ κ) ∧
      ∀ ψ ∈ E.integralDom (g' ∘ κ),
        (E.pushforward hn' hY' κ hκ).integralApply g' ψ = E.integralApply (g' ∘ κ) ψ := by
  constructor
  · ext ψ
    simp only [SpectralMeasure.integralDom, mem_ofPred_eq]
    rw [diagMeasure_pushforward_eq_map, lintegral_map (hg.enorm.pow_const 2) hκ]
    rfl
  · intro ψ _
    have hseq : (fun r : ℕ => (E.pushforward hn' hY' κ hκ).integralOp (truncate g' r) ψ) =
        fun r : ℕ => E.integralOp (truncate (g' ∘ κ) r) ψ := by
      funext r
      rw [integralOp_pushforward E hE hn' hY' κ hκ (measurable_truncate hg r)
        (isBoundedFn_truncate g' r), truncate_comp]
    simp only [SpectralMeasure.integralApply]
    rw [hseq]
theorem pushforward_congr_of_isCarriedBy (E : SpectralMeasure Y H) (hn' : 1 ≤ n')
    (hY' : MeasurableSet Y') (κ κ₂ : Y → Y') (hκ : Measurable κ) (hκ₂ : Measurable κ₂)
    (Δ₀ : BorelSubsets Y) (hc : E.IsCarriedBy Δ₀) (hag : ∀ y ∈ Δ₀.1, κ y = κ₂ y) :
    E.pushforward hn' hY' κ hκ = E.pushforward hn' hY' κ₂ hκ₂ := by
  refine SpectralMeasure.ext_apply fun Δ' => ext_of_inner_self fun ψ => ?_
  have h₀ : E.diagMeasure ψ Δ₀.1ᶜ = 0 := by
    have h := E.diagMeasure_apply ψ ⟨Δ₀.1ᶜ, Δ₀.2.compl⟩
    have hz : E ⟨Δ₀.1ᶜ, Δ₀.2.compl⟩ = 0 := hc
    rw [hz] at h
    simpa using h
  have hae : ∀ᵐ y ∂E.diagMeasure ψ, y ∈ Δ₀.1 := by
    rw [ae_iff]
    exact h₀
  have hset : (κ ⁻¹' Δ'.1 : Set Y) =ᵐ[E.diagMeasure ψ] κ₂ ⁻¹' Δ'.1 := by
    rw [Filter.eventuallyEq_set]
    filter_upwards [hae] with y hy
    simp only [mem_preimage, hag y hy]
  change ⟪ψ, E ⟨κ ⁻¹' Δ'.1, hκ Δ'.2⟩ ψ⟫_ℂ = ⟪ψ, E ⟨κ₂ ⁻¹' Δ'.1, hκ₂ Δ'.2⟩ ψ⟫_ℂ
  rw [E.inner_apply_self_eq_diagMeasure, E.inner_apply_self_eq_diagMeasure]
  simp only [Measure.real]
  rw [measure_congr hset]
theorem spectralPushforwardTheorem_of_bounded
    (hB : SpectralTheory.BoundedBorelCalculus.BoundedBorelCalculusHolds) :
    SpectralPushforwardTheorem :=
  fun H _ _ _ _ _ E =>
    { diagMeasure_pushforward := fun hn' hY' κ hκ ψ => diagMeasure_pushforward_eq_map E hn' hY' κ hκ ψ
      integral_pushforward := fun hn' hY' κ hκ g' hg =>
        integralDom_pushforward_and_apply E (hB H _ _ E) hn' hY' κ hκ g' hg
      pushforward_pushforward := fun _ _ _ _ _ _ _ _ => SpectralMeasure.ext_apply fun _ => rfl
      pushforward_congr := fun hn' hY' κ κ₂ hκ hκ₂ Δ₀ hc hag =>
        pushforward_congr_of_isCarriedBy E hn' hY' κ κ₂ hκ hκ₂ Δ₀ hc hag }
end YangMills.Construction.SpectralPushforward
