import YangMills.Construction.FormsOnATorus.InvariantMeasureOnFreeOrbits
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
namespace YangMills.Construction.GroupActions
theorem freeOrbitMeasure_eq_prod : FreeOrbitMeasureIsProduct := by
  intro K X Z _ _ _ _ _ _ _ _ _ _ μ _ _ m _ act s hmul hpres hemb
  set Ψ : K × Z → X := fun p => act p.1 (s p.2) with hΨ
  set ρ : Measure (K × Z) := m.comap Ψ with hρ
  have hmap : ρ.map Ψ = m.restrict (range Ψ) := hemb.map_comap m
  have hρa : ∀ A : Set (K × Z), ρ A = m (Ψ '' A) := fun A => hemb.comap_apply m A
  have hR : MeasurableSet (range Ψ) := hemb.measurableSet_range
  have hfin : IsFiniteMeasure ρ := ⟨by
    rw [hρa]
    exact measure_lt_top _ _⟩
  have hact : ∀ (k : K) (p : K × Z), act k (Ψ p) = Ψ (k * p.1, p.2) := fun k p => hmul k p.1 (s p.2)
  have hinj : Function.Injective Ψ := hemb.injective
  have htr : ∀ (k : K) (A : Set (K × Z)), MeasurableSet A →
      ρ ((fun p : K × Z => (k * p.1, p.2)) ⁻¹' A) = ρ A := by
    intro k A hA
    have hΨA : MeasurableSet (Ψ '' A) := hemb.measurableSet_image.mpr hA
    have hpre := (hpres k).measure_preimage hΨA.nullMeasurableSet
    have hpreR := (hpres k).measure_preimage hR.nullMeasurableSet
    have hsub : range Ψ ⊆ act k ⁻¹' range Ψ := by
      rintro _ ⟨p, rfl⟩
      exact ⟨_, (hact k p).symm⟩
    have hdiff : m (act k ⁻¹' range Ψ \ range Ψ) = 0 := by
      rw [measure_diff hsub hR.nullMeasurableSet (measure_ne_top _ _), hpreR, tsub_self]
    have hset : act k ⁻¹' (Ψ '' A) ∩ range Ψ = Ψ '' ((fun p : K × Z => (k * p.1, p.2)) ⁻¹' A) := by
      ext x
      constructor
      · rintro ⟨⟨a, ha, hax⟩, ⟨p, rfl⟩⟩
        refine ⟨p, ?_, rfl⟩
        rw [hact k p] at hax
        have := hinj hax
        rw [mem_preimage, ← this]
        exact ha
      · rintro ⟨p, hp, rfl⟩
        exact ⟨⟨_, hp, (hact k p).symm⟩, ⟨p, rfl⟩⟩
    have h0 : m (act k ⁻¹' (Ψ '' A) \ range Ψ) = 0 :=
      measure_mono_null (diff_subset_diff_left (preimage_mono (image_subset_range _ _))) hdiff
    rw [hρa, hρa, ← hset, ← hpre, ← measure_inter_add_diff (act k ⁻¹' (Ψ '' A)) hR, h0, add_zero]
  set ν : Measure Z := ρ.map Prod.snd with hν
  have hfν : IsFiniteMeasure ν := by
    rw [hν]
    infer_instance
  have hνa : ∀ B : Set Z, MeasurableSet B → ν B = ρ (univ ×ˢ B) := by
    intro B hB
    rw [hν, Measure.map_apply measurable_snd hB]
    congr 1
    ext p
    simp
  have hprod : ∀ (C : Set K) (B : Set Z), MeasurableSet C → MeasurableSet B → ρ (C ×ˢ B) = μ C * ν B := by
    intro C B hC hB
    set ρB : Measure K := (ρ.restrict (univ ×ˢ B)).map Prod.fst with hρB
    have hρBa : ∀ D : Set K, MeasurableSet D → ρB D = ρ (D ×ˢ B) := by
      intro D hD
      rw [hρB, Measure.map_apply measurable_fst hD, Measure.restrict_apply (measurable_fst hD)]
      congr 1
      ext p
      simp
    have hfB : IsFiniteMeasure ρB := by
      rw [hρB]
      infer_instance
    have hinv : ρB.IsMulLeftInvariant := ⟨fun k => by
      ext D hD
      rw [Measure.map_apply (measurable_const_mul k) hD, hρBa _ (measurable_const_mul k hD), hρBa _ hD,
        ← htr k _ (hD.prod hB)]
      rfl⟩
    have hs := Measure.isMulInvariant_eq_smul_of_compactSpace ρB μ
    set c := Measure.haarScalarFactor ρB μ with hc
    have h1 : ρB C = (c : ENNReal) * μ C := by
      conv_lhs => rw [hs]
      rw [Measure.smul_apply]
      rfl
    have h2 : ρB univ = (c : ENNReal) := by
      conv_lhs => rw [hs]
      rw [Measure.smul_apply, measure_univ]
      simp [ENNReal.smul_def]
    rw [← hρBa C hC, h1, hνa B hB, ← hρBa univ MeasurableSet.univ, h2, mul_comm]
  refine ⟨ν, hfν, fun f hf => ?_⟩
  have hρν : μ.prod ν = ρ := Measure.prod_eq hprod
  calc ∫⁻ x in range Ψ, f x ∂m = ∫⁻ x, f x ∂(ρ.map Ψ) := by rw [hmap]
    _ = ∫⁻ p, f (Ψ p) ∂ρ := hemb.lintegral_map f
    _ = ∫⁻ p, f (Ψ p) ∂(μ.prod ν) := by rw [hρν]
    _ = ∫⁻ k, ∫⁻ z, f (act k (s z)) ∂ν ∂μ := lintegral_prod _ (hf.comp hemb.measurable).aemeasurable
end YangMills.Construction.GroupActions
end
