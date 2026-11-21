import YangMills.Construction.Measures.SupportFullMeasureAndL2Rank
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
namespace YangMills.Construction.Measures.SupportL2
private theorem card_le_rank_L2 {Y : Type} [TopologicalSpace Y] [TopologicalSpace.MetrizableSpace Y]
    [MeasurableSpace Y] [BorelSpace Y] (μ : Measure Y) [IsProbabilityMeasure μ]
    (hsupp : probabilitySupport μ = Set.univ) (t : Finset Y) :
    (t.card : Cardinal) ≤ Module.rank ℂ (Lp ℂ 2 μ) := by
  obtain ⟨V, hV, hdisj⟩ := (t.finite_toSet).t2_separation
  have hpos : ∀ y : Y, 0 < μ (V y) := fun y => by
    have hy : y ∈ probabilitySupport μ := hsupp ▸ Set.mem_univ y
    exact hy (V y) (hV y).2 (hV y).1
  have hmeas : ∀ y : Y, MeasurableSet (V y) := fun y => (hV y).2.measurableSet
  have hfin : ∀ y : Y, μ (V y) ≠ ⊤ := fun y => measure_ne_top μ _
  let e : t → Lp ℂ 2 μ := fun y => indicatorConstLp 2 (hmeas y) (hfin y) (1 : ℂ)
  have hli : LinearIndependent ℂ e := by
    refine linearIndependent_of_ne_zero_of_inner_eq_zero (𝕜 := ℂ) (fun y h0 => ?_) ?_
    · have hn := norm_indicatorConstLp' (p := 2) (c := (1 : ℂ)) (by norm_num)
        (hpos y).ne' (hs := hmeas y) (hμs := hfin y)
      have h0' : indicatorConstLp 2 (hmeas y) (hfin y) (1 : ℂ) = 0 := h0
      rw [h0', norm_zero] at hn
      have hr : 0 < μ.real (V y) := by
        rw [measureReal_def]
        exact ENNReal.toReal_pos (hpos y).ne' (hfin y)
      have : 0 < ‖(1 : ℂ)‖ * μ.real (V y) ^ (1 / (2 : ENNReal).toReal) := by
        rw [norm_one, one_mul]
        exact Real.rpow_pos_of_pos hr _
      exact this.ne hn
    · intro a b hab
      have hd : Disjoint (V a) (V b) :=
        hdisj a.2 b.2 (fun h => hab (Subtype.ext h))
      rw [L2.inner_indicatorConstLp_indicatorConstLp]
      have : μ (V a ∩ V b) = 0 := by
        rw [hd.inter_eq]; exact measure_empty
      simp [measureReal_def, this]
  have := hli.cardinal_le_rank
  simpa using this
theorem supportFullMeasureAndL2Rank_holds : SupportFullMeasureAndL2Rank := by
  intro Y _ _ _ _ _ μ _
  let := TopologicalSpace.metrizableSpaceMetric Y
  have : SecondCountableTopology Y := UniformSpace.secondCountable_of_separable Y
  have hcompl : (probabilitySupport μ)ᶜ =
      {y | ∃ O : Set Y, IsOpen O ∧ y ∈ O ∧ μ O = 0} := by
    ext y
    simp only [probabilitySupport, mem_compl_iff, mem_ofPred_eq, not_forall,
      not_lt, nonpos_iff_eq_zero, exists_prop]
  have hopen : IsOpen (probabilitySupport μ)ᶜ := by
    rw [hcompl, isOpen_iff_forall_mem_open]
    rintro y ⟨O, hO, hy, h0⟩
    exact ⟨O, fun z hz => ⟨O, hO, hz, h0⟩, hO, hy⟩
  have hnull : μ (probabilitySupport μ)ᶜ = 0 := by
    refine measure_null_of_locally_null _ fun y hy => ?_
    rw [hcompl] at hy
    obtain ⟨O, hO, hyO, h0⟩ := hy
    exact ⟨O, mem_nhdsWithin_of_mem_nhds (hO.mem_nhds hyO), h0⟩
  have hclosed : IsClosed (probabilitySupport μ) := isOpen_compl_iff.1 hopen
  have hone : μ (probabilitySupport μ) = 1 := by
    have := prob_compl_eq_zero_iff (μ := μ) hclosed.measurableSet
    exact this.1 hnull
  refine ⟨⟨hclosed, hone⟩, ⟨?_, ?_, ?_⟩, ?_⟩
  · refine nonempty_iff_ne_empty.2 fun h => ?_
    rw [h, measure_empty] at hone
    exact zero_ne_one hone
  · intro E hE hpos
    refine nonempty_iff_ne_empty.2 fun h => hpos.ne' ?_
    have hle : E ⊆ (probabilitySupport μ)ᶜ := fun y hy hs =>
      (h ▸ (⟨hy, hs⟩ : y ∈ E ∩ probabilitySupport μ) : y ∈ (∅ : Set Y))
    exact measure_mono_null hle hnull
  · intro C hC h1 y hy
    by_contra hyC
    have h0 : μ Cᶜ = 0 := (prob_compl_eq_zero_iff hC.measurableSet).2 h1
    exact (hy Cᶜ hC.isOpen_compl hyC).ne' h0
  · intro _ hsupp
    by_cases hY : Finite Y
    · cases nonempty_fintype Y
      classical
      have hsing : ∀ y : Y, 0 < μ {y} := fun y => by
        have hy : y ∈ probabilitySupport μ := hsupp ▸ Set.mem_univ y
        exact hy {y} (isOpen_discrete _) rfl
      have hall : ∀ p : Y → Prop, (∀ᵐ x ∂μ, p x) → ∀ y, p y := fun p hp y => by
        by_contra hne
        have : μ {y} = 0 := measure_mono_null (fun x hx => by
          rw [mem_singleton_iff.1 hx]; exact hne) (ae_iff.1 hp)
        exact (hsing y).ne' this
      let L : Lp ℂ 2 μ →ₗ[ℂ] (Y → ℂ) :=
        { toFun := fun f => ⇑f
          map_add' := fun f g => funext (hall _ (Lp.coeFn_add f g))
          map_smul' := fun c f => funext (hall _ (Lp.coeFn_smul c f)) }
      have hinj : Function.Injective L := fun f g h =>
        Lp.ext (Filter.EventuallyEq.of_eq h)
      have hle : Module.rank ℂ (Lp ℂ 2 μ) ≤ Cardinal.mk Y := by
        have := LinearMap.rank_le_of_injective L hinj
        rwa [rank_fun', ← Cardinal.mk_fintype] at this
      have hge : Cardinal.mk Y ≤ Module.rank ℂ (Lp ℂ 2 μ) := by
        have := card_le_rank_L2 μ hsupp Finset.univ
        rwa [Finset.card_univ, ← Cardinal.mk_fintype] at this
      exact congrArg Cardinal.toENat (le_antisymm hle hge)
    · have : Infinite Y := not_finite_iff_infinite.1 hY
      rw [ENat.card_eq_top_of_infinite, Cardinal.toENat_eq_top, Cardinal.aleph0_le]
      intro n
      obtain ⟨t, ht⟩ := Infinite.exists_subset_card_eq Y n
      simpa [ht] using card_le_rank_L2 μ hsupp t
end YangMills.Construction.Measures.SupportL2
