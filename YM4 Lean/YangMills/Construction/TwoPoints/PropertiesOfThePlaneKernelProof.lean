import YangMills.Construction.TwoPoints.ElementaryFactsOfMirrorsAndPlatesProof
import YangMills.Construction.TwoPoints.FromThePlaneKernelsToTheOrthogonalGroupProof
import YangMills.Construction.TwoPoints.PropertiesOfThePlaneKernel
import Mathlib
set_option autoImplicit false
open MeasureTheory Set Filter
open scoped Topology
noncomputable section
namespace YangMills.Construction.TwoPoints.AveragedKernelProperties
open YangMills.Construction.InfiniteLattice (AmbientSpace)
theorem continuousAt_of_isRealAnalyticAwayFromZero {K : AmbientSpace → ℝ}
    (h : IsRealAnalyticAwayFromZero K) {x : AmbientSpace} (hx : x ≠ 0) : ContinuousAt K x := by
  let ι : AmbientSpace → Coordinates.ComplexCoordinates 4 := fun v μ => ((v μ : ℝ) : ℂ)
  have hι : Continuous ι :=
    continuous_pi fun μ => Complex.continuous_ofReal.comp (continuous_apply μ)
  have hreal : ∀ v, ι v ∈ Coordinates.ComplexCoordinates.realLocus 4 := fun v j => by simp [ι]
  have hax : ι x ∈ Coordinates.ComplexCoordinates.realLocus 4 \ {0} := by
    refine ⟨hreal x, fun h0 => hx ?_⟩
    funext μ
    have h1 := congrFun h0 μ
    simpa [ι] using h1
  obtain ⟨c, hc⟩ := h.2 (ι x) hax
  have ht : Tendsto ι (𝓝 x) (𝓝[Coordinates.ComplexCoordinates.realLocus 4] (ι x)) :=
    tendsto_nhdsWithin_iff.2 ⟨hι.continuousAt, Eventually.of_forall hreal⟩
  have hpull : ∀ᶠ v in 𝓝 x, HasSum (fun m : Fin 4 → ℕ => (∏ j, (ι v j - ι x j) ^ m j) • c m)
      (fun _ : Fin 1 => ((K v : ℝ) : ℂ)) := by
    filter_upwards [ht.eventually hc] with v hv
    have e : (fun μ => (ι v μ).re) = v := by
      funext μ
      simp [ι]
    simpa only [e] using hv
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hpull
  set δ : ℝ := ε / 2 with hδ
  have hδ0 : 0 < δ := by positivity
  have hδε : δ < ε := by rw [hδ]; linarith
  have hcorner : Summable fun m : Fin 4 → ℕ =>
      ‖(∏ j, (ι (x + fun _ => δ) j - ι x j) ^ m j) • c m‖ := by
    have hd : dist (x + fun _ => δ) x < ε := by
      rw [dist_pi_lt_iff hε]
      intro μ
      simpa [Real.dist_eq, abs_of_pos hδ0] using hδε
    exact ((hball hd).summable).norm
  have hbound : ∀ᶠ v in 𝓝 x, ∀ m : Fin 4 → ℕ,
      ‖(∏ j, (ι v j - ι x j) ^ m j) • c m‖ ≤
        ‖(∏ j, (ι (x + fun _ => δ) j - ι x j) ^ m j) • c m‖ := by
    filter_upwards [Metric.ball_mem_nhds x hδ0] with v hv m
    rw [norm_smul, norm_smul]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    rw [norm_prod, norm_prod]
    refine Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun j _ => ?_
    rw [norm_pow, norm_pow]
    refine pow_le_pow_left₀ (norm_nonneg _) ?_ _
    have h1 : ι v j - ι x j = ((v j - x j : ℝ) : ℂ) := by simp [ι]
    have h2 : ι (x + fun _ => δ) j - ι x j = ((δ : ℝ) : ℂ) := by simp [ι]
    rw [h1, h2, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos hδ0]
    have h3 : dist v x < δ := hv
    have h4 := (dist_pi_lt_iff hδ0).1 h3 j
    rw [Real.dist_eq] at h4
    exact h4.le
  have hterm : ∀ m : Fin 4 → ℕ, Tendsto (fun v => (∏ j, (ι v j - ι x j) ^ m j) • c m) (𝓝 x)
      (𝓝 ((∏ j, (ι x j - ι x j) ^ m j) • c m)) := by
    intro m
    have hcont : Continuous fun v : AmbientSpace => (∏ j, (ι v j - ι x j) ^ m j) • c m :=
      (continuous_finsetProd _ fun j _ =>
        (((continuous_apply j).comp hι).sub continuous_const).pow _).smul continuous_const
    exact hcont.tendsto x
  have hlim := tendsto_tsum_of_dominated_convergence hcorner hterm hbound
  have hx0 : (∑' m : Fin 4 → ℕ, (∏ j, (ι x j - ι x j) ^ m j) • c m) =
      fun _ : Fin 1 => ((K x : ℝ) : ℂ) := (hpull.self_of_nhds).tsum_eq
  rw [hx0] at hlim
  have hev : (fun v => ∑' m : Fin 4 → ℕ, (∏ j, (ι v j - ι x j) ^ m j) • c m) =ᶠ[𝓝 x]
      fun v => fun _ : Fin 1 => ((K v : ℝ) : ℂ) := by
    filter_upwards [hpull] with v hv using hv.tsum_eq
  have h1 : Tendsto (fun v => fun _ : Fin 1 => ((K v : ℝ) : ℂ)) (𝓝 x)
      (𝓝 fun _ : Fin 1 => ((K x : ℝ) : ℂ)) := hlim.congr' hev
  have h2 : Tendsto (fun v => (((K v : ℝ) : ℂ)).re) (𝓝 x) (𝓝 (((K x : ℝ) : ℂ)).re) :=
    (Complex.continuous_re.tendsto _).comp (((continuous_apply (0 : Fin 1)).tendsto _).comp h1)
  simpa [ContinuousAt] using h2
section
theorem integrable_of_support_subset_compact {X : Type*} [TopologicalSpace X] [T2Space X]
    [MeasurableSpace X] [OpensMeasurableSpace X] {μ : Measure X} [IsFiniteMeasureOnCompacts μ]
    {f : X → ℂ} (hf : Continuous f) {C : Set X} (hC : IsCompact C)
    (hs : ∀ x, f x ≠ 0 → x ∈ C) : Integrable f μ :=
  hf.integrable_of_hasCompactSupport
    (HasCompactSupport.intro hC fun x hx => by
      by_contra h
      exact hx (hs x h))
theorem continuous_mul_kernel_of_disjoint_tsupport {X : Type*} [NormedAddCommGroup X]
    {f h k : X → ℂ} (hf : Continuous f) (hh : Continuous h)
    (hd : Disjoint (tsupport f) (tsupport h)) (hk : ∀ x, x ≠ 0 → ContinuousAt k x) :
    Continuous fun p : X × X => f p.1 * h p.2 * k (p.2 - p.1) := by
  refine continuous_iff_continuousAt.2 fun p => ?_
  by_cases hp : p.2 - p.1 = 0
  · have hq : p.2 = p.1 := sub_eq_zero.1 hp
    by_cases h1 : p.1 ∈ tsupport f
    · have h2 : p.2 ∉ tsupport h := fun h2 => (Set.disjoint_left.1 hd h1) (hq ▸ h2)
      have h3 : h =ᶠ[𝓝 p.2] 0 := notMem_tsupport_iff_eventuallyEq.1 h2
      have h4 : (fun p : X × X => f p.1 * h p.2 * k (p.2 - p.1)) =ᶠ[𝓝 p] fun _ => 0 := by
        filter_upwards [continuous_snd.continuousAt.eventually h3] with q hq'
        simp [hq']
      refine ContinuousAt.congr continuousAt_const h4.symm
    · have h3 : f =ᶠ[𝓝 p.1] 0 := notMem_tsupport_iff_eventuallyEq.1 h1
      have h4 : (fun p : X × X => f p.1 * h p.2 * k (p.2 - p.1)) =ᶠ[𝓝 p] fun _ => 0 := by
        filter_upwards [continuous_fst.continuousAt.eventually h3] with q hq'
        simp [hq']
      refine ContinuousAt.congr continuousAt_const h4.symm
  · have h1 : ContinuousAt (fun q : X × X => k (q.2 - q.1)) p :=
      ContinuousAt.comp (f := fun q : X × X => q.2 - q.1) (hk _ hp)
        (continuous_snd.sub continuous_fst).continuousAt
    exact ((hf.comp continuous_fst).continuousAt.mul
      (hh.comp continuous_snd).continuousAt).mul h1
theorem integral_prod_prod_eq_iterated_shift
    (H : (Fin 2 → ℝ) → (Fin 2 → ℝ) → (Fin 2 → ℝ) → (Fin 2 → ℝ) → ℂ)
    (hc : Continuous fun p : ((Fin 2 → ℝ) × (Fin 2 → ℝ)) × ((Fin 2 → ℝ) × (Fin 2 → ℝ)) =>
      H p.1.1 p.2.1 p.1.2 p.2.2)
    {A A' B B' : Set (Fin 2 → ℝ)} (hA : IsCompact A) (hA' : IsCompact A') (hB : IsCompact B)
    (hB' : IsCompact B')
    (hs : ∀ y y' υ υ', H y y' υ υ' ≠ 0 → y ∈ A ∧ y' ∈ A' ∧ υ ∈ B ∧ υ' ∈ B') :
    ∫ p' : (Fin 2 → ℝ) × (Fin 2 → ℝ), ∫ p : (Fin 2 → ℝ) × (Fin 2 → ℝ), H p.1 p'.1 p.2 p'.2 =
      ∫ y', ∫ y, ∫ ζ, ∫ υ, H y y' υ (υ + ζ) := by
  have hint : Integrable (fun q : ((Fin 2 → ℝ) × (Fin 2 → ℝ)) × ((Fin 2 → ℝ) × (Fin 2 → ℝ)) =>
      H q.1.1 q.2.1 q.1.2 q.2.2) (volume.prod volume) :=
    integrable_of_support_subset_compact hc ((hA.prod hB).prod (hA'.prod hB')) fun q hq => by
      obtain ⟨h1, h2, h3, h4⟩ := hs _ _ _ _ hq
      exact ⟨⟨h1, h3⟩, ⟨h2, h4⟩⟩
  have hW : Integrable (fun p' : (Fin 2 → ℝ) × (Fin 2 → ℝ) =>
      ∫ p : (Fin 2 → ℝ) × (Fin 2 → ℝ), H p.1 p'.1 p.2 p'.2) (volume.prod volume) :=
    hint.integral_prod_right
  have hslice : ∀ p' : (Fin 2 → ℝ) × (Fin 2 → ℝ),
      ∫ p : (Fin 2 → ℝ) × (Fin 2 → ℝ), H p.1 p'.1 p.2 p'.2 =
        ∫ y, ∫ υ, H y p'.1 υ p'.2 := by
    intro p'
    refine integral_prod (fun p : (Fin 2 → ℝ) × (Fin 2 → ℝ) => H p.1 p'.1 p.2 p'.2) ?_
    refine integrable_of_support_subset_compact
      (hc.comp (Continuous.prodMk continuous_id continuous_const)) (hA.prod hB) fun q hq => ?_
    obtain ⟨h1, -, h3, -⟩ := hs _ _ _ _ hq
    exact ⟨h1, h3⟩
  have hstep1 : ∫ p' : (Fin 2 → ℝ) × (Fin 2 → ℝ), ∫ p : (Fin 2 → ℝ) × (Fin 2 → ℝ),
      H p.1 p'.1 p.2 p'.2 = ∫ y', ∫ υ', ∫ y, ∫ υ, H y y' υ υ' := by
    have h1 := integral_prod _ hW
    rw [show (∫ p' : (Fin 2 → ℝ) × (Fin 2 → ℝ), ∫ p : (Fin 2 → ℝ) × (Fin 2 → ℝ),
      H p.1 p'.1 p.2 p'.2) = ∫ z, (∫ p : (Fin 2 → ℝ) × (Fin 2 → ℝ), H p.1 z.1 p.2 z.2)
        ∂(volume.prod volume) from rfl, h1]
    exact integral_congr_ae (Eventually.of_forall fun y' => integral_congr_ae
      (Eventually.of_forall fun υ' => hslice (y', υ')))
  rw [hstep1]
  refine integral_congr_ae (Eventually.of_forall fun y' => ?_)
  beta_reduce
  have hswap : ∫ υ', ∫ y, ∫ υ, H y y' υ υ' = ∫ y, ∫ υ', ∫ υ, H y y' υ υ' := by
    refine integral_integral_swap (f := fun υ' y => ∫ υ, H y y' υ υ') ?_
    have h0 : Integrable (fun q : ((Fin 2 → ℝ) × (Fin 2 → ℝ)) × (Fin 2 → ℝ) =>
        H q.1.2 y' q.2 q.1.1) ((volume.prod volume).prod volume) := by
      refine integrable_of_support_subset_compact (C := (B' ×ˢ A) ×ˢ B) ?_
        ((hB'.prod hA).prod hB) fun q hq => ?_
      · exact hc.comp (f := fun q : ((Fin 2 → ℝ) × (Fin 2 → ℝ)) × (Fin 2 → ℝ) =>
          (((q.1.2, q.2), (y', q.1.1)) :
            ((Fin 2 → ℝ) × (Fin 2 → ℝ)) × ((Fin 2 → ℝ) × (Fin 2 → ℝ)))) (by fun_prop)
      · obtain ⟨h1, -, h3, h4⟩ := hs _ _ _ _ hq
        exact ⟨⟨h4, h1⟩, h3⟩
    exact h0.integral_prod_left
  rw [hswap]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  beta_reduce
  have hT : Integrable (fun q : (Fin 2 → ℝ) × (Fin 2 → ℝ) => H y y' q.2 q.1)
      (volume.prod volume) := by
    refine integrable_of_support_subset_compact (C := B' ×ˢ B) ?_ (hB'.prod hB)
      fun q hq => ?_
    · exact hc.comp (f := fun q : (Fin 2 → ℝ) × (Fin 2 → ℝ) =>
        (((y, q.2), (y', q.1)) :
          ((Fin 2 → ℝ) × (Fin 2 → ℝ)) × ((Fin 2 → ℝ) × (Fin 2 → ℝ)))) (by fun_prop)
    · obtain ⟨-, -, h3, h4⟩ := hs _ _ _ _ hq
      exact ⟨h4, h3⟩
  have hZ : Integrable (fun q : (Fin 2 → ℝ) × (Fin 2 → ℝ) => H y y' q.2 (q.2 + q.1))
      (volume.prod volume) := by
    refine integrable_of_support_subset_compact
      (C := ((fun p : (Fin 2 → ℝ) × (Fin 2 → ℝ) => p.1 - p.2) '' (B' ×ˢ B)) ×ˢ B) ?_
      (((hB'.prod hB).image continuous_sub).prod hB) fun q hq => ?_
    · exact hc.comp (f := fun q : (Fin 2 → ℝ) × (Fin 2 → ℝ) =>
        (((y, q.2), (y', q.2 + q.1)) :
          ((Fin 2 → ℝ) × (Fin 2 → ℝ)) × ((Fin 2 → ℝ) × (Fin 2 → ℝ)))) (by fun_prop)
    · obtain ⟨-, -, h3, h4⟩ := hs _ _ _ _ hq
      exact ⟨⟨(q.2 + q.1, q.2), ⟨h4, h3⟩, add_sub_cancel_left _ _⟩, h3⟩
  calc ∫ υ', ∫ υ, H y y' υ υ' = ∫ υ, ∫ υ', H y y' υ υ' :=
        integral_integral_swap (f := fun υ' υ => H y y' υ υ') hT
    _ = ∫ υ, ∫ ζ, H y y' υ (υ + ζ) := by
        refine integral_congr_ae (Eventually.of_forall fun υ => ?_)
        exact (integral_add_left_eq_self (fun υ' => H y y' υ υ') υ).symm
    _ = ∫ ζ, ∫ υ, H y y' υ (υ + ζ) :=
        (integral_integral_swap (f := fun ζ υ => H y y' υ (υ + ζ)) hZ).symm
end
section
theorem planeCoords_assemble (y z : Fin 2 → ℝ) : planeCoords (assemble y z) = y := by
  funext i
  fin_cases i <;> simp [planeCoords, assemble]
theorem transCoords_assemble (y z : Fin 2 → ℝ) :
    transCoords (assemble y z) = z := by
  funext i
  fin_cases i <;> simp [transCoords, assemble]
theorem continuous_assemble :
    Continuous fun p : (Fin 2 → ℝ) × (Fin 2 → ℝ) => assemble p.1 p.2 := by apply _root_.YangMills.Construction.TwoPoints.ReflectionsPlaneFacts.continuous_assemble <;> assumption
theorem assemble_ne_zero {y : Fin 2 → ℝ} (hy : y ≠ 0) (z : Fin 2 → ℝ) :
    assemble y z ≠ 0 := by apply _root_.YangMills.SharedProofs.p69635 <;> assumption
theorem assemble_sub_assemble (y y' z z' : Fin 2 → ℝ) :
    assemble y' z' - assemble y z = assemble (y' - y) (z' - z) := by
  funext i
  fin_cases i <;> simp [assemble]
def splitIndexEquiv : Fin 2 ⊕ Fin 2 ≃ Fin 4 where
  toFun := Sum.elim ![3, 0] ![1, 2]
  invFun := ![Sum.inl 1, Sum.inr 0, Sum.inr 1, Sum.inl 0]
  left_inv := by rintro (i | i) <;> fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl
theorem exists_measurePreserving_assemble :
    ∃ e : ((Fin 2 → ℝ) × (Fin 2 → ℝ)) ≃ᵐ AmbientSpace, MeasurePreserving e volume volume ∧
      ∀ p, e p = assemble p.1 p.2 := by
  let e₀ := MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin 2 ⊕ Fin 2 => ℝ)
  let e₁ := MeasurableEquiv.piCongrLeft (fun _ : Fin 4 => ℝ) splitIndexEquiv
  refine ⟨e₀.symm.trans e₁, ?_, ?_⟩
  · exact (volume_measurePreserving_piCongrLeft (fun _ : Fin 4 => ℝ) splitIndexEquiv).comp
      (volume_measurePreserving_sumPiEquivProdPi_symm (fun _ : Fin 2 ⊕ Fin 2 => ℝ))
  · rintro ⟨y, z⟩
    have splitEval₀ : ∀ (g : Fin 2 ⊕ Fin 2 → ℝ) (a : Fin 2 ⊕ Fin 2),
        e₁ g (splitIndexEquiv a) = g a := fun g a => by
      simp only [e₁, MeasurableEquiv.coe_piCongrLeft]
      exact Equiv.piCongrLeft_apply_apply _ _ _ _
    have key : ∀ a : Fin 2 ⊕ Fin 2, (e₀.symm.trans e₁) (y, z) (splitIndexEquiv a) =
        e₀.symm (y, z) a := fun a => splitEval₀ _ a
    funext i
    fin_cases i
    · exact key (Sum.inl 1)
    · exact key (Sum.inr 0)
    · exact key (Sum.inr 1)
    · exact key (Sum.inl 0)
theorem integral_eq_integral_assemble (g : AmbientSpace → ℂ) :
    ∫ x, g x = ∫ p : (Fin 2 → ℝ) × (Fin 2 → ℝ), g (assemble p.1 p.2) := by
  obtain ⟨e, he, hv⟩ := exists_measurePreserving_assemble
  rw [← he.integral_comp' g]
  exact integral_congr_ae (Eventually.of_forall fun p => by simp only [hv])
end
section
theorem cc1In_dest {O : Set (Fin 2 → ℝ)} {f : (Fin 2 → ℝ) → ℂ} (h : f ∈ cc1In O) :
    ContDiff ℝ 1 f ∧ IsCompact (tsupport f) ∧ tsupport f ⊆ O := h
theorem mem_cc1In_of {O : Set (Fin 2 → ℝ)} {f : (Fin 2 → ℝ) → ℂ}
    (h : ContDiff ℝ 1 f ∧ IsCompact (tsupport f) ∧ tsupport f ⊆ O) :
    f ∈ cc1In O := h
theorem cc1In_mono {O O' : Set (Fin 2 → ℝ)} (hO : O ⊆ O') {f : (Fin 2 → ℝ) → ℂ}
    (h : f ∈ cc1In O) : f ∈ cc1In O' :=
  mem_cc1In_of ⟨(cc1In_dest h).1, (cc1In_dest h).2.1, (cc1In_dest h).2.2.trans hO⟩
theorem comp_homeomorph_mem_cc1In {O : Set (Fin 2 → ℝ)} {f : (Fin 2 → ℝ) → ℂ}
    (h : f ∈ cc1In O) (ι : (Fin 2 → ℝ) ≃ₜ (Fin 2 → ℝ)) (hι : ContDiff ℝ 1 ι) :
    f ∘ ι ∈ cc1In (ι ⁻¹' O) := by
  have hs : tsupport (f ∘ ι) = ι ⁻¹' tsupport f := by
    simp only [tsupport]
    rw [ι.preimage_closure, Function.support_comp_eq_preimage]
  refine mem_cc1In_of ⟨(cc1In_dest h).1.comp hι, ?_, ?_⟩
  · rw [hs]
    exact ι.isCompact_preimage.2 (cc1In_dest h).2.1
  · rw [hs]
    exact preimage_mono (cc1In_dest h).2.2
theorem conjFun_mem_cc1In {O : Set (Fin 2 → ℝ)} {f : (Fin 2 → ℝ) → ℂ}
    (h : f ∈ cc1In O) : conjFun f ∈ cc1In O := by
  have hs : Function.support (conjFun f) = Function.support f := by
    ext x
    simp [conjFun]
  refine mem_cc1In_of ⟨Complex.conjCLE.contDiff.comp (cc1In_dest h).1, ?_, ?_⟩
  · simp only [tsupport, hs]
    exact (cc1In_dest h).2.1
  · simp only [tsupport, hs]
    exact (cc1In_dest h).2.2
theorem compactC1Complex_dest {f : AmbientSpace → ℂ} (h : f ∈ compactC1Complex) :
    ContDiff ℝ 1 f ∧ IsCompact (tsupport f) ∧ tsupport f ⊆ univ := h
end
section
variable {S : (AmbientSpace → ℂ) → (AmbientSpace → ℂ) → ℝ} {φ : (Fin 2 → ℝ) → ℂ}
theorem integrable_ofCoords_mul {K : AmbientSpace → ℝ} (hK : ∀ x, x ≠ 0 → ContinuousAt K x)
    {C : (Fin 2 → ℝ) → ℂ} (hC : Continuous C) (hcs : IsCompact (tsupport C))
    {y : Fin 2 → ℝ} (hy : y ≠ 0) :
    Integrable fun ζ : Fin 2 → ℝ => ((ofCoords K y ζ : ℝ) : ℂ) * C ζ := by
  have h1 : Continuous fun ζ : Fin 2 → ℝ => assemble y ζ :=
    continuous_assemble.comp (f := fun ζ : Fin 2 → ℝ => (y, ζ)) (by fun_prop)
  have h2 : Continuous fun ζ : Fin 2 → ℝ => K (assemble y ζ) :=
    continuous_iff_continuousAt.2 fun ζ =>
      ContinuousAt.comp (f := fun ζ : Fin 2 → ℝ => assemble y ζ)
        (hK _ (assemble_ne_zero hy ζ)) h1.continuousAt
  refine integrable_of_support_subset_compact ((Complex.continuous_ofReal.comp h2).mul hC) hcs
    fun ζ hζ => ?_
  by_contra h
  exact hζ (by simp [image_eq_zero_of_notMem_tsupport h])
theorem isRegularAveragedKernel_of (hK : IsAnalyticKernel S (formKernel S))
    (hsym : ∀ r ∈ dihedralInPlane, ∀ y z : Fin 2 → ℝ,
      r (assemble y z) = assemble (planeCoords (r (embedPlane y))) z)
    (hC : (∀ ζ, (profileCorr φ φ ζ).im = 0) ∧ Continuous (profileCorr φ φ) ∧
      IsCompact (tsupport (profileCorr φ φ))) :
    IsRegularAveragedKernel S φ := by
  obtain ⟨hCim, hCc, hCs⟩ := hC
  have hKc : ∀ x, x ≠ 0 → ContinuousAt (formKernel S) x :=
    fun x hx => continuousAt_of_isRealAnalyticAwayFromZero hK.analytic hx
  refine ⟨fun y hy => integrable_ofCoords_mul hKc hCc hCs hy, ?_, ?_, ?_⟩
  · intro y _
    have e : (fun ζ : Fin 2 → ℝ => ((ofCoords (formKernel S) y ζ : ℝ) : ℂ) *
        profileCorr φ φ ζ) = fun ζ => ((ofCoords (formKernel S) y ζ *
          (profileCorr φ φ ζ).re : ℝ) : ℂ) := by
      funext ζ
      apply Complex.ext <;> simp [hCim ζ]
    change (∫ ζ, ((ofCoords (formKernel S) y ζ : ℝ) : ℂ) * profileCorr φ φ ζ).im = 0
    rw [e, integral_complex_ofReal]
    simp
  · have hU : IsOpen {y : Fin 2 → ℝ | y ≠ 0} := isOpen_ne
    have : LocallyCompactSpace {y : Fin 2 → ℝ // y ≠ 0} := hU.locallyCompactSpace
    let F : {y : Fin 2 → ℝ // y ≠ 0} → (Fin 2 → ℝ) → ℂ := fun y ζ =>
      ((ofCoords (formKernel S) y.1 ζ : ℝ) : ℂ) * profileCorr φ φ ζ
    have hF : Continuous (Function.uncurry F) := by
      have h1 : Continuous fun q : {y : Fin 2 → ℝ // y ≠ 0} × (Fin 2 → ℝ) =>
          assemble q.1.1 q.2 :=
        continuous_assemble.comp
          (f := fun q : {y : Fin 2 → ℝ // y ≠ 0} × (Fin 2 → ℝ) => (q.1.1, q.2)) (by fun_prop)
      have h2 : Continuous fun q : {y : Fin 2 → ℝ // y ≠ 0} × (Fin 2 → ℝ) =>
          formKernel S (assemble q.1.1 q.2) :=
        continuous_iff_continuousAt.2 fun q =>
          ContinuousAt.comp
            (f := fun q : {y : Fin 2 → ℝ // y ≠ 0} × (Fin 2 → ℝ) => assemble q.1.1 q.2)
            (hKc _ (assemble_ne_zero q.1.2 q.2)) h1.continuousAt
      exact (Complex.continuous_ofReal.comp h2).mul (hCc.comp continuous_snd)
    have h3 := continuous_parametric_integral_of_continuous (μ := volume) hF hCs
    refine continuousOn_iff_continuous_domRestrict.2 ?_
    refine h3.congr fun y => ?_
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun ζ hζ => ?_
    simp [F, image_eq_zero_of_notMem_tsupport hζ]
  · intro r hr y hy
    have e : (fun ζ : Fin 2 → ℝ => ((ofCoords (formKernel S) (planeCoords (r (embedPlane y))) ζ :
        ℝ) : ℂ) * profileCorr φ φ ζ) = fun ζ =>
          ((ofCoords (formKernel S) y ζ : ℝ) : ℂ) * profileCorr φ φ ζ := by
      funext ζ
      have h1 : ofCoords (formKernel S) (planeCoords (r (embedPlane y))) ζ =
          ofCoords (formKernel S) y ζ := by
        simp only [ofCoords]
        rw [← hsym r hr y ζ]
        exact hK.invariant r hr.1 _ (assemble_ne_zero hy ζ)
      rw [h1]
    simp only [transverseAveragedKernel]
    rw [e]
end
section
variable {S : (AmbientSpace → ℂ) → (AmbientSpace → ℂ) → ℝ} {φ : (Fin 2 → ℝ) → ℂ}
theorem tensorPlate_assemble (α φ : (Fin 2 → ℝ) → ℂ) (y z : Fin 2 → ℝ) :
    tensorPlate α φ (assemble y z) = α y * φ z := by
  simp [tensorPlate, planeCoords_assemble, transCoords_assemble]
theorem isRestrictedFormKernel_of (hK : IsAnalyticKernel S (formKernel S))
    (hplates : ∀ α ∈ cc1Plane, tensorPlate α φ ∈ compactC1Complex)
    (hdisjoint : ∀ α ∈ cc1Plane, ∀ α' ∈ cc1Plane,
      Disjoint (tsupport α) (tsupport α') →
        DisjointSupports (tensorPlate α φ) (tensorPlate α' φ))
    (hφ : φ ∈ cc1Plane) : IsRestrictedFormKernel S φ := by
  intro α hα α' hα' hd
  have hf := hplates α hα
  have hh := hplates α' hα'
  have hdis := hdisjoint α hα α' hα' hd
  have hKc : ∀ x, x ≠ 0 → ContinuousAt (fun x => ((formKernel S x : ℝ) : ℂ)) x :=
    fun x hx => Complex.continuous_ofReal.continuousAt.comp
      (continuousAt_of_isRealAnalyticAwayFromZero hK.analytic hx)
  have hprod := continuous_mul_kernel_of_disjoint_tsupport
    (compactC1Complex_dest hf).1.continuous (compactC1Complex_dest hh).1.continuous hdis hKc
  let H : (Fin 2 → ℝ) → (Fin 2 → ℝ) → (Fin 2 → ℝ) → (Fin 2 → ℝ) → ℂ := fun y y' υ υ' =>
    tensorPlate α φ (assemble y υ) * tensorPlate α' φ (assemble y' υ') *
      ((formKernel S (assemble y' υ' - assemble y υ) : ℝ) : ℂ)
  have hc : Continuous fun p : ((Fin 2 → ℝ) × (Fin 2 → ℝ)) × ((Fin 2 → ℝ) × (Fin 2 → ℝ)) =>
      H p.1.1 p.2.1 p.1.2 p.2.2 :=
    hprod.comp (f := fun p : ((Fin 2 → ℝ) × (Fin 2 → ℝ)) × ((Fin 2 → ℝ) × (Fin 2 → ℝ)) =>
      (assemble p.1.1 p.1.2, assemble p.2.1 p.2.2))
      ((continuous_assemble.comp continuous_fst).prodMk
        (continuous_assemble.comp continuous_snd))
  have hs : ∀ y y' υ υ', H y y' υ υ' ≠ 0 →
      y ∈ tsupport α ∧ y' ∈ tsupport α' ∧ υ ∈ tsupport φ ∧ υ' ∈ tsupport φ := by
    intro y y' υ υ' hne
    simp only [H, tensorPlate_assemble, ne_eq, mul_eq_zero, not_or] at hne
    exact ⟨subset_tsupport _ hne.1.1.1, subset_tsupport _ hne.1.2.1,
      subset_tsupport _ hne.1.1.2, subset_tsupport _ hne.1.2.2⟩
  have h4 := integral_prod_prod_eq_iterated_shift H hc (cc1In_dest hα).2.1
    (cc1In_dest hα').2.1 (cc1In_dest hφ).2.1 (cc1In_dest hφ).2.1 hs
  have hrep := hK.represents _ hf _ hh hdis
  change complexifyForm S (tensorPlate α φ) (tensorPlate α' φ) = ∫ y', ∫ y, α y * α' y' *
    transverseAveragedKernel S φ (y' - y)
  rw [hrep]
  change (∫ x', ∫ x, tensorPlate α φ x * tensorPlate α' φ x' *
    ((formKernel S (x' - x) : ℝ) : ℂ)) = _
  rw [integral_eq_integral_assemble]
  have hin : ∀ p' : (Fin 2 → ℝ) × (Fin 2 → ℝ),
      ∫ x, tensorPlate α φ x * tensorPlate α' φ (assemble p'.1 p'.2) *
        ((formKernel S (assemble p'.1 p'.2 - x) : ℝ) : ℂ) =
      ∫ p : (Fin 2 → ℝ) × (Fin 2 → ℝ), H p.1 p'.1 p.2 p'.2 := fun p' =>
    integral_eq_integral_assemble _
  simp only [hin]
  rw [h4]
  refine integral_congr_ae (Eventually.of_forall fun y' => ?_)
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  beta_reduce
  have hH : ∀ ζ υ, H y y' υ (υ + ζ) =
      (α y * α' y' * ((ofCoords (formKernel S) (y' - y) ζ : ℝ) : ℂ)) * (φ υ * φ (υ + ζ)) := by
    intro ζ υ
    simp only [H, tensorPlate_assemble, assemble_sub_assemble, ofCoords, add_sub_cancel_left]
    ring
  simp only [hH, integral_const_mul]
  have e : transverseAveragedKernel S φ (y' - y) =
      ∫ ζ, ((ofCoords (formKernel S) (y' - y) ζ : ℝ) : ℂ) * ∫ υ, φ υ * φ (υ + ζ) := rfl
  rw [e, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun ζ => ?_)
  beta_reduce
  ring
end
section
variable {S : (AmbientSpace → ℂ) → (AmbientSpace → ℂ) → ℝ} {φ : (Fin 2 → ℝ) → ℂ}
theorem integral_eq_integral_basis {u v : Fin 2 → ℝ} (hdet : |u 0 * v 1 - v 0 * u 1| = 1)
    {g : (Fin 2 → ℝ) → ℂ} (hg : Integrable g) :
    ∫ y, g y = ∫ s : ℝ, ∫ t : ℝ, g (t • u + s • v) := by
  let M : Matrix (Fin 2) (Fin 2) ℝ := !![u 0, v 0; u 1, v 1]
  have hdetM : M.det = u 0 * v 1 - v 0 * u 1 := by simp [M, Matrix.det_fin_two]
  have hne : M.det ≠ 0 := by
    intro h
    rw [hdetM] at h
    rw [h] at hdet
    simp at hdet
  have hmap : Measure.map (Matrix.toLin' M) volume = (volume : Measure (Fin 2 → ℝ)) := by
    rw [Real.map_matrix_volume_pi_eq_smul_volume_pi hne, abs_inv, hdetM, hdet]
    simp
  have hmp : MeasurePreserving (Matrix.toLin' M) (volume : Measure (Fin 2 → ℝ)) volume :=
    ⟨(LinearMap.continuous_of_finiteDimensional _).measurable, hmap⟩
  have he := MeasurePreserving.symm _ (volume_preserving_finTwoArrow ℝ)
  have hc := hmp.comp he
  have hval : ∀ t s : ℝ, (Matrix.toLin' M) ((MeasurableEquiv.finTwoArrow (α := ℝ)).symm (t, s)) =
      t • u + s • v := by
    intro t s
    have hs : (MeasurableEquiv.finTwoArrow (α := ℝ)).symm (t, s) = ![t, s] := by
      funext i
      fin_cases i <;> rfl
    rw [hs]
    funext i
    fin_cases i <;> simp [M, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;>
      ring
  have h1 : ∫ y, g y = ∫ p : ℝ × ℝ,
      g ((Matrix.toLin' M) ((MeasurableEquiv.finTwoArrow (α := ℝ)).symm p)) := by
    have h := integral_map (μ := volume) hc.aemeasurable (f := g)
      (by rw [hc.map_eq]; exact hg.1)
    rw [hc.map_eq] at h
    exact h
  have hi : Integrable (fun p : ℝ × ℝ =>
      g ((Matrix.toLin' M) ((MeasurableEquiv.finTwoArrow (α := ℝ)).symm p)))
      ((volume : Measure ℝ).prod volume) := (hc.integrable_comp hg.1).2 hg
  rw [h1]
  refine (integral_prod_symm _ hi).trans ?_
  simp only [hval]
theorem mem_cc1In_ambient {O : Set AmbientSpace} {f : AmbientSpace → ℂ}
    (h : ContDiff ℝ 1 f ∧ IsCompact (tsupport f) ∧ tsupport f ⊆ O) :
    f ∈ cc1In O := h
theorem satisfiesNormalFrameFormula_of {m : AmbientSpace} (hnorm : euclidNorm m = 1)
    (hplane : m ∈ coordPlane)
    (hPl : ∀ α ∈ cc1Plane, tensorPlate α φ ∈ compactC1Complex ∧
      tsupport (tensorPlate α φ) =
        {x | planeCoords x ∈ tsupport α ∧ transCoords x ∈ tsupport φ})
    (hreal : ∀ z, (φ z).im = 0) (hker : IsRestrictedFormKernel S φ)
    (hG : ContinuousOn (transverseAveragedKernel S φ) {y | y ≠ 0}) :
    SatisfiesNormalFrameFormula S φ m := by
  have hm1 : m 1 = 0 := congrFun hplane 0
  have hm2 : m 2 = 0 := congrFun hplane 1
  have hsq : m 3 * m 3 + m 0 * m 0 = 1 := by
    have h2 : ∑ μ, m μ ^ 2 = 1 := Real.sqrt_eq_one.1 hnorm
    rw [Fin.sum_univ_four, hm1, hm2] at h2
    linear_combination h2
  set a : Fin 2 → ℝ := planeCoords m with ha
  set b : Fin 2 → ℝ := planeCoords (planePerp m) with hb
  have ha0 : a 0 = m 3 := rfl
  have ha1 : a 1 = m 0 := rfl
  have hb0 : b 0 = -(m 0) := by
    simp [hb, planeCoords, planePerp, PeriodicLattice.coordVec]
  have hb1 : b 1 = m 3 := by
    simp [hb, planeCoords, planePerp, PeriodicLattice.coordVec]
  have hfl1 : planePerp m 1 = 0 := by simp [planePerp, PeriodicLattice.coordVec]
  have hfl2 : planePerp m 2 = 0 := by simp [planePerp, PeriodicLattice.coordVec]
  have haa : a 0 * a 0 + a 1 * a 1 = 1 := by rw [ha0, ha1]; exact hsq
  have hab : a 0 * b 0 + a 1 * b 1 = 0 := by rw [ha0, ha1, hb0, hb1]; ring
  have hpp : ∀ t s : ℝ, planeCoords (t • m + s • planePerp m) = t • a + s • b := by
    intro t s
    funext i
    fin_cases i <;> simp [ha, hb, planeCoords]
  have hed : ∀ x : AmbientSpace, euclidDot m x = euclidDot a (planeCoords x) := by
    intro x
    simp only [euclidDot, Fin.sum_univ_four, Fin.sum_univ_two, hm1, hm2, ha0, ha1]
    simp [planeCoords]
    ring
  have hdot : ∀ c d : ℝ, euclidDot a (c • a + d • b) = c := by
    intro c d
    simp only [euclidDot, Fin.sum_univ_two, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination c * haa + d * hab
  have hRdef : ∀ y, reflectInPlane m y = y - (2 * euclidDot a y) • a := fun _ => rfl
  have hdotR : ∀ y, euclidDot a (reflectInPlane m y) = -euclidDot a y := by
    intro y
    rw [hRdef]
    simp only [euclidDot, Fin.sum_univ_two, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination (-(2 * (a 0 * y 0 + a 1 * y 1))) * haa
  have hRR : ∀ y, reflectInPlane m (reflectInPlane m y) = y := by
    intro y
    rw [hRdef (reflectInPlane m y), hdotR, hRdef y]
    module
  have hRfun : reflectInPlane m = fun y => y - (2 * (a 0 * y 0 + a 1 * y 1)) • a := by
    funext y
    simp [hRdef, euclidDot, Fin.sum_univ_two]
  have hRd : ContDiff ℝ 1 (reflectInPlane m) := by
    rw [hRfun]
    fun_prop
  let ιR : (Fin 2 → ℝ) ≃ₜ (Fin 2 → ℝ) :=
    { toFun := reflectInPlane m
      invFun := reflectInPlane m
      left_inv := hRR
      right_inv := hRR
      continuous_toFun := hRd.continuous
      continuous_invFun := hRd.continuous }
  intro α hα α' hα' t ht s
  set v : AmbientSpace := t • m + s • planePerp m with hv
  have hpv : planeCoords v = t • a + s • b := hpp t s
  have hv1 : v 1 = 0 := by simp [hv, hm1, hfl1]
  have hv2 : v 2 = 0 := by simp [hv, hm2, hfl2]
  have htr : translateFun v (tensorPlate α' φ) = tensorPlate (translatePlaneFun v α') φ := by
    funext x
    simp only [translateFun, tensorPlate, translatePlaneFun]
    have h1 : planeCoords (x - v) = planeCoords x - planeCoords v := by
      funext i
      fin_cases i <;> simp [planeCoords]
    have h2 : transCoords (x - v) = transCoords x := by
      funext i
      fin_cases i <;> simp [transCoords, hv1, hv2]
    rw [h1, h2]
  let ιT : (Fin 2 → ℝ) ≃ₜ (Fin 2 → ℝ) :=
    { toFun := fun y => y - planeCoords v
      invFun := fun y => y + planeCoords v
      left_inv := fun y => by simp
      right_inv := fun y => by simp
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  have hβ : translatePlaneFun v α' ∈ cc1In {y : Fin 2 → ℝ | 0 < euclidDot a y} := by
    refine cc1In_mono ?_ (comp_homeomorph_mem_cc1In hα' ιT (contDiff_id.sub contDiff_const))
    intro y hy
    have h1 : 0 < euclidDot a (y - planeCoords v) := hy
    have h2 : euclidDot a (y - planeCoords v) =
        euclidDot a y - euclidDot a (planeCoords v) := by
      simp only [euclidDot, Fin.sum_univ_two, Pi.sub_apply]
      ring
    have h3 : euclidDot a (planeCoords v) = t := by rw [hpv]; exact hdot t s
    change 0 < euclidDot a y
    rw [h2, h3] at h1
    linarith
  have hγ : reflectPlaneFun m (conjFun α) ∈
      cc1In (reflectInPlane m ⁻¹' {y : Fin 2 → ℝ | 0 < euclidDot a y}) :=
    comp_homeomorph_mem_cc1In (conjFun_mem_cc1In hα) ιR hRd
  have hγneg : ∀ y ∈ tsupport (reflectPlaneFun m (conjFun α)), euclidDot a y < 0 := by
    intro y hy
    have h1 : 0 < euclidDot a (reflectInPlane m y) := (cc1In_dest hγ).2.2 hy
    rw [hdotR] at h1
    linarith
  have hd : Disjoint (tsupport (reflectPlaneFun m (conjFun α)))
      (tsupport (translatePlaneFun v α')) := by
    refine Set.disjoint_left.2 fun y h1 h2 => ?_
    have h3 := hγneg y h1
    have h4 : 0 < euclidDot a y := (cc1In_dest hβ).2.2 h2
    linarith
  have hdom : ∀ β ∈ cc1In {y : Fin 2 → ℝ | 0 < euclidDot a y},
      tensorPlate β φ ∈ halfSpaceDomain m := by
    intro β hβ'
    have hb' : β ∈ cc1Plane := cc1In_mono (subset_univ _) hβ'
    obtain ⟨h1, h2⟩ := hPl β hb'
    refine mem_cc1In_ambient ⟨(compactC1Complex_dest h1).1, (compactC1Complex_dest h1).2.1,
      fun x hx => ?_⟩
    rw [h2] at hx
    have h3 : 0 < euclidDot a (planeCoords x) := (cc1In_dest hβ').2.2 hx.1
    change 0 < euclidDot m x
    rw [hed]
    exact h3
  have hmem := hdom α hα
  have hmem' : translateFun v (tensorPlate α' φ) ∈ halfSpaceDomain m := by
    rw [htr]
    exact hdom _ hβ
  refine ⟨hmem, hmem', ?_⟩
  have hmir : reflectFun m (conjFun (tensorPlate α φ)) =
      tensorPlate (reflectPlaneFun m (conjFun α)) φ := by
    funext x
    have h1 : planeCoords (reflectAcross m x) = reflectInPlane m (planeCoords x) := by
      rw [hRdef]
      simp only [reflectAcross, hed]
      funext i
      fin_cases i <;> simp [planeCoords, ha]
    have h2 : transCoords (reflectAcross m x) = transCoords x := by
      funext i
      fin_cases i <;> simp [transCoords, reflectAcross, hm1, hm2]
    have h3 : ∀ z, (starRingEnd ℂ) (φ z) = φ z := fun z => Complex.conj_eq_iff_im.2 (hreal z)
    simp only [reflectFun, tensorPlate, conjFun, reflectPlaneFun, Function.comp, map_mul, h1, h2,
      h3]
  have e1 : reflectedForm S m ⟨_, hmem⟩ ⟨_, hmem'⟩ =
      complexifyForm S (reflectFun m (conjFun (tensorPlate α φ)))
        (translateFun v (tensorPlate α' φ)) := rfl
  rw [e1, hmir, htr]
  have hk := hker _ (cc1In_mono (subset_univ _) hγ) _ (cc1In_mono (subset_univ _) hβ) hd
  refine (show complexifyForm S _ _ = _ from hk).trans ?_
  have hGc : ∀ y, y ≠ 0 → ContinuousAt (transverseAveragedKernel S φ) y := fun y hy =>
    (hG y hy).continuousAt (isOpen_ne.mem_nhds hy)
  have hQc := continuous_mul_kernel_of_disjoint_tsupport (cc1In_dest hγ).1.continuous
    (cc1In_dest hβ).1.continuous hd hGc
  have hQi : Integrable (fun p : (Fin 2 → ℝ) × (Fin 2 → ℝ) =>
      reflectPlaneFun m (conjFun α) p.1 * translatePlaneFun v α' p.2 *
        transverseAveragedKernel S φ (p.2 - p.1)) (volume.prod volume) := by
    refine integrable_of_support_subset_compact hQc
      ((cc1In_dest hγ).2.1.prod (cc1In_dest hβ).2.1) fun p hp => ?_
    simp only [ne_eq, mul_eq_zero, not_or] at hp
    exact ⟨subset_tsupport _ hp.1.1, subset_tsupport _ hp.1.2⟩
  have hW : Integrable (fun y' : Fin 2 → ℝ => ∫ y, reflectPlaneFun m (conjFun α) y *
      translatePlaneFun v α' y' * transverseAveragedKernel S φ (y' - y)) :=
    hQi.integral_prod_right
  have hslice : ∀ y' : Fin 2 → ℝ, Integrable (fun y : Fin 2 → ℝ =>
      reflectPlaneFun m (conjFun α) y * translatePlaneFun v α' y' *
        transverseAveragedKernel S φ (y' - y)) := by
    intro y'
    refine integrable_of_support_subset_compact
      (hQc.comp (f := fun y : Fin 2 → ℝ => (y, y')) (by fun_prop)) (cc1In_dest hγ).2.1
      fun y hy => ?_
    simp only [ne_eq, mul_eq_zero, not_or] at hy
    exact subset_tsupport _ hy.1.1
  have hdetA : |a 0 * b 1 - b 0 * a 1| = 1 := by
    have : a 0 * b 1 - b 0 * a 1 = 1 := by
      rw [ha0, ha1, hb0, hb1]
      linear_combination hsq
    rw [this]
    simp
  have hdetB : |(-a) 0 * b 1 - b 0 * (-a) 1| = 1 := by
    have : (-a) 0 * b 1 - b 0 * (-a) 1 = -1 := by
      simp only [Pi.neg_apply]
      rw [ha0, ha1, hb0, hb1]
      linear_combination -hsq
    rw [this]
    simp
  change (∫ y', ∫ y, reflectPlaneFun m (conjFun α) y * translatePlaneFun v α' y' *
    transverseAveragedKernel S φ (y' - y)) = ∫ s₂ : ℝ, ∫ t₂ : ℝ, ∫ s₁ : ℝ, ∫ t₁ : ℝ,
      conjFun α (planeCoords (t₁ • m + s₁ • planePerp m)) *
        α' (planeCoords (t₂ • m + s₂ • planePerp m)) *
        transverseAveragedKernel S φ
          (planeCoords ((t + t₁ + t₂) • m + (s + s₂ - s₁) • planePerp m))
  rw [← integral_add_left_eq_self _ (planeCoords v),
    integral_eq_integral_basis hdetA (hW.comp_add_left _)]
  refine integral_congr_ae (Eventually.of_forall fun s₂ => ?_)
  refine integral_congr_ae (Eventually.of_forall fun t₂ => ?_)
  beta_reduce
  rw [integral_eq_integral_basis hdetB (hslice _)]
  refine integral_congr_ae (Eventually.of_forall fun s₁ => ?_)
  refine integral_congr_ae (Eventually.of_forall fun t₁ => ?_)
  beta_reduce
  have hRy : reflectInPlane m (t₁ • (-a) + s₁ • b) = t₁ • a + s₁ • b := by
    have h1 : euclidDot a (t₁ • (-a) + s₁ • b) = -t₁ := by
      rw [smul_neg, ← neg_smul]
      exact hdot _ _
    rw [hRdef, h1]
    module
  have h1 : planeCoords v + (t₂ • a + s₂ • b) - planeCoords v = t₂ • a + s₂ • b :=
    add_sub_cancel_left _ _
  have h2 : planeCoords v + (t₂ • a + s₂ • b) - (t₁ • (-a) + s₁ • b) =
      (t + t₁ + t₂) • a + (s + s₂ - s₁) • b := by
    rw [hpv]
    module
  change conjFun α (reflectInPlane m (t₁ • (-a) + s₁ • b)) *
      α' (planeCoords v + (t₂ • a + s₂ • b) - planeCoords v) *
      transverseAveragedKernel S φ (planeCoords v + (t₂ • a + s₂ • b) - (t₁ • (-a) + s₁ • b)) = _
  rw [hRy, h1, h2, hpp, hpp, hpp]
end
theorem holds (h₁ : AnalyticKernel.Statement)
    (h₂ : ReflectionsPlaneFacts.Statement) : Statement := by
  intro St S hF hP φ hφ
  have hK : IsAnalyticKernel S (formKernel S) := (h₁ St S hF hP).1
  obtain ⟨e1, -, -, -, -, e6, e7, e8⟩ := h₂
  have hφ' : φ ∈ cc1Plane := hφ.1
  have hI := isRegularAveragedKernel_of hK (fun r hr y z => (e6.2.2.1 r hr).2 y z) (e8 φ hφ φ hφ)
  have hk2 : IsRestrictedFormKernel S φ := isRestrictedFormKernel_of hK
    (fun α hα => (e7.1 α hα φ hφ).1)
    (fun α hα α' hα' hd => e7.2 α hα α' hα' φ hφ hd) hφ'
  refine ⟨hI, hk2, fun m hm => ?_⟩
  have hm' : m ∈ reflectionNormals ∧ m ∈ coordPlane := hm
  have hnorm : euclidNorm m = 1 := by
    rcases hm'.1 with ⟨μ, ε, hε, rfl⟩ | ⟨μ, ν, ε, ε', hμν, hε, hε', rfl⟩
    · exact e1.1 μ ε hε
    · exact e1.2.1 μ ν ε ε' hμν hε hε'
  exact satisfiesNormalFrameFormula_of hnorm hm'.2 (fun α hα => e7.1 α hα φ hφ) hφ.2 hk2
    hI.continuousOn
end YangMills.Construction.TwoPoints.AveragedKernelProperties
end
