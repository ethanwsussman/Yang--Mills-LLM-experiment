import YangMills.Construction.Analysis.ZerosOfAnalyticMapsAndThinSets
import YangMills.Construction.ComplexAnalysis.RealAnalyticInCoordinates
import YangMills.Construction.Coordinates.PowerSeriesHolomorphy
import Mathlib
open Set Filter
open scoped Topology
noncomputable section
namespace YangMills.Construction.Analysis
open YangMills.Construction.Coordinates
open YangMills.Construction.Coordinates.ComplexCoordinates
theorem differentiableOn_of_isHolomorphicIn
    (H : ComplexCoordinates.PowerSeriesHolomorphy.Properties) {q : ℕ}
    {D : Set (ComplexCoordinates q)} (hD : IsOpen D) {g : ComplexCoordinates q → ℂ}
    (hg : IsHolomorphicIn (N' := 1) D (fun z _ => g z)) : DifferentiableOn ℂ g D := by
  intro b hb
  obtain ⟨L, hL⟩ := ((H.1 q D hD).1 1 _ hg).2.2.1 b hb
  have hL' : HasFDerivAt (fun z (_ : Fin 1) => g z) L b := hasFDerivAt_of_restrictScalars ℝ hL rfl
  have h0 : HasFDerivAt g ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 => ℂ) 0).comp L) b :=
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 => ℂ) 0).hasFDerivAt.comp b hL'
  exact h0.differentiableAt.differentiableWithinAt
theorem eq_zero_on_complexLine_of_eventually_zero_real {q : ℕ} {D : Set (ComplexCoordinates q)}
    (hDo : IsOpen D) (hDc : Convex ℝ D) {g : ComplexCoordinates q → ℂ} (hg : DifferentiableOn ℂ g D)
    (a v : ComplexCoordinates q) (ha : a ∈ D) (ζ : ℂ) (hζ : a + ζ • v ∈ D)
    (h0 : ∀ᶠ t : ℝ in 𝓝 0, g (a + (t : ℂ) • v) = 0) : g (a + ζ • v) = 0 := by
  have hφd : Differentiable ℂ (fun ζ : ℂ => a + ζ • v) := by fun_prop
  have hOo : IsOpen ((fun ζ : ℂ => a + ζ • v) ⁻¹' D) := hDo.preimage hφd.continuous
  have hOc : Convex ℝ ((fun ζ : ℂ => a + ζ • v) ⁻¹' D) := by
    intro x hx y hy s t hs ht hst
    have hst' : (s : ℂ) + (t : ℂ) = 1 := by exact_mod_cast hst
    have hid : a + (s • x + t • y) • v = s • (a + x • v) + t • (a + y • v) := by
      ext j
      simp only [Pi.add_apply, Pi.smul_apply, Complex.real_smul, smul_eq_mul]
      linear_combination (-(a j)) * hst'
    show a + (s • x + t • y) • v ∈ D
    rw [hid]
    exact hDc hx hy hs ht hst
  have hd : DifferentiableOn ℂ (g ∘ fun ζ : ℂ => a + ζ • v) ((fun ζ : ℂ => a + ζ • v) ⁻¹' D) :=
    hg.comp hφd.differentiableOn (fun _ h => h)
  have han := hd.analyticOnNhd hOo
  have h00 : (0 : ℂ) ∈ (fun ζ : ℂ => a + ζ • v) ⁻¹' D := by simpa using ha
  have hfr : ∃ᶠ z in 𝓝[≠] (0 : ℂ), (g ∘ fun ζ : ℂ => a + ζ • v) z = 0 := by
    have hT : Tendsto (fun t : ℝ => (t : ℂ)) (𝓝[≠] 0) (𝓝[≠] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · exact (Complex.continuous_ofReal.tendsto' 0 0 (by simp)).mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with t ht
        simpa using ht
    exact hT.frequently (h0.filter_mono nhdsWithin_le_nhds).frequently
  exact han.eqOn_zero_of_preconnected_of_frequently_eq_zero hOc.isPreconnected h00 hfr hζ
theorem vanishingFromRealPoints_holds
    (H : ComplexCoordinates.PowerSeriesHolomorphy.Properties) (q : ℕ) :
    VanishingFromRealPoints q := by
  intro D hDo hDc hre g hg U hUne hUsub hUopen hU z hz
  obtain ⟨O, hOo, hUO⟩ := hUopen
  have hdiff := differentiableOn_of_isHolomorphicIn H hDo hg
  obtain ⟨y0, hy0⟩ := hUne
  have hy0D : y0 ∈ D := (hUsub hy0).1
  have hy0R : y0 ∈ realLocus q := (hUsub hy0).2
  have hreal : ∀ y1 ∈ D, y1 ∈ realLocus q → g y1 = 0 := by
    intro y1 hy1 hy1R
    have hev : ∀ᶠ t : ℝ in 𝓝 0, g (y0 + (t : ℂ) • (y1 - y0)) = 0 := by
      have hc : Continuous fun t : ℝ => y0 + (t : ℂ) • (y1 - y0) := by fun_prop
      have hmem : y0 ∈ O := by
        rw [hUO] at hy0
        exact hy0.1
      have hnh : O ∈ 𝓝 ((fun t : ℝ => y0 + (t : ℂ) • (y1 - y0)) 0) := by
        simpa using hOo.mem_nhds hmem
      filter_upwards [hc.continuousAt hnh] with t ht
      apply hU
      rw [hUO]
      refine ⟨ht, fun j => ?_⟩
      have h1 : (y0 j).im = 0 := hy0R j
      have h2 : (y1 j).im = 0 := hy1R j
      simp [h1, h2]
    have key := eq_zero_on_complexLine_of_eventually_zero_real hDo hDc hdiff y0 (y1 - y0) hy0D 1
      (by simpa using hy1) hev
    simpa using key
  have hx : (fun j => ((z j).re : ℂ) : ComplexCoordinates q) ∈ D := hre z hz
  have hzx : (fun j => ((z j).re : ℂ) : ComplexCoordinates q) +
      Complex.I • (fun j => ((z j).im : ℂ) : ComplexCoordinates q) = z := by
    ext j
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [mul_comm]
    exact Complex.re_add_im (z j)
  have hev : ∀ᶠ t : ℝ in 𝓝 0, g ((fun j => ((z j).re : ℂ) : ComplexCoordinates q) +
      (t : ℂ) • (fun j => ((z j).im : ℂ) : ComplexCoordinates q)) = 0 := by
    have hc : Continuous fun t : ℝ => (fun j => ((z j).re : ℂ) : ComplexCoordinates q) +
        (t : ℂ) • (fun j => ((z j).im : ℂ) : ComplexCoordinates q) := by fun_prop
    have hnh : D ∈ 𝓝 ((fun t : ℝ => (fun j => ((z j).re : ℂ) : ComplexCoordinates q) +
        (t : ℂ) • (fun j => ((z j).im : ℂ) : ComplexCoordinates q)) 0) := by
      simpa using hDo.mem_nhds hx
    filter_upwards [hc.continuousAt hnh] with t ht
    refine hreal _ ht fun j => ?_
    simp
  have key := eq_zero_on_complexLine_of_eventually_zero_real hDo hDc hdiff _ _ hx Complex.I
    (by rwa [hzx]) hev
  rwa [hzx] at key
theorem vanishingOfRealAnalytic_holds (H : RealAnalyticity.CoordRealAnalyticIffAnalytic) (q : ℕ) :
    VanishingOfRealAnalytic q := by
  intro D hDo hDc g hg W hWne hWo hW x hx
  have hDR : D ⊆ realLocus q := by
    obtain ⟨O, _, hO⟩ := hDo
    rw [hO]
    exact inter_subset_right
  obtain ⟨hopen, han⟩ := (H q D g hDR).1 hg
  have hιρ : ∀ z ∈ realLocus q,
      (fun j => (((fun j => (z j).re : Fin q → ℝ) j : ℝ) : ℂ) : ComplexCoordinates q) = z := by
    intro z hz
    ext j
    exact Complex.ext (by simp) (by simpa using (hz j).symm)
  have hρc : Continuous fun (z : ComplexCoordinates q) (j : Fin q) => (z j).re := by fun_prop
  have hιc : Continuous fun (u : Fin q → ℝ) (j : Fin q) => (u j : ℂ) := by fun_prop
  have hpre : IsPreconnected ((fun (u : Fin q → ℝ) (j : Fin q) => (u j : ℂ)) ⁻¹' D) := by
    have hE : (fun (u : Fin q → ℝ) (j : Fin q) => (u j : ℂ)) ⁻¹' D =
        (fun (z : ComplexCoordinates q) (j : Fin q) => (z j).re) '' D := by
      ext u
      constructor
      · intro hu
        exact ⟨_, hu, by ext j; simp⟩
      · rintro ⟨z, hz, rfl⟩
        show (fun j => (((fun j => (z j).re : Fin q → ℝ) j : ℝ) : ℂ) : ComplexCoordinates q) ∈ D
        rw [hιρ z (hDR hz)]
        exact hz
    rw [hE]
    exact hDc.isPreconnected.image _ hρc.continuousOn
  obtain ⟨w0, hw0⟩ := hWne
  obtain ⟨O, hOo, hWO⟩ := hWo
  have hw0' : w0 ∈ O ∩ D := hWO ▸ hw0
  have hmem : (fun j => (w0 j).re : Fin q → ℝ) ∈
      (fun (u : Fin q → ℝ) (j : Fin q) => (u j : ℂ)) ⁻¹' O ∩
        (fun (u : Fin q → ℝ) (j : Fin q) => (u j : ℂ)) ⁻¹' D := by
    constructor
    · show (fun j => (((fun j => (w0 j).re : Fin q → ℝ) j : ℝ) : ℂ) : ComplexCoordinates q) ∈ O
      rw [hιρ w0 (hDR hw0'.2)]
      exact hw0'.1
    · show (fun j => (((fun j => (w0 j).re : Fin q → ℝ) j : ℝ) : ℂ) : ComplexCoordinates q) ∈ D
      rw [hιρ w0 (hDR hw0'.2)]
      exact hw0'.2
  have hev : (fun u : Fin q → ℝ => g fun j => (u j : ℂ)) =ᶠ[𝓝 (fun j => (w0 j).re : Fin q → ℝ)] 0 := by
    filter_upwards [((hOo.preimage hιc).inter hopen).mem_nhds hmem] with u hu
    exact hW _ (hWO ▸ hu)
  have hall := han.eqOn_zero_of_preconnected_of_eventuallyEq_zero hpre hmem.2 hev
  have hxm : (fun j => (x j).re : Fin q → ℝ) ∈
      (fun (u : Fin q → ℝ) (j : Fin q) => (u j : ℂ)) ⁻¹' D := by
    show (fun j => (((fun j => (x j).re : Fin q → ℝ) j : ℝ) : ℂ) : ComplexCoordinates q) ∈ D
    rw [hιρ x (hDR hx)]
    exact hx
  have h := hall hxm
  simp only [Pi.zero_apply] at h
  rwa [hιρ x (hDR hx)] at h
theorem interior_zeroLocus_eq_empty {q : ℕ} (Q : MvPolynomial (Fin q) ℝ) (hQ : Q ≠ 0) :
    interior {x : Fin q → ℝ | MvPolynomial.eval x Q = 0} = ∅ := by
  by_contra hne
  obtain ⟨a, ha⟩ := nonempty_iff_ne_empty.2 hne
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 isOpen_interior a ha
  apply hQ
  refine MvPolynomial.funext_set (fun i => Metric.ball (a i) ε) (fun i => ?_) fun x hx => ?_
  · rw [Real.ball_eq_Ioo]
    exact Ioo_infinite (by linarith)
  · have hxb : x ∈ Metric.ball a ε := by
      rw [ball_pi _ hε]
      exact hx
    have h0 : x ∈ {x : Fin q → ℝ | MvPolynomial.eval x Q = 0} := interior_subset (hball hxb)
    simpa using h0
theorem isClosed_and_interior_eq_empty_of_ne_top {q : ℕ} (V : AffineSubspace ℝ (Fin q → ℝ))
    (hV : V ≠ ⊤) : IsClosed (V : Set (Fin q → ℝ)) ∧ interior (V : Set (Fin q → ℝ)) = ∅ := by
  refine ⟨V.closed_of_finiteDimensional, ?_⟩
  by_contra hne
  have htop := isOpen_interior.affineSpan_eq_top (nonempty_iff_ne_empty.2 hne)
  apply hV
  rw [eq_top_iff, ← htop]
  exact affineSpan_le.2 interior_subset
theorem nowhereDenseClosedSets_holds (q : ℕ) : NowhereDenseClosedSets q := by
  refine ⟨fun Q hQ => ⟨?_, interior_zeroLocus_eq_empty Q hQ⟩,
    fun V _ hV => isClosed_and_interior_eq_empty_of_ne_top V hV, fun p W hc hi => ?_⟩
  · exact isClosed_eq (MvPolynomial.continuous_eval Q) continuous_const
  · have hcl : IsClosed (⋃ a, W a) := isClosed_iUnion_of_finite hc
    have hd : Dense (⋃ a, W a)ᶜ := by
      rw [compl_iUnion]
      exact dense_iInter_of_isOpen (fun a => (hc a).isOpen_compl)
        fun a => interior_eq_empty_iff_dense_compl.1 (hi a)
    exact ⟨hcl, interior_eq_empty_iff_dense_compl.2 hd, hcl.isOpen_compl, hd⟩
theorem affineSpan_insert_ne_top_of_codim_two {q : ℕ} (V : AffineSubspace ℝ (Fin q → ℝ))
    (hne : (V : Set (Fin q → ℝ)).Nonempty) (hV : Module.finrank ℝ V.direction + 2 ≤ q)
    (x : Fin q → ℝ) : affineSpan ℝ (insert x (V : Set (Fin q → ℝ))) ≠ ⊤ := by
  obtain ⟨p, hp⟩ := hne
  intro htop
  have hdir : (affineSpan ℝ (insert x (V : Set (Fin q → ℝ)))).direction =
      Submodule.span ℝ {x -ᵥ p} ⊔ V.direction := AffineSubspace.direction_affineSpan_insert hp
  rw [htop, AffineSubspace.direction_top] at hdir
  have h1 : Module.finrank ℝ (⊤ : Submodule ℝ (Fin q → ℝ)) = q := by simp
  have h2 := Submodule.finrank_add_le_finrank_add_finrank (Submodule.span ℝ {x -ᵥ p}) V.direction
  have h3 : Module.finrank ℝ (Submodule.span ℝ {x -ᵥ p}) ≤ 1 := by
    simpa using finrank_span_le_card (R := ℝ) ({x -ᵥ p} : Set (Fin q → ℝ))
  rw [← hdir, h1] at h2
  omega
theorem segment_not_mem_of_not_mem_affineSpan_insert {q : ℕ} (V : AffineSubspace ℝ (Fin q → ℝ))
    {x y : Fin q → ℝ} (hx : x ∉ V) (hy : y ∉ affineSpan ℝ (insert x (V : Set (Fin q → ℝ)))) :
    ∀ p ∈ segment ℝ x y, p ∉ V := by
  intro p hp hpV
  rw [segment_eq_image_lineMap] at hp
  obtain ⟨τ, -, rfl⟩ := hp
  have hτ : τ ≠ 0 := by
    rintro rfl
    exact hx (by simpa using hpV)
  apply hy
  have hxW : x ∈ affineSpan ℝ (insert x (V : Set (Fin q → ℝ))) :=
    subset_affineSpan ℝ _ (mem_insert _ _)
  have hpW : AffineMap.lineMap x y τ ∈ affineSpan ℝ (insert x (V : Set (Fin q → ℝ))) :=
    subset_affineSpan ℝ _ (mem_insert_of_mem _ hpV)
  have hid : y = AffineMap.lineMap x (AffineMap.lineMap x y τ) τ⁻¹ := by
    simp [AffineMap.lineMap_apply, smul_smul, inv_mul_cancel₀ hτ]
  rw [hid]
  exact AffineMap.lineMap_mem _ hxW hpW
theorem complementOfCodimTwoSubspaces_holds (q : ℕ) : ComplementOfCodimTwoSubspaces q := by
  intro _ p _ V hne hfin
  have hVtop : ∀ a, V a ≠ ⊤ := by
    intro a htop
    have h := hfin a
    rw [htop, AffineSubspace.direction_top] at h
    simp at h
  have hc : ∀ a, IsClosed (V a : Set (Fin q → ℝ)) := fun a =>
    (isClosed_and_interior_eq_empty_of_ne_top _ (hVtop a)).1
  have hi : ∀ a, interior (V a : Set (Fin q → ℝ)) = ∅ := fun a =>
    (isClosed_and_interior_eq_empty_of_ne_top _ (hVtop a)).2
  obtain ⟨-, -, hopen, hdense⟩ :=
    (nowhereDenseClosedSets_holds q).2.2 p (fun a => (V a : Set (Fin q → ℝ))) hc hi
  refine ⟨hopen, hdense, hdense.nonempty, ?_⟩
  refine isPreconnected_of_forall_pair fun x hx x' hx' => ?_
  have hxa : ∀ a, x ∉ V a := fun a h => hx (mem_iUnion.2 ⟨a, h⟩)
  have hxa' : ∀ a, x' ∉ V a := fun a h => hx' (mem_iUnion.2 ⟨a, h⟩)
  have hF : ∀ i : Fin p ⊕ Fin p,
      Dense ((Sum.elim (fun a => affineSpan ℝ (insert x (V a : Set (Fin q → ℝ))))
        (fun a => affineSpan ℝ (insert x' (V a : Set (Fin q → ℝ)))) i : AffineSubspace ℝ _) :
          Set (Fin q → ℝ))ᶜ ∧
      IsOpen ((Sum.elim (fun a => affineSpan ℝ (insert x (V a : Set (Fin q → ℝ))))
        (fun a => affineSpan ℝ (insert x' (V a : Set (Fin q → ℝ)))) i : AffineSubspace ℝ _) :
          Set (Fin q → ℝ))ᶜ := by
    rintro (a | a)
    all_goals
      obtain ⟨h1, h2⟩ := isClosed_and_interior_eq_empty_of_ne_top _
        (affineSpan_insert_ne_top_of_codim_two (V a) (hne a) (hfin a) _)
      exact ⟨interior_eq_empty_iff_dense_compl.1 h2, h1.isOpen_compl⟩
  obtain ⟨y, hy⟩ := (dense_iInter_of_isOpen (fun i => (hF i).2) fun i => (hF i).1).nonempty
  rw [mem_iInter] at hy
  have hy1 : ∀ a, y ∉ affineSpan ℝ (insert x (V a : Set (Fin q → ℝ))) := fun a => hy (Sum.inl a)
  have hy2 : ∀ a, y ∉ affineSpan ℝ (insert x' (V a : Set (Fin q → ℝ))) := fun a => hy (Sum.inr a)
  refine ⟨segment ℝ x y ∪ segment ℝ x' y, ?_, Or.inl (left_mem_segment ℝ x y),
    Or.inr (left_mem_segment ℝ x' y), ?_⟩
  · rintro u (hu | hu)
    · exact fun h => by
        obtain ⟨a, ha⟩ := mem_iUnion.1 h
        exact segment_not_mem_of_not_mem_affineSpan_insert (V a) (hxa a) (hy1 a) u hu ha
    · exact fun h => by
        obtain ⟨a, ha⟩ := mem_iUnion.1 h
        exact segment_not_mem_of_not_mem_affineSpan_insert (V a) (hxa' a) (hy2 a) u hu ha
  · exact IsPreconnected.union y (right_mem_segment ℝ x y) (right_mem_segment ℝ x' y)
      (convex_segment x y).isPreconnected (convex_segment x' y).isPreconnected
theorem zerosOfAnalyticMapsAndThinSets_holds
    (H₁ : ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (H₂ : RealAnalyticity.CoordRealAnalyticIffAnalytic) : ZerosOfAnalyticMapsAndThinSets := fun q _ =>
  ⟨vanishingFromRealPoints_holds H₁ q, vanishingOfRealAnalytic_holds H₂ q,
    nowhereDenseClosedSets_holds q, complementOfCodimTwoSubspaces_holds q⟩
end YangMills.Construction.Analysis
end
