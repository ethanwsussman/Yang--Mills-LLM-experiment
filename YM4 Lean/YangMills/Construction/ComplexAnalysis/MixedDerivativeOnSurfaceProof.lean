import YangMills.Construction.ComplexAnalysis.MixedDerivativeOnSurface
import YangMills.Construction.Matrices.HolomorphicOnMatrixFamilies
import Mathlib
set_option autoImplicit false
open Metric Set Filter
open scoped Topology Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.SurfaceMixedDerivative
theorem analyticAt_zero_of_differentiableOn
    (hA : Matrices.ComplexMatrix2.DifferentiableOnFamiliesAnalytic)
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    {U : Set E} {Φ : E → ℂ} (hU : IsOpen U) (hU0 : (0 : E) ∈ U) (hΦ : DifferentiableOn ℂ Φ U) :
    AnalyticAt ℂ Φ 0 := by
  let bs := Module.finBasis ℂ E
  let Pl : (Fin (Module.finrank ℂ E) → Matrices.ComplexMatrix2) →ₗ[ℂ] E :=
    { toFun := fun M => ∑ i, (M i 0 0) • bs i
      map_add' := fun M M' => by
        simp [add_smul, Finset.sum_add_distrib]
      map_smul' := fun c M => by
        simp [Finset.smul_sum, mul_smul] }
  let Ql : E →ₗ[ℂ] (Fin (Module.finrank ℂ E) → Matrices.ComplexMatrix2) :=
    { toFun := fun x i => (bs.repr x i) • (1 : Matrices.ComplexMatrix2)
      map_add' := fun x y => by
        funext i
        simp [add_smul]
      map_smul' := fun c x => by
        funext i
        simp [mul_smul] }
  let Ll : Matrices.ComplexMatrix2 →ₗ[ℂ] ℂ :=
    { toFun := fun M => M 0 0
      map_add' := fun M M' => rfl
      map_smul' := fun c M => rfl }
  let P : (Fin (Module.finrank ℂ E) → Matrices.ComplexMatrix2) →L[ℂ] E :=
    ⟨Pl, Pl.continuous_of_finiteDimensional⟩
  let Q : E →L[ℂ] (Fin (Module.finrank ℂ E) → Matrices.ComplexMatrix2) :=
    ⟨Ql, Ql.continuous_of_finiteDimensional⟩
  let L : Matrices.ComplexMatrix2 →L[ℂ] ℂ := ⟨Ll, Ll.continuous_of_finiteDimensional⟩
  have hPQ : ∀ x, P (Q x) = x := by
    intro x
    change ∑ i, ((bs.repr x i) • (1 : Matrices.ComplexMatrix2)) 0 0 • bs i = x
    simp
  let F : (Fin (Module.finrank ℂ E) → Matrices.ComplexMatrix2) → Matrices.ComplexMatrix2 :=
    fun M => Φ (P M) • (1 : Matrices.ComplexMatrix2)
  have hFd : DifferentiableOn ℂ F (P ⁻¹' U) := by
    have h1 : DifferentiableOn ℂ (fun M => Φ (P M)) (P ⁻¹' U) :=
      hΦ.comp P.differentiableOn (fun M hM => hM)
    exact h1.smul_const _
  have hFa := hA (Fin (Module.finrank ℂ E)) (P ⁻¹' U) F (hU.preimage P.continuous) hFd
  have hQ0 : Q 0 ∈ P ⁻¹' U := by
    change P (Q 0) ∈ U
    rw [hPQ]
    exact hU0
  have hcomp : AnalyticAt ℂ (fun x => L (F (Q x))) 0 :=
    L.analyticAt _ |>.comp ((hFa _ hQ0).comp (Q.analyticAt _))
  refine hcomp.congr (Eventually.of_forall fun x => ?_)
  change (Φ (P (Q x)) • (1 : Matrices.ComplexMatrix2)) 0 0 = Φ x
  rw [hPQ]
  simp
theorem hasDerivAt_zero_of_norm_le_mul_sq {F : Type} [NormedAddCommGroup F] [NormedSpace ℂ F]
    {f : ℂ → F} {K : ℝ} (hf0 : f 0 = 0) (hf : ∀ᶠ x in 𝓝 (0 : ℂ), ‖f x‖ ≤ K * ‖x‖ ^ 2) :
    HasDerivAt f 0 0 := by
  rw [hasDerivAt_iff_isLittleO_nhds_zero]
  have hO : f =O[𝓝 0] (fun x : ℂ => ‖x‖ ^ 2) := by
    refine Asymptotics.IsBigO.of_bound K ?_
    filter_upwards [hf] with x hx
    simpa using hx
  have ho : f =o[𝓝 0] (fun x : ℂ => x) :=
    hO.trans_isLittleO (Asymptotics.isLittleO_norm_pow_id (by norm_num))
  simpa [hf0] using ho
theorem norm_vecPair_le (s t : ℂ) {R : ℝ} (hs : ‖s‖ ≤ R) (ht : ‖t‖ ≤ R) :
    ‖(![s, t] : Coordinates.ComplexCoordinates 2)‖ ≤ R := by
  refine (pi_norm_le_iff_of_nonneg ((norm_nonneg s).trans hs)).2 fun i => ?_
  fin_cases i
  · simpa using hs
  · simpa using ht
theorem differentiable_vecPair_snd (s : ℂ) :
    Differentiable ℂ (fun t : ℂ => (![s, t] : Coordinates.ComplexCoordinates 2)) := by
  refine differentiable_pi.2 fun i => ?_
  fin_cases i
  · simp
  · simp
theorem mixedDerivAtOrigin_eq {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {Φ : E → ℂ} (hΦ : AnalyticAt ℂ Φ 0) {V : Set (Coordinates.ComplexCoordinates 2)}
    {r : Coordinates.ComplexCoordinates 2 → E} (a b c d : E) {C δ : ℝ}
    (hV : IsOpen V) (hV0 : (0 : Coordinates.ComplexCoordinates 2) ∈ V) (hr : DifferentiableOn ℂ r V)
    (hδ : 0 < δ) (hb : ∀ z : Coordinates.ComplexCoordinates 2, ‖z‖ < δ → ‖r z‖ ≤ C * ‖z‖ ^ 3) :
    mixedDerivAtOrigin (fun s t => Φ (surfaceParam a b c d r s t)) =
      fderiv ℂ (fderiv ℂ Φ) 0 a b + fderiv ℂ Φ 0 c := by
  obtain ⟨ε₀, hε₀, hball⟩ := Metric.isOpen_iff.1 hV 0 hV0
  obtain ⟨ε, hε, hεε, hεδ, hε1⟩ : ∃ ε : ℝ, 0 < ε ∧ ε ≤ ε₀ ∧ ε ≤ δ ∧ ε ≤ 1 :=
    ⟨min ε₀ (min δ 1), lt_min hε₀ (lt_min hδ one_pos), min_le_left _ _,
      (min_le_right _ _).trans (min_le_left _ _), (min_le_right _ _).trans (min_le_right _ _)⟩
  have hzero : (![0, 0] : Coordinates.ComplexCoordinates 2) = 0 := by
    funext i
    fin_cases i <;> rfl
  have hr0 : r 0 = 0 := by
    have := hb 0 (by simpa using hδ)
    simpa using this
  have hin : ∀ (s t : ℂ) (R : ℝ), R < ε → ‖s‖ ≤ R → ‖t‖ ≤ R →
      (![s, t] : Coordinates.ComplexCoordinates 2) ∈ V := by
    intro s t R hR hs ht
    apply hball
    rw [mem_ball_zero_iff]
    exact (norm_vecPair_le s t hs ht).trans_lt (hR.trans_le hεε)
  have hbd : ∀ (s t : ℂ) (R : ℝ), R < ε → ‖s‖ ≤ R → ‖t‖ ≤ R →
      ‖r ![s, t]‖ ≤ |C| * R ^ 3 := by
    intro s t R hR hs ht
    have hn := norm_vecPair_le s t hs ht
    have hR0 : 0 ≤ R := (norm_nonneg s).trans hs
    calc ‖r ![s, t]‖ ≤ C * ‖(![s, t] : Coordinates.ComplexCoordinates 2)‖ ^ 3 :=
          hb _ (hn.trans_lt (hR.trans_le hεδ))
      _ ≤ |C| * ‖(![s, t] : Coordinates.ComplexCoordinates 2)‖ ^ 3 :=
          mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
      _ ≤ |C| * R ^ 3 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hn 3) (abs_nonneg C)
  have hsmall : ∀ᶠ s in 𝓝 (0 : ℂ), ‖s‖ < ε := by
    have := Metric.ball_mem_nhds (0 : ℂ) hε
    filter_upwards [this] with s hs
    simpa using hs
  have hcube : ∀ {R : ℝ}, 0 ≤ R → R < ε → |C| * R ^ 3 ≤ |C| * R ^ 2 := by
    intro R h0 h1
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg C)
    have h2 : R ≤ 1 := (h1.trans_le hε1).le
    calc R ^ 3 = R ^ 2 * R := by ring
      _ ≤ R ^ 2 * 1 := mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = R ^ 2 := by ring
  have hs0 : HasDerivAt (fun s : ℂ => r ![s, 0]) 0 0 := by
    refine hasDerivAt_zero_of_norm_le_mul_sq (K := |C|) (by rw [hzero, hr0]) ?_
    filter_upwards [hsmall] with s hs
    exact (hbd s 0 ‖s‖ hs le_rfl (by simp)).trans (hcube (norm_nonneg s) hs)
  have ht0 : HasDerivAt (fun t : ℂ => r ![0, t]) 0 0 := by
    refine hasDerivAt_zero_of_norm_le_mul_sq (K := |C|) (by rw [hzero, hr0]) ?_
    filter_upwards [hsmall] with t ht
    exact (hbd 0 t ‖t‖ ht (by simp) le_rfl).trans (hcube (norm_nonneg t) ht)
  let ρ : ℂ → E := fun s => deriv (fun t : ℂ => r ![s, t]) 0
  have hρ0 : ρ 0 = 0 := ht0.deriv
  have hdiff : ∀ (s t : ℂ) (R : ℝ), R < ε → ‖s‖ ≤ R → ‖t‖ ≤ R →
      DifferentiableAt ℂ (fun t : ℂ => r ![s, t]) t := by
    intro s t R hR hs ht
    have h1 : DifferentiableAt ℂ r ![s, t] :=
      (hr _ (hin s t R hR hs ht)).differentiableAt (hV.mem_nhds (hin s t R hR hs ht))
    exact h1.comp t (differentiable_vecPair_snd s t)
  have hρbound : ∀ᶠ s in 𝓝 (0 : ℂ), ‖ρ s‖ ≤ |C| * ‖s‖ ^ 2 := by
    filter_upwards [hsmall] with s hs
    by_cases hz : s = 0
    · subst hz
      simp [hρ0]
    have hpos : 0 < ‖s‖ := norm_pos_iff.2 hz
    have hdc : DiffContOnCl ℂ (fun t : ℂ => r ![s, t]) (ball 0 ‖s‖) := by
      refine DifferentiableOn.diffContOnCl ?_
      rw [closure_ball _ hpos.ne']
      intro t ht
      exact (hdiff s t ‖s‖ hs le_rfl (by simpa using ht)).differentiableWithinAt
    have hc := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hpos hdc
      (C := |C| * ‖s‖ ^ 3) (fun t ht => hbd s t ‖s‖ hs le_rfl (by simpa using ht.le))
    refine hc.trans (le_of_eq ?_)
    field_simp
  have hρd : HasDerivAt ρ 0 0 := hasDerivAt_zero_of_norm_le_mul_sq hρ0 hρbound
  let σ : ℂ → E := fun s => s • a + r ![s, 0]
  let β : ℂ → E := fun s => b + s • c + ρ s
  have hσ : HasDerivAt σ a 0 := by
    have h1 : HasDerivAt (fun s : ℂ => s • a) a 0 := by
      simpa using (hasDerivAt_id (0 : ℂ)).smul_const a
    exact (h1.add hs0).congr_deriv (by simp)
  have hσ0 : σ 0 = 0 := by
    simp [σ, hzero, hr0]
  have hβ : HasDerivAt β c 0 := by
    have h1 : HasDerivAt (fun s : ℂ => s • c) c 0 := by
      simpa using (hasDerivAt_id (0 : ℂ)).smul_const c
    exact ((h1.const_add b).add hρd).congr_deriv (by simp)
  have hβ0 : β 0 = b := by
    simp [β, hρ0]
  have hD : DifferentiableAt ℂ (fderiv ℂ Φ) 0 := hΦ.fderiv.differentiableAt
  have hDσ : HasDerivAt (fun s => fderiv ℂ Φ (σ s)) (fderiv ℂ (fderiv ℂ Φ) 0 a) 0 := by
    have h1 : HasFDerivAt (fderiv ℂ Φ) (fderiv ℂ (fderiv ℂ Φ) 0) (σ 0) := by
      rw [hσ0]
      exact hD.hasFDerivAt
    exact h1.comp_hasDerivAt 0 hσ
  have hprod : HasDerivAt (fun s => fderiv ℂ Φ (σ s) (β s))
      (fderiv ℂ (fderiv ℂ Φ) 0 a b + fderiv ℂ Φ 0 c) 0 := by
    have h1 := hDσ.clm_apply hβ
    rw [hσ0, hβ0] at h1
    exact h1
  have hev : ∀ᶠ s in 𝓝 (0 : ℂ), AnalyticAt ℂ Φ (σ s) := by
    have h1 : ∀ᶠ x in 𝓝 (σ 0), AnalyticAt ℂ Φ x := by
      rw [hσ0]
      exact hΦ.eventually_analyticAt
    exact hσ.continuousAt.eventually h1
  have hinner : (fun s : ℂ => deriv (fun t : ℂ => Φ (surfaceParam a b c d r s t)) 0) =ᶠ[𝓝 0]
      fun s => fderiv ℂ Φ (σ s) (β s) := by
    filter_upwards [hsmall, hev] with s hs hΦs
    have hrt : HasDerivAt (fun t : ℂ => r ![s, t]) (ρ s) 0 :=
      (hdiff s 0 ‖s‖ hs le_rfl (by simp)).hasDerivAt
    have h1 : HasDerivAt (fun t : ℂ => t • b) b 0 := by
      simpa using (hasDerivAt_id (0 : ℂ)).smul_const b
    have h2 : HasDerivAt (fun t : ℂ => (s * t) • c) (s • c) 0 := by
      simpa using ((hasDerivAt_id (0 : ℂ)).const_mul s).smul_const c
    have h3 : HasDerivAt (fun t : ℂ => t ^ 2 • d) 0 0 := by
      simpa using ((hasDerivAt_id (0 : ℂ)).pow 2).smul_const d
    have hγ : HasDerivAt (fun t : ℂ => surfaceParam a b c d r s t) (β s) 0 := by
      exact ((((h1.const_add (s • a)).add h2).add h3).add hrt).congr_deriv (by simp [β])
    have hγ0 : surfaceParam a b c d r s 0 = σ s := by
      simp [surfaceParam, σ]
    have hF : HasFDerivAt Φ (fderiv ℂ Φ (σ s)) (surfaceParam a b c d r s 0) := by
      rw [hγ0]
      exact hΦs.differentiableAt.hasFDerivAt
    exact (hF.comp_hasDerivAt 0 hγ).deriv
  exact (hprod.congr_of_eventuallyEq hinner).deriv
theorem mixedDerivAlongSurface_holds
    (hA : Matrices.ComplexMatrix2.DifferentiableOnFamiliesAnalytic) :
    MixedDerivAlongSurface := by
  intro E _ _ _ U Φ V r a b c d C δ hU hU0 hΦ hV hV0 hr hδ hb
  have han := analyticAt_zero_of_differentiableOn hA hU hU0 hΦ
  have h1 := mixedDerivAtOrigin_eq han a b c d hV hV0 hr hδ hb
  have h2 := mixedDerivAtOrigin_eq han a b 0 0 (r := fun _ => (0 : E)) (C := 0) (δ := 1)
    isOpen_univ (mem_univ _) (differentiableOn_const _) one_pos (fun z _ => by simp)
  have h3 : (fun s t => Φ (surfaceParam a b 0 0 (fun _ => (0 : E)) s t)) =
      fun s t => Φ (s • a + t • b) := by
    funext s t
    simp [surfaceParam]
  rw [h3] at h2
  have h4 : deriv (fun t : ℂ => Φ (t • c)) 0 = fderiv ℂ Φ 0 c := by
    have hl : HasDerivAt (fun t : ℂ => t • c) c 0 := by
      simpa using (hasDerivAt_id (0 : ℂ)).smul_const c
    have hF : HasFDerivAt Φ (fderiv ℂ Φ 0) ((0 : ℂ) • c) := by
      rw [zero_smul]
      exact han.differentiableAt.hasFDerivAt
    exact (hF.comp_hasDerivAt 0 hl).deriv
  rw [h1, h2, h4]
  simp
end YangMills.Construction.SurfaceMixedDerivative
end
