import YangMills.Construction.Matrices.HolomorphicOnMatrixFamiliesProof
import YangMills.Construction.SourcesOnAFlow.BoundedMapsHolomorphicAlongLinesAreAnalytic
import Mathlib
set_option autoImplicit false
open Metric Set Complex MeasureTheory
open scoped Matrix.Norms.L2Operator Topology Real NNReal
noncomputable section
namespace YangMills.Construction.ComplexAnalysis.LineHolomorphy
theorem analyticAt_of_separating_differentiableOn {X Y ι : Type}
    [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℂ Y] [CompleteSpace Y]
    (h : ℂ → X) (c : ℂ) (R : ℝ) (hR : 0 < R)
    (hc : ContinuousOn h (closedBall c R))
    (L : ι → X →L[ℂ] Y) (hsep : ∀ x, (∀ i, L i x = 0) → x = 0)
    (hdiff : ∀ i, DifferentiableOn ℂ (fun s => L i (h s)) (ball c R)) :
    AnalyticAt ℂ h c := by
  exact _root_.YangMills.Construction.Matrices.Osgood.analyticAt_of_separating_family
    h c R hR hc L hsep hdiff
theorem exists_continuousOn_continuousMap_of_uncurry {T S F : Type} [TopologicalSpace T]
    [TopologicalSpace S] [CompactSpace S] [NormedAddCommGroup F] (A : Set T) (c : T → S → F)
    (hc : Continuous fun p : A × S => c p.1 p.2) :
    ∃ G : T → C(S, F), ContinuousOn G A ∧ ∀ t ∈ A, ∀ s, G t s = c t s := by apply _root_.YangMills.Construction.Matrices.Osgood.exists_continuousOn_curried <;> assumption
def SeparatelyHolomorphicAnalytic (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] : Prop :=
  ∀ (F : Type) [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F] (f : E → F) (U : Set E),
    IsOpen U → ContinuousOn f U →
    (∀ x ∈ U, ∀ v, DifferentiableAt ℂ (fun t : ℂ => f (x + t • v)) 0) → AnalyticOnNhd ℂ f U
theorem differentiableAt_along_line {E F : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] {f : E → F} {U : Set E}
    (hline : ∀ x ∈ U, ∀ v, DifferentiableAt ℂ (fun t : ℂ => f (x + t • v)) 0)
    {x v : E} {t : ℂ} (ht : x + t • v ∈ U) :
    DifferentiableAt ℂ (fun s : ℂ => f (x + s • v)) t := by apply _root_.YangMills.Construction.Matrices.Osgood.differentiableAt_along_line <;> assumption
theorem exists_circleIntegral_bilinear (F : Type) [NormedAddCommGroup F] [NormedSpace ℂ F]
    [CompleteSpace F] (a : ℂ) (ρ : ℝ) (hρ : 0 ≤ ρ) :
    ∃ B : C(sphere a ρ, ℂ) →L[ℂ] C(sphere a ρ, F) →L[ℂ] F, ∀ k g, B k g =
      ∫ θ in (0 : ℝ)..2 * π, (circleMap 0 ρ θ * I) •
        k ⟨circleMap a ρ θ, circleMap_mem_sphere a hρ θ⟩ •
        g ⟨circleMap a ρ θ, circleMap_mem_sphere a hρ θ⟩ := by apply _root_.YangMills.Construction.Matrices.Osgood.exists_circle_bilinear <;> assumption
theorem SeparatelyHolomorphicAnalytic.prod_complex {E : Type} [NormedAddCommGroup E]
    [NormedSpace ℂ E] (hE : SeparatelyHolomorphicAnalytic E) :
    SeparatelyHolomorphicAnalytic (ℂ × E) := by
  intro F _ _ _ f U hU hf hline
  rintro ⟨a, b⟩ hx
  obtain ⟨ρ, hρ, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.1 (hU.mem_nhds hx)
  have hsub : ∀ z ∈ closedBall a ρ, ∀ w ∈ closedBall b ρ, (z, w) ∈ U := by
    intro z hz w hw
    apply hball
    rw [← closedBall_prod_same]
    exact ⟨hz, hw⟩
  obtain ⟨G, hGc, hGe⟩ := exists_continuousOn_continuousMap_of_uncurry (S := sphere a ρ) (ball b ρ)
    (fun w ζ => f ((ζ : ℂ), w))
    (hf.comp_continuous
      ((continuous_subtype_val.comp continuous_snd).prodMk
        (continuous_subtype_val.comp continuous_fst))
      fun p => hsub _ (sphere_subset_closedBall p.2.2) _ (ball_subset_closedBall p.1.2))
  have hsep : ∀ {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℂ Y] (g : C(sphere a ρ, Y)),
      (∀ ζ : sphere a ρ, ContinuousMap.evalCLM ℂ ζ g = 0) → g = 0 := by
    intro Y _ _ g hg
    ext ζ
    simpa using hg ζ
  have hGd : ∀ w ∈ ball b ρ, ∀ v, DifferentiableAt ℂ (fun t : ℂ => G (w + t • v)) 0 := by
    intro w hw v
    have hcont : Continuous fun t : ℂ => w + t • v := by fun_prop
    have hnhds : ∀ᶠ t in 𝓝 (0 : ℂ), w + t • v ∈ ball b ρ :=
      hcont.continuousAt.eventually_mem (by simpa using isOpen_ball.mem_nhds hw)
    obtain ⟨R, hR, hRb⟩ := Metric.nhds_basis_closedBall.mem_iff.1 hnhds
    refine (analyticAt_of_separating_differentiableOn (fun t : ℂ => G (w + t • v)) 0 R hR ?_
      (fun ζ : sphere a ρ => ContinuousMap.evalCLM ℂ ζ) hsep ?_).differentiableAt
    · exact hGc.comp hcont.continuousOn fun t ht => hRb ht
    · intro ζ
      have hl : DifferentiableOn ℂ (fun t : ℂ => f ((ζ : ℂ), w + t • v)) (ball 0 R) := by
        intro t ht
        have hm : w + t • v ∈ ball b ρ := hRb (ball_subset_closedBall ht)
        have hmem : ((ζ : ℂ), w) + t • ((0 : ℂ), v) ∈ U := by
          simpa using hsub _ (sphere_subset_closedBall ζ.2) _ (ball_subset_closedBall hm)
        simpa using (differentiableAt_along_line hline hmem).differentiableWithinAt
      refine hl.congr fun t ht => ?_
      exact hGe _ (hRb (ball_subset_closedBall ht)) ζ
  have hGa : AnalyticAt ℂ G b :=
    hE C(sphere a ρ, F) G (ball b ρ) isOpen_ball hGc hGd b (mem_ball_self hρ)
  have hne : ∀ z ∈ closedBall a (ρ / 2), ∀ ζ ∈ sphere a ρ, ζ - z ≠ 0 := by
    intro z hz ζ hζ h0
    rw [sub_eq_zero] at h0
    subst h0
    rw [mem_sphere] at hζ
    rw [mem_closedBall] at hz
    linarith
  obtain ⟨K, hKc, hKe⟩ := exists_continuousOn_continuousMap_of_uncurry (S := sphere a ρ)
    (closedBall a (ρ / 2))
    (fun z ζ => ((ζ : ℂ) - z)⁻¹)
    (Continuous.inv₀ ((continuous_subtype_val.comp continuous_snd).sub
      (continuous_subtype_val.comp continuous_fst)) fun p => hne _ p.1.2 _ p.2.2)
  have hKa : AnalyticAt ℂ K a := by
    refine analyticAt_of_separating_differentiableOn K a (ρ / 2) (half_pos hρ) hKc
      (fun ζ : sphere a ρ => ContinuousMap.evalCLM ℂ ζ) hsep ?_
    intro ζ
    have hinv : DifferentiableOn ℂ (fun z : ℂ => ((ζ : ℂ) - z)⁻¹) (ball a (ρ / 2)) := by
      intro z hz
      exact (DifferentiableAt.inv (by fun_prop)
        (hne z (ball_subset_closedBall hz) ζ ζ.2)).differentiableWithinAt
    refine hinv.congr fun z hz => ?_
    exact hKe z (ball_subset_closedBall hz) ζ
  obtain ⟨B, hB⟩ := exists_circleIntegral_bilinear F a ρ hρ.le
  have han : AnalyticAt ℂ (((2 * π * I : ℂ)⁻¹) • fun p : ℂ × E => B (K p.1) (G p.2)) (a, b) := by
    have h1 : AnalyticAt ℂ (fun p : ℂ × E => K p.1) (a, b) :=
      AnalyticAt.comp (g := K) (f := fun p : ℂ × E => p.1) hKa analyticAt_fst
    have h2 : AnalyticAt ℂ (fun p : ℂ × E => G p.2) (a, b) :=
      AnalyticAt.comp (g := G) (f := fun p : ℂ × E => p.2) hGa analyticAt_snd
    have h3 := AnalyticAt.comp (g := fun q : C(sphere a ρ, ℂ) × C(sphere a ρ, F) => B q.1 q.2)
      (f := fun p : ℂ × E => (K p.1, G p.2)) (B.analyticAt_bilinear _) (h1.prod h2)
    exact h3.const_smul
  refine han.congr ?_
  have hnb : ball a (ρ / 2) ×ˢ ball b ρ ∈ 𝓝 (a, b) :=
    prod_mem_nhds (ball_mem_nhds a (half_pos hρ)) (ball_mem_nhds b hρ)
  filter_upwards [hnb]
  rintro ⟨z, w⟩ ⟨hz, hw⟩
  have hzc : z ∈ closedBall a (ρ / 2) := ball_subset_closedBall hz
  have hwc : w ∈ closedBall b ρ := ball_subset_closedBall hw
  have hdc : DiffContOnCl ℂ (fun s : ℂ => f (s, w)) (ball a ρ) := by
    refine ⟨?_, ?_⟩
    · intro s hs
      have hmem : ((0 : ℂ), w) + s • ((1 : ℂ), (0 : E)) ∈ U := by
        simpa using hsub s (ball_subset_closedBall hs) w hwc
      simpa using (differentiableAt_along_line hline hmem).differentiableWithinAt
    · rw [closure_ball a hρ.ne']
      exact hf.comp (continuous_id.prodMk continuous_const).continuousOn
        fun s hs => hsub s hs w hwc
  have hzρ : z ∈ ball a ρ := ball_subset_ball (by linarith) hz
  have hcauchy : (2 * π * I : ℂ)⁻¹ • ∮ ζ in C(a, ρ), (ζ - z)⁻¹ • f (ζ, w) = f (z, w) :=
    hdc.two_pi_i_inv_smul_circleIntegral_sub_inv_smul hzρ
  rw [← hcauchy, Pi.smul_apply, hB, circleIntegral]
  congr 1
  refine intervalIntegral.integral_congr fun θ _ => ?_
  simp only [deriv_circleMap]
  rw [hKe z hzc, hGe w hw]
theorem SeparatelyHolomorphicAnalytic.of_continuousLinearEquiv {E E' : Type}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup E'] [NormedSpace ℂ E']
    (hE : SeparatelyHolomorphicAnalytic E) (e : E ≃L[ℂ] E') :
    SeparatelyHolomorphicAnalytic E' := by
  intro F _ _ _ f U hU hf hline x hx
  have hV : IsOpen (e ⁻¹' U) := hU.preimage e.continuous
  have h1 : AnalyticAt ℂ (fun y => f (e y)) (e.symm x) := by
    refine hE F (fun y => f (e y)) (e ⁻¹' U) hV
      (hf.comp e.continuous.continuousOn fun y hy => hy) ?_ (e.symm x) (by simpa using hx)
    intro y hy v
    simpa using hline (e y) hy (e v)
  have h2 : AnalyticAt ℂ (fun y : E' => e.symm y) x := (e.symm : E' →L[ℂ] E).analyticAt x
  have h3 := AnalyticAt.comp (g := fun y => f (e y)) (f := fun y : E' => e.symm y) h1 h2
  have h4 : (fun y => f (e y)) ∘ (fun y : E' => e.symm y) = f := by
    funext y
    simp
  rwa [h4] at h3
theorem separatelyHolomorphicAnalytic_fin (n : ℕ) :
    SeparatelyHolomorphicAnalytic (Fin n → ℂ) := by
  induction n with
  | zero =>
    intro F _ _ _ f U _ _ _ x _
    have : f = fun _ => f x := funext fun y => congrArg f (Subsingleton.elim y x)
    rw [this]
    exact analyticAt_const
  | succ n ih =>
    have e : (ℂ × (Fin n → ℂ)) ≃L[ℂ] (Fin (n + 1) → ℂ) :=
      ContinuousLinearEquiv.ofFinrankEq (by simp [add_comm])
    exact ih.prod_complex.of_continuousLinearEquiv e
theorem boundedLineHolomorphicIsAnalytic_holds :
    YangMills.Construction.ComplexAnalysis.BoundedLineHolomorphicIsAnalytic := by
  intro E _ _ _ F _ _ _ f U M hU hM hline
  have e : (Fin (Module.finrank ℂ E) → ℂ) ≃L[ℂ] E := ContinuousLinearEquiv.ofFinrankEq (by simp)
  refine ((separatelyHolomorphicAnalytic_fin _).of_continuousLinearEquiv e) F f U hU ?_ hline
  intro x hx
  refine ContinuousAt.continuousWithinAt ?_
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hU x hx
  refine continuousAt_of_locally_lipschitz hr ((2 * M + 1) / r) fun y hy => ?_
  by_cases hyx : y = x
  · subst hyx
    simp
  have hs : 0 < ‖y - x‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hyx)
  set s : ℝ := ‖y - x‖ with hsdef
  have hsne : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  set v : E := (s : ℂ)⁻¹ • (y - x) with hv
  have hv1 : ‖v‖ = 1 := by
    rw [hv, norm_smul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hs.le]
    exact inv_mul_cancel₀ hs.ne'
  have hmem : ∀ t ∈ Metric.ball (0 : ℂ) r, x + t • v ∈ U := by
    intro t ht
    refine hball ?_
    have : ‖t‖ < r := by simpa using ht
    simp only [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, hv1, mul_one]
    exact this
  have hg : DifferentiableOn ℂ (fun t : ℂ => f (x + t • v)) (Metric.ball 0 r) := fun t ht =>
    (differentiableAt_along_line hline (hmem t ht)).differentiableWithinAt
  have hmaps : Set.MapsTo (fun t : ℂ => f (x + t • v)) (Metric.ball 0 r)
      (Metric.ball ((fun t : ℂ => f (x + t • v)) 0) (2 * M + 1)) := by
    intro t ht
    simp only [Metric.mem_ball, dist_eq_norm, zero_smul, add_zero]
    have h1 := hM _ (hmem t ht)
    have h2 := hM x hx
    have := norm_sub_le (f (x + t • v)) (f x)
    linarith
  have hz : (s : ℂ) ∈ Metric.ball (0 : ℂ) r := by
    simp only [Metric.mem_ball, dist_zero_right, Complex.norm_real, Real.norm_of_nonneg hs.le]
    have : dist y x = s := by rw [dist_eq_norm]
    rw [← this]
    exact hy
  have hsch := Complex.dist_le_div_mul_dist_of_mapsTo_ball hg
    (hmaps.mono_right Metric.ball_subset_closedBall) hz
  have hy' : x + (s : ℂ) • v = y := by
    rw [hv, smul_smul, mul_inv_cancel₀ hsne, one_smul]
    abel
  simp only [zero_smul, add_zero, hy'] at hsch
  have hd0 : dist (s : ℂ) 0 = dist y x := by
    rw [dist_eq_norm y x, dist_zero_right, Complex.norm_real, Real.norm_of_nonneg hs.le]
  rwa [hd0] at hsch
end YangMills.Construction.ComplexAnalysis.LineHolomorphy
