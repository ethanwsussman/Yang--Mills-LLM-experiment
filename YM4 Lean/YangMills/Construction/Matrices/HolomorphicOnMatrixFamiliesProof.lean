import YangMills.Construction.Matrices.HolomorphicOnMatrixFamilies
import Mathlib
set_option autoImplicit false
open Metric Set Complex MeasureTheory
open scoped Matrix.Norms.L2Operator Topology Real NNReal
noncomputable section
namespace YangMills.Construction.Matrices.Osgood
theorem analyticAt_of_separating_family {X Y ι : Type}
    [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℂ Y] [CompleteSpace Y]
    (h : ℂ → X) (c : ℂ) (R : ℝ) (hR : 0 < R)
    (hc : ContinuousOn h (closedBall c R))
    (L : ι → X →L[ℂ] Y) (sep : ∀ x, (∀ i, L i x = 0) → x = 0)
    (hd : ∀ i, DifferentiableOn ℂ (fun s => L i (h s)) (ball c R)) :
    AnalyticAt ℂ h c := by
  lift R to ℝ≥0 using hR.le
  have hR' : 0 < R := by exact_mod_cast hR
  have hsph : ContinuousOn h (sphere c R) := hc.mono sphere_subset_closedBall
  have hint : CircleIntegrable h c R := hsph.circleIntegrable R.2
  have han := (hasFPowerSeriesOn_cauchy_integral hint hR').analyticAt
  refine han.congr ?_
  filter_upwards [ball_mem_nhds c hR] with z hz
  have hzc : ∀ ζ ∈ sphere c (R : ℝ), ζ - z ≠ 0 := by
    intro ζ hζ h0
    rw [sub_eq_zero] at h0
    subst h0
    rw [mem_sphere] at hζ
    rw [mem_ball] at hz
    linarith
  have hint2 : CircleIntegrable (fun ζ => (ζ - z)⁻¹ • h ζ) c R := by
    refine ContinuousOn.circleIntegrable R.2 ?_
    exact ((continuousOn_id.sub continuousOn_const).inv₀ hzc).smul hsph
  rw [← sub_eq_zero]
  apply sep
  intro i
  have hdc : DiffContOnCl ℂ (fun s => L i (h s)) (ball c R) :=
    ⟨hd i, by rw [closure_ball c hR.ne']; exact (L i).continuous.comp_continuousOn hc⟩
  have hcauchy := hdc.two_pi_i_inv_smul_circleIntegral_sub_inv_smul hz
  have hcomm : L i (∮ ζ in C(c, R), (ζ - z)⁻¹ • h ζ) = ∮ ζ in C(c, R), (ζ - z)⁻¹ • L i (h ζ) := by
    have hii := (circleIntegrable_iff (R : ℝ)).1 hint2
    simp only [circleIntegral]
    rw [← (L i).intervalIntegral_comp_comm hii]
    simp only [map_smul]
  rw [map_sub, map_smul, hcomm, hcauchy, sub_self]
theorem exists_continuousOn_curried {T S F : Type} [TopologicalSpace T] [TopologicalSpace S]
    [CompactSpace S] [NormedAddCommGroup F] (A : Set T) (c : T → S → F)
    (hc : Continuous fun p : A × S => c p.1 p.2) :
    ∃ G : T → C(S, F), ContinuousOn G A ∧ ∀ t ∈ A, ∀ s, G t s = c t s := by
  classical
  let g : C(A, C(S, F)) := ContinuousMap.curry ⟨fun p : A × S => c p.1 p.2, hc⟩
  refine ⟨fun t => if h : t ∈ A then g ⟨t, h⟩ else 0, ?_, ?_⟩
  · rw [continuousOn_iff_continuous_domRestrict]
    have : A.domRestrict (fun t => if h : t ∈ A then g ⟨t, h⟩ else 0) = g := by
      funext t
      simp [Set.domRestrict]
    rw [this]
    exact g.continuous
  · intro t ht s
    simp [ht, g]
def OsgoodCondition (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] : Prop :=
  ∀ (F : Type) [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F] (f : E → F) (U : Set E),
    IsOpen U → ContinuousOn f U →
    (∀ x ∈ U, ∀ v, DifferentiableAt ℂ (fun t : ℂ => f (x + t • v)) 0) → AnalyticOnNhd ℂ f U
theorem differentiableAt_along_line {E F : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] {f : E → F} {U : Set E}
    (hd : ∀ x ∈ U, ∀ v, DifferentiableAt ℂ (fun t : ℂ => f (x + t • v)) 0)
    {x v : E} {t : ℂ} (ht : x + t • v ∈ U) :
    DifferentiableAt ℂ (fun s : ℂ => f (x + s • v)) t := by
  have h2 : DifferentiableAt ℂ (fun s : ℂ => s - t) t := by fun_prop
  have h3 : DifferentiableAt ℂ (fun t' : ℂ => f (x + t • v + t' • v)) ((fun s : ℂ => s - t) t) := by
    simpa using hd _ ht v
  refine (DifferentiableAt.comp (g := fun t' : ℂ => f (x + t • v + t' • v))
    (f := fun s : ℂ => s - t) t h3 h2).congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
  simp only [Function.comp]
  congr 1
  rw [sub_smul]
  abel
theorem exists_circle_bilinear (F : Type) [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    (a : ℂ) (ρ : ℝ) (hρ : 0 ≤ ρ) :
    ∃ B : C(sphere a ρ, ℂ) →L[ℂ] C(sphere a ρ, F) →L[ℂ] F, ∀ k g, B k g =
      ∫ θ in (0 : ℝ)..2 * π, (circleMap 0 ρ θ * I) •
        k ⟨circleMap a ρ θ, circleMap_mem_sphere a hρ θ⟩ •
        g ⟨circleMap a ρ θ, circleMap_mem_sphere a hρ θ⟩ := by
  let pt : ℝ → sphere a ρ := fun θ => ⟨circleMap a ρ θ, circleMap_mem_sphere a hρ θ⟩
  have hpt : Continuous pt := (continuous_circleMap a ρ).subtype_mk _
  have ci : ∀ (k : C(sphere a ρ, ℂ)) (g : C(sphere a ρ, F)),
      IntervalIntegrable (fun θ => (circleMap 0 ρ θ * I) • k (pt θ) • g (pt θ)) volume 0 (2 * π) := by
    intro k g
    refine Continuous.intervalIntegrable ?_ _ _
    exact ((continuous_circleMap 0 ρ).mul continuous_const).smul
      ((k.continuous.comp hpt).smul (g.continuous.comp hpt))
  let B₀ : C(sphere a ρ, ℂ) →ₗ[ℂ] C(sphere a ρ, F) →ₗ[ℂ] F :=
    LinearMap.mk₂ ℂ (fun k g => ∫ θ in (0 : ℝ)..2 * π, (circleMap 0 ρ θ * I) • k (pt θ) • g (pt θ))
      (by
        intro k k' g
        rw [← intervalIntegral.integral_add (ci k g) (ci k' g)]
        refine intervalIntegral.integral_congr fun θ _ => ?_
        simp only [ContinuousMap.add_apply]
        module)
      (by
        intro c k g
        rw [← intervalIntegral.integral_smul]
        refine intervalIntegral.integral_congr fun θ _ => ?_
        simp only [ContinuousMap.smul_apply]
        module)
      (by
        intro k g g'
        rw [← intervalIntegral.integral_add (ci k g) (ci k g')]
        refine intervalIntegral.integral_congr fun θ _ => ?_
        simp only [ContinuousMap.add_apply]
        module)
      (by
        intro c k g
        rw [← intervalIntegral.integral_smul]
        refine intervalIntegral.integral_congr fun θ _ => ?_
        simp only [ContinuousMap.smul_apply]
        module)
  refine ⟨LinearMap.mkContinuous₂ B₀ (|ρ| * (2 * π)) ?_, fun k g => rfl⟩
  intro k g
  have hb : ∀ θ ∈ Set.uIoc (0 : ℝ) (2 * π),
      ‖(circleMap 0 ρ θ * I) • k (pt θ) • g (pt θ)‖ ≤ |ρ| * ‖k‖ * ‖g‖ := by
    intro θ _
    rw [norm_smul, norm_smul, norm_mul, norm_I, mul_one, norm_circleMap_zero, mul_assoc]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul (k.norm_coe_le_norm _) (g.norm_coe_le_norm _) (norm_nonneg _) (norm_nonneg _))
      (abs_nonneg _)
  have h := intervalIntegral.norm_integral_le_of_norm_le_const hb
  have h2 : |2 * π - 0| = 2 * π := by
    rw [sub_zero, abs_of_pos Real.two_pi_pos]
  rw [h2] at h
  calc ‖B₀ k g‖ ≤ |ρ| * ‖k‖ * ‖g‖ * (2 * π) := h
    _ = |ρ| * (2 * π) * ‖k‖ * ‖g‖ := by ring
theorem OsgoodCondition.prod {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (hE : OsgoodCondition E) : OsgoodCondition (ℂ × E) := by
  intro F _ _ _ f U hU hf hd
  rintro ⟨a, b⟩ hx
  obtain ⟨ρ, hρ, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.1 (hU.mem_nhds hx)
  have hsub : ∀ z ∈ closedBall a ρ, ∀ w ∈ closedBall b ρ, (z, w) ∈ U := by
    intro z hz w hw
    apply hball
    rw [← closedBall_prod_same]
    exact ⟨hz, hw⟩
  obtain ⟨G, hGc, hGe⟩ := exists_continuousOn_curried (S := sphere a ρ) (ball b ρ)
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
    refine (analyticAt_of_separating_family (fun t : ℂ => G (w + t • v)) 0 R hR ?_
      (fun ζ : sphere a ρ => ContinuousMap.evalCLM ℂ ζ) hsep ?_).differentiableAt
    · exact hGc.comp hcont.continuousOn fun t ht => hRb ht
    · intro ζ
      have hline : DifferentiableOn ℂ (fun t : ℂ => f ((ζ : ℂ), w + t • v)) (ball 0 R) := by
        intro t ht
        have hm : w + t • v ∈ ball b ρ := hRb (ball_subset_closedBall ht)
        have hmem : ((ζ : ℂ), w) + t • ((0 : ℂ), v) ∈ U := by
          simpa using hsub _ (sphere_subset_closedBall ζ.2) _ (ball_subset_closedBall hm)
        simpa using (differentiableAt_along_line hd hmem).differentiableWithinAt
      refine hline.congr fun t ht => ?_
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
  obtain ⟨K, hKc, hKe⟩ := exists_continuousOn_curried (S := sphere a ρ) (closedBall a (ρ / 2))
    (fun z ζ => ((ζ : ℂ) - z)⁻¹)
    (Continuous.inv₀ ((continuous_subtype_val.comp continuous_snd).sub
      (continuous_subtype_val.comp continuous_fst)) fun p => hne _ p.1.2 _ p.2.2)
  have hKa : AnalyticAt ℂ K a := by
    refine analyticAt_of_separating_family K a (ρ / 2) (half_pos hρ) hKc
      (fun ζ : sphere a ρ => ContinuousMap.evalCLM ℂ ζ) hsep ?_
    intro ζ
    have hinv : DifferentiableOn ℂ (fun z : ℂ => ((ζ : ℂ) - z)⁻¹) (ball a (ρ / 2)) := by
      intro z hz
      exact (DifferentiableAt.inv (by fun_prop)
        (hne z (ball_subset_closedBall hz) ζ ζ.2)).differentiableWithinAt
    refine hinv.congr fun z hz => ?_
    exact hKe z (ball_subset_closedBall hz) ζ
  obtain ⟨B, hB⟩ := exists_circle_bilinear F a ρ hρ.le
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
      simpa using (differentiableAt_along_line hd hmem).differentiableWithinAt
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
theorem OsgoodCondition.of_equiv {E E' : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup E'] [NormedSpace ℂ E'] (hE : OsgoodCondition E) (e : E ≃L[ℂ] E') :
    OsgoodCondition E' := by
  intro F _ _ _ f U hU hf hd x hx
  have hV : IsOpen (e ⁻¹' U) := hU.preimage e.continuous
  have h1 : AnalyticAt ℂ (fun y => f (e y)) (e.symm x) := by
    refine hE F (fun y => f (e y)) (e ⁻¹' U) hV
      (hf.comp e.continuous.continuousOn fun y hy => hy) ?_ (e.symm x) (by simpa using hx)
    intro y hy v
    simpa using hd (e y) hy (e v)
  have h2 : AnalyticAt ℂ (fun y : E' => e.symm y) x := (e.symm : E' →L[ℂ] E).analyticAt x
  have h3 := AnalyticAt.comp (g := fun y => f (e y)) (f := fun y : E' => e.symm y) h1 h2
  have h4 : (fun y => f (e y)) ∘ (fun y : E' => e.symm y) = f := by
    funext y
    simp
  rwa [h4] at h3
theorem osgoodCondition_fin (n : ℕ) : OsgoodCondition (Fin n → ℂ) := by
  induction n with
  | zero =>
    intro F _ _ _ f U _ _ _ x _
    have : f = fun _ => f x := funext fun y => congrArg f (Subsingleton.elim y x)
    rw [this]
    exact analyticAt_const
  | succ n ih =>
    have e : (ℂ × (Fin n → ℂ)) ≃L[ℂ] (Fin (n + 1) → ℂ) :=
      ContinuousLinearEquiv.ofFinrankEq (by simp [add_comm])
    exact ih.prod.of_equiv e
theorem matrixFamily_analytic : ComplexMatrix2.DifferentiableOnFamiliesAnalytic := by
  intro J _ O f hO hf
  have : CompleteSpace ComplexMatrix2 := FiniteDimensional.complete ℂ ComplexMatrix2
  have e : (Fin (Module.finrank ℂ (J → ComplexMatrix2)) → ℂ) ≃L[ℂ] (J → ComplexMatrix2) :=
    ContinuousLinearEquiv.ofFinrankEq (by simp)
  refine ((osgoodCondition_fin _).of_equiv e) ComplexMatrix2 f O hO hf.continuousOn ?_
  intro x hx v
  have h1 : DifferentiableAt ℂ f (x + (0 : ℂ) • v) := by
    simpa using (hf x hx).differentiableAt (hO.mem_nhds hx)
  have h2 : DifferentiableAt ℂ (fun t : ℂ => x + t • v) 0 := by fun_prop
  exact h1.comp (0 : ℂ) h2
end YangMills.Construction.Matrices.Osgood
