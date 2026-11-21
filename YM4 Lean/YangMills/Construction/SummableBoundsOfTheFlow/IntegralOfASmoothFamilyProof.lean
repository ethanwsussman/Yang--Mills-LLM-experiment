import YangMills.Construction.SummableBoundsOfTheFlow.IntegralOfASmoothFamily
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Topology Interval
open Set MeasureTheory
set_option linter.unusedSectionVars false
namespace YangMills.Construction
namespace IteratedDerivative
namespace ParametricIntegral
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
theorem eventually_contDiffAt_slice {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] (n : ℕ)
    (A : ℝ × E → F) (x₀ : E)
    (hA : ∀ t ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ (n : WithTop ℕ∞) A (t, x₀)) :
    ∀ᶠ x in 𝓝 x₀, ∀ t ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ (n : WithTop ℕ∞) A (t, x) := by
  apply isCompact_Icc.eventually_forall_of_forall_eventually
  intro t ht
  have h := (hA t ht).eventually (by simp)
  have hswap : Filter.Tendsto (fun y : E × ℝ => (y.2, y.1)) (𝓝 (x₀, t)) (𝓝 (t, x₀)) :=
    continuous_swap.tendsto (x₀, t)
  exact hswap.eventually h
theorem continuousAt_fst_slice {F : Type} [TopologicalSpace F] {A : ℝ × E → F} {t : ℝ} {x : E}
    (h : ContinuousAt A (t, x)) : ContinuousAt (fun t' => A (t', x)) t :=
  ContinuousAt.comp (g := A) (f := fun t' : ℝ => (t', x)) h (by fun_prop)
theorem continuousAt_snd_slice {F : Type} [TopologicalSpace F] {A : ℝ × E → F} {t : ℝ} {x : E}
    (h : ContinuousAt A (t, x)) : ContinuousAt (fun x' => A (t, x')) x :=
  ContinuousAt.comp (g := A) (f := fun x' : E => (t, x')) h (by fun_prop)
theorem continuousOn_fst_slice {F : Type} [TopologicalSpace F] {A : ℝ × E → F} {x : E}
    (h : ∀ t ∈ Icc (0 : ℝ) 1, ContinuousAt A (t, x)) :
    ContinuousOn (fun t => A (t, x)) (Icc 0 1) :=
  fun t ht => (continuousAt_fst_slice (h t ht)).continuousWithinAt
theorem mem_Icc_of_mem_uIoc {t : ℝ} (h : t ∈ Ι (0 : ℝ) 1) : t ∈ Icc (0 : ℝ) 1 := by
  rw [uIoc_of_le zero_le_one] at h
  exact Ioc_subset_Icc_self h
theorem exists_bound_eventually {F : Type} [NormedAddCommGroup F] (A : ℝ × E → F) (x₀ : E)
    (h : ∀ t ∈ Icc (0 : ℝ) 1, ContinuousAt A (t, x₀)) :
    ∃ M : ℝ, ∀ᶠ x in 𝓝 x₀, ∀ t ∈ Icc (0 : ℝ) 1, ‖A (t, x)‖ ≤ M := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (continuousOn_fst_slice h)
  refine ⟨C + 1, ?_⟩
  apply isCompact_Icc.eventually_forall_of_forall_eventually
  intro t ht
  have hn : ContinuousAt (fun y => ‖A y‖) (t, x₀) := (h t ht).norm
  have hlt := hn.eventually (Iio_mem_nhds (show ‖A (t, x₀)‖ < C + 1 by linarith [hC t ht]))
  have hswap : Filter.Tendsto (fun y : E × ℝ => (y.2, y.1)) (𝓝 (x₀, t)) (𝓝 (t, x₀)) :=
    continuous_swap.tendsto (x₀, t)
  filter_upwards [hswap.eventually hlt] with y hy
  exact le_of_lt hy
variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
theorem continuousAt_integral (A : ℝ × E → F) (x₀ : E)
    (hA : ∀ t ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ ((0 : ℕ) : WithTop ℕ∞) A (t, x₀)) :
    ContinuousAt (fun x => ∫ t in (0 : ℝ)..1, A (t, x)) x₀ := by
  obtain ⟨M, hM⟩ := exists_bound_eventually A x₀ fun t ht => (hA t ht).continuousAt
  refine intervalIntegral.continuousAt_of_dominated_interval (F := fun x t => A (t, x))
    (bound := fun _ => M) ?_ ?_ ?_ ?_
  · filter_upwards [eventually_contDiffAt_slice 0 A x₀ hA] with x hx
    exact ((continuousOn_fst_slice fun t ht => (hx t ht).continuousAt).mono
      (fun s hs => mem_Icc_of_mem_uIoc hs)).aestronglyMeasurable measurableSet_uIoc
  · filter_upwards [hM] with x hx
    exact Filter.Eventually.of_forall fun s hs => hx s (mem_Icc_of_mem_uIoc hs)
  · exact intervalIntegrable_const
  · exact Filter.Eventually.of_forall fun s hs =>
      continuousAt_snd_slice (hA s (mem_Icc_of_mem_uIoc hs)).continuousAt
def partialSnd (A : ℝ × E → F) (y : ℝ × E) : E →L[ℝ] F :=
  (fderiv ℝ A y).comp (ContinuousLinearMap.inr ℝ ℝ E)
theorem contDiffAt_partialSnd (A : ℝ × E → F) (y : ℝ × E) (n : ℕ)
    (h : ContDiffAt ℝ ((n + 1 : ℕ) : WithTop ℕ∞) A y) :
    ContDiffAt ℝ (n : WithTop ℕ∞) (partialSnd A) y :=
  (h.fderiv_right (m := n) (by norm_cast)).clm_comp contDiffAt_const
theorem hasFDerivAt_snd_slice {A : ℝ × E → F} {t : ℝ} {x : E}
    (h : ContDiffAt ℝ ((1 : ℕ) : WithTop ℕ∞) A (t, x)) :
    HasFDerivAt (fun x' => A (t, x')) (partialSnd A (t, x)) x :=
  ((h.differentiableAt (by simp)).hasFDerivAt).comp x (hasFDerivAt_prodMk_right t x)
theorem hasFDerivAt_parametric_integral (A : ℝ × E → F) (x₀ : E)
    (hA : ∀ t ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ ((1 : ℕ) : WithTop ℕ∞) A (t, x₀)) :
    HasFDerivAt (fun x => ∫ t in (0 : ℝ)..1, A (t, x))
      (∫ t in (0 : ℝ)..1, partialSnd A (t, x₀)) x₀ := by
  have hA' : ∀ t ∈ Icc (0 : ℝ) 1, ContinuousAt (partialSnd A) (t, x₀) := fun t ht =>
    (contDiffAt_partialSnd A (t, x₀) 0 (by simpa using hA t ht)).continuousAt
  obtain ⟨M, hM⟩ := exists_bound_eventually (partialSnd A) x₀ hA'
  have hev := eventually_contDiffAt_slice 1 A x₀ hA
  refine intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le (F := fun x t => A (t, x))
    (F' := fun x t => partialSnd A (t, x)) (bound := fun _ => M)
    (s := {x | (∀ t ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ ((1 : ℕ) : WithTop ℕ∞) A (t, x)) ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ‖partialSnd A (t, x)‖ ≤ M}) (hev.and hM) ?_ ?_ ?_ ?_ ?_ ?_
  · filter_upwards [hev] with x hx
    exact ((continuousOn_fst_slice fun t ht => (hx t ht).continuousAt).mono
      (fun s hs => mem_Icc_of_mem_uIoc hs)).aestronglyMeasurable measurableSet_uIoc
  · exact (continuousOn_fst_slice fun t ht => (hA t ht).continuousAt).intervalIntegrable_of_Icc
      zero_le_one
  · exact ((continuousOn_fst_slice hA').mono (fun s hs => mem_Icc_of_mem_uIoc hs)).aestronglyMeasurable
      measurableSet_uIoc
  · exact Filter.Eventually.of_forall fun s hs x hx => hx.2 s (mem_Icc_of_mem_uIoc hs)
  · exact intervalIntegrable_const
  · exact Filter.Eventually.of_forall fun s hs x hx =>
      hasFDerivAt_snd_slice (hx.1 s (mem_Icc_of_mem_uIoc hs))
theorem contDiffAt_parametric_integral : ∀ (n : ℕ) {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F] (A : ℝ × E → F) (x₀ : E),
    (∀ t ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ (n : WithTop ℕ∞) A (t, x₀)) →
    ContDiffAt ℝ (n : WithTop ℕ∞) (fun x => ∫ t in (0 : ℝ)..1, A (t, x)) x₀
  | 0, F, _, _, _, A, x₀, hA => by
    have hev := eventually_contDiffAt_slice 0 A x₀ hA
    have : ContDiffAt ℝ (0 : WithTop ℕ∞) (fun x => ∫ t in (0 : ℝ)..1, A (t, x)) x₀ :=
      contDiffAt_zero.2 ⟨_, hev, fun x hx => (continuousAt_integral A x hx).continuousWithinAt⟩
    simpa using this
  | n + 1, F, _, _, _, A, x₀, hA => by
    have hev := eventually_contDiffAt_slice (n + 1) A x₀ hA
    have hsucc : ContDiffAt ℝ ((n : WithTop ℕ∞) + 1) (fun x => ∫ t in (0 : ℝ)..1, A (t, x)) x₀ := by
      rw [contDiffAt_succ_iff_hasFDerivAt]
      refine ⟨fun x => ∫ t in (0 : ℝ)..1, partialSnd A (t, x), ⟨_, hev, fun x hx =>
        hasFDerivAt_parametric_integral A x fun t ht => (hx t ht).of_le (by norm_cast; omega)⟩,
        contDiffAt_parametric_integral n (partialSnd A) x₀ fun t ht =>
          contDiffAt_partialSnd A (t, x₀) n (hA t ht)⟩
    exact_mod_cast hsucc
theorem derivAlong_integral (l : List E) : ∀ (A : ℝ × E → ℝ) (x₀ : E) (R : DerivAlongRules E ℝ),
    (∀ t ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ (l.length : WithTop ℕ∞) A (t, x₀)) →
    derivAlong (fun x => ∫ t in (0 : ℝ)..1, A (t, x)) l x₀ =
      ∫ t in (0 : ℝ)..1, derivAlong (fun x => A (t, x)) l x₀ := by
  induction l using List.reverseRecOn with
  | nil => intro A x₀ _ _; rfl
  | append_singleton l u ih =>
    intro A x₀ R hA
    have hlen : ((l ++ [u]).length : ℕ) = l.length + 1 := by simp
    rw [hlen] at hA
    have hA1 : ∀ t ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ ((1 : ℕ) : WithTop ℕ∞) A (t, x₀) := fun t ht =>
      (hA t ht).of_le (by norm_cast; omega)
    have hB : ∀ t ∈ Icc (0 : ℝ) 1,
        ContDiffAt ℝ (l.length : WithTop ℕ∞) (fun y => partialSnd A y u) (t, x₀) := fun t ht =>
      (contDiffAt_partialSnd A (t, x₀) l.length (hA t ht)).clm_apply contDiffAt_const
    have e1 : (fun x => fderiv ℝ (fun x' => ∫ t in (0 : ℝ)..1, A (t, x')) x u) =ᶠ[𝓝 x₀]
        fun x => ∫ t in (0 : ℝ)..1, partialSnd A (t, x) u := by
      filter_upwards [eventually_contDiffAt_slice 1 A x₀ hA1] with x hx
      rw [(hasFDerivAt_parametric_integral A x hx).fderiv, ContinuousLinearMap.intervalIntegral_apply]
      exact (continuousOn_fst_slice fun t ht =>
        (contDiffAt_partialSnd A (t, x) 0 (by simpa using hx t ht)).continuousAt).intervalIntegrable_of_Icc
          zero_le_one
    rw [R.append]
    change derivAlong (fun x => fderiv ℝ (fun x' => ∫ t in (0 : ℝ)..1, A (t, x')) x u) l x₀ = _
    rw [(R.congr _ _ x₀ l e1).self_of_nhds, ih (fun y => partialSnd A y u) x₀ R hB]
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [uIcc_of_le zero_le_one] at ht
    rw [R.append]
    have e2 : (fun x => partialSnd A (t, x) u) =ᶠ[𝓝 x₀] derivAlong (fun x => A (t, x)) [u] := by
      have ht1 := ((hA1 t ht).eventually (by simp))
      have hc : Filter.Tendsto (fun x : E => (t, x)) (𝓝 x₀) (𝓝 (t, x₀)) :=
        (by fun_prop : Continuous fun x : E => (t, x)).tendsto x₀
      filter_upwards [hc.eventually ht1] with x hx
      simp only [derivAlong]
      rw [(hasFDerivAt_snd_slice hx).fderiv]
    exact (R.congr _ _ x₀ l e2).self_of_nhds
end ParametricIntegral
open ParametricIntegral in
theorem intervalIntegralSmoothFamily_holds (h : DerivAlongRulesHold) :
    IntervalIntegralSmoothFamily := by
  intro Q _ _ A p₀ n hs
  refine ⟨contDiffAt_parametric_integral n A p₀ hs, fun l hl =>
    derivAlong_integral l A p₀ (h.1 Q ℝ) fun v hv => (hs v hv).of_le (by exact_mod_cast hl)⟩
end IteratedDerivative
end YangMills.Construction
end
