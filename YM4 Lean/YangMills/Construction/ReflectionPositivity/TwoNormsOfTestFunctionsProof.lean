import YangMills.Construction.ReflectionPositivity.ApproximationWithALimitOnEveryTupleIsBoundedProof
import YangMills.Construction.Torus.GeometryAndFreeKernelOfATestPairProof
import YangMills.Construction.ReflectionPositivity.TwoNormsOfTestFunctions
import Mathlib
set_option autoImplicit false
open Filter Topology
namespace YangMills.Construction.TestNormComparison
open SeparatedTupleFunctionals TestFunctions
open InfiniteLattice (AmbientSpace)
theorem hasDerivAt_axisLine {f : AmbientSpace → ℝ} (hf : HasContPartials f) (μ : Fin 4)
    (x : AmbientSpace) (t : ℝ) :
    HasDerivAt (fun s : ℝ => f (x + s • Pi.single μ (1 : ℝ)))
      (partialDerivR4 μ f (x + t • Pi.single μ (1 : ℝ))) t := by
  have hshift : HasDerivAt
      (fun s : ℝ => f (x + t • Pi.single μ (1 : ℝ) + s • Pi.single μ (1 : ℝ)))
      (partialDerivR4 μ f (x + t • Pi.single μ (1 : ℝ))) (t - t) := by
    rw [sub_self]
    exact ((hf μ).1 (x + t • Pi.single μ (1 : ℝ))).hasDerivAt
  refine (HasDerivAt.comp_sub_const t t hshift).congr_of_eventuallyEq
    (Eventually.of_forall fun s => ?_)
  show f _ = f _
  congr 1
  rw [sub_smul]
  abel
theorem hasCompactSupport_of_c1CompactSupp {f : AmbientSpace → ℝ} (hf : f ∈ c1CompactSupp ℝ) :
    HasCompactSupport f := hf.1.2
theorem hasCompactSupport_partialDerivR4 {f : AmbientSpace → ℝ} (hf : f ∈ c1CompactSupp ℝ)
    (μ : Fin 4) : HasCompactSupport (partialDerivR4 μ f) := by
  refine HasCompactSupport.intro (hasCompactSupport_of_c1CompactSupp hf) fun x hx => ?_
  have hvanish : f =ᶠ[𝓝 x] 0 := notMem_tsupport_iff_eventuallyEq.mp hx
  have hto : Tendsto (fun s : ℝ => x + s • (Pi.single μ (1 : ℝ) : AmbientSpace)) (𝓝 0) (𝓝 x) := by
    have hcont : Continuous fun s : ℝ => x + s • (Pi.single μ (1 : ℝ) : AmbientSpace) := by
      fun_prop
    simpa using hcont.tendsto 0
  have hloc : (fun s : ℝ => f (x + s • Pi.single μ (1 : ℝ))) =ᶠ[𝓝 0] fun _ => 0 :=
    hto.eventually hvanish
  show deriv _ 0 = 0
  rw [hloc.deriv_eq]
  simp
theorem isBoundedFun_partialDerivR4 {f : AmbientSpace → ℝ} (hf : f ∈ c1CompactSupp ℝ)
    (μ : Fin 4) : IsBoundedFun (partialDerivR4 μ f) :=
  (hf.2 μ).2.bounded_above_of_compact_support (hasCompactSupport_partialDerivR4 hf μ)
theorem norm_le_uniformNorm {g : AmbientSpace → ℝ} (hg : IsBoundedFun g) (x : AmbientSpace) :
    ‖g x‖ ≤ uniformNorm g := by apply _root_.YangMills.Construction.TestPairs.norm_le_uniformNorm <;> assumption
theorem uniformNorm_nonneg (g : AmbientSpace → ℝ) : 0 ≤ uniformNorm g := by apply _root_.YangMills.Construction.ReflectionPositivity.ApproximatingSequences.BoundedOfLimits.uniformNorm_nonneg <;> assumption
theorem c1NormR4_nonneg (f : AmbientSpace → ℝ) : 0 ≤ c1NormR4 f := by apply _root_.YangMills.Construction.ReflectionPositivity.ApproximatingSequences.BoundedOfLimits.c1NormR4_nonneg <;> assumption
theorem norm_partialDerivR4_le_c1NormR4 {f : AmbientSpace → ℝ} (hf : f ∈ c1CompactSupp ℝ)
    (μ : Fin 4) (x : AmbientSpace) : ‖partialDerivR4 μ f x‖ ≤ c1NormR4 f :=
  ((norm_le_uniformNorm (isBoundedFun_partialDerivR4 hf μ) x).trans
    (le_ciSup (f := fun ν => uniformNorm (partialDerivR4 ν f)) (Set.finite_range _).bddAbove μ)).trans
    (le_max_right _ _)
theorem norm_sub_le_of_axis_step {f : AmbientSpace → ℝ} (hf : HasContPartials f) {C : ℝ}
    (μ : Fin 4) (hC : ∀ x, ‖partialDerivR4 μ f x‖ ≤ C) (x : AmbientSpace) (t : ℝ) :
    ‖f (x + t • Pi.single μ (1 : ℝ)) - f x‖ ≤ C * |t| := by
  have hmv := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun s : ℝ => f (x + s • Pi.single μ (1 : ℝ)))
    (f' := fun s : ℝ => partialDerivR4 μ f (x + s • Pi.single μ (1 : ℝ)))
    (C := C) (s := Set.univ) (x := 0) (y := t)
    (fun s _ => (hasDerivAt_axisLine hf μ x s).hasDerivWithinAt) (fun s _ => hC _) convex_univ
    (Set.mem_univ _) (Set.mem_univ _)
  simpa using hmv
theorem sum_abs_le_two_mul_euclidNormVec (v : AmbientSpace) :
    ∑ μ, |v μ| ≤ 2 * TorusMetric.euclidNormVec v := by apply _root_.YangMills.Construction.ReflectionPositivity.ApproximatingSequences.BoundedOfLimits.sum_abs_le_two_mul_euclidNormVec <;> assumption
theorem norm_sub_le_two_mul_bound_mul_euclidDistR4 {f : AmbientSpace → ℝ} (hf : HasContPartials f)
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ μ x, ‖partialDerivR4 μ f x‖ ≤ C) (x y : AmbientSpace) :
    ‖f x - f y‖ ≤ 2 * C * euclidDistR4 x y := by
  set d : AmbientSpace := x - y with hd
  set p₁ : AmbientSpace := y + d 0 • Pi.single 0 (1 : ℝ) with hp₁
  set p₂ : AmbientSpace := p₁ + d 1 • Pi.single 1 (1 : ℝ) with hp₂
  set p₃ : AmbientSpace := p₂ + d 2 • Pi.single 2 (1 : ℝ) with hp₃
  have hx : x = p₃ + d 3 • Pi.single 3 (1 : ℝ) := by
    funext i
    fin_cases i <;> simp [hp₁, hp₂, hp₃, hd]
  have e₀ := norm_sub_le_of_axis_step hf 0 (hC 0) y (d 0)
  have e₁ := norm_sub_le_of_axis_step hf 1 (hC 1) p₁ (d 1)
  have e₂ := norm_sub_le_of_axis_step hf 2 (hC 2) p₂ (d 2)
  have e₃ := norm_sub_le_of_axis_step hf 3 (hC 3) p₃ (d 3)
  rw [← hp₁] at e₀
  rw [← hp₂] at e₁
  rw [← hp₃] at e₂
  rw [← hx] at e₃
  have htel : f x - f y = (f x - f p₃) + (f p₃ - f p₂) + (f p₂ - f p₁) + (f p₁ - f y) := by ring
  have hl1 := sum_abs_le_two_mul_euclidNormVec d
  rw [Fin.sum_univ_four] at hl1
  calc ‖f x - f y‖
      ≤ ‖f x - f p₃‖ + ‖f p₃ - f p₂‖ + ‖f p₂ - f p₁‖ + ‖f p₁ - f y‖ := by
        rw [htel]
        exact norm_add₄_le
    _ ≤ C * (|d 0| + |d 1| + |d 2| + |d 3|) := by nlinarith
    _ ≤ C * (2 * TorusMetric.euclidNormVec d) := mul_le_mul_of_nonneg_left hl1 hC0
    _ = 2 * C * euclidDistR4 x y := by
        rw [euclidDistR4]
        ring
theorem euclidDistR4_axis_step (μ : Fin 4) (x : AmbientSpace) (s : ℝ) :
    euclidDistR4 (x + s • Pi.single μ (1 : ℝ)) x = |s| := by
  have hsq : ∑ ν, ((s • (Pi.single μ (1 : ℝ) : AmbientSpace)) ν) ^ 2 = s ^ 2 := by
    simp [Pi.single_apply]
  rw [euclidDistR4, TorusMetric.euclidNormVec, add_sub_cancel_left, hsq, Real.sqrt_sq_eq_abs]
theorem norm_partialDerivR4_le_of_lipschitz {f : AmbientSpace → ℝ} (hf : HasContPartials f)
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ x y, ‖f x - f y‖ ≤ C * euclidDistR4 x y) (μ : Fin 4)
    (x : AmbientSpace) : ‖partialDerivR4 μ f x‖ ≤ C := by
  have hder := hasDerivAt_axisLine hf μ x 0
  rw [zero_smul, add_zero] at hder
  refine hder.le_of_lip' hC0 (Eventually.of_forall fun s => ?_)
  have hb := hC (x + s • Pi.single μ (1 : ℝ)) x
  rw [euclidDistR4_axis_step] at hb
  simpa using hb
theorem c1NormR4_le_sharpNormR4_and_le {M : ℝ} (hM : 1 ≤ M) {f : AmbientSpace → ℝ}
    (hf : f ∈ c1CompactSupp ℝ) :
    c1NormR4 f ≤ sharpNormR4 M f ∧ sharpNormR4 M f ≤ 80 * M * c1NormR4 f := by
  have hc0 := c1NormR4_nonneg f
  have hbound : ∀ x y, ‖f x - f y‖ ≤ (2 * c1NormR4 f) * euclidDistR4 x y :=
    norm_sub_le_two_mul_bound_mul_euclidDistR4 hf.2 hc0 (norm_partialDerivR4_le_c1NormR4 hf)
  have hmem : (2 * c1NormR4 f) ∈
      {C : ℝ | 0 ≤ C ∧ ∀ x y, ‖f x - f y‖ ≤ C * euclidDistR4 x y} := ⟨by positivity, hbound⟩
  have hlipUp : lipConstR4 f ≤ 2 * c1NormR4 f := csInf_le ⟨0, fun _ h => h.1⟩ hmem
  have hpd : ∀ μ x, ‖partialDerivR4 μ f x‖ ≤ lipConstR4 f := fun μ x =>
    le_csInf ⟨_, hmem⟩ fun _ h => norm_partialDerivR4_le_of_lipschitz hf.2 h.1 h.2 μ x
  have hlip0 : 0 ≤ lipConstR4 f := (norm_nonneg _).trans (hpd 0 0)
  have hlipSh : lipConstR4 f ≤ sharpNormR4 M f := by
    refine le_trans ?_ (le_max_right _ _)
    nlinarith
  refine ⟨max_le (le_max_left _ _) (ciSup_le fun μ => ciSup_le fun x => ?_), max_le ?_ ?_⟩
  · exact (hpd μ x).trans hlipSh
  · have hsup : uniformNorm f ≤ c1NormR4 f := le_max_left _ _
    nlinarith
  · nlinarith
theorem sub_mem_c1CompactSupp {g f : AmbientSpace → ℝ} (hg : g ∈ c1CompactSupp ℝ)
    (hf : f ∈ c1CompactSupp ℝ) : g - f ∈ c1CompactSupp ℝ := by
  refine ⟨⟨hg.1.1.sub hf.1.1, ?_⟩, fun μ => ?_⟩
  · exact (hasCompactSupport_of_c1CompactSupp hg).sub (hasCompactSupport_of_c1CompactSupp hf)
  · have hdiff : ∀ x : AmbientSpace, DifferentiableAt ℝ
        (fun t : ℝ => (g - f) (x + t • Pi.single μ (1 : ℝ))) 0 := fun x =>
      ((hg.2 μ).1 x).sub ((hf.2 μ).1 x)
    have heq : partialDerivR4 μ (g - f) = partialDerivR4 μ g - partialDerivR4 μ f := by
      funext x
      exact ((((hg.2 μ).1 x).hasDerivAt).sub (((hf.2 μ).1 x).hasDerivAt)).deriv
    exact ⟨hdiff, heq ▸ (hg.2 μ).2.sub (hf.2 μ).2⟩
theorem normsEquivalent : NormsEquivalent := by
  intro M hM
  refine ⟨fun f hf => c1NormR4_le_sharpNormR4_and_le hM hf, fun r₀ s f _ hs hf => ?_⟩
  have hcmp : ∀ᶠ r in atTop, c1NormR4 (s r - f) ≤ sharpNormR4 M (s r - f) ∧
      sharpNormR4 M (s r - f) ≤ 80 * M * c1NormR4 (s r - f) :=
    (eventually_ge_atTop r₀).mono fun r hr =>
      c1NormR4_le_sharpNormR4_and_le hM (sub_mem_c1CompactSupp (hs r hr) hf)
  constructor
  · intro h
    have hmul : Tendsto (fun r => 80 * M * c1NormR4 (s r - f)) atTop (𝓝 0) := by
      simpa using h.const_mul (80 * M)
    exact squeeze_zero'
      (hcmp.mono fun r hr => (c1NormR4_nonneg _).trans hr.1)
      (hcmp.mono fun r hr => hr.2) hmul
  · intro h
    exact squeeze_zero' (Eventually.of_forall fun r => c1NormR4_nonneg _)
      (hcmp.mono fun r hr => hr.1) h
end YangMills.Construction.TestNormComparison
