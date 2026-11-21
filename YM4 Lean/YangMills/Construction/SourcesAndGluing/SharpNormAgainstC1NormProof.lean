import YangMills.Construction.ReflectionPositivity.ApproximationWithALimitOnEveryTupleIsBoundedProof
import YangMills.Construction.SourcesAndGluing.SharpNormAgainstC1Norm
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.SourcesAndGluing.SharpNormBound
open TestFunctions
variable {𝕜 : Type*} [RCLike 𝕜]
theorem sum_abs_le_two_mul_euclidNormVec (w : Fin 4 → ℝ) :
    ∑ i, |w i| ≤ 2 * TorusMetric.euclidNormVec w := by apply _root_.YangMills.Construction.ReflectionPositivity.ApproximatingSequences.BoundedOfLimits.sum_abs_le_two_mul_euclidNormVec <;> assumption
theorem partialDerivR4_eq_fderiv_single {g : (Fin 4 → ℝ) → 𝕜} (hg : IsC1R4 g) (i : Fin 4)
    (p : Fin 4 → ℝ) : partialDerivR4 i g p = fderiv ℝ g p (Pi.single i 1) := by
  have hdp : DifferentiableAt ℝ g p := (ContDiff.differentiable hg (by norm_num)) p
  have hray : HasDerivAt (fun t : ℝ => p + t • (Pi.single i (1 : ℝ) : Fin 4 → ℝ))
      (Pi.single i (1 : ℝ)) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const
      (Pi.single i (1 : ℝ) : Fin 4 → ℝ)).const_add p
  have hdp' : HasFDerivAt g (fderiv ℝ g p) (p + (0 : ℝ) • (Pi.single i (1 : ℝ) : Fin 4 → ℝ)) := by
    simpa using hdp.hasFDerivAt
  exact (hdp'.comp_hasDerivAt (0 : ℝ) hray).deriv
theorem norm_fderiv_apply_le_of_partials {g : (Fin 4 → ℝ) → 𝕜} (hg : IsC1R4 g) {K : ℝ}
    (hK : ∀ (i : Fin 4) p, ‖partialDerivR4 i g p‖ ≤ K) (q w : Fin 4 → ℝ) :
    ‖fderiv ℝ g q w‖ ≤ 2 * K * TorusMetric.euclidNormVec w := by
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK 0 q)
  have hw : w = ∑ i, w i • (Pi.single i (1 : ℝ) : Fin 4 → ℝ) := by
    funext j
    simp [Finset.sum_apply, Pi.single_apply]
  calc ‖fderiv ℝ g q w‖
      = ‖∑ i, w i • fderiv ℝ g q (Pi.single i (1 : ℝ))‖ := by
        conv_lhs => rw [hw, map_sum]
        simp only [map_smul]
    _ ≤ ∑ i, ‖w i • fderiv ℝ g q (Pi.single i (1 : ℝ))‖ := norm_sum_le _ _
    _ ≤ ∑ i, |w i| * K := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [norm_smul, Real.norm_eq_abs, ← partialDerivR4_eq_fderiv_single hg]
        exact mul_le_mul_of_nonneg_left (hK i q) (abs_nonneg _)
    _ = (∑ i, |w i|) * K := (Finset.sum_mul _ _ _).symm
    _ ≤ (2 * TorusMetric.euclidNormVec w) * K :=
        mul_le_mul_of_nonneg_right (sum_abs_le_two_mul_euclidNormVec w) hK0
    _ = 2 * K * TorusMetric.euclidNormVec w := by ring
theorem norm_sub_le_of_partials_le {g : (Fin 4 → ℝ) → 𝕜} (hg : IsC1R4 g) {K : ℝ}
    (hK : ∀ (i : Fin 4) p, ‖partialDerivR4 i g p‖ ≤ K) (p q : Fin 4 → ℝ) :
    ‖g p - g q‖ ≤ 2 * K * euclidDistR4 p q := by
  have hdiff : Differentiable ℝ g := ContDiff.differentiable hg (by norm_num)
  have hseg : ∀ t : ℝ, HasDerivAt (fun t : ℝ => q + t • (p - q)) (p - q) t := fun t => by
    simpa using ((hasDerivAt_id t).smul_const (p - q)).const_add q
  have hcomp : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt (fun t : ℝ => g (q + t • (p - q)))
        (fderiv ℝ g (q + t • (p - q)) (p - q)) (Set.Icc (0 : ℝ) 1) t := fun t _ =>
    ((hdiff _).hasFDerivAt.comp_hasDerivAt t (hseg t)).hasDerivWithinAt
  have h := norm_image_sub_le_of_norm_deriv_le_segment_01' hcomp
    (fun t _ => norm_fderiv_apply_le_of_partials hg hK (q + t • (p - q)) (p - q))
  simpa [euclidDistR4] using h
theorem sharp_le_of_uniform_and_difference_bound {X : Type*} {δ : X → X → ℝ} {f : X → 𝕜}
    {c N : ℝ} (hc : 0 ≤ c) (hN : 1 ≤ N) (hunif : uniformNorm f ≤ c)
    (hf : ∀ p q, ‖f p - f q‖ ≤ 2 * c * δ p q) :
    IsLipschitzFor δ f ∧ bestLipschitzConstant δ f ≤ 2 * c ∧
      max (uniformNorm f) (40 * N * bestLipschitzConstant δ f) ≤ 80 * N * c := by
  have hlip : bestLipschitzConstant δ f ≤ 2 * c :=
    csInf_le ⟨0, fun _ h => h.1⟩ ⟨by positivity, hf⟩
  refine ⟨⟨2 * c, by positivity, hf⟩, hlip, max_le ?_ ?_⟩
  · nlinarith
  · nlinarith
theorem norm_apply_le_uniformNorm {X E : Type*} [Norm E] {f : X → E} (hf : IsBoundedFun f)
    (p : X) : ‖f p‖ ≤ uniformNorm f := by
  obtain ⟨C, hC⟩ := hf
  exact le_ciSup (f := fun p => ‖f p‖) ⟨C, by rintro _ ⟨q, rfl⟩; exact hC q⟩ p
theorem uniformNorm_nonneg_of_rclike {X : Type*} (f : X → 𝕜) : 0 ≤ uniformNorm f :=
  Real.iSup_nonneg fun _ => norm_nonneg _
theorem le_iSup_fin_four (a : Fin 4 → ℝ) (i : Fin 4) : a i ≤ ⨆ j, a j :=
  le_ciSup (Set.finite_range a).bddAbove i
theorem bound_on_R4 (D : GluingSetup) {f : (Fin 4 → ℝ) → 𝕜} (hf : IsC1R4 f)
    (hfin : HasFiniteC1NormR4 f) :
    IsLipschitzFor euclidDistR4 f ∧ lipConstR4 f ≤ 2 * c1NormR4 f ∧
      D.sharpNormR4 f ≤ sharpConst D.M * c1NormR4 f := by
  have hunif : uniformNorm f ≤ c1NormR4 f := le_max_left _ _
  have hpart : ∀ (i : Fin 4) p, ‖partialDerivR4 i f p‖ ≤ c1NormR4 f := fun i p =>
    ((norm_apply_le_uniformNorm (hfin.2 i) p).trans
      (le_iSup_fin_four (fun j => uniformNorm (partialDerivR4 j f)) i)).trans (le_max_right _ _)
  exact sharp_le_of_uniform_and_difference_bound ((uniformNorm_nonneg_of_rclike f).trans hunif)
    D.one_le_M hunif (norm_sub_le_of_partials_le hf hpart)
theorem bound_on_torus (D : GluingSetup)
    (hmin : TorusLifts.TorusDistEqMinOverLifts (PeriodicLattice.torusSide D.L D.m))
    {f : D.Torus → 𝕜} (hf : D.IsC1 f) (hfin : D.HasFiniteC1NormTorus f) :
    IsLipschitzFor euclidDistTorus f ∧ lipConstTorus f ≤ 2 * D.c1Norm f ∧
      D.sharpNormTorus f ≤ sharpConst D.M * D.c1Norm f := by
  have hunif : uniformNorm f ≤ D.c1Norm f := le_max_left _ _
  have hpart : ∀ (i : Fin 4) p,
      ‖partialDerivR4 i (f ∘ D.proj) p‖ ≤ D.c1Norm f := fun i p => by
    rw [← congrFun (D.partialDeriv_comp_proj i f) p]
    exact ((norm_apply_le_uniformNorm (hfin.2 i) _).trans
      (le_iSup_fin_four (fun j => uniformNorm (D.partialDeriv j f)) i)).trans (le_max_right _ _)
  refine sharp_le_of_uniform_and_difference_bound ((uniformNorm_nonneg_of_rclike f).trans hunif)
    D.one_le_M hunif ?_
  intro s t
  obtain ⟨p, rfl⟩ := D.proj_surjective s
  obtain ⟨q, rfl⟩ := D.proj_surjective t
  obtain ⟨q', hq', hdist⟩ := (hmin _ _ p q rfl rfl).2.2.2
  have hq : f (D.proj q) = (f ∘ D.proj) q' := by
    rw [Function.comp_apply]
    exact congrArg f hq'.symm
  have h := norm_sub_le_of_partials_le hf hpart p q'
  rw [hq]
  calc ‖f (D.proj p) - (f ∘ D.proj) q'‖
      = ‖(f ∘ D.proj) p - (f ∘ D.proj) q'‖ := rfl
    _ ≤ 2 * D.c1Norm f * euclidDistR4 p q' := h
    _ = 2 * D.c1Norm f * euclidDistTorus (D.proj p) (D.proj q) := by
      rw [euclidDistR4, hdist]
      rfl
theorem statement_holds (hlifts : TorusLifts.LiftsAndDescendedMaps.Statement) : Statement := by
  intro D 𝕜 _
  exact ⟨fun f hf hfin => bound_on_torus D (hlifts D.toStandingParameters).1 hf hfin,
    fun f hf hfin => bound_on_R4 D hf hfin⟩
end YangMills.Construction.SourcesAndGluing.SharpNormBound
end
