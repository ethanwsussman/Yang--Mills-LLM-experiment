import YangMills.Construction.Continuum.SharpNormOfATestFunctionAndNeighbourhoodsOfDisjointCompactSets
import YangMills.Construction.ReflectionPositivity.ApproximationWithALimitOnEveryTupleIsBoundedProof
import YangMills.Construction.ReflectionPositivity.FunctionsOfClassC1OnOneTorusProof
import Mathlib
set_option autoImplicit false
open Filter Set Topology
open YangMills.Construction.TorusMetric YangMills.Construction.TestFunctions
open YangMills.Construction.LimitSpaces YangMills.Construction.LimitSpaces.Ambient
open YangMills.Construction.AmbientPoints
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.Continuum.SeparatedFourTuples.SharpNormAndThickenings
section Numbers
variable {E : Type*} [NormedAddCommGroup E]
theorem euclidDistR4_nonneg (x y : Fin 4 → ℝ) : 0 ≤ euclidDistR4 x y := Real.sqrt_nonneg _
theorem lipConstR4_nonneg (f : (Fin 4 → ℝ) → E) : 0 ≤ lipConstR4 f :=
  Real.sInf_nonneg fun _ h => h.1
theorem lipConstR4_le {f : (Fin 4 → ℝ) → E} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ x y, ‖f x - f y‖ ≤ C * euclidDistR4 x y) : lipConstR4 f ≤ C :=
  csInf_le ⟨0, fun _ h => h.1⟩ ⟨hC, h⟩
theorem norm_sub_le_lipConstR4 {f : (Fin 4 → ℝ) → E} (hf : IsLipschitzFor euclidDistR4 f)
    (x y : Fin 4 → ℝ) : ‖f x - f y‖ ≤ lipConstR4 f * euclidDistR4 x y := by
  obtain ⟨C, hC, hCf⟩ := hf
  rcases (euclidDistR4_nonneg x y).eq_or_lt with h | h
  · have h₁ := hCf x y
    rw [← h, mul_zero] at h₁ ⊢
    exact h₁
  · rw [← div_le_iff₀ h]
    refine le_csInf ⟨C, hC, hCf⟩ ?_
    rintro D ⟨-, hD⟩
    exact (div_le_iff₀ h).2 (hD x y)
theorem norm_le_uniformNorm {X : Type*} {f : X → E} (hf : IsBoundedFun f) (x : X) :
    ‖f x‖ ≤ uniformNorm f := by
  obtain ⟨C, hC⟩ := hf
  exact le_ciSup (f := fun x => ‖f x‖) ⟨C, by rintro _ ⟨y, rfl⟩; exact hC y⟩ x
theorem uniformNorm_nonneg {X : Type*} (f : X → E) : 0 ≤ uniformNorm f :=
  Real.iSup_nonneg fun _ => norm_nonneg _
theorem uniformNorm_le {X : Type*} [Nonempty X] {f : X → E} {C : ℝ} (h : ∀ x, ‖f x‖ ≤ C) :
    uniformNorm f ≤ C :=
  ciSup_le h
theorem sharpNormR4_nonneg (M : ℝ) (f : (Fin 4 → ℝ) → E) : 0 ≤ sharpNormR4 M f :=
  (uniformNorm_nonneg f).trans (le_max_left _ _)
theorem sharpNormR4_add_le {M : ℝ} (hM : 0 ≤ M) {f g : (Fin 4 → ℝ) → E}
    (hfb : IsBoundedFun f) (hfl : IsLipschitzFor euclidDistR4 f)
    (hgb : IsBoundedFun g) (hgl : IsLipschitzFor euclidDistR4 g) :
    sharpNormR4 M (f + g) ≤ sharpNormR4 M f + sharpNormR4 M g := by
  have hsup : uniformNorm (f + g) ≤ uniformNorm f + uniformNorm g :=
    uniformNorm_le fun x => (norm_add_le _ _).trans
      (add_le_add (norm_le_uniformNorm hfb x) (norm_le_uniformNorm hgb x))
  have hlip : lipConstR4 (f + g) ≤ lipConstR4 f + lipConstR4 g := by
    refine lipConstR4_le (add_nonneg (lipConstR4_nonneg f) (lipConstR4_nonneg g)) fun x y => ?_
    have h : (f + g) x - (f + g) y = (f x - f y) + (g x - g y) := by
      simp only [Pi.add_apply]
      abel
    rw [h, add_mul]
    exact (norm_add_le _ _).trans
      (add_le_add (norm_sub_le_lipConstR4 hfl x y) (norm_sub_le_lipConstR4 hgl x y))
  refine max_le (hsup.trans (add_le_add (le_max_left _ _) (le_max_left _ _))) ?_
  have h40 : 0 ≤ 40 * M := by positivity
  calc 40 * M * lipConstR4 (f + g) ≤ 40 * M * (lipConstR4 f + lipConstR4 g) :=
        mul_le_mul_of_nonneg_left hlip h40
    _ = 40 * M * lipConstR4 f + 40 * M * lipConstR4 g := by ring
    _ ≤ sharpNormR4 M f + sharpNormR4 M g :=
        add_le_add (le_max_right _ _) (le_max_right _ _)
theorem isLipschitzFor_smul {f : (Fin 4 → ℝ) → ℝ} (hf : IsLipschitzFor euclidDistR4 f) (a : ℝ) :
    IsLipschitzFor euclidDistR4 (a • f) := by
  obtain ⟨C, hC, h⟩ := hf
  refine ⟨|a| * C, mul_nonneg (abs_nonneg a) hC, fun x y => ?_⟩
  have h' : (a • f) x - (a • f) y = a * (f x - f y) := by simp [mul_sub]
  rw [h', norm_mul, Real.norm_eq_abs a, mul_assoc]
  exact mul_le_mul_of_nonneg_left (h x y) (abs_nonneg a)
theorem lipConstR4_smul_le {f : (Fin 4 → ℝ) → ℝ} (hf : IsLipschitzFor euclidDistR4 f) (a : ℝ) :
    lipConstR4 (a • f) ≤ |a| * lipConstR4 f := by
  refine lipConstR4_le (mul_nonneg (abs_nonneg a) (lipConstR4_nonneg f)) fun x y => ?_
  have h : (a • f) x - (a • f) y = a * (f x - f y) := by simp [mul_sub]
  rw [h, norm_mul, Real.norm_eq_abs a, mul_assoc]
  exact mul_le_mul_of_nonneg_left (norm_sub_le_lipConstR4 hf x y) (abs_nonneg a)
theorem lipConstR4_smul {f : (Fin 4 → ℝ) → ℝ} (hf : IsLipschitzFor euclidDistR4 f) (a : ℝ) :
    lipConstR4 (a • f) = |a| * lipConstR4 f := by
  refine le_antisymm (lipConstR4_smul_le hf a) ?_
  rcases eq_or_ne a 0 with rfl | ha
  · simpa using lipConstR4_nonneg ((0 : ℝ) • f)
  · have h := lipConstR4_smul_le (isLipschitzFor_smul hf a) a⁻¹
    rw [smul_smul, inv_mul_cancel₀ ha, one_smul, abs_inv] at h
    have ha' : 0 < |a| := abs_pos.2 ha
    calc |a| * lipConstR4 f ≤ |a| * (|a|⁻¹ * lipConstR4 (a • f)) :=
          mul_le_mul_of_nonneg_left h ha'.le
      _ = lipConstR4 (a • f) := mul_inv_cancel_left₀ ha'.ne' _
theorem uniformNorm_smul {X : Type*} (f : X → ℝ) (a : ℝ) :
    uniformNorm (a • f) = |a| * uniformNorm f := by
  simp only [TestFunctions.uniformNorm, Pi.smul_apply, smul_eq_mul, norm_mul, Real.norm_eq_abs]
  rw [Real.mul_iSup_of_nonneg (abs_nonneg a)]
theorem sharpNormR4_smul (M : ℝ) {f : (Fin 4 → ℝ) → ℝ} (hf : IsLipschitzFor euclidDistR4 f)
    (a : ℝ) : sharpNormR4 M (a • f) = |a| * sharpNormR4 M f := by
  simp only [TestFunctions.sharpNormR4]
  rw [uniformNorm_smul, lipConstR4_smul hf, mul_max_of_nonneg _ _ (abs_nonneg a)]
  congr 1
  ring
theorem eq_zero_of_sharpNormR4_eq_zero {M : ℝ} {f : (Fin 4 → ℝ) → ℝ} (hf : IsBoundedFun f)
    (h : sharpNormR4 M f = 0) : f = 0 := by
  have h₁ : uniformNorm f ≤ 0 := h ▸ le_max_left _ _
  funext x
  exact norm_le_zero_iff.1 ((norm_le_uniformNorm hf x).trans h₁)
end Numbers
section Derivatives
theorem partialDerivR4_eq_fderiv {f : (Fin 4 → ℝ) → ℝ} (hf : Differentiable ℝ f) (μ : Fin 4)
    (x : Fin 4 → ℝ) : partialDerivR4 μ f x = fderiv ℝ f x (Pi.single μ (1 : ℝ)) := by
  have hl : HasDerivAt (fun t : ℝ => x + t • (Pi.single μ (1 : ℝ) : Fin 4 → ℝ))
      (Pi.single μ (1 : ℝ)) 0 := by
    have h := ((hasDerivAt_id (0 : ℝ)).smul_const (Pi.single μ (1 : ℝ) : Fin 4 → ℝ)).const_add x
    rw [one_smul] at h
    exact h
  have hd : HasFDerivAt f (fderiv ℝ f x) (x + (0 : ℝ) • (Pi.single μ (1 : ℝ) : Fin 4 → ℝ)) := by
    rw [zero_smul, add_zero]
    exact (hf x).hasFDerivAt
  exact (hd.comp_hasDerivAt (0 : ℝ) hl).deriv
theorem clm_apply_eq_sum_coord (D : (Fin 4 → ℝ) →L[ℝ] ℝ) (v : Fin 4 → ℝ) :
    D v = ∑ μ, v μ * D (Pi.single μ (1 : ℝ)) := by apply _root_.YangMills.Construction.ReflectionPositivity.TorusC1Facts.clm_apply_eq_sum_basis <;> assumption
theorem sum_abs_le_two_mul_euclidNormVec (v : Fin 4 → ℝ) : ∑ μ, |v μ| ≤ 2 * euclidNormVec v := by apply _root_.YangMills.Construction.ReflectionPositivity.ApproximatingSequences.BoundedOfLimits.sum_abs_le_two_mul_euclidNormVec <;> assumption
theorem norm_sub_le_of_fderiv_coord_bound {F : (Fin 4 → ℝ) → ℝ} (hF : Differentiable ℝ F)
    {B : ℝ} (hB : 0 ≤ B)
    (h : ∀ z μ, |fderiv ℝ F z (Pi.single μ (1 : ℝ))| ≤ B) (x y : Fin 4 → ℝ) :
    ‖F x - F y‖ ≤ 2 * B * euclidDistR4 x y := by
  obtain ⟨v, hv⟩ : ∃ v, v = x - y := ⟨_, rfl⟩
  have hdist : euclidDistR4 x y = euclidNormVec v := by
    rw [hv]
    rfl
  have hder : ∀ t : ℝ, HasDerivAt (fun t : ℝ => F (y + t • v)) (fderiv ℝ F (y + t • v) v) t := by
    intro t
    have hl : HasDerivAt (fun t : ℝ => y + t • v) v t := by
      have h₁ := ((hasDerivAt_id t).smul_const v).const_add y
      rw [one_smul] at h₁
      exact h₁
    exact (hF _).hasFDerivAt.comp_hasDerivAt t hl
  have hb : ∀ t : ℝ, ‖fderiv ℝ F (y + t • v) v‖ ≤ 2 * B * euclidDistR4 x y := by
    intro t
    rw [clm_apply_eq_sum_coord, Real.norm_eq_abs, hdist]
    calc |∑ μ, v μ * fderiv ℝ F (y + t • v) (Pi.single μ (1 : ℝ))|
        ≤ ∑ μ, |v μ * fderiv ℝ F (y + t • v) (Pi.single μ (1 : ℝ))| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ μ, |v μ| * B := Finset.sum_le_sum fun μ _ => by
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left (h _ μ) (abs_nonneg _)
      _ = (∑ μ, |v μ|) * B := by rw [Finset.sum_mul]
      _ ≤ (2 * euclidNormVec v) * B :=
          mul_le_mul_of_nonneg_right (sum_abs_le_two_mul_euclidNormVec v) hB
      _ = 2 * B * euclidNormVec v := by ring
  have h₁ := norm_image_sub_le_of_norm_deriv_le_segment_01' (f := fun t : ℝ => F (y + t • v))
    (fun t _ => (hder t).hasDerivWithinAt) (fun t _ => hb t)
  have e1 : y + (1 : ℝ) • v = x := by
    rw [one_smul, hv]
    abel
  have e0 : y + (0 : ℝ) • v = y := by rw [zero_smul, add_zero]
  simp only [e1, e0] at h₁
  exact h₁
variable {g : (Fin 4 → ℝ) → ℝ}
theorem isBoundedFun_of_contDiff (hc : ContDiff ℝ 1 g) (hs : HasCompactSupport g) :
    IsBoundedFun g :=
  hc.continuous.bounded_above_of_compact_support hs
theorem isBoundedFun_partialDerivR4 (hc : ContDiff ℝ 1 g) (hs : HasCompactSupport g) (μ : Fin 4) :
    IsBoundedFun (partialDerivR4 μ g) := by
  have he : partialDerivR4 μ g = fun z => fderiv ℝ g z (Pi.single μ (1 : ℝ)) :=
    funext fun z => partialDerivR4_eq_fderiv (hc.differentiable one_ne_zero) μ z
  rw [he]
  exact ((hc.continuous_fderiv one_ne_zero).clm_apply continuous_const).bounded_above_of_compact_support
    (hs.fderiv_apply (𝕜 := ℝ) _)
theorem abs_fderiv_coord_le_c1NormR4 (hc : ContDiff ℝ 1 g) (hs : HasCompactSupport g)
    (z : Fin 4 → ℝ) (μ : Fin 4) : |fderiv ℝ g z (Pi.single μ (1 : ℝ))| ≤ c1NormR4 g := by
  rw [← partialDerivR4_eq_fderiv (hc.differentiable one_ne_zero), ← Real.norm_eq_abs]
  calc ‖partialDerivR4 μ g z‖ ≤ uniformNorm (partialDerivR4 μ g) :=
        norm_le_uniformNorm (isBoundedFun_partialDerivR4 hc hs μ) z
    _ ≤ ⨆ μ : Fin 4, uniformNorm (partialDerivR4 μ g) :=
        le_ciSup (f := fun μ : Fin 4 => uniformNorm (partialDerivR4 μ g))
          (Set.finite_range _).bddAbove μ
    _ ≤ c1NormR4 g := le_max_right _ _
theorem c1NormR4_nonneg : 0 ≤ c1NormR4 g := by apply _root_.YangMills.Construction.ReflectionPositivity.ApproximatingSequences.BoundedOfLimits.c1NormR4_nonneg <;> assumption
theorem isLipschitzFor_of_contDiff (hc : ContDiff ℝ 1 g) (hs : HasCompactSupport g) :
    IsLipschitzFor euclidDistR4 g :=
  ⟨2 * c1NormR4 g, mul_nonneg zero_le_two c1NormR4_nonneg, fun x y =>
    norm_sub_le_of_fderiv_coord_bound (hc.differentiable one_ne_zero) c1NormR4_nonneg
      (abs_fderiv_coord_le_c1NormR4 hc hs) x y⟩
theorem sharpNormR4_le_of_contDiff (hc : ContDiff ℝ 1 g) (hs : HasCompactSupport g) {M : ℝ}
    (hM : 1 ≤ M) : sharpNormR4 M g ≤ 80 * M * c1NormR4 g := by
  have hC : 0 ≤ c1NormR4 g := c1NormR4_nonneg
  have hlip : lipConstR4 g ≤ 2 * c1NormR4 g :=
    lipConstR4_le (mul_nonneg zero_le_two hC) fun x y =>
      norm_sub_le_of_fderiv_coord_bound (hc.differentiable one_ne_zero) hC
        (abs_fderiv_coord_le_c1NormR4 hc hs) x y
  have hsup : uniformNorm g ≤ c1NormR4 g := le_max_left _ _
  refine max_le ?_ ?_
  · nlinarith
  · nlinarith
theorem tendsto_sharpNormR4_translate_sub (hc : ContDiff ℝ 1 g) (hs : HasCompactSupport g)
    {M : ℝ} (hM : 0 ≤ M) (v : Fin 4 → ℝ) :
    Tendsto (fun w : Fin 4 → ℝ => sharpNormR4 M fun x => g (x - w) - g (x - v))
      (𝓝 v) (𝓝 0) := by
  have hdiff : Differentiable ℝ g := hc.differentiable one_ne_zero
  have hug : UniformContinuous g :=
    hc.continuous.uniformContinuous_of_tendsto_cocompact hs.is_zero_at_infty
  have hud : UniformContinuous (fderiv ℝ g) :=
    (hc.continuous_fderiv one_ne_zero).uniformContinuous_of_tendsto_cocompact
      (hs.fderiv (𝕜 := ℝ)).is_zero_at_infty
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hpos : 0 < 2 * (80 * M + 1) := by positivity
  obtain ⟨η, hη⟩ : ∃ η, η = ε / (2 * (80 * M + 1)) := ⟨_, rfl⟩
  have hη₀ : 0 < η := hη ▸ div_pos hε hpos
  have hηε : η * (80 * M + 1) < ε := by
    have h₁ : η * (2 * (80 * M + 1)) = ε := by
      rw [hη]
      exact div_mul_cancel₀ _ hpos.ne'
    nlinarith
  obtain ⟨δ₁, h₁, H₁⟩ := Metric.uniformContinuous_iff.1 hug η hη₀
  obtain ⟨δ₂, h₂, H₂⟩ := Metric.uniformContinuous_iff.1 hud η hη₀
  filter_upwards [Metric.ball_mem_nhds v (lt_min h₁ h₂)] with w hw
  have hd : ∀ x : Fin 4 → ℝ, dist (x - w) (x - v) < min δ₁ δ₂ := fun x => by
    rw [dist_sub_left]
    exact hw
  have hderiv : ∀ a : Fin 4 → ℝ, ∀ z : Fin 4 → ℝ,
      HasFDerivAt (fun x => g (x - a)) (fderiv ℝ g (z - a)) z := by
    intro a z
    have hda : DifferentiableAt ℝ (fun x => g (x - a)) z :=
      (differentiableAt_comp_sub a).2 (hdiff _)
    have h₃ := hda.hasFDerivAt
    rw [fderiv_comp_sub] at h₃
    exact h₃
  have hF : ∀ z, HasFDerivAt (fun x => g (x - w) - g (x - v))
      (fderiv ℝ g (z - w) - fderiv ℝ g (z - v)) z :=
    fun z => (hderiv w z).sub (hderiv v z)
  have hFd : Differentiable ℝ (fun x => g (x - w) - g (x - v)) :=
    fun z => (hF z).differentiableAt
  have hbound : ∀ z (μ : Fin 4),
      |fderiv ℝ (fun x => g (x - w) - g (x - v)) z (Pi.single μ (1 : ℝ))| ≤ η := by
    intro z μ
    rw [(hF z).fderiv, ← Real.norm_eq_abs]
    have he : ‖(Pi.single μ (1 : ℝ) : Fin 4 → ℝ)‖ ≤ 1 :=
      (pi_norm_le_iff_of_nonneg zero_le_one).2 fun ν => by
        rw [Pi.single_apply]
        split_ifs <;> simp
    have hn : ‖fderiv ℝ g (z - w) - fderiv ℝ g (z - v)‖ ≤ η := by
      rw [← dist_eq_norm]
      exact (H₂ ((hd z).trans_le (min_le_right _ _))).le
    calc ‖(fderiv ℝ g (z - w) - fderiv ℝ g (z - v)) (Pi.single μ (1 : ℝ))‖
        ≤ ‖fderiv ℝ g (z - w) - fderiv ℝ g (z - v)‖ * ‖(Pi.single μ (1 : ℝ) : Fin 4 → ℝ)‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ η * 1 := mul_le_mul hn he (norm_nonneg _) hη₀.le
      _ = η := mul_one η
  have hsup : uniformNorm (fun x => g (x - w) - g (x - v)) ≤ η := uniformNorm_le fun x => by
    rw [← dist_eq_norm]
    exact (H₁ ((hd x).trans_le (min_le_left _ _))).le
  have hlip : lipConstR4 (fun x => g (x - w) - g (x - v)) ≤ 2 * η :=
    lipConstR4_le (by positivity) fun x y =>
      norm_sub_le_of_fderiv_coord_bound hFd hη₀.le hbound x y
  have hsharp : sharpNormR4 M (fun x => g (x - w) - g (x - v)) ≤ η * (80 * M + 1) := by
    refine max_le ?_ ?_
    · nlinarith
    · have h40 : 0 ≤ 40 * M := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hlip h40]
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (sharpNormR4_nonneg _ _)]
  exact hsharp.trans_lt hηε
end Derivatives
section Space
variable {s : Conventions.StandingParameters}
theorem hasCompactSupport_of_mem_c1SupportedIn {A : Set (EuclideanFour s)} {g : (Fin 4 → ℝ) → ℝ}
    (hg : g ∈ c1SupportedIn A) : HasCompactSupport g := by
  have hs : tsupport (g ∘ (homeomorphPi (s := s))) = (homeomorphPi (s := s)) ⁻¹' tsupport g :=
    tsupport_comp_homeo homeomorphPi g
  have h' : IsCompact ((homeomorphPi (s := s)) ⁻¹' tsupport g) := by
    rw [← hs]
    exact hg.2.1
  exact homeomorphPi.isCompact_preimage.1 h'
theorem contDiff_of_mem_c1SupportedIn {A : Set (EuclideanFour s)} {g : (Fin 4 → ℝ) → ℝ}
    (hg : g ∈ c1SupportedIn A) : ContDiff ℝ 1 g :=
  hg.1
theorem tsupport_linComb_subset {X : Type*} [TopologicalSpace X] (t t' : ℝ) (f g : X → ℝ) :
    tsupport (t • f + t' • g) ⊆ tsupport f ∪ tsupport g := by
  refine closure_minimal ?_ ((isClosed_tsupport _).union (isClosed_tsupport _))
  intro u hu
  by_contra hn
  simp only [Set.mem_union, not_or] at hn
  exact hu (by simp [image_eq_zero_of_notMem_tsupport hn.1, image_eq_zero_of_notMem_tsupport hn.2])
theorem linComb_mem_c1SupportedIn {A : Set (EuclideanFour s)} {f g : EuclideanFour s → ℝ}
    (hf : f ∈ c1SupportedIn A) (hg : g ∈ c1SupportedIn A) (t t' : ℝ) :
    t • f + t' • g ∈ c1SupportedIn A := by
  have hsub := tsupport_linComb_subset t t' f g
  obtain ⟨h₁, h₂, h₃⟩ := hf
  obtain ⟨h₄, h₅, h₆⟩ := hg
  exact ⟨(ContDiff.const_smul t h₁).add (ContDiff.const_smul t' h₄),
    (h₂.union h₅).of_isClosed_subset (isClosed_tsupport _) hsub,
    hsub.trans (Set.union_subset h₃ h₆)⟩
theorem isFunctionSubspace_c1SupportedIn (A : Set (EuclideanFour s)) :
    IsFunctionSubspace (c1SupportedIn A) := by
  refine ⟨{ carrier := c1SupportedIn A, add_mem' := ?_, zero_mem' := ?_, smul_mem' := ?_ },
    rfl⟩
  · intro f g hf hg
    have h := linComb_mem_c1SupportedIn hf hg 1 1
    rw [one_smul, one_smul] at h
    exact h
  · have h0 : tsupport (0 : EuclideanFour s → ℝ) = ∅ := by simp [tsupport]
    refine ⟨contDiff_const (c := (0 : ℝ)), ?_, ?_⟩
    · rw [h0]
      exact isCompact_empty
    · rw [h0]
      exact Set.empty_subset _
  · intro c f hf
    have h := linComb_mem_c1SupportedIn hf hf c 0
    rw [zero_smul, add_zero] at h
    exact h
theorem isNormOn_c1SupportedIn (M : SharpParameter) (A : Set (EuclideanFour s)) :
    IsNormOn (c1SupportedIn A) (sharpNormR4 (M : ℝ)) := by
  have hM : 0 ≤ (M : ℝ) := zero_le_one.trans M.2
  have hb : ∀ f ∈ c1SupportedIn A, IsBoundedFun (f : (Fin 4 → ℝ) → ℝ) := fun f hf =>
    isBoundedFun_of_contDiff (contDiff_of_mem_c1SupportedIn hf)
      (hasCompactSupport_of_mem_c1SupportedIn hf)
  have hl : ∀ f ∈ c1SupportedIn A, IsLipschitzFor euclidDistR4 (f : (Fin 4 → ℝ) → ℝ) :=
    fun f hf => isLipschitzFor_of_contDiff (contDiff_of_mem_c1SupportedIn hf)
      (hasCompactSupport_of_mem_c1SupportedIn hf)
  refine ⟨fun f _ => sharpNormR4_nonneg _ f, fun f hf h => ?_, fun a f hf => ?_,
    fun f hf g hg => ?_⟩
  · exact eq_zero_of_sharpNormR4_eq_zero (hb f hf) h
  · exact sharpNormR4_smul _ (hl f hf) a
  · exact sharpNormR4_add_le hM (hb f hf) (hl f hf) (hb g hg) (hl g hg)
end Space
section Isometries
variable {s : Conventions.StandingParameters}
theorem isometryPreservesNorms_holds (M : SharpParameter) (r : FourIsometry s) :
    IsometryPreservesNorms s M r := by
  intro E _ f _ _
  have hsup : uniformNorm (transportFn r.1 f) = uniformNorm f :=
    r.1.symm.surjective.iSup_comp fun y => ‖f y‖
  have hlip : lipConstR4 (transportFn r.1 f) = lipConstR4 f := by
    refine congrArg sInf (Set.ext fun C => ?_)
    constructor
    · rintro ⟨h0, h⟩
      refine ⟨h0, fun (x y : EuclideanFour s) => ?_⟩
      have h₁ : ‖f (r.1.symm (r.1 x)) - f (r.1.symm (r.1 y))‖ ≤
          C * euclidDistR4 (r.1 x) (r.1 y) := h (r.1 x) (r.1 y)
      have h₂ : euclidDistR4 (r.1 x) (r.1 y) = euclidDistR4 x y := r.2 x y
      rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply, h₂] at h₁
      exact h₁
    · rintro ⟨h0, h⟩
      refine ⟨h0, fun x y => ?_⟩
      have h₁ : ‖f (r.1.symm x) - f (r.1.symm y)‖ ≤
          C * euclidDistR4 (r.1.symm x) (r.1.symm y) := h (r.1.symm x) (r.1.symm y)
      have h₂ : euclidDistR4 (r.1.symm x) (r.1.symm y) = euclidDistR4 x y :=
        isDistIsometry_symm r.2 x y
      rw [h₂] at h₁
      exact h₁
  exact ⟨hsup, hlip, congrArg₂ (fun a b : ℝ => max a (40 * (M : ℝ) * b)) hsup hlip⟩
theorem setDistR4_image {σ : (Fin 4 → ℝ) → Fin 4 → ℝ}
    (hσ : ∀ a b, euclidDistR4 (σ a) (σ b) = euclidDistR4 a b) (S S' : Set (Fin 4 → ℝ)) :
    setDistR4 (σ '' S) (σ '' S') = setDistR4 S S' := by
  simp only [TestFunctions.setDistR4, iInf_image]
  refine iInf_congr fun a => iInf_congr fun _ => iInf_congr fun b => iInf_congr fun _ => ?_
  exact congrArg ENNReal.ofReal (hσ a b)
theorem isometryPreservesBallsAndSetDist_holds (r : FourIsometry s) :
    IsometryPreservesBallsAndSetDist s r := by
  refine ⟨fun S x R hS => ⟨r.1 x, ?_⟩, fun S S' => ?_⟩
  · rintro _ ⟨z, hz, rfl⟩
    have h : euclidDistR4 (r.1 z) (r.1 x) = euclidDistR4 z x := r.2 z x
    have h₂ : euclidDistR4 z x ≤ R := hS hz
    exact h.le.trans h₂
  · exact setDistR4_image (σ := r.1) (fun a b => r.2 a b) S S'
end Isometries
section Thickenings
variable {s : Conventions.StandingParameters}
theorem setDistR4_eq_iInf_edist (S S' : Set (EuclideanFour s)) :
    setDistR4 S S' = ⨅ a ∈ S, ⨅ b ∈ S', edist a b := by
  simp only [edist_dist]
  rfl
theorem setDistR4_singleton (x : EuclideanFour s) (B : Set (EuclideanFour s)) :
    setDistR4 ({x} : Set (EuclideanFour s)) B = Metric.infEDist x B := by
  have h := setDistR4_eq_iInf_edist ({x} : Set (EuclideanFour s)) B
  rw [iInf_singleton] at h
  exact h
theorem setDistR4_pos {A B : Set (EuclideanFour s)} (hA : IsCompact A) (hB : IsCompact B)
    (h : Disjoint A B) : 0 < setDistR4 A B := by
  obtain ⟨r, hr, H⟩ := Metric.exists_pos_forall_lt_edist hA hB.isClosed h
  rw [setDistR4_eq_iInf_edist]
  exact lt_of_lt_of_le (ENNReal.coe_pos.2 hr)
    (le_iInf₂ fun a ha => le_iInf₂ fun b hb => (H a ha b hb).le)
theorem setDistR4_ne_top {A B : Set (EuclideanFour s)} (hA : A.Nonempty) (hB : B.Nonempty) :
    setDistR4 A B ≠ ⊤ := by
  obtain ⟨a, ha⟩ := hA
  obtain ⟨b, hb⟩ := hB
  rw [setDistR4_eq_iInf_edist]
  exact ne_top_of_le_ne_top (edist_ne_top a b) ((iInf₂_le a ha).trans (iInf₂_le b hb))
variable {k : ℕ} {A : Fin k → Set (EuclideanFour s)}
theorem minPairSetDist_le {i l : Fin k} (hil : i ≠ l) (hi : (A i).Nonempty)
    (hl : (A l).Nonempty) : minPairSetDist A ≤ setDistR4 (A i) (A l) :=
  (iInf_le _ i).trans ((iInf_le _ l).trans (iInf_le _ ⟨hil, hi, hl⟩))
theorem minPairSetDist_pos (hc : ∀ i, IsCompact (A i))
    (hd : Pairwise fun i l => Disjoint (A i) (A l)) (hp : HasTwoNonemptyMembers A) :
    0 < minPairSetDist A := by
  obtain ⟨i₀, l₀, -⟩ := hp
  have : Nonempty (Fin k × Fin k) := ⟨(i₀, l₀)⟩
  let g : Fin k × Fin k → ℝ≥0∞ := fun p =>
    ⨅ (_ : p.1 ≠ p.2 ∧ (A p.1).Nonempty ∧ (A p.2).Nonempty), setDistR4 (A p.1) (A p.2)
  have hg : minPairSetDist A = ⨅ p, g p := by
    rw [iInf_prod]
    rfl
  obtain ⟨p, hp⟩ := exists_eq_ciInf_of_finite (f := g)
  rw [hg, ← hp]
  by_cases hq : p.1 ≠ p.2 ∧ (A p.1).Nonempty ∧ (A p.2).Nonempty
  · change 0 < ⨅ (_ : p.1 ≠ p.2 ∧ (A p.1).Nonempty ∧ (A p.2).Nonempty),
      setDistR4 (A p.1) (A p.2)
    rw [iInf_pos hq]
    exact setDistR4_pos (hc _) (hc _) (hd hq.1)
  · change 0 < ⨅ (_ : p.1 ≠ p.2 ∧ (A p.1).Nonempty ∧ (A p.2).Nonempty),
      setDistR4 (A p.1) (A p.2)
    rw [iInf_neg hq]
    exact ENNReal.zero_lt_top
theorem minPairSetDist_ne_top (hp : HasTwoNonemptyMembers A) :
    minPairSetDist A ≠ ⊤ := by
  obtain ⟨i, l, hil, hi, hl⟩ := hp
  exact ne_top_of_le_ne_top (setDistR4_ne_top hi hl) (minPairSetDist_le hil hi hl)
theorem separationConst_pos (hc : ∀ i, IsCompact (A i))
    (hd : Pairwise fun i l => Disjoint (A i) (A l)) : 0 < separationConst A := by
  unfold separationConst
  split_ifs with h
  · exact ENNReal.toReal_pos (minPairSetDist_pos hc hd h).ne' (minPairSetDist_ne_top h)
  · exact one_pos
theorem ofReal_separationConst_le {i l : Fin k} (hil : i ≠ l) (hi : (A i).Nonempty)
    (hl : (A l).Nonempty) :
    ENNReal.ofReal (separationConst A) ≤ setDistR4 (A i) (A l) := by
  have hp : HasTwoNonemptyMembers A := ⟨i, l, hil, hi, hl⟩
  have h : separationConst A = (minPairSetDist A).toReal := if_pos hp
  rw [h, ENNReal.ofReal_toReal (minPairSetDist_ne_top hp)]
  exact minPairSetDist_le hil hi hl
theorem thickening_of_empty {i : Fin k} (h : A i = ∅) : thickening A i = ∅ :=
  if_pos h
theorem thickening_eq_cthickening {i : Fin k} (h : (A i).Nonempty) :
    thickening A i = Metric.cthickening (separationConst A / 3) (A i) := by
  unfold thickening
  rw [if_neg h.ne_empty]
  ext x
  rw [Metric.mem_cthickening_iff, ← setDistR4_singleton]
  exact Iff.rfl
theorem isCompact_cthickening_euclideanFour {B : Set (EuclideanFour s)} (hB : IsCompact B)
    (δ : ℝ) : IsCompact (Metric.cthickening δ B) := by
  have h : Metric.cthickening δ B = (equivEuclidean (s := s)) ⁻¹'
      Metric.cthickening δ ((equivEuclidean (s := s)) '' B) := by
    ext x
    rw [Set.mem_preimage, Metric.mem_cthickening_iff, Metric.mem_cthickening_iff,
      Metric.infEDist_image (equivEuclidean (s := s)).isometry]
  rw [h]
  exact (equivEuclidean (s := s)).toHomeomorph.isCompact_preimage.2
    ((hB.image (equivEuclidean (s := s)).continuous).cthickening)
theorem mem_cthickening_of_dist_le {B : Set (EuclideanFour s)} {x y : EuclideanFour s}
    (hx : x ∈ B) {δ : ℝ} (h : euclidDistR4 y x ≤ δ) : y ∈ Metric.cthickening δ B := by
  rw [Metric.mem_cthickening_iff]
  refine (Metric.infEDist_le_edist_of_mem hx).trans ?_
  rw [edist_dist]
  exact ENNReal.ofReal_le_ofReal h
theorem euclidDistR4_add_self (x v : Fin 4 → ℝ) : euclidDistR4 (x + v) x = euclidNormVec v := by
  unfold euclidDistR4
  rw [add_sub_cancel_left]
theorem disjointCompactsHaveDisjointThickenings_holds (s : Conventions.StandingParameters) :
    DisjointCompactsHaveDisjointThickenings s := by
  intro k _ A hc hd
  have hsep := separationConst_pos hc hd
  have hq : 0 ≤ separationConst A / 3 := by positivity
  refine ⟨hsep, fun i => ?_, fun i l hil => ?_, fun i v hv => ?_⟩
  · by_cases h : A i = ∅
    · rw [thickening_of_empty h]
      exact isCompact_empty
    · rw [thickening_eq_cthickening (Set.nonempty_iff_ne_empty.2 h)]
      exact isCompact_cthickening_euclideanFour (hc i) _
  · change Disjoint (thickening A i) (thickening A l)
    by_cases hi : A i = ∅
    · rw [thickening_of_empty hi]
      exact Set.empty_disjoint _
    by_cases hl : A l = ∅
    · rw [thickening_of_empty hl]
      exact Set.disjoint_empty _
    have hi' := Set.nonempty_iff_ne_empty.2 hi
    have hl' := Set.nonempty_iff_ne_empty.2 hl
    rw [thickening_eq_cthickening hi', thickening_eq_cthickening hl', Set.disjoint_left]
    intro x hx hy
    rw [Metric.mem_cthickening_iff] at hx hy
    obtain ⟨a, ha, hax⟩ := (hc i).exists_infEDist_eq_edist hi' x
    obtain ⟨b, hb, hbx⟩ := (hc l).exists_infEDist_eq_edist hl' x
    rw [hax, edist_dist, ENNReal.ofReal_le_ofReal_iff hq] at hx
    rw [hbx, edist_dist, ENNReal.ofReal_le_ofReal_iff hq] at hy
    have h1 : ENNReal.ofReal (separationConst A) ≤ ENNReal.ofReal (dist a b) := by
      refine (ofReal_separationConst_le hil hi' hl').trans ?_
      rw [setDistR4_eq_iInf_edist, ← edist_dist]
      exact (iInf₂_le a ha).trans (iInf₂_le b hb)
    rw [ENNReal.ofReal_le_ofReal_iff dist_nonneg] at h1
    have h2 : dist a b ≤ dist a x + dist x b := dist_triangle _ _ _
    rw [dist_comm a x] at h2
    linarith
  · rintro _ ⟨x, hx, rfl⟩
    rw [thickening_eq_cthickening ⟨x, hx⟩]
    exact mem_cthickening_of_dist_le hx ((euclidDistR4_add_self x v).le.trans hv)
end Thickenings
theorem statement_holds : Statement := by
  intro s M
  have hM : 0 ≤ (M : ℝ) := zero_le_one.trans M.2
  refine ⟨⟨?_, fun A => ⟨isFunctionSubspace_c1SupportedIn A, isNormOn_c1SupportedIn M A⟩⟩,
    fun r => ⟨isometryPreservesNorms_holds M r, isometryPreservesBallsAndSetDist_holds r⟩, ?_,
    disjointCompactsHaveDisjointThickenings_holds s⟩
  · intro f hf
    have hc := contDiff_of_mem_c1SupportedIn hf
    have hs := hasCompactSupport_of_mem_c1SupportedIn hf
    exact ⟨isBoundedFun_of_contDiff hc hs, isLipschitzFor_of_contDiff hc hs,
      fun μ => isBoundedFun_partialDerivR4 hc hs μ, sharpNormR4_le_of_contDiff hc hs M.2⟩
  · intro f hf v
    exact tendsto_sharpNormR4_translate_sub (contDiff_of_mem_c1SupportedIn hf)
      (hasCompactSupport_of_mem_c1SupportedIn hf) hM v
end YangMills.Construction.Continuum.SeparatedFourTuples.SharpNormAndThickenings
end
