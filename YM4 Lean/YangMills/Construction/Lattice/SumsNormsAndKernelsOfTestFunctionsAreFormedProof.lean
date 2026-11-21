import YangMills.Construction.Lattice.PeriodicLattices
import YangMills.Construction.Lattice.LayerBondsCoarseSpacesAndAverages
import YangMills.Construction.Lattice.SumsNormsAndKernelsOfTestFunctionsAreFormed
import YangMills.Construction.SystemOfAdmissibleConstants.CumulantConditionsFromTheInequalityProof
import YangMills.Construction.Torus.GeometryAndFreeKernelOfATestPairProof
import Mathlib
set_option autoImplicit false
open MeasureTheory Set YangMills.Construction.TorusMetric YangMills.Construction.PeriodicLattice
noncomputable section
namespace YangMills.Construction.TestFunctions
namespace WellFormed
theorem abs_apply_le_euclidNormVec (v : Fin 4 → ℝ) (μ : Fin 4) : |v μ| ≤ euclidNormVec v := by apply _root_.YangMills.Construction.Parametrix.UnitKernelSupport.abs_apply_le_euclidNormVec <;> assumption
theorem torusProj_add_vec (ℓ : ℝ) (v w : Fin 4 → ℝ) :
    torusProj ℓ (v + w) = torusProj ℓ v + torusProj ℓ w := by apply _root_.YangMills.Construction.TestPairs.torusProj_map_add <;> assumption
theorem torusProj_sub_vec (ℓ : ℝ) (v w : Fin 4 → ℝ) :
    torusProj ℓ (v - w) = torusProj ℓ v - torusProj ℓ w := by apply _root_.YangMills.Construction.TestPairs.torusProj_map_sub <;> assumption
theorem eq_of_translates_close {ℓ : ℝ} (hℓ : 0 < ℓ) (k k' : Fin 4 → ℤ) (v : Fin 4 → ℝ)
    (hd : euclidNormVec ((v + latticeTranslate ℓ k) - (v + latticeTranslate ℓ k')) ≤ ℓ / 2) :
    k = k' := by
  funext μ
  have h := (abs_apply_le_euclidNormVec _ μ).trans hd
  simp only [Pi.sub_apply, Pi.add_apply, latticeTranslate] at h
  have h2 : |ℓ * ((k μ : ℝ) - k' μ)| ≤ ℓ / 2 := by
    have e : v μ + ℓ * (k μ : ℝ) - (v μ + ℓ * (k' μ : ℝ)) = ℓ * ((k μ : ℝ) - k' μ) := by ring
    rwa [e] at h
  rw [abs_mul, abs_of_pos hℓ] at h2
  have h3 : |(k μ : ℝ) - k' μ| ≤ 1 / 2 := by
    by_contra hc
    push Not at hc
    nlinarith
  by_contra hne
  have h4 : (1 : ℤ) ≤ |k μ - k' μ| := Int.one_le_abs (sub_ne_zero.mpr hne)
  have h5 : (1 : ℝ) ≤ |(k μ : ℝ) - k' μ| := by exact_mod_cast h4
  linarith
theorem periodize_properties {E : Type} [AddCommMonoid E] [TopologicalSpace E] {ℓ : ℝ}
    {A : Set (Fin 4 → ℝ)} {f : (Fin 4 → ℝ) → E} (hℓ : 0 < ℓ) (h : IsPeriodizable ℓ A f) :
    (∀ (v : Fin 4 → ℝ) (k k' : Fin 4 → ℤ), f (v + latticeTranslate ℓ k) ≠ 0 →
      f (v + latticeTranslate ℓ k') ≠ 0 → k = k') ∧
      (∀ v ∈ A, periodize ℓ f (torusProj ℓ v) = f v) ∧
      ∀ x, x ∉ torusProj ℓ '' A → periodize ℓ f x = 0 := by
  obtain ⟨hd, hs⟩ := h
  refine ⟨fun v k k' h1 h2 => eq_of_translates_close hℓ k k' v (hd _ (hs h1) _ (hs h2)), ?_, ?_⟩
  · intro v hv
    have hp0 : latticeTranslate ℓ 0 = 0 := by
      funext μ
      simp [latticeTranslate]
    rw [periodize_torusProj, periodicSum, tsum_eq_single (0 : Fin 4 → ℤ)]
    · rw [hp0, add_zero]
    · intro k hk
      by_contra hne
      apply hk
      refine eq_of_translates_close hℓ k 0 v ?_
      rw [hp0, add_zero]
      exact hd _ (hs hne) _ hv
  · intro x hx
    have h0 : ∀ k, f (liftPoint x + latticeTranslate ℓ k) = 0 := by
      intro k
      by_contra hne
      exact hx ⟨_, hs hne, by rw [torusProj_add_latticeTranslate, torusProj_liftPoint]⟩
    simp [periodize, periodicSum, h0]
theorem torusEuclidNorm_le {ℓ : ℝ} (hℓ : 0 < ℓ) (u : Torus4 ℓ) :
    torusEuclidNorm u ≤ ℓ := by apply _root_.YangMills.SharedProofs.p53575 <;> assumption
theorem isBoundedFun_of_isLipschitzFor {ℓ : ℝ} (hℓ : 0 < ℓ) {E : Type} [NormedAddCommGroup E]
    {f : Torus4 ℓ → E} (h : IsLipschitzFor euclidDistTorus f) : IsBoundedFun f := by
  obtain ⟨C, hC, hf⟩ := h
  refine ⟨‖f 0‖ + C * ℓ, fun x => ?_⟩
  have h1 := hf x 0
  have h2 : euclidDistTorus x 0 ≤ ℓ := torusEuclidNorm_le hℓ _
  have h3 : ‖f x‖ ≤ ‖f x - f 0‖ + ‖f 0‖ := by simpa using norm_add_le (f x - f 0) (f 0)
  nlinarith [mul_le_mul_of_nonneg_left h2 hC]
theorem bestLipschitzConstant_properties {X E : Type} [NormedAddCommGroup E]
    {d : X → X → ℝ} {f : X → E} (h0 : ∀ x y, 0 ≤ d x y) (hf : IsLipschitzFor d f) :
    0 ≤ bestLipschitzConstant d f ∧
      (∀ x y, ‖f x - f y‖ ≤ bestLipschitzConstant d f * d x y) ∧
      ∀ C : ℝ, 0 ≤ C → (∀ x y, ‖f x - f y‖ ≤ C * d x y) → bestLipschitzConstant d f ≤ C := by
  obtain ⟨C₀, hC₀⟩ := hf
  refine ⟨Real.sInf_nonneg fun C hC => hC.1, fun x y => ?_, fun C hC hb => ?_⟩
  · rcases (h0 x y).eq_or_lt with h | h
    · have h1 := hC₀.2 x y
      rw [← h] at h1 ⊢
      simpa using h1
    · have h1 : ‖f x - f y‖ / d x y ≤ bestLipschitzConstant d f :=
        le_csInf ⟨C₀, hC₀⟩ fun C hC => (div_le_iff₀ h).mpr (hC.2 x y)
      exact (div_le_iff₀ h).mp h1
  · exact csInf_le ⟨0, fun C hC => hC.1⟩ ⟨hC, hb⟩
section Kernels
variable {𝕜 : Type} [RCLike 𝕜]
theorem continuous_euclidNormVec : Continuous euclidNormVec := by apply _root_.YangMills.Construction.SeparatedTuples.continuous_euclidNormVec <;> assumption
theorem measurable_inverseEighthWeight :
    Measurable fun u : Fin 4 → ℝ => ((euclidNormVec u ^ (-8 : ℤ) : ℝ) : 𝕜) := by
  have h1 : Measurable fun t : ℝ => t ^ (-8 : ℤ) := by
    have e : (fun t : ℝ => t ^ (-8 : ℤ)) = fun t => (t ^ 8)⁻¹ := by
      funext t
      rw [zpow_neg]
      norm_cast
    rw [e]
    exact (measurable_id.pow_const 8).inv
  exact RCLike.continuous_ofReal.measurable.comp (h1.comp continuous_euclidNormVec.measurable)
theorem integrable_inverseEighthIntegrand {f h : (Fin 4 → ℝ) → 𝕜} (hp : IsKernelPairR4 f h) :
    Integrable fun z : (Fin 4 → ℝ) × (Fin 4 → ℝ) =>
      f z.1 * h z.2 * ((euclidNormVec (z.1 - z.2) ^ (-8 : ℤ) : ℝ) : 𝕜) := by
  obtain ⟨⟨Cf, hCf⟩, ⟨Ch, hCh⟩, hfm, hhm, hfc, hhc, hd⟩ := hp
  obtain ⟨δ, hδ, hδd⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hd
  have hδ' : (0 : ℝ) < δ := by exact_mod_cast hδ
  have hsep : ∀ x ∈ tsupport f, ∀ y ∈ tsupport h, (δ : ℝ) ≤ euclidNormVec (x - y) := by
    intro x hx y hy
    have h1 : (δ : ENNReal) ≤ ENNReal.ofReal (euclidNormVec (x - y)) :=
      hδd.le.trans ((iInf₂_le x hx).trans (iInf₂_le y hy))
    rw [← ENNReal.ofReal_coe_nnreal] at h1
    exact (ENNReal.ofReal_le_ofReal_iff (Real.sqrt_nonneg _)).mp h1
  have hS : IsCompact (tsupport f ×ˢ tsupport h) := hfc.isCompact.prod hhc.isCompact
  have hSm : MeasurableSet (tsupport f ×ˢ tsupport h) := hS.isClosed.measurableSet
  have hmeas : Measurable fun z : (Fin 4 → ℝ) × (Fin 4 → ℝ) =>
      f z.1 * h z.2 * ((euclidNormVec (z.1 - z.2) ^ (-8 : ℤ) : ℝ) : 𝕜) :=
    ((hfm.comp measurable_fst).mul (hhm.comp measurable_snd)).mul
      ((measurable_inverseEighthWeight (𝕜 := 𝕜)).comp (measurable_fst.sub measurable_snd))
  have hIn : IntegrableOn (fun z : (Fin 4 → ℝ) × (Fin 4 → ℝ) =>
      f z.1 * h z.2 * ((euclidNormVec (z.1 - z.2) ^ (-8 : ℤ) : ℝ) : 𝕜))
      (tsupport f ×ˢ tsupport h) := by
    refine Measure.integrableOn_of_bounded (M := Cf * Ch * ((δ : ℝ) ^ 8)⁻¹)
      hS.measure_lt_top.ne hmeas.aestronglyMeasurable ?_
    refine ae_restrict_of_forall_mem hSm fun z hz => ?_
    have he := hsep _ hz.1 _ hz.2
    have he0 : 0 < euclidNormVec (z.1 - z.2) := hδ'.trans_le he
    have hw : ‖((euclidNormVec (z.1 - z.2) ^ (-8 : ℤ) : ℝ) : 𝕜)‖ ≤ ((δ : ℝ) ^ 8)⁻¹ := by
      rw [RCLike.norm_ofReal, abs_of_pos (zpow_pos he0 _), zpow_neg]
      have e : euclidNormVec (z.1 - z.2) ^ (8 : ℤ) = euclidNormVec (z.1 - z.2) ^ 8 := by norm_cast
      rw [e]
      exact inv_anti₀ (pow_pos hδ' _) (pow_le_pow_left₀ hδ'.le he _)
    rw [norm_mul, norm_mul]
    exact mul_le_mul (mul_le_mul (hCf _) (hCh _) (norm_nonneg _) ((norm_nonneg _).trans (hCf z.1)))
      hw (norm_nonneg _) (mul_nonneg ((norm_nonneg _).trans (hCf z.1))
        ((norm_nonneg _).trans (hCh z.2)))
  refine (integrableOn_iff_integrable_of_support_subset ?_).mp hIn
  intro z hz
  by_contra hn
  apply hz
  have h1 : z.1 ∉ tsupport f ∨ z.2 ∉ tsupport h := by
    by_contra hc
    push Not at hc
    exact hn ⟨hc.1, hc.2⟩
  rcases h1 with h1 | h1
  · simp [image_eq_zero_of_notMem_tsupport h1]
  · simp [image_eq_zero_of_notMem_tsupport h1]
def halfOpenCube (ℓ : ℝ) (c : Fin 4 → ℝ) : Set (Fin 4 → ℝ) :=
  Set.pi univ fun μ => Ioc (c μ - ℓ / 2) (c μ - ℓ / 2 + ℓ)
theorem measurableSet_halfOpenCube (ℓ : ℝ) (c : Fin 4 → ℝ) : MeasurableSet (halfOpenCube ℓ c) :=
  MeasurableSet.univ_pi fun _ => measurableSet_Ioc
variable {ℓ : ℝ}
theorem measurePreserving_torusProj [Fact (0 < ℓ)] (c : Fin 4 → ℝ) :
    MeasurePreserving (torusProj ℓ) (volume.restrict (halfOpenCube ℓ c)) volume := by
  have h := measurePreserving_pi
    (fun i : Fin 4 => (volume : Measure ℝ).restrict (Ioc (c i - ℓ / 2) (c i - ℓ / 2 + ℓ)))
    (fun _ : Fin 4 => (volume : Measure (AddCircle ℓ)))
    (fun i => AddCircle.measurePreserving_mk ℓ (c i - ℓ / 2))
  rw [← Measure.restrict_pi_pi] at h
  exact h
def cubeSection [Fact (0 < ℓ)] (c : Fin 4 → ℝ) (u : Torus4 ℓ) : Fin 4 → ℝ :=
  fun μ => (AddCircle.equivIoc ℓ (c μ - ℓ / 2) (u μ) : ℝ)
theorem measurable_cubeSection [Fact (0 < ℓ)] (c : Fin 4 → ℝ) :
    Measurable (cubeSection (ℓ := ℓ) c) :=
  measurable_pi_lambda _ fun μ => measurable_subtype_coe.comp
    ((AddCircle.measurableEquivIoc ℓ (c μ - ℓ / 2)).measurable.comp (measurable_pi_apply μ))
theorem cubeSection_mem [Fact (0 < ℓ)] (c : Fin 4 → ℝ) (u : Torus4 ℓ) :
    cubeSection c u ∈ halfOpenCube ℓ c :=
  fun μ _ => (AddCircle.equivIoc ℓ (c μ - ℓ / 2) (u μ)).2
theorem torusProj_cubeSection [Fact (0 < ℓ)] (c : Fin 4 → ℝ) (u : Torus4 ℓ) :
    torusProj ℓ (cubeSection c u) = u := by
  funext μ
  exact (AddCircle.equivIoc ℓ (c μ - ℓ / 2)).symm_apply_apply (u μ)
theorem cubeSection_torusProj [Fact (0 < ℓ)] {c x : Fin 4 → ℝ} (hx : x ∈ halfOpenCube ℓ c) :
    cubeSection c (torusProj ℓ x) = x := by
  funext μ
  show ((AddCircle.equivIoc ℓ (c μ - ℓ / 2) ((x μ : ℝ) : AddCircle ℓ)) : ℝ) = x μ
  rw [AddCircle.equivIoc_coe_eq (hx μ (mem_univ μ))]
theorem euclidNormVec_le_torusEuclidNorm (hℓ : 0 < ℓ) {v : Fin 4 → ℝ}
    (hv : ∀ μ, |v μ| ≤ ℓ / 2) : euclidNormVec v ≤ torusEuclidNorm (torusProj ℓ v) := by
  refine le_csInf ⟨_, v, rfl, rfl⟩ ?_
  rintro _ ⟨w, hw, rfl⟩
  have hw' : torusProj ℓ w = torusProj ℓ v := hw
  unfold euclidNormVec
  refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun μ _ => ?_)
  have h1 : ‖((v μ : ℝ) : AddCircle ℓ)‖ = |v μ| :=
    (AddCircle.norm_coe_eq_abs_iff ℓ hℓ.ne').mpr (by rw [abs_of_pos hℓ]; exact hv μ)
  have h2 : ((w μ : ℝ) : AddCircle ℓ) = (v μ : AddCircle ℓ) := congrFun hw' μ
  have h3 : |v μ| ≤ |w μ| := by
    rw [← h1, ← h2]
    exact addCircle_norm_coe_le_abs _
  exact sq_le_sq.mpr h3
theorem euclidNormVec_eq_of_torusProj_eq (hℓ : 0 < ℓ) {v w : Fin 4 → ℝ}
    (h : torusProj ℓ v = torusProj ℓ w)
    (hv : ∀ μ, |v μ| ≤ ℓ / 2) (hw : ∀ μ, |w μ| ≤ ℓ / 2) : euclidNormVec v = euclidNormVec w := by
  have h1 : ∀ μ, |v μ| = |w μ| := fun μ => by
    have e : ((v μ : ℝ) : AddCircle ℓ) = (w μ : AddCircle ℓ) := congrFun h μ
    rw [← (AddCircle.norm_coe_eq_abs_iff ℓ hℓ.ne').mpr (by rw [abs_of_pos hℓ]; exact hv μ),
      ← (AddCircle.norm_coe_eq_abs_iff ℓ hℓ.ne').mpr (by rw [abs_of_pos hℓ]; exact hw μ), e]
  unfold euclidNormVec
  congr 1
  exact Finset.sum_congr rfl fun μ _ => by rw [← sq_abs, h1 μ, sq_abs]
theorem abs_sub_le_of_mem_closedBallR4 {c x : Fin 4 → ℝ} {r : ℝ} (hx : x ∈ closedBallR4 c r)
    (μ : Fin 4) : |x μ - c μ| ≤ r :=
  (abs_apply_le_euclidNormVec (x - c) μ).trans hx
theorem closedBallR4_subset_halfOpenCube {c : Fin 4 → ℝ} {r : ℝ} (hℓ : 0 < ℓ) (hr : r ≤ ℓ / 4) :
    closedBallR4 c r ⊆ halfOpenCube ℓ c := by
  intro x hx μ _
  have h1 := abs_le.mp (abs_sub_le_of_mem_closedBallR4 hx μ)
  exact ⟨by linarith [h1.1], by linarith [h1.2]⟩
theorem mem_closedBallR4_of_ne_zero (hℓ : 0 < ℓ) {f : Torus4 ℓ → 𝕜} {c x : Fin 4 → ℝ} {r : ℝ}
    (hsub : tsupport f ⊆ closedBallTorus (torusProj ℓ c) r) (hx : x ∈ halfOpenCube ℓ c)
    (hne : f (torusProj ℓ x) ≠ 0) : x ∈ closedBallR4 c r := by
  have h1 : torusProj ℓ x ∈ closedBallTorus (torusProj ℓ c) r := hsub (subset_tsupport _ hne)
  have hb : ∀ μ, |(x - c) μ| ≤ ℓ / 2 := fun μ => by
    have h2 := hx μ (mem_univ μ)
    simp only [Pi.sub_apply]
    rw [abs_le]
    constructor <;> linarith [h2.1, h2.2]
  have h2 := euclidNormVec_le_torusEuclidNorm hℓ hb
  rw [torusProj_sub_vec] at h2
  exact h2.trans h1
theorem liftToBall_eq_of_mem_halfOpenCube (hℓ : 0 < ℓ) {f : Torus4 ℓ → 𝕜} {c x : Fin 4 → ℝ}
    {r : ℝ} (hsub : tsupport f ⊆ closedBallTorus (torusProj ℓ c) r)
    (hx : x ∈ halfOpenCube ℓ c) :
    liftToBall ℓ c r f x = f (torusProj ℓ x) := by
  by_cases hb : x ∈ closedBallR4 c r
  · simp [liftToBall, hb]
  · have h0 : f (torusProj ℓ x) = 0 := by
      by_contra hne
      exact hb (mem_closedBallR4_of_ne_zero hℓ hsub hx hne)
    simp [liftToBall, hb, h0]
def productIntegrand [Fact (0 < ℓ)] (f h : Torus4 ℓ → 𝕜) (c : Fin 4 → ℝ)
    (p : Torus4 ℓ × Torus4 ℓ) : 𝕜 :=
  f p.1 * h p.2 * ((euclidNormVec (cubeSection c p.1 - cubeSection c p.2) ^ (-8 : ℤ) : ℝ) : 𝕜)
theorem measurable_of_measurable_comp_torusProj [Fact (0 < ℓ)] {f : Torus4 ℓ → 𝕜}
    (hf : Measurable (f ∘ torusProj ℓ)) : Measurable f := by
  have e : f = (f ∘ torusProj ℓ) ∘ cubeSection 0 := by
    funext u
    simp [torusProj_cubeSection]
  rw [e]
  exact hf.comp (measurable_cubeSection 0)
theorem inverseEighthKernel_liftToBall_eq_integral [Fact (0 < ℓ)] {f h : Torus4 ℓ → 𝕜}
    (hfm : Measurable (f ∘ torusProj ℓ)) (hhm : Measurable (h ∘ torusProj ℓ)) {c : Fin 4 → ℝ}
    {r : ℝ} (hr : r ≤ ℓ / 4) (hf : tsupport f ⊆ closedBallTorus (torusProj ℓ c) r)
    (hh : tsupport h ⊆ closedBallTorus (torusProj ℓ c) r) :
    inverseEighthKernel (liftToBall ℓ c r f) (liftToBall ℓ c r h) =
      ∫ p, productIntegrand f h c p
        ∂((volume : Measure (Torus4 ℓ)).prod (volume : Measure (Torus4 ℓ))) := by
  have hℓ : 0 < ℓ := Fact.out
  have hmp := (measurePreserving_torusProj (ℓ := ℓ) c).prod
    (measurePreserving_torusProj (ℓ := ℓ) c)
  rw [Measure.prod_restrict] at hmp
  have hQ : MeasurableSet (halfOpenCube ℓ c ×ˢ halfOpenCube ℓ c) :=
    (measurableSet_halfOpenCube ℓ c).prod (measurableSet_halfOpenCube ℓ c)
  have hG : Measurable (productIntegrand f h c) := by
    have hl := measurable_cubeSection (ℓ := ℓ) c
    exact (((measurable_of_measurable_comp_torusProj hfm).comp measurable_fst).mul
      ((measurable_of_measurable_comp_torusProj hhm).comp measurable_snd)).mul
      ((measurable_inverseEighthWeight (𝕜 := 𝕜)).comp
        ((hl.comp measurable_fst).sub (hl.comp measurable_snd)))
  have hzero : ∀ z : (Fin 4 → ℝ) × (Fin 4 → ℝ), z ∉ halfOpenCube ℓ c ×ˢ halfOpenCube ℓ c →
      liftToBall ℓ c r f z.1 * liftToBall ℓ c r h z.2 *
        ((euclidNormVec (z.1 - z.2) ^ (-8 : ℤ) : ℝ) : 𝕜) = 0 := by
    intro z hz
    have h1 : z.1 ∉ halfOpenCube ℓ c ∨ z.2 ∉ halfOpenCube ℓ c := by
      by_contra hc
      push Not at hc
      exact hz ⟨hc.1, hc.2⟩
    rcases h1 with h1 | h1
    · have h2 : z.1 ∉ closedBallR4 c r := fun h3 =>
        h1 (closedBallR4_subset_halfOpenCube hℓ hr h3)
      simp [liftToBall, h2]
    · have h2 : z.2 ∉ closedBallR4 c r := fun h3 =>
        h1 (closedBallR4_subset_halfOpenCube hℓ hr h3)
      simp [liftToBall, h2]
  have heq : ∀ z ∈ halfOpenCube ℓ c ×ˢ halfOpenCube ℓ c,
      liftToBall ℓ c r f z.1 * liftToBall ℓ c r h z.2 *
        ((euclidNormVec (z.1 - z.2) ^ (-8 : ℤ) : ℝ) : 𝕜) =
      productIntegrand f h c (Prod.map (torusProj ℓ) (torusProj ℓ) z) := by
    intro z hz
    simp only [productIntegrand, Prod.map_fst, Prod.map_snd]
    rw [liftToBall_eq_of_mem_halfOpenCube hℓ hf hz.1, liftToBall_eq_of_mem_halfOpenCube hℓ hh hz.2,
      cubeSection_torusProj hz.1, cubeSection_torusProj hz.2]
  unfold inverseEighthKernel
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero,
    setIntegral_congr_fun hQ heq, ← hmp.map_eq,
    integral_map hmp.measurable.aemeasurable hG.aestronglyMeasurable]
  rfl
theorem productIntegrand_indep [Fact (0 < ℓ)] {f h : Torus4 ℓ → 𝕜} {c c' : Fin 4 → ℝ}
    {r r' : ℝ} (hr : r ≤ ℓ / 4) (hr' : r' ≤ ℓ / 4)
    (hf : tsupport f ⊆ closedBallTorus (torusProj ℓ c) r)
    (hh : tsupport h ⊆ closedBallTorus (torusProj ℓ c) r)
    (hf' : tsupport f ⊆ closedBallTorus (torusProj ℓ c') r')
    (hh' : tsupport h ⊆ closedBallTorus (torusProj ℓ c') r')
    (p : Torus4 ℓ × Torus4 ℓ) :
    productIntegrand f h c p = productIntegrand f h c' p := by
  have hℓ : 0 < ℓ := Fact.out
  obtain ⟨s, t⟩ := p
  unfold productIntegrand
  by_cases hs : f s = 0
  · simp [hs]
  by_cases ht : h t = 0
  · simp [ht]
  have key : ∀ {e : Fin 4 → ℝ} {ρ : ℝ}, ρ ≤ ℓ / 4 →
      tsupport f ⊆ closedBallTorus (torusProj ℓ e) ρ →
      tsupport h ⊆ closedBallTorus (torusProj ℓ e) ρ →
      ∀ μ, |(cubeSection e s - cubeSection e t) μ| ≤ ℓ / 2 := by
    intro e ρ hρ h1 h2 μ
    have hx := mem_closedBallR4_of_ne_zero hℓ h1 (cubeSection_mem e s)
      (by rwa [torusProj_cubeSection])
    have hy := mem_closedBallR4_of_ne_zero hℓ h2 (cubeSection_mem e t)
      (by rwa [torusProj_cubeSection])
    have h3 := abs_le.mp (abs_sub_le_of_mem_closedBallR4 hx μ)
    have h4 := abs_le.mp (abs_sub_le_of_mem_closedBallR4 hy μ)
    simp only [Pi.sub_apply]
    rw [abs_le]
    constructor <;> linarith [h3.1, h3.2, h4.1, h4.2]
  have hcov : torusProj ℓ (cubeSection c s - cubeSection c t) =
      torusProj ℓ (cubeSection c' s - cubeSection c' t) := by
    rw [torusProj_sub_vec, torusProj_sub_vec, torusProj_cubeSection, torusProj_cubeSection,
      torusProj_cubeSection, torusProj_cubeSection]
  rw [euclidNormVec_eq_of_torusProj_eq hℓ hcov (key hr hf hh) (key hr' hf' hh')]
theorem inverseEighthKernelTorus_eq {f h : Torus4 ℓ → 𝕜} {c : Fin 4 → ℝ} {r : ℝ}
    (hfm : Measurable (f ∘ torusProj ℓ)) (hhm : Measurable (h ∘ torusProj ℓ))
    (hk : IsKernelBallTorus f h c r) :
    inverseEighthKernelTorus f h = inverseEighthKernel (liftToBall ℓ c r f) (liftToBall ℓ c r h) := by
  obtain ⟨-, hr0, hr, hf, hh⟩ := id hk
  have : Fact (0 < ℓ) := ⟨by linarith⟩
  have H : ∃ q : (Fin 4 → ℝ) × ℝ, IsKernelBallTorus f h q.1 q.2 := ⟨(c, r), hk⟩
  obtain ⟨-, -, hr', hf', hh'⟩ := H.choose_spec
  rw [inverseEighthKernelTorus, dif_pos H, inverseEighthKernel_liftToBall_eq_integral hfm hhm hr' hf' hh',
    inverseEighthKernel_liftToBall_eq_integral hfm hhm hr hf hh]
  exact integral_congr_ae (Filter.Eventually.of_forall
    (productIntegrand_indep hr' hr hf' hh' hf hh))
end Kernels
end WellFormed
theorem objectsAreWellFormed : ObjectsAreWellFormed := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro L m j hL
    have := SeparatedSequences.BaseParameters.site_finite hL m j
    exact PeriodicLattice.ConjugationReality.finite_plaquette L m j
  · intro X E _ f hb
    obtain ⟨C, hC⟩ := hb
    have hbdd : BddAbove (range fun x => ‖f x‖) := ⟨C, by rintro _ ⟨x, rfl⟩; exact hC x⟩
    exact ⟨fun x => le_ciSup hbdd x, fun hne C' hC' => by
      have := hne
      exact ciSup_le hC'⟩
  · intro X E _ d f h0 hf
    exact WellFormed.bestLipschitzConstant_properties h0 hf
  · intro L m E _ f hL hf
    have hside : 0 < PeriodicLattice.torusSide L m := by
      have : (0 : ℝ) < L := by exact_mod_cast hL
      unfold PeriodicLattice.torusSide
      positivity
    exact WellFormed.isBoundedFun_of_isLipschitzFor hside hf
  · intro E _ _ f μ x hf
    have hd : Differentiable ℝ f := ContDiff.differentiable hf (by norm_num)
    exact (hd _).comp (0 : ℝ) (by fun_prop)
  · intro E _ _ ℓ f μ x hf
    have hd : Differentiable ℝ (f ∘ torusProj ℓ) := ContDiff.differentiable hf (by norm_num)
    have e : (fun t : ℝ => f (x + torusProj ℓ (t • Pi.single μ (1 : ℝ)))) =
        fun t : ℝ => (f ∘ torusProj ℓ) (liftPoint x + t • Pi.single μ (1 : ℝ)) := by
      funext t
      simp only [Function.comp_apply]
      rw [WellFormed.torusProj_add_vec, torusProj_liftPoint]
    rw [e]
    exact (hd _).comp (0 : ℝ) (by fun_prop)
  · intro E _ _ ℓ A f hℓ h
    exact WellFormed.periodize_properties hℓ h
  · intro 𝕜 _ f h hp
    exact WellFormed.integrable_inverseEighthIntegrand hp
  · intro 𝕜 _ ℓ f h c r _ _ hfm hhm hk
    exact WellFormed.inverseEighthKernelTorus_eq hfm hhm hk
end YangMills.Construction.TestFunctions
