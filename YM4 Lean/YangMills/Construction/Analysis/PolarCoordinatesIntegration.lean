import YangMills.Construction.Analysis.PolarCoordinatesLowDim
import Mathlib
open MeasureTheory Metric Set
open scoped ENNReal
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Analysis.PolarCoordinates
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
private theorem lintegral_radialPowDensity (k : ℕ) (g : ℝ → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻ r : Ioi (0 : ℝ), g r ∂Measure.volumeIoiPow k =
      ∫⁻ r in Ioi (0 : ℝ), g r * ENNReal.ofReal (r ^ k) := by
  have hdens : Measurable fun r : Ioi (0 : ℝ) => ENNReal.ofReal ((r : ℝ) ^ k) := by fun_prop
  have hgsub : Measurable fun r : Ioi (0 : ℝ) => g r := hg.comp measurable_subtype_coe
  rw [Measure.volumeIoiPow, lintegral_withDensity_eq_lintegral_mul _ hdens hgsub,
    ← lintegral_subtype_comap measurableSet_Ioi (fun r => g r * ENNReal.ofReal (r ^ k))]
  exact lintegral_congr fun r => mul_comm _ _
private theorem integrable_radialPowDensity_iff (k : ℕ) (g : ℝ → ℝ) :
    Integrable (fun r : Ioi (0 : ℝ) => g r) (Measure.volumeIoiPow k) ↔
      IntegrableOn (fun r : ℝ => g r * r ^ k) (Ioi 0) := by
  rw [integrableOn_iff_comap_subtypeVal measurableSet_Ioi, Measure.volumeIoiPow,
    integrable_withDensity_iff_integrable_smul' (by fun_prop) (by simp)]
  refine integrable_congr (.of_forall ?_)
  rintro ⟨r, hr⟩
  have hrpos : (0 : ℝ) < r := hr
  simp [ENNReal.toReal_ofReal, pow_nonneg hrpos.le, mul_comm]
private theorem integral_radialPowDensity (k : ℕ) (g : ℝ → ℝ) :
    ∫ r : Ioi (0 : ℝ), g r ∂Measure.volumeIoiPow k = ∫ r in Ioi (0 : ℝ), g r * r ^ k := by
  simp only [Measure.volumeIoiPow, ENNReal.ofReal]
  rw [integral_withDensity_eq_integral_smul (by fun_prop),
    ← integral_subtype_comap measurableSet_Ioi (fun r => g r * r ^ k)]
  refine integral_congr_ae (.of_forall ?_)
  rintro ⟨r, hr⟩
  have hrpos : (0 : ℝ) < r := hr
  simp [NNReal.smul_def, Real.coe_toNNReal _ (pow_nonneg hrpos.le k), mul_comm]
omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem radius_smul_direction (x : ({0}ᶜ : Set E)) :
    ((homeomorphUnitSphereProd E x).2 : ℝ) • ((homeomorphUnitSphereProd E x).1 : E) = x := by
  have hx : ‖(x : E)‖ ≠ 0 := norm_ne_zero_iff.mpr x.2
  simp [smul_smul, hx]
private abbrev polarPullback {F : Type} (f : E → F) (p : sphere (0 : E) 1 × Ioi (0 : ℝ)) : F :=
  f ((p.2 : ℝ) • (p.1 : E))
omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem polarPullback_comp_homeomorph {F : Type} (f : E → F) :
    polarPullback f ∘ homeomorphUnitSphereProd E = f ∘ ((↑) : ({0}ᶜ : Set E) → E) := by
  funext x
  simp only [Function.comp, polarPullback, radius_smul_direction]
private theorem lintegralFormula_finrank [Nontrivial E] :
    LintegralFormula E (Module.finrank ℝ E) := by
  intro f hf
  have hmp := (volume : Measure E).measurePreserving_homeomorphUnitSphereProd
  have hmeas : Measurable (polarPullback f) := by
    have : Measurable fun p : sphere (0 : E) 1 × Ioi (0 : ℝ) => (p.2 : ℝ) • (p.1 : E) := by
      fun_prop
    exact hf.comp this
  calc ∫⁻ x, f x
      = ∫⁻ x in ({0}ᶜ : Set E), f x := by rw [restrict_compl_singleton]
    _ = ∫⁻ x : ({0}ᶜ : Set E), f x ∂((volume : Measure E).comap (↑)) :=
        (lintegral_subtype_comap (measurableSet_singleton _).compl f).symm
    _ = ∫⁻ x : ({0}ᶜ : Set E), polarPullback f (homeomorphUnitSphereProd E x)
          ∂((volume : Measure E).comap (↑)) :=
        lintegral_congr fun x => (congrFun (polarPullback_comp_homeomorph f) x).symm
    _ = ∫⁻ p, polarPullback f p
          ∂(sphereMeasure E).prod (Measure.volumeIoiPow (Module.finrank ℝ E - 1)) :=
        hmp.lintegral_comp_emb (Homeomorph.measurableEmbedding _) _
    _ = ∫⁻ n : sphere (0 : E) 1, ∫⁻ r : Ioi (0 : ℝ), polarPullback f (n, r)
          ∂Measure.volumeIoiPow (Module.finrank ℝ E - 1) ∂sphereMeasure E :=
        lintegral_prod _ hmeas.aemeasurable
    _ = _ := by
        refine lintegral_congr fun n => ?_
        exact lintegral_radialPowDensity _ (fun r => f (r • (n : E))) (by fun_prop)
private theorem integralFormula_finrank [Nontrivial E] :
    IntegralFormula E (Module.finrank ℝ E) := by
  intro f hf
  have hmp := (volume : Measure E).measurePreserving_homeomorphUnitSphereProd
  have hcomap : Integrable (f ∘ ((↑) : ({0}ᶜ : Set E) → E)) ((volume : Measure E).comap (↑)) := by
    rw [← integrableOn_iff_comap_subtypeVal (measurableSet_singleton _).compl]
    exact hf.integrableOn
  have hprod : Integrable (polarPullback f)
      ((sphereMeasure E).prod (Measure.volumeIoiPow (Module.finrank ℝ E - 1))) := by
    rw [← hmp.integrable_comp_emb (Homeomorph.measurableEmbedding _),
      polarPullback_comp_homeomorph]
    exact hcomap
  have hinner : ∀ n : sphere (0 : E) 1,
      ∫ r : Ioi (0 : ℝ), polarPullback f (n, r) ∂Measure.volumeIoiPow (Module.finrank ℝ E - 1) =
        ∫ r in Ioi (0 : ℝ), f (r • (n : E)) * r ^ (Module.finrank ℝ E - 1) := fun n =>
    integral_radialPowDensity _ (fun r => f (r • (n : E)))
  refine ⟨?_, ?_, ?_⟩
  · filter_upwards [hprod.prod_right_ae] with n hn
    exact (integrable_radialPowDensity_iff _ (fun r => f (r • (n : E)))).mp hn
  · have := hprod.integral_prod_left
    simp only [hinner] at this
    exact this
  · calc ∫ x, f x
        = ∫ x in ({0}ᶜ : Set E), f x := by rw [restrict_compl_singleton]
      _ = ∫ x : ({0}ᶜ : Set E), f x ∂((volume : Measure E).comap (↑)) :=
          (integral_subtype_comap (measurableSet_singleton _).compl f).symm
      _ = ∫ x : ({0}ᶜ : Set E), polarPullback f (homeomorphUnitSphereProd E x)
            ∂((volume : Measure E).comap (↑)) :=
          integral_congr_ae (.of_forall fun x => (congrFun (polarPullback_comp_homeomorph f) x).symm)
      _ = ∫ p, polarPullback f p
            ∂(sphereMeasure E).prod (Measure.volumeIoiPow (Module.finrank ℝ E - 1)) :=
          hmp.integral_comp (Homeomorph.measurableEmbedding _) _
      _ = ∫ n : sphere (0 : E) 1, ∫ r : Ioi (0 : ℝ), polarPullback f (n, r)
            ∂Measure.volumeIoiPow (Module.finrank ℝ E - 1) ∂sphereMeasure E :=
          integral_prod _ hprod
      _ = _ := by simp only [hinner]
omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem norm_smul_unitSphere (n : sphere (0 : E) 1) {r : ℝ} (hr : r ∈ Ioi (0 : ℝ)) :
    ‖r • (n : E)‖ = r := by
  have hrpos : (0 : ℝ) < r := hr
  simp [norm_smul, abs_of_pos hrpos]
private theorem radialLintegralFormula_of (d : ℕ) (A : ℝ) (hl : LintegralFormula E d)
    (hA : sphereMeasure E univ = ENNReal.ofReal A) : RadialLintegralFormula E d A := by
  intro φ hφ
  rw [hl (fun x => φ ‖x‖) (by fun_prop)]
  have hinner : ∀ n : sphere (0 : E) 1,
      ∫⁻ r in Ioi (0 : ℝ), φ ‖r • (n : E)‖ * ENNReal.ofReal (r ^ (d - 1)) =
        ∫⁻ r in Ioi (0 : ℝ), φ r * ENNReal.ofReal (r ^ (d - 1)) := fun n =>
    setLIntegral_congr_fun measurableSet_Ioi fun r hr => by rw [norm_smul_unitSphere n hr]
  simp only [hinner]
  rw [lintegral_const, hA, mul_comm]
private theorem radialIntegralFormula_of (d : ℕ) (A : ℝ) (hi : IntegralFormula E d)
    (hApos : 0 < A) (hA : sphereMeasure E univ = ENNReal.ofReal A) :
    RadialIntegralFormula E d A := by
  intro φ hφ
  obtain ⟨hae, -, heq⟩ := hi _ hφ
  have hne : sphereMeasure E ≠ 0 := by
    intro hzero
    rw [hzero] at hA
    simp only [Measure.coe_zero, Pi.zero_apply] at hA
    exact (ENNReal.ofReal_pos.mpr hApos).ne hA
  have : (ae (sphereMeasure E)).NeBot := ae_neBot.mpr hne
  obtain ⟨n, hn⟩ := hae.exists
  refine ⟨hn.congr_fun (fun r hr => by simp only [norm_smul_unitSphere n hr]) measurableSet_Ioi, ?_⟩
  have hinner : ∀ n : sphere (0 : E) 1,
      ∫ r in Ioi (0 : ℝ), φ ‖r • (n : E)‖ * r ^ (d - 1) =
        ∫ r in Ioi (0 : ℝ), φ r * r ^ (d - 1) := fun n =>
    setIntegral_congr_fun measurableSet_Ioi fun r hr => by
      simp only [norm_smul_unitSphere n hr]
  rw [heq]
  simp only [hinner]
  rw [integral_const, smul_eq_mul, measureReal_def, hA, ENNReal.toReal_ofReal hApos.le]
private theorem polarFormulas_of_sphereMeasure [Nontrivial E] (d : ℕ) (A : ℝ)
    (hd : Module.finrank ℝ E = d) (hApos : 0 < A)
    (hA : sphereMeasure E univ = ENNReal.ofReal A) : PolarFormulas E d A := by
  subst hd
  exact ⟨lintegralFormula_finrank, integralFormula_finrank, hA,
    radialLintegralFormula_of _ _ lintegralFormula_finrank hA,
    radialIntegralFormula_of _ _ integralFormula_finrank hApos hA⟩
private theorem sphereMeasure_univ_dim_three (hd : Module.finrank ℝ E = 3) :
    sphereMeasure E univ = ENNReal.ofReal (4 * Real.pi) := by
  have : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) (by omega)
  show (volume : Measure E).toSphere univ = _
  rw [Measure.toSphere_apply_univ,
    InnerProductSpace.volume_ball_of_dim_odd (k := 1) (by omega) (0 : E) 1, hd,
    ENNReal.ofReal_one, one_pow, one_mul, ← ENNReal.ofReal_natCast,
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  norm_num [Nat.doubleFactorial]
  ring
private theorem sphereMeasure_univ_dim_four (hd : Module.finrank ℝ E = 4) :
    sphereMeasure E univ = ENNReal.ofReal (2 * Real.pi ^ 2) := by
  have : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) (by omega)
  show (volume : Measure E).toSphere univ = _
  rw [Measure.toSphere_apply_univ,
    InnerProductSpace.volume_ball_of_dim_even (k := 2) (by omega) (0 : E) 1, hd,
    ENNReal.ofReal_one, one_pow, one_mul, ← ENNReal.ofReal_natCast,
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  norm_num [Nat.factorial]
  ring
theorem polarCoordinatesDimThreeFour_holds : PolarCoordinatesDimThreeFour := by
  intro E _ _ _ _ _
  refine ⟨fun hd => ?_, fun hd => ?_⟩
  · have : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) (by omega)
    exact polarFormulas_of_sphereMeasure 3 _ hd (by positivity) (sphereMeasure_univ_dim_three hd)
  · have : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) (by omega)
    exact polarFormulas_of_sphereMeasure 4 _ hd (by positivity) (sphereMeasure_univ_dim_four hd)
end YangMills.Construction.Analysis.PolarCoordinates
