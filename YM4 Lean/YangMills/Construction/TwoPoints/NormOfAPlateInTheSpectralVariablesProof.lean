import YangMills.Construction.TwoPoints.ElementaryFactsOfMirrorsAndPlates
import YangMills.Construction.TwoPoints.GrowthOfTheAxisDecayFunctionAtTheOriginProof
import YangMills.Construction.TwoPoints.NormOfAPlateInTheSpectralVariables
import YangMills.Construction.TwoPoints.PropertiesOfThePlaneKernel
import Mathlib
set_option autoImplicit false
open MeasureTheory Filter Set
open scoped NNReal ENNReal ComplexConjugate
noncomputable section
namespace YangMills.Construction.TwoPoints
open InfiniteLattice (AmbientSpace)
open PeriodicLattice (coordVec)
namespace PlateNormViaSpectralMeasure
abbrev planeVolume : Measure (ℝ × ℝ) := (volume : Measure ℝ).prod (volume : Measure ℝ)
section Fubini
variable {P : Type*}
def expWave (E q : P → ℝ) (x : ℝ × ℝ) (p : P) : ℂ :=
  Complex.exp (((-x.1 * E p : ℝ) : ℂ) + Complex.I * ((x.2 * q p : ℝ) : ℂ))
theorem norm_expWave (E q : P → ℝ) (x : ℝ × ℝ) (p : P) :
    ‖expWave E q x p‖ = Real.exp (-x.1 * E p) := by
  rw [expWave, Complex.norm_exp]
  simp
theorem conj_expWave_mul_expWave (E q : P → ℝ) (x y : ℝ × ℝ) (p : P) :
    conj (expWave E q x p) * expWave E q y p = expWave E q (x.1 + y.1, y.2 - x.2) p := by
  simp only [expWave]
  rw [← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring
theorem continuous_expWave (E q : P → ℝ) (p : P) :
    Continuous fun x : ℝ × ℝ => expWave E q x p := by
  unfold expWave
  fun_prop
variable [MeasurableSpace P]
theorem measurable_expWave {E q : P → ℝ} (hE : Measurable E) (hq : Measurable q) :
    Measurable fun y : (ℝ × ℝ) × P => expWave E q y.1 y.2 := by
  unfold expWave
  fun_prop
variable {ρ : Measure P} {E q : P → ℝ} {a : ℝ × ℝ → ℂ} {c : ℝ}
def wavePairProduct (E q : P → ℝ) (a : ℝ × ℝ → ℂ) (z : (ℝ × ℝ) × (ℝ × ℝ)) (p : P) : ℂ :=
  conj (a z.1 * expWave E q z.1 p) * (a z.2 * expWave E q z.2 p)
omit [MeasurableSpace P] in
theorem norm_mul_expWave_le (hE0 : ∀ p, 0 ≤ E p) (hpos : ∀ x, a x ≠ 0 → c ≤ x.1)
    (x : ℝ × ℝ) (p : P) :
    ‖a x * expWave E q x p‖ ≤ ‖a x‖ * Real.exp (-c * E p) := by
  rw [norm_mul, norm_expWave]
  by_cases h : a x = 0
  · simp [h]
  · refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (norm_nonneg _)
    nlinarith [hpos x h, hE0 p]
theorem integrable_wavePairProduct (hE : Measurable E) (hq : Measurable q) (hE0 : ∀ p, 0 ≤ E p)
    (ha : Continuous a) (hc : HasCompactSupport a) (hpos : ∀ x, a x ≠ 0 → c ≤ x.1)
    (hfin : Integrable (fun p => Real.exp (-(2 * c) * E p)) ρ) :
    Integrable (Function.uncurry (wavePairProduct E q a))
      ((planeVolume.prod planeVolume).prod ρ) := by
  have hint : Integrable (fun x => ‖a x‖) planeVolume :=
    ha.norm.integrable_of_hasCompactSupport hc.norm
  have hb := (hint.mul_prod hint).mul_prod hfin
  refine hb.mono' ?_ (ae_of_all _ fun y => ?_)
  · have hw := measurable_expWave hE hq
    have ham := ha.measurable
    have h1 : Measurable fun y : ((ℝ × ℝ) × (ℝ × ℝ)) × P => a y.1.1 * expWave E q y.1.1 y.2 :=
      (ham.comp (measurable_fst.comp measurable_fst)).mul
        (hw.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd))
    have h2 : Measurable fun y : ((ℝ × ℝ) × (ℝ × ℝ)) × P => a y.1.2 * expWave E q y.1.2 y.2 :=
      (ham.comp (measurable_snd.comp measurable_fst)).mul
        (hw.comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd))
    exact ((Complex.continuous_conj.measurable.comp h1).mul h2).aestronglyMeasurable
  · obtain ⟨⟨x, x'⟩, p⟩ := y
    simp only [Function.uncurry, wavePairProduct, norm_mul, RCLike.norm_conj]
    have h1 := norm_mul_expWave_le (q := q) hE0 hpos x p
    have h2 := norm_mul_expWave_le (q := q) hE0 hpos x' p
    rw [norm_mul] at h1 h2
    have he : Real.exp (-(2 * c) * E p) = Real.exp (-c * E p) * Real.exp (-c * E p) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [he]
    calc ‖a x‖ * ‖expWave E q x p‖ * (‖a x'‖ * ‖expWave E q x' p‖)
        ≤ (‖a x‖ * Real.exp (-c * E p)) * (‖a x'‖ * Real.exp (-c * E p)) :=
          mul_le_mul h1 h2 (by positivity) (by positivity)
      _ = _ := by ring
theorem conj_mul_mul_kernel_eq_integral {K : ℝ → ℝ → ℂ} (hc0 : 0 < c)
    (hpos : ∀ x, a x ≠ 0 → c ≤ x.1)
    (hK : ∀ t : ℝ, 0 < t → ∀ s : ℝ, K t s = ∫ p, expWave E q (t, s) p ∂ρ) (x y : ℝ × ℝ) :
    conj (a x) * a y * K (x.1 + y.1) (y.2 - x.2) = ∫ p, wavePairProduct E q a (x, y) p ∂ρ := by
  by_cases hx : a x = 0
  · simp [wavePairProduct, hx]
  by_cases hy : a y = 0
  · simp [wavePairProduct, hy]
  have ht : 0 < x.1 + y.1 := by linarith [hpos x hx, hpos y hy]
  rw [hK _ ht, ← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun p => ?_)
  simp only [wavePairProduct, map_mul]
  rw [← conj_expWave_mul_expWave]
  ring
omit [MeasurableSpace P] in
theorem integral_mul_expWave_eq_iterated (ha : Continuous a) (hc : HasCompactSupport a) (p : P) :
    ∫ x, a x * expWave E q x p ∂planeVolume =
      ∫ t : ℝ, ∫ s : ℝ, a (t, s) * expWave E q (t, s) p := by
  refine integral_prod _ ?_
  exact (ha.mul (continuous_expWave E q p)).integrable_of_hasCompactSupport hc.mul_right
theorem integrable_and_fourfold_integral_eq [SFinite ρ] {K : ℝ → ℝ → ℂ} (hE : Measurable E)
    (hq : Measurable q) (hE0 : ∀ p, 0 ≤ E p) (ha : Continuous a) (hc : HasCompactSupport a)
    (hc0 : 0 < c) (hpos : ∀ x, a x ≠ 0 → c ≤ x.1)
    (hfin : Integrable (fun p => Real.exp (-(2 * c) * E p)) ρ)
    (hK : ∀ t : ℝ, 0 < t → ∀ s : ℝ, K t s = ∫ p, expWave E q (t, s) p ∂ρ) :
    Integrable (fun p => ‖∫ t : ℝ, ∫ s : ℝ, a (t, s) * expWave E q (t, s) p‖ ^ 2) ρ ∧
      (∫ s₂ : ℝ, ∫ t₂ : ℝ, ∫ s₁ : ℝ, ∫ t₁ : ℝ,
        conj (a (t₁, s₁)) * a (t₂, s₂) * K (t₁ + t₂) (s₂ - s₁)) =
        ((∫ p, ‖∫ t : ℝ, ∫ s : ℝ, a (t, s) * expWave E q (t, s) p‖ ^ 2 ∂ρ : ℝ) : ℂ) := by
  have hG := integrable_wavePairProduct (ρ := ρ) hE hq hE0 ha hc hpos hfin
  have hsplit : ∀ p, ∫ z, wavePairProduct E q a z p ∂(planeVolume.prod planeVolume) =
      ((‖∫ t : ℝ, ∫ s : ℝ, a (t, s) * expWave E q (t, s) p‖ ^ 2 : ℝ) : ℂ) := by
    intro p
    simp only [wavePairProduct]
    rw [integral_prod_mul (fun x => conj (a x * expWave E q x p))
        (fun x => a x * expWave E q x p),
      integral_conj, integral_mul_expWave_eq_iterated ha hc, Complex.conj_mul']
    push_cast
    rfl
  have hintP : Integrable
      (fun p => ∫ z, wavePairProduct E q a z p ∂(planeVolume.prod planeVolume)) ρ :=
    hG.integral_prod_right
  have hint : Integrable
      (fun p => ‖∫ t : ℝ, ∫ s : ℝ, a (t, s) * expWave E q (t, s) p‖ ^ 2) ρ := by
    have := hintP.norm
    refine this.congr (ae_of_all _ fun p => ?_)
    simp only [hsplit]
    rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  refine ⟨hint, ?_⟩
  have hH : Integrable (fun z => ∫ p, wavePairProduct E q a z p ∂ρ)
      (planeVolume.prod planeVolume) :=
    hG.integral_prod_left
  have hinner : ∀ᵐ y ∂planeVolume,
      ∫ x, (∫ p, wavePairProduct E q a (x, y) p ∂ρ) ∂planeVolume =
        ∫ s₁ : ℝ, ∫ t₁ : ℝ, ∫ p, wavePairProduct E q a ((t₁, s₁), y) p ∂ρ := by
    filter_upwards [hH.prod_left_ae] with y hy
    exact integral_prod_symm _ hy
  have hT : Integrable (fun y : ℝ × ℝ => ∫ s₁ : ℝ, ∫ t₁ : ℝ,
      ∫ p, wavePairProduct E q a ((t₁, s₁), y) p ∂ρ) planeVolume :=
    (hH.swap.integral_prod_left).congr hinner
  have hmain : (∫ s₂ : ℝ, ∫ t₂ : ℝ, ∫ s₁ : ℝ, ∫ t₁ : ℝ,
      ∫ p, wavePairProduct E q a ((t₁, s₁), (t₂, s₂)) p ∂ρ) =
      ∫ z, ∫ p, wavePairProduct E q a z p ∂ρ ∂(planeVolume.prod planeVolume) := by
    rw [integral_prod_symm _ hH, ← integral_prod_symm _ hT]
    exact (integral_congr_ae hinner).symm
  calc (∫ s₂ : ℝ, ∫ t₂ : ℝ, ∫ s₁ : ℝ, ∫ t₁ : ℝ,
        conj (a (t₁, s₁)) * a (t₂, s₂) * K (t₁ + t₂) (s₂ - s₁))
      = ∫ s₂ : ℝ, ∫ t₂ : ℝ, ∫ s₁ : ℝ, ∫ t₁ : ℝ,
          ∫ p, wavePairProduct E q a ((t₁, s₁), (t₂, s₂)) p ∂ρ := by
        simp only [fun t₁ s₁ t₂ s₂ => conj_mul_mul_kernel_eq_integral (ρ := ρ) (q := q) (E := E)
          hc0 hpos hK (t₁, s₁) (t₂, s₂)]
    _ = ∫ z, ∫ p, wavePairProduct E q a z p ∂ρ ∂(planeVolume.prod planeVolume) := hmain
    _ = ∫ p, ∫ z, wavePairProduct E q a z p ∂(planeVolume.prod planeVolume) ∂ρ :=
        integral_integral_swap hG
    _ = ∫ p, ((‖∫ t : ℝ, ∫ s : ℝ, a (t, s) * expWave E q (t, s) p‖ ^ 2 : ℝ) : ℂ) ∂ρ :=
        integral_congr_ae (ae_of_all _ hsplit)
    _ = _ := integral_ofReal
end Fubini
section Frame
def normalFrame (m : AmbientSpace) (x : ℝ × ℝ) : Fin 2 → ℝ :=
  planeCoords (x.1 • m + x.2 • planePerp m)
theorem normalFrame_zero (m : AmbientSpace) (x : ℝ × ℝ) :
    normalFrame m x 0 = x.1 * m 3 - x.2 * m 0 := by
  simp [normalFrame, planeCoords, planePerp, coordVec, PeriodicLattice.coordVec]
  ring
theorem normalFrame_one (m : AmbientSpace) (x : ℝ × ℝ) :
    normalFrame m x 1 = x.1 * m 0 + x.2 * m 3 := by
  simp [normalFrame, planeCoords, planePerp, coordVec, PeriodicLattice.coordVec]
theorem continuous_normalFrame (m : AmbientSpace) : Continuous (normalFrame m) := by
  refine continuous_pi fun i => ?_
  fin_cases i
  · simp only [Fin.zero_eta, normalFrame_zero]
    fun_prop
  · simp only [Fin.mk_one, normalFrame_one]
    fun_prop
def normalFrameInv (m : AmbientSpace) (y : Fin 2 → ℝ) : ℝ × ℝ :=
  (m 3 * y 0 + m 0 * y 1, -(m 0) * y 0 + m 3 * y 1)
theorem continuous_normalFrameInv (m : AmbientSpace) : Continuous (normalFrameInv m) := by
  unfold normalFrameInv
  fun_prop
theorem normalFrameInv_normalFrame {m : AmbientSpace} (hm : m 3 ^ 2 + m 0 ^ 2 = 1)
    (x : ℝ × ℝ) : normalFrameInv m (normalFrame m x) = x := by
  obtain ⟨t, s⟩ := x
  simp only [normalFrameInv, normalFrame_zero, normalFrame_one]
  refine Prod.ext ?_ ?_
  · change m 3 * (t * m 3 - s * m 0) + m 0 * (t * m 0 + s * m 3) = t
    linear_combination t * hm
  · change -(m 0) * (t * m 3 - s * m 0) + m 3 * (t * m 0 + s * m 3) = s
    linear_combination s * hm
theorem euclidDot_normalFrame {m : AmbientSpace} (hm : m 3 ^ 2 + m 0 ^ 2 = 1) (x : ℝ × ℝ) :
    euclidDot (planeCoords m) (normalFrame m x) = x.1 := by
  simp only [euclidDot, Fin.sum_univ_two, normalFrame_zero, normalFrame_one]
  simp only [planeCoords, Matrix.cons_val_zero, Matrix.cons_val_one]
  linear_combination x.1 * hm
theorem sq_add_sq_of_mem_planeReflectionNormals (h : PlaneNormalsEight) {m : AmbientSpace}
    (hm : m ∈ planeReflectionNormals) : m 3 ^ 2 + m 0 ^ 2 = 1 := by
  have h1 := h.1
  rw [h1] at hm
  obtain ⟨j, rfl⟩ := hm
  simp [planeUnit, coordVec, PeriodicLattice.coordVec]
theorem exists_pos_le_euclidDot {m : AmbientSpace} {K : Set (Fin 2 → ℝ)} (hK : IsCompact K)
    (hsub : K ⊆ {y | 0 < euclidDot (planeCoords m) y}) :
    ∃ c : ℝ, 0 < c ∧ ∀ y ∈ K, c ≤ euclidDot (planeCoords m) y := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · exact ⟨1, one_pos, by simp⟩
  have hcont : ContinuousOn (euclidDot (planeCoords m)) K := by
    apply Continuous.continuousOn
    unfold euclidDot
    fun_prop
  obtain ⟨y₀, hy₀, hmin⟩ := hK.exists_isMinOn hne hcont
  exact ⟨_, hsub hy₀, fun y hy => hmin hy⟩
end Frame
section Measure
variable {S : (AmbientSpace → ℂ) → (AmbientSpace → ℂ) → ℝ} {φ : (Fin 2 → ℝ) → ℂ}
  {m : AmbientSpace} {ρ : Measure SpectralCalculus.SpectralPlane}
theorem measurable_energyDecay (t : ℝ) : Measurable (energyDecay t) := by apply _root_.YangMills.Construction.TwoPoints.AxisDecayGrowthAtZero.measurable_energyDecay <;> assumption
theorem energyDecay_nonneg (t : ℝ) (p : SpectralCalculus.SpectralPlane) :
    0 ≤ energyDecay t p :=
  (Real.exp_pos _).le
theorem integrable_energyDecay (hρ : IsAveragedKernelSpectralMeasure S φ m ρ) {t : ℝ}
    (ht : 0 < t) : Integrable (energyDecay t) ρ := by
  refine ⟨(measurable_energyDecay t).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall (energyDecay_nonneg t))]
  exact hρ.lintegral_decay_lt_top ⟨t, ht.le⟩ (by exact_mod_cast ht)
theorem sigmaFinite_of_isAveragedKernelSpectralMeasure
    (hρ : IsAveragedKernelSpectralMeasure S φ m ρ) : SigmaFinite ρ := by
  have hfin : IsFiniteMeasure (ρ.withDensity fun p => ENNReal.ofReal (energyDecay 1 p)) :=
    isFiniteMeasure_withDensity (hρ.lintegral_decay_lt_top 1 one_pos).ne
  have hm₁ : Measurable fun p : SpectralCalculus.SpectralPlane =>
      ENNReal.ofReal (energyDecay 1 p) :=
    (measurable_energyDecay 1).ennreal_ofReal
  have hm₂ : Measurable fun p : SpectralCalculus.SpectralPlane =>
      ENNReal.ofReal (energyDecay (-1) p) :=
    (measurable_energyDecay (-1)).ennreal_ofReal
  have hone : (fun p : SpectralCalculus.SpectralPlane => ENNReal.ofReal (energyDecay 1 p)) *
      (fun p => ENNReal.ofReal (energyDecay (-1) p)) = 1 := by
    funext p
    simp only [Pi.mul_apply, Pi.one_apply]
    rw [← ENNReal.ofReal_mul (energyDecay_nonneg _ _), energyDecay, energyDecay,
      ← Real.exp_add]
    simp
  have hback : ρ = (ρ.withDensity fun p => ENNReal.ofReal (energyDecay 1 p)).withDensity
      fun p => ENNReal.ofReal (energyDecay (-1) p) := by
    rw [← withDensity_mul _ hm₁ hm₂, hone, withDensity_one]
  rw [hback]
  exact SigmaFinite.withDensity_ofReal _
end Measure
theorem holds (hElem : ReflectionsPlaneFacts.Statement)
    (hKernel : AveragedKernelProperties.Statement)
    (hSpace : ReflectedSpaceAndSlides.Statement)
    (hCompletion : SpectralCalculus.FormCompletionAndBoundedExtension) : Statement := by
  intro St S φ hF hP hφ m hm ρ hρ α hα h
  obtain ⟨-, -, -, h8, -, -, -, -⟩ := hElem
  have hunit := sq_add_sq_of_mem_planeReflectionNormals h8 hm
  have hs : SigmaFinite ρ := sigmaFinite_of_isAveragedKernelSpectralMeasure hρ
  obtain ⟨hα1, hαc, hαO⟩ := hα
  obtain ⟨c, hc0, hfloor⟩ := exists_pos_le_euclidDot (m := m) hαc hαO
  set a : ℝ × ℝ → ℂ := fun x => α (normalFrame m x) with ha_def
  have hαcont : Continuous α := hα1.continuous
  have ha : Continuous a := hαcont.comp (continuous_normalFrame m)
  have hmem : ∀ x, a x ≠ 0 → normalFrame m x ∈ tsupport α :=
    fun x hx => subset_tsupport _ (Function.mem_support.mpr hx)
  have hcs : HasCompactSupport a := by
    refine HasCompactSupport.intro (hαc.image (continuous_normalFrameInv m)) fun x hx => ?_
    by_contra h0
    exact hx ⟨_, hmem x h0, normalFrameInv_normalFrame hunit x⟩
  have hpos : ∀ x, a x ≠ 0 → c ≤ x.1 := fun x hx => by
    have := hfloor _ (hmem x hx)
    rwa [euclidDot_normalFrame hunit] at this
  have hfin : Integrable
      (fun p : SpectralCalculus.SpectralPlane => Real.exp (-(2 * c) * (p.1 : ℝ))) ρ :=
    integrable_energyDecay hρ (by positivity : 0 < 2 * c)
  have hK : ∀ t : ℝ, 0 < t → ∀ s : ℝ,
      transverseAveragedKernel S φ (normalFrame m (t, s)) =
        ∫ p, expWave (fun p : SpectralCalculus.SpectralPlane => (p.1 : ℝ)) (fun p => p.2)
          (t, s) p ∂ρ :=
    fun t ht s => hρ.kernel_eq_integral ⟨t, ht.le⟩ (by exact_mod_cast ht) s
  obtain ⟨hint, hfour⟩ := integrable_and_fourfold_integral_eq (ρ := ρ)
    (E := fun p : SpectralCalculus.SpectralPlane => (p.1 : ℝ))
    (q := fun p => p.2) (a := a) (c := c)
    (K := fun t s => transverseAveragedKernel S φ (normalFrame m (t, s)))
    (by fun_prop) measurable_snd (fun p => p.1.2) ha hcs hc0 hpos hfin hK
  obtain ⟨h₁, h₂, hform⟩ := (hKernel St S hF hP φ hφ).2.2 m hm α ⟨hα1, hαc, hαO⟩ α
    ⟨hα1, hαc, hαO⟩ 0 le_rfl 0
  obtain ⟨C₂, hC₂⟩ := hP.ballDecay
  have hnonneg : SpectralCalculus.IsPosHermitianForm (reflectedForm S m) :=
    (hSpace St S C₂ m ⟨hF, hm.1, hP⟩ hC₂).1.1.posHermitian
  have hfacts := (hCompletion.1 (halfSpaceDomain m) (reflectedForm S m) hnonneg).2.1
  have hsame : (⟨_, h₂⟩ : halfSpaceDomain m) = ⟨tensorPlate α φ, h⟩ := by
    apply Subtype.ext
    funext x
    simp [translateFun]
  have hinner : ((‖reflectedClass S m ⟨tensorPlate α φ, h⟩‖ ^ 2 : ℝ) : ℂ) =
      normalFrameIntegral S φ m α α 0 0 := by
    rw [← hform, hsame]
    have := hfacts.inner_constClass ⟨tensorPlate α φ, h⟩ ⟨tensorPlate α φ, h⟩
    rw [show reflectedForm S m ⟨tensorPlate α φ, h⟩ ⟨tensorPlate α φ, h⟩ = _ from this.symm,
      inner_self_eq_norm_sq_to_K]
    push_cast
    rfl
  have hframe : normalFrameIntegral S φ m α α 0 0 =
      ∫ s₂ : ℝ, ∫ t₂ : ℝ, ∫ s₁ : ℝ, ∫ t₁ : ℝ,
        conj (a (t₁, s₁)) * a (t₂, s₂) *
          transverseAveragedKernel S φ (normalFrame m (t₁ + t₂, s₂ - s₁)) := by
    simp only [normalFrameIntegral, lebesgueIntegral, integralWrt, conjFun, zero_add, ha_def,
      normalFrame]
  have hreal : ‖reflectedClass S m ⟨tensorPlate α φ, h⟩‖ ^ 2 =
      ∫ p, ‖∫ t : ℝ, ∫ s : ℝ, a (t, s) *
        expWave (fun p : SpectralCalculus.SpectralPlane => (p.1 : ℝ)) (fun p => p.2)
          (t, s) p‖ ^ 2 ∂ρ := by
    have := hinner.trans (hframe.trans hfour)
    exact_mod_cast this
  rw [hreal, ofReal_integral_eq_lintegral_ofReal hint
    (Eventually.of_forall fun p => by positivity)]
  refine lintegral_congr fun p => ?_
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
  rfl
end PlateNormViaSpectralMeasure
end YangMills.Construction.TwoPoints
end
