import YangMills.Construction.PeriodicOperators.BoundOfTheKernelOfAMatrixFunction
import YangMills.Construction.PeriodicOperators.TranslationsOfTheSymbolProof
import Mathlib
set_option autoImplicit false
open Set Topology MeasureTheory
noncomputable section
namespace YangMills.Construction.PeriodicOperators.MatrixFunctionKernel
open TorusMetric (l1NormVec euclidNormVec)
open RiemannSums (HolomorphicNearStrip PeriodicOnStrip BoundedOnStrip)
section Phases
variable {I : PeriodicData}
theorem phase_translate_invariant (hP : IsPeriodic I) (e n : Fin 4 → ℤ) (i : I.Carrier) :
    Complex.exp (2 * Real.pi * Complex.I *
        bilinDot (toComplexVec (castVec e)) (toComplexVec (I.pos (I.translate n i)))) =
      Complex.exp (2 * Real.pi * Complex.I *
        bilinDot (toComplexVec (castVec e)) (toComplexVec (I.pos i))) := by
  rw [hP.pos_translate]
  have hdot : bilinDot (toComplexVec (castVec e)) (toComplexVec (I.pos i + castVec n)) =
      bilinDot (toComplexVec (castVec e)) (toComplexVec (I.pos i)) +
        ((∑ μ, e μ * n μ : ℤ) : ℂ) := by
    simp [bilinDot, toComplexVec, castVec, mul_add, Finset.sum_add_distrib]
  have hone : Complex.exp (2 * Real.pi * Complex.I * ((∑ μ, e μ * n μ : ℤ) : ℂ)) = 1 := by
    rw [show (2 * Real.pi * Complex.I * ((∑ μ, e μ * n μ : ℤ) : ℂ)) =
      ((∑ μ, e μ * n μ : ℤ) : ℂ) * (2 * Real.pi * Complex.I) by ring]
    exact Complex.exp_int_mul_two_pi_mul_I _
  rw [hdot, mul_add, Complex.exp_add, hone, mul_one]
theorem phaseOn_mkQuot (hP : IsPeriodic I) (e : Fin 4 → ℤ) (i : I.Carrier) :
    phaseOn I e (I.mkQuot 1 i) = Complex.exp (2 * Real.pi * Complex.I *
      bilinDot (toComplexVec (castVec e)) (toComplexVec (I.pos i))) := by
  let g : I.UnitQuot → ℂ := Quot.lift
    (fun i => Complex.exp (2 * Real.pi * Complex.I *
      bilinDot (toComplexVec (castVec e)) (toComplexVec (I.pos i))))
    (by
      rintro a _ ⟨n, rfl⟩
      exact (phase_translate_invariant hP e _ a).symm)
  have hex : ∃ z, ∀ j, I.mkQuot 1 j = I.mkQuot 1 i →
      Complex.exp (2 * Real.pi * Complex.I *
        bilinDot (toComplexVec (castVec e)) (toComplexVec (I.pos j))) = z :=
    ⟨g (I.mkQuot 1 i), fun j hj => by rw [← hj]; rfl⟩
  exact (Classical.epsilon_spec hex i rfl).symm
theorem phaseOn_ne_zero (hP : IsPeriodic I) (e : Fin 4 → ℤ) (c : I.UnitQuot) :
    phaseOn I e c ≠ 0 := by apply _root_.YangMills.Construction.PeriodicOperators.SymbolTranslation.phaseOn_ne_zero <;> assumption
theorem phaseMul_isUnit (hP : IsPeriodic I) (e : Fin 4 → ℤ) :
    IsUnit (phaseMul I e : Module.End ℂ (I.UnitQuot → ℂ)) := by
  have hne := phaseOn_ne_zero hP e
  let D : (I.UnitQuot → ℂ) →ₗ[ℂ] (I.UnitQuot → ℂ) :=
    { toFun := fun f c => (phaseOn I e c)⁻¹ * f c
      map_add' := fun f g => by
        funext c
        simp [mul_add]
      map_smul' := fun z f => by
        funext c
        simp [mul_left_comm] }
  exact ⟨{ val := phaseMul I e
           inv := D
           val_inv := by
            refine LinearMap.ext fun f => funext fun c => ?_
            show phaseOn I e c * ((phaseOn I e c)⁻¹ * f c) = f c
            rw [mul_inv_cancel_left₀ (hne c)]
           inv_val := by
            refine LinearMap.ext fun f => funext fun c => ?_
            show (phaseOn I e c)⁻¹ * (phaseOn I e c * f c) = f c
            rw [inv_mul_cancel_left₀ (hne c)] }, rfl⟩
theorem quotHomInverse_phaseMul_apply (hP : IsPeriodic I) (e : Fin 4 → ℤ)
    (f : I.UnitQuot → ℂ) (c : I.UnitQuot) :
    quotHomInverse (phaseMul I e) f c = (phaseOn I e c)⁻¹ * f c := by
  have he := Ring.mul_inverse_cancel (phaseMul I e : Module.End ℂ (I.UnitQuot → ℂ))
    (phaseMul_isUnit hP e)
  have hc := congrFun (LinearMap.congr_fun he f) c
  change phaseOn I e c * quotHomInverse (phaseMul I e) f c = f c at hc
  rw [eq_inv_mul_iff_mul_eq₀ (phaseOn_ne_zero hP e c)]
  exact hc
end Phases
section Entries
variable {I J : PeriodicData}
open Classical in
theorem linearMapEntry_conj_phaseMul (hJ : IsPeriodic J) (e : Fin 4 → ℤ) (A : QuotHom I J)
    (d : J.UnitQuot) (c : I.UnitQuot) :
    linearMapEntry ((quotHomInverse (phaseMul J e)).comp
        (A.comp (phaseMul I e))) d c =
      (phaseOn J e d)⁻¹ * linearMapEntry A d c * phaseOn I e c := by
  simp only [linearMapEntry, LinearMap.comp_apply]
  rw [quotHomInverse_phaseMul_apply hJ]
  have hs : phaseMul I e (Pi.single c 1) = phaseOn I e c • Pi.single c 1 := by
    funext b
    show phaseOn I e b * (Pi.single c (1 : ℂ) : I.UnitQuot → ℂ) b = _
    by_cases hb : b = c
    · subst hb
      simp
    · simp [hb]
  rw [hs, map_smul, Pi.smul_apply, smul_eq_mul]
  ring
end Entries
section Holomorphy
variable {O : Set (Fin 4 → ℂ)} {f g : (Fin 4 → ℂ) → ℂ}
theorem isHolomorphicIn_scalar_iff :
    Coordinates.ComplexCoordinates.IsHolomorphicIn (N' := 1) O (fun z _ => f z) ↔
      IsOpen O ∧ ContinuousOn f O ∧ ∀ a ∈ O, ∀ j : Fin 4, ∀ᶠ ζ in 𝓝 (0 : ℂ),
        DifferentiableAt ℂ
          (fun ζ : ℂ => f (a + ζ • Coordinates.ComplexCoordinates.stdBasisVector j)) ζ := by
  constructor
  · rintro ⟨hO, hc, hd⟩
    refine ⟨hO, ?_, fun a ha j => (hd a ha j).mono fun ζ hζ => ?_⟩
    · exact (continuous_apply (0 : Fin 1)).comp_continuousOn hc
    · exact differentiableAt_pi.mp hζ 0
  · rintro ⟨hO, hc, hd⟩
    refine ⟨hO, ?_, fun a ha j => (hd a ha j).mono fun ζ hζ => ?_⟩
    · exact continuousOn_pi.mpr fun _ => hc
    · exact differentiableAt_pi.mpr fun _ => hζ
theorem isHolomorphicIn_scalar_mul
    (hf : Coordinates.ComplexCoordinates.IsHolomorphicIn (N' := 1) O (fun z _ => f z))
    (hg : Coordinates.ComplexCoordinates.IsHolomorphicIn (N' := 1) O (fun z _ => g z)) :
    Coordinates.ComplexCoordinates.IsHolomorphicIn (N' := 1) O (fun z _ => f z * g z) := by
  obtain ⟨hO, hc, hd⟩ := isHolomorphicIn_scalar_iff.mp hf
  obtain ⟨-, hc', hd'⟩ := isHolomorphicIn_scalar_iff.mp hg
  refine isHolomorphicIn_scalar_iff.mpr ⟨hO, hc.mul hc', fun a ha j => ?_⟩
  filter_upwards [hd a ha j, hd' a ha j] with ζ h1 h2
  exact h1.mul h2
theorem differentiable_planeWave (Y : Fin 4 → ℂ) :
    Differentiable ℂ fun z : Fin 4 → ℂ => Complex.exp (-Complex.I * bilinDot z Y) := by
  unfold bilinDot
  fun_prop
theorem isHolomorphicIn_planeWave (hO : IsOpen O) (Y : Fin 4 → ℂ) :
    Coordinates.ComplexCoordinates.IsHolomorphicIn (N' := 1) O
      (fun z _ => Complex.exp (-Complex.I * bilinDot z Y)) := by
  refine isHolomorphicIn_scalar_iff.mpr ⟨hO, (differentiable_planeWave Y).continuous.continuousOn,
    fun a _ j => Filter.Eventually.of_forall fun ζ => ?_⟩
  have hline : Differentiable ℂ
      fun ζ : ℂ => a + ζ • Coordinates.ComplexCoordinates.stdBasisVector j :=
    (differentiable_id.smul_const _).const_add _
  exact ((differentiable_planeWave Y).comp hline) ζ
end Holomorphy
theorem norm_torusAverage_le (f : InfiniteLattice.AmbientSpace → ℂ) {C : ℝ}
    (hC : ∀ κ, ‖f κ‖ ≤ C) : ‖torusAverage f‖ ≤ C := by
  have hvol : (volume : Measure InfiniteLattice.AmbientSpace)
      (Icc (fun _ : Fin 4 => -Real.pi) fun _ => Real.pi) =
      ENNReal.ofReal ((2 * Real.pi) ^ 4) := by
    rw [Real.volume_Icc_pi]
    have : ENNReal.ofReal (Real.pi - -Real.pi) = ENNReal.ofReal (2 * Real.pi) := by
      congr 1; ring
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [this, ENNReal.ofReal_pow (by positivity)]
  have h1 := norm_setIntegral_le_of_norm_le_const (μ := volume)
    (s := Icc (fun _ : Fin 4 => -Real.pi) fun _ => Real.pi) (f := f) (C := C)
    (by rw [hvol]; exact ENNReal.ofReal_lt_top) (fun x _ => hC x)
  have hreal : (volume : Measure InfiniteLattice.AmbientSpace).real
      (Icc (fun _ : Fin 4 => -Real.pi) fun _ => Real.pi) = (2 * Real.pi) ^ 4 := by
    rw [Measure.real, hvol, ENNReal.toReal_ofReal (by positivity)]
  rw [hreal] at h1
  unfold torusAverage
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  calc ((2 * Real.pi) ^ 4)⁻¹ * _ ≤ ((2 * Real.pi) ^ 4)⁻¹ * (C * (2 * Real.pi) ^ 4) := by
        gcongr
    _ = C := by field_simp
theorem norm_planeWave (κ : Fin 4 → ℂ) (y : InfiniteLattice.AmbientSpace) :
    ‖Complex.exp (-Complex.I * bilinDot κ (toComplexVec y))‖ =
      Real.exp (∑ μ, (κ μ).im * y μ) := by
  rw [Complex.norm_exp]
  congr 1
  simp [bilinDot, toComplexVec, Complex.mul_re, Complex.mul_im]
theorem euclidNormVec_le_l1NormVec (v : Fin 4 → ℝ) : euclidNormVec v ≤ l1NormVec v := by
  have h0 : 0 ≤ l1NormVec v := Finset.sum_nonneg fun _ _ => abs_nonneg _
  refine Real.sqrt_le_iff.mpr ⟨h0, ?_⟩
  simp only [l1NormVec, Fin.sum_univ_four, ← sq_abs (v _)]
  nlinarith [abs_nonneg (v 0), abs_nonneg (v 1), abs_nonneg (v 2), abs_nonneg (v 3),
    mul_nonneg (abs_nonneg (v 0)) (abs_nonneg (v 1)), mul_nonneg (abs_nonneg (v 0)) (abs_nonneg (v 2)),
    mul_nonneg (abs_nonneg (v 0)) (abs_nonneg (v 3)), mul_nonneg (abs_nonneg (v 1)) (abs_nonneg (v 2)),
    mul_nonneg (abs_nonneg (v 1)) (abs_nonneg (v 3)), mul_nonneg (abs_nonneg (v 2)) (abs_nonneg (v 3))]
section Kernel
variable {I J : PeriodicData}
def shiftedIntegrand (M : (Fin 4 → ℂ) → QuotHom I J) (j : J.Carrier) (i : I.Carrier)
    (κ : Fin 4 → ℂ) : ℂ :=
  carrierEntry (M κ) j i *
    Complex.exp (-Complex.I * bilinDot κ (toComplexVec (I.pos i - J.pos j)))
theorem shiftedIntegrand_holomorphic {υ : ℝ} {M : (Fin 4 → ℂ) → QuotHom I J}
    (hM : IsHolomorphicNbhd (imStrip υ) M) (j : J.Carrier) (i : I.Carrier) :
    HolomorphicNearStrip υ (shiftedIntegrand M j i) := by
  obtain ⟨O, hO, hsub, hh⟩ := hM
  exact ⟨O, hsub, isHolomorphicIn_scalar_mul (hh _ _) (isHolomorphicIn_planeWave hO _)⟩
theorem shiftedIntegrand_periodic (hI : IsPeriodic I) (hJ : IsPeriodic J) {υ : ℝ}
    {M : (Fin 4 → ℂ) → QuotHom I J} (hQ : IsQuasiPeriodic (imStrip υ) M) (j : J.Carrier)
    (i : I.Carrier) : PeriodicOnStrip υ (shiftedIntegrand M j i) := by
  rintro κ hκ q ⟨n, hn⟩
  have hpoint : κ + toComplexVec q = addTwoPiInt κ n := by
    funext μ
    have := hn μ
    simp only [Pi.add_apply, toComplexVec, addTwoPiInt, this]
    push_cast
    ring
  have hdot : bilinDot (addTwoPiInt κ n) (toComplexVec (I.pos i - J.pos j)) =
      bilinDot κ (toComplexVec (I.pos i - J.pos j)) +
        2 * Real.pi * (bilinDot (toComplexVec (castVec n)) (toComplexVec (I.pos i)) -
          bilinDot (toComplexVec (castVec n)) (toComplexVec (J.pos j))) := by
    simp only [bilinDot, addTwoPiInt, toComplexVec, castVec, Pi.sub_apply, Finset.mul_sum,
      ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun μ _ => ?_
    push_cast
    ring
  rw [hpoint]
  simp only [shiftedIntegrand, carrierEntry]
  rw [hQ n κ hκ, linearMapEntry_conj_phaseMul hJ, phaseOn_mkQuot hI, phaseOn_mkQuot hJ, hdot]
  set a := bilinDot (toComplexVec (castVec n)) (toComplexVec (I.pos i))
  set b := bilinDot (toComplexVec (castVec n)) (toComplexVec (J.pos j))
  set w := bilinDot κ (toComplexVec (I.pos i - J.pos j))
  have hexp : Complex.exp (-Complex.I * (w + 2 * Real.pi * (a - b))) =
      Complex.exp (-Complex.I * w) * (Complex.exp (2 * Real.pi * Complex.I * a))⁻¹ *
        Complex.exp (2 * Real.pi * Complex.I * b) := by
    rw [← Complex.exp_neg, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    ring
  rw [hexp]
  have h1 := Complex.exp_ne_zero (2 * Real.pi * Complex.I * a)
  have h2 := Complex.exp_ne_zero (2 * Real.pi * Complex.I * b)
  field_simp
theorem bddAbove_norm_carrierEntry {υ : ℝ} {M : (Fin 4 → ℂ) → QuotHom I J}
    (hB : QuotHomFamilyBoundedOn (imStrip υ) M) (j : J.Carrier) (i : I.Carrier) :
    BddAbove ((fun κ => ‖carrierEntry (M κ) j i‖) '' imStrip υ) := by
  obtain ⟨C, hC⟩ := hB (J.mkQuot 1 j, I.mkQuot 1 i)
  exact ⟨C, by
    rintro _ ⟨κ, hκ, rfl⟩
    exact hC κ hκ⟩
theorem shiftedIntegrand_bounded {υ : ℝ} {M : (Fin 4 → ℂ) → QuotHom I J}
    (hB : QuotHomFamilyBoundedOn (imStrip υ) M) (j : J.Carrier) (i : I.Carrier) :
    BoundedOnStrip υ (shiftedIntegrand M j i) := by
  obtain ⟨C, hC⟩ := hB (J.mkQuot 1 j, I.mkQuot 1 i)
  set y := I.pos i - J.pos j with hy
  refine ⟨|C| * Real.exp (υ * l1NormVec y), fun κ hκ => ?_⟩
  have h1 : ‖carrierEntry (M κ) j i‖ ≤ |C| := (hC κ hκ).trans (le_abs_self C)
  have h2 : ∑ μ, (κ μ).im * y μ ≤ υ * l1NormVec y := by
    rw [l1NormVec, Finset.mul_sum]
    refine Finset.sum_le_sum fun μ _ => ?_
    calc (κ μ).im * y μ ≤ |(κ μ).im * y μ| := le_abs_self _
      _ = |(κ μ).im| * |y μ| := abs_mul _ _
      _ ≤ υ * |y μ| := by gcongr; exact hκ μ
  simp only [shiftedIntegrand]
  rw [norm_mul, norm_planeWave]
  exact mul_le_mul h1 (Real.exp_le_exp.mpr h2) (Real.exp_pos _).le (abs_nonneg _)
theorem norm_matFunKernel_le (hR : RiemannSums.Claim) (hI : IsPeriodic I)
    (hJ : IsPeriodic J) {υ : ℝ} (hυ : 0 < υ) {M : (Fin 4 → ℂ) → QuotHom I J}
    (hH : IsHolomorphicNbhd (imStrip υ) M) (hB : QuotHomFamilyBoundedOn (imStrip υ) M)
    (hQ : IsQuasiPeriodic (imStrip υ) M) (j : J.Carrier) (i : I.Carrier) :
    ‖matFunKernel I J M j i‖ ≤
      sSup ((fun κ => ‖carrierEntry (M κ) j i‖) '' imStrip υ) *
        Real.exp (-υ * l1NormVec (I.pos i - J.pos j)) := by
  set y := I.pos i - J.pos j with hy
  let s : Fin 4 → ℝ := fun μ => if 0 ≤ y μ then 1 else -1
  have hs : ∀ μ, s μ * y μ = |y μ| := by
    intro μ
    by_cases h : 0 ≤ y μ
    · simp [s, h, abs_of_nonneg h]
    · simp [s, h, abs_of_neg (not_le.mp h)]
  have hs1 : ∀ μ, |s μ| = 1 := by
    intro μ
    by_cases h : 0 ≤ y μ <;> simp [s, h]
  let ϑ : Fin 4 → ℂ := fun μ => ((-(υ * s μ) : ℝ) : ℂ) * Complex.I
  have hϑim : ∀ μ, (ϑ μ).im = -(υ * s μ) := fun μ => by simp [ϑ]
  have hϑ : ϑ ∈ imStrip υ := fun μ => by
    rw [hϑim, abs_neg, abs_mul, hs1, abs_of_pos hυ, mul_one]
  have hshift := (hR 1 υ (shiftedIntegrand M j i) one_pos hυ
    (shiftedIntegrand_holomorphic hH j i) (shiftedIntegrand_periodic hI hJ hQ j i)
    (shiftedIntegrand_bounded hB j i)).2 ϑ hϑ
  have hker : matFunKernel I J M j i =
      torusAverage fun κ => shiftedIntegrand M j i (toComplexVec κ) := rfl
  rw [hker, ← hshift]
  refine norm_torusAverage_le _ fun κ => ?_
  have hmem : toComplexVec κ + ϑ ∈ imStrip υ := fun μ => by
    have := hϑ μ
    simpa [toComplexVec] using this
  simp only [shiftedIntegrand]
  rw [norm_mul, norm_planeWave, ← hy]
  have hsum : ∑ μ, (((toComplexVec κ + ϑ) μ).im) * y μ = -υ * l1NormVec y := by
    rw [l1NormVec, Finset.mul_sum]
    refine Finset.sum_congr rfl fun μ _ => ?_
    have him : ((toComplexVec κ + ϑ) μ).im = -(υ * s μ) := by
      simp [toComplexVec, hϑim]
    rw [him, ← hs μ]
    ring
  rw [hsum]
  exact mul_le_mul_of_nonneg_right
    (le_csSup (bddAbove_norm_carrierEntry hB j i) ⟨_, hmem, rfl⟩) (Real.exp_pos _).le
theorem matFunKernel_shiftInvariant (hI : IsPeriodic I) (hJ : IsPeriodic J)
    (M : (Fin 4 → ℂ) → QuotHom I J) : IsShiftInvariant I J (matFunKernel I J M) := by
  intro n j i
  have hc : I.mkQuot 1 (I.translate n i) = I.mkQuot 1 i :=
    (Quot.sound ⟨n, by rw [one_nsmul]⟩).symm
  have hc' : J.mkQuot 1 (J.translate n j) = J.mkQuot 1 j :=
    (Quot.sound ⟨n, by rw [one_nsmul]⟩).symm
  show torusAverage _ = torusAverage _
  congr 1
  funext κ
  simp only [matFunIntegrand, carrierEntry, hc, hc', hI.pos_translate,
    hJ.pos_translate, add_sub_add_right_eq_sub]
theorem exists_uniform_sSup_bound (hI : IsPeriodic I) (hJ : IsPeriodic J)
    {υ : ℝ} (hυ : 0 < υ) {M : (Fin 4 → ℂ) → QuotHom I J}
    (hB : QuotHomFamilyBoundedOn (imStrip υ) M) :
    ∃ C : ℝ, 0 < C ∧ ∀ j i, sSup ((fun κ => ‖carrierEntry (M κ) j i‖) '' imStrip υ) ≤ C := by
  have := hI.finite_quot
  have := hJ.finite_quot
  have := Fintype.ofFinite I.UnitQuot
  have := Fintype.ofFinite J.UnitQuot
  choose B hBd using hB
  refine ⟨1 + ∑ e, |B e|, by positivity, fun j i => ?_⟩
  have hne : ((fun κ => ‖carrierEntry (M κ) j i‖) '' imStrip υ).Nonempty :=
    ⟨_, 0, fun μ => by simpa using hυ.le, rfl⟩
  refine csSup_le hne ?_
  rintro _ ⟨κ, hκ, rfl⟩
  have h1 : ‖carrierEntry (M κ) j i‖ ≤ B (J.mkQuot 1 j, I.mkQuot 1 i) :=
    hBd (J.mkQuot 1 j, I.mkQuot 1 i) κ hκ
  have h2 : |B (J.mkQuot 1 j, I.mkQuot 1 i)| ≤ ∑ e, |B e| :=
    Finset.single_le_sum (f := fun e => |B e|) (fun _ _ => abs_nonneg _) (Finset.mem_univ _)
  linarith [le_abs_self (B (J.mkQuot 1 j, I.mkQuot 1 i))]
end Kernel
theorem decayBound_holds (hR : RiemannSums.Claim) : DecayBound := by
  intro I J hI hJ υ hυ M hH hB hQ
  have hbound := norm_matFunKernel_le hR hI hJ hυ hH hB hQ
  refine ⟨⟨matFunKernel_shiftInvariant hI hJ M, ?_⟩, hbound⟩
  obtain ⟨C, hC, hsup⟩ := exists_uniform_sSup_bound hI hJ hυ hB
  refine ⟨C, υ, hC, hυ, fun j i => (hbound j i).trans ?_⟩
  have hL : l1NormVec (I.pos i - J.pos j) = l1NormVec (J.pos j - I.pos i) := by
    simp only [l1NormVec, Pi.sub_apply, abs_sub_comm]
  rw [hL]
  refine mul_le_mul (hsup j i) (Real.exp_le_exp.mpr ?_) (Real.exp_pos _).le hC.le
  have := euclidNormVec_le_l1NormVec (J.pos j - I.pos i)
  nlinarith
end YangMills.Construction.PeriodicOperators.MatrixFunctionKernel
end
