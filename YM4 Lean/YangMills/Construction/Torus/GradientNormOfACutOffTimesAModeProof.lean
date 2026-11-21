import YangMills.Construction.Torus.GradientNormLipschitzConstantAndSharpNormProof
import YangMills.Construction.Torus.GradientNormOfACutOffTimesAMode
import YangMills.Construction.Torus.RestrictionsSumsProductsAndTensorsOfTestFunctions
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal ContDiff
noncomputable section
namespace YangMills.Construction.AmbientPoints.CutoffTimesMode
open YangMills.Construction.Torus.FourierBox
open YangMills.Construction.TorusMetric (euclidNormVec)
variable {s : YangMills.Construction.Conventions.StandingParameters}
abbrev coordIndex (μ : Fin 4) : Fin (4 * 1) := Fin.cast (by norm_num) μ
def toPoint (w : Fin (4 * 1) → ℝ) : Fin 4 → ℝ := fun μ => w (coordIndex μ)
def modeAt (P : ℝ) (κ : Fin 4 → ℤ) : Pt s .euclidean → ℂ := fun x => fourierMode P κ x
theorem tupleProj_zero (w : Fin (4 * 1) → ℝ) :
    tupleProj s .euclidean 1 w 0 = toPoint w := by
  change (flattenCoords 1).symm w 0 = toPoint w
  funext μ
  have h : 4 * ((0 : Fin 1) : ℕ) + (μ : ℕ) < 4 * 1 := by
    have := μ.2
    simp only [Fin.val_zero]
    omega
  have e : coordIndex μ = ⟨4 * ((0 : Fin 1) : ℕ) + (μ : ℕ), h⟩ := by
    ext
    simp [coordIndex]
  rw [toPoint, e]
  exact flattenCoords_symm_apply w 0 μ h
theorem modeAt_comp_tupleProj (P : ℝ) (κ : Fin 4 → ℤ) :
    ofSinglePoint (modeAt (s := s) P κ) ∘ tupleProj s .euclidean 1 =
      fourierMode P κ ∘ toPoint := by
  funext w
  change fourierMode P κ (tupleProj s .euclidean 1 w 0) = fourierMode P κ (toPoint w)
  rw [tupleProj_zero]
theorem contDiff_toPoint : ContDiff ℝ ∞ toPoint :=
  contDiff_pi.mpr fun μ => contDiff_apply ℝ ℝ (coordIndex μ)
theorem isSmoothFn_modeAt (P : ℝ) (κ : Fin 4 → ℤ) :
    IsSmoothFn (ofSinglePoint (modeAt (s := s) P κ)) := by
  refine ⟨isOpen_univ, fun n _ => ?_⟩
  rw [modeAt_comp_tupleProj]
  exact continuousPartialsUpTo_of_contDiff n ((contDiff_fourierMode P κ).comp contDiff_toPoint)
theorem norm_fourierMode (P : ℝ) (κ : Fin 4 → ℤ) (x : Fin 4 → ℝ) : ‖fourierMode P κ x‖ = 1 := by
  have h : 2 * Real.pi * Complex.I * (intDot κ x : ℂ) / (P : ℂ) =
      ((2 * Real.pi * intDot κ x / P : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [fourierMode, h]
  exact Complex.norm_exp_ofReal_mul_I _
theorem norm_modeAt (P : ℝ) (κ : Fin 4 → ℤ) (x : Pt s .euclidean) :
    ‖modeAt (s := s) P κ x‖ = 1 :=
  norm_fourierMode P κ x
theorem iteratedPartial_single {D : ℕ} (j : Fin D) (G : (Fin D → ℝ) → ℂ) :
    iteratedPartial (Pi.single j 1 : YangMills.Construction.PowerSeries.MultiIndex D) G =
      partialDeriv j G := by apply _root_.YangMills.Construction.AmbientPoints.GradientC1Bounds.iteratedPartial_single <;> assumption
theorem partialDeriv_fourierMode (P : ℝ) (κ : Fin 4 → ℤ) (μ : Fin 4) (w : Fin (4 * 1) → ℝ) :
    partialDeriv (coordIndex μ) (fourierMode P κ ∘ toPoint) w =
      fourierMode P κ (toPoint w) * (2 * Real.pi * Complex.I * ((κ μ : ℝ) : ℂ) / (P : ℂ)) := by
  have hS : ∀ t : ℝ, intDot κ (toPoint (w + t • Pi.single (coordIndex μ) 1)) =
      intDot κ (toPoint w) + t * (κ μ : ℝ) := by
    intro t
    have hp : ∀ ν, toPoint (w + t • Pi.single (coordIndex μ) 1) ν =
        toPoint w ν + t * (if ν = μ then 1 else 0) := by
      intro ν
      simp only [toPoint, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply,
        Fin.cast_inj]
    simp only [intDot, hp, mul_add, Finset.sum_add_distrib]
    congr 1
    simp [mul_comm]
  have hin : HasDerivAt (fun t : ℝ => intDot κ (toPoint w) + t * (κ μ : ℝ))
      (κ μ : ℝ) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (κ μ : ℝ)).const_add
      (intDot κ (toPoint w))
  have hc := (hin.ofReal_comp.const_mul (2 * Real.pi * Complex.I)).div_const (P : ℂ)
  have he := hc.cexp
  have hline : HasLineDerivAt ℝ (fourierMode P κ ∘ toPoint)
      (fourierMode P κ (toPoint w) * (2 * Real.pi * Complex.I * ((κ μ : ℝ) : ℂ) / (P : ℂ))) w
      (Pi.single (coordIndex μ) 1) := by
    have hfun : (fun t : ℝ => (fourierMode P κ ∘ toPoint) (w + t • Pi.single (coordIndex μ) 1)) =
        fun t : ℝ => Complex.exp (2 * Real.pi * Complex.I *
          ((intDot κ (toPoint w) + t * (κ μ : ℝ) : ℝ) : ℂ) / (P : ℂ)) := by
      funext t
      simp only [Function.comp_apply, fourierMode, hS]
    rw [HasLineDerivAt, hfun]
    simpa [fourierMode] using he
  exact hline.lineDeriv
theorem partialAt_modeAt (hT : TupleDerivProps s .euclidean 1) (P : ℝ)
    (κ : Fin 4 → ℤ) (μ : Fin 4) (x : Pt s .euclidean) :
    partialAt μ (modeAt (s := s) P κ) x =
      fourierMode P κ x * (2 * Real.pi * Complex.I * ((κ μ : ℝ) : ℂ) / (P : ℂ)) := by
  obtain ⟨w, hw⟩ := tupleProj_surjective s .euclidean 1 (fun _ => x)
  have hx : toPoint w = x := by
    rw [← tupleProj_zero (s := s), hw]
  have hsize : (((basisMultiIndex μ).order : ℕ) : ℕ∞) ≤ ⊤ := le_top
  obtain ⟨H, hH, -⟩ :=
    ((hT ⊤ (ofSinglePoint (modeAt P κ)) (isSmoothFn_modeAt P κ)).1
      (basisMultiIndex μ) hsize).1
  have hd := multiDeriv_comp_tupleProj (α := basisMultiIndex μ)
    (F := ofSinglePoint (modeAt (s := s) P κ)) ⟨H, hH⟩
  have hwd := congrFun hd w
  rw [Function.comp_apply, hw, modeAt_comp_tupleProj] at hwd
  rw [partialAt, hwd]
  have hm : iteratedPartial (basisMultiIndex μ) (fourierMode P κ ∘ toPoint) w =
      partialDeriv (coordIndex μ) (fourierMode P κ ∘ toPoint) w :=
    congrFun (iteratedPartial_single _ _) w
  rw [hm, partialDeriv_fourierMode, hx]
theorem gradNorm_modeAt (hT : TupleDerivProps s .euclidean 1) {ρ : ℝ} (hρ : 0 < ρ)
    (κ : Fin 4 → ℤ) (x : Pt s .euclidean) :
    gradNorm (modeAt (s := s) (4 * ρ) κ) x =
      euclidNormInt κ / bumpScale ρ := by
  have hterm : ∀ μ, ‖gradient (modeAt (s := s) (4 * ρ) κ) x μ‖ ^ 2 =
      (Real.pi / (2 * ρ)) ^ 2 * (κ μ : ℝ) ^ 2 := by
    intro μ
    have hn : ‖(2 * Real.pi * Complex.I * ((κ μ : ℝ) : ℂ) / ((4 * ρ : ℝ) : ℂ))‖ =
        Real.pi / (2 * ρ) * |(κ μ : ℝ)| := by
      rw [norm_div, norm_mul, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real,
        Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
        Real.norm_eq_abs, abs_of_pos Real.pi_pos, abs_of_pos (by positivity : 0 < 4 * ρ)]
      simp only [Complex.norm_ofNat]
      field_simp
      ring
    have hv : gradient (modeAt (s := s) (4 * ρ) κ) x μ = modeAt (s := s) (4 * ρ) κ x *
        (2 * Real.pi * Complex.I * ((κ μ : ℝ) : ℂ) / ((4 * ρ : ℝ) : ℂ)) :=
      partialAt_modeAt hT _ _ _ _
    rw [hv, norm_mul, norm_modeAt, one_mul, hn, mul_pow, sq_abs]
  have hsum : ∑ μ, ‖gradient (modeAt (s := s) (4 * ρ) κ) x μ‖ ^ 2 =
      (Real.pi / (2 * ρ)) ^ 2 * ∑ μ, (κ μ : ℝ) ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun μ _ => hterm μ
  have hpos : 0 ≤ Real.pi / (2 * ρ) := by positivity
  rw [gradNorm, hsum, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hpos, euclidNormInt,
    euclidNormVec, bumpScale]
  field_simp
theorem cutoffTimesModeGradNorm_holds (hT : TupleTopology.Holds)
    (hS : GradientC1Bounds.Statement)
    (hR : TestFnOperations) : CutoffTimesModeGradNorm := by
  intro s ρ hρ A χ κ hA hχ
  have hD : TupleDerivProps s .euclidean 1 := ((hT s .euclidean).1 1 le_rfl).2.2.2.2
  have hΩ : IsOpen (singletonTuples A) := hA.preimage (continuous_apply (0 : Fin 1))
  have hprod := ((hR s .euclidean 1 le_rfl).2.1 _ hΩ).2.2.2
  have hmain := hprod (asFunctionOnOnePoint χ) (ofSinglePoint (modeAt (4 * ρ) κ)) hχ.1
    (isSmoothFn_modeAt _ _)
  have hEq : ofSinglePoint (fun x => (χ x : ℂ) * fourierMode (4 * ρ) κ x) =
      asFunctionOnOnePoint χ * ofSinglePoint (modeAt (s := s) (4 * ρ) κ) := rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [hEq]
    exact hmain.2.2.1 (Or.inl hχ)
  · rw [hEq]
    exact hmain.2.1.trans inter_subset_left
  · have hscale : 0 < bumpScale ρ := by
      have := Real.pi_pos
      rw [bumpScale]
      positivity
    have hκ : 0 ≤ euclidNormInt κ := Real.sqrt_nonneg _
    have hc : 0 ≤ euclidNormInt κ / bumpScale ρ := div_nonneg hκ hscale.le
    have hg : IsCnAtPoint 1 (fun x : Pt s .euclidean => (χ x : ℂ)) :=
      ⟨hχ.1.1, fun n _ => hχ.1.2 n le_top⟩
    have hh : IsCnAtPoint 1 (modeAt (s := s) (4 * ρ) κ) :=
      ⟨(isSmoothFn_modeAt (s := s) (4 * ρ) κ).1,
        fun n _ => (isSmoothFn_modeAt (s := s) (4 * ρ) κ).2 n le_top⟩
    have hgrad := ((hS s .euclidean).1 _ _ hg hh).2.2.1
    have hsup : ∀ x, ENNReal.ofReal |χ x| ≤ c1GradNorm fun x => (χ x : ℂ) := by
      intro x
      refine le_trans ?_ (le_max_left _ _)
      rw [tupleSupNorm_ofSinglePoint]
      have := le_iSup (fun x => ENNReal.ofReal ‖(χ x : ℂ)‖) x
      simpa using this
    have hlen : ∀ x, ENNReal.ofReal (gradNorm (fun x => (χ x : ℂ)) x) ≤
        c1GradNorm fun x => (χ x : ℂ) := by
      intro x
      exact (le_iSup (fun x => ENNReal.ofReal (gradNorm (fun x => (χ x : ℂ)) x)) x).trans
        (le_max_right _ _)
    have hone : (c1GradNorm fun x => (χ x : ℂ)) ≤ (c1GradNorm fun x => (χ x : ℂ)) *
        ENNReal.ofReal (1 + euclidNormInt κ / bumpScale ρ) :=
      le_mul_of_one_le_right' (ENNReal.one_le_ofReal.mpr (by linarith))
    refine max_le ?_ ?_
    · rw [tupleSupNorm_ofSinglePoint]
      refine iSup_le fun x => ?_
      have hx : ‖(χ x : ℂ) * modeAt (s := s) (4 * ρ) κ x‖ = |χ x| := by
        rw [norm_mul, norm_modeAt, mul_one, Complex.norm_real, Real.norm_eq_abs]
      exact (le_of_eq (congrArg ENNReal.ofReal hx)).trans ((hsup x).trans hone)
    · refine iSup_le fun x => ?_
      have h1 : gradNorm (fun x => (χ x : ℂ) * fourierMode (4 * ρ) κ x) x ≤
          |χ x| * (euclidNormInt κ / bumpScale ρ) +
            gradNorm (fun x => (χ x : ℂ)) x := by
        have h2 := hgrad x
        rw [gradNorm_modeAt hD hρ, Complex.norm_real, Real.norm_eq_abs] at h2
        rw [norm_modeAt, one_mul] at h2
        exact h2
      calc ENNReal.ofReal (gradNorm (fun x => (χ x : ℂ) * fourierMode (4 * ρ) κ x) x)
          ≤ ENNReal.ofReal (|χ x| * (euclidNormInt κ / bumpScale ρ) +
              gradNorm (fun x => (χ x : ℂ)) x) := ENNReal.ofReal_le_ofReal h1
        _ = ENNReal.ofReal |χ x| * ENNReal.ofReal (euclidNormInt κ / bumpScale ρ) +
              ENNReal.ofReal (gradNorm (fun x => (χ x : ℂ)) x) := by
            rw [ENNReal.ofReal_add (mul_nonneg (abs_nonneg _) hc)
                (show 0 ≤ gradNorm (fun x => (χ x : ℂ)) x from Real.sqrt_nonneg _),
              ENNReal.ofReal_mul (abs_nonneg _)]
        _ ≤ (c1GradNorm fun x => (χ x : ℂ)) *
                ENNReal.ofReal (euclidNormInt κ / bumpScale ρ) +
              c1GradNorm fun x => (χ x : ℂ) := by
            gcongr
            · exact hsup x
            · exact hlen x
        _ = (c1GradNorm fun x => (χ x : ℂ)) *
              ENNReal.ofReal (1 + euclidNormInt κ / bumpScale ρ) := by
            rw [ENNReal.ofReal_add zero_le_one hc, ENNReal.ofReal_one, mul_add, mul_one, add_comm]
end YangMills.Construction.AmbientPoints.CutoffTimesMode
