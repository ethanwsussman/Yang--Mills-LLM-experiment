import YangMills.Construction.FormHilbert.JointSpectralCalculus
import YangMills.Construction.ReflectionPositivity.CarrierOfTheSitePicture
import YangMills.Construction.ReflectionPositivity.CurveOfTheSpectralVariables
import YangMills.Construction.ReflectionPositivity.EnergyMomentumInequalityAtOneStepLinkForm
import YangMills.Construction.ReflectionPositivity.LinkPictureInTheSitePicture
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
open MeasureTheory Set
open scoped ComplexConjugate ComplexOrder ENNReal Real
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.SiteCarrier
open YangMills.Construction.ReflectionPositivity.MirrorHyperplanes (unitPositiveClass)
open YangMills.Construction.FormHilbert
open YangMills.Construction.JointSpectrum (CommutingFamily SpectralDomain)
open YangMills.Construction.ReflectionPositivity.DirectionPictures
section Calculus
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {J : Type} [Fintype J] [Nonempty J]
theorem isBddMeasurable_of_continuous {φ : SpectralDomain J → ℂ} (h : Continuous φ) :
    IsBddMeasurable φ := by
  refine ⟨h.measurable, ?_⟩
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn h.continuousOn
  exact ⟨C, fun p => hC p (mem_univ p)⟩
theorem isBddMeasurable_mul {φ φ' : SpectralDomain J → ℂ} (h : IsBddMeasurable φ)
    (h' : IsBddMeasurable φ') : IsBddMeasurable fun p => φ p * φ' p := by
  obtain ⟨m, C, hC⟩ := h
  obtain ⟨m', C', hC'⟩ := h'
  refine ⟨m.mul m', C * C', fun p => ?_⟩
  rw [norm_mul]
  exact mul_le_mul (hC p) (hC' p) (norm_nonneg _) ((norm_nonneg _).trans (hC p))
theorem isBddMeasurable_add_mul {φ φ' : SpectralDomain J → ℂ} (h : IsBddMeasurable φ)
    (h' : IsBddMeasurable φ') (c : ℂ) : IsBddMeasurable fun p => φ p + c * φ' p := by
  obtain ⟨m, C, hC⟩ := h
  obtain ⟨m', C', hC'⟩ := h'
  refine ⟨m.add (m'.const_mul c), C + ‖c‖ * C', fun p => ?_⟩
  refine (norm_add_le _ _).trans (add_le_add (hC p) ?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (hC' p) (norm_nonneg _)
theorem isBddMeasurable_indicator (Δ : MeasSubset J) :
    IsBddMeasurable (Δ.1.indicator fun _ => (1 : ℂ)) := by
  refine ⟨measurable_const.indicator Δ.2, 1, fun p => ?_⟩
  by_cases h : p ∈ Δ.1 <;> simp [h]
theorem eq_of_isSpectralIntegral {E : BorelPVM J H} {φ : SpectralDomain J → ℂ}
    {A B : H →L[ℂ] H} (hA : E.IsSpectralIntegral φ A) (hB : E.IsSpectralIntegral φ B) :
    A = B := by
  have h0 : ((A - B : H →L[ℂ] H) : H →ₗ[ℂ] H) = 0 := by
    refine (inner_map_self_eq_zero _).mp fun x => ?_
    have : inner ℂ x ((A - B) x) = 0 := by
      rw [sub_apply, inner_sub_right, hA x, hB x, sub_self]
    change inner ℂ ((A - B) x) x = 0
    rw [← inner_conj_symm, this, map_zero]
  have h1 : A - B = 0 := by
    ext x
    exact congrArg (fun T : H →ₗ[ℂ] H => T x) h0
  exact sub_eq_zero.mp h1
theorem spectralOp_eq {E : BorelPVM J H} {φ : SpectralDomain J → ℂ}
    {A : H →L[ℂ] H} (hA : E.IsSpectralIntegral φ A) : E.spectralOp φ = A := by
  have h : ∃ A, E.IsSpectralIntegral φ A := ⟨A, hA⟩
  rw [BorelPVM.spectralOp, dif_pos h]
  exact eq_of_isSpectralIntegral (Classical.choose_spec h) hA
theorem isSpectralIntegral_indicator (E : BorelPVM J H) (Δ : MeasSubset J) :
    E.IsSpectralIntegral (Δ.1.indicator fun _ => (1 : ℂ)) (E Δ) := fun ψ => by
  rw [integral_indicator_const _ Δ.2, E.inner_apply_eq_norm_sq, Measure.real,
    E.quadMeasure_apply ψ Δ, ENNReal.toReal_ofReal (by positivity)]
  simp
theorem proj_eq_zero_of_null (E : BorelPVM J H) (Δ : MeasSubset J)
    (h : ∀ ψ, E.quadMeasure ψ Δ.1 = 0) : E Δ = 0 := by
  ext ψ
  have h₁ := E.quadMeasure_apply ψ Δ
  rw [h ψ] at h₁
  have h₂ : ‖E Δ ψ‖ ^ 2 ≤ 0 := ENNReal.ofReal_eq_zero.mp h₁.symm
  have h₃ : ‖E Δ ψ‖ = 0 := by nlinarith [norm_nonneg (E Δ ψ)]
  simpa using h₃
theorem null_of_proj_eq_zero (E : BorelPVM J H) (Δ : MeasSubset J)
    (h : E Δ = 0) (ψ : H) : E.quadMeasure ψ Δ.1 = 0 := by
  rw [E.quadMeasure_apply ψ Δ, h]
  simp
def timeFn (p : SpectralDomain J) : ℂ := ((p.1 : ℝ) : ℂ)
def phaseFn (l : J) (p : SpectralDomain J) : ℂ := (p.2 l : ℂ)
theorem continuous_timeFn : Continuous (timeFn (J := J)) := by
  unfold timeFn
  fun_prop
theorem continuous_phaseFn (l : J) : Continuous (phaseFn (J := J) l) := by
  unfold phaseFn
  fun_prop
def siteDefect (l : J) (p : SpectralDomain J) : ℝ :=
  (1 - (p.1 : ℝ)) ^ 2 - (p.1 : ℝ) * ‖1 - (p.2 l : ℂ)‖ ^ 2
theorem continuous_siteDefect (l : J) : Continuous (siteDefect (J := J) l) := by
  unfold siteDefect
  fun_prop
theorem measurable_siteDefect (l : J) : Measurable (siteDefect (J := J) l) :=
  (continuous_siteDefect l).measurable
theorem isBddMeasurable_siteDefect (l : J) : IsBddMeasurable fun p : SpectralDomain J =>
    (siteDefect l p : ℂ) :=
  isBddMeasurable_of_continuous (Complex.continuous_ofReal.comp (continuous_siteDefect l))
variable {S : CommutingFamily H J} {E : BorelPVM J H}
theorem spectralOp_siteDefect (hj : IsJointPVM S E) (hb : BoundedFunctionalCalculus S E)
    (l : J) :
    E.spectralOp (fun p => (siteDefect l p : ℂ)) =
      (1 - S.A) ^ 2 - S.A * ((2 : ℂ) • 1 - (S.B l : H →L[ℂ] H) - star (S.B l : H →L[ℂ] H)) := by
  have bτ : IsBddMeasurable (timeFn (J := J)) :=
    isBddMeasurable_of_continuous continuous_timeFn
  have bζ : IsBddMeasurable (phaseFn (J := J) l) :=
    isBddMeasurable_of_continuous (continuous_phaseFn l)
  have bζ' : IsBddMeasurable fun p : SpectralDomain J => conj (phaseFn l p) :=
    isBddMeasurable_of_continuous (Complex.continuous_conj.comp (continuous_phaseFn l))
  have b1 : IsBddMeasurable fun _ : SpectralDomain J => (1 : ℂ) :=
    isBddMeasurable_of_continuous continuous_const
  have hτ : E.spectralOp timeFn = S.A := spectralOp_eq hj.1
  have hζ : E.spectralOp (phaseFn l) = (S.B l : H →L[ℂ] H) := spectralOp_eq (hj.2 l)
  have hζ' : E.spectralOp (fun p => conj (phaseFn l p)) = star (S.B l : H →L[ℂ] H) := by
    ext ψ
    refine ext_inner_right ℂ fun χ => ?_
    rw [← hb.inner_spectralOp _ bζ, hζ, ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.adjoint_inner_left]
  have h1 : E.spectralOp (fun _ => (1 : ℂ)) = 1 := by
    have h := spectralOp_eq (isSpectralIntegral_indicator E ⟨univ, MeasurableSet.univ⟩)
    rw [show E ⟨univ, MeasurableSet.univ⟩ = 1 from E.proj_univ] at h
    simpa using h
  have bg1 := isBddMeasurable_add_mul b1 bτ (-1)
  have b3 := isBddMeasurable_add_mul b1 b1 1
  have b4 := isBddMeasurable_add_mul b3 bζ (-1)
  have b5 := isBddMeasurable_add_mul b4 bζ' (-1)
  have a1 : E.spectralOp (fun p => 1 + (-1 : ℂ) * timeFn p) = 1 - S.A :=
    (hb.spectralOp_add_smul (fun _ => 1) timeFn b1 bτ (-1)).trans
      (by rw [h1, hτ]; simp [sub_eq_add_neg])
  have a2 : E.spectralOp (fun p => (1 + (-1 : ℂ) * timeFn p) *
      (1 + (-1 : ℂ) * timeFn p)) = (1 - S.A) ^ 2 :=
    (hb.spectralOp_mul _ _ bg1 bg1).trans (by rw [a1, sq])
  have a3 : E.spectralOp (fun _ => (1 : ℂ) + 1 * 1) = (2 : ℂ) • 1 :=
    (hb.spectralOp_add_smul (fun _ => 1) (fun _ => 1) b1 b1 1).trans
      (by rw [h1]; simp [two_smul])
  have a4 : E.spectralOp (fun p => ((1 : ℂ) + 1 * 1) + (-1) * phaseFn l p) =
      (2 : ℂ) • 1 - (S.B l : H →L[ℂ] H) :=
    (hb.spectralOp_add_smul (fun _ => (1 : ℂ) + 1 * 1) (phaseFn l) b3 bζ (-1)).trans
      (by rw [a3, hζ]; simp [sub_eq_add_neg])
  have a5 : E.spectralOp (fun p => (((1 : ℂ) + 1 * 1) + (-1) * phaseFn l p) +
      (-1) * conj (phaseFn l p)) =
      (2 : ℂ) • 1 - (S.B l : H →L[ℂ] H) - star (S.B l : H →L[ℂ] H) :=
    (hb.spectralOp_add_smul (fun p => ((1 : ℂ) + 1 * 1) + (-1) * phaseFn l p)
      (fun p => conj (phaseFn l p)) b4 bζ' (-1)).trans
      (by rw [a4, hζ']; simp [sub_eq_add_neg])
  have a6 : E.spectralOp (fun p => timeFn p * ((((1 : ℂ) + 1 * 1) + (-1) * phaseFn l p) +
      (-1) * conj (phaseFn l p))) =
      S.A * ((2 : ℂ) • 1 - (S.B l : H →L[ℂ] H) - star (S.B l : H →L[ℂ] H)) :=
    (hb.spectralOp_mul _ _ bτ b5).trans (by rw [hτ, a5])
  have a7 := (hb.spectralOp_add_smul _ _ (isBddMeasurable_mul bg1 bg1)
    (isBddMeasurable_mul bτ b5) (-1)).trans (by rw [a2, a6]; simp [sub_eq_add_neg] :
      _ = (1 - S.A) ^ 2 - S.A * ((2 : ℂ) • 1 - (S.B l : H →L[ℂ] H) - star (S.B l : H →L[ℂ] H)))
  refine Eq.trans (congrArg E.spectralOp (funext fun p => ?_)) a7
  have hn : ((‖1 - phaseFn l p‖ : ℝ) : ℂ) ^ 2 = (1 - phaseFn l p) * (1 - conj (phaseFn l p)) := by
    rw [← Complex.mul_conj', map_sub, map_one]
  have hc : phaseFn l p * conj (phaseFn l p) = 1 := by
    rw [Complex.mul_conj', phaseFn, Circle.norm_coe]
    simp
  simp only [siteDefect]
  change ((((1 - (p.1 : ℝ)) ^ 2 - (p.1 : ℝ) * ‖1 - phaseFn l p‖ ^ 2 : ℝ)) : ℂ) = _
  push_cast
  simp only [timeFn]
  linear_combination (-((p.1 : ℝ) : ℂ)) * hn + (-((p.1 : ℝ) : ℂ)) * hc
def negativeDefectSet (l : J) : MeasSubset J :=
  ⟨{p | 0 ≤ siteDefect l p}ᶜ, (measurableSet_le measurable_const (measurable_siteDefect l)).compl⟩
theorem spectralOp_siteDefect_split (hb : BoundedFunctionalCalculus S E) (l : J) :
    E.spectralOp (fun p => (siteDefect l p : ℂ)) = E (levelZeroSet J) +
      E (positiveLevelSet J) * E.spectralOp (fun p => (siteDefect l p : ℂ)) *
        E (positiveLevelSet J) := by
  set i₀ : SpectralDomain J → ℂ := (levelZeroSet J).1.indicator fun _ => (1 : ℂ) with hi₀
  set iP : SpectralDomain J → ℂ :=
    (positiveLevelSet J).1.indicator fun _ => (1 : ℂ) with hiP
  have b₀ : IsBddMeasurable i₀ := isBddMeasurable_indicator _
  have bP : IsBddMeasurable iP := isBddMeasurable_indicator _
  have bd := isBddMeasurable_siteDefect (J := J) l
  have e₀ : E.spectralOp i₀ = E (levelZeroSet J) :=
    spectralOp_eq (isSpectralIntegral_indicator E _)
  have eP : E.spectralOp iP = E (positiveLevelSet J) :=
    spectralOp_eq (isSpectralIntegral_indicator E _)
  have hmul := hb.spectralOp_mul _ _ (isBddMeasurable_mul bP bd) bP
  rw [hb.spectralOp_mul _ _ bP bd, eP] at hmul
  rw [← hmul, ← e₀]
  have hadd := hb.spectralOp_add_smul i₀ (fun p => iP p * (siteDefect l p : ℂ) * iP p) b₀
    (isBddMeasurable_mul (isBddMeasurable_mul bP bd) bP) 1
  rw [one_smul] at hadd
  rw [← hadd]
  refine congrArg E.spectralOp (funext fun p => ?_)
  by_cases h : (p.1 : ℝ) = 0
  · have h₀ : p ∈ (levelZeroSet J).1 := Subtype.ext h
    have hP : p ∉ (positiveLevelSet J).1 := fun hp => by
      have hp' : 0 < (p.1 : ℝ) := hp
      exact hp'.ne' h
    have hd : siteDefect l p = 1 := by simp [siteDefect, h]
    simp [hi₀, hiP, h₀, hP, hd]
  · have h₀ : p ∉ (levelZeroSet J).1 := fun hp => h (congrArg Subtype.val hp)
    have hP : p ∈ (positiveLevelSet J).1 := lt_of_le_of_ne p.1.2.1 (Ne.symm h)
    simp [hi₀, hiP, h₀, hP]
theorem proj_negativeDefectSet {H' : Type} [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
    [CompleteSpace H'] {S' : CommutingFamily H' J} {E' : BorelPVM J H'}
    (hb : BoundedFunctionalCalculus S E) (hr : RealFunctionalCalculus E)
    (hj' : IsJointPVM S' E') (hb' : BoundedFunctionalCalculus S' E')
    (W : H' →L[ℂ] H) (hW : ∀ ψ ψ', inner ℂ (W ψ) (W ψ') = inner ℂ ψ ψ')
    (hWE : ∀ φ, IsBddMeasurable φ → W ∘L E'.spectralOp φ = E.spectralOp φ ∘L W)
    (hran : ∀ ψ, ∃ ψ', W ψ' = E (positiveLevelSet J) ψ) (l : J)
    (hone : S'.A * ((2 : ℂ) • 1 - (S'.B l : H' →L[ℂ] H') - star (S'.B l : H' →L[ℂ] H')) ≤
      (1 - S'.A) ^ 2) : E (negativeDefectSet l) = 0 := by
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn
    (continuous_siteDefect (J := J) l).continuousOn
  have hreal := hr (siteDefect l) (measurable_siteDefect l) ⟨C, fun p => by
    simpa using hC p (mem_univ p)⟩
  refine hreal.2.mp ?_
  set B := E.spectralOp fun p => (siteDefect l p : ℂ) with hB
  have hB' : 0 ≤ E'.spectralOp fun p => (siteDefect l p : ℂ) := by
    rw [spectralOp_siteDefect hj' hb' l]
    exact sub_nonneg.mpr hone
  rw [le_iff_inner_sub_nonneg hreal.1 (IsSelfAdjoint.zero _)]
  intro ψ
  rw [sub_zero]
  obtain ⟨ψ', hψ'⟩ := hran ψ
  set P := E (positiveLevelSet J) with hP
  have hs := (isSelfAdjoint_iff_inner_eq P).mp (E.isStarProj _).isSelfAdjoint
  have hsplit : inner ℂ ψ (B ψ) = ((‖E (levelZeroSet J) ψ‖ ^ 2 : ℝ) : ℂ) +
      inner ℂ (P ψ) (B (P ψ)) := by
    have h₁ : B ψ = E (levelZeroSet J) ψ + P (B (P ψ)) :=
      congrArg (fun A : H →L[ℂ] H => A ψ) (spectralOp_siteDefect_split hb l)
    calc inner ℂ ψ (B ψ) = inner ℂ ψ (E (levelZeroSet J) ψ + P (B (P ψ))) := by rw [← h₁]
      _ = _ := by rw [inner_add_right, E.inner_apply_eq_norm_sq, hs]
  have hlink : inner ℂ (P ψ) (B (P ψ)) =
      inner ℂ ψ' ((E'.spectralOp fun p => (siteDefect l p : ℂ)) ψ') := by
    have h₂ : W ((E'.spectralOp fun p => (siteDefect l p : ℂ)) ψ') = B (W ψ') :=
      congrArg (fun A : H' →L[ℂ] H => A ψ') (hWE _ (isBddMeasurable_siteDefect l))
    rw [← hψ', ← h₂, hW]
  rw [hsplit, hlink]
  refine add_nonneg ?_ (((ContinuousLinearMap.nonneg_iff_isPositive _).mp hB').inner_nonneg_right ψ')
  exact_mod_cast (by positivity : (0 : ℝ) ≤ ‖E (levelZeroSet J) ψ‖ ^ 2)
theorem phaseFn_eq_one {l : J} {p : SpectralDomain J} (ht : p.1 = 1) (hp : 0 ≤ siteDefect l p) :
    phaseFn l p = 1 := by
  have h : (1 - ((1 : unitInterval) : ℝ)) ^ 2 - ((1 : unitInterval) : ℝ) *
      ‖1 - (p.2 l : ℂ)‖ ^ 2 ≥ 0 := by
    have := hp
    rw [siteDefect, ht] at this
    exact this
  simp only [Set.Icc.coe_one, sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    one_mul, zero_sub, ge_iff_le, Left.nonneg_neg_iff] at h
  have h₀ : ‖1 - (p.2 l : ℂ)‖ = 0 := by nlinarith [norm_nonneg (1 - (p.2 l : ℂ))]
  have h₁ : 1 - (p.2 l : ℂ) = 0 := norm_eq_zero.mp h₀
  exact (sub_eq_zero.mp h₁).symm
theorem phase_mul_levelOne (hj : IsJointPVM S E) (hb : BoundedFunctionalCalculus S E) (l : J)
    (hz : E (negativeDefectSet l) = 0) :
    (S.B l : H →L[ℂ] H) * E (levelOneSet J) = E (levelOneSet J) ∧
      E (levelOneSet J) * (S.B l : H →L[ℂ] H) = E (levelOneSet J) := by
  set ind : SpectralDomain J → ℂ := (levelOneSet J).1.indicator fun _ => (1 : ℂ) with hind
  have bind : IsBddMeasurable ind := isBddMeasurable_indicator _
  have bζ : IsBddMeasurable (phaseFn (J := J) l) :=
    isBddMeasurable_of_continuous (continuous_phaseFn l)
  have hi : E.spectralOp ind = E (levelOneSet J) :=
    spectralOp_eq (isSpectralIntegral_indicator E _)
  have hζ : E.spectralOp (phaseFn l) = (S.B l : H →L[ℂ] H) := spectralOp_eq (hj.2 l)
  have off : ∀ p, p ∉ (negativeDefectSet (J := J) l).1 → phaseFn l p * ind p = ind p :=
    fun p hp => by
    have hp' : 0 ≤ siteDefect l p := by simpa [negativeDefectSet] using hp
    by_cases h : p ∈ (levelOneSet J).1
    · have : p.1 = 1 := h
      rw [phaseFn_eq_one this hp', one_mul]
    · simp [hind, h]
  have c₁ : E.spectralOp (fun p => phaseFn l p * ind p) = E.spectralOp ind :=
    hb.spectralOp_congr _ _ (isBddMeasurable_mul bζ bind) bind _ hz off
  have c₂ : E.spectralOp (fun p => ind p * phaseFn l p) = E.spectralOp ind :=
    hb.spectralOp_congr _ _ (isBddMeasurable_mul bind bζ) bind _ hz fun p hp => by
      rw [mul_comm]
      exact off p hp
  constructor
  · rw [← hζ, ← hi, ← hb.spectralOp_mul _ _ bζ bind]
    exact c₁
  · rw [← hζ, ← hi, ← hb.spectralOp_mul _ _ bind bζ]
    exact c₂
end Calculus
section Carrier
variable (μ : Fin 4)
theorem fromSpectrum_mem_variableDomain (q : SpectralDomain (TransverseAxis μ)) :
    fromSpectrum μ q ∈ variableDomain μ :=
  fun _ => ⟨Complex.neg_pi_lt_arg _, Complex.arg_le_pi _⟩
theorem toSpectrum_fromSpectrum (q : SpectralDomain (TransverseAxis μ)) :
    toSpectrum μ (fromSpectrum μ q) = q :=
  Prod.ext (expNegEnergy_energyOfUnit _) (funext fun _ => Circle.exp_arg _)
theorem siteDefect_toSpectrum (x : ℝ≥0∞ × (TransverseAxis μ → ℝ)) (l : TransverseAxis μ) :
    siteDefect l (toSpectrum μ x) =
      (1 - ((expNegEnergy x.1 : unitInterval) : ℝ)) ^ 2 -
        ((expNegEnergy x.1 : unitInterval) : ℝ) *
          ‖1 - Complex.exp (Complex.I * (x.2 l : ℂ))‖ ^ 2 := by
  simp only [siteDefect, toSpectrum, Circle.coe_exp, mul_comm Complex.I]
theorem mem_imageInSpectrum_iff (q : SpectralDomain (TransverseAxis μ)) :
    q ∈ imageInSpectrum μ (siteCone μ) ↔ ∀ l, 0 ≤ siteDefect l q := by
  constructor
  · rintro ⟨x, ⟨⟨-, hc⟩, -⟩, rfl⟩ l
    rw [siteDefect_toSpectrum]
    exact sub_nonneg.mpr (hc l)
  · intro h
    have hdom := fromSpectrum_mem_variableDomain μ q
    refine ⟨fromSpectrum μ q, ⟨⟨hdom, fun l => ?_⟩, hdom⟩,
      toSpectrum_fromSpectrum μ q⟩
    have h' : 0 ≤ siteDefect l (toSpectrum μ (fromSpectrum μ q)) := by
      rw [toSpectrum_fromSpectrum]
      exact h l
    rw [siteDefect_toSpectrum] at h'
    exact sub_nonneg.mp h'
theorem imageInSpectrum_eq : imageInSpectrum μ (siteCone μ) =
    ⋂ l : TransverseAxis μ, {q | 0 ≤ siteDefect l q} := by
  ext q
  simp [mem_imageInSpectrum_iff]
theorem isClosed_imageInSpectrum : IsClosed (imageInSpectrum μ (siteCone μ)) := by
  rw [imageInSpectrum_eq]
  exact isClosed_iInter fun l => isClosed_le continuous_const (continuous_siteDefect l)
theorem compl_imageInSpectrum_eq : (imageInSpectrum μ (siteCone μ))ᶜ =
    ⋃ l : TransverseAxis μ, (negativeDefectSet l).1 := by
  rw [imageInSpectrum_eq, compl_iInter]
  rfl
variable {μ}
theorem curve_consequences (hCurve : SpectralCurve.CurveFacts)
    {x : ℝ≥0∞ × (TransverseAxis μ → ℝ)} (hx : x ∈ siteCone μ) (htop : x.1 ≠ ⊤)
    (l : TransverseAxis μ) :
    Real.cosh x.1.toReal + Real.cos (x.2 l) ≥ 2 ∧ x.1.toReal ≥ slopeConstant * |x.2 l| ∧
      (x.1.toReal = 0 → x.2 l = 0) := by
  obtain ⟨hd, hc⟩ := hx
  have hval : ((expNegEnergy x.1 : unitInterval) : ℝ) = Real.exp (-x.1.toReal) := by
    simp [expNegEnergy, htop]
  have hon : SpectralCurve.AboveCurve (SpectralCurve.expNegEnergy x.1.toReal)
      (SpectralCurve.phaseOf (x.2 l)) := by
    have := hc l
    rw [hval] at this
    exact this
  obtain ⟨hforms, -, habove⟩ := hCurve x.1.toReal (x.2 l) 1 ENNReal.toReal_nonneg le_rfl
  obtain ⟨h₁, h₂, h₃⟩ := habove hon (abs_le.mpr ⟨(hd l).1.le, (hd l).2⟩)
  refine ⟨?_, h₂.le.trans h₁, h₃⟩
  have hw : 0 < SpectralCurve.expNegEnergy x.1.toReal := Real.exp_pos _
  have hf := hforms.1
  have hnn : 0 ≤ 2 * SpectralCurve.expNegEnergy x.1.toReal *
      (Real.cosh x.1.toReal + Real.cos (x.2 l) - 2) := by
    rw [← hf]
    exact sub_nonneg.mpr hon
  have := nonneg_of_mul_nonneg_right hnn (by positivity)
  linarith
end Carrier
theorem siteCarrierFacts_holds
    (hCurve : SpectralCurve.CurveFacts)
    (hLink : LinkPictureEmbedsInSitePicture)
    (hOne : OneStepEnergyMomentumLink)
    (hPic : ReflectionPairTheorem)
    (hSpec : JointSpectralCalculusTheorem) :
    SiteCarrierFacts := by
  intro ν μ
  obtain ⟨-, -, -, -, hj, htopP, -⟩ := hPic ν μ ReflectionPair.site
  obtain ⟨-, -, -, -, hj', -, -⟩ := hPic ν μ ReflectionPair.link
  obtain ⟨-, -, hall⟩ := hSpec (ReflectionPair.site.Hilb ν μ) (TransverseAxis μ)
    (ReflectionPair.site.opFamily ν μ)
  obtain ⟨-, -, hall'⟩ := hSpec (ReflectionPair.link.Hilb ν μ) (TransverseAxis μ)
    (ReflectionPair.link.opFamily ν μ)
  obtain ⟨-, hb, -, hr, hk, hroot, htrans⟩ := hall _ hj
  obtain ⟨-, hb', -, -, -, -, -⟩ := hall' _ hj'
  obtain ⟨-, -, ⟨-, hW, hWT, hWU⟩, -⟩ := hLink ν μ
  let W₀ := LinearMap.isometryOfInner (linkSiteIntertwiner ν μ) hW.1.2
  let W : ReflectionPair.link.Hilb ν μ →L[ℂ] ReflectionPair.site.Hilb ν μ :=
    (transferKernelOrth ν μ).subtypeL ∘L W₀.toContinuousLinearMap
  have hWapp : ∀ ψ, W ψ = (linkSiteIntertwiner ν μ ψ : ReflectionPair.site.Hilb ν μ) :=
    fun _ => rfl
  have hWi : ∀ ψ ψ', inner ℂ (W ψ) (W ψ') = inner ℂ ψ ψ' := fun ψ ψ' => hW.1.2 ψ ψ'
  have hint : IntertwinesIsometrically (ReflectionPair.site.opFamily ν μ)
      (ReflectionPair.link.opFamily ν μ) W :=
    ⟨hWi, ContinuousLinearMap.ext fun ψ => hWT ψ,
      fun l => ContinuousLinearMap.ext fun ψ => hWU l ψ⟩
  have hWE := (htrans _ _ _ hj' W hint).2
  have hran : ∀ ψ, ∃ ψ', W ψ' =
      ReflectionPair.site.jointPVM ν μ (positiveLevelSet (TransverseAxis μ)) ψ := by
    intro ψ
    have hm : ReflectionPair.site.jointPVM ν μ (positiveLevelSet (TransverseAxis μ)) ψ ∈
        (transferKernelOrth ν μ : Set (ReflectionPair.site.Hilb ν μ)) := by
      rw [coe_transferKernelOrth]
      have := hroot.positiveLevel_range
      exact this ▸ mem_range_self ψ
    obtain ⟨ψ', hψ'⟩ := hW.1.1.2 ⟨_, hm⟩
    exact ⟨ψ', congrArg Subtype.val hψ'⟩
  have hneg : ∀ l, ReflectionPair.site.jointPVM ν μ (negativeDefectSet l) = 0 :=
    fun l => proj_negativeDefectSet hb hr hj' hb' W hWi hWE hran l (hOne ν μ l).2.2
  have hFixed : ∀ ψ, ReflectionPair.site.transferOp ν μ
      (groundProjection μ ReflectionPair.site ν ψ) =
      groundProjection μ ReflectionPair.site ν ψ := by
    intro ψ
    have hm : groundProjection μ ReflectionPair.site ν ψ ∈
        {ψ | (1 - ReflectionPair.site.transferOp ν μ) ψ = 0} := htopP.2 ▸ mem_range_self ψ
    have h₀ : groundProjection μ ReflectionPair.site ν ψ -
        ReflectionPair.site.transferOp ν μ (groundProjection μ ReflectionPair.site ν ψ) = 0 := hm
    exact (sub_eq_zero.mp h₀).symm
  refine ⟨⟨isClosed_imageInSpectrum μ, ?_⟩, fun x hx => ⟨fun h0 => ?_, fun htop => ⟨fun l => ?_, ?_⟩⟩,
    fun l => phase_mul_levelOne hj hb l (hneg l), fun n => ?_, hk.tendsto_pow⟩
  · refine proj_eq_zero_of_null _ _ fun ψ => ?_
    change (ReflectionPair.site.jointPVM ν μ).quadMeasure ψ
      (imageInSpectrum μ (siteCone μ))ᶜ = 0
    rw [compl_imageInSpectrum_eq]
    exact measure_iUnion_null fun l => null_of_proj_eq_zero _ _ (hneg l) ψ
  · have htop : x.1 ≠ ⊤ := by simp [h0]
    refine funext fun l => (curve_consequences hCurve hx htop l).2.2 ?_
    simp [h0]
  · exact (curve_consequences hCurve hx htop l).1
  · obtain ⟨l, -, hl⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun l => |x.2 l|)
    rw [angleSupNorm, hl]
    exact (curve_consequences hCurve hx htop l).2.1
  · induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, mul_assoc]
      have : ReflectionPair.site.transferOp ν μ * groundProjection μ ReflectionPair.site ν =
          groundProjection μ ReflectionPair.site ν := ContinuousLinearMap.ext hFixed
      rw [this, ih]
end YangMills.Construction.ReflectionPositivity.SiteCarrier
