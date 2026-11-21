import YangMills.Construction.InfiniteLattice.UnitLatticeIsometriesAndPlaquettes
import YangMills.Construction.ReflectionPositivity.ActionOfTheLatticeIsometriesTheTwoFieldsAndTheReflections
import YangMills.Construction.ReflectionPositivity.CarrierOfTheSitePictureProof
import YangMills.Construction.ReflectionPositivity.ReflectionsCarrierAndZeroEnergyOfTheLinkPicture
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
open MeasureTheory Set
open scoped ComplexConjugate ENNReal Real
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.DirectionPictures.LinkConeGroundProof
open YangMills.Construction.InfiniteLattice (GaugeField IsBoundedObservable)
open YangMills.Construction.ReflectionPositivity.MirrorHyperplanes (unitPositiveClass UnitMirrorPair)
open YangMills.Construction.FormHilbert
open YangMills.Construction.JointSpectrum (CommutingFamily SpectralDomain)
open YangMills.Construction.ReflectionPositivity.DirectionPictures.SpectralCurve (phaseOf AboveCurve)
section CauchySchwarz
variable {X : Type*} [MeasurableSpace X] {m : Measure X} [IsFiniteMeasure m]
theorem norm_integral_conj_mul_le_sqrt_mul_sqrt {f g : X → ℂ} (hf : Measurable f)
    (hg : Measurable g) {a b : ℝ} (hfa : ∀ x, ‖f x‖ ≤ a) (hgb : ∀ x, ‖g x‖ ≤ b) :
    ‖∫ x, conj (f x) * g x ∂m‖ ≤ √(∫ x, ‖f x‖ ^ 2 ∂m) * √(∫ x, ‖g x‖ ^ 2 ∂m) := by
  have mem : ∀ {u : X → ℂ} {c : ℝ}, Measurable u → (∀ x, ‖u x‖ ≤ c) →
      MemLp (fun x => ‖u x‖) (ENNReal.ofReal 2) m := fun hu hc =>
    MemLp.of_bound hu.norm.aestronglyMeasurable _
      (Filter.Eventually.of_forall fun x => by simpa using hc x)
  have holder := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := m) Real.HolderConjugate.two_two
    (f := fun x => ‖f x‖) (g := fun x => ‖g x‖)
    (Filter.Eventually.of_forall fun x => norm_nonneg _)
    (Filter.Eventually.of_forall fun x => norm_nonneg _) (mem hf hfa) (mem hg hgb)
  simp only [Real.rpow_two] at holder
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
  refine (norm_integral_le_integral_norm _).trans (le_of_eq_of_le ?_ holder)
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp
end CauchySchwarz
section Calculus
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {J : Type} [Fintype J] [Nonempty J]
theorem isBddMeasurable_of_continuous {φ : SpectralDomain J → ℂ} (h : Continuous φ) :
    IsBddMeasurable φ := by apply _root_.YangMills.Construction.ReflectionPositivity.SiteCarrier.isBddMeasurable_of_continuous <;> assumption
theorem isBddMeasurable_mul {φ ψ : SpectralDomain J → ℂ} (h : IsBddMeasurable φ)
    (h' : IsBddMeasurable ψ) : IsBddMeasurable fun p => φ p * ψ p := by apply _root_.YangMills.Construction.ReflectionPositivity.SiteCarrier.isBddMeasurable_mul <;> assumption
theorem isBddMeasurable_add_const_mul {φ ψ : SpectralDomain J → ℂ} (h : IsBddMeasurable φ)
    (h' : IsBddMeasurable ψ) (c : ℂ) : IsBddMeasurable fun p => φ p + c * ψ p := by apply _root_.YangMills.Construction.ReflectionPositivity.SiteCarrier.isBddMeasurable_add_mul <;> assumption
theorem spectralOp_eq_of {E : BorelPVM J H} {φ : SpectralDomain J → ℂ}
    {A : H →L[ℂ] H} (hA : E.IsSpectralIntegral φ A) : E.spectralOp φ = A := by apply _root_.YangMills.Construction.ReflectionPositivity.SiteCarrier.spectralOp_eq <;> assumption
theorem isSpectralIntegral_indicator (E : BorelPVM J H) (Δ : MeasSubset J) :
    E.IsSpectralIntegral (Δ.1.indicator fun _ => (1 : ℂ)) (E Δ) := by apply _root_.YangMills.Construction.ReflectionPositivity.SiteCarrier.isSpectralIntegral_indicator <;> assumption
theorem proj_eq_zero_of_quadMeasure (E : BorelPVM J H) (Δ : MeasSubset J)
    (h : ∀ ψ, E.quadMeasure ψ Δ.1 = 0) : E Δ = 0 := by apply _root_.YangMills.Construction.ReflectionPositivity.SiteCarrier.proj_eq_zero_of_null <;> assumption
theorem quadMeasure_eq_zero_of_proj (E : BorelPVM J H) (Δ : MeasSubset J)
    (h : E Δ = 0) (ψ : H) : E.quadMeasure ψ Δ.1 = 0 := by apply _root_.YangMills.Construction.ReflectionPositivity.SiteCarrier.null_of_proj_eq_zero <;> assumption
def tCoord (p : SpectralDomain J) : ℂ := ((p.1 : ℝ) : ℂ)
def circleCoord (l : J) (p : SpectralDomain J) : ℂ := (p.2 l : ℂ)
theorem continuous_tCoord : Continuous (tCoord (J := J)) := by apply _root_.YangMills.Construction.ReflectionPositivity.SiteCarrier.continuous_timeFn <;> assumption
theorem continuous_circleCoord (l : J) : Continuous (circleCoord (J := J) l) := by apply _root_.YangMills.Construction.ReflectionPositivity.SiteCarrier.continuous_phaseFn <;> assumption
def stepDefect (l : J) (p : SpectralDomain J) : ℝ :=
  (1 - (p.1 : ℝ)) ^ 2 - (p.1 : ℝ) * ‖1 - (p.2 l : ℂ)‖ ^ 2
theorem continuous_stepDefect (l : J) : Continuous (stepDefect (J := J) l) := by
  unfold stepDefect
  fun_prop
variable {S : CommutingFamily H J} {E : BorelPVM J H}
theorem spectralOp_stepDefect (hj : IsJointPVM S E) (hb : BoundedFunctionalCalculus S E)
    (l : J) :
    E.spectralOp (fun p => (stepDefect l p : ℂ)) =
      (1 - S.A) ^ 2 - S.A * ((2 : ℂ) • 1 - (S.B l : H →L[ℂ] H) - star (S.B l : H →L[ℂ] H)) := by
  have bt : IsBddMeasurable (tCoord (J := J)) :=
    isBddMeasurable_of_continuous continuous_tCoord
  have bz : IsBddMeasurable (circleCoord (J := J) l) :=
    isBddMeasurable_of_continuous (continuous_circleCoord l)
  have bz' : IsBddMeasurable fun p : SpectralDomain J => conj (circleCoord l p) :=
    isBddMeasurable_of_continuous (Complex.continuous_conj.comp (continuous_circleCoord l))
  have b1 : IsBddMeasurable fun _ : SpectralDomain J => (1 : ℂ) :=
    isBddMeasurable_of_continuous continuous_const
  have ht : E.spectralOp tCoord = S.A := spectralOp_eq_of hj.1
  have hz : E.spectralOp (circleCoord l) = (S.B l : H →L[ℂ] H) := spectralOp_eq_of (hj.2 l)
  have hz' : E.spectralOp (fun p => conj (circleCoord l p)) = star (S.B l : H →L[ℂ] H) := by
    ext ψ
    refine ext_inner_right ℂ fun χ => ?_
    rw [← hb.inner_spectralOp _ bz, hz, ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.adjoint_inner_left]
  have h1 : E.spectralOp (fun _ => (1 : ℂ)) = 1 := by
    have h := spectralOp_eq_of (isSpectralIntegral_indicator E ⟨univ, MeasurableSet.univ⟩)
    rw [show E ⟨univ, MeasurableSet.univ⟩ = 1 from E.proj_univ] at h
    simpa using h
  have bg1 := isBddMeasurable_add_const_mul b1 bt (-1)
  have b3 := isBddMeasurable_add_const_mul b1 b1 1
  have b4 := isBddMeasurable_add_const_mul b3 bz (-1)
  have b5 := isBddMeasurable_add_const_mul b4 bz' (-1)
  have e1 : E.spectralOp (fun p => 1 + (-1 : ℂ) * tCoord p) = 1 - S.A :=
    (hb.spectralOp_add_smul (fun _ => 1) tCoord b1 bt (-1)).trans
      (by rw [h1, ht]; simp [sub_eq_add_neg])
  have e2 : E.spectralOp (fun p => (1 + (-1 : ℂ) * tCoord p) *
      (1 + (-1 : ℂ) * tCoord p)) = (1 - S.A) ^ 2 :=
    (hb.spectralOp_mul _ _ bg1 bg1).trans (by rw [e1, sq])
  have e3 : E.spectralOp (fun _ => (1 : ℂ) + 1 * 1) = (2 : ℂ) • 1 :=
    (hb.spectralOp_add_smul (fun _ => 1) (fun _ => 1) b1 b1 1).trans
      (by rw [h1]; simp [two_smul])
  have e4 : E.spectralOp (fun p => ((1 : ℂ) + 1 * 1) + (-1) * circleCoord l p) =
      (2 : ℂ) • 1 - (S.B l : H →L[ℂ] H) :=
    (hb.spectralOp_add_smul (fun _ => (1 : ℂ) + 1 * 1) (circleCoord l) b3 bz (-1)).trans
      (by rw [e3, hz]; simp [sub_eq_add_neg])
  have e5 : E.spectralOp (fun p => (((1 : ℂ) + 1 * 1) + (-1) * circleCoord l p) +
      (-1) * conj (circleCoord l p)) =
      (2 : ℂ) • 1 - (S.B l : H →L[ℂ] H) - star (S.B l : H →L[ℂ] H) :=
    (hb.spectralOp_add_smul (fun p => ((1 : ℂ) + 1 * 1) + (-1) * circleCoord l p)
      (fun p => conj (circleCoord l p)) b4 bz' (-1)).trans
      (by rw [e4, hz']; simp [sub_eq_add_neg])
  have e6 : E.spectralOp (fun p => tCoord p * ((((1 : ℂ) + 1 * 1) + (-1) * circleCoord l p) +
      (-1) * conj (circleCoord l p))) =
      S.A * ((2 : ℂ) • 1 - (S.B l : H →L[ℂ] H) - star (S.B l : H →L[ℂ] H)) :=
    (hb.spectralOp_mul _ _ bt b5).trans (by rw [ht, e5])
  have e7 := (hb.spectralOp_add_smul _ _ (isBddMeasurable_mul bg1 bg1)
    (isBddMeasurable_mul bt b5) (-1)).trans (by rw [e2, e6]; simp [sub_eq_add_neg] :
      _ = (1 - S.A) ^ 2 - S.A * ((2 : ℂ) • 1 - (S.B l : H →L[ℂ] H) - star (S.B l : H →L[ℂ] H)))
  refine Eq.trans (congrArg E.spectralOp (funext fun p => ?_)) e7
  have hn : ((‖1 - circleCoord l p‖ : ℝ) : ℂ) ^ 2 =
      (1 - circleCoord l p) * (1 - conj (circleCoord l p)) := by
    rw [← Complex.mul_conj', map_sub, map_one]
  have hc : circleCoord l p * conj (circleCoord l p) = 1 := by
    rw [Complex.mul_conj', circleCoord, Circle.norm_coe]
    simp
  simp only [stepDefect]
  change ((((1 - (p.1 : ℝ)) ^ 2 - (p.1 : ℝ) * ‖1 - circleCoord l p‖ ^ 2 : ℝ)) : ℂ) = _
  push_cast
  simp only [tCoord]
  linear_combination (-((p.1 : ℝ) : ℂ)) * hn + (-((p.1 : ℝ) : ℂ)) * hc
theorem measurable_stepDefect (l : J) : Measurable (stepDefect (J := J) l) :=
  (continuous_stepDefect l).measurable
def stepDefectNegSet (l : J) : MeasSubset J :=
  ⟨{p | 0 ≤ stepDefect l p}ᶜ, (measurableSet_le measurable_const (measurable_stepDefect l)).compl⟩
theorem proj_stepDefectNegSet (hj : IsJointPVM S E) (hb : BoundedFunctionalCalculus S E)
    (hr : RealFunctionalCalculus E) (l : J)
    (hone : S.A * ((2 : ℂ) • 1 - (S.B l : H →L[ℂ] H) - star (S.B l : H →L[ℂ] H)) ≤
      (1 - S.A) ^ 2) : E (stepDefectNegSet l) = 0 := by
  have hpos : 0 ≤ E.spectralOp fun p => (stepDefect l p : ℂ) := by
    rw [spectralOp_stepDefect hj hb l]
    exact sub_nonneg.mpr hone
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn
    (continuous_stepDefect (J := J) l).continuousOn
  exact ((hr (stepDefect l) (measurable_stepDefect l) ⟨C, fun p => by
    simpa using hC p (mem_univ p)⟩).2.mp hpos)
theorem circleCoord_eq_one_of_top {l : J} {p : SpectralDomain J} (ht : p.1 = 1)
    (hp : 0 ≤ stepDefect l p) : circleCoord l p = 1 := by
  have h : (1 - ((1 : unitInterval) : ℝ)) ^ 2 - ((1 : unitInterval) : ℝ) *
      ‖1 - (p.2 l : ℂ)‖ ^ 2 ≥ 0 := by
    have := hp
    rw [stepDefect, ht] at this
    exact this
  simp only [Set.Icc.coe_one, sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    one_mul, zero_sub, ge_iff_le, Left.nonneg_neg_iff] at h
  have h₀ : ‖1 - (p.2 l : ℂ)‖ = 0 := by nlinarith [norm_nonneg (1 - (p.2 l : ℂ))]
  have h₁ : 1 - (p.2 l : ℂ) = 0 := norm_eq_zero.mp h₀
  exact (sub_eq_zero.mp h₁).symm
theorem circleOp_mul_levelOne (hj : IsJointPVM S E) (hb : BoundedFunctionalCalculus S E)
    (l : J) (hz : E (stepDefectNegSet l) = 0) :
    (S.B l : H →L[ℂ] H) * E (levelOneSet J) = E (levelOneSet J) ∧
      E (levelOneSet J) * (S.B l : H →L[ℂ] H) = E (levelOneSet J) := by
  set ind : SpectralDomain J → ℂ := (levelOneSet J).1.indicator fun _ => (1 : ℂ) with hind
  have bind : IsBddMeasurable ind := by
    refine ⟨measurable_const.indicator (levelOneSet J).2, 1, fun p => ?_⟩
    by_cases h : p ∈ (levelOneSet J).1 <;> simp [hind, h]
  have bz : IsBddMeasurable (circleCoord (J := J) l) :=
    isBddMeasurable_of_continuous (continuous_circleCoord l)
  have hi : E.spectralOp ind = E (levelOneSet J) :=
    spectralOp_eq_of (isSpectralIntegral_indicator E _)
  have hzeta : E.spectralOp (circleCoord l) = (S.B l : H →L[ℂ] H) := spectralOp_eq_of (hj.2 l)
  have off : ∀ p, p ∉ (stepDefectNegSet (J := J) l).1 → circleCoord l p * ind p = ind p :=
    fun p hp => by
      have hp' : 0 ≤ stepDefect l p := by simpa [stepDefectNegSet] using hp
      by_cases h : p ∈ (levelOneSet J).1
      · have : p.1 = 1 := h
        rw [circleCoord_eq_one_of_top this hp', one_mul]
      · simp [hind, h]
  have c₁ : E.spectralOp (fun p => circleCoord l p * ind p) = E.spectralOp ind :=
    hb.spectralOp_congr _ _ (isBddMeasurable_mul bz bind) bind _ hz off
  have c₂ : E.spectralOp (fun p => ind p * circleCoord l p) = E.spectralOp ind :=
    hb.spectralOp_congr _ _ (isBddMeasurable_mul bind bz) bind _ hz fun p hp => by
      rw [mul_comm]
      exact off p hp
  constructor
  · rw [← hzeta, ← hi, ← hb.spectralOp_mul _ _ bz bind]
    exact c₁
  · rw [← hzeta, ← hi, ← hb.spectralOp_mul _ _ bind bz]
    exact c₂
end Calculus
section Cone
variable (μ : Fin 4)
theorem slopeConstant_nonneg : 0 ≤ slopeConstant := by
  have h : 0 ≤ Real.log (1 + √2) :=
    Real.log_nonneg (by linarith [Real.sqrt_nonneg (2 : ℝ)])
  unfold slopeConstant
  positivity
theorem fromSpectrum_mem_variableDomain (q : SpectralDomain (TransverseAxis μ)) :
    fromSpectrum μ q ∈ variableDomain μ :=
  fun _ => ⟨Complex.neg_pi_lt_arg _, Complex.arg_le_pi _⟩
theorem toSpectrum_fromSpectrum (q : SpectralDomain (TransverseAxis μ)) :
    toSpectrum μ (fromSpectrum μ q) = q :=
  Prod.ext (expNegEnergy_energyOfUnit _) (funext fun _ => Circle.exp_arg _)
theorem mem_imageInSpectrum_linkCone_iff (q : SpectralDomain (TransverseAxis μ)) :
    q ∈ imageInSpectrum μ (linkCone μ) ↔
      ((q.1 : ℝ) ≠ 0 ∧ ∀ l, slopeConstant * |Complex.arg (q.2 l)| ≤ -Real.log q.1) := by
  constructor
  · rintro ⟨x, ⟨⟨hd, htop, hle⟩, -⟩, rfl⟩
    have hval : ((expNegEnergy x.1 : unitInterval) : ℝ) = Real.exp (-x.1.toReal) := by
      simp [expNegEnergy, htop]
    refine ⟨?_, fun l => ?_⟩
    · change ((expNegEnergy x.1 : unitInterval) : ℝ) ≠ 0
      rw [hval]
      exact (Real.exp_pos _).ne'
    · change slopeConstant * |Complex.arg (Circle.exp (x.2 l))| ≤
        -Real.log ((expNegEnergy x.1 : unitInterval) : ℝ)
      have ha : Complex.arg (Circle.exp (x.2 l)) = x.2 l := Circle.arg_exp (hd l).1 (hd l).2
      rw [hval, Real.log_exp, neg_neg, ha]
      refine (mul_le_mul_of_nonneg_left ?_ slopeConstant_nonneg).trans hle
      exact Finset.le_sup' (fun l => |x.2 l|) (Finset.mem_univ l)
  · rintro ⟨h0, hle⟩
    have hdom := fromSpectrum_mem_variableDomain μ q
    have hnn : 0 ≤ -Real.log (q.1 : ℝ) := neg_nonneg.mpr (Real.log_nonpos q.1.2.1 q.1.2.2)
    have he : (energyOfUnit q.1).toReal = -Real.log q.1 := by
      rw [energyOfUnit, if_neg h0, ENNReal.toReal_ofReal hnn]
    refine ⟨fromSpectrum μ q, ⟨⟨hdom, ?_, ?_⟩, hdom⟩, toSpectrum_fromSpectrum μ q⟩
    · change energyOfUnit q.1 ≠ ⊤
      simp [energyOfUnit, h0]
    · change slopeConstant * angleSupNorm μ (fun l => Complex.arg (q.2 l)) ≤
        (energyOfUnit q.1).toReal
      obtain ⟨l, -, hl⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
        (fun l => |Complex.arg (q.2 l)|)
      rw [angleSupNorm, hl, he]
      exact hle l
theorem measurableSet_imageInSpectrum_linkCone :
    MeasurableSet (imageInSpectrum μ (linkCone μ)) := by
  have h : imageInSpectrum μ (linkCone μ) = {q | (q.1 : ℝ) ≠ 0} ∩
      ⋂ l, {q | slopeConstant * |Complex.arg (q.2 l)| ≤ -Real.log q.1} := by
    ext q
    simp [mem_imageInSpectrum_linkCone_iff]
  rw [h]
  have mt : Measurable fun q : SpectralDomain (TransverseAxis μ) => (q.1 : ℝ) :=
    measurable_subtype_coe.comp measurable_fst
  refine MeasurableSet.inter ?_ (MeasurableSet.iInter fun l => measurableSet_le ?_ ?_)
  · exact (mt (measurableSet_singleton (0 : ℝ))).compl
  · have ma : Measurable fun q : SpectralDomain (TransverseAxis μ) =>
        Complex.arg (q.2 l) :=
      Complex.measurable_arg.comp
        ((by fun_prop : Continuous fun z : Circle => (z : ℂ)).measurable.comp
          ((measurable_pi_apply l).comp measurable_snd))
    exact (ma.abs).const_mul _
  · exact (Real.measurable_log.comp mt).neg
theorem compl_imageInSpectrum_linkCone_subset (hCurve : SpectralCurve.CurveFacts) :
    (imageInSpectrum μ (linkCone μ))ᶜ ⊆
      (spectrumBottom (TransverseAxis μ)).1 ∪ ⋃ l, (stepDefectNegSet l).1 := by
  intro q hq
  by_contra hcon
  simp only [mem_union, mem_iUnion, not_or, not_exists] at hcon
  obtain ⟨hb, hn⟩ := hcon
  apply hq
  have h0 : (q.1 : ℝ) ≠ 0 := fun h => hb (Subtype.ext h)
  have hpos : 0 < (q.1 : ℝ) := lt_of_le_of_ne q.1.2.1 (Ne.symm h0)
  have hnn : 0 ≤ -Real.log (q.1 : ℝ) := neg_nonneg.mpr (Real.log_nonpos q.1.2.1 q.1.2.2)
  refine (mem_imageInSpectrum_linkCone_iff μ q).mpr ⟨h0, fun l => ?_⟩
  have hd : 0 ≤ stepDefect l q := by simpa [stepDefectNegSet] using hn l
  have hw : SpectralCurve.expNegEnergy (-Real.log (q.1 : ℝ)) = q.1 := by
    rw [SpectralCurve.expNegEnergy, neg_neg, Real.exp_log hpos]
  have hph : phaseOf (Complex.arg (q.2 l)) = q.2 l := by
    have h := Complex.norm_mul_exp_arg_mul_I (q.2 l : ℂ)
    rw [Circle.norm_coe] at h
    rw [phaseOf, mul_comm]
    simpa using h
  have hon : AboveCurve (SpectralCurve.expNegEnergy (-Real.log (q.1 : ℝ)))
      (phaseOf (Complex.arg (q.2 l))) := by
    rw [hw, hph, AboveCurve]
    exact sub_nonneg.mp hd
  exact ((hCurve _ _ 1 hnn le_rfl).2.2 hon (Complex.abs_arg_le_pi _)).2.1.le.trans
    ((hCurve _ _ 1 hnn le_rfl).2.2 hon (Complex.abs_arg_le_pi _)).1
end Cone
theorem linkPictureReflectionsConeGround_holds
    (hAction : YangMills.Construction.ReflectionPositivity.MirrorHyperplanes.SymmetryActionAndReflections)
    (hCurve : SpectralCurve.CurveFacts)
    (hGroup : YangMills.Construction.InfiniteLattice.UnitSymmetriesAndFaces.Summary)
    (hLink : LinkPictureEmbedsInSitePicture)
    (hOne : OneStepEnergyMomentumLink)
    (hPic : ReflectionPairTheorem)
    (hSpec : JointSpectralCalculusTheorem) :
    LinkPictureReflectionsConeGround := by
  intro ν μ
  obtain ⟨-, -, -, -, hj, -, hbot⟩ := hPic ν μ ReflectionPair.link
  obtain ⟨-, -, hall⟩ := hSpec (ReflectionPair.link.Hilb ν μ) (TransverseAxis μ)
    (ReflectionPair.link.opFamily ν μ)
  obtain ⟨-, hb, -, hr, hk, -, -⟩ := hall _ hj
  have hinj : Function.Injective (ReflectionPair.link.transferOp ν μ) := (hLink ν μ).2.2.2
  have hneg : ∀ l, ReflectionPair.link.jointPVM ν μ (stepDefectNegSet l) = 0 :=
    fun l => proj_stepDefectNegSet hj hb hr l (hOne ν μ l).2.2
  have hE0 : ReflectionPair.link.jointPVM ν μ (spectrumBottom (TransverseAxis μ)) = 0 := by
    ext ψ
    have hm : ReflectionPair.link.jointPVM ν μ (spectrumBottom (TransverseAxis μ)) ψ ∈
        {ψ | ReflectionPair.link.transferOp ν μ ψ = 0} := hbot.2 ▸ mem_range_self ψ
    exact hinj (hm.trans (map_zero _).symm)
  refine ⟨fun P => ?_, ⟨hinj, hE0⟩, ⟨measurableSet_imageInSpectrum_linkCone μ, ?_⟩, ?_, ?_⟩
  · have hprob : IsProbabilityMeasure (ν : Measure (GaugeField (1 : ℝ))) := ν.2.1
    have hinv := hGroup.2.1 ν ν.2 P.reflect
    refine ⟨fun F hF => hinv F hF, fun F G hF hG => ?_⟩
    obtain ⟨hθ, -, -⟩ := hAction.2.2.2.2.1 P.reflect F hF
    obtain ⟨mθ, Cθ, bθ⟩ := hθ
    obtain ⟨mG, CG, bG⟩ := hG
    obtain ⟨mF, CF, bF⟩ := hF
    have hsq : ∫ U, ‖P.reflect.actOn F U‖ ^ 2 ∂(ν : Measure (GaugeField (1 : ℝ))) =
        ∫ U, ‖F U‖ ^ 2 ∂(ν : Measure (GaugeField (1 : ℝ))) := by
      have hobs : IsBoundedObservable fun U => (((‖F U‖ ^ 2 : ℝ)) : ℂ) := by
        refine ⟨Complex.measurable_ofReal.comp (mF.norm.pow_const 2), CF ^ 2, fun U => ?_⟩
        have : ‖(((‖F U‖ ^ 2 : ℝ)) : ℂ)‖ = ‖F U‖ ^ 2 := by simp
        rw [this]
        exact pow_le_pow_left₀ (norm_nonneg _) (bF U) 2
      have h := hinv _ hobs
      have h' : ∫ U, (((‖P.reflect.actOn F U‖ ^ 2 : ℝ)) : ℂ)
          ∂(ν : Measure (GaugeField (1 : ℝ))) =
          ∫ U, (((‖F U‖ ^ 2 : ℝ)) : ℂ) ∂(ν : Measure (GaugeField (1 : ℝ))) := h
      rw [integral_complex_ofReal, integral_complex_ofReal] at h'
      exact_mod_cast h'
    rw [← hsq]
    exact norm_integral_conj_mul_le_sqrt_mul_sqrt mθ mG bθ bG
  · refine proj_eq_zero_of_quadMeasure _ _ fun ψ => ?_
    refine measure_mono_null (compl_imageInSpectrum_linkCone_subset μ hCurve)
      (measure_union_null ?_ ?_)
    · exact quadMeasure_eq_zero_of_proj _ _ hE0 ψ
    · exact measure_iUnion_null fun l => quadMeasure_eq_zero_of_proj _ _ (hneg l) ψ
  · exact hk.tendsto_pow
  · intro l
    exact circleOp_mul_levelOne hj hb l (hneg l)
end YangMills.Construction.ReflectionPositivity.DirectionPictures.LinkConeGroundProof
