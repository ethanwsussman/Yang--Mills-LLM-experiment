import YangMills.Construction.FormHilbert.JointSpectralCalculus
import YangMills.Construction.ReflectionPositivity.CarrierOfTheSitePicture
import YangMills.Construction.ReflectionPositivity.CurveOfTheSpectralVariables
import YangMills.Construction.ReflectionPositivity.EnergyMomentumInequalityAtOneStepLinkFormProof
import YangMills.Construction.ReflectionPositivity.InequalitiesAtSeveralSteps
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
open MeasureTheory Set
open scoped ComplexConjugate ComplexOrder ENNReal
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.DirectionPictures.MultiStep
open YangMills.Construction.InfiniteLattice (GaugeField axisStep shift)
open YangMills.Construction.JointSpectrum (CommutingFamily SpectralDomain spectralMonomial torusMonomial)
open YangMills.Construction.FormHilbert
section Weights
variable {ι : Type*} [Fintype ι]
def multiStepWeight (a : ι) (k : ℕ) (p : SpectralDomain ι) : ℝ :=
  (1 - (p.1 : ℝ) ^ k) ^ 2 - (p.1 : ℝ) ^ k * ‖1 - (p.2 a : ℂ) ^ k‖ ^ 2
theorem continuous_multiStepWeight (a : ι) (k : ℕ) : Continuous (multiStepWeight a k) := by
  have ht : Continuous fun p : SpectralDomain ι => (p.1 : ℝ) :=
    continuous_subtype_val.comp continuous_fst
  have hw : Continuous fun p : SpectralDomain ι => (p.2 a : ℂ) := by fun_prop
  unfold multiStepWeight
  exact (((continuous_const.sub (ht.pow k)).pow 2).sub
    ((ht.pow k).mul (((continuous_const.sub (hw.pow k)).norm).pow 2)))
theorem continuous_spectralMonomial (n : ℕ) (y : ι → ℤ) :
    Continuous (spectralMonomial (J := ι) n y) := by
  have ht : Continuous fun p : SpectralDomain ι => ((p.1 : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (continuous_subtype_val.comp continuous_fst)
  have hw : ∀ b : ι, Continuous fun p : SpectralDomain ι => (p.2 b : ℂ) ^ y b := by
    intro b
    simp_rw [← Circle.coe_zpow]
    have hc : Continuous fun w : Circle => (w : ℂ) := by fun_prop
    exact hc.comp ((continuous_zpow (y b)).comp ((continuous_apply b).comp continuous_snd))
  unfold spectralMonomial torusMonomial
  exact (ht.pow n).mul (continuous_finsetProd _ fun b _ => hw b)
theorem isBddMeasurable_of_continuous {f : SpectralDomain ι → ℂ} (h : Continuous f) :
    IsBddMeasurable f := by
  obtain ⟨M, hM⟩ := isCompact_univ.exists_bound_of_continuousOn h.continuousOn
  exact ⟨h.measurable, M, fun p => hM p (mem_univ p)⟩
theorem torusMonomial_of_support (w : ι → Circle) (a : ι) (m : ι → ℤ)
    (hm : ∀ b, b ≠ a → m b = 0) :
    torusMonomial w m = (w a : ℂ) ^ m a := by
  classical
  unfold torusMonomial
  refine Fintype.prod_eq_single a fun b hb => ?_
  rw [hm b hb, zpow_zero]
theorem multiStepWeight_eq_sum (a : ι) (k : ℕ) {m₀ m₁ m₂ : ι → ℤ}
    (h₀ : ∀ b, b ≠ a → m₀ b = 0) (h₁ : ∀ b, b ≠ a → m₁ b = 0) (h₂ : ∀ b, b ≠ a → m₂ b = 0)
    (e₀ : m₀ a = 0) (e₁ : m₁ a = k) (e₂ : m₂ a = -(k : ℤ)) :
    (fun p : SpectralDomain ι => ((multiStepWeight a k p : ℝ) : ℂ)) = fun p =>
      spectralMonomial 0 m₀ p + (-4 : ℂ) * spectralMonomial k m₀ p +
        (1 : ℂ) * spectralMonomial (2 * k) m₀ p +
        (1 : ℂ) * spectralMonomial k m₁ p + (1 : ℂ) * spectralMonomial k m₂ p := by
  funext p
  have hn1 : ‖(p.2 a : ℂ) ^ k‖ = 1 := by rw [norm_pow, Circle.norm_coe, one_pow]
  have hw : (p.2 a : ℂ) ^ k * ((p.2 a : ℂ) ^ k)⁻¹ = 1 :=
    mul_inv_cancel₀ (by intro h; simp [h] at hn1)
  have hconj : (starRingEnd ℂ) ((p.2 a : ℂ) ^ k) = ((p.2 a : ℂ) ^ k)⁻¹ :=
    (Complex.inv_eq_conj hn1).symm
  have hn : ((‖1 - (p.2 a : ℂ) ^ k‖ ^ 2 : ℝ) : ℂ) =
      (1 - (p.2 a : ℂ) ^ k) * (1 - ((p.2 a : ℂ) ^ k)⁻¹) := by
    have := Complex.mul_conj' (1 - (p.2 a : ℂ) ^ k)
    rw [map_sub, map_one, hconj] at this
    rw [this]
    push_cast
    rfl
  simp only [spectralMonomial, torusMonomial_of_support p.2 a _ h₀,
    torusMonomial_of_support p.2 a _ h₁, torusMonomial_of_support p.2 a _ h₂, e₀, e₁, e₂,
    multiStepWeight]
  rw [Complex.ofReal_sub, Complex.ofReal_mul, hn]
  push_cast
  rw [zpow_neg, zpow_natCast, pow_mul']
  simp only [pow_zero, zpow_zero, one_mul, mul_one]
  generalize ((p.1 : ℝ) : ℂ) ^ k = τ
  generalize (p.2 a : ℂ) ^ k = w at *
  generalize w⁻¹ = w' at *
  linear_combination (-τ) * hw
end Weights
section Operators
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {ι : Type*} [Fintype ι] [Nonempty ι]
theorem proj_eq_zero_of_subset (E : BorelPVM ι H) {s t : MeasSubset ι}
    (hs : s.1 ⊆ t.1) (h : E t = 0) : E s = 0 := by
  have e : (⟨s.1 ∩ t.1, s.2.inter t.2⟩ : MeasSubset ι) = s :=
    Subtype.ext (inter_eq_left.mpr hs)
  have h₁ := E.proj_inter s t
  rw [e] at h₁
  change E s = E s * E t at h₁
  rw [h₁, h, mul_zero]
def multiStepOperator (S : CommutingFamily H ι) (k : ℕ) (m₀ m₁ m₂ : ι → ℤ) : H →L[ℂ] H :=
  S.A ^ 0 * S.unitaryMonomial m₀ + (-4 : ℂ) • (S.A ^ k * S.unitaryMonomial m₀) +
    (1 : ℂ) • (S.A ^ (2 * k) * S.unitaryMonomial m₀) +
    (1 : ℂ) • (S.A ^ k * S.unitaryMonomial m₁) +
    (1 : ℂ) • (S.A ^ k * S.unitaryMonomial m₂)
theorem spectralOp_multiStepWeight {S : CommutingFamily H ι} {E : BorelPVM ι H}
    (hC : BoundedFunctionalCalculus S E) (a : ι) (k : ℕ) {m₀ m₁ m₂ : ι → ℤ}
    (h₀ : ∀ b, b ≠ a → m₀ b = 0) (h₁ : ∀ b, b ≠ a → m₁ b = 0) (h₂ : ∀ b, b ≠ a → m₂ b = 0)
    (e₀ : m₀ a = 0) (e₁ : m₁ a = k) (e₂ : m₂ a = -(k : ℤ)) :
    E.spectralOp (fun p => ((multiStepWeight a k p : ℝ) : ℂ)) =
      multiStepOperator S k m₀ m₁ m₂ := by
  have hadd : ∀ (f : SpectralDomain ι → ℂ), Continuous f → ∀ (c : ℂ) (n : ℕ) (y : ι → ℤ),
      E.spectralOp (fun p => f p + c * spectralMonomial n y p) =
        E.spectralOp f + c • (S.A ^ n * S.unitaryMonomial y) := fun f hf c n y => by
    rw [hC.spectralOp_add_smul _ _ (isBddMeasurable_of_continuous hf)
      (isBddMeasurable_of_continuous (continuous_spectralMonomial n y)),
      hC.spectralOp_monomial]
  have hm := fun (n : ℕ) (y : ι → ℤ) => continuous_spectralMonomial (ι := ι) n y
  rw [multiStepWeight_eq_sum a k h₀ h₁ h₂ e₀ e₁ e₂]
  have c₁ : Continuous fun p : SpectralDomain ι =>
      spectralMonomial 0 m₀ p + (-4 : ℂ) * spectralMonomial k m₀ p :=
    (hm 0 m₀).add (continuous_const.mul (hm k m₀))
  have c₂ : Continuous fun p : SpectralDomain ι =>
      spectralMonomial 0 m₀ p + (-4 : ℂ) * spectralMonomial k m₀ p +
        (1 : ℂ) * spectralMonomial (2 * k) m₀ p :=
    c₁.add (continuous_const.mul (hm (2 * k) m₀))
  have c₃ : Continuous fun p : SpectralDomain ι =>
      spectralMonomial 0 m₀ p + (-4 : ℂ) * spectralMonomial k m₀ p +
        (1 : ℂ) * spectralMonomial (2 * k) m₀ p + (1 : ℂ) * spectralMonomial k m₁ p :=
    c₂.add (continuous_const.mul (hm k m₁))
  rw [hadd _ c₃ 1 k m₂, hadd _ c₂ 1 k m₁, hadd _ c₁ 1 (2 * k) m₀, hadd _ (hm 0 m₀) (-4) k m₀,
    hC.spectralOp_monomial]
  rfl
theorem unitaryMonomial_eq_of_support [DecidableEq ι] (S : CommutingFamily H ι) (a : ι)
    (m : ι → ℤ) (hm : ∀ b, b ≠ a → m b = 0) :
    S.unitaryMonomial m = ((S.B a ^ m a : unitary (H →L[ℂ] H)) : H →L[ℂ] H) := by apply _root_.YangMills.Construction.ReflectionPositivity.DirectionPictures.EnergyMomentumOneStep.unitaryMonomial_eq_of_support <;> assumption
omit [CompleteSpace H] in
theorem multiStepSum_eq (X Y Y' : H →L[ℂ] H) :
    1 + (-4 : ℂ) • X + (1 : ℂ) • (X * X) + (1 : ℂ) • (X * Y) + (1 : ℂ) • (X * Y') =
      (1 - X) ^ 2 - X * ((2 : ℂ) • 1 - Y - Y') := by
  have h₂ : (2 : ℂ) • (1 : H →L[ℂ] H) = 1 + 1 := two_smul ℂ 1
  have h₄ : (-4 : ℂ) • X = -(X + X + X + X) := by
    rw [show (-4 : ℂ) = -(1 + 1 + 1 + 1) by norm_num, neg_smul, add_smul, add_smul, add_smul,
      one_smul]
  rw [h₂, h₄]
  simp only [one_smul]
  noncomm_ring
end Operators
theorem intPoint_single (a : Fin 4) (y : ℤ) : intPoint (Pi.single a y) = y • axisStep 1 a := by apply _root_.YangMills.Construction.ReflectionPositivity.DirectionPictures.EnergyMomentumOneStep.intPoint_single <;> assumption
theorem multiStepWeight_nonneg (hCurve : SpectralCurve.CurveFacts) {μ : Fin 4}
    (a : TransverseAxis μ) {k : ℕ} (hk : 1 ≤ k) {q : SpectralDomain (TransverseAxis μ)}
    (hq : q ∈ imageInSpectrum μ (siteCone μ)) : 0 ≤ multiStepWeight a k q := by
  obtain ⟨x, ⟨hx, -⟩, rfl⟩ := hq
  have hc := hx.2 a
  by_cases hT : x.1 = ⊤
  · have h0 : ((expNegEnergy x.1 : unitInterval) : ℝ) = 0 := by simp [expNegEnergy, hT]
    have e : multiStepWeight a k (toSpectrum μ x) = 1 := by
      change (1 - ((expNegEnergy x.1 : unitInterval) : ℝ) ^ k) ^ 2 -
        ((expNegEnergy x.1 : unitInterval) : ℝ) ^ k * _ = 1
      rw [h0, zero_pow (by omega)]
      simp
    rw [e]
    exact zero_le_one
  · have hv : ((expNegEnergy x.1 : unitInterval) : ℝ) =
        SpectralCurve.expNegEnergy x.1.toReal := by
      simp [expNegEnergy, hT, SpectralCurve.expNegEnergy]
    have hw : ((toSpectrum μ x).2 a : ℂ) = SpectralCurve.phaseOf (x.2 a) := by
      change ((Circle.exp (x.2 a) : Circle) : ℂ) = _
      rw [Circle.coe_exp, SpectralCurve.phaseOf, mul_comm]
    have hp := (hCurve x.1.toReal (x.2 a) k ENNReal.toReal_nonneg hk).2.1
    have hon : SpectralCurve.AboveCurve (SpectralCurve.expNegEnergy x.1.toReal)
        (SpectralCurve.phaseOf (x.2 a)) := by
      unfold SpectralCurve.AboveCurve
      rw [← hv]
      exact hc
    have h := hp hon
    unfold SpectralCurve.AboveCurve at h
    rw [← hv, ← hw] at h
    have e : multiStepWeight a k (toSpectrum μ x) =
        (1 - ((expNegEnergy x.1 : unitInterval) : ℝ) ^ k) ^ 2 -
          ((expNegEnergy x.1 : unitInterval) : ℝ) ^ k * ‖1 - ((toSpectrum μ x).2 a : ℂ) ^ k‖ ^ 2 :=
      rfl
    rw [e]
    exact sub_nonneg.mpr h
theorem multiStepInequalities_holds (hCarrier : SiteCarrierFacts)
    (hSpectral : JointSpectralCalculusTheorem)
    (hCurve : SpectralCurve.CurveFacts)
    (hPictures : ReflectionPairTheorem) :
    MultiStepInequalities := by
  intro ν μ a k hk
  have hP := hPictures ν μ ReflectionPair.site
  have hJoint : IsJointPVM (ReflectionPair.site.opFamily ν μ)
      (ReflectionPair.site.jointPVM ν μ) := hP.2.2.2.2.1
  obtain ⟨-, -, hE⟩ := hSpectral (ReflectionPair.site.Hilb ν μ) (TransverseAxis μ)
    (ReflectionPair.site.opFamily ν μ)
  obtain ⟨-, hCalc, -, hReal, -⟩ := hE _ hJoint
  obtain ⟨⟨hClosed, hCar⟩, -⟩ := hCarrier ν μ
  let m : ℤ → TransverseAxis μ → ℤ := fun y b => (Pi.single a.1 y : Fin 4 → ℤ) b.1
  have hm : ∀ y b, b ≠ a → m y b = 0 := fun y b hb =>
    Pi.single_eq_of_ne (fun e => hb (Subtype.ext e)) _
  have hma : ∀ y, m y a = y := fun y => Pi.single_eq_same _ _
  have hnn : 0 ≤ multiStepOperator (ReflectionPair.site.opFamily ν μ) k (m 0) (m k)
      (m (-(k : ℤ))) := by
    have hcont := continuous_multiStepWeight a k
    obtain ⟨M, hM⟩ := isCompact_univ.exists_bound_of_continuousOn hcont.continuousOn
    have hiff := (hReal _ hcont.measurable
      ⟨M, fun p => by simpa [Real.norm_eq_abs] using hM p (mem_univ p)⟩).2
    rw [spectralOp_multiStepWeight hCalc a k (hm 0) (hm k) (hm _) (hma 0) (hma k) (hma _)] at hiff
    refine hiff.mpr (proj_eq_zero_of_subset _ ?_ hCar)
    intro q hq hin
    exact hq (multiStepWeight_nonneg hCurve a hk hin)
  have hU₀ : (ReflectionPair.site.opFamily ν μ).unitaryMonomial (m 0) = 1 := by
    rw [unitaryMonomial_eq_of_support _ a _ (hm 0), hma, zpow_zero]
    rfl
  have hUk : (ReflectionPair.site.opFamily ν μ).unitaryMonomial (m k) =
      ReflectionPair.site.shiftOp ν μ a ^ k := by
    rw [unitaryMonomial_eq_of_support _ a _ (hm k), hma, zpow_natCast]
    exact SubmonoidClass.coe_pow _ k
  have hUm : (ReflectionPair.site.opFamily ν μ).unitaryMonomial (m (-(k : ℤ))) =
      star (ReflectionPair.site.shiftOp ν μ a) ^ k := by
    rw [unitaryMonomial_eq_of_support _ a _ (hm _), hma, zpow_neg, zpow_natCast, ← inv_pow]
    exact SubmonoidClass.coe_pow _ k
  have hsum : multiStepOperator (ReflectionPair.site.opFamily ν μ) k (m 0) (m k)
      (m (-(k : ℤ))) =
      (1 - ReflectionPair.site.transferOp ν μ ^ k) ^ 2 -
        ReflectionPair.site.transferOp ν μ ^ k *
          ((2 : ℂ) • 1 - ReflectionPair.site.shiftOp ν μ a ^ k -
            star (ReflectionPair.site.shiftOp ν μ a) ^ k) := by
    rw [← multiStepSum_eq]
    simp only [multiStepOperator, hU₀, hUk, hUm, pow_zero, mul_one, two_mul, pow_add]
    rfl
  refine ⟨?_, fun F hF => ?_⟩
  · rw [ge_iff_le, ContinuousLinearMap.le_def, ← hsum]
    exact (ContinuousLinearMap.nonneg_iff_isPositive _).mp hnn
  · have hi := ((ContinuousLinearMap.nonneg_iff_isPositive _).mp hnn).inner_nonneg_right
      (ReflectionPair.site.obsClass ν μ F)
    have key : ∀ (n : ℕ) (y : ℤ),
        inner ℂ (ReflectionPair.site.obsClass ν μ F)
            (((ReflectionPair.site.opFamily ν μ).A ^ n *
              (ReflectionPair.site.opFamily ν μ).unitaryMonomial (m y))
              (ReflectionPair.site.obsClass ν μ F)) =
          ∫ U, conj ((MirrorHyperplanes.siteReflect μ).actOn F U) *
            (shift (n • axisStep (1 : ℝ) μ + y • axisStep (1 : ℝ) a.1)).actOn F U
            ∂(ν : Measure (GaugeField (1 : ℝ))) := by
      intro n y
      have h := hP.2.2.1 F hF F hF n (Pi.single a.1 y) (Pi.single_eq_of_ne a.2.symm _)
      rw [intPoint_single] at h
      exact h
    simp only [multiStepOperator, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      inner_add_right, inner_smul_right, key] at hi
    have e₀ : (0 : ℕ) • axisStep (1 : ℝ) μ + (0 : ℤ) • axisStep (1 : ℝ) a.1 = 0 := by simp
    have e₁ : k • axisStep (1 : ℝ) μ + (0 : ℤ) • axisStep (1 : ℝ) a.1 =
        k • axisStep (1 : ℝ) μ := by simp
    have e₂ : (2 * k) • axisStep (1 : ℝ) μ + (0 : ℤ) • axisStep (1 : ℝ) a.1 =
        (2 * k) • axisStep (1 : ℝ) μ := by simp
    have e₃ : k • axisStep (1 : ℝ) μ + (k : ℤ) • axisStep (1 : ℝ) a.1 =
        k • axisStep (1 : ℝ) μ + k • axisStep (1 : ℝ) a.1 := by simp
    have e₄ : k • axisStep (1 : ℝ) μ + (-(k : ℤ)) • axisStep (1 : ℝ) a.1 =
        k • axisStep (1 : ℝ) μ - k • axisStep (1 : ℝ) a.1 := by
      rw [neg_smul, natCast_zsmul, sub_eq_add_neg]
    rw [e₀, e₁, e₂, e₃, e₄] at hi
    dsimp only
    convert hi using 1
    ring
end YangMills.Construction.ReflectionPositivity.DirectionPictures.MultiStep
