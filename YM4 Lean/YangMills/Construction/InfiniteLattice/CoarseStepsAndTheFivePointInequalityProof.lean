import YangMills.Construction.EnergyMomentum.ArcoshCurveChord
import YangMills.Construction.InfiniteLattice.CoarseStepsAndTheFivePointInequality
import YangMills.Construction.InfiniteLattice.EveryPairOfDirectionsAndTheJointCarrier
import YangMills.Construction.InfiniteLattice.GibbsStatesByWindowsAndPeriodGroups
import YangMills.Construction.JointSpectrum.BorelCalculusApplications
import YangMills.Construction.JointSpectrum.BorelFunctionalCalculus
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
open MeasureTheory Set
open scoped InnerProductSpace ComplexOrder ComplexConjugate
noncomputable section
namespace YangMills.Construction
open OneLoopNotation ComplexHilbert ContractionUnitary
open JointSpectrum JointSpectrum.SpectralIntegral ScalarSpectralMeasures
namespace LatticeConventions
namespace CoarseStepFivePoint
open InfiniteLattice (GaugeField IsBoundedObservable LatticePoint localRegionObservables axisStep shift)
theorem natCast_mul_sinh_le_sinh_mul {k : ℕ} (hk : 1 ≤ k) {x : ℝ} (hx : 0 ≤ x) :
    (k : ℝ) * Real.sinh x ≤ Real.sinh (k * x) := by
  induction k, hk using Nat.le_induction with
  | base => simp
  | succ m hm ih =>
    have hs : 0 ≤ Real.sinh x := Real.sinh_nonneg_iff.mpr hx
    have hsm : 0 ≤ Real.sinh (m * x) := Real.sinh_nonneg_iff.mpr (by positivity)
    have hc : 1 ≤ Real.cosh x := Real.one_le_cosh x
    have hcm : 1 ≤ Real.cosh (m * x) := Real.one_le_cosh _
    have e : ((m + 1 : ℕ) : ℝ) * x = m * x + x := by push_cast; ring
    rw [e, Real.sinh_add]
    push_cast
    nlinarith [mul_le_mul_of_nonneg_left hc hsm, mul_le_mul_of_nonneg_right hcm hs]
theorem abs_sin_natCast_mul_le (k : ℕ) (θ : ℝ) :
    |Real.sin (k * θ)| ≤ (k : ℝ) * |Real.sin θ| := by
  induction k with
  | zero => simp
  | succ m ih =>
    have e : ((m + 1 : ℕ) : ℝ) * θ = m * θ + θ := by push_cast; ring
    have hc : |Real.cos θ| ≤ 1 := abs_le.mpr ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩
    have hcm : |Real.cos (m * θ)| ≤ 1 := abs_le.mpr ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩
    rw [e, Real.sin_add]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul]
    push_cast
    nlinarith [abs_nonneg (Real.sin (m * θ)), abs_nonneg (Real.sin θ),
      mul_le_mul_of_nonneg_left hc (abs_nonneg (Real.sin (m * θ))),
      mul_le_mul_of_nonneg_right hcm (abs_nonneg (Real.sin θ))]
theorem one_sub_exp_neg_sq (x : ℝ) :
    (1 - Real.exp (-x)) ^ 2 = 4 * Real.exp (-x) * Real.sinh (x / 2) ^ 2 := by
  have h₁ : Real.exp (-x) = Real.exp (-(x / 2)) * Real.exp (-(x / 2)) := by
    rw [← Real.exp_add]; congr 1; ring
  have h₂ : Real.exp (x / 2) * Real.exp (-(x / 2)) = 1 := by
    rw [← Real.exp_add]; simp
  rw [Real.sinh_eq, h₁]
  generalize Real.exp (-(x / 2)) = u at *
  generalize Real.exp (x / 2) = w at *
  have : 4 * (u * u) * ((w - u) / 2) ^ 2 = (w * u - u * u) ^ 2 := by ring
  rw [this, h₂]
theorem pow_mul_norm_one_sub_pow_sq_le (hc : EnergyMomentum.ArcoshCurve.ConditionsEquiv) {t : ℝ}
    (ht : 0 ≤ t) (ht₁ : t ≤ 1) {z : ℂ} (hz : ‖z‖ = 1)
    (hcone : (1 - t) ^ 2 ≥ t * ‖1 - z‖ ^ 2) {k : ℕ} (hk : 1 ≤ k) :
    t ^ k * ‖1 - z ^ k‖ ^ 2 ≤ (1 - t ^ k) ^ 2 := by
  rcases ht.eq_or_lt with rfl | ht₀
  · simp [zero_pow (by omega : k ≠ 0)]
  have hp : Complex.arg z ∈ Ioc (-Real.pi) Real.pi := ⟨Complex.neg_pi_lt_arg z, Complex.arg_le_pi z⟩
  have hzexp : z = Complex.exp (Complex.I * (Complex.arg z : ℂ)) := by
    have := Complex.norm_mul_exp_arg_mul_I z
    rw [hz] at this
    rw [mul_comm Complex.I]
    simpa using this.symm
  have h := hc t ⟨ht₀, ht₁⟩ (Complex.arg z) hp
  dsimp only at h
  rw [← hzexp] at h
  obtain ⟨hE, h₁, -⟩ := h
  generalize hθ : Complex.arg z = p at *
  have hE₀ : 0 ≤ -Real.log t := hE
  set E : ℝ := -Real.log t with hEdef
  have hsin : |Real.sin (p / 2)| ≤ Real.sinh (E / 2) := h₁.mp hcone
  have hchain : |Real.sin (k * (p / 2))| ≤ Real.sinh (k * (E / 2)) :=
    (abs_sin_natCast_mul_le k _).trans
      ((mul_le_mul_of_nonneg_left hsin (Nat.cast_nonneg k)).trans
        (natCast_mul_sinh_le_sinh_mul hk (by positivity)))
  have htk : t ^ k = Real.exp (-(k * E)) := by
    have : t = Real.exp (-E) := by rw [hEdef, neg_neg, Real.exp_log ht₀]
    conv_lhs => rw [this]
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hzk : z ^ k = Complex.exp (Complex.I * (((k : ℝ) * p : ℝ) : ℂ)) := by
    conv_lhs => rw [hzexp]
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hnorm : ‖1 - z ^ k‖ ^ 2 = 4 * Real.sin (k * (p / 2)) ^ 2 := by
    rw [norm_sub_rev, hzk, Complex.norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs, sq_abs]
    have : (k : ℝ) * p / 2 = k * (p / 2) := by ring
    rw [this]
    ring
  have hsq : Real.sin (k * (p / 2)) ^ 2 ≤ Real.sinh (k * (E / 2)) ^ 2 := by
    rw [← sq_abs (Real.sin _)]
    exact pow_le_pow_left₀ (abs_nonneg _) hchain 2
  have hx : (k : ℝ) * E / 2 = k * (E / 2) := by ring
  rw [hnorm, htk, one_sub_exp_neg_sq, hx]
  have : 0 ≤ Real.exp (-(k * E)) := (Real.exp_pos _).le
  nlinarith [mul_le_mul_of_nonneg_left hsq this]
section System
variable {𝒦 : Type} [NormedAddCommGroup 𝒦] [InnerProductSpace ℂ 𝒦] [CompleteSpace 𝒦]
  {J : Type} [Fintype J] [Nonempty J] [Unique J]
def coarseCone (k : ℕ) (p : SpectralDomain J) : ℝ :=
  (1 - (p.1 : ℝ) ^ k) ^ 2 - (p.1 : ℝ) ^ k * ‖1 - (p.2 default : ℂ) ^ k‖ ^ 2
theorem continuous_coarseCone (k : ℕ) : Continuous (coarseCone (J := J) k) := by
  have ht : Continuous fun p : SpectralDomain J => (p.1 : ℝ) :=
    continuous_subtype_val.comp continuous_fst
  have hz : Continuous fun p : SpectralDomain J => (p.2 default : ℂ) := by fun_prop
  unfold coarseCone
  exact (((continuous_const.sub (ht.pow k)).pow 2).sub
    ((ht.pow k).mul (((continuous_const.sub (hz.pow k)).norm).pow 2)))
theorem continuous_spectralMonomial (n : ℕ) (y : J → ℤ) :
    Continuous (spectralMonomial (J := J) n y) := by
  have ht : Continuous fun p : SpectralDomain J => ((p.1 : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (continuous_subtype_val.comp continuous_fst)
  have hz : ∀ α : J, Continuous fun p : SpectralDomain J => (p.2 α : ℂ) ^ y α := by
    intro α
    simp_rw [← Circle.coe_zpow]
    have hc : Continuous fun ζ : Circle => (ζ : ℂ) := by fun_prop
    exact hc.comp ((continuous_zpow (y α)).comp ((continuous_apply α).comp continuous_snd))
  unfold spectralMonomial torusMonomial
  exact (ht.pow n).mul (continuous_finsetProd _ fun α _ => hz α)
def fiveTermPoly (J : Type) [Fintype J] [Unique J] (k : ℕ) : SpectralDomain J → ℂ :=
  spectralMonomial 0 (fun _ => 0) + (-4 : ℂ) • spectralMonomial k (fun _ => 0) +
    (1 : ℂ) • spectralMonomial (2 * k) (fun _ => 0) + (1 : ℂ) • spectralMonomial k (fun _ => (k : ℤ)) +
    (1 : ℂ) • spectralMonomial k (fun _ => -(k : ℤ))
def fiveTermOp (S : CommutingFamily 𝒦 J) (k : ℕ) : 𝒦 →L[ℂ] 𝒦 :=
  FamilyPolynomials.familyMonomial S 0 (fun _ => 0) +
    (-4 : ℂ) • FamilyPolynomials.familyMonomial S k (fun _ => 0) +
    (1 : ℂ) • FamilyPolynomials.familyMonomial S (2 * k) (fun _ => 0) +
    (1 : ℂ) • FamilyPolynomials.familyMonomial S k (fun _ => (k : ℤ)) +
    (1 : ℂ) • FamilyPolynomials.familyMonomial S k (fun _ => -(k : ℤ))
theorem coarseCone_eq_fiveTermPoly (k : ℕ) :
    (fun p : SpectralDomain J => ((coarseCone k p : ℝ) : ℂ)) = fiveTermPoly J k := by
  funext p
  have hz : ‖(p.2 default : ℂ) ^ k‖ = 1 := by rw [norm_pow, Circle.norm_coe, one_pow]
  have hw : (p.2 default : ℂ) ^ k * ((p.2 default : ℂ) ^ k)⁻¹ = 1 :=
    mul_inv_cancel₀ (by intro h; simp [h] at hz)
  have hconj : (starRingEnd ℂ) ((p.2 default : ℂ) ^ k) = ((p.2 default : ℂ) ^ k)⁻¹ :=
    (Complex.inv_eq_conj hz).symm
  have hn : ((‖1 - (p.2 default : ℂ) ^ k‖ ^ 2 : ℝ) : ℂ) =
      (1 - (p.2 default : ℂ) ^ k) * (1 - ((p.2 default : ℂ) ^ k)⁻¹) := by
    have := Complex.mul_conj' (1 - (p.2 default : ℂ) ^ k)
    rw [map_sub, map_one, hconj] at this
    rw [this]
    push_cast
    rfl
  simp only [fiveTermPoly, coarseCone, Pi.add_apply, Pi.smul_apply, smul_eq_mul, spectralMonomial,
    torusMonomial, Fintype.prod_unique]
  rw [Complex.ofReal_sub, Complex.ofReal_mul, hn]
  push_cast
  rw [zpow_neg, zpow_natCast, pow_mul']
  simp only [pow_zero, zpow_zero, one_mul, mul_one]
  generalize ((p.1 : ℝ) : ℂ) ^ k = τ
  generalize (p.2 default : ℂ) ^ k = w at *
  generalize w⁻¹ = w' at *
  linear_combination (-τ) * hw
variable (hcal : JointSpectrum.BorelCalculus.BorelCalculusStatement) (S : CommutingFamily 𝒦 J)
include hcal in
theorem spectralIntegral_fiveTermPoly (k : ℕ) (ψ : 𝒦) :
    spectralIntegral S (fiveTermPoly J k) ψ = fiveTermOp S k ψ := by
  obtain ⟨-, -, hMono, hAdd, -⟩ := hcal 𝒦 J S
  have hstep : ∀ (f : SpectralDomain J → ℂ) (c : ℂ) (n : ℕ) (y : J → ℤ), Measurable f →
      integralDomain S f = univ →
      integralDomain S (f + c • spectralMonomial n y) = univ ∧
        ∀ ψ, spectralIntegral S (f + c • spectralMonomial n y) ψ =
          spectralIntegral S f ψ + c • FamilyPolynomials.familyMonomial S n y ψ := by
    intro f c n y hf hd
    have hm : Measurable (spectralMonomial (J := J) n y) :=
      (continuous_spectralMonomial n y).measurable
    have hψ : ∀ ψ, ψ ∈ integralDomain S f ∧ ψ ∈ integralDomain S (spectralMonomial n y) :=
      fun ψ => ⟨hd ▸ mem_univ ψ, (hMono n y).1 ▸ mem_univ ψ⟩
    refine ⟨eq_univ_of_forall fun ψ => (hAdd f _ hf hm c ψ (hψ ψ).1 (hψ ψ).2).1, fun ψ => ?_⟩
    rw [(hAdd f _ hf hm c ψ (hψ ψ).1 (hψ ψ).2).2, (hMono n y).2]
  have hm₀ : ∀ (n : ℕ) (y : J → ℤ), Measurable (spectralMonomial (J := J) n y) :=
    fun n y => (continuous_spectralMonomial n y).measurable
  have hs : ∀ (c : ℂ) (n : ℕ) (y : J → ℤ), Measurable (c • spectralMonomial (J := J) n y) :=
    fun c n y => (hm₀ n y).const_smul c
  obtain ⟨d₁, e₁⟩ := hstep _ (-4) k (fun _ => 0) (hm₀ 0 fun _ => 0) (hMono 0 fun _ => 0).1
  obtain ⟨d₂, e₂⟩ := hstep _ 1 (2 * k) (fun _ => 0) ((hm₀ 0 _).add (hs _ _ _)) d₁
  obtain ⟨d₃, e₃⟩ := hstep _ 1 k (fun _ => (k : ℤ)) (((hm₀ 0 _).add (hs _ _ _)).add (hs _ _ _)) d₂
  obtain ⟨-, e₄⟩ := hstep _ 1 k (fun _ => -(k : ℤ))
    ((((hm₀ 0 _).add (hs _ _ _)).add (hs _ _ _)).add (hs _ _ _)) d₃
  rw [fiveTermPoly, e₄, e₃, e₂, e₁, (hMono 0 fun _ => 0).2]
  simp only [fiveTermOp, add_apply, smul_apply]
variable (hfacts : JointSpectrum.CalculusApplications.CalculusApplicationsStatement)
  (hcurve : EnergyMomentum.ArcoshCurve.Statement)
include hcal hfacts hcurve in
theorem fiveTermOp_nonneg (hC : MeasurableSet (coneInteriorOf J))
    (hE : jointSpectralMeasure S (coneInteriorOf J)ᶜ = 0) {k : ℕ} (hk : 1 ≤ k) :
    0 ≤ fiveTermOp S k := by
  have hcont := continuous_coarseCone (J := J) k
  obtain ⟨M, hM⟩ := isCompact_univ.exists_bound_of_continuousOn hcont.continuousOn
  obtain ⟨C, hCf, -, hiff⟩ := (hfacts 𝒦 J S).1 _ hcont.measurable
    ⟨M, fun p => by simpa [Real.norm_eq_abs] using hM p (mem_univ p)⟩
  have hCeq : C = fiveTermOp S k := by
    ext ψ
    rw [hCf, coarseCone_eq_fiveTermPoly, spectralIntegral_fiveTermPoly hcal]
  rw [← hCeq, hiff]
  obtain ⟨-, -, -, -, -, -, -, -, -, hEm, -⟩ := hcal 𝒦 J S
  have hsub : {p : SpectralDomain J | coarseCone k p < 0} ⊆ (coneInteriorOf J)ᶜ := by
    intro p hp hin
    have h := pow_mul_norm_one_sub_pow_sq_le hcurve.2.1 p.1.2.1 p.1.2.2
      (Circle.norm_coe (p.2 default)) hin hk
    have hp' : coarseCone k p < 0 := hp
    unfold coarseCone at hp'
    linarith
  have hmeas : MeasurableSet {p : SpectralDomain J | coarseCone k p < 0} :=
    measurableSet_lt hcont.measurable measurable_const
  funext ψ
  have h₁ := (hEm _ ψ hC.compl).2
  rw [hE] at h₁
  have h₂ : ScalarSpectralMeasures.spectralMeasure S ψ (coneInteriorOf J)ᶜ = 0 := by
    rw [← h₁]
    simp
  have h₃ := (hEm _ ψ hmeas).2
  rw [measure_mono_null hsub h₂] at h₃
  simpa using h₃
end System
section Operators
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
theorem inner_apply_nonneg_of_nonneg {C : H →L[ℂ] H} (h : 0 ≤ C) (ψ : H) : 0 ≤ ⟪ψ, C ψ⟫_ℂ := by
  have hs : IsSymmetricOp C :=
    (isSymmetricOp_iff C).mpr (IsSelfAdjoint.of_nonneg h)
  have hp := (ContinuousLinearMap.nonneg_iff_isPositive C).mp h
  have hre : 0 ≤ (⟪C ψ, ψ⟫_ℂ).re := (ContinuousLinearMap.isPositive_def.mp hp).2 ψ
  rw [← hs ψ ψ] at hre
  exact Complex.le_def.mpr ⟨hre, (hs.inner_self_apply_im_eq_zero ψ).symm⟩
theorem opGE_of_nonneg_sub {P Q : H →L[ℂ] H} (hP : IsSelfAdjoint P) (h : 0 ≤ P - Q) :
    OpGE P Q := by
  have hQ : IsSelfAdjoint Q := by
    have := hP.sub (IsSelfAdjoint.of_nonneg h)
    simpa using this
  refine ⟨(isSymmetricOp_iff Q).mpr hQ, (isSymmetricOp_iff P).mpr hP, fun ψ => ?_⟩
  have h₁ := inner_apply_nonneg_of_nonneg h ψ
  rw [sub_apply, inner_sub_right] at h₁
  exact sub_nonneg.mp h₁
theorem coe_zpow_eq_zpowOp {V : H →L[ℂ] H} (b : unitary (H →L[ℂ] H))
    (hb : (b : H →L[ℂ] H) = V) (hV : IsUnitaryMap (V : H →ₗ[ℂ] H)) (y : ℤ) :
    ((b ^ y : unitary (H →L[ℂ] H)) : H →L[ℂ] H) = zpowOp V y := by
  have hinv : opInv V = ((b⁻¹ : unitary (H →L[ℂ] H)) : H →L[ℂ] H) := by
    have h₁ : opInv V * V = 1 := (isTwoSidedInverse_opInv hV).2
    have h₂ : V * ((b⁻¹ : unitary (H →L[ℂ] H)) : H →L[ℂ] H) = 1 := by
      rw [← hb]
      exact congrArg Subtype.val (mul_inv_cancel b)
    exact left_inv_eq_right_inv h₁ h₂
  rcases le_or_gt 0 y with hy | hy
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hy
    rw [zpow_natCast, zpowOp_natCast, ← hb]
    exact SubmonoidClass.coe_pow b n
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, y = -(n : ℤ) := ⟨(-y).toNat, by omega⟩
    rw [zpowOp_of_neg _ hy, hinv, zpow_neg, zpow_natCast, ← inv_pow]
    simp only [neg_neg, Int.toNat_natCast]
    exact SubmonoidClass.coe_pow b⁻¹ n
variable {J : Type} [Fintype J] [Nonempty J] [Unique J]
theorem unitaryMonomial_const (S : CommutingFamily H J) (y : ℤ) :
    S.unitaryMonomial (fun _ => y) = ((S.B default ^ y : unitary (H →L[ℂ] H)) : H →L[ℂ] H) := by
  simp [CommutingFamily.unitaryMonomial, Finset.univ_unique, Finset.noncommProd_singleton]
theorem familyMonomial_const (S : CommutingFamily H J) {T V : H →L[ℂ] H} (hT : S.A = T)
    (hB : ((S.B default : unitary (H →L[ℂ] H)) : H →L[ℂ] H) = V)
    (hV : IsUnitaryMap (V : H →ₗ[ℂ] H)) (n : ℕ) (y : ℤ) :
    FamilyPolynomials.familyMonomial S n (fun _ => y) = T ^ n * zpowOp V y := by
  rw [FamilyPolynomials.familyMonomial, hT, unitaryMonomial_const, coe_zpow_eq_zpowOp _ hB hV]
theorem fiveTermOp_eq (S : CommutingFamily H J) {T V : H →L[ℂ] H} (hT : S.A = T)
    (hB : ((S.B default : unitary (H →L[ℂ] H)) : H →L[ℂ] H) = V)
    (hV : IsUnitaryMap (V : H →ₗ[ℂ] H)) (k : ℕ) :
    fiveTermOp S k = (idOp H - T ^ k) ^ 2 -
      T ^ k * ((2 : ℂ) • idOp H - zpowOp V (k : ℤ) - zpowOp V (-(k : ℤ))) := by
  have hid : idOp H = 1 := rfl
  have h₂ : (2 : ℂ) • (1 : H →L[ℂ] H) = 1 + 1 := by
    rw [show (2 : ℂ) = 1 + 1 by norm_num, add_smul, one_smul]
  have h₄ : (-4 : ℂ) • T ^ k = -(T ^ k + T ^ k + T ^ k + T ^ k) := by
    rw [show (-4 : ℂ) = -(1 + 1 + 1 + 1) by norm_num, neg_smul, add_smul, add_smul, add_smul,
      one_smul]
  simp only [fiveTermOp, familyMonomial_const S hT hB hV, zpowOp_zero, mul_one,
    pow_zero, one_smul, hid, h₂, h₄]
  rw [two_mul, pow_add]
  generalize T ^ k = X
  generalize zpowOp V (k : ℤ) = Y
  generalize zpowOp V (-(k : ℤ)) = Y'
  noncomm_ring
end Operators
section Correlations
variable {a : ℝ}
theorem isBoundedObservable_conjFun_mul {A B : GaugeField a → ℂ} (hA : IsBoundedObservable A)
    (hB : IsBoundedObservable B) : IsBoundedObservable (fun U => conjFun A U * B U) := by
  obtain ⟨mA, C, hC⟩ := hA
  obtain ⟨mB, D, hD⟩ := hB
  refine ⟨(Complex.continuous_conj.measurable.comp mA).mul mB, C * D, fun U => ?_⟩
  rw [norm_mul]
  have h₁ : ‖conjFun A U‖ ≤ C := by simpa [conjFun] using hC U
  exact mul_le_mul h₁ (hD U) (norm_nonneg _) ((norm_nonneg _).trans h₁)
theorem integrable_of_isBoundedObservable {A : GaugeField a → ℂ} (hA : IsBoundedObservable A)
    (ν : Measure (GaugeField a)) [IsProbabilityMeasure ν] : Integrable A ν := by
  obtain ⟨mA, C, hC⟩ := hA
  exact Integrable.of_bound mA.aestronglyMeasurable C (ae_of_all _ hC)
theorem integral_mixState {A : GaugeField a → ℂ} (hA : IsBoundedObservable A)
    (ν₁ ν₂ : Measure (GaugeField a)) [IsProbabilityMeasure ν₁] [IsProbabilityMeasure ν₂]
    {s : ℝ} (h₀ : 0 ≤ s) (h₁ : s ≤ 1) :
    ∫ U, A U ∂(mixState s ν₁ ν₂) = (s : ℂ) * ∫ U, A U ∂ν₁ + (1 - (s : ℂ)) * ∫ U, A U ∂ν₂ := by
  have i₁ := integrable_of_isBoundedObservable hA ν₁
  have i₂ := integrable_of_isBoundedObservable hA ν₂
  rw [mixState, integral_add_measure (i₁.smul_measure ENNReal.ofReal_ne_top)
    (i₂.smul_measure ENNReal.ofReal_ne_top), integral_smul_measure, integral_smul_measure,
    ENNReal.toReal_ofReal h₀, ENNReal.toReal_ofReal (sub_nonneg.mpr h₁)]
  simp [Complex.real_smul]
end Correlations
open SiteFrame in
theorem coarseStepFivePointBound_holds
    (hPairs : DirectionPairsSupport.PairwiseConeAndJointSupport)
    (hMat : CoordinatePictureOperators)
    (hCal : JointSpectrum.BorelCalculus.BorelCalculusStatement)
    (hUses : JointSpectrum.CalculusApplications.CalculusApplicationsStatement)
    (hCurve : EnergyMomentum.ArcoshCurve.Statement) :
    CoarseStepFivePointBound := by
  intro a μ lam hne ν _ hS
  have hpic : LinkFrame.IsAdmissibleState a μ ν := ⟨hS.1, hS.2.1⟩
  have hM := (hMat a μ ν hpic).2.2
  have hCar := (hPairs.1.2 a μ lam hne ν hS).2
  have hOps := hM.singleShiftFamily_ops ⟨lam, hne.symm⟩
  have hUni := hM.2.2.2.1 ⟨lam, hne.symm⟩
  have hMatrix := hM.2.2.2.2.2.2.2
  have hfive : ∀ k : ℕ, 1 ≤ k →
      0 ≤ fiveTermOp (singleShiftFamily a μ ν ⟨lam, hne.symm⟩) k :=
    fun k hk => fiveTermOp_nonneg hCal _ hUses hCurve hCar.1 hCar.2 hk
  have hOM := familyMonomial_const (singleShiftFamily a μ ν ⟨lam, hne.symm⟩) hOps.1
    (hOps.2 default) hUni
  have hobs : ∀ F ∈ localRegionObservables (a : ℝ) {x : Point | 0 ≤ x μ},
      IsBoundedObservable F := by
    intro F hF
    obtain ⟨Q, -, hF⟩ := mem_iUnion₂.mp hF
    exact hF.1
  have hcorr : ∀ F, IsBoundedObservable F → ∀ v : LatticePoint (a : ℝ),
      IsBoundedObservable (reflectedCorrelationFun a μ F v) := fun F hF v =>
    isBoundedObservable_conjFun_mul (InfiniteLattice.IsBoundedObservable.actOn hF _)
      (InfiniteLattice.IsBoundedObservable.actOn hF _)
  refine ⟨fun k hk => ?_, fun F hF k hk => ?_, fun F hF => ⟨fun v _ => ⟨hcorr F (hobs F hF) v, rfl⟩,
    fun k _ => ?_⟩⟩
  · have h := hfive k hk
    rw [fiveTermOp_eq _ hOps.1 (hOps.2 default) hUni] at h
    refine opGE_of_nonneg_sub ?_ h
    have hT : IsSelfAdjoint (transferOperator a μ ν) :=
      (isSymmetricOp_iff _).mp hM.1
    exact ((IsSelfAdjoint.one _).sub (hT.pow k)).pow 2
  · have hmem : F ∈ upperSpace a μ := by
      rw [← SetLike.mem_coe, coe_upperSpace]
      exact hF
    have h := inner_apply_nonneg_of_nonneg (hfive k hk) (siteClass a μ ν ⟨F, hmem⟩)
    have hv : ∀ (n : ℕ) (y : ℤ),
        ⟪siteClass a μ ν ⟨F, hmem⟩, FamilyPolynomials.familyMonomial
            (singleShiftFamily a μ ν ⟨lam, hne.symm⟩) n (fun _ => y) (siteClass a μ ν ⟨F, hmem⟩)⟫_ℂ =
          reflectedCorrelation a μ ν F (n • axisStep (a : ℝ) μ + y • axisStep (a : ℝ) lam) := by
      intro n y
      rw [hOM]
      exact hMatrix ⟨F, hmem⟩ ⟨F, hmem⟩ ⟨lam, hne.symm⟩ n y
    simp only [fiveTermOp, add_apply, smul_apply, inner_add_right, inner_smul_right, hv] at h
    have e₀ : (0 : ℕ) • axisStep (a : ℝ) μ + (0 : ℤ) • axisStep (a : ℝ) lam = 0 := by simp
    have e₁ : k • axisStep (a : ℝ) μ + (0 : ℤ) • axisStep (a : ℝ) lam = k • axisStep (a : ℝ) μ := by
      simp
    have e₂ : (2 * k) • axisStep (a : ℝ) μ + (0 : ℤ) • axisStep (a : ℝ) lam =
        (2 * k) • axisStep (a : ℝ) μ := by
      simp
    have e₃ : k • axisStep (a : ℝ) μ + (k : ℤ) • axisStep (a : ℝ) lam =
        k • axisStep (a : ℝ) μ + k • axisStep (a : ℝ) lam := by simp
    have e₄ : k • axisStep (a : ℝ) μ + (-(k : ℤ)) • axisStep (a : ℝ) lam =
        k • axisStep (a : ℝ) μ - k • axisStep (a : ℝ) lam := by
      rw [neg_smul, natCast_zsmul, sub_eq_add_neg]
    rw [e₀, e₁, e₂, e₃, e₄] at h
    unfold FivePointBound
    convert h using 1
    ring
  · have hc := hcorr F (hobs F hF)
    refine ⟨fun ν₁ ν₂ _ _ s h₀ h₁ => integral_mixState (hc _) ν₁ ν₂ h₀ h₁,
      fun ν₁ ν₂ _ _ s h₀ h₁ => ?_,
      fun ν₁ ν₂ _ _ s h₀ h₁ => integral_mixState (hc _) ν₁ ν₂ h₀ h₁,
      fun ν₁ ν₂ _ _ s h₀ h₁ => integral_mixState (hc _) ν₁ ν₂ h₀ h₁,
      fun ν₁ ν₂ _ _ s h₀ h₁ => integral_mixState (hc _) ν₁ ν₂ h₀ h₁⟩
    have := integral_mixState (hc (k • axisStep (a : ℝ) μ)) ν₁ ν₂ h₀ h₁
    change -4 * (∫ U, reflectedCorrelationFun a μ F _ U ∂(mixState s ν₁ ν₂)) =
      (s : ℂ) * (-4 * ∫ U, reflectedCorrelationFun a μ F _ U ∂ν₁) +
        (1 - (s : ℂ)) * (-4 * ∫ U, reflectedCorrelationFun a μ F _ U ∂ν₂)
    rw [this]
    ring
end CoarseStepFivePoint
end LatticeConventions
end YangMills.Construction
end
