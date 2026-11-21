import YangMills.Construction.InfiniteLattice.EveryPairOfDirectionsAndTheJointCarrierProof
import YangMills.Construction.ReflectionPositivity.CarrierOfTheSitePictureProof
import YangMills.Construction.ReflectionPositivity.EnergyMomentumMeasuresOfAPicture
import YangMills.Construction.ReflectionPositivity.SitePicturesOfADirection
import Mathlib
set_option autoImplicit false
open MeasureTheory Set Filter Topology
open scoped ENNReal ComplexConjugate
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.DirectionPictures.SpectralMeasures.Derivation
open ReflectionPositivity.MirrorHyperplanes (unitPositiveClass)
open HilbertSpace (SesqForm)
open JointSpectrum (CommutingFamily SpectralDomain spectralMonomial torusMonomial)
open FormHilbert
open EnergyMomentum
section Polarization
variable {V : Type*} [AddCommGroup V] [Module ℂ V]
theorem sesq_expand {b : SesqForm V} (hb : b.IsSesquilinear) (u v : V) (c : ℂ) :
    b (v + c • u) (v + c • u) =
      b v v + c * b v u + conj c * b u v + conj c * c * b u u := by
  rw [hb.add_left, hb.add_right, hb.add_right, hb.smul_left, hb.smul_left, hb.smul_right,
    hb.smul_right]
  ring
theorem sesq_polarization {b : SesqForm V} (hb : b.IsSesquilinear) (u v : V) :
    b u v = (1 / 4) * ∑ k ∈ Finset.range 4, Complex.I ^ k *
      b (v + Complex.I ^ k • u) (v + Complex.I ^ k • u) := by
  have hI3 : Complex.I ^ 3 = -Complex.I := by rw [pow_succ, Complex.I_sq]; ring
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, sesq_expand hb, pow_zero, pow_one,
    Complex.I_sq, hI3, map_one, map_neg, Complex.conj_I, zero_add]
  linear_combination (-(1 / 2) * (b v u - b u v)) * Complex.I_sq
theorem sesq_conjSymm_of_im_diag {b : SesqForm V} (hb : b.IsSesquilinear)
    (hr : ∀ w : V, (b w w).im = 0) : b.IsConjSymm := by
  intro u v
  have e₁ := sesq_expand hb u v 1
  have e₂ := sesq_expand hb u v Complex.I
  have r₁ := hr (v + (1 : ℂ) • u)
  have r₂ := hr (v + Complex.I • u)
  rw [e₁] at r₁
  rw [e₂] at r₂
  have du := hr u
  have dv := hr v
  simp only [map_one, one_mul, Complex.conj_I, Complex.add_im, Complex.mul_im, Complex.I_re,
    Complex.I_im, Complex.neg_re, Complex.neg_im, zero_mul, one_mul, zero_add, add_zero, neg_zero,
    Complex.mul_re, du, dv, mul_zero, neg_mul, Complex.mul_I_re, Complex.mul_I_im, neg_neg,
    Complex.I_mul_I, Complex.neg_re, Complex.one_re, Complex.one_im] at r₁ r₂
  apply Complex.ext
  · simp only [Complex.conj_re]
    linarith
  · simp only [Complex.conj_im]
    linarith
end Polarization
section Calculus
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {J : Type} [Fintype J] [Nonempty J]
def innerOpForm (A : H →L[ℂ] H) : SesqForm H := fun x y => inner ℂ x (A y)
theorem innerOpForm_isSesquilinear (A : H →L[ℂ] H) : (innerOpForm A).IsSesquilinear where
  add_left := fun _ _ _ => by simp [innerOpForm, inner_add_left]
  smul_left := fun _ _ _ => by simp [innerOpForm, inner_smul_left, mul_comm]
  add_right := fun _ _ _ => by simp [innerOpForm, inner_add_right]
  smul_right := fun _ _ _ => by simp [innerOpForm, inner_smul_right]
structure CalcSetup (S : CommutingFamily H J) (E : BorelPVM J H) : Prop where
  moment : ∀ u, HasSpectralMoments S u (spectralMomentMeasure S u)
  unique : ∀ u m, HasSpectralMoments S u m → m = spectralMomentMeasure S u
  spectral : IsJointPVM S E
  scalar : ∀ (u : H) (Δ : MeasSubset J),
    inner ℂ u (E Δ u) = (((spectralMomentMeasure S u).real Δ.1 : ℝ) : ℂ)
  calculus : BoundedFunctionalCalculus S E
  real : RealFunctionalCalculus E
variable {S : CommutingFamily H J} {E : BorelPVM J H}
theorem spectralOp_isSpectralIntegral {φ : SpectralDomain J → ℂ}
    (h : ∃ A, E.IsSpectralIntegral φ A) : E.IsSpectralIntegral φ (E.spectralOp φ) := by
  unfold BorelPVM.spectralOp
  rw [dif_pos h]
  exact Classical.choose_spec h
theorem spectralOp_eq_of_isSpectralIntegral {φ : SpectralDomain J → ℂ} {A : H →L[ℂ] H}
    (h : E.IsSpectralIntegral φ A) : E.spectralOp φ = A := by apply _root_.YangMills.Construction.ReflectionPositivity.SiteCarrier.spectralOp_eq <;> assumption
namespace CalcSetup
variable (st : CalcSetup S E)
include st
theorem finiteMeasure (u : H) : IsFiniteMeasure (spectralMomentMeasure S u) := (st.moment u).1
theorem quadMeasure_eq (u : H) : E.quadMeasure u = spectralMomentMeasure S u := by
  haveI := st.finiteMeasure u
  refine Measure.ext fun s hs => ?_
  have h₁ := E.quadMeasure_apply u ⟨s, hs⟩
  have h₂ := st.scalar u ⟨s, hs⟩
  rw [E.inner_apply_eq_norm_sq] at h₂
  have h₃ : ‖E ⟨s, hs⟩ u‖ ^ 2 = (spectralMomentMeasure S u).real s := by exact_mod_cast h₂
  simp only at h₁
  rw [h₁, h₃, ofReal_measureReal]
theorem inner_spectralOp_self {g : SpectralDomain J → ℂ} (hg : IsBddMeasurable g) (u : H) :
    inner ℂ u (E.spectralOp g u) = ∫ q, g q ∂(spectralMomentMeasure S u) := by
  rw [spectralOp_isSpectralIntegral (st.calculus.exists_spectralOp g hg) u, st.quadMeasure_eq]
theorem polar_sum_eq {g : SpectralDomain J → ℂ} (hg : IsBddMeasurable g) (u v : H) :
    (1 / 4) * ∑ k ∈ Finset.range 4, Complex.I ^ k *
        ∫ q, g q ∂(spectralMomentMeasure S (v + Complex.I ^ k • u)) =
      inner ℂ u (E.spectralOp g v) := by
  have h := sesq_polarization (innerOpForm_isSesquilinear (E.spectralOp g)) u v
  simp only [innerOpForm] at h
  rw [h]
  simp only [st.inner_spectralOp_self hg]
end CalcSetup
theorem isBddMeasurable_const (c : ℂ) : IsBddMeasurable (fun _ : SpectralDomain J => c) :=
  ⟨measurable_const, ‖c‖, fun _ => le_rfl⟩
theorem isBddMeasurable_add_mul {φ φ' : SpectralDomain J → ℂ} (h : IsBddMeasurable φ)
    (h' : IsBddMeasurable φ') (c : ℂ) : IsBddMeasurable (fun q => φ q + c * φ' q) := by apply _root_.YangMills.Construction.ReflectionPositivity.SiteCarrier.isBddMeasurable_add_mul <;> assumption
theorem isBddMeasurable_mul {φ φ' : SpectralDomain J → ℂ} (h : IsBddMeasurable φ)
    (h' : IsBddMeasurable φ') : IsBddMeasurable (fun q => φ q * φ' q) := by apply _root_.YangMills.Construction.ReflectionPositivity.SiteCarrier.isBddMeasurable_mul <;> assumption
theorem isBddMeasurable_conj {φ : SpectralDomain J → ℂ} (h : IsBddMeasurable φ) :
    IsBddMeasurable (fun q => conj (φ q)) := by
  obtain ⟨m, C, hC⟩ := h
  refine ⟨Complex.continuous_conj.measurable.comp m, C, fun q => ?_⟩
  rw [RCLike.norm_conj]
  exact hC q
theorem spectralMonomial_continuous (n : ℕ) (y : J → ℤ) :
    Continuous (spectralMonomial n y : SpectralDomain J → ℂ) := by
  unfold spectralMonomial torusMonomial
  refine Continuous.mul (by fun_prop) (continuous_finsetProd _ fun α _ => ?_)
  refine Continuous.zpow₀ (by fun_prop) _ fun q => Or.inl ?_
  exact Circle.coe_ne_zero _
theorem norm_torusMonomial_eq_one (ζ : J → Circle) (y : J → ℤ) : ‖torusMonomial ζ y‖ = 1 := by
  simp [torusMonomial, norm_prod, Circle.norm_coe]
theorem norm_spectralMonomial_le_one (n : ℕ) (y : J → ℤ) (q : SpectralDomain J) :
    ‖spectralMonomial n y q‖ ≤ 1 := by
  rw [spectralMonomial, norm_mul, norm_torusMonomial_eq_one, mul_one, norm_pow, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg q.1.2.1]
  exact pow_le_one₀ q.1.2.1 q.1.2.2
theorem isBddMeasurable_spectralMonomial (n : ℕ) (y : J → ℤ) :
    IsBddMeasurable (spectralMonomial n y : SpectralDomain J → ℂ) :=
  ⟨(spectralMonomial_continuous n y).measurable, 1, norm_spectralMonomial_le_one n y⟩
end Calculus
section Moments
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {J : Type} [Fintype J] [Nonempty J]
  {S : CommutingFamily H J} {E : BorelPVM J H}
theorem unitaryMonomial_zero (S : CommutingFamily H J) : S.unitaryMonomial 0 = 1 := by apply _root_.YangMills.Construction.LatticeConventions.DirectionPairsSupport.unitaryMonomial_zero <;> assumption
theorem CalcSetup.spectralOp_one (st : CalcSetup S E) : E.spectralOp (fun _ => 1) = 1 := by
  have h := st.calculus.spectralOp_monomial 0 0
  have e : (spectralMonomial 0 (0 : J → ℤ) : SpectralDomain J → ℂ) = fun _ => 1 := by
    funext q
    simp [spectralMonomial, torusMonomial]
  rw [e, pow_zero, unitaryMonomial_zero, one_mul] at h
  exact h
theorem CalcSetup.inner_unitaryMonomial_moment (st : CalcSetup S E) (n : ℕ) (y y' : J → ℤ)
    (u : H) :
    inner ℂ (S.unitaryMonomial y u) ((S.A ^ n * S.unitaryMonomial y') (S.unitaryMonomial y u)) =
      inner ℂ u ((S.A ^ n * S.unitaryMonomial y') u) := by
  have hc := st.calculus
  have hU : S.unitaryMonomial y = E.spectralOp (spectralMonomial 0 y) := by
    rw [hc.spectralOp_monomial, pow_zero, one_mul]
  have hm := isBddMeasurable_spectralMonomial (J := J) 0 y
  have hM := isBddMeasurable_spectralMonomial (J := J) n y'
  rw [← hc.spectralOp_monomial n y', hU]
  have h1 : ∀ v, inner ℂ (E.spectralOp (spectralMonomial 0 y) u) v =
      inner ℂ u (E.spectralOp (fun q => conj (spectralMonomial 0 y q)) v) := by
    intro v
    calc inner ℂ (E.spectralOp (spectralMonomial 0 y) u) v
        = conj (inner ℂ v (E.spectralOp (spectralMonomial 0 y) u)) := (inner_conj_symm _ _).symm
      _ = conj (inner ℂ (E.spectralOp (fun q => conj (spectralMonomial 0 y q)) v) u) := by
          rw [hc.inner_spectralOp _ hm u v]
      _ = inner ℂ u (E.spectralOp (fun q => conj (spectralMonomial 0 y q)) v) :=
          inner_conj_symm _ _
  rw [h1]
  have e1 := hc.spectralOp_mul (spectralMonomial n y') (spectralMonomial 0 y) hM hm
  have e2 := hc.spectralOp_mul (fun q => conj (spectralMonomial 0 y q))
    (fun q => spectralMonomial n y' q * spectralMonomial 0 y q) (isBddMeasurable_conj hm)
    (isBddMeasurable_mul hM hm)
  have e3 : (fun q => conj (spectralMonomial 0 y q) *
      (spectralMonomial n y' q * spectralMonomial 0 y q)) = spectralMonomial n y' := by
    funext q
    have h : conj (spectralMonomial 0 y q) * spectralMonomial 0 y q = 1 := by
      have hn : ‖spectralMonomial 0 y q‖ = 1 := by
        simp [spectralMonomial, norm_torusMonomial_eq_one]
      rw [Complex.conj_mul', hn]
      simp
    linear_combination (spectralMonomial n y' q) * h
  rw [e3, e1] at e2
  have e4 := congrArg (fun T : H →L[ℂ] H => T u) e2
  simp only [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply] at e4
  rw [← e4]
def coneDefect (l : J) (q : SpectralDomain J) : ℝ :=
  (1 - (q.1 : ℝ)) ^ 2 - (q.1 : ℝ) * ‖1 - (q.2 l : ℂ)‖ ^ 2
theorem continuous_coneDefect (l : J) : Continuous (coneDefect l) := by
  unfold coneDefect
  fun_prop
theorem abs_coneDefect_le (l : J) (q : SpectralDomain J) :
    |coneDefect l q| ≤ 5 := by
  have h0 := q.1.2.1
  have h1 := q.1.2.2
  have hz : ‖1 - (q.2 l : ℂ)‖ ≤ 2 := by
    refine (norm_sub_le _ _).trans ?_
    rw [Circle.norm_coe, norm_one]
    norm_num
  have hz2 : ‖1 - (q.2 l : ℂ)‖ ^ 2 ≤ 4 := by
    have := norm_nonneg (1 - (q.2 l : ℂ))
    nlinarith
  have hb : (q.1 : ℝ) * ‖1 - (q.2 l : ℂ)‖ ^ 2 ≤ 4 := by
    have := sq_nonneg ‖1 - (q.2 l : ℂ)‖
    nlinarith
  have hb0 : 0 ≤ (q.1 : ℝ) * ‖1 - (q.2 l : ℂ)‖ ^ 2 := by positivity
  have ha : (1 - (q.1 : ℝ)) ^ 2 ≤ 1 := by nlinarith
  have ha0 := sq_nonneg (1 - (q.1 : ℝ))
  rw [coneDefect, abs_le]
  constructor <;> linarith
theorem coneDefect_eq (l : J) (q : SpectralDomain J) :
    ((coneDefect l q : ℝ) : ℂ) =
      (1 + -1 * ((q.1 : ℝ) : ℂ)) * (1 + -1 * ((q.1 : ℝ) : ℂ)) +
        -1 * (((q.1 : ℝ) : ℂ) * (1 + 1 * 1 + -1 * (q.2 l : ℂ) + -1 * conj (q.2 l : ℂ))) := by
  have hz : conj (q.2 l : ℂ) * (q.2 l : ℂ) = 1 := by
    rw [Complex.conj_mul', Circle.norm_coe]
    simp
  have hn := Complex.conj_mul' (1 - (q.2 l : ℂ))
  simp only [coneDefect]
  push_cast
  rw [← hn]
  simp only [map_sub, map_one]
  linear_combination (-((q.1 : ℝ) : ℂ)) * hz
theorem CalcSetup.moment_negPart_null (st : CalcSetup S E) (l : J)
    (hY : S.A * ((2 : ℂ) • 1 - (S.B l : H →L[ℂ] H) - star (S.B l : H →L[ℂ] H)) ≤ (1 - S.A) ^ 2)
    (u : H) : spectralMomentMeasure S u {q | coneDefect l q < 0} = 0 := by
  have hc := st.calculus
  have hA : E.spectralOp (fun q => ((q.1 : ℝ) : ℂ)) = S.A :=
    spectralOp_eq_of_isSpectralIntegral st.spectral.1
  have hB : E.spectralOp (fun q => ((q.2 l : Circle) : ℂ)) = (S.B l : H →L[ℂ] H) :=
    spectralOp_eq_of_isSpectralIntegral (st.spectral.2 l)
  have b1 : IsBddMeasurable (fun _ : SpectralDomain J => (1 : ℂ)) := isBddMeasurable_const 1
  have bt : IsBddMeasurable (fun q : SpectralDomain J => ((q.1 : ℝ) : ℂ)) := by
    refine ⟨(Complex.continuous_ofReal.comp
      (continuous_subtype_val.comp continuous_fst)).measurable, 1, fun q => ?_⟩
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg q.1.2.1]
    exact q.1.2.2
  have bz : IsBddMeasurable (fun q : SpectralDomain J => ((q.2 l : Circle) : ℂ)) := by
    refine ⟨Continuous.measurable (by fun_prop), 1, fun q => ?_⟩
    rw [Circle.norm_coe]
  have hBc : E.spectralOp (fun q => conj ((q.2 l : Circle) : ℂ)) =
      star (S.B l : H →L[ℂ] H) := by
    refine ContinuousLinearMap.ext fun v => ext_inner_right ℂ fun w => ?_
    rw [← hc.inner_spectralOp _ bz w v, hB, ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.adjoint_inner_left]
  have h1 := st.spectralOp_one
  have bf := isBddMeasurable_add_mul b1 bt (-1)
  have hf := hc.spectralOp_add_smul _ _ b1 bt (-1)
  have b2 := isBddMeasurable_add_mul b1 b1 1
  have h2 := hc.spectralOp_add_smul _ _ b1 b1 1
  have bg1 := isBddMeasurable_add_mul b2 bz (-1)
  have hg1 := hc.spectralOp_add_smul _ _ b2 bz (-1)
  have bg := isBddMeasurable_add_mul bg1 (isBddMeasurable_conj bz) (-1)
  have hg := hc.spectralOp_add_smul _ _ bg1 (isBddMeasurable_conj bz) (-1)
  have hff := hc.spectralOp_mul _ _ bf bf
  have htg := hc.spectralOp_mul _ _ bt bg
  have hall := hc.spectralOp_add_smul _ _ (isBddMeasurable_mul bf bf)
    (isBddMeasurable_mul bt bg) (-1)
  have e : (fun q : SpectralDomain J => ((coneDefect l q : ℝ) : ℂ)) = _ :=
    funext (coneDefect_eq l)
  have hI : E.spectralOp (fun q : SpectralDomain J => ((coneDefect l q : ℝ) : ℂ)) =
      (1 - S.A) ^ 2 - S.A * ((2 : ℂ) • 1 - (S.B l : H →L[ℂ] H) - star (S.B l : H →L[ℂ] H)) := by
    rw [e, hall, hff, htg, hg, hg1, h2, hf, h1, hA, hB, hBc]
    simp only [neg_smul, one_smul, two_smul, sq, sub_eq_add_neg, neg_one_mul]
  have hφ : Measurable (coneDefect (J := J) l) := (continuous_coneDefect l).measurable
  have hr := st.real (coneDefect l) hφ ⟨5, abs_coneDefect_le l⟩
  have hpos : 0 ≤ E.spectralOp (fun q : SpectralDomain J => ((coneDefect l q : ℝ) : ℂ)) := by
    rw [hI]
    exact sub_nonneg.mpr hY
  have hcar := hr.2.mp hpos
  have hset : {q | coneDefect l q < 0} = {q | 0 ≤ coneDefect l q}ᶜ := by
    ext q
    simp
  have h0 : E ⟨{q | 0 ≤ coneDefect l q}ᶜ, (measurableSet_le measurable_const hφ).compl⟩ = 0 :=
    hcar
  rw [hset, ← st.quadMeasure_eq,
    E.quadMeasure_apply u ⟨_, (measurableSet_le measurable_const hφ).compl⟩, h0]
  simp
end Moments
section Chart
variable {μ : Fin 4}
theorem chart_eq_pair (x : SpectralSpace μ) :
    chart μ x = (expNegEnergy x.energy, fun l => Circle.exp (x.momentum l)) := rfl
theorem chart_continuous : Continuous (chart μ) :=
  (chartHomeomorph μ).continuous
theorem chart_symm_continuous : Continuous (chart μ).symm :=
  (chartHomeomorph μ).symm.continuous
def orthPoint (y : TransverseAxis μ → ℤ) : orthLattice μ :=
  ⟨fun i => if h : i ≠ μ then y ⟨i, h⟩ else 0, by simp [mem_orthLattice]⟩
def orthCoords (w : orthLattice μ) : TransverseAxis μ → ℤ :=
  fun l => (w : Fin 4 → ℤ) l.1
theorem orthCoords_orthPoint (y : TransverseAxis μ → ℤ) :
    orthCoords (orthPoint y) = y := by
  funext l
  simp [orthCoords, orthPoint, l.2]
theorem emMonomial_eq (n : ℕ) (w : orthLattice μ) (x : SpectralSpace μ) :
    energyMomentumMonomial μ n w x = spectralMonomial n (orthCoords w) (chart μ x) := by
  simp only [energyMomentumMonomial, spectralMonomial, torusMonomial, chart_eq_pair,
    expNegNatMulEnergy, angleDot, orthCoords]
  push_cast
  congr 1
  rw [Finset.mul_sum, Complex.exp_sum]
  refine Finset.prod_congr rfl fun l _ => ?_
  rw [← Complex.exp_int_mul]
  congr 1
  ring
theorem emMonomial_comp_symm (n : ℕ) (w : orthLattice μ) :
    energyMomentumMonomial μ n w ∘ (chart μ).symm = spectralMonomial n (orthCoords w) := by
  funext q
  simp [emMonomial_eq]
theorem emMonomial_continuous (n : ℕ) (w : orthLattice μ) :
    Continuous (energyMomentumMonomial μ n w) := by
  have h : energyMomentumMonomial μ n w = spectralMonomial n (orthCoords w) ∘ (chart μ) := by
    funext x
    exact emMonomial_eq n w x
  rw [h]
  exact (spectralMonomial_continuous n _).comp chart_continuous
theorem emMonomial_isBoundedBorelFn (n : ℕ) (w : orthLattice μ) :
    IsBoundedBorelFn (energyMomentumMonomial μ n w) :=
  ⟨(emMonomial_continuous n w).measurable, 1, fun x => by
    rw [emMonomial_eq]
    exact norm_spectralMonomial_le_one _ _ _⟩
theorem isBddMeasurable_comp_chart_symm {φ : SpectralSpace μ → ℂ}
    (h : IsBoundedBorelFn φ) : IsBddMeasurable (φ ∘ (chart μ).symm) := by
  obtain ⟨m, C, hC⟩ := h
  exact ⟨m.comp chart_symm_continuous.measurable, C, fun q => hC _⟩
theorem mem_cone_iff (x : SpectralSpace μ) :
    x ∈ coneInSpectral μ ↔ ∀ l, 0 ≤ coneDefect l (chart μ x) := by
  have key : ∀ l, coneDefect l (chart μ x) =
      (1 - ((expNegEnergy x.1.1 : unitInterval) : ℝ)) ^ 2 -
        ((expNegEnergy x.1.1 : unitInterval) : ℝ) *
          ‖1 - Complex.exp (Complex.I * (x.1.2 l : ℂ))‖ ^ 2 := by
    intro l
    have e : ((Circle.exp (x.momentum l) : Circle) : ℂ) =
        Complex.exp (Complex.I * (x.1.2 l : ℂ)) := by
      rw [Circle.coe_exp, mul_comm]
      rfl
    simp only [coneDefect, chart_eq_pair, e]
    rfl
  constructor
  · rintro ⟨-, h⟩ l
    rw [key]
    exact sub_nonneg.mpr (h l)
  · intro h
    refine ⟨x.2, fun l => ?_⟩
    have := h l
    rw [key] at this
    exact sub_nonneg.mp this
theorem zeta_continuous (l : TransverseAxis μ) :
    Continuous fun x : SpectralSpace μ => (((chart μ x).2 l : Circle) : ℂ) := by
  have c : Continuous fun q : SpectralDomain (TransverseAxis μ) => ((q.2 l : Circle) : ℂ) := by
    fun_prop
  exact c.comp chart_continuous
theorem energyOfUnit_measurable : Measurable energyOfUnit := by
  unfold energyOfUnit
  refine Measurable.ite ?_ measurable_const ?_
  · exact (measurableSet_singleton (0 : ℝ)).preimage measurable_subtype_coe
  · exact ENNReal.measurable_ofReal.comp
      (Real.measurable_log.comp measurable_subtype_coe).neg
theorem momentum_measurable (l : TransverseAxis μ) :
    Measurable fun x : SpectralSpace μ => x.momentum l := by
  have h : (fun x : SpectralSpace μ => x.momentum l) =
      fun x => Complex.arg ((chart μ x).2 l : ℂ) := by
    funext x
    exact (Circle.arg_exp (x.2 l).1 (x.2 l).2).symm
  rw [h]
  exact Complex.measurable_arg.comp (zeta_continuous l).measurable
theorem spectralSpaceProps (μ : Fin 4) : SpectralSpaceProps μ := by
  have hchart := chart_continuous (μ := μ)
  refine ⟨(chartHomeomorph μ).symm.compactSpace,
    (chartHomeomorph μ).isEmbedding.metrizableSpace, inferInstance,
    fun f => continuous_iff_continuous_comp_chart_symm,
    fun T => measurableSet_iff_measurableSet_chart_image,
    fun n w => emMonomial_continuous n w, ?_, ?_, ?_, ?_, ?_, fun l => momentum_measurable l,
    ?_⟩
  · have h : coneInSpectral μ =
        ⋂ l, (fun x => coneDefect l (chart μ x)) ⁻¹' Ici 0 := by
      ext x
      simp [mem_cone_iff]
    rw [h]
    exact isClosed_iInter fun l =>
      isClosed_Ici.preimage ((continuous_coneDefect l).comp hchart)
  · intro f hf e
    have h : ∀ η, f (spectralPointOf μ e η) =
        (f ∘ (chart μ).symm) (expNegEnergy e, toCircles μ η) := by
      intro η
      have e' : chart μ (spectralPointOf μ e η) = (expNegEnergy e, toCircles μ η) := by
        refine Prod.ext rfl (funext fun l => ?_)
        change Circle.exp (boxRep μ η l) = toCircles μ η l
        rw [← toCircles_torusProj, torusProj_boxRep]
      rw [← e']
      simp
    simp_rw [h]
    exact (continuous_iff_continuous_comp_chart_symm.mp hf).comp
      (continuous_const.prodMk (toCircles μ).continuous)
  · have h : Continuous fun x : SpectralSpace μ => (((chart μ x).1 : unitInterval) : ℝ) :=
      continuous_subtype_val.comp (continuous_fst.comp hchart)
    exact h.measurable
  · have h : (fun x : SpectralSpace μ => x.energy) =
        fun x => energyOfUnit (chart μ x).1 := by
      funext x
      exact (energyOfUnit_expNegEnergy _).symm
    rw [h]
    exact energyOfUnit_measurable.comp (continuous_fst.comp hchart).measurable
  · intro l
    have h : (fun x : SpectralSpace μ => Complex.exp (Complex.I * (x.momentum l : ℂ))) =
        fun x => (((chart μ x).2 l : Circle) : ℂ) := by
      funext x
      simp only [chart_eq_pair, Circle.coe_exp, mul_comm]
    rw [h]
    exact (zeta_continuous l).measurable
  · exact (continuous_torusProj μ).measurable.comp
      (measurable_pi_lambda _ fun l => momentum_measurable l)
end Chart
section Density
variable {μ : Fin 4}
theorem comp_chart_mem_energyMomentumPolys {q : SpectralDomain (TransverseAxis μ) → ℂ}
    (hq : q ∈ JointSpectrum.spectralPolynomials (TransverseAxis μ)) :
    q ∘ chart μ ∈ energyMomentumPolys μ := by
  obtain ⟨s, c, h⟩ := hq
  have e : q ∘ chart μ = ∑ i ∈ s, c i • energyMomentumMonomial μ i.1 (orthPoint i.2) := by
    funext x
    simp [h, Finset.sum_apply, emMonomial_eq, orthCoords_orthPoint]
  rw [e]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _
    (Submodule.subset_span ⟨(i.1, orthPoint i.2), rfl⟩)
theorem map_chart_map_symm (σ : Measure (SpectralSpace μ)) :
    (σ.map (chartMeasurableEquiv μ)).map (chartMeasurableEquiv μ).symm = σ := by
  rw [Measure.map_map (chartMeasurableEquiv μ).symm.measurable
    (chartMeasurableEquiv μ).measurable]
  simp
theorem integrable_of_isBoundedBorelFn {σ : Measure (SpectralSpace μ)} [IsFiniteMeasure σ]
    {φ : SpectralSpace μ → ℂ} (h : IsBoundedBorelFn φ) : Integrable φ σ := by
  obtain ⟨m, C, hC⟩ := h
  exact Integrable.of_bound m.aestronglyMeasurable C (ae_of_all _ hC)
def posPartCombo {k : ℕ} (a : Fin k → ℝ) (σ : Fin k → Measure (SpectralSpace μ)) :
    Measure (SpectralSpace μ) :=
  ∑ i, ENNReal.ofReal (a i) • σ i
theorem isFiniteMeasure_posPartCombo {k : ℕ} (a : Fin k → ℝ)
    (σ : Fin k → Measure (SpectralSpace μ)) (hσ : ∀ i, IsFiniteMeasure (σ i)) :
    IsFiniteMeasure (posPartCombo a σ) := by
  refine ⟨?_⟩
  rw [posPartCombo, Measure.finsetSum_apply]
  refine ENNReal.sum_lt_top.mpr fun i _ => ?_
  rw [Measure.smul_apply, smul_eq_mul]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)
theorem integral_posPartCombo {k : ℕ} (a : Fin k → ℝ)
    (σ : Fin k → Measure (SpectralSpace μ)) (hσ : ∀ i, IsFiniteMeasure (σ i))
    {φ : SpectralSpace μ → ℂ} (h : IsBoundedBorelFn φ) :
    ∫ x, φ x ∂posPartCombo a σ = ∑ i, ((max (a i) 0 : ℝ) : ℂ) * ∫ x, φ x ∂σ i := by
  rw [posPartCombo, integral_finsetSum_measure]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_smul_measure, ENNReal.toReal_ofReal', Complex.real_smul]
  · intro i _
    have := hσ i
    exact (integrable_of_isBoundedBorelFn h).smul_measure ENNReal.ofReal_ne_top
theorem realCombo_eq_zero
    (hdet : ∀ (ρ ρ' : Measure (SpectralDomain (TransverseAxis μ))) [IsFiniteMeasure ρ]
      [IsFiniteMeasure ρ'], (∀ (n : ℕ) (y : TransverseAxis μ → ℤ),
        ∫ q, spectralMonomial n y q ∂ρ = ∫ q, spectralMonomial n y q ∂ρ') → ρ = ρ')
    {k : ℕ} (a : Fin k → ℝ) (σ : Fin k → Measure (SpectralSpace μ))
    (hσ : ∀ i, IsFiniteMeasure (σ i))
    (h : ∀ (n : ℕ) (w : orthLattice μ),
      ∑ i, (a i : ℂ) * ∫ x, energyMomentumMonomial μ n w x ∂σ i = 0)
    {φ : SpectralSpace μ → ℂ} (hφ : IsBoundedBorelFn φ) :
    ∑ i, (a i : ℂ) * ∫ x, φ x ∂σ i = 0 := by
  have hP := isFiniteMeasure_posPartCombo a σ hσ
  have hN := isFiniteMeasure_posPartCombo (fun i => -a i) σ hσ
  have diff : ∀ {g : SpectralSpace μ → ℂ}, IsBoundedBorelFn g →
      ∫ x, g x ∂posPartCombo a σ - ∫ x, g x ∂posPartCombo (fun i => -a i) σ =
        ∑ i, (a i : ℂ) * ∫ x, g x ∂σ i := by
    intro g hg
    rw [integral_posPartCombo a σ hσ hg,
      integral_posPartCombo (fun i => -a i) σ hσ hg, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← sub_mul, ← Complex.ofReal_sub, max_zero_sub_max_neg_zero_eq_self]
  have hmap : (posPartCombo a σ).map (chartMeasurableEquiv μ) =
      (posPartCombo (fun i => -a i) σ).map (chartMeasurableEquiv μ) := by
    refine hdet _ _ fun n y => ?_
    rw [(chartMeasurableEquiv μ).measurableEmbedding.integral_map,
      (chartMeasurableEquiv μ).measurableEmbedding.integral_map]
    have e : ∀ x, spectralMonomial n y (chartMeasurableEquiv μ x) =
        energyMomentumMonomial μ n (orthPoint y) x := by
      intro x
      rw [emMonomial_eq, orthCoords_orthPoint]
      rfl
    simp only [e]
    exact sub_eq_zero.mp ((diff (emMonomial_isBoundedBorelFn n _)).trans (h n _))
  have hPN : posPartCombo a σ = posPartCombo (fun i => -a i) σ := by
    rw [← map_chart_map_symm (posPartCombo a σ), hmap, map_chart_map_symm]
  rw [← diff hφ, hPN, sub_self]
theorem conj_emMonomial_neg (n : ℕ) (w : orthLattice μ) (x : SpectralSpace μ) :
    conj (energyMomentumMonomial μ n (-w) x) = energyMomentumMonomial μ n w x := by
  have hd : angleDot μ x.momentum ((-w : orthLattice μ) : Fin 4 → ℤ) =
      -angleDot μ x.momentum (w : Fin 4 → ℤ) := by
    simp [angleDot]
  simp only [energyMomentumMonomial, map_mul, Complex.conj_ofReal, ← Complex.exp_conj, hd,
    Complex.conj_I]
  congr 2
  push_cast
  ring
theorem monomialDensity (hs : ScalarSpectralMeasures.ScalarSpectralMeasuresStatement)
    (μ : Fin 4) : MonomialDensity μ := by
  have hS := hs ℂ (TransverseAxis μ)
    (Classical.arbitrary (CommutingFamily ℂ (TransverseAxis μ)))
  have hdense := hS.1
  have hdet := hS.2.2.1
  refine ⟨fun f hf => ?_, fun k σ c hσ h φ hφ => ?_⟩
  · let g : C(SpectralDomain (TransverseAxis μ), ℂ) :=
      ⟨f ∘ (chart μ).symm, continuous_iff_continuous_comp_chart_symm.mp hf⟩
    choose G hG hd using fun j : ℕ =>
      hdense.exists_dist_lt g (Nat.one_div_pos_of_nat (α := ℝ) (n := j))
    refine ⟨fun j => G j ∘ chart μ, fun j => comp_chart_mem_energyMomentumPolys (hG j), ?_⟩
    refine Metric.tendstoUniformly_iff.mpr fun ε hε => ?_
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt hε
    filter_upwards [eventually_ge_atTop N] with j hj x
    have h₁ : dist (g (chart μ x)) (G j (chart μ x)) ≤ dist g (G j) :=
      ContinuousMap.dist_apply_le_dist _
    have h₂ : g (chart μ x) = f x := by simp [g]
    rw [h₂] at h₁
    have h₃ : (1 : ℝ) / ((j : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.succ_le_succ hj)
    exact lt_of_le_of_lt h₁ (((hd j).trans_le h₃).trans hN)
  · have hconj : ∀ (n : ℕ) (w : orthLattice μ),
        ∑ i, conj (c i) * ∫ x, energyMomentumMonomial μ n w x ∂σ i = 0 := by
      intro n w
      have h' := congrArg conj (h n (-w))
      simp only [map_sum, map_mul, map_zero] at h'
      rw [← h']
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← integral_conj]
      simp only [conj_emMonomial_neg]
    have hre : ∀ X : Fin k → ℂ, ∑ i, ((c i).re : ℂ) * X i =
        (1 / 2) * (∑ i, c i * X i + ∑ i, conj (c i) * X i) := by
      intro X
      rw [← Finset.sum_add_distrib, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      have := Complex.add_conj (c i)
      push_cast at this
      linear_combination (-(1 / 2) * X i) * this
    have him : ∀ X : Fin k → ℂ, ∑ i, ((c i).im : ℂ) * X i =
        (-Complex.I / 2) * (∑ i, c i * X i - ∑ i, conj (c i) * X i) := by
      intro X
      rw [← Finset.sum_sub_distrib, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      have h₁ := Complex.sub_conj (c i)
      push_cast at h₁
      linear_combination (Complex.I / 2 * X i) * h₁ + (((c i).im : ℂ) * X i) * Complex.I_sq
    have ha := realCombo_eq_zero hdet (fun i => (c i).re) σ hσ
      (fun n w => by rw [hre, h n w, hconj n w]; simp) hφ
    have hb := realCombo_eq_zero hdet (fun i => (c i).im) σ hσ
      (fun n w => by rw [him, h n w, hconj n w]; simp) hφ
    have e : ∑ i, c i * ∫ x, φ x ∂σ i =
        ∑ i, ((c i).re : ℂ) * ∫ x, φ x ∂σ i +
          Complex.I * ∑ i, ((c i).im : ℂ) * ∫ x, φ x ∂σ i := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      conv_lhs => rw [← Complex.re_add_im (c i)]
      ring
    rw [e, ha, hb]
    simp
end Density
section OnePair
variable {p : ReflectionPair} {ν : unitPositiveClass} {μ : Fin 4}
theorem shiftMonomial_eq (w : orthLattice μ) :
    p.shiftMonomial ν μ (w : Fin 4 → ℤ) = (p.opFamily ν μ).unitaryMonomial (orthCoords w) := rfl
theorem hasSpectralMoments_map {u : p.Hilb ν μ} {σ : Measure (SpectralSpace μ)}
    (h : p.IsSpectralMeasure ν μ u σ) :
    HasSpectralMoments (p.opFamily ν μ) u (σ.map (chartMeasurableEquiv μ)) := by
  have := h.1
  refine ⟨inferInstance, fun n y => ?_⟩
  rw [(chartMeasurableEquiv μ).measurableEmbedding.integral_map]
  have e := h.2 n (orthPoint y)
  have e1 : ∀ x, energyMomentumMonomial μ n (orthPoint y) x =
      spectralMonomial n y (chartMeasurableEquiv μ x) := by
    intro x
    rw [emMonomial_eq, orthCoords_orthPoint]
    rfl
  simp only [e1] at e
  rw [← e]
  have e2 : p.shiftMonomial ν μ ((orthPoint y : orthLattice μ) : Fin 4 → ℤ) =
      (p.opFamily ν μ).unitaryMonomial y := by
    rw [shiftMonomial_eq, orthCoords_orthPoint]
  rw [e2]
  rfl
theorem isSpectralMeasure_map {u : p.Hilb ν μ}
    {m : Measure (SpectralDomain (TransverseAxis μ))}
    (h : HasSpectralMoments (p.opFamily ν μ) u m) :
    p.IsSpectralMeasure ν μ u (m.map (chartMeasurableEquiv μ).symm) := by
  have := h.1
  refine ⟨inferInstance, fun n w => ?_⟩
  rw [(chartMeasurableEquiv μ).symm.measurableEmbedding.integral_map]
  have e1 : ∀ q, energyMomentumMonomial μ n w ((chartMeasurableEquiv μ).symm q) =
      spectralMonomial n (orthCoords w) q := congrFun (emMonomial_comp_symm n w)
  simp only [e1]
  exact (h.2 n _).symm
variable {E : BorelPVM (TransverseAxis μ) (p.Hilb ν μ)}
theorem eq_map_of_isSpectralMeasure (st : CalcSetup (p.opFamily ν μ) E) {u : p.Hilb ν μ}
    {σ : Measure (SpectralSpace μ)} (h : p.IsSpectralMeasure ν μ u σ) :
    σ = (spectralMomentMeasure (p.opFamily ν μ) u).map (chartMeasurableEquiv μ).symm := by
  rw [← st.unique u _ (hasSpectralMoments_map h), map_chart_map_symm]
theorem spectralMeasure_eq_map (st : CalcSetup (p.opFamily ν μ) E) (u : p.Hilb ν μ) :
    p.spectralMeasure ν μ u =
      (spectralMomentMeasure (p.opFamily ν μ) u).map (chartMeasurableEquiv μ).symm := by
  have h : ∃ σ, p.IsSpectralMeasure ν μ u σ := ⟨_, isSpectralMeasure_map (st.moment u)⟩
  unfold ReflectionPair.spectralMeasure
  rw [dif_pos h]
  exact eq_map_of_isSpectralMeasure st h.choose_spec
theorem isSpectralMeasure_spectralMeasure (st : CalcSetup (p.opFamily ν μ) E) (u : p.Hilb ν μ) :
    p.IsSpectralMeasure ν μ u (p.spectralMeasure ν μ u) := by
  rw [spectralMeasure_eq_map st]
  exact isSpectralMeasure_map (st.moment u)
theorem integral_spectralMeasure (st : CalcSetup (p.opFamily ν μ) E) {G : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] (F : SpectralSpace μ → G) (u : p.Hilb ν μ) :
    ∫ x, F x ∂p.spectralMeasure ν μ u =
      ∫ q, F ((chart μ).symm q) ∂spectralMomentMeasure (p.opFamily ν μ) u := by
  rw [spectralMeasure_eq_map st,
    (chartMeasurableEquiv μ).symm.measurableEmbedding.integral_map]
  rfl
theorem spectralIntegral_eq_inner (st : CalcSetup (p.opFamily ν μ) E) {φ : SpectralSpace μ → ℂ}
    (hφ : IsBoundedBorelFn φ) (u v : p.Hilb ν μ) :
    p.spectralIntegral ν μ u v φ = inner ℂ u (E.spectralOp (φ ∘ (chart μ).symm) v) := by
  rw [← st.polar_sum_eq (isBddMeasurable_comp_chart_symm hφ) u v]
  unfold ReflectionPair.spectralIntegral polarIntegral
  simp only [integral_spectralMeasure st, Function.comp]
theorem spectralMeasure_univ (st : CalcSetup (p.opFamily ν μ) E) (u : p.Hilb ν μ) :
    p.spectralMeasure ν μ u univ = ENNReal.ofReal (‖u‖ ^ 2) := by
  have hσ := isSpectralMeasure_spectralMeasure st u
  have := hσ.1
  have h0 := hσ.2 0 0
  have e0 : energyMomentumMonomial μ 0 (0 : orthLattice μ) = fun _ => 1 := by
    funext x
    rw [emMonomial_eq]
    simp [spectralMonomial, torusMonomial, orthCoords]
  have e1 : p.shiftMonomial ν μ ((0 : orthLattice μ) : Fin 4 → ℤ) = 1 :=
    unitaryMonomial_zero (p.opFamily ν μ)
  rw [e0, e1, pow_zero, one_mul, one_apply_eq_self, inner_self_eq_norm_sq_to_K,
    integral_const] at h0
  have h1 : ‖u‖ ^ 2 = (p.spectralMeasure ν μ u).real univ := by
    have h2 : ((‖u‖ ^ 2 : ℝ) : ℂ) = (((p.spectralMeasure ν μ u).real univ : ℝ) : ℂ) := by
      simpa using h0
    exact_mod_cast h2
  rw [h1, ofReal_measureReal]
theorem uniqueSpectralMeasure (st : CalcSetup (p.opFamily ν μ) E) :
    UniqueSpectralMeasure p ν μ := by
  intro u
  have hσ := isSpectralMeasure_spectralMeasure st u
  refine ⟨⟨_, hσ, fun σ h => ?_⟩, hσ, spectralMeasure_univ st u, fun c => ?_⟩
  · rw [eq_map_of_isSpectralMeasure st h, spectralMeasure_eq_map st]
  · have := hσ.1
    have hh : p.IsSpectralMeasure ν μ (c • u)
        (ENNReal.ofReal (‖c‖ ^ 2) • p.spectralMeasure ν μ u) := by
      refine ⟨Measure.smul_finite _ ENNReal.ofReal_ne_top, fun n w => ?_⟩
      rw [integral_smul_measure, ← hσ.2 n w, map_smul, inner_smul_left, inner_smul_right,
        ENNReal.toReal_ofReal (by positivity), Complex.real_smul]
      push_cast
      rw [← Complex.conj_mul']
      ring
    rw [eq_map_of_isSpectralMeasure st hh, spectralMeasure_eq_map st]
theorem spectralIntegral_add (st : CalcSetup (p.opFamily ν μ) E) {φ₁ φ₂ : SpectralSpace μ → ℂ}
    (h₁ : IsBoundedBorelFn φ₁) (h₂ : IsBoundedBorelFn φ₂) (u v : p.Hilb ν μ) :
    p.spectralIntegral ν μ u v (φ₁ + φ₂) =
      p.spectralIntegral ν μ u v φ₁ + p.spectralIntegral ν μ u v φ₂ := by
  have h₃ : IsBoundedBorelFn (φ₁ + φ₂) := by
    obtain ⟨m₁, C₁, hC₁⟩ := h₁
    obtain ⟨m₂, C₂, hC₂⟩ := h₂
    exact ⟨m₁.add m₂, C₁ + C₂, fun x => (norm_add_le _ _).trans (add_le_add (hC₁ x) (hC₂ x))⟩
  have e : (φ₁ + φ₂) ∘ (chart μ).symm = fun q =>
      (φ₁ ∘ (chart μ).symm) q + 1 * (φ₂ ∘ (chart μ).symm) q := by
    funext q
    simp
  rw [spectralIntegral_eq_inner st h₃, spectralIntegral_eq_inner st h₁,
    spectralIntegral_eq_inner st h₂, e,
    st.calculus.spectralOp_add_smul _ _ (isBddMeasurable_comp_chart_symm h₁)
      (isBddMeasurable_comp_chart_symm h₂) 1]
  simp [inner_add_right]
theorem isBoundedBorelFn_smul {φ : SpectralSpace μ → ℂ} (h : IsBoundedBorelFn φ) (c : ℂ) :
    IsBoundedBorelFn (c • φ) := by
  obtain ⟨m, C, hC⟩ := h
  refine ⟨m.const_smul c, ‖c‖ * C, fun x => ?_⟩
  rw [Pi.smul_apply, norm_smul]
  exact mul_le_mul_of_nonneg_left (hC x) (norm_nonneg _)
theorem spectralIntegral_smul (st : CalcSetup (p.opFamily ν μ) E) {φ : SpectralSpace μ → ℂ}
    (h : IsBoundedBorelFn φ) (c : ℂ) (u v : p.Hilb ν μ) :
    p.spectralIntegral ν μ u v (c • φ) = c * p.spectralIntegral ν μ u v φ := by
  have h0 : E.spectralOp (fun _ => 0) = 0 :=
    spectralOp_eq_of_isSpectralIntegral fun u => by simp
  have e : (c • φ) ∘ (chart μ).symm = fun q =>
      (fun _ => (0 : ℂ)) q + c * (φ ∘ (chart μ).symm) q := by
    funext q
    simp
  rw [spectralIntegral_eq_inner st (isBoundedBorelFn_smul h c), spectralIntegral_eq_inner st h, e,
    st.calculus.spectralOp_add_smul _ _ (isBddMeasurable_const 0)
      (isBddMeasurable_comp_chart_symm h) c, h0]
  simp [inner_smul_right]
theorem integralLinear (st : CalcSetup (p.opFamily ν μ) E) : IntegralLinear p ν μ := by
  refine ⟨fun u v φ₁ φ₂ h₁ h₂ => spectralIntegral_add st h₁ h₂ u v,
    fun u v c φ h => spectralIntegral_smul st h c u v, fun φ h => ?_⟩
  have e : (fun u v : p.Hilb ν μ => p.spectralIntegral ν μ u v φ) =
      innerOpForm (E.spectralOp (φ ∘ (chart μ).symm)) := by
    funext u v
    exact spectralIntegral_eq_inner st h u v
  rw [e]
  exact innerOpForm_isSesquilinear _
theorem integralDiag (st : CalcSetup (p.opFamily ν μ) E) : IntegralDiag p ν μ := by
  intro u φ h
  rw [spectralIntegral_eq_inner st h,
    st.inner_spectralOp_self (isBddMeasurable_comp_chart_symm h), integral_spectralMeasure st]
  rfl
theorem integralBound (st : CalcSetup (p.opFamily ν μ) E) : IntegralBound p ν μ := by
  intro u v φ h C hC hnull
  have hσ := isSpectralMeasure_spectralMeasure st v
  have := hσ.1
  have hg := isBddMeasurable_comp_chart_symm h
  rw [spectralIntegral_eq_inner st h]
  set M := sSup ((fun x => ‖φ x‖) '' C) with hMdef
  have hM : 0 ≤ M := Real.sSup_nonneg (by
    rintro _ ⟨x, -, rfl⟩
    exact norm_nonneg _)
  obtain ⟨hm, B, hB⟩ := h
  have hbdd : BddAbove ((fun x => ‖φ x‖) '' C) := ⟨B, by
    rintro _ ⟨x, -, rfl⟩
    exact hB x⟩
  have hae : ∀ᵐ x ∂p.spectralMeasure ν μ v, ‖φ x‖ ^ 2 ≤ M ^ 2 := by
    have hmem : ∀ᵐ x ∂p.spectralMeasure ν μ v, x ∈ C := by
      rw [ae_iff]
      exact hnull v
    filter_upwards [hmem] with x hx
    exact pow_le_pow_left₀ (norm_nonneg _) (le_csSup hbdd ⟨x, hx, rfl⟩) 2
  have hint : Integrable (fun x => ‖φ x‖ ^ 2) (p.spectralMeasure ν μ v) := by
    refine Integrable.of_bound (hm.norm.pow_const 2).aestronglyMeasurable (B ^ 2)
      (ae_of_all _ fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ (norm_nonneg _) (hB x) 2
  have hn : ‖E.spectralOp (φ ∘ (chart μ).symm) v‖ ^ 2 ≤ (M * ‖v‖) ^ 2 := by
    rw [st.calculus.norm_spectralOp_sq _ hg v]
    have e : ∫ q, ‖(φ ∘ (chart μ).symm) q‖ ^ 2 ∂spectralMomentMeasure (p.opFamily ν μ) v =
        ∫ x, ‖φ x‖ ^ 2 ∂p.spectralMeasure ν μ v :=
      (integral_spectralMeasure st (fun x => ‖φ x‖ ^ 2) v).symm
    rw [e]
    have hle := integral_mono_ae hint (integrable_const (M ^ 2)) hae
    rw [integral_const, smul_eq_mul, measureReal_def, spectralMeasure_univ st v,
      ENNReal.toReal_ofReal (by positivity)] at hle
    rw [mul_pow]
    linarith
  have hn' : ‖E.spectralOp (φ ∘ (chart μ).symm) v‖ ≤ M * ‖v‖ :=
    (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp hn
  calc ‖inner ℂ u (E.spectralOp (φ ∘ (chart μ).symm) v)‖
      ≤ ‖u‖ * ‖E.spectralOp (φ ∘ (chart μ).symm) v‖ := norm_inner_le_norm _ _
    _ ≤ ‖u‖ * (M * ‖v‖) := mul_le_mul_of_nonneg_left hn' (norm_nonneg _)
    _ = M * ‖u‖ * ‖v‖ := by ring
theorem integralContinuity (st : CalcSetup (p.opFamily ν μ) E) : IntegralContinuity p ν μ := by
  intro u v φ f hφ hf hu
  refine Metric.tendsto_nhds.mpr fun ε hε => ?_
  have hK : 0 < ‖u‖ * ‖v‖ + 1 := by positivity
  have hδ : 0 < ε / (‖u‖ * ‖v‖ + 1) := div_pos hε hK
  filter_upwards [Metric.tendstoUniformly_iff.mp hu _ hδ] with k hk
  have hd : IsBoundedBorelFn (f k + (-1 : ℂ) • φ) := by
    obtain ⟨m₁, C₁, hC₁⟩ := hf k
    obtain ⟨m₂, C₂, hC₂⟩ := isBoundedBorelFn_smul hφ (-1 : ℂ)
    exact ⟨m₁.add m₂, C₁ + C₂, fun x => (norm_add_le _ _).trans (add_le_add (hC₁ x) (hC₂ x))⟩
  have e : p.spectralIntegral ν μ u v (f k) - p.spectralIntegral ν μ u v φ =
      p.spectralIntegral ν μ u v (f k + (-1 : ℂ) • φ) := by
    rw [spectralIntegral_add st (hf k) (isBoundedBorelFn_smul hφ _), spectralIntegral_smul st hφ]
    ring
  have hb := integralBound st u v _ hd univ MeasurableSet.univ (fun w => by simp)
  have hs : sSup ((fun x => ‖(f k + (-1 : ℂ) • φ) x‖) '' univ) ≤ ε / (‖u‖ * ‖v‖ + 1) := by
    refine Real.sSup_le ?_ hδ.le
    rintro _ ⟨x, -, rfl⟩
    have h₁ := hk x
    rw [dist_comm, dist_eq_norm] at h₁
    have e₂ : (f k + (-1 : ℂ) • φ) x = f k x - φ x := by
      simp [sub_eq_add_neg]
    simp only [e₂]
    exact h₁.le
  rw [dist_eq_norm, e]
  have hnn : 0 ≤ ‖u‖ * ‖v‖ := by positivity
  calc ‖p.spectralIntegral ν μ u v (f k + (-1 : ℂ) • φ)‖
      ≤ sSup ((fun x => ‖(f k + (-1 : ℂ) • φ) x‖) '' univ) * ‖u‖ * ‖v‖ := hb
    _ = sSup ((fun x => ‖(f k + (-1 : ℂ) • φ) x‖) '' univ) * (‖u‖ * ‖v‖) := by ring
    _ ≤ ε / (‖u‖ * ‖v‖ + 1) * (‖u‖ * ‖v‖) := mul_le_mul_of_nonneg_right hs hnn
    _ < ε := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ hK]
      nlinarith
theorem supportOnCone (st : CalcSetup (p.opFamily ν μ) E)
    (hY : ∀ l : TransverseAxis μ, p.transferOp ν μ * ((2 : ℂ) • 1 - p.shiftOp ν μ l -
      star (p.shiftOp ν μ l)) ≤ (1 - p.transferOp ν μ) ^ 2) :
    SupportOnCone p ν μ := by
  intro u
  rw [spectralMeasure_eq_map st, MeasurableEquiv.map_apply]
  refine measure_mono_null (t := ⋃ l, {q | coneDefect l q < 0}) ?_
    (measure_iUnion_null fun l => st.moment_negPart_null l (hY l) u)
  intro q hq
  have hq' : (chart μ).symm q ∉ coneInSpectral μ := hq
  rw [mem_cone_iff] at hq'
  push Not at hq'
  obtain ⟨l, hl⟩ := hq'
  rw [Equiv.apply_symm_apply] at hl
  exact mem_iUnion.mpr ⟨l, hl⟩
theorem momentIdentity (st : CalcSetup (p.opFamily ν μ) E) : MomentIdentity p ν μ := by
  intro u v n w
  rw [spectralIntegral_eq_inner st (emMonomial_isBoundedBorelFn n w), emMonomial_comp_symm,
    st.calculus.spectralOp_monomial]
  rfl
theorem translationInvariance (st : CalcSetup (p.opFamily ν μ) E) :
    TranslationInvariance p ν μ := by
  intro u w
  have hσ := isSpectralMeasure_spectralMeasure st u
  have hh : p.IsSpectralMeasure ν μ (p.shiftMonomial ν μ (w : Fin 4 → ℤ) u)
      (p.spectralMeasure ν μ u) := by
    refine ⟨hσ.1, fun n w' => ?_⟩
    rw [← hσ.2 n w']
    exact st.inner_unitaryMonomial_moment n _ _ u
  rw [spectralMeasure_eq_map st, ← eq_map_of_isSpectralMeasure st hh]
end OnePair
theorem spectralMeasuresTheorem_holds (hcalc : JointSpectralCalculusTheorem)
    (hscalar : ScalarSpectralMeasures.ScalarSpectralMeasuresStatement)
    (hlink : OneStepEnergyMomentumLink)
    (hsite : SiteReflectionPair.Conclusion) :
    SpectralMeasuresTheorem := by
  intro μ
  refine ⟨spectralSpaceProps μ, monomialDensity hscalar μ, fun ν p => ?_⟩
  obtain ⟨h₁, ⟨E, hE, -⟩, h₃⟩ := hcalc (p.Hilb ν μ) (TransverseAxis μ) (p.opFamily ν μ)
  obtain ⟨a, b, -, d, -⟩ := h₃ E hE
  have st : CalcSetup (p.opFamily ν μ) E :=
    ⟨fun u => (h₁ u).2, fun u m hm => (h₁ u).1.unique hm (h₁ u).2, hE, a, b, d⟩
  have hY : ∀ l : TransverseAxis μ, p.transferOp ν μ * ((2 : ℂ) • 1 - p.shiftOp ν μ l -
      star (p.shiftOp ν μ l)) ≤ (1 - p.transferOp ν μ) ^ 2 := by
    intro l
    cases p with
    | link => exact (hlink ν μ l).2.2
    | site =>
      have h := ((hsite ν μ 1).2.2.1 l 1 le_rfl).1
      simpa only [pow_one, ge_iff_le] using h
  exact ⟨fun b' hb' => ⟨sesq_polarization hb', sesq_conjSymm_of_im_diag hb'⟩,
    uniqueSpectralMeasure st, integralLinear st, integralDiag st, integralBound st,
    integralContinuity st, supportOnCone st hY, momentIdentity st, translationInvariance st⟩
end YangMills.Construction.ReflectionPositivity.DirectionPictures.SpectralMeasures.Derivation
