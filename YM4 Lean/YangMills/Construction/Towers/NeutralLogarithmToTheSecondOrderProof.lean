import YangMills.Construction.Towers.FirstCoefficientOnTheGaugeColumnProof
import YangMills.Construction.Towers.PowersOfTheMassivePropagatorProof
import YangMills.Construction.Towers.ChargedSymbolAtFluxZeroProof
import YangMills.Construction.Towers.NeutralLogarithmToTheSecondOrder
import YangMills.Construction.Towers.QuantizationIsTheSumOfItsSeries
import YangMills.Construction.Towers.RelationsOfTheWeylOperators
import YangMills.Construction.Towers.SecondOrderInTheFluxProof
import YangMills.Construction.Towers.SumsAndProductsOfSymbols
import YangMills.Construction.Towers.SymbolsOfTheParametrix
import YangMills.Construction.Towers.TracesOfTheParametrixOverTheHalfLineProof
import Mathlib
set_option autoImplicit false
open Filter Set MeasureTheory YangMills.Construction.OperatorCalculus YangMills.Construction.Tower.UnitLatticeL2 YangMills.Construction.Tower.UnitaryCombinations YangMills.Construction.OneLoopNotation
open YangMills.Construction.PeriodicOperators (torusAverage toComplexVec castVec bilinDot)
open YangMills.Construction.InfiniteLattice (AmbientSpace)
open scoped Matrix ComplexConjugate
noncomputable section
namespace YangMills.Construction.Tower.ConstantFieldSymbols
open YangMills.Construction.Tower.MagneticWeyl YangMills.Construction.Tower.MagneticWeyl.FluxSecondOrder YangMills.Construction.Tower.Massive
namespace NeutralSector
abbrev torusBox : Set AmbientSpace := Icc (fun _ : Fin 4 => -Real.pi) (fun _ => Real.pi)
theorem torusAverage_add {g h : AmbientSpace → ℂ} (hg : Continuous g) (hh : Continuous h) :
    (torusAverage fun q => g q + h q) = torusAverage g + torusAverage h := by apply _root_.YangMills.SharedProofs.p18494 <;> assumption
theorem torusAverage_sub {g h : AmbientSpace → ℂ} (hg : Continuous g) (hh : Continuous h) :
    (torusAverage fun q => g q - h q) = torusAverage g - torusAverage h := by apply _root_.YangMills.Construction.Tower.MagneticWeyl.HalfLineTrace.average_sub <;> assumption
theorem torusAverage_const_mul (c : ℂ) (g : AmbientSpace → ℂ) :
    (torusAverage fun q => c * g q) = c * torusAverage g := by apply _root_.YangMills.Construction.PeriodicOperators.KernelSymbol.torusAverage_const_mul <;> assumption
theorem torusAverage_const (c : ℂ) : (torusAverage fun _ => c) = c := by apply _root_.YangMills.Construction.Tower.MagneticWeyl.HalfLineTrace.average_const <;> assumption
theorem norm_torusAverage_le {g : AmbientSpace → ℂ} {C : ℝ} (hC : ∀ q ∈ torusBox, ‖g q‖ ≤ C) :
    ‖torusAverage g‖ ≤ C := by apply _root_.YangMills.Construction.Tower.MagneticWeyl.HalfLineTrace.norm_average_le <;> assumption
theorem continuous_torusAverage {g : ℝ → AmbientSpace → ℂ} (hg : Continuous (Function.uncurry g)) :
    Continuous fun w => torusAverage (g w) := by apply _root_.YangMills.Construction.Tower.MagneticWeyl.HalfLineTrace.continuous_average <;> assumption
theorem intervalIntegral_torusAverage_comm {g : ℝ → AmbientSpace → ℂ}
    (hg : Continuous (Function.uncurry g)) {y : ℝ} (hy : 0 ≤ y) :
    (∫ w in (0 : ℝ)..y, torusAverage (g w)) = torusAverage fun q => ∫ w in (0 : ℝ)..y, g w q := by apply _root_.YangMills.Construction.Tower.MagneticWeyl.HalfLineTrace.intervalIntegral_average_comm <;> assumption
def resolventGap (u : AmbientSpace → ℝ) (w : ℝ) (q : AmbientSpace) : ℂ :=
  (((1 + |w|)⁻¹ - (u q + |w|)⁻¹ : ℝ) : ℂ)
theorem continuous_uncurry_resolventGap {u : AmbientSpace → ℝ} (hu : Continuous u)
    (hpos : ∀ q, 0 < u q) : Continuous (Function.uncurry (resolventGap u)) := by
  have h1 : Continuous fun p : ℝ × AmbientSpace => (1 + |p.1|)⁻¹ :=
    Continuous.inv₀ (by fun_prop) fun p => by positivity
  have h2 : Continuous fun p : ℝ × AmbientSpace => (u p.2 + |p.1|)⁻¹ :=
    Continuous.inv₀ (by fun_prop) fun p => by
      have := hpos p.2
      positivity
  exact Complex.continuous_ofReal.comp (h1.sub h2)
theorem integral_inv_sub_inv {a y : ℝ} (ha : 0 < a) (hy : 0 ≤ y) :
    ∫ w in (0 : ℝ)..y, ((1 + |w|)⁻¹ - (a + |w|)⁻¹) =
      Real.log (1 + y) - Real.log (a + y) + Real.log a := by
  have hcongr : ∫ w in (0 : ℝ)..y, ((1 + |w|)⁻¹ - (a + |w|)⁻¹) =
      ∫ w in (0 : ℝ)..y, ((1 + w)⁻¹ - (a + w)⁻¹) := by
    refine intervalIntegral.integral_congr fun w hw => ?_
    rw [uIcc_of_le hy] at hw
    simp only [abs_of_nonneg hw.1]
  have hd : ∀ w ∈ uIcc (0 : ℝ) y, HasDerivAt (fun w => Real.log (1 + w) - Real.log (a + w))
      ((1 + w)⁻¹ - (a + w)⁻¹) w := by
    intro w hw
    rw [uIcc_of_le hy] at hw
    have h1 : 1 + w ≠ 0 := by have := hw.1; positivity
    have h2 : a + w ≠ 0 := by have := hw.1; positivity
    have h : HasDerivAt (fun w => Real.log (1 + w) - Real.log (a + w))
        (1 / (1 + w) - 1 / (a + w)) w :=
      (((hasDerivAt_id w).const_add 1).log h1).sub (((hasDerivAt_id w).const_add a).log h2)
    simpa [one_div] using h
  have hc : ContinuousOn (fun w : ℝ => (1 + w)⁻¹ - (a + w)⁻¹) (uIcc 0 y) := by
    rw [uIcc_of_le hy]
    refine ContinuousOn.sub (ContinuousOn.inv₀ (by fun_prop) fun w hw => ?_)
      (ContinuousOn.inv₀ (by fun_prop) fun w hw => ?_)
    · have := hw.1; positivity
    · have := hw.1; positivity
  rw [hcongr, intervalIntegral.integral_eq_sub_of_hasDerivAt hd hc.intervalIntegrable]
  simp only [add_zero, Real.log_one]
  ring
theorem abs_log_sub_log_le {a b y C : ℝ} (hy : 0 < y) (ha : y ≤ a) (hb : y ≤ b) (hC : |a - b| ≤ C) :
    |Real.log a - Real.log b| ≤ C / y := by
  have hC0 : 0 ≤ C := (abs_nonneg _).trans hC
  have key : ∀ {s t : ℝ}, y ≤ s → y ≤ t → |s - t| ≤ C → Real.log s - Real.log t ≤ C / y := by
    intro s t hs ht hst
    have hs0 : 0 < s := by linarith
    have ht0 : 0 < t := by linarith
    rw [← Real.log_div hs0.ne' ht0.ne']
    have h := Real.log_le_sub_one_of_pos (div_pos hs0 ht0)
    have h2 : s / t - 1 = (s - t) / t := by field_simp
    have h3 : (s - t) / t ≤ C / y := by
      have h4 : s - t ≤ C := (le_abs_self _).trans hst
      calc (s - t) / t ≤ C / t := by gcongr
        _ ≤ C / y := by gcongr
    linarith
  rw [abs_le]
  constructor
  · have := key hb ha (by rwa [abs_sub_comm])
    linarith
  · exact key ha hb hC
theorem tendsto_integral_resolventGap {u : AmbientSpace → ℝ} (hu : Continuous u) {z M : ℝ}
    (hz : 0 < z) (hlo : ∀ q, z ≤ u q) (hhi : ∀ q, u q ≤ M) :
    Tendsto (fun y : ℝ => ∫ w in (0 : ℝ)..y, torusAverage (resolventGap u w)) atTop
      (nhds (torusAverage fun q => ((Real.log (u q) : ℝ) : ℂ))) := by
  have hpos : ∀ q, 0 < u q := fun q => hz.trans_le (hlo q)
  have hlog : Continuous fun q => ((Real.log (u q) : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (hu.log fun q => (hpos q).ne')
  have hrest : ∀ y : ℝ, 0 ≤ y → Continuous fun q =>
      ((Real.log (1 + y) - Real.log (u q + y) : ℝ) : ℂ) := fun y hy =>
    Complex.continuous_ofReal.comp (continuous_const.sub ((hu.add continuous_const).log fun q =>
      (add_pos_of_pos_of_nonneg (hpos q) hy).ne'))
  have hsplit : ∀ y : ℝ, 0 ≤ y → (∫ w in (0 : ℝ)..y, torusAverage (resolventGap u w)) =
      (torusAverage fun q => ((Real.log (u q) : ℝ) : ℂ)) +
        torusAverage fun q => ((Real.log (1 + y) - Real.log (u q + y) : ℝ) : ℂ) := by
    intro y hy
    rw [intervalIntegral_torusAverage_comm (continuous_uncurry_resolventGap hu hpos) hy,
      ← torusAverage_add hlog (hrest y hy)]
    congr 1
    funext q
    simp only [resolventGap]
    rw [intervalIntegral.integral_ofReal, integral_inv_sub_inv (hpos q) hy]
    push_cast
    ring
  have hM : 0 < M := (hpos 0).trans_le (hhi 0)
  have hzero : Tendsto (fun y : ℝ =>
      torusAverage fun q => ((Real.log (1 + y) - Real.log (u q + y) : ℝ) : ℂ)) atTop (nhds 0) := by
    have hb : Tendsto (fun y : ℝ => (1 + M) / y) atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    refine squeeze_zero_norm' ?_ hb
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with y hy
    refine norm_torusAverage_le fun q _ => ?_
    rw [Complex.norm_real, Real.norm_eq_abs]
    refine abs_log_sub_log_le hy (by linarith) (by linarith [hpos q]) ?_
    have h1 := hpos q
    have h2 := hhi q
    rw [abs_le]
    constructor <;> linarith
  have h := (tendsto_const_nhds (x := torusAverage fun q => ((Real.log (u q) : ℝ) : ℂ))).add hzero
  rw [add_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with y hy
  exact (hsplit y hy).symm
def psiR (q : AmbientSpace) : ℝ := ∑ μ, (2 - 2 * Real.cos (q μ))
def rhoR (q : AmbientSpace) : ℝ := (2 - 2 * Real.cos (q 0)) + (2 - 2 * Real.cos (q 1))
theorem latticeSymbol_eq_psiR (q : AmbientSpace) : latticeSymbol (toComplexVec q) = (psiR q : ℂ) := by
  simp [latticeSymbol, psiR, axisSymbol, toComplexVec]
theorem axisSymbol_add_eq_rhoR (q : AmbientSpace) :
    axisSymbol 0 (toComplexVec q) + axisSymbol 1 (toComplexVec q) = (rhoR q : ℂ) := by
  simp [rhoR, axisSymbol, toComplexVec]
theorem continuous_psiR : Continuous psiR := by
  unfold psiR
  fun_prop
theorem continuous_rhoR : Continuous rhoR := by
  unfold rhoR
  fun_prop
theorem rhoR_nonneg (q : AmbientSpace) : 0 ≤ rhoR q := by
  unfold rhoR
  linarith [Real.cos_le_one (q 0), Real.cos_le_one (q 1)]
theorem rhoR_le_psiR (q : AmbientSpace) : rhoR q ≤ psiR q := by
  simp only [rhoR, psiR, Fin.sum_univ_four]
  linarith [Real.cos_le_one (q 2), Real.cos_le_one (q 3)]
theorem psiR_le_sixteen (q : AmbientSpace) : psiR q ≤ 16 := by
  simp only [psiR, Fin.sum_univ_four]
  linarith [Real.neg_one_le_cos (q 0), Real.neg_one_le_cos (q 1), Real.neg_one_le_cos (q 2),
    Real.neg_one_le_cos (q 3)]
theorem abs_log_quadratic_remainder_le {ψ ρ z f : ℝ} (hρ : 0 ≤ ρ) (hρψ : ρ ≤ ψ) (hz : 0 < z)
    (hf : |f| ≤ 1) :
    |Real.log (ψ + z + (Real.cos f - 1) * ρ) - Real.log (ψ + z) + f ^ 2 / 2 * (ρ / (ψ + z))| ≤
      f ^ 4 := by
  set u := ψ + z with hu
  have hu0 : 0 < u := by linarith
  set x := ρ / u with hx
  have hx0 : 0 ≤ x := by positivity
  have hx1 : x ≤ 1 := by
    rw [hx, div_le_one hu0]
    linarith
  set c := Real.cos f - 1 with hc
  have hc0 : c ≤ 0 := by linarith [Real.cos_le_one f]
  have hc1 : -(f ^ 2 / 2) ≤ c := by linarith [Real.one_sub_sq_div_two_le_cos (x := f)]
  have hf2 : f ^ 2 ≤ 1 := by
    rw [← sq_abs]
    exact pow_le_one₀ (abs_nonneg f) hf
  set χ := c * x with hχ
  have hχabs : |χ| ≤ f ^ 2 / 2 := by
    rw [abs_le]
    constructor <;> nlinarith
  have hχ2 : |χ| ≤ 1 / 2 := by linarith
  have hlog : Real.log (u + c * ρ) - Real.log u = Real.log (1 + χ) := by
    have h1 : u + c * ρ = u * (1 + χ) := by
      rw [hχ, hx]
      field_simp
    have h2 : 0 < 1 + χ := by
      have := (abs_le.mp hχ2).1
      linarith
    rw [h1, Real.log_mul hu0.ne' h2.ne']
    ring
  have hL : |Real.log (1 + χ) - χ| ≤ 2 * χ ^ 2 := by
    have h := Real.abs_log_sub_add_sum_range_le (x := -χ) (by rw [abs_neg]; linarith) 1
    simp only [Finset.range_one, Finset.sum_singleton, zero_add, pow_one, Nat.cast_zero, div_one,
      sub_neg_eq_add, abs_neg] at h
    have h' : |Real.log (1 + χ) - χ| = |-χ + Real.log (1 + χ)| := by
      congr 1
      ring
    rw [h']
    refine h.trans ?_
    rw [div_le_iff₀ (by linarith)]
    have : |χ| ^ 2 = χ ^ 2 := sq_abs χ
    norm_num at this ⊢
    nlinarith [sq_nonneg χ]
  have hχsq : 2 * χ ^ 2 ≤ f ^ 4 / 2 := by
    have h1 : χ ^ 2 ≤ (f ^ 2 / 2) ^ 2 := by
      rw [← sq_abs χ]
      exact pow_le_pow_left₀ (abs_nonneg χ) hχabs 2
    nlinarith
  have hcos : |c + f ^ 2 / 2| ≤ f ^ 4 * (5 / 96) := by
    have h := Real.cos_bound hf
    have h' : Real.cos f - (1 - f ^ 2 / 2) = c + f ^ 2 / 2 := by
      rw [hc]
      ring
    rw [h'] at h
    have h4 : |f| ^ 4 = f ^ 4 := by
      rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, sq_abs, ← pow_mul]
    rwa [h4] at h
  have hsplit : Real.log (u + c * ρ) - Real.log u + f ^ 2 / 2 * x =
      (Real.log (1 + χ) - χ) + (c + f ^ 2 / 2) * x := by
    rw [hlog, hχ]
    ring
  rw [hsplit]
  have hf4 : 0 ≤ f ^ 4 := by positivity
  have h2 : |(c + f ^ 2 / 2) * x| ≤ f ^ 4 * (5 / 96) := by
    rw [abs_mul, abs_of_nonneg hx0]
    calc |c + f ^ 2 / 2| * x ≤ |c + f ^ 2 / 2| * 1 := by gcongr
      _ ≤ f ^ 4 * (5 / 96) := by simpa using hcos
  calc _ ≤ |Real.log (1 + χ) - χ| + |(c + f ^ 2 / 2) * x| := abs_add_le _ _
    _ ≤ f ^ 4 := by linarith
theorem one_sub_exp_mul_conj_self (t : ℝ) :
    (1 - Complex.exp (Complex.I * (t : ℂ))) * conj (1 - Complex.exp (Complex.I * (t : ℂ))) =
      ((2 - 2 * Real.cos t : ℝ) : ℂ) := by
  rw [Complex.mul_conj, mul_comm Complex.I, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im,
    Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
  congr 1
  nlinarith [Real.sin_sq_add_cos_sq t]
theorem faceRow_mul_conjTranspose (q : AmbientSpace) :
    faceRow q * (faceRow q)ᴴ = (rhoR q : ℂ) • (1 : Matrix (Fin 1) (Fin 1) ℂ) := by
  ext i j
  have hi : i = 0 := Subsingleton.elim _ _
  have hj : j = 0 := Subsingleton.elim _ _
  subst hi hj
  have h1 := one_sub_exp_mul_conj_self (q 1)
  have h0 := one_sub_exp_mul_conj_self (q 0)
  have h0' : (Complex.exp (Complex.I * (q 0 : ℂ)) - 1) *
      conj (Complex.exp (Complex.I * (q 0 : ℂ)) - 1) = ((2 - 2 * Real.cos (q 0) : ℝ) : ℂ) := by
    rw [← h0, ← neg_sub (1 : ℂ), map_neg, neg_mul_neg]
  simp only [Matrix.mul_apply, Fin.sum_univ_four, faceRow, Matrix.conjTranspose_apply,
    Matrix.of_apply, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one, rhoR]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, star_zero, mul_zero,
    add_zero, RCLike.star_def]
  rw [h1, h0']
  push_cast
  ring
theorem faceGram_mul_self (q : AmbientSpace) :
    faceGram q * faceGram q = (rhoR q : ℂ) • faceGram q := by
  unfold faceGram
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc (faceRow q), faceRow_mul_conjTranspose, Matrix.smul_mul,
    Matrix.one_mul, Matrix.mul_smul]
theorem diagSum_faceGram (q : AmbientSpace) :
    Matrices.RectangularMatrix.diagSum (faceGram q) = (rhoR q : ℂ) := by
  change Matrix.trace (faceGram q) = _
  unfold faceGram
  rw [Matrix.trace_mul_comm, faceRow_mul_conjTranspose]
  simp
theorem diagSum_one_four :
    Matrices.RectangularMatrix.diagSum (1 : Matrix (Fin 4) (Fin 4) ℂ) = 4 := by
  change Matrix.trace (1 : Matrix (Fin 4) (Fin 4) ℂ) = _
  simp
theorem diagSum_smul_four (c : ℂ) (X : Matrix (Fin 4) (Fin 4) ℂ) :
    Matrices.RectangularMatrix.diagSum (c • X) = c * Matrices.RectangularMatrix.diagSum X := by
  change Matrix.trace (c • X) = c * Matrix.trace X
  simp
theorem diagSum_sub_four (X Y : Matrix (Fin 4) (Fin 4) ℂ) :
    Matrices.RectangularMatrix.diagSum (X - Y) =
      Matrices.RectangularMatrix.diagSum X - Matrices.RectangularMatrix.diagSum Y := by
  change Matrix.trace (X - Y) = Matrix.trace X - Matrix.trace Y
  simp
def denomU (s : ℝ) (q : AmbientSpace) : ℝ := psiR q + s
def denomV (f s : ℝ) (q : AmbientSpace) : ℝ := psiR q + s + (Real.cos f - 1) * rhoR q
def neutralInv (f s : ℝ) (q : AmbientSpace) : Matrix (Fin 4) (Fin 4) ℂ :=
  ((denomU s q)⁻¹ : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) -
    ((((Real.cos f - 1) * (denomU s q)⁻¹ * (denomV f s q)⁻¹ : ℝ)) : ℂ) • faceGram q
theorem neutralSectorSymbol_add_smul_one (f s : ℝ) (q : AmbientSpace) :
    neutralSectorSymbol f q + (s : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) =
      (denomU s q : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) +
        ((Real.cos f - 1 : ℝ) : ℂ) • faceGram q := by
  simp only [neutralSectorSymbol, denomU, latticeSymbol_eq_psiR]
  push_cast
  module
theorem neutralSectorSymbol_mul_neutralInv (f s : ℝ) (q : AmbientSpace) (hu : denomU s q ≠ 0)
    (hv : denomV f s q ≠ 0) :
    (neutralSectorSymbol f q + (s : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ)) * neutralInv f s q = 1 := by
  rw [neutralSectorSymbol_add_smul_one, neutralInv]
  set u := denomU s q with hdu
  set v := denomV f s q with hdv
  set c := Real.cos f - 1 with hc
  set ρ := rhoR q with hρ
  have hvu : v = u + c * ρ := rfl
  have h1 : (u : ℂ) * (u⁻¹ : ℂ) = 1 := by
    have : (u : ℂ) ≠ 0 := by exact_mod_cast hu
    field_simp
  have h2 : (c : ℂ) * (u⁻¹ : ℂ) - (u : ℂ) * ((c * u⁻¹ * v⁻¹ : ℝ) : ℂ) -
      (c : ℂ) * ((c * u⁻¹ * v⁻¹ : ℝ) : ℂ) * (ρ : ℂ) = 0 := by
    have : c * u⁻¹ - u * (c * u⁻¹ * v⁻¹) - c * (c * u⁻¹ * v⁻¹) * ρ = 0 := by
      field_simp
      rw [hvu]
      ring
    exact_mod_cast this
  have hF := faceGram_mul_self q
  calc ((u : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) + (c : ℂ) • faceGram q) *
        ((u⁻¹ : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) - ((c * u⁻¹ * v⁻¹ : ℝ) : ℂ) • faceGram q)
      = ((u : ℂ) * (u⁻¹ : ℂ)) • (1 : Matrix (Fin 4) (Fin 4) ℂ) +
          ((c : ℂ) * (u⁻¹ : ℂ) - (u : ℂ) * ((c * u⁻¹ * v⁻¹ : ℝ) : ℂ)) • faceGram q -
          ((c : ℂ) * ((c * u⁻¹ * v⁻¹ : ℝ) : ℂ)) • (faceGram q * faceGram q) := by
        simp only [add_mul, mul_sub, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one,
          smul_smul]
        module
    _ = ((u : ℂ) * (u⁻¹ : ℂ)) • (1 : Matrix (Fin 4) (Fin 4) ℂ) +
          ((c : ℂ) * (u⁻¹ : ℂ) - (u : ℂ) * ((c * u⁻¹ * v⁻¹ : ℝ) : ℂ) -
            (c : ℂ) * ((c * u⁻¹ * v⁻¹ : ℝ) : ℂ) * (ρ : ℂ)) • faceGram q := by
        rw [hF, smul_smul]
        module
    _ = 1 := by rw [h1, h2, one_smul, zero_smul, add_zero]
theorem diagSum_neutralInv (f s : ℝ) (q : AmbientSpace) (hu : denomU s q ≠ 0)
    (hv : denomV f s q ≠ 0) :
    Matrices.RectangularMatrix.diagSum (neutralInv f s q) =
      3 * (((denomU s q)⁻¹ : ℝ) : ℂ) + (((denomV f s q)⁻¹ : ℝ) : ℂ) := by
  rw [neutralInv, diagSum_sub_four, diagSum_smul_four, diagSum_smul_four, diagSum_one_four,
    diagSum_faceGram]
  set u := denomU s q with hdu
  set v := denomV f s q with hdv
  have hvu : v = u + (Real.cos f - 1) * rhoR q := rfl
  have : u⁻¹ * 4 - (Real.cos f - 1) * u⁻¹ * v⁻¹ * rhoR q = 3 * u⁻¹ + v⁻¹ := by
    field_simp
    rw [hvu]
    ring
  exact_mod_cast this
theorem pointwiseAdjoint_neutralSectorSymbol (f : ℝ) (q : AmbientSpace) :
    pointwiseAdjoint (neutralSectorSymbol f) q = neutralSectorSymbol f q := by
  have hF : (faceGram q)ᴴ = faceGram q := by
    unfold faceGram
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  have hr : ∀ x : ℝ, star (x : ℂ) = x := fun x => Complex.conj_ofReal x
  simp only [pointwiseAdjoint, neutralSectorSymbol, latticeSymbol_eq_psiR, Matrix.conjTranspose_add,
    Matrix.conjTranspose_smul, Matrix.conjTranspose_one, hF]
  rw [hr, hr]
theorem fourierChar_add (n m : Fin 4 → ℤ) (q : AmbientSpace) :
    fourierChar (n + m) q = fourierChar n q * fourierChar m q := by apply _root_.YangMills.Construction.Tower.ConstantFieldSymbols.FluxZero.fourierChar_add <;> assumption
theorem conj_fourierChar (n : Fin 4 → ℤ) (q : AmbientSpace) :
    conj (fourierChar n q) = fourierChar (-n) q := by apply _root_.YangMills.Construction.Tower.ConstantFieldSymbols.FluxZero.conj_fourierChar <;> assumption
theorem fourierChar_zero (q : AmbientSpace) : fourierChar 0 q = 1 := by apply _root_.YangMills.Construction.Tower.ConstantFieldSymbols.FluxZero.fourierChar_zero <;> assumption
theorem fourierChar_single (μ : Fin 4) (q : AmbientSpace) :
    fourierChar (Pi.single μ 1) q = Complex.exp (Complex.I * (q μ : ℂ)) := by apply _root_.YangMills.Construction.Tower.ConstantFieldSymbols.GaugeColumnFirstCoeff.fourierChar_basisIndex <;> assumption
def rowFreq : Fin 3 → Fin 4 → ℤ := ![0, Pi.single 1 1, Pi.single 0 1]
def rowCoeff : Fin 3 → Matrix (Fin 1) (Fin 4) ℂ :=
  ![Matrix.of fun _ => ![1, -1, 0, 0], Matrix.of fun _ => ![-1, 0, 0, 0],
    Matrix.of fun _ => ![0, 1, 0, 0]]
theorem faceRow_eq_sum (q : AmbientSpace) :
    faceRow q = ∑ i, fourierChar (rowFreq i) q • rowCoeff i := by
  ext i j
  simp only [Fin.sum_univ_three, rowFreq, rowCoeff, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val, fourierChar_zero, fourierChar_single, Matrix.add_apply, Matrix.smul_apply,
    Matrix.of_apply, faceRow, smul_eq_mul]
  fin_cases j <;> simp <;> ring
theorem faceGram_eq_sum (q : AmbientSpace) :
    faceGram q = ∑ i, ∑ j, fourierChar (-rowFreq i + rowFreq j) q •
      ((rowCoeff i)ᴴ * rowCoeff j) := by
  unfold faceGram
  rw [faceRow_eq_sum, Matrix.conjTranspose_sum, Matrix.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, fourierChar_add,
    ← conj_fourierChar]
  rfl
section FiniteFourier
variable (hSum : MagneticWeyl.SymbolAlgebra.Claim)
include hSum
theorem isFiniteFourier_add {a b : AmbientSpace → Matrix (Fin 4) (Fin 4) ℂ}
    (ha : IsFiniteFourierSymbol a) (hb : IsFiniteFourierSymbol b) :
    IsFiniteFourierSymbol fun q => a q + b q := by
  obtain ⟨h1, h2, -⟩ := (hSum 4 4 4).2.1.1 a b ha.1 hb.1
  refine ⟨h1, (ha.2.union hb.2).subset fun n hn => ?_⟩
  by_contra hc
  simp only [mem_union, mem_ofPred_eq, not_or, not_not] at hc
  exact hn (by rw [h2, hc.1, hc.2, add_zero])
theorem isFiniteFourier_smul (c : ℂ) {a : AmbientSpace → Matrix (Fin 4) (Fin 4) ℂ}
    (ha : IsFiniteFourierSymbol a) : IsFiniteFourierSymbol fun q => c • a q := by
  obtain ⟨h1, h2, -⟩ := (hSum 4 4 4).2.1.2.1 c a ha.1
  refine ⟨h1, ha.2.subset fun n hn => ?_⟩
  by_contra hc
  simp only [mem_ofPred_eq, not_not] at hc
  exact hn (by rw [h2, hc, smul_zero])
theorem isFiniteFourier_const (C : Matrix (Fin 4) (Fin 4) ℂ) :
    IsFiniteFourierSymbol fun _ : AmbientSpace => C := by
  obtain ⟨h1, -, h3, -⟩ := (hSum 4 4 4).2.1.2.2.1 C
  refine ⟨h1, (finite_singleton (0 : Fin 4 → ℤ)).subset fun n hn => ?_⟩
  by_contra hc
  exact hn (h3 n hc)
theorem isFiniteFourier_sum {ι : Type} (S : Finset ι) {a : ι → AmbientSpace → Matrix (Fin 4) (Fin 4) ℂ}
    (ha : ∀ i ∈ S, IsFiniteFourierSymbol (a i)) :
    IsFiniteFourierSymbol fun q => ∑ i ∈ S, a i q := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using isFiniteFourier_const hSum 0
  | insert i S hi ih =>
    simp only [Finset.sum_insert hi]
    exact isFiniteFourier_add hSum (ha i (Finset.mem_insert_self i S))
      (ih fun j hj => ha j (Finset.mem_insert_of_mem hj))
end FiniteFourier
theorem isFiniteFourier_neutralSectorSymbol_add (hSum : MagneticWeyl.SymbolAlgebra.Claim)
    (hCalc : MagneticWeyl.FluxZeroCalculus.Claim)
    (hPsi : MagneticWeyl.ApproxInverseSymbolBounds) (f : ℝ) (C : Matrix (Fin 4) (Fin 4) ℂ) :
    IsFiniteFourierSymbol fun q => neutralSectorSymbol f q + C := by
  have hterm : ∀ (n : Fin 4 → ℤ) (T : Matrix (Fin 4) (Fin 4) ℂ),
      IsFiniteFourierSymbol fun q => fourierChar n q • T := by
    intro n T
    have h := ((hCalc 0 4 4 4).2.2.2.2.1 {n} fun _ => T).1
    simpa using h
  have hflux : IsFiniteFourierSymbol faceGram := by
    have h : IsFiniteFourierSymbol fun q => ∑ i, ∑ j, fourierChar (-rowFreq i + rowFreq j) q •
        ((rowCoeff i)ᴴ * rowCoeff j) :=
      isFiniteFourier_sum hSum _ fun i _ => isFiniteFourier_sum hSum _ fun j _ => hterm _ _
    rwa [show (fun q => ∑ i, ∑ j, fourierChar (-rowFreq i + rowFreq j) q •
      ((rowCoeff i)ᴴ * rowCoeff j)) = faceGram from (funext faceGram_eq_sum).symm] at h
  have hpsi : IsFiniteFourierSymbol (FluxExpansion.baseSymbolMatrix 4) := (hPsi 4).1
  exact isFiniteFourier_add hSum (isFiniteFourier_add hSum hpsi (isFiniteFourier_smul hSum _ hflux))
    (isFiniteFourier_const hSum C)
section Positivity
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
theorem isBoundedBelowBy_half_of_isUnit (A : BddOp H) (hA : IsSelfAdjointOp A)
    (hU : ∀ t : ℝ, 0 < t → IsUnit (A + scalarOp (t : ℂ))) {z : ℝ} (hz : 0 < z) :
    IsBoundedBelowBy (addScalar A z) (z / 2) := by
  have hsa : IsSelfAdjoint A := ContinuousLinearMap.isSelfAdjoint_iff'.mpr hA
  have hnn : (0 : BddOp H) ≤ A := by
    rw [StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) A hsa]
    intro x hx
    by_contra hneg
    have hx0 : 0 < -x := by linarith [not_le.mp hneg]
    refine (spectrum.mem_iff.mp hx) ?_
    have e : algebraMap ℝ (BddOp H) x - A =
        -(A + scalarOp ((-x : ℝ) : ℂ)) := by
      refine ContinuousLinearMap.ext fun v => ?_
      simp [scalarOp, Algebra.algebraMap_eq_smul_one, Complex.coe_smul]
      abel
    rw [e]
    exact (hU _ hx0).neg
  have hp : A.IsPositive := (ContinuousLinearMap.nonneg_iff_isPositive A).1 hnn
  intro ψ
  have h1 : 0 ≤ (inner ℂ ψ (A ψ)).re := hp.re_inner_nonneg_right ψ
  have h2 : (inner ℂ ψ (A ψ)).im = 0 := by
    have h3 : inner ℂ (A ψ) ψ = inner ℂ ψ (A ψ) := by
      have := ContinuousLinearMap.adjoint_inner_left A ψ ψ
      rw [show ContinuousLinearMap.adjoint A = A from hA] at this
      exact this
    have h4 := inner_conj_symm (𝕜 := ℂ) (A ψ) ψ
    rw [h3] at h4
    exact Complex.conj_eq_iff_im.mp h4
  have hself : inner ℂ ψ ψ = ((‖ψ‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]
    norm_cast
  have hexp : inner ℂ ψ (addScalar A z ψ) - ((z / 2 : ℝ) : ℂ) * inner ℂ ψ ψ =
      inner ℂ ψ (A ψ) + ((z / 2 * ‖ψ‖ ^ 2 : ℝ) : ℂ) := by
    simp only [addScalar, scalarOp, add_apply,
      smul_apply, ContinuousLinearMap.id_apply, inner_add_right,
      inner_smul_right, hself]
    push_cast
    ring
  rw [hexp]
  have hn : 0 ≤ z / 2 * ‖ψ‖ ^ 2 := by positivity
  constructor
  · rw [Complex.add_im, Complex.ofReal_im, h2, add_zero]
  · simp only [Complex.add_re, Complex.ofReal_re]
    linarith
end Positivity
theorem matMulUnitaryOp_add {L : ℕ}
    (hSeries : UnitaryOperatorSeriesClaim)
    (X Y : Matrix (Fin 4) (Fin 4) ℂ) {V : ScalarL2 L →ₗ[ℂ] ScalarL2 L}
    (hV : IsUnitaryOp V) :
    matMulUnitaryOp (X + Y) V = matMulUnitaryOp X V + matMulUnitaryOp Y V := by
  have hB := (hSeries L 4 4).1
  refine ContinuousLinearMap.ext fun u => lp.ext (funext fun x => ?_)
  rw [add_apply, lp.coeFn_add, Pi.add_apply, (hB (X + Y) V hV).1,
    (hB X V hV).1, (hB Y V hV).1]
  simp [matMulUnitary, map_add]
theorem matMulUnitaryOp_smul_one_id {L : ℕ}
    (hSeries : UnitaryOperatorSeriesClaim)
    (hRelations : MagneticWeylRelations) (c : ℂ) :
    matMulUnitaryOp (c • (1 : Matrix (Fin 4) (Fin 4) ℂ)) (magneticWeyl L 0 0) =
      (scalarOp c : BddOp (VectorL2 L 4)) := by
  have hB := ((hSeries L 4 4).1 (c • (1 : Matrix (Fin 4) (Fin 4) ℂ)) (magneticWeyl L 0 0)
    (magneticWeyl_isUnitary 0 0)).1
  have hId : ∀ u : ScalarL2 L, magneticWeyl L 0 0 u = u :=
    fun u => (hRelations L 0 0 0).2.1 u
  refine ContinuousLinearMap.ext fun u => lp.ext (funext fun x => ?_)
  rw [hB]
  have hC : applyCoordwise (magneticWeyl L 0 0) u x = u x := by
    ext i
    simp [applyCoordwise, hId, coord]
  simp [matMulUnitary, hC, scalarOp]
theorem hasAbsSummableFourier_of_isWeylSymbol {a : AmbientSpace → Matrix (Fin 4) (Fin 4) ℂ}
    (ha : IsWeylSymbol a) : HasAbsSummableFourier a := by
  obtain ⟨c, hc, hs⟩ := ha
  exact ⟨c, hc, by simpa using hs 0 (by norm_num)⟩
theorem weylQuant_add_smul_one {L : ℕ} (hSum : MagneticWeyl.SymbolAlgebra.Claim)
    (hQuant : WeylQuantHasSum)
    (hSeries : UnitaryOperatorSeriesClaim)
    (hRelations : MagneticWeylRelations)
    {a : AmbientSpace → Matrix (Fin 4) (Fin 4) ℂ} (ha : IsWeylSymbol a) (c : ℂ) :
    weylQuant L 0 (fun q => a q + c • (1 : Matrix (Fin 4) (Fin 4) ℂ)) =
      weylQuant L 0 a + scalarOp c := by
  set C : Matrix (Fin 4) (Fin 4) ℂ := c • 1 with hCdef
  obtain ⟨hConst, hC0, hCn, -⟩ := (hSum 4 4 4).2.1.2.2.1 C
  obtain ⟨hs, hco, -⟩ := (hSum 4 4 4).2.1.1 a (fun _ => C) ha hConst
  have h1 := (hQuant L 0 4 4 a (hasAbsSummableFourier_of_isWeylSymbol ha)).1
  have h2 := (hQuant L 0 4 4 _ (hasAbsSummableFourier_of_isWeylSymbol hs)).1
  have h3 : HasSum (fun n : Fin 4 → ℤ =>
      if n = 0 then (scalarOp c : BddOp (VectorL2 L 4)) else 0)
      (scalarOp c) := hasSum_ite_eq 0 _
  have hU := fun n => magneticWeyl_isUnitary (L := L) 0 n
  have hZero : ∀ n, matMulUnitaryOp (0 : Matrix (Fin 4) (Fin 4) ℂ)
      (magneticWeyl L 0 n) = 0 := by
    intro n
    have h := matMulUnitaryOp_add hSeries (0 : Matrix (Fin 4) (Fin 4) ℂ) 0 (hU n)
    rw [add_zero] at h
    exact left_eq_add.mp h
  have hTerm : ∀ n : Fin 4 → ℤ,
      matMulUnitaryOp (fourierCoeff (fun q => a q + C) n) (magneticWeyl L 0 n) =
        matMulUnitaryOp (fourierCoeff a n) (magneticWeyl L 0 n) +
          if n = 0 then (scalarOp c : BddOp (VectorL2 L 4)) else 0 := by
    intro n
    rw [hco, matMulUnitaryOp_add hSeries _ _ (hU n)]
    by_cases hn : n = 0
    · subst hn
      simp only [if_true]
      rw [hC0, hCdef, matMulUnitaryOp_smul_one_id hSeries hRelations]
    · simp only [if_neg hn]
      rw [hCn n hn, hZero]
  rw [funext hTerm] at h2
  exact h2.unique (h1.add h3)
theorem trace_scalarOp_sub {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {τ : BddOp H → ℂ} {𝔑 : ℕ} (h : AbelianFieldDensity.IsBoundedLinearTrace τ 𝔑) (c : ℂ)
    (T : BddOp H) : τ (scalarOp c - T) = c * (𝔑 : ℂ) - τ T := by apply _root_.YangMills.Construction.Tower.MagneticWeyl.FluxSecondOrder.trace_scalarOp_sub <;> assumption
theorem torusAverage_resolventGap {u : AmbientSpace → ℝ} (hu : Continuous u) (hpos : ∀ q, 0 < u q)
    {w : ℝ} (hw : 0 ≤ w) :
    torusAverage (resolventGap u w) =
      (((1 + w)⁻¹ : ℝ) : ℂ) - torusAverage fun q => (((u q + w)⁻¹ : ℝ) : ℂ) := by
  have hc : Continuous fun q => (((u q + w)⁻¹ : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (Continuous.inv₀ (hu.add continuous_const) fun q =>
      (add_pos_of_pos_of_nonneg (hpos q) hw).ne')
  have h := torusAverage_sub (continuous_const (y := (((1 + w)⁻¹ : ℝ) : ℂ))) hc
  rw [torusAverage_const] at h
  rw [← h]
  congr 1
  funext q
  simp only [resolventGap, abs_of_nonneg hw]
  push_cast
  rfl
end NeutralSector
open NeutralSector in
theorem neutralLogSecondOrder_holds
    (hDens : MagneticWeyl.ResolventDensityViaParametrix)
    (hLim : OperatorCalculus.Calculus.Statement)
    (hTrace : AbelianFieldDensity.TraceIsBoundedLinear)
    (hAdj : WeylQuantAdjoint)
    (hCalc : MagneticWeyl.FluxZeroCalculus.Claim)
    (hSum : MagneticWeyl.SymbolAlgebra.Claim)
    (hPsi : MagneticWeyl.ApproxInverseSymbolBounds)
    (hQuant : WeylQuantHasSum)
    (hSeries : UnitaryOperatorSeriesClaim)
    (hRelations : MagneticWeylRelations) :
    NeutralLogSecondOrder := by
  intro L _ z hz
  refine ⟨1, fun f hf => ?_⟩
  have hcos0 : 0 ≤ Real.cos f := by
    have h1 := Real.one_sub_sq_div_two_le_cos (x := f)
    have h2 : f ^ 2 ≤ 1 := by
      rw [← sq_abs]
      exact pow_le_one₀ (abs_nonneg f) hf
    linarith
  have hcos1 : Real.cos f ≤ 1 := Real.cos_le_one f
  have hψ0 : ∀ q, 0 ≤ psiR q := fun q => (rhoR_nonneg q).trans (rhoR_le_psiR q)
  have hfirst : ∀ s : ℝ, 0 < s → ∀ q, 0 < denomU s q := fun s hs q => by
    have := hψ0 q
    simp only [denomU]
    linarith
  have hsecond : ∀ s : ℝ, 0 < s → ∀ q, s ≤ denomV f s q := fun s hs q => by
    have h1 := rhoR_nonneg q
    have h2 := rhoR_le_psiR q
    simp only [denomV]
    nlinarith
  have hsym : IsWeylSymbol (neutralSectorSymbol f) := by
    have h := (isFiniteFourier_neutralSectorSymbol_add hSum hCalc hPsi f 0).1
    simpa using h
  have hright : ∀ s : ℝ, 0 < s → ∀ q,
      (neutralSectorSymbol f q + (s : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ)) * neutralInv f s q = 1 :=
    fun s hs q => neutralSectorSymbol_mul_neutralInv f s q (hfirst s hs q).ne'
      (hs.trans_le (hsecond s hs q)).ne'
  have hinv : ∀ s : ℝ, 0 < s → ∀ q,
      (neutralSectorSymbol f q + (s : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ))⁻¹ = neutralInv f s q :=
    fun s hs q => Matrix.inv_eq_right_inv (hright s hs q)
  have hcalc : ∀ s : ℝ, 0 < s → _ := fun s hs => (hCalc L 4 4 4).2.2.2.2.2
    (fun q => neutralSectorSymbol f q + (s : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ))
    (isFiniteFourier_neutralSectorSymbol_add hSum hCalc hPsi f _)
    (fun q => IsUnit.of_mul_eq_one _ (hright s hs q))
  set A := weylQuant L 0 (neutralSectorSymbol f) with hA
  have hAself : IsSelfAdjointOp A := by
    have h := (hAdj L 0 4 4 (neutralSectorSymbol f) hsym).2
    rwa [show pointwiseAdjoint (neutralSectorSymbol f) = neutralSectorSymbol f from
      funext (pointwiseAdjoint_neutralSectorSymbol f)] at h
  have hAtLeast : IsBoundedBelowBy (addScalar A z) (z / 2) := by
    refine isBoundedBelowBy_half_of_isUnit A hAself (fun t ht => ?_) hz
    rw [hA, ← weylQuant_add_smul_one hSum hQuant hSeries hRelations hsym]
    obtain ⟨-, h1, h2⟩ := hcalc t ht
    exact ⟨⟨_, _, h1, h2⟩, rfl⟩
  obtain ⟨hNumber, -, -, -, -, -, hLog⟩ := hLim (VectorL2 L 4) (VectorL2 L 4)
  set S := addScalar A z with hS
  have hSself : IsSelfAdjointOp S := (hNumber A hAself z 0).1
  obtain ⟨-, hnc, -, hint, -, huniq, hlog⟩ := hLog S (z / 2) hSself (by positivity) hAtLeast
  obtain ⟨hlin, hpass⟩ := (hTrace L 0).2.2 4 (by norm_num)
  obtain ⟨-, hconv, hτc, -, hτl, hτeq⟩ := hpass (resolventDiff S) hnc (by
    obtain ⟨l, hl⟩ := hint
    exact ⟨l, by simpa only [abs_norm] using hl⟩)
  have hX : AbelianFieldDensity.opIntegralIoi (resolventDiff S) =
      opLog S := huniq.unique hconv hlog
  have hlim : Tendsto (fun y : ℝ => ∫ w in (0 : ℝ)..y,
      AbelianFieldDensity.vecTraceAt (resolventDiff S w) 0) atTop
      (nhds (logTrace L z 0 (neutralSectorSymbol f))) := by
    have : logTrace L z 0 (neutralSectorSymbol f) =
        AbelianFieldDensity.complexIntegralIoi
          fun w => AbelianFieldDensity.vecTraceAt (resolventDiff S w) 0 := by
      rw [← hτeq, hX]
      rfl
    rw [this]
    exact hτl
  set u₁ : AmbientSpace → ℝ := fun q => psiR q + z with hu₁
  set u₂ : AmbientSpace → ℝ := fun q => psiR q + z + (Real.cos f - 1) * rhoR q with hu₂
  have hc₁ : Continuous u₁ := continuous_psiR.add continuous_const
  have hc₂ : Continuous u₂ :=
    hc₁.add (continuous_const.mul continuous_rhoR)
  have hlo₁ : ∀ q, z ≤ u₁ q := fun q => by
    have := hψ0 q
    simp only [hu₁]
    linarith
  have hlo₂ : ∀ q, z ≤ u₂ q := fun q => hsecond z hz q
  have hhi₁ : ∀ q, u₁ q ≤ 16 + z := fun q => by
    have := psiR_le_sixteen q
    simp only [hu₁]
    linarith
  have hhi₂ : ∀ q, u₂ q ≤ 16 + z := fun q => by
    have h1 := hhi₁ q
    have h2 := rhoR_nonneg q
    have h3 : (Real.cos f - 1) * rhoR q ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) h2
    simp only [hu₂]
    simp only [hu₁] at h1
    linarith
  have hp₁ : ∀ q, 0 < u₁ q := fun q => hz.trans_le (hlo₁ q)
  have hp₂ : ∀ q, 0 < u₂ q := fun q => hz.trans_le (hlo₂ q)
  have hres : ∀ w : ℝ, 0 ≤ w →
      AbelianFieldDensity.vecTraceAt (inverseOp (addScalar S w)) 0 =
        3 * (torusAverage fun q => (((u₁ q + w)⁻¹ : ℝ) : ℂ)) +
          torusAverage fun q => (((u₂ q + w)⁻¹ : ℝ) : ℂ) := by
    intro w hw
    have hzw : 0 < z + w := by positivity
    obtain ⟨hρ, -, -⟩ := hcalc (z + w) hzw
    have hconst := (hSum 4 4 4).2.1.2.2.1 (0 : Matrix (Fin 4) (Fin 4) ℂ)
    have hstar : moyalProduct 0
        (fun q => (neutralSectorSymbol f q +
          ((z + w : ℝ) : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ))⁻¹)
        (fun q => neutralSectorSymbol f q + ((z + w : ℝ) : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ)) =
        (fun q => 1 + (fun _ : AmbientSpace => (0 : Matrix (Fin 4) (Fin 4) ℂ)) q) := by
      rw [(hCalc L 4 4 4).2.2.1 _ _ hρ (isFiniteFourier_neutralSectorSymbol_add hSum hCalc hPsi f _).1]
      funext q
      rw [hinv _ hzw q, add_zero]
      exact mul_eq_one_comm.mp (hright _ hzw q)
    have h := hDens L 4 0 z w hz hw (neutralSectorSymbol f) _ _ hsym hρ hconst.1
      (pointwiseAdjoint_neutralSectorSymbol f) hAtLeast hstar
    have hzero : weightedCoeffNorm 0 (fun _ : AmbientSpace => (0 : Matrix (Fin 4) (Fin 4) ℂ)) = 0 := by
      have h0 := ((hSum 4 4 4).2.1.2.1 0 (neutralSectorSymbol f) hsym).2.2 0 (by norm_num)
      simpa using h0
    rw [hzero, mul_zero, zero_mul] at h
    have heq := sub_eq_zero.mp (norm_le_zero_iff.mp h)
    rw [show inverseOp (addScalar S w) =
      inverseOp (addScalar (addScalar (weylQuant L 0 (neutralSectorSymbol f)) z) w) from rfl, heq]
    have hcw : ∀ {u : AmbientSpace → ℝ}, Continuous u → (∀ q, 0 < u q) →
        Continuous fun q => (((u q + w)⁻¹ : ℝ) : ℂ) := fun hu hpos =>
      Complex.continuous_ofReal.comp (Continuous.inv₀ (hu.add continuous_const) fun q =>
        (add_pos_of_pos_of_nonneg (hpos q) hw).ne')
    have hc3 : Continuous fun q => (3 : ℂ) * (((u₁ q + w)⁻¹ : ℝ) : ℂ) :=
      continuous_const.mul (hcw hc₁ hp₁)
    rw [← torusAverage_const_mul, ← torusAverage_add hc3 (hcw hc₂ hp₂)]
    congr 1
    funext q
    rw [hinv _ hzw q, diagSum_neutralInv f _ q (hfirst _ hzw q).ne'
      (hzw.trans_le (hsecond _ hzw q)).ne']
    have e1 : denomU (z + w) q = u₁ q + w := by
      simp only [denomU, hu₁]
      ring
    have e2 : denomV f (z + w) q = u₂ q + w := by
      simp only [denomV, hu₂]
      ring
    rw [e1, e2]
  have hτ : ∀ w : ℝ, 0 ≤ w → AbelianFieldDensity.vecTraceAt (resolventDiff S w) 0 =
      3 * torusAverage (resolventGap u₁ w) + torusAverage (resolventGap u₂ w) := by
    intro w hw
    have h := _root_.YangMills.Construction.Tower.ConstantFieldSymbols.NeutralSector.trace_scalarOp_sub hlin (((1 + w)⁻¹ : ℝ) : ℂ) (inverseOp (addScalar S w))
    have h' : AbelianFieldDensity.vecTraceAt (resolventDiff S w) 0 = _ := h
    rw [h', hres w hw, torusAverage_resolventGap hc₁ hp₁ hw, torusAverage_resolventGap hc₂ hp₂ hw]
    push_cast
    ring
  have hG₁ : Continuous fun w => torusAverage (resolventGap u₁ w) :=
    continuous_torusAverage (continuous_uncurry_resolventGap hc₁ hp₁)
  have hG₂ : Continuous fun w => torusAverage (resolventGap u₂ w) :=
    continuous_torusAverage (continuous_uncurry_resolventGap hc₂ hp₂)
  have hT₁ := tendsto_integral_resolventGap hc₁ hz hlo₁ hhi₁
  have hT₂ := tendsto_integral_resolventGap hc₂ hz hlo₂ hhi₂
  have hsplit : ∀ y : ℝ, 0 ≤ y →
      3 * (∫ w in (0 : ℝ)..y, torusAverage (resolventGap u₁ w)) +
          (∫ w in (0 : ℝ)..y, torusAverage (resolventGap u₂ w)) =
        ∫ w in (0 : ℝ)..y, AbelianFieldDensity.vecTraceAt (resolventDiff S w) 0 := by
    intro y hy
    have hG₃ : Continuous fun w => (3 : ℂ) * torusAverage (resolventGap u₁ w) :=
      continuous_const.mul hG₁
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add
      (hG₃.intervalIntegrable _ _) (hG₂.intervalIntegrable _ _)]
    refine intervalIntegral.integral_congr fun w hw => ?_
    rw [uIcc_of_le hy] at hw
    exact (hτ w hw.1).symm
  have hvalue : logTrace L z 0 (neutralSectorSymbol f) =
      3 * (torusAverage fun q => ((Real.log (u₁ q) : ℝ) : ℂ)) +
        torusAverage fun q => ((Real.log (u₂ q) : ℝ) : ℂ) := by
    refine tendsto_nhds_unique hlim (((hT₁.const_mul 3).add hT₂).congr' ?_)
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with y hy
    exact hsplit y hy
  have hl₁ : Continuous fun q => ((Real.log (u₁ q) : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (hc₁.log fun q => (hp₁ q).ne')
  have hl₂ : Continuous fun q => ((Real.log (u₂ q) : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (hc₂.log fun q => (hp₂ q).ne')
  have hzeroth : constantTerm 4 z =
      4 * torusAverage fun q => ((Real.log (u₁ q) : ℝ) : ℂ) := by
    rw [← torusAverage_const_mul]
    unfold constantTerm
    congr 1
    funext q
    rw [diagSum_smul_four, diagSum_one_four, latticeSymbol_eq_psiR, ← Complex.ofReal_add,
      Complex.ofReal_log (hp₁ q).le, mul_comm]
  have hρc : Continuous fun q => ((rhoR q / u₁ q : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (continuous_rhoR.div hc₁ fun q => (hp₁ q).ne')
  have hsecondCoefficient : (torusAverage fun q => resolvent z (toComplexVec q) *
      (axisSymbol 0 (toComplexVec q) + axisSymbol 1 (toComplexVec q))) =
      torusAverage fun q => ((rhoR q / u₁ q : ℝ) : ℂ) := by
    congr 1
    funext q
    rw [axisSymbol_add_eq_rhoR, Massive.resolvent, latticeSymbol_eq_psiR]
    simp only [hu₁]
    push_cast
    rw [div_eq_mul_inv, mul_comm]
  rw [hvalue, hzeroth, hsecondCoefficient, one_mul]
  have hcombine : 3 * (torusAverage fun q => ((Real.log (u₁ q) : ℝ) : ℂ)) +
        (torusAverage fun q => ((Real.log (u₂ q) : ℝ) : ℂ)) -
      (4 * (torusAverage fun q => ((Real.log (u₁ q) : ℝ) : ℂ)) -
        (f : ℂ) ^ 2 / 2 * torusAverage fun q => ((rhoR q / u₁ q : ℝ) : ℂ)) =
      torusAverage fun q => ((Real.log (u₂ q) - Real.log (u₁ q) +
        f ^ 2 / 2 * (rhoR q / u₁ q) : ℝ) : ℂ) := by
    have h1 := torusAverage_sub hl₂ hl₁
    have h2 := torusAverage_const_mul ((f : ℂ) ^ 2 / 2) fun q => ((rhoR q / u₁ q : ℝ) : ℂ)
    have hc4 : Continuous fun q => (f : ℂ) ^ 2 / 2 * ((rhoR q / u₁ q : ℝ) : ℂ) :=
      continuous_const.mul hρc
    have hc5 : Continuous fun q => ((Real.log (u₂ q) : ℝ) : ℂ) - ((Real.log (u₁ q) : ℝ) : ℂ) :=
      hl₂.sub hl₁
    have h3 := torusAverage_add hc5 hc4
    have hfun : (fun q => ((Real.log (u₂ q) - Real.log (u₁ q) +
        f ^ 2 / 2 * (rhoR q / u₁ q) : ℝ) : ℂ)) = fun q =>
        (((Real.log (u₂ q) : ℝ) : ℂ) - ((Real.log (u₁ q) : ℝ) : ℂ)) +
          (f : ℂ) ^ 2 / 2 * ((rhoR q / u₁ q : ℝ) : ℂ) := by
      funext q
      push_cast
      ring
    rw [hfun, h3, h1, h2]
    ring
  rw [hcombine]
  refine norm_torusAverage_le fun q _ => ?_
  rw [Complex.norm_real, Real.norm_eq_abs]
  exact abs_log_quadratic_remainder_le (rhoR_nonneg q) (rhoR_le_psiR q) hz hf
end YangMills.Construction.Tower.ConstantFieldSymbols
end
