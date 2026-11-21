import YangMills.Construction.FormsOnATorus.ColumnOfTheLimitFormProof
import YangMills.Construction.PassageToTheLimit.SpaceAsAMetricSpaceTestFunctionsTranslationsReflectionsProof
import YangMills.Construction.Towers.AsymptoticsOfTheMassiveCoefficientProof
import YangMills.Construction.Towers.CoefficientsOfASymbol
import YangMills.Construction.Towers.StarProductOfTwoSymbols
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Tower.UnitLatticeL2 OneLoopNotation
open InfiniteLattice (AmbientSpace)
open PeriodicOperators (castVec toComplexVec bilinDot)
open scoped Matrix.Norms.L2Operator
namespace Tower
namespace MoyalProduct
open MagneticWeyl
theorem opNormValue_eq_norm {M M' : ℕ} [NeZero M] [NeZero M'] (X : Matrix (Fin M) (Fin M') ℂ) :
    Matrices.RectangularMatrix.opNormValue X = ‖X‖ :=
  (Matrix.l2_opNorm_def X).symm
def latticeWeight (v : Fin 4 → ℤ) : ℝ := 1 + TorusMetric.euclidNormVec (castVec v)
theorem euclidNormVec_nonneg (x : Fin 4 → ℝ) : 0 ≤ TorusMetric.euclidNormVec x := by apply _root_.YangMills.Construction.Parametrix.UnitKernelSupport.euclidNormVec_nonneg <;> assumption
theorem one_le_latticeWeight (v : Fin 4 → ℤ) : 1 ≤ latticeWeight v := by apply _root_.YangMills.DeltaSharedProofs.p500919 <;> assumption
theorem euclidNormVec_add_le (x y : Fin 4 → ℝ) :
    TorusMetric.euclidNormVec (x + y) ≤
      TorusMetric.euclidNormVec x + TorusMetric.euclidNormVec y := by apply _root_.YangMills.Construction.LimitSpaces.AmbientMetric.euclidNormVec_add_le <;> assumption
theorem latticeWeight_add_le (v w : Fin 4 → ℤ) :
    latticeWeight (v + w) ≤ latticeWeight v * latticeWeight w := by
  have hcast : castVec (v + w) = castVec v + castVec w := by
    funext i
    simp [castVec]
  have htri := euclidNormVec_add_le (castVec v) (castVec w)
  rw [← hcast] at htri
  have hv := euclidNormVec_nonneg (castVec v)
  have hw := euclidNormVec_nonneg (castVec w)
  simp only [latticeWeight]
  nlinarith [mul_nonneg hv hw]
theorem norm_exp_half_phase (θ : ℝ) (k : ℤ) :
    ‖Complex.exp (Complex.I / 2 * (θ : ℂ) * (k : ℂ))‖ = 1 := by
  have : Complex.I / 2 * (θ : ℂ) * (k : ℂ) = ((θ * k / 2 : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [this, Complex.norm_exp_ofReal_mul_I]
theorem norm_fourierChar (v : Fin 4 → ℤ) (x : AmbientSpace) : ‖fourierChar v x‖ = 1 := by apply _root_.YangMills.Construction.Tower.Massive.CoefficientAsymptoticsProof.norm_fourierChar <;> assumption
variable {d₁ d₂ d₃ : ℕ}
def twistedConvolution (θ : ℝ) (F : (Fin 4 → ℤ) → Matrix (Fin d₁) (Fin d₂) ℂ)
    (G : (Fin 4 → ℤ) → Matrix (Fin d₂) (Fin d₃) ℂ) (v : Fin 4 → ℤ) :
    Matrix (Fin d₁) (Fin d₃) ℂ :=
  ∑' p : {p : (Fin 4 → ℤ) × (Fin 4 → ℤ) // p.1 + p.2 = v},
    Complex.exp (Complex.I / 2 * (θ : ℂ) * (symplecticForm p.1.1 p.1.2 : ℂ)) • (F p.1.1 * G p.1.2)
theorem twistedConvolution_weighted_bound (θ : ℝ) (F : (Fin 4 → ℤ) → Matrix (Fin d₁) (Fin d₂) ℂ)
    (G : (Fin 4 → ℤ) → Matrix (Fin d₂) (Fin d₃) ℂ) (r : ℕ)
    (hF : Summable fun v => ‖F v‖ * latticeWeight v ^ r)
    (hG : Summable fun v => ‖G v‖ * latticeWeight v ^ r) :
    (Summable fun v => ‖twistedConvolution θ F G v‖ * latticeWeight v ^ r) ∧
      ∑' v, ‖twistedConvolution θ F G v‖ * latticeWeight v ^ r ≤
        (∑' v, ‖F v‖ * latticeWeight v ^ r) * ∑' v, ‖G v‖ * latticeWeight v ^ r := by
  have hw0 : ∀ v, 0 ≤ latticeWeight v ^ r := fun v =>
    pow_nonneg (le_trans zero_le_one (one_le_latticeWeight v)) r
  have hwne : ∀ v, latticeWeight v ^ r ≠ 0 := fun v =>
    (pow_pos (lt_of_lt_of_le zero_lt_one (one_le_latticeWeight v)) r).ne'
  set f : (Fin 4 → ℤ) → ℝ := fun v => ‖F v‖ * latticeWeight v ^ r with hf
  set g : (Fin 4 → ℤ) → ℝ := fun v => ‖G v‖ * latticeWeight v ^ r with hg
  have hf0 : ∀ v, 0 ≤ f v := fun v => mul_nonneg (norm_nonneg _) (hw0 v)
  have hg0 : ∀ v, 0 ≤ g v := fun v => mul_nonneg (norm_nonneg _) (hw0 v)
  have hprod : Summable (fun p : (Fin 4 → ℤ) × (Fin 4 → ℤ) => f p.1 * g p.2) :=
    hF.mul_of_nonneg hG hf0 hg0
  have hprodsum : (∑' v, f v) * ∑' v, g v = ∑' p : (Fin 4 → ℤ) × (Fin 4 → ℤ), f p.1 * g p.2 :=
    hF.tsum_mul_tsum hG hprod
  let e := Equiv.sigmaFiberEquiv (fun p : (Fin 4 → ℤ) × (Fin 4 → ℤ) => p.1 + p.2)
  let T : (Σ v : Fin 4 → ℤ, {p : (Fin 4 → ℤ) × (Fin 4 → ℤ) // p.1 + p.2 = v}) → ℝ :=
    fun s => f s.2.1.1 * g s.2.1.2
  have hT : Summable T :=
    (e.summable_iff (f := fun p : (Fin 4 → ℤ) × (Fin 4 → ℤ) => f p.1 * g p.2)).mpr hprod
  have hT0 : 0 ≤ T := fun s => mul_nonneg (hf0 _) (hg0 _)
  obtain ⟨hfibre, houter⟩ := (summable_sigma_of_nonneg hT0).mp hT
  have houtersum : ∑' v, ∑' p, T ⟨v, p⟩ = (∑' v, f v) * ∑' v, g v := by
    rw [hprodsum, ← hT.tsum_sigma]
    exact e.tsum_eq (fun p : (Fin 4 → ℤ) × (Fin 4 → ℤ) => f p.1 * g p.2)
  have hcmp : ∀ v, ‖twistedConvolution θ F G v‖ * latticeWeight v ^ r ≤ ∑' p, T ⟨v, p⟩ := by
    intro v
    have hterm : ∀ p : {p : (Fin 4 → ℤ) × (Fin 4 → ℤ) // p.1 + p.2 = v},
        ‖Complex.exp (Complex.I / 2 * (θ : ℂ) * (symplecticForm p.1.1 p.1.2 : ℂ)) • (F p.1.1 * G p.1.2)‖ *
          latticeWeight v ^ r ≤ T ⟨v, p⟩ := by
      intro p
      have hwt : latticeWeight v ^ r ≤ latticeWeight p.1.1 ^ r * latticeWeight p.1.2 ^ r := by
        have hle : latticeWeight v ≤ latticeWeight p.1.1 * latticeWeight p.1.2 := by
          have := latticeWeight_add_le p.1.1 p.1.2
          rwa [p.2] at this
        rw [← mul_pow]
        exact pow_le_pow_left₀ (le_trans zero_le_one (one_le_latticeWeight _)) hle r
      have hnm : ‖Complex.exp (Complex.I / 2 * (θ : ℂ) * (symplecticForm p.1.1 p.1.2 : ℂ)) •
          (F p.1.1 * G p.1.2)‖ ≤ ‖F p.1.1‖ * ‖G p.1.2‖ := by
        rw [norm_smul, norm_exp_half_phase, one_mul]
        exact Matrix.l2_opNorm_mul _ _
      calc _ ≤ (‖F p.1.1‖ * ‖G p.1.2‖) * (latticeWeight p.1.1 ^ r * latticeWeight p.1.2 ^ r) :=
            mul_le_mul hnm hwt (hw0 v) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
        _ = T ⟨v, p⟩ := by
            simp only [T, hf, hg]
            ring
    have hsw : Summable fun p : {p : (Fin 4 → ℤ) × (Fin 4 → ℤ) // p.1 + p.2 = v} =>
        ‖Complex.exp (Complex.I / 2 * (θ : ℂ) * (symplecticForm p.1.1 p.1.2 : ℂ)) • (F p.1.1 * G p.1.2)‖ *
          latticeWeight v ^ r :=
      Summable.of_nonneg_of_le (fun _ => mul_nonneg (norm_nonneg _) (hw0 v)) hterm (hfibre v)
    have hsn : Summable fun p : {p : (Fin 4 → ℤ) × (Fin 4 → ℤ) // p.1 + p.2 = v} =>
        ‖Complex.exp (Complex.I / 2 * (θ : ℂ) * (symplecticForm p.1.1 p.1.2 : ℂ)) • (F p.1.1 * G p.1.2)‖ :=
      (summable_mul_right_iff (hwne v)).mp hsw
    calc ‖twistedConvolution θ F G v‖ * latticeWeight v ^ r
        ≤ (∑' p : {p : (Fin 4 → ℤ) × (Fin 4 → ℤ) // p.1 + p.2 = v},
            ‖Complex.exp (Complex.I / 2 * (θ : ℂ) * (symplecticForm p.1.1 p.1.2 : ℂ)) •
              (F p.1.1 * G p.1.2)‖) * latticeWeight v ^ r :=
          mul_le_mul_of_nonneg_right (norm_tsum_le_tsum_norm hsn) (hw0 v)
      _ = ∑' p : {p : (Fin 4 → ℤ) × (Fin 4 → ℤ) // p.1 + p.2 = v},
            ‖Complex.exp (Complex.I / 2 * (θ : ℂ) * (symplecticForm p.1.1 p.1.2 : ℂ)) •
              (F p.1.1 * G p.1.2)‖ * latticeWeight v ^ r := tsum_mul_right.symm
      _ ≤ ∑' p, T ⟨v, p⟩ := hsw.tsum_le_tsum hterm (hfibre v)
  have hsumm : Summable fun v => ‖twistedConvolution θ F G v‖ * latticeWeight v ^ r :=
    Summable.of_nonneg_of_le (fun v => mul_nonneg (norm_nonneg _) (hw0 v)) hcmp houter
  exact ⟨hsumm, (hsumm.tsum_le_tsum hcmp houter).trans houtersum.le⟩
end MoyalProduct
open MagneticWeyl MoyalProduct in
theorem moyalProductBounds_of_fourierCoeffs (h : FourierCoeffsOfSymbol) :
    MoyalProductBounds := by
  intro θ d₁ d₂ d₃ _ _ _ s t hs ht
  have hss := ((h d₁ d₂ s).2 hs).2
  have hst := ((h d₂ d₃ t).2 ht).2
  have key : ∀ r : ℕ, r ≤ 3 →
      Summable (fun v => Matrices.RectangularMatrix.opNormValue (moyalCoeff θ s t v) *
        (1 + TorusMetric.euclidNormVec (castVec v)) ^ r) ∧
      ∑' v, Matrices.RectangularMatrix.opNormValue (moyalCoeff θ s t v) *
        (1 + TorusMetric.euclidNormVec (castVec v)) ^ r ≤
          weightedCoeffNorm r s * weightedCoeffNorm r t := by
    intro r hr
    have hb := twistedConvolution_weighted_bound θ (fourierCoeff s) (fourierCoeff t) r
      (by simpa only [opNormValue_eq_norm, latticeWeight] using hss r hr)
      (by simpa only [opNormValue_eq_norm, latticeWeight] using hst r hr)
    have hmc : moyalCoeff θ s t = twistedConvolution θ (fourierCoeff s) (fourierCoeff t) := rfl
    simpa only [hmc, opNormValue_eq_norm, latticeWeight, weightedCoeffNorm] using hb
  have hsum0 : Summable fun v => Matrices.RectangularMatrix.opNormValue (moyalCoeff θ s t v) := by
    simpa using (key 0 (by norm_num)).1
  have hexp : HasFourierExpansion (moyalCoeff θ s t) (moyalProduct θ s t) := by
    intro x
    have hx : Summable fun v => fourierChar v x • moyalCoeff θ s t v := by
      refine Summable.of_norm ?_
      simp only [norm_smul, norm_fourierChar, one_mul, ← opNormValue_eq_norm]
      exact hsum0
    exact hx.hasSum
  have hsym : IsWeylSymbol (moyalProduct θ s t) := ⟨_, hexp, fun r hr => (key r hr).1⟩
  have hcoeff : fourierCoeff (moyalProduct θ s t) = moyalCoeff θ s t :=
    (((h d₁ d₃ _).1 ⟨_, hexp, hsum0⟩).2.2 _ hexp hsum0).symm
  refine ⟨key, hexp, hsym, hcoeff, fun r hr => ?_⟩
  have hnorm : weightedCoeffNorm r (moyalProduct θ s t) = ∑' v,
      Matrices.RectangularMatrix.opNormValue (moyalCoeff θ s t v) *
        (1 + TorusMetric.euclidNormVec (castVec v)) ^ r := by
    rw [weightedCoeffNorm, hcoeff]
  rw [hnorm]
  exact (key r hr).2
end Tower
end YangMills.Construction
end
