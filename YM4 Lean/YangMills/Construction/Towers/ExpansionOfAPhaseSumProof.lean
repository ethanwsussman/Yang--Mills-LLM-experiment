import YangMills.Construction.Towers.CoefficientsOfASymbol
import YangMills.Construction.Towers.ExpansionOfAPhaseSum
import YangMills.Construction.Towers.SumsAndProductsOfSymbols
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction
open InfiniteLattice (AmbientSpace)
open PeriodicOperators (toComplexVec castVec)
open scoped ComplexConjugate
noncomputable section
namespace Tower
open UnitLatticeL2
namespace ConstantFieldSymbols
open MagneticWeyl AbelianFieldDensity
namespace TrigMatrixSum
def planeWaveMatrix (n : Fin 4 → ℤ) (M : Matrix (Fin 4) (Fin 4) ℂ) (q : AmbientSpace) :
    Matrix (Fin 4) (Fin 4) ℂ :=
  fourierChar n q • M
def planeWaveCoeff (n : Fin 4 → ℤ) (M : Matrix (Fin 4) (Fin 4) ℂ) (m : Fin 4 → ℤ) :
    Matrix (Fin 4) (Fin 4) ℂ := by
  classical exact if m = n then M else 0
theorem planeWaveCoeff_self (n : Fin 4 → ℤ) (M : Matrix (Fin 4) (Fin 4) ℂ) :
    planeWaveCoeff n M n = M := by
  simp [planeWaveCoeff]
theorem planeWaveCoeff_of_ne {n m : Fin 4 → ℤ} (M : Matrix (Fin 4) (Fin 4) ℂ) (h : m ≠ n) :
    planeWaveCoeff n M m = 0 := by
  simp [planeWaveCoeff, h]
theorem opNormValue_zero :
    Matrices.RectangularMatrix.opNormValue (0 : Matrix (Fin 4) (Fin 4) ℂ) = 0 := by
  simp [Matrices.RectangularMatrix.opNormValue, OneLoopNotation.opNormOf]
theorem planeWaveMatrix_hasFourierExpansion (n : Fin 4 → ℤ) (M : Matrix (Fin 4) (Fin 4) ℂ) :
    HasFourierExpansion (planeWaveCoeff n M) (planeWaveMatrix n M) := by
  intro q
  have h := hasSum_single (f := fun m => fourierChar m q • planeWaveCoeff n M m) n
    (fun m hm => by simp [planeWaveCoeff_of_ne M hm])
  simpa [planeWaveCoeff_self, planeWaveMatrix] using h
theorem planeWaveMatrix_summable (n : Fin 4 → ℤ) (M : Matrix (Fin 4) (Fin 4) ℂ) (j : ℕ) :
    Summable fun m => Matrices.RectangularMatrix.opNormValue (planeWaveCoeff n M m) *
      (1 + TorusMetric.euclidNormVec (castVec m)) ^ j :=
  summable_of_ne_finset_zero (s := {n}) fun m hm => by
    rw [planeWaveCoeff_of_ne M (by simpa using hm), opNormValue_zero, zero_mul]
theorem planeWaveMatrix_isWeylSymbol (n : Fin 4 → ℤ) (M : Matrix (Fin 4) (Fin 4) ℂ) :
    IsWeylSymbol (planeWaveMatrix n M) :=
  ⟨_, planeWaveMatrix_hasFourierExpansion n M, fun j _ => planeWaveMatrix_summable n M j⟩
theorem fourierCoeff_planeWaveMatrix (hcoeff : FourierCoeffsOfSymbol) (n : Fin 4 → ℤ)
    (M : Matrix (Fin 4) (Fin 4) ℂ) : fourierCoeff (planeWaveMatrix n M) = planeWaveCoeff n M := by
  have hs : Summable fun m => Matrices.RectangularMatrix.opNormValue (planeWaveCoeff n M m) := by
    simpa using planeWaveMatrix_summable n M 0
  exact (((hcoeff 4 4 (planeWaveMatrix n M)).1
    ⟨_, planeWaveMatrix_hasFourierExpansion n M, hs⟩).2.2 _
    (planeWaveMatrix_hasFourierExpansion n M) hs).symm
variable {ι : Type}
def weightedWaveSum (s : Finset ι) (n : ι → Fin 4 → ℤ) (M : ι → Matrix (Fin 4) (Fin 4) ℂ)
    (g : ι → ℂ) (q : AmbientSpace) : Matrix (Fin 4) (Fin 4) ℂ :=
  ∑ k ∈ s, g k • planeWaveMatrix (n k) (M k) q
theorem weightedWaveSum_props (hcoeff : FourierCoeffsOfSymbol)
    (hsymbols : SymbolAlgebra.Claim) (s : Finset ι) (n : ι → Fin 4 → ℤ)
    (M : ι → Matrix (Fin 4) (Fin 4) ℂ) (g : ι → ℂ) :
    IsWeylSymbol (weightedWaveSum s n M g) ∧
      (∀ m, fourierCoeff (weightedWaveSum s n M g) m =
        ∑ k ∈ s, g k • planeWaveCoeff (n k) (M k) m) ∧
      weightedCoeffNorm 3 (weightedWaveSum s n M g) ≤
        ∑ k ∈ s, ‖g k‖ * weightedCoeffNorm 3 (planeWaveMatrix (n k) (M k)) := by
  classical
  obtain ⟨hadd, hmul, hconst, -⟩ := (hsymbols 4 4 4).2.1
  induction s using Finset.induction_on with
  | empty =>
    have hz : weightedWaveSum (∅ : Finset ι) n M g =
        fun q => (0 : ℂ) • (fun _ : AmbientSpace => (0 : Matrix (Fin 4) (Fin 4) ℂ)) q := by
      funext q
      simp [weightedWaveSum]
    rw [hz]
    obtain ⟨h1, h2, h3⟩ := hmul 0 _ (hconst 0).1
    refine ⟨h1, fun m => ?_, ?_⟩
    · rw [h2 m]
      simp
    · rw [h3 3 le_rfl]
      simp
  | insert k s hk ih =>
    obtain ⟨ih1, ih2, ih3⟩ := ih
    obtain ⟨m1, m2, m3⟩ := hmul (g k) _ (planeWaveMatrix_isWeylSymbol (n k) (M k))
    obtain ⟨a1, a2, a3⟩ := hadd _ _ m1 ih1
    have hz : weightedWaveSum (insert k s) n M g =
        fun q => g k • planeWaveMatrix (n k) (M k) q + weightedWaveSum s n M g q := by
      funext q
      simp [weightedWaveSum, Finset.sum_insert hk]
    rw [hz]
    refine ⟨a1, fun m => ?_, ?_⟩
    · rw [a2 m, m2 m, ih2 m, fourierCoeff_planeWaveMatrix hcoeff, Finset.sum_insert hk]
    · rw [Finset.sum_insert hk]
      refine (a3 3 le_rfl).trans ?_
      rw [m3 3 le_rfl]
      exact add_le_add_right ih3 _
theorem norm_cexp_I_mul_sub_taylor_le (x : ℝ) :
    ‖Complex.exp (Complex.I * (x : ℂ)) - 1 - Complex.I * (x : ℂ) + (x : ℂ) ^ 2 / 2‖ ≤
      |x| ^ 3 := by
  have hexp : ∀ t : ℝ, HasDerivAt (fun u : ℝ => Complex.exp (Complex.I * (u : ℂ)))
      (Complex.I * Complex.exp (Complex.I * (t : ℂ))) t := by
    intro t
    have h1 : HasDerivAt (fun u : ℝ => Complex.I * (u : ℂ)) Complex.I t := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := t)).const_mul Complex.I
    simpa [mul_comm] using h1.cexp
  have hlin : ∀ t : ℝ, HasDerivAt (fun u : ℝ => Complex.I * (u : ℂ)) Complex.I t := by
    intro t
    simpa using (Complex.ofRealCLM.hasDerivAt (x := t)).const_mul Complex.I
  have hsq : ∀ t : ℝ, HasDerivAt (fun u : ℝ => (u : ℂ) ^ 2 / 2) (t : ℂ) t := by
    intro t
    have h1 : HasDerivAt (fun u : ℝ => (u : ℂ)) 1 t := by
      simpa using (hasDerivAt_id t).ofReal_comp
    simpa using (h1.pow 2).div_const 2
  have h2 : ∀ t : ℝ, ‖Complex.exp (Complex.I * (t : ℂ)) - 1 - Complex.I * (t : ℂ)‖ ≤ t ^ 2 := by
    intro t
    have hd : ∀ u ∈ Set.Icc (-|t|) |t|, HasDerivWithinAt
        (fun u : ℝ => Complex.exp (Complex.I * (u : ℂ)) - 1 - Complex.I * (u : ℂ))
        (Complex.I * (Complex.exp (Complex.I * (u : ℂ)) - 1)) (Set.Icc (-|t|) |t|) u := by
      intro u _
      have := ((hexp u).sub_const 1).sub (hlin u)
      have he : Complex.I * Complex.exp (Complex.I * (u : ℂ)) - Complex.I =
          Complex.I * (Complex.exp (Complex.I * (u : ℂ)) - 1) := by ring
      rw [he] at this
      exact this.hasDerivWithinAt
    have hb : ∀ u ∈ Set.Icc (-|t|) |t|,
        ‖Complex.I * (Complex.exp (Complex.I * (u : ℂ)) - 1)‖ ≤ |t| := by
      intro u hu
      rw [norm_mul, Complex.norm_I, one_mul]
      refine Real.norm_exp_I_mul_ofReal_sub_one_le.trans ?_
      rw [Real.norm_eq_abs]
      exact abs_le.mpr hu
    have hm := (convex_Icc (-|t|) |t|).norm_image_sub_le_of_norm_hasDerivWithin_le hd hb
      (x := 0) (y := t) (by simp) (by simp [neg_abs_le, le_abs_self])
    simpa [sq_abs, sq, abs_mul_abs_self] using hm
  have hd : ∀ u ∈ Set.Icc (-|x|) |x|, HasDerivWithinAt
      (fun u : ℝ => Complex.exp (Complex.I * (u : ℂ)) - 1 - Complex.I * (u : ℂ) + (u : ℂ) ^ 2 / 2)
      (Complex.I * (Complex.exp (Complex.I * (u : ℂ)) - 1 - Complex.I * (u : ℂ)))
      (Set.Icc (-|x|) |x|) u := by
    intro u _
    have := (((hexp u).sub_const 1).sub (hlin u)).add (hsq u)
    have he : Complex.I * Complex.exp (Complex.I * (u : ℂ)) - Complex.I + (u : ℂ) =
        Complex.I * (Complex.exp (Complex.I * (u : ℂ)) - 1 - Complex.I * (u : ℂ)) := by
      linear_combination (u : ℂ) * Complex.I_sq
    rw [he] at this
    exact this.hasDerivWithinAt
  have hb : ∀ u ∈ Set.Icc (-|x|) |x|,
      ‖Complex.I * (Complex.exp (Complex.I * (u : ℂ)) - 1 - Complex.I * (u : ℂ))‖ ≤ x ^ 2 := by
    intro u hu
    rw [norm_mul, Complex.norm_I, one_mul]
    refine (h2 u).trans ?_
    exact sq_le_sq.mpr (abs_le.mpr hu)
  have hm := (convex_Icc (-|x|) |x|).norm_image_sub_le_of_norm_hasDerivWithin_le hd hb
    (x := 0) (y := x) (by simp) (by simp [neg_abs_le, le_abs_self])
  have e3 : |x| ^ 3 = x ^ 2 * |x| := by
    rw [pow_succ, sq_abs]
  simpa [e3] using hm
theorem nonpos_of_le_const_mul {a K : ℝ}
    (h : ∀ φ : ℝ, 0 < φ → φ ≤ Real.pi → a ≤ K * φ) : a ≤ 0 := by
  by_contra ha
  push Not at ha
  have hK : 0 < 2 * (|K| + 1) := by positivity
  have h0 : 0 < min Real.pi (a / (2 * (|K| + 1))) := lt_min Real.pi_pos (div_pos ha hK)
  have h1 : min Real.pi (a / (2 * (|K| + 1))) ≤ a / (2 * (|K| + 1)) := min_le_right _ _
  have h2 := h _ h0 (min_le_left _ _)
  generalize min Real.pi (a / (2 * (|K| + 1))) = φ at h0 h1 h2
  have h3 : K * φ ≤ |K| * φ := mul_le_mul_of_nonneg_right (le_abs_self K) h0.le
  have h4 : φ * (2 * (|K| + 1)) ≤ a := (le_div_iff₀ hK).mp h1
  nlinarith [abs_nonneg K]
theorem eq_zero_of_linear_quadratic_cubic (x y : ℂ) (K : ℝ)
    (h : ∀ φ : ℝ, |φ| ≤ Real.pi → ‖(φ : ℂ) * x + (φ : ℂ) ^ 2 * y‖ ≤ K * |φ| ^ 3) :
    x = 0 ∧ y = 0 := by
  have hy : y = 0 := by
    have hle : ‖y‖ ≤ 0 := by
      refine nonpos_of_le_const_mul (K := K) fun φ hφ hπ => ?_
      have h1 := h φ (by rwa [abs_of_pos hφ])
      have h2 := h (-φ) (by rwa [abs_neg, abs_of_pos hφ])
      rw [abs_neg] at h2
      rw [abs_of_pos hφ] at h1 h2
      have e : ((2 * φ ^ 2 : ℝ) : ℂ) * y = ((φ : ℂ) * x + (φ : ℂ) ^ 2 * y) +
          (((-φ : ℝ) : ℂ) * x + ((-φ : ℝ) : ℂ) ^ 2 * y) := by
        push_cast
        ring
      have h3 : ‖((2 * φ ^ 2 : ℝ) : ℂ) * y‖ ≤ K * φ ^ 3 + K * φ ^ 3 := by
        rw [e]
        exact (norm_add_le _ _).trans (add_le_add h1 h2)
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)] at h3
      have hp : 0 < 2 * φ ^ 2 := by positivity
      have h4 : (2 * φ ^ 2) * ‖y‖ ≤ (2 * φ ^ 2) * (K * φ) := by
        calc (2 * φ ^ 2) * ‖y‖ ≤ K * φ ^ 3 + K * φ ^ 3 := h3
          _ = (2 * φ ^ 2) * (K * φ) := by ring
      exact le_of_mul_le_mul_left h4 hp
    exact norm_le_zero_iff.mp hle
  refine ⟨?_, hy⟩
  have hle : ‖x‖ ≤ 0 := by
    refine nonpos_of_le_const_mul (K := |K| * Real.pi) fun φ hφ hπ => ?_
    have h1 := h φ (by rwa [abs_of_pos hφ])
    rw [abs_of_pos hφ] at h1
    simp only [hy, mul_zero, add_zero] at h1
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hφ.le] at h1
    have hk : K * φ ^ 3 ≤ φ * (|K| * Real.pi * φ) := by
      calc K * φ ^ 3 ≤ |K| * φ ^ 3 := mul_le_mul_of_nonneg_right (le_abs_self K) (by positivity)
        _ = φ * (|K| * φ * φ) := by ring
        _ ≤ φ * (|K| * Real.pi * φ) := by gcongr
    exact le_of_mul_le_mul_left (h1.trans hk) hφ
  exact norm_le_zero_iff.mp hle
def cubicPhaseError (c φ : ℝ) : ℂ :=
  Complex.exp (Complex.I * ((c * φ : ℝ) : ℂ)) - 1 - Complex.I * ((c * φ : ℝ) : ℂ) +
    ((c * φ : ℝ) : ℂ) ^ 2 / 2
theorem norm_cubicPhaseError_le (c φ : ℝ) : ‖cubicPhaseError c φ‖ ≤ |c| ^ 3 * |φ| ^ 3 := by
  have h := norm_cexp_I_mul_sub_taylor_le (c * φ)
  rwa [abs_mul, mul_pow] at h
variable [Fintype ι]
theorem trigMatrixSum_eq_weightedWaveSum (c : ι → ℝ) (n : ι → Fin 4 → ℤ)
    (M : ι → Matrix (Fin 4) (Fin 4) ℂ) (φ : ℝ) :
    trigMatrixSum c n M φ =
      weightedWaveSum Finset.univ n M fun k => Complex.exp (Complex.I * ((c k * φ : ℝ) : ℂ)) := by
  funext q
  simp only [trigMatrixSum, weightedWaveSum, planeWaveMatrix, smul_smul]
theorem trigMatrixSum_taylor (c : ι → ℝ) (n : ι → Fin 4 → ℤ)
    (M : ι → Matrix (Fin 4) (Fin 4) ℂ) (φ : ℝ) (q : AmbientSpace) :
    trigMatrixSum c n M φ q = trigMatrixSum c n M 0 q +
      (φ : ℂ) • weightedWaveSum Finset.univ n M (fun k => Complex.I * (c k : ℂ)) q +
      (φ : ℂ) ^ 2 • weightedWaveSum Finset.univ n M (fun k => -(c k : ℂ) ^ 2 / 2) q +
      weightedWaveSum Finset.univ n M (fun k => cubicPhaseError (c k) φ) q := by
  rw [trigMatrixSum_eq_weightedWaveSum, trigMatrixSum_eq_weightedWaveSum]
  simp only [weightedWaveSum, Finset.smul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [smul_smul, ← add_smul]
  congr 1
  have h0 : Complex.exp (Complex.I * ((c k * 0 : ℝ) : ℂ)) = 1 := by simp
  rw [h0]
  simp only [cubicPhaseError]
  generalize Complex.exp (Complex.I * ((c k * φ : ℝ) : ℂ)) = E
  push_cast
  ring
theorem norm_weightedWaveSum_error_entry (c : ι → ℝ) (n : ι → Fin 4 → ℤ)
    (M : ι → Matrix (Fin 4) (Fin 4) ℂ) (φ : ℝ) (q : AmbientSpace) (i j : Fin 4) :
    ‖weightedWaveSum Finset.univ n M (fun k => cubicPhaseError (c k) φ) q i j‖ ≤
      (∑ k, |c k| ^ 3 * ‖planeWaveMatrix (n k) (M k) q i j‖) * |φ| ^ 3 := by
  simp only [weightedWaveSum, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  rw [Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  rw [norm_mul]
  calc ‖cubicPhaseError (c k) φ‖ * ‖planeWaveMatrix (n k) (M k) q i j‖
      ≤ (|c k| ^ 3 * |φ| ^ 3) * ‖planeWaveMatrix (n k) (M k) q i j‖ :=
        mul_le_mul_of_nonneg_right (norm_cubicPhaseError_le (c k) φ) (norm_nonneg _)
    _ = |c k| ^ 3 * ‖planeWaveMatrix (n k) (M k) q i j‖ * |φ| ^ 3 := by ring
theorem taylorTerms_isHermitian (c : ι → ℝ) (n : ι → Fin 4 → ℤ)
    (M : ι → Matrix (Fin 4) (Fin 4) ℂ)
    (hherm : ∀ φ : ℝ, |φ| ≤ Real.pi → ∀ q,
      pointwiseAdjoint (trigMatrixSum c n M φ) q = trigMatrixSum c n M φ q)
    (q : AmbientSpace) :
    (weightedWaveSum Finset.univ n M (fun k => Complex.I * (c k : ℂ)) q).IsHermitian ∧
      (weightedWaveSum Finset.univ n M (fun k => -(c k : ℂ) ^ 2 / 2) q).IsHermitian := by
  have hent : ∀ φ : ℝ, |φ| ≤ Real.pi → ∀ a b,
      trigMatrixSum c n M φ q a b = conj (trigMatrixSum c n M φ q b a) := by
    intro φ hφ a b
    have h := congrArg (fun X : Matrix (Fin 4) (Fin 4) ℂ => X a b) (hherm φ hφ q)
    simpa [pointwiseAdjoint, Matrix.conjTranspose_apply] using h.symm
  have key : ∀ i j,
      weightedWaveSum Finset.univ n M (fun k => Complex.I * (c k : ℂ)) q i j =
        conj (weightedWaveSum Finset.univ n M (fun k => Complex.I * (c k : ℂ)) q j i) ∧
      weightedWaveSum Finset.univ n M (fun k => -(c k : ℂ) ^ 2 / 2) q i j =
        conj (weightedWaveSum Finset.univ n M (fun k => -(c k : ℂ) ^ 2 / 2) q j i) := by
    intro i j
    have hv := eq_zero_of_linear_quadratic_cubic
      (weightedWaveSum Finset.univ n M (fun k => Complex.I * (c k : ℂ)) q i j -
        conj (weightedWaveSum Finset.univ n M (fun k => Complex.I * (c k : ℂ)) q j i))
      (weightedWaveSum Finset.univ n M (fun k => -(c k : ℂ) ^ 2 / 2) q i j -
        conj (weightedWaveSum Finset.univ n M (fun k => -(c k : ℂ) ^ 2 / 2) q j i))
      ((∑ k, |c k| ^ 3 * ‖planeWaveMatrix (n k) (M k) q j i‖) +
        ∑ k, |c k| ^ 3 * ‖planeWaveMatrix (n k) (M k) q i j‖)
      (fun φ hφ => ?_)
    · exact ⟨sub_eq_zero.mp hv.1, sub_eq_zero.mp hv.2⟩
    have h0 := hent 0 (by simp [Real.pi_pos.le]) i j
    have e1 := congrArg (fun X : Matrix (Fin 4) (Fin 4) ℂ => X i j)
      (trigMatrixSum_taylor c n M φ q)
    have e2 := congrArg (fun X : Matrix (Fin 4) (Fin 4) ℂ => conj (X j i))
      (trigMatrixSum_taylor c n M φ q)
    have e3 := hent φ hφ i j
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add, map_mul, map_pow,
      Complex.conj_ofReal] at e1 e2
    have e : (φ : ℂ) * (weightedWaveSum Finset.univ n M (fun k => Complex.I * (c k : ℂ)) q i j -
          conj (weightedWaveSum Finset.univ n M (fun k => Complex.I * (c k : ℂ)) q j i)) +
        (φ : ℂ) ^ 2 * (weightedWaveSum Finset.univ n M (fun k => -(c k : ℂ) ^ 2 / 2) q i j -
          conj (weightedWaveSum Finset.univ n M (fun k => -(c k : ℂ) ^ 2 / 2) q j i)) =
        conj (weightedWaveSum Finset.univ n M (fun k => cubicPhaseError (c k) φ) q j i) -
          weightedWaveSum Finset.univ n M (fun k => cubicPhaseError (c k) φ) q i j := by
      linear_combination e3 + e2 - e1 - h0
    rw [e, add_mul]
    refine (norm_sub_le _ _).trans
      (add_le_add ?_ (norm_weightedWaveSum_error_entry c n M φ q i j))
    rw [Complex.norm_conj]
    exact norm_weightedWaveSum_error_entry c n M φ q j i
  exact ⟨Matrix.IsHermitian.ext fun i j => (key i j).1.symm,
    Matrix.IsHermitian.ext fun i j => (key i j).2.symm⟩
end TrigMatrixSum
open TrigMatrixSum in
theorem trigMatrixSumExpansion_holds (hcoeff : FourierCoeffsOfSymbol)
    (hsymbols : SymbolAlgebra.Claim) : TrigMatrixSumExpansion := by
  intro ι _ c n M
  have htrig : ∀ g : ι → ℂ, IsFiniteFourierSymbol (weightedWaveSum Finset.univ n M g) := by
    intro g
    have hf := weightedWaveSum_props hcoeff hsymbols Finset.univ n M g
    refine ⟨hf.1, (Set.finite_range n).subset fun m hm => ?_⟩
    by_contra hnot
    apply hm
    rw [hf.2.1 m]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [planeWaveCoeff_of_ne _ (fun e => hnot ⟨k, e.symm⟩), smul_zero]
  refine ⟨fun φ => ?_, fun h0 hherm hK => ?_⟩
  · rw [trigMatrixSum_eq_weightedWaveSum]
    exact htrig _
  refine ⟨∑ k, TorusMetric.euclidNormVec (castVec (n k)),
    ∑ k, |c k| ^ 3 * weightedCoeffNorm 3 (planeWaveMatrix (n k) (M k)),
    weightedWaveSum Finset.univ n M (fun k => Complex.I * (c k : ℂ)),
    weightedWaveSum Finset.univ n M (fun k => -(c k : ℂ) ^ 2 / 2),
    fun φ => weightedWaveSum Finset.univ n M (fun k => cubicPhaseError (c k) φ), ?_⟩
  exact
    { linear_isFiniteFourierSymbol := htrig _
      quadratic_isFiniteFourierSymbol := htrig _
      linear_isHermitian := fun q => (taylorTerms_isHermitian c n M hherm q).1
      quadratic_isHermitian := fun q => (taylorTerms_isHermitian c n M hherm q).2
      isFiniteFourierSymbol := fun φ _ => by
        rw [trigMatrixSum_eq_weightedWaveSum]
        exact htrig _
      isHermitian := hherm
      fourierCoeff_eq_zero := fun φ _ m hm => by
        rw [trigMatrixSum_eq_weightedWaveSum,
          (weightedWaveSum_props hcoeff hsymbols Finset.univ n M _).2.1 m]
        refine Finset.sum_eq_zero fun k _ => ?_
        have hne : m ≠ n k := by
          rintro rfl
          have hle : TorusMetric.euclidNormVec (castVec (n k)) ≤
              ∑ k, TorusMetric.euclidNormVec (castVec (n k)) :=
            Finset.single_le_sum (f := fun k => TorusMetric.euclidNormVec (castVec (n k)))
              (fun _ _ => Real.sqrt_nonneg _) (Finset.mem_univ k)
          exact absurd hm (not_lt.mpr hle)
        rw [planeWaveCoeff_of_ne _ hne, smul_zero]
      eq_add := fun φ _ q => (trigMatrixSum_taylor c n M φ q).trans (by rw [h0 q])
      error_isWeylSymbol := fun φ _ =>
        (weightedWaveSum_props hcoeff hsymbols Finset.univ n M _).1
      error_norm_le := fun φ _ => by
        refine (weightedWaveSum_props hcoeff hsymbols Finset.univ n M _).2.2.trans ?_
        rw [Finset.sum_mul]
        refine Finset.sum_le_sum fun k _ => ?_
        have hnn : 0 ≤ weightedCoeffNorm 3 (planeWaveMatrix (n k) (M k)) :=
          ((hsymbols 4 4 4).2.1.2.2.2 _ (planeWaveMatrix_isWeylSymbol (n k) (M k))).1 3 le_rfl
        calc ‖cubicPhaseError (c k) φ‖ * weightedCoeffNorm 3 (planeWaveMatrix (n k) (M k))
            ≤ (|c k| ^ 3 * |φ| ^ 3) * weightedCoeffNorm 3 (planeWaveMatrix (n k) (M k)) :=
              mul_le_mul_of_nonneg_right (norm_cubicPhaseError_le (c k) φ) hnn
          _ = |c k| ^ 3 * weightedCoeffNorm 3 (planeWaveMatrix (n k) (M k)) * |φ| ^ 3 := by ring
      massiveOp_eq := hK }
end ConstantFieldSymbols
end Tower
end
end YangMills.Construction
