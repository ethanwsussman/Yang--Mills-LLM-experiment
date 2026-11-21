import YangMills.Construction.Matrices.SeriesWithSummableMatrixCoefficientsProof
import YangMills.Construction.Towers.CoefficientsOfASymbol
import YangMills.Construction.Towers.TheCoefficientsOfTheExpansionInTheFlux
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open PeriodicOperators (castVec toComplexVec bilinDot)
open InfiniteLattice (AmbientSpace)
namespace Tower.MagneticWeyl.FluxExpansion
variable {N' : ℕ} [NeZero N']
theorem opNormValue_nonneg (X : Matrix (Fin N') (Fin N') ℂ) :
    0 ≤ Matrices.RectangularMatrix.opNormValue X :=
  norm_nonneg _
theorem opNormValue_add_le (X Y : Matrix (Fin N') (Fin N') ℂ) :
    Matrices.RectangularMatrix.opNormValue (X + Y) ≤
      Matrices.RectangularMatrix.opNormValue X + Matrices.RectangularMatrix.opNormValue Y := by
  simp only [Matrices.RectangularMatrix.opNormValue, OneLoopNotation.opNormOf, map_add]
  exact norm_add_le _ _
theorem opNormValue_smul (c : ℂ) (X : Matrix (Fin N') (Fin N') ℂ) :
    Matrices.RectangularMatrix.opNormValue (c • X) = ‖c‖ * Matrices.RectangularMatrix.opNormValue X := by
  simp only [Matrices.RectangularMatrix.opNormValue, OneLoopNotation.opNormOf, map_smul]
  exact norm_smul _ _
theorem norm_entry_le_opNormValue (X : Matrix (Fin N') (Fin N') ℂ) (i k : Fin N') :
    ‖X i k‖ ≤ Matrices.RectangularMatrix.opNormValue X := by
  have h1 : (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin X)
      (EuclideanSpace.single k (1 : ℂ))) i = X i k := by
    simp [Matrix.toLpLin_apply]
  calc ‖X i k‖ = ‖(LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin X)
        (EuclideanSpace.single k (1 : ℂ))) i‖ := by rw [h1]
    _ ≤ ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin X)
        (EuclideanSpace.single k (1 : ℂ))‖ := PiLp.norm_apply_le _ _
    _ ≤ ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin X)‖ *
        ‖EuclideanSpace.single k (1 : ℂ)‖ := ContinuousLinearMap.le_opNorm _ _
    _ = Matrices.RectangularMatrix.opNormValue X := by
        simp [Matrices.RectangularMatrix.opNormValue, OneLoopNotation.opNormOf]
theorem polyWeight_nonneg (n : Fin 4 → ℤ) (j : ℕ) :
    0 ≤ (1 + TorusMetric.euclidNormVec (castVec n)) ^ j :=
  pow_nonneg (add_nonneg zero_le_one (Real.sqrt_nonneg _)) j
theorem isWeylSymbol_add {a b : AmbientSpace → Matrix (Fin N') (Fin N') ℂ} (ha : IsWeylSymbol a)
    (hb : IsWeylSymbol b) : IsWeylSymbol (fun q => a q + b q) := by
  obtain ⟨c, hc, hc'⟩ := ha
  obtain ⟨d, hd, hd'⟩ := hb
  refine ⟨fun n => c n + d n, fun q => ?_, fun j hj => ?_⟩
  · simpa only [smul_add] using (hc q).add (hd q)
  · refine Summable.of_nonneg_of_le
      (fun n => mul_nonneg (opNormValue_nonneg _) (polyWeight_nonneg n j)) (fun n => ?_)
      ((hc' j hj).add (hd' j hj))
    rw [← add_mul]
    exact mul_le_mul_of_nonneg_right (opNormValue_add_le _ _) (polyWeight_nonneg n j)
theorem isWeylSymbol_smul (k : ℂ) {a : AmbientSpace → Matrix (Fin N') (Fin N') ℂ}
    (ha : IsWeylSymbol a) : IsWeylSymbol (fun q => k • a q) := by
  obtain ⟨c, hc, hc'⟩ := ha
  refine ⟨fun n => k • c n, fun q => ?_, fun j hj => ?_⟩
  · have h := (hc q).const_smul k
    simp only [smul_comm k] at h
    exact h
  · simp only [opNormValue_smul, mul_assoc]
    exact (hc' j hj).mul_left _
theorem fourierCoeff_add (h : FourierCoeffsOfSymbol)
    {a b : AmbientSpace → Matrix (Fin N') (Fin N') ℂ} (ha : IsWeylSymbol a) (hb : IsWeylSymbol b)
    (n : Fin 4 → ℤ) :
    fourierCoeff (fun q => a q + b q) n = fourierCoeff a n + fourierCoeff b n := by
  obtain ⟨ha1, ha2, -⟩ := (h N' N' a).1 ((h N' N' a).2 ha).1
  obtain ⟨hb1, hb2, -⟩ := (h N' N' b).1 ((h N' N' b).2 hb).1
  have Hs := h N' N' (fun q => a q + b q)
  have key := (Hs.1 (Hs.2 (isWeylSymbol_add ha hb)).1).2.2
    (fun n => fourierCoeff a n + fourierCoeff b n)
    (fun q => by simpa only [smul_add] using (ha1 q).add (hb1 q))
    (Summable.of_nonneg_of_le (fun _ => opNormValue_nonneg _) (fun _ => opNormValue_add_le _ _)
      (ha2.add hb2))
  exact (congrFun key n).symm
theorem fourierCoeff_smul (h : FourierCoeffsOfSymbol) (k : ℂ)
    {a : AmbientSpace → Matrix (Fin N') (Fin N') ℂ} (ha : IsWeylSymbol a) (n : Fin 4 → ℤ) :
    fourierCoeff (fun q => k • a q) n = k • fourierCoeff a n := by
  obtain ⟨ha1, ha2, -⟩ := (h N' N' a).1 ((h N' N' a).2 ha).1
  have Hs := h N' N' (fun q => k • a q)
  have key := (Hs.1 (Hs.2 (isWeylSymbol_smul k ha)).1).2.2 (fun n => k • fourierCoeff a n)
    (fun q => by
      have h' := (ha1 q).const_smul k
      simp only [smul_comm k] at h'
      exact h')
    (by simp only [opNormValue_smul]; exact ha2.mul_left _)
  exact (congrFun key n).symm
theorem opNormValue_fourierCoeff_le (h : FourierCoeffsOfSymbol)
    {a : AmbientSpace → Matrix (Fin N') (Fin N') ℂ} (ha : IsWeylSymbol a) (n : Fin 4 → ℤ) :
    Matrices.RectangularMatrix.opNormValue (fourierCoeff a n) ≤ weightedCoeffNorm 3 a := by
  have hsum := ((h N' N' a).2 ha).2 3 le_rfl
  calc Matrices.RectangularMatrix.opNormValue (fourierCoeff a n)
      ≤ Matrices.RectangularMatrix.opNormValue (fourierCoeff a n) *
        (1 + TorusMetric.euclidNormVec (castVec n)) ^ 3 :=
        le_mul_of_one_le_right (opNormValue_nonneg _)
          (one_le_pow₀ (le_add_of_nonneg_right (Real.sqrt_nonneg _)))
    _ ≤ weightedCoeffNorm 3 a :=
        hsum.le_tsum n fun m _ => mul_nonneg (opNormValue_nonneg _) (polyWeight_nonneg m 3)
theorem eq_zero_of_le_const_mul {a C r : ℝ} (ha : 0 ≤ a) (hr : 0 < r)
    (h : ∀ t, 0 < t → t ≤ r → a ≤ C * t) : a = 0 := by
  by_contra hne
  have ha' : 0 < a := lt_of_le_of_ne ha (Ne.symm hne)
  have hC : 0 < C := by
    have h1 := h r hr le_rfl
    by_contra hc
    have hc := not_lt.mp hc
    nlinarith
  have ht : 0 < min r (a / (2 * C)) := lt_min hr (by positivity)
  have h1 := h _ ht (min_le_left _ _)
  have h2 : C * min r (a / (2 * C)) ≤ C * (a / (2 * C)) :=
    mul_le_mul_of_nonneg_left (min_le_right _ _) hC.le
  have h3 : C * (a / (2 * C)) = a / 2 := by field_simp
  linarith
theorem eq_zero_of_cubic_bound {x y : ℂ} {C r : ℝ} (hr : 0 < r)
    (h : ∀ φ : ℝ, |φ| ≤ r → ‖(φ : ℂ) * x + (φ : ℂ) ^ 2 * y‖ ≤ C * |φ| ^ 3) : x = 0 ∧ y = 0 := by
  have hC : 0 ≤ C := by
    have h1 := h r (by rw [abs_of_pos hr])
    rw [abs_of_pos hr] at h1
    have h2 := (norm_nonneg _).trans h1
    by_contra hc
    have hc := not_le.mp hc
    have := mul_neg_of_neg_of_pos hc (pow_pos hr 3)
    linarith
  have both : ∀ t : ℝ, 0 < t → t ≤ r →
      2 * t ^ 2 * ‖y‖ ≤ 2 * (C * t ^ 3) ∧ 2 * t * ‖x‖ ≤ 2 * (C * t ^ 3) := by
    intro t ht htr
    have h1 := h t (by rwa [abs_of_pos ht])
    have h2 := h (-t) (by rwa [abs_neg, abs_of_pos ht])
    rw [abs_of_pos ht] at h1
    rw [abs_neg, abs_of_pos ht] at h2
    constructor
    · have e : (2 * (t : ℂ) ^ 2) * y = ((t : ℂ) * x + (t : ℂ) ^ 2 * y) +
          (((-t : ℝ) : ℂ) * x + ((-t : ℝ) : ℂ) ^ 2 * y) := by push_cast; ring
      have hn : ‖(2 * (t : ℂ) ^ 2) * y‖ = 2 * t ^ 2 * ‖y‖ := by simp
      have h3 := norm_add_le ((t : ℂ) * x + (t : ℂ) ^ 2 * y)
        (((-t : ℝ) : ℂ) * x + ((-t : ℝ) : ℂ) ^ 2 * y)
      rw [← e, hn] at h3
      linarith
    · have e : (2 * (t : ℂ)) * x = ((t : ℂ) * x + (t : ℂ) ^ 2 * y) -
          (((-t : ℝ) : ℂ) * x + ((-t : ℝ) : ℂ) ^ 2 * y) := by push_cast; ring
      have hn : ‖(2 * (t : ℂ)) * x‖ = 2 * t * ‖x‖ := by
        simp [abs_of_pos ht]
      have h3 := norm_sub_le ((t : ℂ) * x + (t : ℂ) ^ 2 * y)
        (((-t : ℝ) : ℂ) * x + ((-t : ℝ) : ℂ) ^ 2 * y)
      rw [← e, hn] at h3
      linarith
  have hy : ‖y‖ = 0 := eq_zero_of_le_const_mul (norm_nonneg _) hr (C := C) fun t ht htr => by
    have h1 := (both t ht htr).1
    have h2 : t ^ 2 * ‖y‖ ≤ t ^ 2 * (C * t) := by nlinarith
    exact le_of_mul_le_mul_left h2 (by positivity)
  have hx : ‖x‖ = 0 := eq_zero_of_le_const_mul (norm_nonneg _) hr (C := C * r) fun t ht htr => by
    have h1 := (both t ht htr).2
    have h2 : t * ‖x‖ ≤ t * (C * t ^ 2) := by nlinarith
    have h3 : ‖x‖ ≤ C * t ^ 2 := le_of_mul_le_mul_left h2 ht
    have h4 : C * t ^ 2 ≤ C * r * t := by
      have : t ^ 2 ≤ r * t := by nlinarith
      nlinarith
    linarith
  exact ⟨norm_eq_zero.mp hx, norm_eq_zero.mp hy⟩
theorem finite_euclidBall (D : ℝ) :
    {n : Fin 4 → ℤ | TorusMetric.euclidNormVec (castVec n) ≤ D}.Finite := by
  refine (Set.finite_Icc (fun _ : Fin 4 => -⌈|D|⌉) (fun _ => ⌈|D|⌉)).subset fun n hn => ?_
  have hb : ∀ μ, |(n μ : ℝ)| ≤ |D| := fun μ => by
    have h1 : |(n μ : ℝ)| ≤ TorusMetric.euclidNormVec (castVec n) := by
      refine Real.abs_le_sqrt ?_
      exact Finset.single_le_sum (f := fun ν => castVec n ν ^ 2)
        (fun ν _ => sq_nonneg _) (Finset.mem_univ μ)
    exact h1.trans ((show TorusMetric.euclidNormVec (castVec n) ≤ D from hn).trans (le_abs_self D))
  have hc : ∀ μ, |n μ| ≤ ⌈|D|⌉ := fun μ => by
    have h2 : ((|n μ| : ℤ) : ℝ) ≤ (⌈|D|⌉ : ℝ) := by
      rw [Int.cast_abs]
      exact (hb μ).trans (Int.le_ceil _)
    exact_mod_cast h2
  exact ⟨fun μ => (abs_le.mp (hc μ)).1, fun μ => (abs_le.mp (hc μ)).2⟩
theorem continuous_fourierChar (n : Fin 4 → ℤ) : Continuous (fourierChar n) := by apply _root_.YangMills.Construction.Matrices.FourierMatrixSeries.continuous_character <;> assumption
theorem continuous_of_isFiniteFourierSymbol (h : FourierCoeffsOfSymbol)
    {a : AmbientSpace → Matrix (Fin N') (Fin N') ℂ} (ha : IsFiniteFourierSymbol a) :
    Continuous a := by
  have h1 := ((h N' N' a).1 ((h N' N' a).2 ha.1).1).1
  have e : a = fun q => ∑ n ∈ ha.2.toFinset, fourierChar n q • fourierCoeff a n := by
    funext q
    refine (h1 q).unique (hasSum_sum_of_ne_finset_zero fun n hn => ?_)
    have : fourierCoeff a n = 0 := by
      by_contra hne
      exact hn (ha.2.mem_toFinset.mpr hne)
    rw [this, smul_zero]
  rw [e]
  exact continuous_finsetSum _ fun n _ => (continuous_fourierChar n).smul continuous_const
theorem fluxCoefficientsAreTrigPolys_holds (h : FourierCoeffsOfSymbol) :
    FluxCoefficientsAreTrigPolys := by
  intro N' _ D C r σ₁ σ₂ σ σr hr hyp
  have h0 : |(0 : ℝ)| ≤ r := by simpa using hr.le
  obtain ⟨hσ0, hD0, he0, hs0, hb0⟩ := hyp 0 h0
  obtain ⟨S, hSdef⟩ : ∃ S : ℝ → AmbientSpace → Matrix (Fin N') (Fin N') ℂ, ∀ φ,
      S φ = fun q => σ φ q + (-1 : ℂ) • σ 0 q + (-1 : ℂ) • σr φ q + σr 0 q :=
    ⟨_, fun _ => rfl⟩
  have part1 : ∀ φ, |φ| ≤ r → IsWeylSymbol (fun q => σ φ q + (-1 : ℂ) • σ 0 q) := fun φ hφ =>
    isWeylSymbol_add (hyp φ hφ).1.1 (isWeylSymbol_smul _ hσ0.1)
  have part2 : ∀ φ, |φ| ≤ r → IsWeylSymbol (fun q => (-1 : ℂ) • σr φ q) := fun φ hφ =>
    isWeylSymbol_smul _ (hyp φ hφ).2.2.2.1
  have part3 : ∀ φ, |φ| ≤ r →
      IsWeylSymbol (fun q => σ φ q + (-1 : ℂ) • σ 0 q + (-1 : ℂ) • σr φ q) := fun φ hφ =>
    isWeylSymbol_add (part1 φ hφ) (part2 φ hφ)
  have hS : ∀ φ, |φ| ≤ r → IsWeylSymbol (S φ) := fun φ hφ => by
    rw [hSdef φ]
    exact isWeylSymbol_add (part3 φ hφ) hs0
  have hSe : ∀ φ, |φ| ≤ r → ∀ q, S φ q = (φ : ℂ) • σ₁ q + (φ : ℂ) ^ 2 • σ₂ q := by
    intro φ hφ q
    have e1 := (hyp φ hφ).2.2.1 q
    have e0 := he0 q
    simp only [Complex.ofReal_zero, zero_smul, add_zero, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow] at e0
    rw [hSdef φ]
    simp only []
    rw [e1, e0]
    module
  have hrr : |r| ≤ r := by rw [abs_of_pos hr]
  have hnr : |-r| ≤ r := by rwa [abs_neg]
  have hrc : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  have hA : σ₁ = fun q => (1 / (2 * (r : ℂ))) • (S r q + (-1 : ℂ) • S (-r) q) := by
    funext q
    rw [hSe r hrr, hSe (-r) hnr, Complex.ofReal_neg]
    match_scalars <;> field_simp <;> ring
  have hB : σ₂ = fun q => (1 / (2 * (r : ℂ) ^ 2)) • (S r q + S (-r) q) := by
    funext q
    rw [hSe r hrr, hSe (-r) hnr, Complex.ofReal_neg]
    match_scalars <;> field_simp <;> ring
  have hA' : IsWeylSymbol σ₁ := by
    rw [hA]
    exact isWeylSymbol_smul _ (isWeylSymbol_add (hS r hrr) (isWeylSymbol_smul _ (hS (-r) hnr)))
  have hB' : IsWeylSymbol σ₂ := by
    rw [hB]
    exact isWeylSymbol_smul _ (isWeylSymbol_add (hS r hrr) (hS (-r) hnr))
  have hvan : ∀ n : Fin 4 → ℤ, D < TorusMetric.euclidNormVec (castVec n) →
      fourierCoeff σ₁ n = 0 ∧ fourierCoeff σ₂ n = 0 := by
    intro n hn
    have key : ∀ i k, fourierCoeff σ₁ n i k = 0 ∧ fourierCoeff σ₂ n i k = 0 := by
      intro i k
      refine eq_zero_of_cubic_bound (C := C) hr fun φ hφ => ?_
      obtain ⟨hσ, hDφ, heφ, hsφ, hbφ⟩ := hyp φ hφ
      have c1 : fourierCoeff (S φ) n =
          (φ : ℂ) • fourierCoeff σ₁ n + (φ : ℂ) ^ 2 • fourierCoeff σ₂ n := by
        have e : S φ = fun q => (φ : ℂ) • σ₁ q + (φ : ℂ) ^ 2 • σ₂ q := funext (hSe φ hφ)
        rw [e, fourierCoeff_add h (isWeylSymbol_smul _ hA') (isWeylSymbol_smul _ hB'),
          fourierCoeff_smul h _ hA', fourierCoeff_smul h _ hB']
      have c2 : fourierCoeff (S φ) n =
          (-1 : ℂ) • fourierCoeff (σr φ) n + fourierCoeff (σr 0) n := by
        rw [hSdef φ, fourierCoeff_add h (part3 φ hφ) hs0,
          fourierCoeff_add h (part1 φ hφ) (part2 φ hφ),
          fourierCoeff_add h hσ.1 (isWeylSymbol_smul _ hσ0.1), fourierCoeff_smul h _ hσ0.1,
          fourierCoeff_smul h _ hsφ, hDφ n hn, hD0 n hn]
        simp
      have e : (φ : ℂ) * fourierCoeff σ₁ n i k + (φ : ℂ) ^ 2 * fourierCoeff σ₂ n i k =
          -fourierCoeff (σr φ) n i k + fourierCoeff (σr 0) n i k := by
        have := congrFun (congrFun (c1.symm.trans c2) i) k
        simpa [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] using this
      have z : fourierCoeff (σr 0) n i k = 0 := by
        have h1 := (norm_entry_le_opNormValue (fourierCoeff (σr 0) n) i k).trans
          ((opNormValue_fourierCoeff_le h hs0 n).trans hb0)
        simp only [abs_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
          mul_zero] at h1
        exact norm_le_zero_iff.mp h1
      rw [e, z, add_zero, norm_neg]
      exact (norm_entry_le_opNormValue _ i k).trans ((opNormValue_fourierCoeff_le h hsφ n).trans hbφ)
    exact ⟨Matrix.ext fun i k => (key i k).1, Matrix.ext fun i k => (key i k).2⟩
  have t1 : IsFiniteFourierSymbol σ₁ := ⟨hA', (finite_euclidBall D).subset fun n hn => by
    by_contra hlt
    exact hn (hvan n (not_le.mp hlt)).1⟩
  have t2 : IsFiniteFourierSymbol σ₂ := ⟨hB', (finite_euclidBall D).subset fun n hn => by
    by_contra hlt
    exact hn (hvan n (not_le.mp hlt)).2⟩
  exact ⟨t1, t2, continuous_of_isFiniteFourierSymbol h t1,
    continuous_of_isFiniteFourierSymbol h t2⟩
end Tower.MagneticWeyl.FluxExpansion
end YangMills.Construction
end
