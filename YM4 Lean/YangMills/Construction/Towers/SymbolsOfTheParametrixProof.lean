import YangMills.Construction.Towers.HolomorphicSymbolsAndTheCalculusAtFluxZeroProof
import YangMills.Construction.Towers.SymbolsOfTheParametrix
import Mathlib
set_option autoImplicit false
open YangMills.Construction.PeriodicOperators (imStrip toComplexVec castVec matrixCoeffs
  BoundedOnEntrywise bilinDot)
open YangMills.Construction.InfiniteLattice (AmbientSpace)
noncomputable section
namespace YangMills.Construction.Tower.MagneticWeyl
namespace ApproxInverseSymbols
open FluxExpansion FluxZeroCalculus
def IsLowFrequencySum {N' : ℕ} (a : AmbientSpace → Matrix (Fin N') (Fin N') ℂ) : Prop :=
  ∃ c : (Fin 4 → ℤ) →₀ Matrix (Fin N') (Fin N') ℂ,
    (∀ n ∈ c.support, TorusMetric.euclidNormVec (castVec n) ≤ 1) ∧
      ∀ q, a q = c.sum fun n M => fourierChar n q • M
variable {N' : ℕ}
theorem isLowFrequencySum_single {n : Fin 4 → ℤ} (hn : TorusMetric.euclidNormVec (castVec n) ≤ 1)
    (M : Matrix (Fin N') (Fin N') ℂ) : IsLowFrequencySum fun q => fourierChar n q • M := by
  refine ⟨Finsupp.single n M, fun m hm => ?_, fun q => ?_⟩
  · rw [Finset.mem_singleton.mp (Finsupp.support_single_subset hm)]
    exact hn
  · change fourierChar n q • M = _
    rw [Finsupp.sum_single_index (by simp)]
theorem isLowFrequencySum_add {a b : AmbientSpace → Matrix (Fin N') (Fin N') ℂ}
    (ha : IsLowFrequencySum a) (hb : IsLowFrequencySum b) :
    IsLowFrequencySum fun q => a q + b q := by
  classical
  obtain ⟨c, hc, hac⟩ := ha
  obtain ⟨c', hc', hbc⟩ := hb
  refine ⟨c + c', fun n hn => ?_, fun q => ?_⟩
  · rcases Finset.mem_union.mp (Finsupp.support_add hn) with h | h
    · exact hc n h
    · exact hc' n h
  · change a q + b q = _
    rw [hac, hbc, Finsupp.sum_add_index' (fun _ => by simp) (fun _ _ _ => by simp [smul_add])]
theorem isLowFrequencySum_sum {ι : Type} (s : Finset ι)
    (f : ι → AmbientSpace → Matrix (Fin N') (Fin N') ℂ)
    (hf : ∀ i, IsLowFrequencySum (f i)) : IsLowFrequencySum fun q => ∑ i ∈ s, f i q := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp, by simp⟩
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact isLowFrequencySum_add (hf i) ih
def axisIndex (μ : Fin 4) (k : ℤ) : Fin 4 → ℤ := Pi.single μ k
theorem fourierChar_axisIndex (μ : Fin 4) (k : ℤ) (q : AmbientSpace) :
    fourierChar (axisIndex μ k) q = Complex.exp ((k : ℂ) * (q μ : ℂ) * Complex.I) := by
  have h : intDot (axisIndex μ k) q = (k : ℂ) * (q μ : ℂ) := by
    simp only [intDot, bilinDot, toComplexVec, castVec, axisIndex]
    rw [Finset.sum_eq_single μ]
    · simp
    · intro ν _ hν
      simp [Pi.single_eq_of_ne hν]
    · simp
  rw [fourierChar, h, mul_comm]
theorem euclidNormVec_axisIndex_le (μ : Fin 4) {k : ℤ} (hk : (k : ℝ) ^ 2 ≤ 1) :
    TorusMetric.euclidNormVec (castVec (axisIndex μ k)) ≤ 1 := by
  refine Real.sqrt_le_one.mpr ?_
  rw [Finset.sum_eq_single μ]
  · simpa [castVec, axisIndex] using hk
  · intro ν _ hν
    simp [castVec, axisIndex, Pi.single_eq_of_ne hν]
  · simp
theorem isLowFrequencySum_axisWave (μ : Fin 4) (α β γ : ℂ) :
    IsLowFrequencySum (N' := N') fun q =>
      (α + β * Complex.exp ((q μ : ℂ) * Complex.I) +
        γ * Complex.exp (-(q μ : ℂ) * Complex.I)) • (1 : Matrix (Fin N') (Fin N') ℂ) := by
  have h0 := isLowFrequencySum_single (N' := N') (n := axisIndex μ 0)
    (euclidNormVec_axisIndex_le μ (by norm_num)) (α • 1)
  have h1 := isLowFrequencySum_single (N' := N') (n := axisIndex μ 1)
    (euclidNormVec_axisIndex_le μ (by norm_num)) (β • 1)
  have h2 := isLowFrequencySum_single (N' := N') (n := axisIndex μ (-1))
    (euclidNormVec_axisIndex_le μ (by norm_num)) (γ • 1)
  have h := isLowFrequencySum_add (isLowFrequencySum_add h0 h1) h2
  convert h using 2 with q
  rw [fourierChar_axisIndex, fourierChar_axisIndex, fourierChar_axisIndex]
  simp only [Int.cast_zero, Int.cast_one, Int.cast_neg, zero_mul, Complex.exp_zero, one_mul,
    neg_mul, smul_smul, add_smul]
  rw [mul_comm (Complex.exp _) β, mul_comm (Complex.exp _) γ]
theorem isLowFrequencySum_baseSymbolMatrix : IsLowFrequencySum (baseSymbolMatrix N') := by
  have h := isLowFrequencySum_sum (N' := N') Finset.univ _ fun μ : Fin 4 =>
    isLowFrequencySum_axisWave μ 2 (-1) (-1)
  convert h using 2 with q
  rw [baseSymbolMatrix, ← Finset.sum_smul]
  congr 1
  simp only [baseSymbol, Massive.latticeSymbol, Massive.axisSymbol, toComplexVec]
  refine Finset.sum_congr rfl fun μ _ => ?_
  linear_combination -Complex.two_cos (q μ : ℂ)
theorem isLowFrequencySum_baseSymbolDeriv (μ : Fin 4) :
    IsLowFrequencySum (N' := N') fun q =>
      baseSymbolDeriv μ q • (1 : Matrix (Fin N') (Fin N') ℂ) := by
  have h := isLowFrequencySum_axisWave (N' := N') μ 0 (-Complex.I) Complex.I
  convert h using 2 with q
  congr 1
  rw [baseSymbolDeriv]
  linear_combination Complex.two_sin (q μ : ℂ)
theorem isLowFrequencySum_baseSymbolSecondDeriv (μ : Fin 4) :
    IsLowFrequencySum (N' := N') fun q =>
      baseSymbolSecondDeriv μ q • (1 : Matrix (Fin N') (Fin N') ℂ) := by
  have h := isLowFrequencySum_axisWave (N' := N') μ 0 1 1
  convert h using 2 with q
  congr 1
  rw [baseSymbolSecondDeriv]
  linear_combination Complex.two_cos (q μ : ℂ)
variable [NeZero N']
theorem isFiniteFourierSymbol_of_isLowFrequencySum (hD : FluxZeroCalculus.Claim)
    {a : AmbientSpace → Matrix (Fin N') (Fin N') ℂ} (ha : IsLowFrequencySum a) :
    IsFiniteFourierSymbol a := by
  obtain ⟨c, -, hc⟩ := ha
  have h := ((hD 0 N' N' N').2.2.2.2.1 c.support c).1
  have e : a = fun q => ∑ n ∈ c.support, fourierChar n q • c n := funext hc
  rw [e]
  exact h
theorem fourierCoeff_eq_zero_of_one_lt (hC : FourierCoeffsOfSymbol)
    {a : AmbientSpace → Matrix (Fin N') (Fin N') ℂ} (ha : IsLowFrequencySum a) (n : Fin 4 → ℤ)
    (hn : 1 < TorusMetric.euclidNormVec (castVec n)) : fourierCoeff a n = 0 := by
  obtain ⟨c, hs, hc⟩ := ha
  have hsum : HasFourierExpansion (⇑c) a := fun q => by
    rw [hc q]
    refine hasSum_sum_of_ne_finset_zero fun m hm => ?_
    rw [Finsupp.notMem_support_iff.mp hm, smul_zero]
  have hsm : Summable fun m => Matrices.RectangularMatrix.opNormValue (c m) :=
    summable_of_ne_finset_zero (s := c.support) fun m hm => by
      rw [Finsupp.notMem_support_iff.mp hm]
      simp [Matrices.RectangularMatrix.opNormValue, OneLoopNotation.opNormOf]
  have h := ((hC N' N' a).1 ⟨c, hsum, hsm⟩).2.2 c hsum hsm
  rw [← h]
  by_contra hne
  exact absurd (hs n (Finsupp.mem_support_iff.mpr hne)) (not_le.mpr hn)
omit [NeZero N'] in
theorem exists_strip_width {z : ℝ} (hz : 0 < z) :
    ∃ υ : ℝ, 0 < υ ∧ 8 * (Real.cosh υ - 1) ≤ z / 2 := by
  have hcont : Continuous fun t : ℝ => 8 * (Real.cosh t - 1) :=
    continuous_const.mul (Real.continuous_cosh.sub continuous_const)
  have h0 : ∀ᶠ t in nhds (0 : ℝ), 8 * (Real.cosh t - 1) < z / 2 :=
    (hcont.tendsto 0).eventually (gt_mem_nhds (by simpa using half_pos hz))
  obtain ⟨ε, hε, h⟩ := Metric.eventually_nhds_iff.mp h0
  refine ⟨ε / 2, half_pos hε, (h ?_).le⟩
  rw [Real.dist_eq, sub_zero, abs_of_pos (half_pos hε)]
  exact half_lt_self hε
omit [NeZero N'] in
theorem re_cos_eq (w : ℂ) : (Complex.cos w).re = Real.cos w.re * Real.cosh w.im := by
  rw [Complex.cos_eq]
  simp [← Complex.ofReal_cos, ← Complex.ofReal_cosh, ← Complex.ofReal_sin, ← Complex.ofReal_sinh]
omit [NeZero N'] in
theorem neg_le_re_latticeSymbol {υ : ℝ} {κ : Fin 4 → ℂ} (hκ : κ ∈ imStrip υ) :
    -(8 * (Real.cosh υ - 1)) ≤ (Massive.latticeSymbol κ).re := by
  have h : ∀ μ, -(2 * (Real.cosh υ - 1)) ≤ (Massive.axisSymbol μ κ).re := by
    intro μ
    have hy : Real.cosh (κ μ).im ≤ Real.cosh υ :=
      Real.cosh_le_cosh.mpr ((hκ μ).trans (le_abs_self υ))
    have hc : Real.cos (κ μ).re * Real.cosh (κ μ).im ≤ Real.cosh (κ μ).im :=
      mul_le_of_le_one_left (Real.cosh_pos _).le (Real.cos_le_one _)
    simp only [Massive.axisSymbol, Complex.sub_re, Complex.mul_re, Complex.re_ofNat,
      Complex.im_ofNat, zero_mul, sub_zero, re_cos_eq]
    linarith
  have hsum : ∑ _μ : Fin 4, -(2 * (Real.cosh υ - 1)) ≤
      ∑ μ, (Massive.axisSymbol μ κ).re :=
    Finset.sum_le_sum fun μ _ => h μ
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  rw [Massive.latticeSymbol, Complex.re_sum]
  push_cast at hsum
  linarith
omit [NeZero N'] in
theorem latticeSymbol_add_period (κ : Fin 4 → ℂ) {p : AmbientSpace}
    (hp : p ∈ InfiniteLattice.latticeSubgroup (2 * Real.pi)) :
    Massive.latticeSymbol (κ + toComplexVec p) = Massive.latticeSymbol κ := by
  obtain ⟨m, hm⟩ := hp
  refine Finset.sum_congr rfl fun μ _ => ?_
  have h : (κ + toComplexVec p) μ = κ μ + (m μ : ℂ) * (2 * (Real.pi : ℂ)) := by
    simp [toComplexVec, hm μ]
  rw [Massive.axisSymbol, Massive.axisSymbol, h, Complex.cos_add_int_mul_two_pi]
omit [NeZero N'] in
theorem differentiable_latticeSymbol : Differentiable ℂ Massive.latticeSymbol := by
  unfold Massive.latticeSymbol Massive.axisSymbol
  fun_prop
theorem isHolomorphicIn_of_differentiableOn {O : Set (Coordinates.ComplexCoordinates 4)}
    (ho : IsOpen O) {f : (Fin 4 → ℂ) → ℂ} (hf : DifferentiableOn ℂ f O) :
    Coordinates.ComplexCoordinates.IsHolomorphicIn (N' := 1) O fun x _ => f x := by apply _root_.YangMills.Construction.Tower.MagneticWeyl.FluxZeroCalculus.isHolomorphicIn_of_differentiableOn <;> assumption
def resolventExtension (N' : ℕ) (s : ℝ) (κ : Fin 4 → ℂ) : Matrix (Fin N') (Fin N') ℂ :=
  (Massive.latticeSymbol κ + (s : ℂ))⁻¹ • (1 : Matrix (Fin N') (Fin N') ℂ)
omit [NeZero N'] in
theorem realRestrict_resolventExtension (s : ℝ) :
    FluxZeroCalculus.realRestrict (resolventExtension N' s) = termZero N' s := rfl
omit [NeZero N'] in
theorem isLatticePeriodicOnStrip_resolventExtension (υ s : ℝ) :
    IsLatticePeriodicOnStrip υ (resolventExtension N' s) := by
  intro κ _ p hp
  rw [resolventExtension, resolventExtension, latticeSymbol_add_period κ hp]
omit [NeZero N'] in
theorem isAnalyticNearStrip_resolventExtension {υ s z : ℝ} (hz : 0 < z) (hzs : z ≤ s)
    (hυ : 8 * (Real.cosh υ - 1) ≤ z / 2) :
    IsAnalyticNearStrip υ (resolventExtension N' s) := by
  have hcont : Continuous fun κ : Fin 4 → ℂ => (Massive.latticeSymbol κ + (s : ℂ)).re :=
    Complex.continuous_re.comp (differentiable_latticeSymbol.continuous.add continuous_const)
  have hO : IsOpen {κ : Fin 4 → ℂ | 0 < (Massive.latticeSymbol κ + (s : ℂ)).re} :=
    isOpen_lt continuous_const hcont
  refine ⟨_, fun κ hκ => ?_, by norm_num, hO, fun e => ?_⟩
  · have h := neg_le_re_latticeSymbol hκ
    change 0 < (Massive.latticeSymbol κ + (s : ℂ)).re
    simp only [Complex.add_re, Complex.ofReal_re]
    linarith
  · have hw : DifferentiableOn ℂ (fun κ => Massive.latticeSymbol κ + (s : ℂ))
        {κ : Fin 4 → ℂ | 0 < (Massive.latticeSymbol κ + (s : ℂ)).re} :=
      (differentiable_latticeSymbol.add_const _).differentiableOn
    have hne : ∀ κ ∈ {κ : Fin 4 → ℂ | 0 < (Massive.latticeSymbol κ + (s : ℂ)).re},
        Massive.latticeSymbol κ + (s : ℂ) ≠ 0 := fun κ hκ h0 => by
      have hκ' : 0 < (Massive.latticeSymbol κ + (s : ℂ)).re := hκ
      rw [h0] at hκ'
      simp at hκ'
    have hf := (hw.inv hne).mul_const ((1 : Matrix (Fin N') (Fin N') ℂ) e.1 e.2)
    have he : (fun κ => matrixCoeffs (resolventExtension N' s κ) e) =
        fun κ => (Massive.latticeSymbol κ + (s : ℂ))⁻¹ *
          (1 : Matrix (Fin N') (Fin N') ℂ) e.1 e.2 := by
      funext κ
      simp [matrixCoeffs, resolventExtension, Matrix.smul_apply]
    have := isHolomorphicIn_of_differentiableOn hO (f := fun κ =>
      matrixCoeffs (resolventExtension N' s κ) e) (by rw [he]; exact hf)
    exact this
omit [NeZero N'] in
theorem norm_inv_latticeSymbol_add_le {υ s z : ℝ} (hz : 0 < z) (hzs : z ≤ s)
    (hυ : 8 * (Real.cosh υ - 1) ≤ z / 2) {κ : Fin 4 → ℂ} (hκ : κ ∈ imStrip υ) :
    ‖(Massive.latticeSymbol κ + (s : ℂ))⁻¹‖ ≤ 2 / s := by
  have h := neg_le_re_latticeSymbol hκ
  have hs : 0 < s := hz.trans_le hzs
  have hre : s / 2 ≤ (Massive.latticeSymbol κ + (s : ℂ)).re := by
    simp only [Complex.add_re, Complex.ofReal_re]
    linarith
  have hn : s / 2 ≤ ‖Massive.latticeSymbol κ + (s : ℂ)‖ := hre.trans (Complex.re_le_norm _)
  rw [norm_inv, show 2 / s = (s / 2)⁻¹ by rw [inv_div]]
  exact inv_anti₀ (half_pos hs) hn
theorem opNormValue_one_le :
    Matrices.RectangularMatrix.opNormValue (1 : Matrix (Fin N') (Fin N') ℂ) ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => ?_
  change ‖Matrix.toEuclideanLin (1 : Matrix (Fin N') (Fin N') ℂ) v‖ ≤ 1 * ‖v‖
  simp
theorem opNormValue_resolventExtension_le {υ s z : ℝ} (hz : 0 < z) (hzs : z ≤ s)
    (hυ : 8 * (Real.cosh υ - 1) ≤ z / 2) {κ : Fin 4 → ℂ} (hκ : κ ∈ imStrip υ) :
    Matrices.RectangularMatrix.opNormValue (resolventExtension N' s κ) ≤ 2 / s := by
  have hsm : Matrices.RectangularMatrix.opNormValue (resolventExtension N' s κ) =
      ‖(Massive.latticeSymbol κ + (s : ℂ))⁻¹‖ *
        Matrices.RectangularMatrix.opNormValue (1 : Matrix (Fin N') (Fin N') ℂ) := by
    change ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin
        ((Massive.latticeSymbol κ + (s : ℂ))⁻¹ • (1 : Matrix (Fin N') (Fin N') ℂ)))‖ =
      ‖(Massive.latticeSymbol κ + (s : ℂ))⁻¹‖ * ‖LinearMap.toContinuousLinearMap
        (Matrix.toEuclideanLin (1 : Matrix (Fin N') (Fin N') ℂ))‖
    rw [map_smul, map_smul, norm_smul]
  rw [hsm]
  calc _ ≤ ‖(Massive.latticeSymbol κ + (s : ℂ))⁻¹‖ * 1 :=
        mul_le_mul_of_nonneg_left opNormValue_one_le (norm_nonneg _)
    _ ≤ 2 / s := by rw [mul_one]; exact norm_inv_latticeSymbol_add_le hz hzs hυ hκ
omit [NeZero N'] in
theorem boundedOnEntrywise_resolventExtension {υ s z : ℝ} (hz : 0 < z) (hzs : z ≤ s)
    (hυ : 8 * (Real.cosh υ - 1) ≤ z / 2) :
    BoundedOnEntrywise matrixCoeffs (imStrip υ) (resolventExtension N' s) := by
  intro e
  refine ⟨2 / s, fun κ hκ => ?_⟩
  have hb := norm_inv_latticeSymbol_add_le hz hzs hυ hκ
  have h1 : ‖(1 : Matrix (Fin N') (Fin N') ℂ) e.1 e.2‖ ≤ 1 := by
    rw [Matrix.one_apply]
    split_ifs <;> simp
  have he : matrixCoeffs (resolventExtension N' s κ) e = (Massive.latticeSymbol κ + (s : ℂ))⁻¹ *
      (1 : Matrix (Fin N') (Fin N') ℂ) e.1 e.2 := by
    simp [matrixCoeffs, resolventExtension, Matrix.smul_apply]
  rw [he, norm_mul]
  calc _ ≤ ‖(Massive.latticeSymbol κ + (s : ℂ))⁻¹‖ * 1 :=
        mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
    _ ≤ 2 / s := by rw [mul_one]; exact hb
omit [NeZero N'] in
theorem weightedTerm_nonneg (υ : ℝ) (n : Fin 4 → ℤ) : 0 ≤ weightedTerm υ n :=
  mul_nonneg (Real.exp_pos _).le (pow_nonneg (add_nonneg zero_le_one (Real.sqrt_nonneg _)) _)
theorem termZero_bound (hD : FluxZeroCalculus.Claim) {z : ℝ}
    (hz : 0 < z) : ∃ K : ℝ, 0 ≤ K ∧ ∀ s : ℝ, z ≤ s →
      IsWeylSymbol (termZero N' s) ∧ weightedCoeffNorm 3 (termZero N' s) ≤ K / s := by
  obtain ⟨υ, hυ0, hυ⟩ := exists_strip_width hz
  have hT : 0 ≤ ∑' n, weightedTerm υ n := tsum_nonneg (weightedTerm_nonneg υ)
  refine ⟨2 * ∑' n, weightedTerm υ n, by positivity, fun s hzs => ?_⟩
  obtain ⟨hsym, -, -, hnorm⟩ := (hD 0 N' N' N').1 υ (resolventExtension N' s) hυ0
    (isLatticePeriodicOnStrip_resolventExtension υ s)
    (isAnalyticNearStrip_resolventExtension hz hzs hυ)
    (boundedOnEntrywise_resolventExtension hz hzs hυ)
  rw [realRestrict_resolventExtension] at hsym hnorm
  refine ⟨hsym, hnorm.trans ?_⟩
  have hne : Nonempty (imStrip υ) := ⟨⟨0, fun μ => by simpa using hυ0.le⟩⟩
  have hsup : stripSupNorm υ (resolventExtension N' s) ≤ 2 / s :=
    ciSup_le fun κ => opNormValue_resolventExtension_le hz hzs hυ κ.2
  calc _ ≤ 2 / s * ∑' n, weightedTerm υ n := mul_le_mul_of_nonneg_right hsup hT
    _ = 2 * (∑' n, weightedTerm υ n) / s := by ring
end ApproxInverseSymbols
theorem approxInverseSymbolBounds_holds (hD : FluxZeroCalculus.Claim)
    (hC : FourierCoeffsOfSymbol) : ApproxInverseSymbolBounds := by
  intro N' _
  refine ⟨ApproxInverseSymbols.isFiniteFourierSymbol_of_isLowFrequencySum hD
      ApproxInverseSymbols.isLowFrequencySum_baseSymbolMatrix,
    fun n hn => ApproxInverseSymbols.fourierCoeff_eq_zero_of_one_lt hC
      ApproxInverseSymbols.isLowFrequencySum_baseSymbolMatrix n hn,
    fun μ => ⟨ApproxInverseSymbols.isFiniteFourierSymbol_of_isLowFrequencySum hD
        (ApproxInverseSymbols.isLowFrequencySum_baseSymbolDeriv μ),
      ApproxInverseSymbols.isFiniteFourierSymbol_of_isLowFrequencySum hD
        (ApproxInverseSymbols.isLowFrequencySum_baseSymbolSecondDeriv μ)⟩,
    fun z hz => ApproxInverseSymbols.termZero_bound hD hz⟩
end YangMills.Construction.Tower.MagneticWeyl
end
