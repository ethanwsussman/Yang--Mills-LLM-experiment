import YangMills.Construction.PeriodicOperators.RiemannSumsAndShiftsProof
import YangMills.Construction.Towers.BracketsOfTwoSymbolsAsSeriesProof
import YangMills.Construction.Towers.TheFreePropagatorsAndTheirRootsProof
import YangMills.Construction.FourierSeries.FejerMeansUniformLimit
import YangMills.Construction.PeriodicOperators.CovariantKernelsOfFiniteRangeProof
import YangMills.Construction.PeriodicOperators.EntriesDeterminantsAndHolomorphicFunctionsProof
import YangMills.Construction.Towers.AsymptoticsOfTheMassiveCoefficientProof
import YangMills.Construction.Towers.ChargedSymbolAtFluxZeroProof
import YangMills.Construction.Towers.CoefficientsOfASymbolProof
import YangMills.Construction.Towers.RulesOfTheMagneticWeylCalculus
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.MagneticWeyl.FluxZeroCalculus
open YangMills.Construction.Tower.UnitLatticeL2 YangMills.Construction.Tower.UnitaryCombinations
open YangMills.Construction.OneLoopNotation
open YangMills.Construction.Matrices.FourierMatrixSeries
open YangMills.Construction.PeriodicOperators (imStrip toComplexVec castVec matrixCoeffs
  HolomorphicOnEntrywise BoundedOnEntrywise bilinDot torusAverage)
open YangMills.Construction.InfiniteLattice (AmbientSpace)
open YangMills.Construction.Matrices.RectangularMatrix (opNormValue)
variable {N' N'' N''' : ℕ}
section MatrixNorms
variable [NeZero N'] [NeZero N'']
theorem opNormValue_nonneg (X : Matrix (Fin N') (Fin N'') ℂ) : 0 ≤ opNormValue X :=
  norm_nonneg _
theorem norm_toEuclideanLin_le (X : Matrix (Fin N') (Fin N'') ℂ) (v : EuclideanSpace ℂ (Fin N'')) :
    ‖Matrix.toEuclideanLin X v‖ ≤ opNormValue X * ‖v‖ :=
  (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin X)).le_opNorm v
theorem norm_entry_le_opNormValue (X : Matrix (Fin N') (Fin N'') ℂ) (i : Fin N') (k : Fin N'') :
    ‖X i k‖ ≤ opNormValue X := by apply _root_.YangMills.Construction.Tower.Massive.CoefficientAsymptoticsProof.norm_apply_le_opNormValue <;> assumption
theorem opNormValue_le_sum_norm (X : Matrix (Fin N') (Fin N'') ℂ) :
    opNormValue X ≤ ∑ i, ∑ k, ‖X i k‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
  have hX : Matrix.toEuclideanLin X v =
      ∑ i, ∑ k, (X i k * v k) • EuclideanSpace.single i (1 : ℂ) := by
    ext l
    simp [Matrix.toEuclideanLin_apply, Matrix.mulVec, dotProduct, Finset.sum_apply,
      Pi.single_apply]
  change ‖Matrix.toEuclideanLin X v‖ ≤ _
  rw [hX, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  rw [norm_smul, EuclideanSpace.norm_single, norm_one, mul_one, norm_mul]
  exact mul_le_mul_of_nonneg_left (PiLp.norm_apply_le v k) (norm_nonneg _)
theorem opNormValue_smul (s : ℂ) (X : Matrix (Fin N') (Fin N'') ℂ) :
    opNormValue (s • X) = ‖s‖ * opNormValue X := by
  change ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (s • X))‖ =
    ‖s‖ * ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin X)‖
  rw [map_smul, map_smul, norm_smul]
abbrev periodCube : Set AmbientSpace := Set.Icc (fun _ : Fin 4 => -Real.pi) (fun _ => Real.pi)
theorem volume_periodCube : (MeasureTheory.volume periodCube).toReal = (2 * Real.pi) ^ 4 := by
  rw [Real.volume_Icc_pi]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [ENNReal.toReal_pow, ENNReal.toReal_ofReal (by linarith [Real.pi_pos])]
  congr 1
  ring
theorem opNormValue_torusAverage_le (M : AmbientSpace → Matrix (Fin N') (Fin N'') ℂ)
    (hM : ∀ i k, Continuous fun q => M q i k) {B : ℝ} (hB : ∀ q, opNormValue (M q) ≤ B) :
    opNormValue (Matrix.of fun i k => torusAverage fun q => M q i k) ≤ B := by
  have hB0 : 0 ≤ B := (opNormValue_nonneg _).trans (hB 0)
  refine ContinuousLinearMap.opNorm_le_bound _ hB0 fun v => ?_
  change ‖Matrix.toEuclideanLin (Matrix.of fun i k => torusAverage fun q => M q i k) v‖ ≤ _
  set F : AmbientSpace → EuclideanSpace ℂ (Fin N') := fun q => Matrix.toEuclideanLin (M q) v
    with hFdef
  have hFl : ∀ q l, F q l = ∑ k, M q l k * v k := fun q l => by
    simp [hFdef, Matrix.toEuclideanLin_apply, Matrix.mulVec, dotProduct]
  have hF : Continuous F := by
    have : F = fun q => WithLp.toLp 2 fun l => ∑ k, M q l k * v k := by
      funext q
      ext l
      exact hFl q l
    rw [this]
    refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun l => ?_)
    exact continuous_finsetSum _ fun k _ => (hM l k).mul continuous_const
  have hint : MeasureTheory.IntegrableOn F periodCube :=
    hF.continuousOn.integrableOn_compact isCompact_Icc
  have hX : Matrix.toEuclideanLin (Matrix.of fun i k => torusAverage fun q => M q i k) v =
      (((2 * Real.pi) ^ 4)⁻¹ : ℝ) • ∫ q in periodCube, F q := by
    ext l
    have h1 : (∫ q in periodCube, F q) l = ∫ q in periodCube, F q l :=
      ((EuclideanSpace.proj l : EuclideanSpace ℂ (Fin N') →L[ℂ] ℂ).integral_comp_comm hint).symm
    have h2 : (∫ q in periodCube, F q l) = ∑ k, (∫ q in periodCube, M q l k) * v k := by
      simp only [hFl]
      rw [MeasureTheory.integral_finsetSum]
      · exact Finset.sum_congr rfl fun k _ => MeasureTheory.integral_mul_const _ _
      · exact fun k _ => ((hM l k).mul continuous_const).continuousOn.integrableOn_compact
          isCompact_Icc
    simp only [PiLp.smul_apply, h1, h2, Matrix.toEuclideanLin_apply, Matrix.mulVec, dotProduct,
      Matrix.of_apply, torusAverage, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp [mul_assoc]
  rw [hX, norm_smul]
  have hbound : ‖∫ q in periodCube, F q‖ ≤ B * ‖v‖ * (MeasureTheory.volume periodCube).toReal := by
    refine MeasureTheory.norm_setIntegral_le_of_norm_le_const ?_ fun q _ => ?_
    · exact isCompact_Icc.measure_lt_top
    · exact (norm_toEuclideanLin_le _ v).trans (mul_le_mul_of_nonneg_right (hB q) (norm_nonneg _))
  rw [volume_periodCube] at hbound
  have hp : 0 < (2 * Real.pi) ^ 4 := by
    have := Real.pi_pos
    positivity
  rw [Real.norm_of_nonneg (inv_nonneg.mpr hp.le)]
  calc ((2 * Real.pi) ^ 4)⁻¹ * ‖∫ q in periodCube, F q‖
      ≤ ((2 * Real.pi) ^ 4)⁻¹ * (B * ‖v‖ * (2 * Real.pi) ^ 4) :=
        mul_le_mul_of_nonneg_left hbound (inv_nonneg.mpr hp.le)
    _ = B * ‖v‖ := by field_simp
end MatrixNorms
section CharacterSeries
variable [NeZero N'] [NeZero N'']
theorem norm_fourierChar (n : Fin 4 → ℤ) (q : AmbientSpace) : ‖fourierChar n q‖ = 1 := by apply _root_.YangMills.Construction.Tower.Massive.CoefficientAsymptoticsProof.norm_fourierChar <;> assumption
theorem character_neg (n : Fin 4 → ℤ) (q : AmbientSpace) :
    Matrices.FourierMatrixSeries.character (-n) q = Complex.exp (-(Complex.I * intDot n q)) := by apply _root_.YangMills.Construction.Tower.FourierCoeffsProof.character_neg <;> assumption
theorem hasSum_fourierChar_smul (c : CoeffFamily N' N'') (hc : AbsSummable c) (q : AmbientSpace) :
    HasSum (fun n => fourierChar n q • c n) (seriesSum c q) := by apply _root_.YangMills.Construction.Tower.BracketExpansion.hasFourierExpansion_seriesSum <;> assumption
theorem fourierCoeff_seriesSum (hQ : Matrices.FourierMatrixSeries.statement)
    (c : CoeffFamily N' N'') (hc : AbsSummable c) : fourierCoeff (seriesSum c) = c := by
  funext n
  ext i k
  have h := (hQ N' N'' c hc).1.coeff_eq_average n i k
  rw [h]
  simp only [fourierCoeff, Matrix.of_apply, character_neg]
theorem eq_seriesSum_of_hasFourierExpansion (hQ : Matrices.FourierMatrixSeries.statement)
    {c : CoeffFamily N' N''} {a : AmbientSpace → Matrix (Fin N') (Fin N'') ℂ}
    (hs : HasFourierExpansion c a) (hc : AbsSummable c) : a = seriesSum c ∧ fourierCoeff a = c := by
  have ha : a = seriesSum c := funext fun q => (hs q).unique (hasSum_fourierChar_smul c hc q)
  exact ⟨ha, ha ▸ fourierCoeff_seriesSum hQ c hc⟩
theorem absSummable_of_weighted {c : CoeffFamily N' N''}
    (hw : ∀ j : ℕ, j ≤ 3 → Summable fun n => opNormValue (c n) *
      (1 + TorusMetric.euclidNormVec (castVec n)) ^ j) : AbsSummable c := by
  simpa [AbsSummable] using hw 0 (by norm_num)
theorem weylSymbol_eq_seriesSum (hQ : Matrices.FourierMatrixSeries.statement)
    {a : AmbientSpace → Matrix (Fin N') (Fin N'') ℂ} (h : IsWeylSymbol a) :
    AbsSummable (fourierCoeff a) ∧ a = seriesSum (fourierCoeff a) := by
  obtain ⟨c, hs, hw⟩ := h
  have hc := absSummable_of_weighted hw
  obtain ⟨h1, h2⟩ := eq_seriesSum_of_hasFourierExpansion hQ hs hc
  rw [h2]
  exact ⟨hc, h1⟩
theorem finiteFourierSum_props (hQ : Matrices.FourierMatrixSeries.statement)
    (S : Finset (Fin 4 → ℤ)) (t : CoeffFamily N' N'') :
    IsFiniteFourierSymbol (fun q => ∑ n ∈ S, fourierChar n q • t n) ∧
      fourierCoeff (fun q => ∑ n ∈ S, fourierChar n q • t n) =
        fun n => if n ∈ S then t n else 0 := by
  classical
  set c : CoeffFamily N' N'' := fun n => if n ∈ S then t n else 0 with hcdef
  have hzero : ∀ n ∉ S, c n = 0 := fun n hn => by simp [hcdef, hn]
  have hs : HasFourierExpansion c (fun q => ∑ n ∈ S, fourierChar n q • t n) := fun q => by
    have h := hasSum_sum_of_ne_finset_zero (L := SummationFilter.unconditional _)
      (f := fun n => fourierChar n q • c n) (s := S) (fun n hn => by simp [hzero n hn])
    have e : ∑ n ∈ S, fourierChar n q • c n = ∑ n ∈ S, fourierChar n q • t n :=
      Finset.sum_congr rfl fun n hn => by simp [hcdef, hn]
    rwa [e] at h
  have hw : ∀ j : ℕ, j ≤ 3 → Summable fun n => opNormValue (c n) *
      (1 + TorusMetric.euclidNormVec (castVec n)) ^ j := fun j _ =>
    summable_of_ne_finset_zero (s := S) fun n hn => by
      have h0 : opNormValue (0 : Matrix (Fin N') (Fin N'') ℂ) = 0 := by
        simp [opNormValue, opNormOf]
      rw [hzero n hn, h0, zero_mul]
  have hco := (eq_seriesSum_of_hasFourierExpansion hQ hs (absSummable_of_weighted hw)).2
  refine ⟨⟨⟨c, hs, hw⟩, ?_⟩, hco⟩
  rw [hco]
  refine S.finite_toSet.subset fun n hn => ?_
  by_contra h
  exact hn (hzero n h)
end CharacterSeries
section ExponentialPhase
def expPhase (n : Fin 4 → ℤ) (κ : Fin 4 → ℂ) : ℂ :=
  Complex.exp (-(Complex.I * bilinDot (toComplexVec (castVec n)) κ))
theorem differentiable_expPhase (n : Fin 4 → ℤ) : Differentiable ℂ (expPhase n) := by
  unfold expPhase bilinDot
  fun_prop
theorem expPhase_add (n : Fin 4 → ℤ) (κ κ' : Fin 4 → ℂ) :
    expPhase n (κ + κ') = expPhase n κ * expPhase n κ' := by apply _root_.YangMills.Construction.PeriodicOperators.RiemannSums.expChar_add <;> assumption
theorem expPhase_periodic (n : Fin 4 → ℤ) {p : AmbientSpace}
    (hp : p ∈ InfiniteLattice.latticeSubgroup (2 * Real.pi)) :
    expPhase n (toComplexVec p) = 1 := by
  obtain ⟨m, hm⟩ := hp
  have h : -(Complex.I * bilinDot (toComplexVec (castVec n)) (toComplexVec p)) =
      ((-∑ μ, n μ * m μ : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
    simp only [bilinDot, toComplexVec, castVec, hm]
    push_cast
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_neg_distrib, Finset.sum_mul]
    exact Finset.sum_congr rfl fun μ _ => by ring
  rw [expPhase, h, Complex.exp_int_mul_two_pi_mul_I]
theorem norm_expPhase (n : Fin 4 → ℤ) (κ : Fin 4 → ℂ) :
    ‖expPhase n κ‖ = Real.exp (∑ μ, (n μ : ℝ) * (κ μ).im) := by apply _root_.YangMills.Construction.PeriodicOperators.RiemannSums.norm_expChar <;> assumption
theorem character_eq_expPhase (n : Fin 4 → ℤ) (q : AmbientSpace) :
    Matrices.FourierMatrixSeries.character n q = expPhase (-n) (toComplexVec q) := by
  have h : bilinDot (toComplexVec (castVec (-n))) (toComplexVec q) =
      -bilinDot (toComplexVec (castVec n)) (toComplexVec q) := by
    simp [bilinDot, castVec, toComplexVec]
  rw [expPhase, h, mul_neg, neg_neg]
  rfl
theorem toComplexVec_add (p p' : AmbientSpace) :
    toComplexVec (p + p') = toComplexVec p + toComplexVec p' := by apply _root_.YangMills.Construction.PeriodicOperators.CovariantFiniteRangeProof.toComplexVec_add <;> assumption
theorem continuous_toComplexVec : Continuous toComplexVec := by apply _root_.YangMills.Construction.PeriodicOperators.EntriesDets.continuous_toComplexVec <;> assumption
theorem update_add_two_pi (y : AmbientSpace) (j : Fin 4) :
    ∃ p ∈ InfiniteLattice.latticeSubgroup (2 * Real.pi),
      Function.update y j (y j + 2 * Real.pi) = y + p := by
  refine ⟨Pi.single j (2 * Real.pi), ⟨Pi.single j 1, fun μ => ?_⟩, ?_⟩
  · by_cases h : μ = j
    · subst h; simp
    · simp [h]
  · funext μ
    by_cases h : μ = j
    · subst h; simp
    · simp [h]
theorem isHolomorphicIn_mul_entire {O : Set (Coordinates.ComplexCoordinates 4)}
    {f h : (Fin 4 → ℂ) → ℂ}
    (hf : Coordinates.ComplexCoordinates.IsHolomorphicIn (N' := 1) O fun x _ => f x)
    (hh : Differentiable ℂ h) :
    Coordinates.ComplexCoordinates.IsHolomorphicIn (N' := 1) O fun x _ => f x * h x := by
  obtain ⟨ho, hc, hd⟩ := hf
  refine ⟨ho, ?_, ?_⟩
  · have h1 : ContinuousOn f O := (continuous_apply (0 : Fin 1)).comp_continuousOn hc
    exact continuousOn_pi.mpr fun _ => h1.mul hh.continuous.continuousOn
  · intro a ha j
    filter_upwards [hd a ha j] with ζ hζ
    have h1 : DifferentiableAt ℂ
        (fun ζ : ℂ => f (a + ζ • Coordinates.ComplexCoordinates.stdBasisVector j)) ζ :=
      differentiableAt_pi.mp hζ 0
    have h2 : Differentiable ℂ
        (fun ζ : ℂ => a + ζ • Coordinates.ComplexCoordinates.stdBasisVector j) := by
      fun_prop
    exact differentiableAt_pi.mpr fun _ => h1.mul (hh.comp h2).differentiableAt
end ExponentialPhase
section FourierSumOnStrip
variable [NeZero N'] [NeZero N'']
theorem fourierCoeffOnTorus_eq (f : AmbientSpace → ℂ) (k : Fin 4 → ℤ) :
    FourierSeries.fourierCoeffOnTorus f k =
      torusAverage fun q => f q * Complex.exp (-(Complex.I * intDot k q)) := by
  have hset : Set.pi Set.univ (fun _ : Fin 4 => Set.Icc (-Real.pi) Real.pi) = periodCube :=
    Set.pi_univ_Icc _ _
  rw [FourierSeries.fourierCoeffOnTorus, torusAverage, hset]
  have hexp : ∀ y : Fin 4 → ℝ, (∑ j, (k j : ℂ) * (y j : ℂ)) * Complex.I =
      Complex.I * intDot k y := fun y => by
    simp [intDot, bilinDot, castVec, toComplexVec, mul_comm]
  simp only [hexp]
  push_cast
  rfl
theorem eq_seriesSum_fourierCoeff (hF : FourierSeries.FejerTheoremAndTorusUniqueness)
    (hQ : Matrices.FourierMatrixSeries.statement)
    (A : AmbientSpace → Matrix (Fin N') (Fin N'') ℂ) (hcA : ∀ i k, Continuous fun q => A q i k)
    (hpA : ∀ q, ∀ p ∈ InfiniteLattice.latticeSubgroup (2 * Real.pi), A (q + p) = A q)
    (hc : AbsSummable (fourierCoeff A)) : A = seriesSum (fourierCoeff A) := by
  funext q
  ext i k
  have hcont : Continuous (seriesSum (fourierCoeff A)) := (hQ N' N'' _ hc).1.continuous_sum
  refine congrFun (hF.2 4 (fun y => A y i k) (fun y => seriesSum (fourierCoeff A) y i k) (hcA i k)
    (hcont.matrix_elem i k) (fun j y => ?_) (fun j y => ?_) fun m => ?_) q
  · obtain ⟨p, hp, h⟩ := update_add_two_pi y j
    change A (Function.update y j (y j + 2 * Real.pi)) i k = A y i k
    rw [h, hpA y p hp]
  · obtain ⟨p, hp, h⟩ := update_add_two_pi y j
    change seriesSum (fourierCoeff A) (Function.update y j (y j + 2 * Real.pi)) i k =
      seriesSum (fourierCoeff A) y i k
    have hw : ∀ n, Matrices.FourierMatrixSeries.character n (y + p) =
        Matrices.FourierMatrixSeries.character n y := fun n => by
      rw [character_eq_expPhase, character_eq_expPhase, toComplexVec_add, expPhase_add,
        expPhase_periodic _ hp, mul_one]
    rw [h]
    simp only [seriesSum, hw]
  · rw [fourierCoeffOnTorus_eq, fourierCoeffOnTorus_eq]
    have h := congrFun (fourierCoeff_seriesSum hQ _ hc) m
    have h2 := congrFun (congrFun h i) k
    exact h2.symm
theorem summable_weightedTerm {υ : ℝ} (hυ : 0 < υ) : Summable (weightedTerm υ) := by
  set f : ℤ → ℝ := fun j => Real.exp (-υ * |(j : ℝ)|) * (1 + |(j : ℝ)|) ^ 3 with hfdef
  have hf0 : 0 ≤ f := fun j => by
    have : 0 ≤ |(j : ℝ)| := abs_nonneg _
    simp only [hfdef, Pi.zero_apply]
    positivity
  have hnat : Summable fun m : ℕ => Real.exp (-υ * (m : ℝ)) * (1 + (m : ℝ)) ^ 3 := by
    have h0 := Real.summable_pow_mul_exp_neg_nat_mul 0 hυ
    have h1 := Real.summable_pow_mul_exp_neg_nat_mul 1 hυ
    have h2 := Real.summable_pow_mul_exp_neg_nat_mul 2 hυ
    have h3 := Real.summable_pow_mul_exp_neg_nat_mul 3 hυ
    refine (((h0.add (h1.mul_left 3)).add (h2.mul_left 3)).add h3).congr fun m => ?_
    ring
  have hf : Summable f := by
    refine Summable.of_nat_of_neg ?_ ?_
    · refine hnat.congr fun m => ?_
      simp [hfdef]
    · refine hnat.congr fun m => ?_
      simp [hfdef]
  have hprod : Summable fun x : ℤ × ℤ × ℤ × ℤ => f x.1 * (f x.2.1 * (f x.2.2.1 * f x.2.2.2)) := by
    have h34 := hf.mul_of_nonneg hf hf0 hf0
    have h234 := hf.mul_of_nonneg h34 hf0 (fun x => mul_nonneg (hf0 _) (hf0 _))
    exact hf.mul_of_nonneg h234 hf0 (fun x => mul_nonneg (hf0 _) (mul_nonneg (hf0 _) (hf0 _)))
  have hinj : Function.Injective fun n : Fin 4 → ℤ => (n 0, n 1, n 2, n 3) := by
    intro n n' h
    simp only [Prod.mk.injEq] at h
    funext μ
    fin_cases μ
    · exact h.1
    · exact h.2.1
    · exact h.2.2.1
    · exact h.2.2.2
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) (hprod.comp_injective hinj)
  · have : 0 ≤ TorusMetric.euclidNormVec (castVec n) := Real.sqrt_nonneg _
    have h2 : 0 < expWeight υ n := Real.exp_pos _
    rw [weightedTerm]
    positivity
  · simp only [Function.comp, hfdef, weightedTerm, expWeight, castVec, TorusMetric.euclidNormVec,
      Fin.sum_univ_four]
    set a := |(n 0 : ℝ)| with ha
    set b := |(n 1 : ℝ)| with hb
    set c := |(n 2 : ℝ)| with hc
    set d := |(n 3 : ℝ)| with hd
    have ha0 : 0 ≤ a := abs_nonneg _
    have hb0 : 0 ≤ b := abs_nonneg _
    have hc0 : 0 ≤ c := abs_nonneg _
    have hd0 : 0 ≤ d := abs_nonneg _
    have hsq : Real.sqrt ((n 0 : ℝ) ^ 2 + (n 1 : ℝ) ^ 2 + (n 2 : ℝ) ^ 2 + (n 3 : ℝ) ^ 2) ≤
        a + b + c + d := by
      rw [← sq_abs (n 0 : ℝ), ← sq_abs (n 1 : ℝ), ← sq_abs (n 2 : ℝ), ← sq_abs (n 3 : ℝ)]
      refine Real.sqrt_le_iff.mpr ⟨by positivity, ?_⟩
      nlinarith [mul_nonneg ha0 hb0, mul_nonneg ha0 hc0, mul_nonneg ha0 hd0, mul_nonneg hb0 hc0,
        mul_nonneg hb0 hd0, mul_nonneg hc0 hd0]
    have hw : 1 + Real.sqrt ((n 0 : ℝ) ^ 2 + (n 1 : ℝ) ^ 2 + (n 2 : ℝ) ^ 2 + (n 3 : ℝ) ^ 2) ≤
        (1 + a) * ((1 + b) * ((1 + c) * (1 + d))) := by
      have : 1 + (a + b + c + d) ≤ (1 + a) * ((1 + b) * ((1 + c) * (1 + d))) := by
        have e : (1 + a) * ((1 + b) * ((1 + c) * (1 + d))) - (1 + (a + b + c + d)) =
            a * b + a * c + a * d + b * c + b * d + c * d + a * b * c + a * b * d + a * c * d +
              b * c * d + a * b * c * d := by ring
        have : 0 ≤ (1 + a) * ((1 + b) * ((1 + c) * (1 + d))) - (1 + (a + b + c + d)) := by
          rw [e]
          positivity
        linarith
      linarith
    have hexp : Real.exp (-υ * (a + b + c + d)) =
        Real.exp (-υ * a) * (Real.exp (-υ * b) * (Real.exp (-υ * c) * Real.exp (-υ * d))) := by
      rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    have hpow := pow_le_pow_left₀ (by positivity) hw 3
    calc _ ≤ Real.exp (-υ * (a + b + c + d)) *
            ((1 + a) * ((1 + b) * ((1 + c) * (1 + d)))) ^ 3 :=
          mul_le_mul_of_nonneg_left hpow (Real.exp_pos _).le
      _ = _ := by
          rw [hexp]
          ring
end FourierSumOnStrip
section CoefficientDecay
variable [NeZero N'] [NeZero N'']
theorem bddAbove_opNormValue_imStrip {υ : ℝ} {a : (Fin 4 → ℂ) → Matrix (Fin N') (Fin N'') ℂ}
    (hbd : BoundedOnEntrywise matrixCoeffs (imStrip υ) a) :
    BddAbove (Set.range fun κ : imStrip υ => opNormValue (a κ)) := by
  choose C hC using hbd
  refine ⟨∑ i, ∑ k, C (i, k), ?_⟩
  rintro _ ⟨κ, rfl⟩
  refine (opNormValue_le_sum_norm _).trans
    (Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun k _ => hC (i, k) κ κ.2)
theorem abs_sign_le_and_mul_sign (m : ℤ) : |((Int.sign m : ℤ) : ℝ)| ≤ 1 ∧
    (m : ℝ) * ((Int.sign m : ℤ) : ℝ) = |(m : ℝ)| := by
  refine ⟨?_, by exact_mod_cast Int.mul_sign_self m⟩
  rcases Int.sign_trichotomy m with h | h | h <;> rw [h] <;> norm_num
theorem opNormValue_fourierCoeff_le (hR : PeriodicOperators.RiemannSums.Claim) {υ : ℝ}
    (hυ : 0 < υ) {a : (Fin 4 → ℂ) → Matrix (Fin N') (Fin N'') ℂ}
    (hper : IsLatticePeriodicOnStrip υ a) (hhol : IsAnalyticNearStrip υ a)
    (hbd : BoundedOnEntrywise matrixCoeffs (imStrip υ) a) (n : Fin 4 → ℤ) :
    opNormValue (fourierCoeff (realRestrict a) n) ≤ stripSupNorm υ a * expWeight υ n := by
  obtain ⟨O, hO, -, -, hent⟩ := hhol
  have hcont : ∀ i k, ContinuousOn (fun κ => a κ i k) O := fun i k =>
    (continuous_apply (0 : Fin 1)).comp_continuousOn (hent (i, k)).2.1
  set ϑ : Fin 4 → ℂ := fun μ => ((-(υ * ((Int.sign (n μ) : ℤ) : ℝ)) : ℝ) : ℂ) * Complex.I
    with hϑdef
  have hϑim : ∀ μ, (ϑ μ).im = -(υ * ((Int.sign (n μ) : ℤ) : ℝ)) := fun μ => by
    simp [hϑdef]
  have hϑ : ϑ ∈ imStrip υ := fun μ => by
    rw [hϑim, abs_neg, abs_mul, abs_of_pos hυ]
    have := (abs_sign_le_and_mul_sign (n μ)).1
    nlinarith
  have hshift : ∀ q : AmbientSpace, toComplexVec q + ϑ ∈ imStrip υ := fun q μ => by
    have : (toComplexVec q μ).im = 0 := by simp [toComplexVec]
    simpa [this] using hϑ μ
  have hmap : Continuous fun q : AmbientSpace => toComplexVec q + ϑ :=
    continuous_toComplexVec.add continuous_const
  have hstripBound : ∀ κ ∈ imStrip υ, ‖expPhase n κ‖ ≤ Real.exp (∑ μ, |(n μ : ℝ)| * υ) :=
    fun κ hκ => by
    rw [norm_expPhase]
    refine Real.exp_le_exp.mpr (Finset.sum_le_sum fun μ _ => ?_)
    calc (n μ : ℝ) * (κ μ).im ≤ |(n μ : ℝ) * (κ μ).im| := le_abs_self _
      _ = |(n μ : ℝ)| * |(κ μ).im| := abs_mul _ _
      _ ≤ |(n μ : ℝ)| * υ := mul_le_mul_of_nonneg_left (hκ μ) (abs_nonneg _)
  have hshiftInt : ∀ i k, (torusAverage fun q => (fun κ => a κ i k * expPhase n κ)
      (toComplexVec q + ϑ)) = torusAverage fun q => (fun κ => a κ i k * expPhase n κ)
      (toComplexVec q) := fun i k => by
    refine (hR 1 υ (fun κ => a κ i k * expPhase n κ) one_pos hυ
      ⟨O, hO, isHolomorphicIn_mul_entire (hent (i, k)) (differentiable_expPhase n)⟩ ?_ ?_).2 ϑ hϑ
    · intro κ hκ p hp
      have h1 : a (κ + toComplexVec p) = a κ := hper κ hκ p hp
      simp only [h1, expPhase_add, expPhase_periodic n hp, mul_one]
    · obtain ⟨C, hC⟩ := hbd (i, k)
      refine ⟨C * Real.exp (∑ μ, |(n μ : ℝ)| * υ), fun κ hκ => ?_⟩
      rw [norm_mul]
      exact mul_le_mul (hC κ hκ) (hstripBound κ hκ) (norm_nonneg _)
        ((norm_nonneg _).trans (hC κ hκ))
  set M : AmbientSpace → Matrix (Fin N') (Fin N'') ℂ :=
    fun q => expPhase n (toComplexVec q + ϑ) • a (toComplexVec q + ϑ) with hMdef
  have hco : fourierCoeff (realRestrict a) n =
      Matrix.of fun i k => torusAverage fun q => M q i k := by
    ext i k
    simp only [fourierCoeff, Matrix.of_apply]
    have h := hshiftInt i k
    simp only [hMdef, Matrix.smul_apply, smul_eq_mul, mul_comm (expPhase n _)]
    exact h.symm
  rw [hco]
  refine opNormValue_torusAverage_le M (fun i k => ?_) fun q => ?_
  · refine ((differentiable_expPhase n).continuous.comp hmap).mul ?_
    exact (hcont i k).comp_continuous hmap fun q => hO (hshift q)
  · rw [hMdef]
    simp only
    rw [opNormValue_smul, norm_expPhase, mul_comm]
    have h1 : ∑ μ, (n μ : ℝ) * (toComplexVec q μ + ϑ μ).im = -υ * ∑ μ, |(n μ : ℝ)| := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun μ _ => ?_
      have h2 : (toComplexVec q μ).im = 0 := by simp [toComplexVec]
      rw [Complex.add_im, h2, zero_add, hϑim, ← (abs_sign_le_and_mul_sign (n μ)).2]
      ring
    have h3 : opNormValue (a (toComplexVec q + ϑ)) ≤ stripSupNorm υ a :=
      le_ciSup (bddAbove_opNormValue_imStrip hbd) (⟨_, hshift q⟩ : imStrip υ)
    simp only [Pi.add_apply] at *
    rw [h1]
    exact mul_le_mul_of_nonneg_right h3 (Real.exp_pos _).le
theorem stripSymbolBounds_holds (hF : FourierSeries.FejerTheoremAndTorusUniqueness)
    (hQ : Matrices.FourierMatrixSeries.statement)
    (hR : PeriodicOperators.RiemannSums.Claim) : StripSymbolBounds N' N'' := by
  intro υ a hυ hper hhol hbd
  have hcoef := opNormValue_fourierCoeff_le hR hυ hper hhol hbd
  have hsum := summable_weightedTerm hυ
  have hS0 : 0 ≤ stripSupNorm υ a :=
    Real.iSup_nonneg fun κ => opNormValue_nonneg _
  have hwt : ∀ n : Fin 4 → ℤ, (1 : ℝ) ≤ 1 + TorusMetric.euclidNormVec (castVec n) := fun n => by
    have : 0 ≤ TorusMetric.euclidNormVec (castVec n) := Real.sqrt_nonneg _
    linarith
  have hterm : ∀ (j : ℕ), j ≤ 3 → ∀ n : Fin 4 → ℤ,
      opNormValue (fourierCoeff (realRestrict a) n) *
        (1 + TorusMetric.euclidNormVec (castVec n)) ^ j ≤
      stripSupNorm υ a * weightedTerm υ n := fun j hj n => by
    have h1 : (1 + TorusMetric.euclidNormVec (castVec n)) ^ j ≤
        (1 + TorusMetric.euclidNormVec (castVec n)) ^ 3 := pow_le_pow_right₀ (hwt n) hj
    have h2 : (0 : ℝ) ≤ (1 + TorusMetric.euclidNormVec (castVec n)) ^ j :=
      pow_nonneg (by linarith [hwt n]) _
    calc _ ≤ stripSupNorm υ a * expWeight υ n *
          (1 + TorusMetric.euclidNormVec (castVec n)) ^ j :=
          mul_le_mul_of_nonneg_right (hcoef n) h2
      _ ≤ stripSupNorm υ a * expWeight υ n * (1 + TorusMetric.euclidNormVec (castVec n)) ^ 3 :=
          mul_le_mul_of_nonneg_left h1 (mul_nonneg hS0 (Real.exp_pos _).le)
      _ = _ := by rw [weightedTerm]; ring
  have hw : ∀ j : ℕ, j ≤ 3 → Summable fun n => opNormValue (fourierCoeff (realRestrict a) n) *
      (1 + TorusMetric.euclidNormVec (castVec n)) ^ j := fun j hj =>
    Summable.of_nonneg_of_le
      (fun n => mul_nonneg (opNormValue_nonneg _) (pow_nonneg (by linarith [hwt n]) _))
      (hterm j hj) (hsum.mul_left _)
  have hc : AbsSummable (fourierCoeff (realRestrict a)) := absSummable_of_weighted hw
  obtain ⟨O, hO, -, -, hent⟩ := hhol
  have hreal : ∀ q : AmbientSpace, toComplexVec q ∈ imStrip υ := fun q μ => by
    simp [toComplexVec, hυ.le]
  have hA : realRestrict a = seriesSum (fourierCoeff (realRestrict a)) := by
    refine eq_seriesSum_fourierCoeff hF hQ _ (fun i k => ?_) (fun q p hp => ?_) hc
    · have h1 : ContinuousOn (fun κ => a κ i k) O :=
        (continuous_apply (0 : Fin 1)).comp_continuousOn (hent (i, k)).2.1
      exact h1.comp_continuous continuous_toComplexVec fun q => hO (hreal q)
    · change a (toComplexVec (q + p)) = a (toComplexVec q)
      rw [toComplexVec_add]
      exact hper _ (hreal q) p hp
  refine ⟨⟨fourierCoeff (realRestrict a), fun q => ?_, hw⟩, hcoef, hsum, ?_⟩
  · have h := hasSum_fourierChar_smul _ hc q
    rwa [← congrFun hA q] at h
  · rw [weightedCoeffNorm, ← tsum_mul_left]
    exact (hw 3 le_rfl).tsum_le_tsum (hterm 3 le_rfl) (hsum.mul_left _)
end CoefficientDecay
section Translations
variable {L : ℕ}
theorem magneticTranslation_zero_apply (μ : Fin 4) (w : ScalarL2 L)
    (x : Tower.FullSpace.Vertex L 0 0) :
    magneticTranslation L 0 μ w x = w (x + InfiniteLattice.axisStep _ μ) := by
  change Complex.exp (2 * Complex.I * (halfFluxAngle L 0 (Tower.FullSpace.forwardEdge x μ) : ℂ)) •
    w (x + InfiniteLattice.axisStep _ μ) = _
  simp [halfFluxAngle]
theorem magneticTranslation_inv_apply (μ : Fin 4) (w : ScalarL2 L)
    (x : Tower.FullSpace.Vertex L 0 0) :
    (magneticTranslation L 0 μ)⁻¹ w x = w (x - InfiniteLattice.axisStep _ μ) := by
  have h := magneticTranslation_zero_apply μ ((magneticTranslation L 0 μ)⁻¹ w)
    (x - InfiniteLattice.axisStep _ μ)
  have h1 : magneticTranslation L 0 μ ((magneticTranslation L 0 μ)⁻¹ w) = w := by
    have := congrArg (fun e : ScalarL2 L ≃ₗᵢ[ℂ] ScalarL2 L => e w)
      (mul_inv_cancel (magneticTranslation L 0 μ))
    simpa [LinearIsometryEquiv.coe_mul] using this
  rw [h1, sub_add_cancel] at h
  exact h.symm
theorem magneticTranslation_zpow_apply (μ : Fin 4) (k : ℤ) (w : ScalarL2 L)
    (x : Tower.FullSpace.Vertex L 0 0) :
    (magneticTranslation L 0 μ ^ k) w x = w (x + k • InfiniteLattice.axisStep _ μ) := by
  induction k using Int.induction_on generalizing w x with
  | zero => simp [LinearIsometryEquiv.coe_one]
  | succ i ih =>
    rw [zpow_add_one, LinearIsometryEquiv.coe_mul, Function.comp_apply, ih,
      magneticTranslation_zero_apply, add_smul, one_smul, add_assoc]
  | pred i ih =>
    rw [zpow_sub_one, LinearIsometryEquiv.coe_mul, Function.comp_apply, ih,
      magneticTranslation_inv_apply, sub_smul, one_smul, sub_eq_add_neg (-(i : ℤ) • _),
      ← add_assoc, sub_eq_add_neg]
theorem magneticWeyl_zero_apply (n : Fin 4 → ℤ) (w : ScalarL2 L)
    (x : Tower.FullSpace.Vertex L 0 0) :
    magneticWeyl L 0 n w x = w (x + n 0 • InfiniteLattice.axisStep _ 0 +
      n 1 • InfiniteLattice.axisStep _ 1 + n 2 • InfiniteLattice.axisStep _ 2 +
      n 3 • InfiniteLattice.axisStep _ 3) := by
  have h : magneticWeyl L 0 n w = magneticTranslationProd L 0 n w := by
    simp [magneticWeyl]
  rw [h, magneticTranslationProd]
  simp only [LinearIsometryEquiv.coe_mul, Function.comp_apply]
  rw [magneticTranslation_zpow_apply, magneticTranslation_zpow_apply,
    magneticTranslation_zpow_apply, magneticTranslation_zpow_apply]
theorem magneticWeylIsTranslation_holds : MagneticWeylIsTranslation L := by
  intro n x w
  have hs : Tower.meshAt L 0 0 = 1 := by simp [Tower.meshAt]
  have h : latticePoint L x + n 0 • InfiniteLattice.axisStep _ 0 +
      n 1 • InfiniteLattice.axisStep _ 1 + n 2 • InfiniteLattice.axisStep _ 2 +
      n 3 • InfiniteLattice.axisStep _ 3 = latticePoint L (x + n) := by
    refine Subtype.ext (funext fun μ => ?_)
    fin_cases μ <;> simp [latticePoint, castVec, InfiniteLattice.axisStep, hs]
  rw [magneticWeyl_zero_apply, h]
theorem magneticWeyl_zero_zero : magneticWeyl L 0 0 = LinearMap.id := by
  refine LinearMap.ext fun w => lp.ext (funext fun x => ?_)
  rw [magneticWeyl_zero_apply]
  simp
end Translations
section FluxZeroProducts
variable [NeZero N'] [NeZero N''] [NeZero N''']
theorem moyalProductIsPointwise_holds (hQ : Matrices.FourierMatrixSeries.statement) :
    MoyalProductIsPointwise N' N'' N''' := by
  intro a a' ha ha'
  funext q
  obtain ⟨hc, hea⟩ := weylSymbol_eq_seriesSum hQ ha
  obtain ⟨hc', hea'⟩ := weylSymbol_eq_seriesSum hQ ha'
  have hconv : ∀ n, moyalCoeff 0 a a' n =
      coeffConv (fourierCoeff a) (fourierCoeff a') n := fun n => by
    simp [moyalCoeff, coeffConv]
  have hp := ((hQ N' N'' _ hc).2.2 N''' _ hc').sum_mul_sum q
  have e1 := congrFun hea q
  have e2 := congrFun hea' q
  rw [e1, e2, hp]
  change (∑' n, fourierChar n q • moyalCoeff 0 a a' n) = _
  simp only [hconv]
  rfl
theorem fourierChar_add (x n : Fin 4 → ℤ) (q : AmbientSpace) :
    fourierChar (x + n) q = fourierChar x q * fourierChar n q := by apply _root_.YangMills.Construction.Tower.ConstantFieldSymbols.FluxZero.fourierChar_add <;> assumption
theorem finiteFourierSymbol_eq_sum (hQ : Matrices.FourierMatrixSeries.statement)
    {a : AmbientSpace → Matrix (Fin N') (Fin N'') ℂ} (h : IsFiniteFourierSymbol a)
    (q : AmbientSpace) :
    a q = ∑ n ∈ h.2.toFinset, fourierChar n q • fourierCoeff a n := by
  obtain ⟨hc, hea⟩ := weylSymbol_eq_seriesSum hQ h.1
  have h1 := hasSum_fourierChar_smul _ hc q
  rw [← congrFun hea q] at h1
  refine h1.unique (hasSum_sum_of_ne_finset_zero fun n hn => ?_)
  have : fourierCoeff a n = 0 := by
    by_contra h0
    exact hn (h.2.mem_toFinset.mpr h0)
  simp [this]
theorem actsOnPlaneWaves_holds (hQ : Matrices.FourierMatrixSeries.statement) :
    ActsOnPlaneWavesByMultiplication N' N'' := by
  intro a h q v x
  rw [finsum_eq_sum_of_support_subset (s := h.2.toFinset)]
  · rw [finiteFourierSymbol_eq_sum hQ h q, map_sum, LinearMap.sum_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [planeWaveVec, fourierChar_add, map_smul, map_smul, LinearMap.smul_apply, smul_smul]
  · intro n hn
    by_contra h0
    have : fourierCoeff a n = 0 := by
      by_contra h1
      exact h0 (h.2.mem_toFinset.mpr h1)
    simp [this] at hn
theorem finiteTranslationSums_holds (hQ : Matrices.FourierMatrixSeries.statement) {L : ℕ}
    (hZ : Tower.UnitaryOperatorSeriesClaim) :
    FiniteTranslationSumsAreQuantized L N' N'' := by
  classical
  intro S t
  obtain ⟨htp, hco⟩ := finiteFourierSum_props hQ S t
  refine ⟨htp, ?_⟩
  rw [weylQuant, hco]
  set c : CoeffFamily N' N'' := fun n => if n ∈ S then t n else 0 with hcdef
  have hunit := fun n => magneticWeyl_isUnitary (L := L) 0 n
  have hzero : ∀ n ∉ S, matMulUnitaryOp (c n) (magneticWeyl L 0 n) = 0 := fun n hn => by
    have h1 := ((hZ L N' N'').1 (c n) _ (hunit n)).2
    have h0 : opNormValue (c n) = 0 := by
      simp [hcdef, hn, opNormValue, opNormOf]
    rw [h0] at h1
    exact norm_le_zero_iff.mp h1
  have hsum : AbsSummable c := summable_of_ne_finset_zero (s := S) fun n hn => by
    simp [hcdef, hn, opNormValue, opNormOf]
  have hconv := ((hZ L N' N'').2 c (magneticWeyl L 0) hsum hunit).1
  obtain ⟨e⟩ : Nonempty (ℕ+ ≃ (Fin 4 → ℤ)) := nonempty_equiv_of_countable
  have hlim := hconv e
  have hev : ∀ᶠ m : ℕ+ in Filter.atTop,
      ∑ l ∈ Finset.Icc 1 m, matMulUnitaryOp (c (e l)) (magneticWeyl L 0 (e l)) =
        ∑ n ∈ S, matMulUnitaryOp (t n) (magneticWeyl L 0 n) := by
    filter_upwards [Filter.eventually_ge_atTop (S.sup e.symm)] with m hm
    have hS : S ⊆ (Finset.Icc 1 m).map e.toEmbedding := fun n hn => by
      refine Finset.mem_map.mpr ⟨e.symm n, Finset.mem_Icc.mpr ⟨PNat.one_le _, ?_⟩, by simp⟩
      exact (Finset.le_sup (f := e.symm) hn).trans hm
    have h1 : ∑ l ∈ Finset.Icc 1 m, matMulUnitaryOp (c (e l)) (magneticWeyl L 0 (e l)) =
        ∑ n ∈ (Finset.Icc 1 m).map e.toEmbedding,
          matMulUnitaryOp (c n) (magneticWeyl L 0 n) := by
      rw [Finset.sum_map]
      rfl
    rw [h1, ← Finset.sum_subset hS fun n _ hn => hzero n hn]
    exact Finset.sum_congr rfl fun n hn => by simp [hcdef, hn]
  exact tendsto_nhds_unique (tendsto_const_nhds.congr' (hev.mono fun _ h => h.symm)) hlim
end FluxZeroProducts
section InverseSymbols
theorem isHolomorphicIn_of_differentiableOn {O : Set (Coordinates.ComplexCoordinates 4)}
    (ho : IsOpen O) {f : (Fin 4 → ℂ) → ℂ} (hf : DifferentiableOn ℂ f O) :
    Coordinates.ComplexCoordinates.IsHolomorphicIn (N' := 1) O fun x _ => f x := by apply _root_.YangMills.Construction.Tower.FreeResolvents.isHolomorphicIn_of_differentiableOn <;> assumption
theorem differentiable_det_of_entries {m : ℕ} {M : (Fin 4 → ℂ) → Matrix (Fin m) (Fin m) ℂ}
    (h : ∀ i j, Differentiable ℂ fun κ => M κ i j) : Differentiable ℂ fun κ => (M κ).det := by
  have hp : ∀ (s : Finset (Fin m)) (g : Fin m → (Fin 4 → ℂ) → ℂ),
      (∀ i, Differentiable ℂ (g i)) → Differentiable ℂ fun κ => ∏ i ∈ s, g i κ := by
    classical
    intro s g hg
    induction s using Finset.induction_on with
    | empty => simp
    | insert i s hi ih =>
      simp only [Finset.prod_insert hi]
      exact (hg i).mul ih
  simp only [Matrix.det_apply]
  refine Differentiable.fun_sum fun σ _ => ?_
  exact (hp Finset.univ (fun i κ => M κ (σ i) i) fun i => h _ _).const_smul _
theorem differentiable_adjugate_of_entries {m : ℕ}
    {M : (Fin 4 → ℂ) → Matrix (Fin m) (Fin m) ℂ}
    (h : ∀ i j, Differentiable ℂ fun κ => M κ i j) (i j : Fin m) :
    Differentiable ℂ fun κ => (M κ).adjugate i j := by
  simp only [Matrix.adjugate_apply]
  refine differentiable_det_of_entries fun k l => ?_
  by_cases hk : k = j
  · subst hk
    simp only [Matrix.updateRow_self]
    exact differentiable_const _
  · simp only [Matrix.updateRow_ne hk]
    exact h k l
theorem exists_periodCube_reduction (κ : Fin 4 → ℂ) :
    ∃ p ∈ InfiniteLattice.latticeSubgroup (2 * Real.pi), ∃ q ∈ periodCube,
      κ = (toComplexVec q + fun μ => ((κ μ).im : ℂ) * Complex.I) + toComplexVec p := by
  set m : Fin 4 → ℤ := fun μ => ⌊((κ μ).re + Real.pi) / (2 * Real.pi)⌋ with hm
  refine ⟨fun μ => (m μ : ℝ) * (2 * Real.pi), ⟨m, fun _ => rfl⟩,
    fun μ => (κ μ).re - (m μ : ℝ) * (2 * Real.pi), ⟨fun μ => ?_, fun μ => ?_⟩, ?_⟩
  · have h1 : (m μ : ℝ) ≤ ((κ μ).re + Real.pi) / (2 * Real.pi) := Int.floor_le _
    rw [le_div_iff₀ (by positivity)] at h1
    simp only
    linarith
  · have h1 : ((κ μ).re + Real.pi) / (2 * Real.pi) < (m μ : ℝ) + 1 := Int.lt_floor_add_one _
    rw [div_lt_iff₀ (by positivity)] at h1
    simp only
    linarith
  · funext μ
    apply Complex.ext <;> simp [toComplexVec]
variable [NeZero N']
def entireExtension (F : Finset (Fin 4 → ℤ)) (c : CoeffFamily N' N') (κ : Fin 4 → ℂ) :
    Matrix (Fin N') (Fin N') ℂ :=
  ∑ n ∈ F, expPhase (-n) κ • c n
theorem entireExtension_real (F : Finset (Fin 4 → ℤ)) (c : CoeffFamily N' N') (q : AmbientSpace) :
    entireExtension F c (toComplexVec q) = ∑ n ∈ F, fourierChar n q • c n :=
  Finset.sum_congr rfl fun n _ => by rw [← character_eq_expPhase]; rfl
theorem entireExtension_periodic (F : Finset (Fin 4 → ℤ)) (c : CoeffFamily N' N')
    (κ : Fin 4 → ℂ) {p : AmbientSpace} (hp : p ∈ InfiniteLattice.latticeSubgroup (2 * Real.pi)) :
    entireExtension F c (κ + toComplexVec p) = entireExtension F c κ :=
  Finset.sum_congr rfl fun n _ => by rw [expPhase_add, expPhase_periodic _ hp, mul_one]
theorem differentiable_entireExtension (F : Finset (Fin 4 → ℤ)) (c : CoeffFamily N' N')
    (i j : Fin N') : Differentiable ℂ fun κ => entireExtension F c κ i j := by
  simp only [entireExtension, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  exact Differentiable.fun_sum fun n _ => (differentiable_expPhase (-n)).mul_const _
def adjugateInverse (E : (Fin 4 → ℂ) → Matrix (Fin N') (Fin N') ℂ) (κ : Fin 4 → ℂ) :
    Matrix (Fin N') (Fin N') ℂ :=
  (E κ).det⁻¹ • (E κ).adjugate
theorem exists_strip_extension_inv (hQ : Matrices.FourierMatrixSeries.statement)
    (a : AmbientSpace → Matrix (Fin N') (Fin N') ℂ) (h : IsFiniteFourierSymbol a)
    (hu : ∀ q, IsUnit (a q)) :
    ∃ (υ : ℝ) (b : (Fin 4 → ℂ) → Matrix (Fin N') (Fin N') ℂ), 0 < υ ∧
      IsLatticePeriodicOnStrip υ b ∧ IsAnalyticNearStrip υ b ∧
      BoundedOnEntrywise matrixCoeffs (imStrip υ) b ∧
      realRestrict b = fun q => (a q)⁻¹ := by
  set E := entireExtension h.2.toFinset (fourierCoeff a) with hE
  have hEreal : ∀ q, E (toComplexVec q) = a q := fun q => by
    rw [hE, entireExtension_real]
    exact (finiteFourierSymbol_eq_sum hQ h q).symm
  have hEper : ∀ κ, ∀ p ∈ InfiniteLattice.latticeSubgroup (2 * Real.pi),
      E (κ + toComplexVec p) = E κ :=
    fun κ p hp => entireExtension_periodic _ _ κ hp
  have hEd := differentiable_entireExtension (N' := N') h.2.toFinset (fourierCoeff a)
  have hD : Differentiable ℂ fun κ => (E κ).det := differentiable_det_of_entries hEd
  have hK : IsCompact (toComplexVec '' periodCube) :=
    isCompact_Icc.image continuous_toComplexVec
  have hU : IsOpen {κ | (E κ).det ≠ 0} := isOpen_ne_fun hD.continuous continuous_const
  have hKU : toComplexVec '' periodCube ⊆ {κ | (E κ).det ≠ 0} := by
    rintro _ ⟨q, -, rfl⟩
    change (E (toComplexVec q)).det ≠ 0
    rw [hEreal]
    exact ((Matrix.isUnit_iff_isUnit_det _).mp (hu q)).ne_zero
  obtain ⟨δ, hδ, hsub⟩ := hK.exists_thickening_subset_open hU hKU
  set υ := δ / 4 with hυdef
  have hυ : 0 < υ := by positivity
  have hnz : ∀ κ : Fin 4 → ℂ, (∀ μ, |(κ μ).im| < 2 * υ) → (E κ).det ≠ 0 := fun κ hκ => by
    obtain ⟨p, hp, q, hq, hr⟩ := exists_periodCube_reduction κ
    rw [hr, hEper _ p hp]
    refine hsub (Metric.mem_thickening_iff.mpr ⟨toComplexVec q, ⟨q, hq, rfl⟩, ?_⟩)
    refine (dist_pi_lt_iff hδ).mpr fun μ => ?_
    have h1 : |(κ μ).im| < δ := by
      have := hκ μ
      linarith
    simpa [dist_eq_norm, Complex.norm_real] using h1
  set O : Set (Coordinates.ComplexCoordinates 4) := {κ | ∀ μ, |(κ μ).im| < 2 * υ} with hOdef
  have hOopen : IsOpen O := by
    have : O = ⋂ μ : Fin 4, {κ : Fin 4 → ℂ | |(κ μ).im| < 2 * υ} := by
      ext κ
      simp [hOdef]
    rw [this]
    refine isOpen_iInter_of_finite fun μ => isOpen_lt ?_ continuous_const
    exact continuous_abs.comp (Complex.continuous_im.comp (continuous_apply μ))
  have hstrip : imStrip υ ⊆ O := fun κ hκ μ => by
    have := hκ μ
    linarith
  have hbd : ∀ i j, DifferentiableOn ℂ (fun κ => adjugateInverse E κ i j) O := fun i j => by
    simp only [adjugateInverse, Matrix.smul_apply, smul_eq_mul]
    exact (hD.differentiableOn.inv fun κ hκ => hnz κ hκ).mul
      (differentiable_adjugate_of_entries hEd i j).differentiableOn
  have hbper : ∀ κ, ∀ p ∈ InfiniteLattice.latticeSubgroup (2 * Real.pi),
      adjugateInverse E (κ + toComplexVec p) = adjugateInverse E κ := fun κ p hp => by
    simp only [adjugateInverse, hEper κ p hp]
  refine ⟨υ, adjugateInverse E, hυ, fun κ _ p hp => hbper κ p hp, ⟨O, hstrip, by norm_num,
    hOopen, fun e => isHolomorphicIn_of_differentiableOn hOopen (hbd e.1 e.2)⟩, fun e => ?_, ?_⟩
  · set box : Set AmbientSpace := Set.Icc (fun _ => -υ) (fun _ => υ) with hbox
    set g : AmbientSpace × AmbientSpace → Fin 4 → ℂ :=
      fun x => toComplexVec x.1 + fun μ => ((x.2 μ : ℝ) : ℂ) * Complex.I with hg
    have hgc : Continuous g := by
      refine (continuous_toComplexVec.comp continuous_fst).add (continuous_pi fun μ => ?_)
      exact (Complex.continuous_ofReal.comp ((continuous_apply μ).comp continuous_snd)).mul
        continuous_const
    have hcomp : IsCompact (g '' (periodCube ×ˢ box)) :=
      (isCompact_Icc.prod isCompact_Icc).image hgc
    have hin : g '' (periodCube ×ˢ box) ⊆ O := by
      rintro _ ⟨⟨q, y⟩, ⟨-, hy⟩, rfl⟩ μ
      have h1 : -υ ≤ y μ := hy.1 μ
      have h2 : y μ ≤ υ := hy.2 μ
      have h3 : (g (q, y) μ).im = y μ := by simp [hg, toComplexVec]
      rw [h3]
      exact abs_lt.mpr ⟨by linarith, by linarith⟩
    obtain ⟨C, hC⟩ := hcomp.exists_bound_of_continuousOn ((hbd e.1 e.2).continuousOn.mono hin)
    refine ⟨C, fun κ hκ => ?_⟩
    obtain ⟨p, hp, q, hq, hr⟩ := exists_periodCube_reduction κ
    have hmem : (toComplexVec q + fun μ => ((κ μ).im : ℂ) * Complex.I) ∈
        g '' (periodCube ×ˢ box) :=
      ⟨(q, fun μ => (κ μ).im), ⟨hq, fun μ => (abs_le.mp (hκ μ)).1,
        fun μ => (abs_le.mp (hκ μ)).2⟩, rfl⟩
    have := hC _ hmem
    rw [hr, hbper _ p hp]
    exact this
  · funext q
    exact show adjugateInverse E (toComplexVec q) = (a q)⁻¹ from by
      simp only [adjugateInverse, hEreal, Matrix.inv_def, Ring.inverse_eq_inv']
theorem weylQuant_one (hQ : Matrices.FourierMatrixSeries.statement) {L : ℕ}
    (hZ : Tower.UnitaryOperatorSeriesClaim) :
    weylQuant L 0 (fun _ => (1 : Matrix (Fin N') (Fin N') ℂ)) =
      ContinuousLinearMap.id ℂ (VectorL2 L N') := by
  have h := (finiteTranslationSums_holds (N' := N') (N'' := N') hQ (L := L) hZ {0} fun _ => 1).2
  have hchar : ∀ q : AmbientSpace, fourierChar 0 q = 1 := fun q => by
    simp [fourierChar, intDot, bilinDot, castVec, toComplexVec]
  simp only [Finset.sum_singleton, hchar, one_smul] at h
  rw [← h, magneticWeyl_zero_zero]
  have hb := ((hZ L N' N').1 1 LinearMap.id ?_).1
  · refine ContinuousLinearMap.ext fun w => lp.ext (funext fun x => ?_)
    rw [hb]
    ext i
    simp [matMulUnitary, applyCoordwise, coord, Matrix.toEuclideanLin_apply]
  · exact ⟨Function.bijective_id, fun _ => rfl⟩
theorem inverseOfFiniteFourierSymbol_holds (hF : FourierSeries.FejerTheoremAndTorusUniqueness)
    (hQ : Matrices.FourierMatrixSeries.statement)
    (hR : PeriodicOperators.RiemannSums.Claim)
    (hW : Tower.MagneticWeylCalculusRules)
    (hZ : Tower.UnitaryOperatorSeriesClaim) (L : ℕ) :
    InverseOfFiniteFourierSymbol L N' := by
  intro a h hu
  obtain ⟨υ, b, hυ, hper, hhol, hbd, hb⟩ := exists_strip_extension_inv hQ a h hu
  have hs : IsWeylSymbol fun q => (a q)⁻¹ := by
    have := (stripSymbolBounds_holds hF hQ hR υ b hυ hper hhol hbd).1
    rwa [hb] at this
  have hdet : ∀ q, IsUnit (a q).det := fun q => (Matrix.isUnit_iff_isUnit_det _).mp (hu q)
  have h1 := ((hW L 0).2.2.2.2 N' N' N' a _ h.1 hs).1.2.2.2
  have h2 := ((hW L 0).2.2.2.2 N' N' N' _ a hs h.1).1.2.2.2
  have s1 := moyalProductIsPointwise_holds (N' := N') (N'' := N') (N''' := N') hQ a _ h.1 hs
  have s2 := moyalProductIsPointwise_holds (N' := N') (N'' := N') (N''' := N') hQ _ a hs h.1
  have e1 : (fun q => a q * (a q)⁻¹) = fun _ => 1 :=
    funext fun q => Matrix.mul_nonsing_inv _ (hdet q)
  have e2 : (fun q => (a q)⁻¹ * a q) = fun _ => 1 :=
    funext fun q => Matrix.nonsing_inv_mul _ (hdet q)
  refine ⟨hs, ?_, ?_⟩
  · rw [h1, s1, e1, weylQuant_one hQ hZ]
  · rw [h2, s2, e2, weylQuant_one hQ hZ]
end InverseSymbols
theorem claim_holds (hF : FourierSeries.FejerTheoremAndTorusUniqueness)
    (hQ : Matrices.FourierMatrixSeries.statement)
    (hR : PeriodicOperators.RiemannSums.Claim)
    (hW : Tower.MagneticWeylCalculusRules)
    (hZ : Tower.UnitaryOperatorSeriesClaim) : FluxZeroCalculus.Claim :=
  fun L _ _ _ _ _ _ => ⟨stripSymbolBounds_holds hF hQ hR, magneticWeylIsTranslation_holds,
    moyalProductIsPointwise_holds hQ, actsOnPlaneWaves_holds hQ, finiteTranslationSums_holds hQ hZ,
    inverseOfFiniteFourierSymbol_holds hF hQ hR hW hZ L⟩
end YangMills.Construction.Tower.MagneticWeyl.FluxZeroCalculus
end
