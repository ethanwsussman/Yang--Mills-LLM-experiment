import YangMills.Construction.FormsOnATorus.ColumnOfTheLimitFormProof
import YangMills.Construction.Towers.BracketsOfTwoSymbolsAsSeries
import YangMills.Construction.Towers.HolomorphicSymbolsAndTheCalculusAtFluxZeroProof
import YangMills.Construction.Towers.StarProductOfTwoSymbols
import YangMills.Construction.Towers.SumsAndProductsOfSymbols
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Tower.UnitLatticeL2 OneLoopNotation
open InfiniteLattice (AmbientSpace)
open PeriodicOperators (castVec toComplexVec bilinDot)
open scoped Matrix.Norms.L2Operator
namespace Tower.MagneticWeyl
namespace SymbolAlgebra
open Matrices.FourierMatrixSeries
theorem opNormValue_eq_norm {M M' : ℕ} [NeZero M] [NeZero M'] (X : Matrix (Fin M) (Fin M') ℂ) :
    Matrices.RectangularMatrix.opNormValue X = ‖X‖ :=
  (Matrix.l2_opNorm_def X).symm
abbrev latticeWeight (n : Fin 4 → ℤ) : ℝ := 1 + TorusMetric.euclidNormVec (castVec n)
theorem one_le_latticeWeight (n : Fin 4 → ℤ) : 1 ≤ latticeWeight n := by apply _root_.YangMills.DeltaSharedProofs.p500919 <;> assumption
theorem latticeWeight_nonneg (n : Fin 4 → ℤ) : 0 ≤ latticeWeight n :=
  zero_le_one.trans (one_le_latticeWeight n)
theorem latticeWeight_zero : latticeWeight 0 = 1 := by
  simp [latticeWeight, TorusMetric.euclidNormVec, castVec]
theorem abs_apply_le_latticeWeight (n : Fin 4 → ℤ) (μ : Fin 4) : |(n μ : ℝ)| ≤ latticeWeight n := by
  have h : |(n μ : ℝ)| ≤ TorusMetric.euclidNormVec (castVec n) := by
    refine Real.abs_le_sqrt ?_
    exact Finset.single_le_sum (f := fun ν => castVec n ν ^ 2)
      (fun ν _ => sq_nonneg _) (Finset.mem_univ μ)
  simp only [latticeWeight]
  linarith
theorem abs_symplecticForm_le (n m : Fin 4 → ℤ) :
    |(symplecticForm n m : ℝ)| ≤ 2 * (latticeWeight n * latticeWeight m) := by
  have h₁ : |(n 0 : ℝ) * (m 1 : ℝ)| ≤ latticeWeight n * latticeWeight m := by
    rw [abs_mul]
    exact mul_le_mul (abs_apply_le_latticeWeight n 0) (abs_apply_le_latticeWeight m 1)
      (abs_nonneg _) (latticeWeight_nonneg n)
  have h₂ : |(n 1 : ℝ) * (m 0 : ℝ)| ≤ latticeWeight n * latticeWeight m := by
    rw [abs_mul]
    exact mul_le_mul (abs_apply_le_latticeWeight n 1) (abs_apply_le_latticeWeight m 0)
      (abs_nonneg _) (latticeWeight_nonneg n)
  have h : (symplecticForm n m : ℝ) = (n 0 : ℝ) * (m 1 : ℝ) - (n 1 : ℝ) * (m 0 : ℝ) := by
    simp [symplecticForm]
  rw [h]
  calc _ ≤ |(n 0 : ℝ) * (m 1 : ℝ)| + |(n 1 : ℝ) * (m 0 : ℝ)| := abs_sub _ _
    _ ≤ _ := by linarith
theorem fourierChar_zero (q : AmbientSpace) : fourierChar 0 q = 1 := by apply _root_.YangMills.Construction.Tower.ConstantFieldSymbols.FluxZero.fourierChar_zero <;> assumption
variable {N' N'' N''' : ℕ}
theorem hasFourierExpansion_add {x y : CoeffFamily N' N''}
    {a b : AmbientSpace → Matrix (Fin N') (Fin N'') ℂ}
    (ha : HasFourierExpansion x a) (hb : HasFourierExpansion y b) :
    HasFourierExpansion (fun n => x n + y n) (fun q => a q + b q) := fun q => by
  simpa only [smul_add] using (ha q).add (hb q)
theorem hasFourierExpansion_smul (c : ℂ) {x : CoeffFamily N' N''}
    {a : AmbientSpace → Matrix (Fin N') (Fin N'') ℂ}
    (ha : HasFourierExpansion x a) :
    HasFourierExpansion (fun n => c • x n) (fun q => c • a q) := fun q => by
  have h : (fun n => fourierChar n q • c • x n) = fun n => c • fourierChar n q • x n :=
    funext fun n => smul_comm _ _ _
  rw [h]
  exact (ha q).const_smul c
section Weighted
variable [NeZero N'] [NeZero N'']
theorem opNormValue_nonneg (X : Matrix (Fin N') (Fin N'') ℂ) :
    0 ≤ Matrices.RectangularMatrix.opNormValue X := by apply _root_.YangMills.Construction.Tower.MagneticWeyl.FluxZeroCalculus.opNormValue_nonneg <;> assumption
theorem weightedTerm_nonneg (j : ℕ) (X : Matrix (Fin N') (Fin N'') ℂ) (n : Fin 4 → ℤ) :
    0 ≤ Matrices.RectangularMatrix.opNormValue X * latticeWeight n ^ j :=
  mul_nonneg (opNormValue_nonneg X) (pow_nonneg (latticeWeight_nonneg n) j)
theorem weightedTerm_add_le (j : ℕ) (X Y : Matrix (Fin N') (Fin N'') ℂ) (n : Fin 4 → ℤ) :
    Matrices.RectangularMatrix.opNormValue (X + Y) * latticeWeight n ^ j ≤
      Matrices.RectangularMatrix.opNormValue X * latticeWeight n ^ j +
        Matrices.RectangularMatrix.opNormValue Y * latticeWeight n ^ j := by
  rw [← add_mul]
  refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg (latticeWeight_nonneg n) j)
  simp only [opNormValue_eq_norm]
  exact norm_add_le X Y
theorem weightedTerm_smul (j : ℕ) (c : ℂ) (X : Matrix (Fin N') (Fin N'') ℂ) (n : Fin 4 → ℤ) :
    Matrices.RectangularMatrix.opNormValue (c • X) * latticeWeight n ^ j =
      ‖c‖ * (Matrices.RectangularMatrix.opNormValue X * latticeWeight n ^ j) := by
  simp only [opNormValue_eq_norm, norm_smul, mul_assoc]
theorem weightedAbsSummable_add {j : ℕ} {x y : CoeffFamily N' N''}
    (hx : WeightedAbsSummable j x) (hy : WeightedAbsSummable j y) :
    WeightedAbsSummable j fun n => x n + y n :=
  Summable.of_nonneg_of_le (fun n => weightedTerm_nonneg j _ n)
    (fun n => weightedTerm_add_le j _ _ n) (hx.add hy)
theorem weightedAbsSummable_smul {j : ℕ} (c : ℂ) {x : CoeffFamily N' N''}
    (hx : WeightedAbsSummable j x) : WeightedAbsSummable j fun n => c • x n := by
  unfold WeightedAbsSummable
  simp only [weightedTerm_smul]
  exact hx.mul_left _
theorem absSummable_of_weightedAbsSummable_zero {x : CoeffFamily N' N''}
    (hx : WeightedAbsSummable 0 x) : AbsSummable x := by
  simpa [WeightedAbsSummable, AbsSummable] using hx
theorem weightedAbsSummable_zero_of_absSummable {x : CoeffFamily N' N''} (hx : AbsSummable x) :
    WeightedAbsSummable 0 x := by
  simpa [WeightedAbsSummable, AbsSummable] using hx
theorem weightedCoeffNorm_add_le {j : ℕ} {a b f : AmbientSpace → Matrix (Fin N') (Fin N'') ℂ}
    (hf : fourierCoeff f = fun n => fourierCoeff a n + fourierCoeff b n)
    (ha : WeightedAbsSummable j (fourierCoeff a)) (hb : WeightedAbsSummable j (fourierCoeff b)) :
    weightedCoeffNorm j f ≤ weightedCoeffNorm j a + weightedCoeffNorm j b := by
  have hs : WeightedAbsSummable j (fourierCoeff f) := by
    rw [hf]
    exact weightedAbsSummable_add ha hb
  unfold weightedCoeffNorm
  rw [← Summable.tsum_add ha hb]
  refine Summable.tsum_le_tsum (fun n => ?_) hs (ha.add hb)
  rw [hf]
  exact weightedTerm_add_le j _ _ n
theorem weightedCoeffNorm_smul {j : ℕ} (c : ℂ) {a f : AmbientSpace → Matrix (Fin N') (Fin N'') ℂ}
    (hf : fourierCoeff f = fun n => c • fourierCoeff a n) :
    weightedCoeffNorm j f = ‖c‖ * weightedCoeffNorm j a := by
  unfold weightedCoeffNorm
  rw [hf, ← tsum_mul_left]
  exact tsum_congr fun n => weightedTerm_smul j c _ n
theorem weightedCoeffNorm_nonneg (j : ℕ) (a : AmbientSpace → Matrix (Fin N') (Fin N'') ℂ) :
    0 ≤ weightedCoeffNorm j a :=
  tsum_nonneg fun n => weightedTerm_nonneg j _ n
theorem weightedCoeffNorm_mono {j k : ℕ} (hjk : j ≤ k)
    {a : AmbientSpace → Matrix (Fin N') (Fin N'') ℂ}
    (hj : WeightedAbsSummable j (fourierCoeff a)) (hk : WeightedAbsSummable k (fourierCoeff a)) :
    weightedCoeffNorm j a ≤ weightedCoeffNorm k a := by
  refine Summable.tsum_le_tsum (fun n => ?_) hj hk
  exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (one_le_latticeWeight n) hjk)
    (opNormValue_nonneg _)
end Weighted
section Linear
variable [NeZero N'] [NeZero N'']
theorem absSummableLinear (hC : FourierCoeffsOfSymbol) : AbsSummableLinear N' N'' := by
  refine ⟨fun a b ha hb => ?_, fun c a ha => ?_⟩
  · obtain ⟨sa, na, -⟩ := (hC N' N'' a).1 ha
    obtain ⟨sb, nb, -⟩ := (hC N' N'' b).1 hb
    have hs := hasFourierExpansion_add sa sb
    have hn : AbsSummable fun n => fourierCoeff a n + fourierCoeff b n :=
      absSummable_of_weightedAbsSummable_zero
        (weightedAbsSummable_add (weightedAbsSummable_zero_of_absSummable na)
          (weightedAbsSummable_zero_of_absSummable nb))
    have hab : HasAbsSummableFourier fun q => a q + b q := ⟨_, hs, hn⟩
    have hco := ((hC N' N'' _).1 hab).2.2 _ hs hn
    exact ⟨hab, fun n => (congrFun hco n).symm, weightedCoeffNorm_add_le hco.symm
      (weightedAbsSummable_zero_of_absSummable na) (weightedAbsSummable_zero_of_absSummable nb)⟩
  · obtain ⟨sa, na, -⟩ := (hC N' N'' a).1 ha
    have hs := hasFourierExpansion_smul c sa
    have hn : AbsSummable fun n => c • fourierCoeff a n :=
      absSummable_of_weightedAbsSummable_zero
        (weightedAbsSummable_smul c (weightedAbsSummable_zero_of_absSummable na))
    have hca : HasAbsSummableFourier fun q => c • a q := ⟨_, hs, hn⟩
    have hco := ((hC N' N'' _).1 hca).2.2 _ hs hn
    exact ⟨hca, fun n => (congrFun hco n).symm, weightedCoeffNorm_smul c hco.symm⟩
theorem symbolSpace (hS : Matrices.FourierMatrixSeries.statement)
    (hC : FourierCoeffsOfSymbol) : SymbolSpace N' N'' := by
  refine ⟨fun a b ha hb => ?_, fun c a ha => ?_, fun c => ?_, fun a ha => ?_⟩
  · obtain ⟨hsa, wa⟩ := (hC N' N'' a).2 ha
    obtain ⟨hsb, wb⟩ := (hC N' N'' b).2 hb
    obtain ⟨sa, -, -⟩ := (hC N' N'' a).1 hsa
    obtain ⟨sb, -, -⟩ := (hC N' N'' b).1 hsb
    have hs := hasFourierExpansion_add sa sb
    have hw : ∀ j : ℕ, j ≤ 3 → WeightedAbsSummable j fun n => fourierCoeff a n + fourierCoeff b n :=
      fun j hj => weightedAbsSummable_add (wa j hj) (wb j hj)
    have hab : IsWeylSymbol fun q => a q + b q := ⟨_, hs, hw⟩
    have hn : AbsSummable fun n => fourierCoeff a n + fourierCoeff b n :=
      absSummable_of_weightedAbsSummable_zero (hw 0 (by norm_num))
    have hco := ((hC N' N'' _).1 ((hC N' N'' _).2 hab).1).2.2 _ hs hn
    exact ⟨hab, fun n => (congrFun hco n).symm, fun j hj =>
      weightedCoeffNorm_add_le hco.symm (wa j hj) (wb j hj)⟩
  · obtain ⟨hsa, wa⟩ := (hC N' N'' a).2 ha
    obtain ⟨sa, -, -⟩ := (hC N' N'' a).1 hsa
    have hs := hasFourierExpansion_smul c sa
    have hw : ∀ j : ℕ, j ≤ 3 → WeightedAbsSummable j fun n => c • fourierCoeff a n :=
      fun j hj => weightedAbsSummable_smul c (wa j hj)
    have hca : IsWeylSymbol fun q => c • a q := ⟨_, hs, hw⟩
    have hn : AbsSummable fun n => c • fourierCoeff a n :=
      absSummable_of_weightedAbsSummable_zero (hw 0 (by norm_num))
    have hco := ((hC N' N'' _).1 ((hC N' N'' _).2 hca).1).2.2 _ hs hn
    exact ⟨hca, fun n => (congrFun hco n).symm, fun j _ => weightedCoeffNorm_smul c hco.symm⟩
  · have hs : HasFourierExpansion (Pi.single 0 c : CoeffFamily N' N'') fun _ : AmbientSpace => c := by
      intro q
      have h := hasSum_single
        (f := fun n => fourierChar n q • (Pi.single 0 c : CoeffFamily N' N'') n)
        0 (fun n hn => by simp [Pi.single_eq_of_ne hn])
      simpa [fourierChar_zero] using h
    have hterm : ∀ j : ℕ, HasSum (fun n => Matrices.RectangularMatrix.opNormValue
        ((Pi.single 0 c : CoeffFamily N' N'') n) * latticeWeight n ^ j)
        (Matrices.RectangularMatrix.opNormValue c) := by
      intro j
      have hz : Matrices.RectangularMatrix.opNormValue (0 : Matrix (Fin N') (Fin N'') ℂ) = 0 := by
        rw [opNormValue_eq_norm, norm_zero]
      have h := hasSum_single (f := fun n => Matrices.RectangularMatrix.opNormValue
        ((Pi.single 0 c : CoeffFamily N' N'') n) * latticeWeight n ^ j) 0
        (fun n hn => by simp [Pi.single_eq_of_ne hn, hz])
      simpa [latticeWeight_zero] using h
    have hw : ∀ j : ℕ, j ≤ 3 → WeightedAbsSummable j (Pi.single 0 c : CoeffFamily N' N'') :=
      fun j _ => (hterm j).summable
    have hc : IsWeylSymbol fun _ : AmbientSpace => c := ⟨_, hs, hw⟩
    have hn : AbsSummable (Pi.single 0 c : CoeffFamily N' N'') :=
      absSummable_of_weightedAbsSummable_zero (hw 0 (by norm_num))
    have hco := ((hC N' N'' _).1 ((hC N' N'' _).2 hc).1).2.2 _ hs hn
    refine ⟨hc, ?_, fun n hn0 => ?_, fun j _ => ?_⟩
    · rw [← hco]
      simp
    · rw [← hco]
      exact Pi.single_eq_of_ne hn0 _
    · unfold weightedCoeffNorm
      rw [← hco]
      exact (hterm j).tsum_eq
  · obtain ⟨hs, hw⟩ := (hC N' N'' a).2 ha
    obtain ⟨hsum, hn, -⟩ := (hC N' N'' a).1 hs
    have ea : seriesSum (fourierCoeff a) = a := funext fun q => (hsum q).tsum_eq
    refine ⟨fun j _ => weightedCoeffNorm_nonneg j a,
      weightedCoeffNorm_mono (by norm_num) (hw 0 (by norm_num)) (hw 3 le_rfl),
      fun n => ?_, ?_, fun μ q i k => ?_⟩
    · have h₁ := Summable.le_tsum (hw 3 le_rfl) n (fun m _ => weightedTerm_nonneg 3 _ m)
      refine le_trans ?_ h₁
      exact le_mul_of_one_le_right (opNormValue_nonneg _) (one_le_pow₀ (one_le_latticeWeight n))
    · have h := (hS N' N'' _ hn).1.continuous_sum
      rwa [ea] at h
    · have tb : TermwiseDiffProps 1 (fourierCoeff a) :=
        (hS N' N'' _ hn).2.1 1 le_rfl (hw 1 (by norm_num))
      obtain ⟨D, hD, -⟩ := tb.partial_deriv μ
      rw [ea] at hD
      have e : coordDeriv μ a q i k = D q i k := (hD.2 q i k).deriv
      rw [e]
      exact hD.2 q i k
end Linear
section Products
variable [NeZero N'] [NeZero N''] [NeZero N''']
theorem weighted_conv_bound (hS : Matrices.FourierMatrixSeries.statement)
    {x : CoeffFamily N' N''} {y : CoeffFamily N'' N'''} (g : (Fin 4 → ℤ) → (Fin 4 → ℤ) → ℂ)
    {K : ℝ} (hK : 0 ≤ K) {j : ℕ}
    (hg : ∀ n m, ‖g n m‖ ≤ K * (latticeWeight n ^ j * latticeWeight m ^ j))
    (hx : WeightedAbsSummable j x) (hy : WeightedAbsSummable j y) :
    (Summable fun n => Matrices.RectangularMatrix.opNormValue
      (∑' p : SumPairs n, g p.1.1 p.1.2 • (x p.1.1 * y p.1.2))) ∧
    ∑' n, Matrices.RectangularMatrix.opNormValue
        (∑' p : SumPairs n, g p.1.1 p.1.2 • (x p.1.1 * y p.1.2)) ≤
      K * ((∑' n, Matrices.RectangularMatrix.opNormValue (x n) * latticeWeight n ^ j) *
        ∑' n, Matrices.RectangularMatrix.opNormValue (y n) * latticeWeight n ^ j) := by
  have normX : ∀ {M M' : ℕ} [NeZero M] [NeZero M'] (z : CoeffFamily M M') (n : Fin 4 → ℤ),
      Matrices.RectangularMatrix.opNormValue (((latticeWeight n ^ j : ℝ) : ℂ) • z n) =
        Matrices.RectangularMatrix.opNormValue (z n) * latticeWeight n ^ j := by
    intro M M' _ _ z n
    simp only [opNormValue_eq_norm, norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (pow_nonneg (latticeWeight_nonneg n) j)]
    ring
  set X : CoeffFamily N' N'' := fun n => ((latticeWeight n ^ j : ℝ) : ℂ) • x n with hXdef
  set Y : CoeffFamily N'' N''' := fun n => ((latticeWeight n ^ j : ℝ) : ℂ) • y n with hYdef
  have hX : AbsSummable X := by
    unfold AbsSummable
    simp only [hXdef, normX]
    exact hx
  have hY : AbsSummable Y := by
    unfold AbsSummable
    simp only [hYdef, normX]
    exact hy
  have P : ProductProps X Y := (hS N' N'' X hX).2.2 N''' Y hY
  have hb : ∀ (n : Fin 4 → ℤ) (p : SumPairs n), ‖g p.1.1 p.1.2 • (x p.1.1 * y p.1.2)‖ ≤
      K * (Matrices.RectangularMatrix.opNormValue (X p.1.1) *
        Matrices.RectangularMatrix.opNormValue (Y p.1.2)) := by
    intro n p
    have h₁ : ‖x p.1.1 * y p.1.2‖ ≤ ‖x p.1.1‖ * ‖y p.1.2‖ := Matrix.l2_opNorm_mul _ _
    simp only [hXdef, hYdef, normX, norm_smul, opNormValue_eq_norm]
    calc ‖g p.1.1 p.1.2‖ * ‖x p.1.1 * y p.1.2‖
        ≤ (K * (latticeWeight p.1.1 ^ j * latticeWeight p.1.2 ^ j)) * (‖x p.1.1‖ * ‖y p.1.2‖) :=
          mul_le_mul (hg _ _) h₁ (norm_nonneg _)
            (mul_nonneg hK (mul_nonneg (pow_nonneg (latticeWeight_nonneg _) j)
              (pow_nonneg (latticeWeight_nonneg _) j)))
      _ = _ := by ring
  have hin : ∀ n : Fin 4 → ℤ, Matrices.RectangularMatrix.opNormValue
      (∑' p : SumPairs n, g p.1.1 p.1.2 • (x p.1.1 * y p.1.2)) ≤
      K * ∑' p : SumPairs n, Matrices.RectangularMatrix.opNormValue (X p.1.1) *
        Matrices.RectangularMatrix.opNormValue (Y p.1.2) := by
    intro n
    rw [opNormValue_eq_norm]
    exact tsum_of_norm_bounded ((P.inner_norms_summable n).hasSum.mul_left K) (hb n)
  have htot := P.hasSum_norms.mul_left K
  have hsum : Summable fun n => Matrices.RectangularMatrix.opNormValue
      (∑' p : SumPairs n, g p.1.1 p.1.2 • (x p.1.1 * y p.1.2)) :=
    Summable.of_nonneg_of_le (fun n => opNormValue_nonneg _) hin htot.summable
  refine ⟨hsum, ?_⟩
  have hle := hasSum_le hin hsum.hasSum htot
  have e₁ : ∑' n, Matrices.RectangularMatrix.opNormValue (X n) =
      ∑' n, Matrices.RectangularMatrix.opNormValue (x n) * latticeWeight n ^ j :=
    tsum_congr fun n => normX x n
  have e₂ : ∑' n, Matrices.RectangularMatrix.opNormValue (Y n) =
      ∑' n, Matrices.RectangularMatrix.opNormValue (y n) * latticeWeight n ^ j :=
    tsum_congr fun n => normX y n
  rwa [e₁, e₂] at hle
theorem hasAbsSummableFourier_and_norm_le (hC : FourierCoeffsOfSymbol)
    {f : AmbientSpace → Matrix (Fin N') (Fin N''') ℂ} {c : CoeffFamily N' N'''} {B : ℝ}
    (hf : HasFourierExpansion c f)
    (hs : Summable fun n => Matrices.RectangularMatrix.opNormValue (c n))
    (hB : ∑' n, Matrices.RectangularMatrix.opNormValue (c n) ≤ B) :
    HasAbsSummableFourier f ∧ weightedCoeffNorm 0 f ≤ B := by
  have hcf : HasAbsSummableFourier f := ⟨c, hf, hs⟩
  refine ⟨hcf, ?_⟩
  have hco := ((hC N' N''' f).1 hcf).2.2 c hf hs
  unfold weightedCoeffNorm
  rw [← hco]
  simpa using hB
theorem pointwiseProducts (hS : Matrices.FourierMatrixSeries.statement)
    (hC : FourierCoeffsOfSymbol) (hP : MoyalProductBounds)
    (hB : SymbolBracketSeries)
    (hD : FluxZeroCalculus.Claim) :
    PointwiseProducts N' N'' N''' := by
  intro a a' ha ha'
  have hstar : moyalProduct 0 a a' = fun q => a q * a' q :=
    (hD 0 N' N'' N''').2.2.1 a a' ha ha'
  obtain ⟨-, -, hsym, -, hnorm⟩ := hP 0 N' N'' N''' a a' ha ha'
  rw [hstar] at hsym hnorm
  obtain ⟨-, wa⟩ := (hC N' N'' a).2 ha
  obtain ⟨-, wa'⟩ := (hC N'' N''' a').2 ha'
  obtain ⟨-, sb, ss⟩ := hB N' N'' N''' a a' ha ha'
  have n₁ : 0 ≤ weightedCoeffNorm 1 a' := weightedCoeffNorm_nonneg 1 a'
  have n₂ : 0 ≤ weightedCoeffNorm 2 a' := weightedCoeffNorm_nonneg 2 a'
  have n₃ : 0 ≤ weightedCoeffNorm 3 a := weightedCoeffNorm_nonneg 3 a
  have b₁ := weighted_conv_bound hS (x := fourierCoeff a) (y := fourierCoeff a')
    (fun n m => -(symplecticForm n m : ℂ)) (K := 2) (by norm_num) (j := 1)
    (fun n m => by
      have h := abs_symplecticForm_le n m
      rw [norm_neg, Complex.norm_intCast]
      simpa using h)
    (wa 1 (by norm_num)) (wa' 1 (by norm_num))
  have b₂ := weighted_conv_bound hS (x := fourierCoeff a) (y := fourierCoeff a')
    (fun n m => (symplecticForm n m : ℂ) ^ 2) (K := 4) (by norm_num) (j := 2)
    (fun n m => by
      have h := abs_symplecticForm_le n m
      rw [norm_pow, Complex.norm_intCast]
      calc |(symplecticForm n m : ℝ)| ^ 2 ≤ (2 * (latticeWeight n * latticeWeight m)) ^ 2 :=
            pow_le_pow_left₀ (abs_nonneg _) h 2
        _ = _ := by ring)
    (wa 2 (by norm_num)) (wa' 2 (by norm_num))
  have m₁ : weightedCoeffNorm 1 a * weightedCoeffNorm 1 a' ≤
      weightedCoeffNorm 3 a * weightedCoeffNorm 3 a' :=
    mul_le_mul (weightedCoeffNorm_mono (by norm_num) (wa 1 (by norm_num)) (wa 3 le_rfl))
      (weightedCoeffNorm_mono (by norm_num) (wa' 1 (by norm_num)) (wa' 3 le_rfl)) n₁ n₃
  have m₂ : weightedCoeffNorm 2 a * weightedCoeffNorm 2 a' ≤
      weightedCoeffNorm 3 a * weightedCoeffNorm 3 a' :=
    mul_le_mul (weightedCoeffNorm_mono (by norm_num) (wa 2 (by norm_num)) (wa 3 le_rfl))
      (weightedCoeffNorm_mono (by norm_num) (wa' 2 (by norm_num)) (wa' 3 le_rfl)) n₂ n₃
  have r₁ := hasAbsSummableFourier_and_norm_le hC sb b₁.1
    (B := 2 * weightedCoeffNorm 3 a * weightedCoeffNorm 3 a') (b₁.2.trans (by
      change 2 * (weightedCoeffNorm 1 a * weightedCoeffNorm 1 a') ≤ _
      linarith))
  have r₂ := hasAbsSummableFourier_and_norm_le hC ss b₂.1
    (B := 4 * weightedCoeffNorm 3 a * weightedCoeffNorm 3 a') (b₂.2.trans (by
      change 4 * (weightedCoeffNorm 2 a * weightedCoeffNorm 2 a') ≤ _
      linarith))
  exact ⟨hsym, hnorm, r₁.1, r₁.2, r₂.1, r₂.2⟩
end Products
def moyalPhase (φ : ℝ) (n m : Fin 4 → ℤ) : ℂ :=
  Complex.exp (Complex.I / 2 * (φ : ℂ) * (symplecticForm n m : ℂ))
theorem norm_moyalPhase (φ : ℝ) (n m : Fin 4 → ℤ) : ‖moyalPhase φ n m‖ = 1 := by
  have h : Complex.I / 2 * (φ : ℂ) * (symplecticForm n m : ℂ) =
      ((φ * (symplecticForm n m : ℝ) / 2 : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [moyalPhase, h, Complex.norm_exp_ofReal_mul_I]
def twistedConv (φ : ℝ) (x : CoeffFamily N' N'') (y : CoeffFamily N'' N''') (n : Fin 4 → ℤ) :
    Matrix (Fin N') (Fin N''') ℂ :=
  ∑' p : SumPairs n, moyalPhase φ p.1.1 p.1.2 • (x p.1.1 * y p.1.2)
section Star
variable [NeZero N'] [NeZero N''] [NeZero N''']
theorem summable_twistedConv_terms (hS : Matrices.FourierMatrixSeries.statement) (φ : ℝ)
    {x : CoeffFamily N' N''} {y : CoeffFamily N'' N'''} (hx : AbsSummable x) (hy : AbsSummable y)
    (n : Fin 4 → ℤ) :
    Summable fun p : SumPairs n => moyalPhase φ p.1.1 p.1.2 • (x p.1.1 * y p.1.2) := by
  have P : ProductProps x y := (hS N' N'' x hx).2.2 N''' y hy
  refine Summable.of_norm ?_
  have h := P.conv_terms_summable n
  simpa only [norm_smul, norm_moyalPhase, one_mul, opNormValue_eq_norm] using h
theorem twistedConv_add_left (hS : Matrices.FourierMatrixSeries.statement) (φ : ℝ)
    {x x' : CoeffFamily N' N''} {y : CoeffFamily N'' N'''} (hx : AbsSummable x)
    (hx' : AbsSummable x') (hy : AbsSummable y) (n : Fin 4 → ℤ) :
    twistedConv φ (fun n => x n + x' n) y n = twistedConv φ x y n + twistedConv φ x' y n := by
  have h := ((summable_twistedConv_terms hS φ hx hy n).hasSum.add
    (summable_twistedConv_terms hS φ hx' hy n).hasSum).tsum_eq
  rw [twistedConv, twistedConv, twistedConv, ← h]
  exact tsum_congr fun p => by rw [Matrix.add_mul, smul_add]
theorem twistedConv_add_right (hS : Matrices.FourierMatrixSeries.statement) (φ : ℝ)
    {x : CoeffFamily N' N''} {y y' : CoeffFamily N'' N'''} (hx : AbsSummable x)
    (hy : AbsSummable y) (hy' : AbsSummable y') (n : Fin 4 → ℤ) :
    twistedConv φ x (fun n => y n + y' n) n = twistedConv φ x y n + twistedConv φ x y' n := by
  have h := ((summable_twistedConv_terms hS φ hx hy n).hasSum.add
    (summable_twistedConv_terms hS φ hx hy' n).hasSum).tsum_eq
  rw [twistedConv, twistedConv, twistedConv, ← h]
  exact tsum_congr fun p => by rw [Matrix.mul_add, smul_add]
theorem twistedConv_smul_left (hS : Matrices.FourierMatrixSeries.statement) (φ : ℝ)
    (c : ℂ) {x : CoeffFamily N' N''} {y : CoeffFamily N'' N'''} (hx : AbsSummable x)
    (hy : AbsSummable y) (n : Fin 4 → ℤ) :
    twistedConv φ (fun n => c • x n) y n = c • twistedConv φ x y n := by
  have h := ((summable_twistedConv_terms hS φ hx hy n).hasSum.const_smul c).tsum_eq
  rw [twistedConv, twistedConv, ← h]
  exact tsum_congr fun p => by rw [Matrix.smul_mul, smul_comm]
theorem twistedConv_smul_right (hS : Matrices.FourierMatrixSeries.statement) (φ : ℝ)
    (c : ℂ) {x : CoeffFamily N' N''} {y : CoeffFamily N'' N'''} (hx : AbsSummable x)
    (hy : AbsSummable y) (n : Fin 4 → ℤ) :
    twistedConv φ x (fun n => c • y n) n = c • twistedConv φ x y n := by
  have h := ((summable_twistedConv_terms hS φ hx hy n).hasSum.const_smul c).tsum_eq
  rw [twistedConv, twistedConv, ← h]
  exact tsum_congr fun p => by rw [Matrix.mul_smul, smul_comm]
omit [NeZero N'] [NeZero N''] [NeZero N'''] in
theorem moyalCoeff_eq_twistedConv (φ : ℝ) (a : AmbientSpace → Matrix (Fin N') (Fin N'') ℂ)
    (a' : AmbientSpace → Matrix (Fin N'') (Fin N''') ℂ) :
    moyalCoeff φ a a' = twistedConv φ (fourierCoeff a) (fourierCoeff a') := rfl
omit [NeZero N'] [NeZero N''] [NeZero N'''] in
theorem moyalProduct_eq_add {φ : ℝ} {f : AmbientSpace → Matrix (Fin N') (Fin N'') ℂ}
    {g : AmbientSpace → Matrix (Fin N'') (Fin N''') ℂ} {s t : CoeffFamily N' N'''}
    {A B : AmbientSpace → Matrix (Fin N') (Fin N''') ℂ}
    (h : moyalCoeff φ f g = fun n => s n + t n)
    (hs : HasFourierExpansion s A) (ht : HasFourierExpansion t B) :
    moyalProduct φ f g = fun q => A q + B q := by
  funext q
  unfold moyalProduct
  rw [h]
  exact (hasFourierExpansion_add hs ht q).tsum_eq
omit [NeZero N'] [NeZero N''] [NeZero N'''] in
theorem moyalProduct_eq_smul {φ : ℝ} (c : ℂ) {f : AmbientSpace → Matrix (Fin N') (Fin N'') ℂ}
    {g : AmbientSpace → Matrix (Fin N'') (Fin N''') ℂ} {s : CoeffFamily N' N'''}
    {A : AmbientSpace → Matrix (Fin N') (Fin N''') ℂ}
    (h : moyalCoeff φ f g = fun n => c • s n) (hs : HasFourierExpansion s A) :
    moyalProduct φ f g = fun q => c • A q := by
  funext q
  unfold moyalProduct
  rw [h]
  exact (hasFourierExpansion_smul c hs q).tsum_eq
theorem moyalBilinear (hS : Matrices.FourierMatrixSeries.statement)
    (hC : FourierCoeffsOfSymbol) (hP : MoyalProductBounds) :
    MoyalBilinear N' N'' N''' := by
  intro φ a b a' b' c ha hb ha' hb'
  have sym := symbolSpace (N' := N') (N'' := N'') hS hC
  have sym' := symbolSpace (N' := N'') (N'' := N''') hS hC
  have summ : ∀ {M M' : ℕ} [NeZero M] [NeZero M'] {f : AmbientSpace → Matrix (Fin M) (Fin M') ℂ},
      IsWeylSymbol f → AbsSummable (fourierCoeff f) := fun {M M'} _ _ {f} hf =>
    ((hC M M' f).1 ((hC M M' f).2 hf).1).2.1
  have ca : AbsSummable (fourierCoeff a) := summ ha
  have cb : AbsSummable (fourierCoeff b) := summ hb
  have ca' : AbsSummable (fourierCoeff a') := summ ha'
  have cb' : AbsSummable (fourierCoeff b') := summ hb'
  have iaa := (hP φ N' N'' N''' a a' ha ha').2.1
  have iba := (hP φ N' N'' N''' b a' hb ha').2.1
  have iab := (hP φ N' N'' N''' a b' ha hb').2.1
  have eL : fourierCoeff (fun q => a q + b q) = fun n => fourierCoeff a n + fourierCoeff b n :=
    funext (sym.1 a b ha hb).2.1
  have eR : fourierCoeff (fun q => a' q + b' q) = fun n => fourierCoeff a' n + fourierCoeff b' n :=
    funext (sym'.1 a' b' ha' hb').2.1
  have sL : fourierCoeff (fun q => c • a q) = fun n => c • fourierCoeff a n :=
    funext (sym.2.1 c a ha).2.1
  have sR : fourierCoeff (fun q => c • a' q) = fun n => c • fourierCoeff a' n :=
    funext (sym'.2.1 c a' ha').2.1
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine moyalProduct_eq_add (funext fun n => ?_) iaa iba
    rw [moyalCoeff_eq_twistedConv, eL]
    exact twistedConv_add_left hS φ ca cb ca' n
  · refine moyalProduct_eq_add (funext fun n => ?_) iaa iab
    rw [moyalCoeff_eq_twistedConv, eR]
    exact twistedConv_add_right hS φ ca ca' cb' n
  · refine moyalProduct_eq_smul c (funext fun n => ?_) iaa
    rw [moyalCoeff_eq_twistedConv, sL]
    exact twistedConv_smul_left hS φ c ca ca' n
  · refine moyalProduct_eq_smul c (funext fun n => ?_) iaa
    rw [moyalCoeff_eq_twistedConv, sR]
    exact twistedConv_smul_right hS φ c ca ca' n
end Star
end SymbolAlgebra
theorem SymbolAlgebra.claim_of
    (hS : Matrices.FourierMatrixSeries.statement)
    (hC : FourierCoeffsOfSymbol) (hP : MoyalProductBounds)
    (hB : SymbolBracketSeries)
    (hD : FluxZeroCalculus.Claim) :
    SymbolAlgebra.Claim := by
  intro N' N'' N''' _ _ _
  exact ⟨SymbolAlgebra.absSummableLinear hC,
    SymbolAlgebra.symbolSpace hS hC,
    SymbolAlgebra.pointwiseProducts hS hC hP hB hD,
    SymbolAlgebra.moyalBilinear hS hC hP⟩
end Tower.MagneticWeyl
end YangMills.Construction
end
