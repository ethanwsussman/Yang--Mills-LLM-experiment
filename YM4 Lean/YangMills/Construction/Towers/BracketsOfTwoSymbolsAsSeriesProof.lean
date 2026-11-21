import YangMills.Construction.Matrices.SeriesWithSummableMatrixCoefficients
import YangMills.Construction.Towers.AsymptoticsOfTheMassiveCoefficientProof
import YangMills.Construction.Towers.BracketsOfTwoSymbolsAsSeries
import YangMills.Construction.Towers.CoefficientsOfASymbol
import Mathlib
set_option autoImplicit false
open YangMills.Construction.Tower.UnitLatticeL2 YangMills.Construction.Tower.UnitaryCombinations
open YangMills.Construction.OneLoopNotation
open YangMills.Construction.InfiniteLattice (AmbientSpace)
open YangMills.Construction.PeriodicOperators (castVec toComplexVec bilinDot)
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.Tower
namespace BracketExpansion
open YangMills.Construction.Tower.MagneticWeyl YangMills.Construction.Matrices.FourierMatrixSeries
theorem opNormValue_eq_norm {M M' : ℕ} [NeZero M] [NeZero M'] (X : Matrix (Fin M) (Fin M') ℂ) :
    YangMills.Construction.Matrices.RectangularMatrix.opNormValue X = ‖X‖ :=
  (Matrix.l2_opNorm_def X).symm
theorem norm_fourierChar (k : Fin 4 → ℤ) (q : AmbientSpace) : ‖fourierChar k q‖ = 1 := by apply _root_.YangMills.Construction.Tower.Massive.CoefficientAsymptoticsProof.norm_fourierChar <;> assumption
variable {N' N'' N''' : ℕ}
theorem hasFourierExpansion_seriesSum [NeZero N'] [NeZero N''] {c : CoeffFamily N' N''}
    (hc : AbsSummable c) : HasFourierExpansion c (seriesSum c) := by
  intro q
  have hs : Summable fun k => fourierChar k q • c k := by
    refine Summable.of_norm ?_
    simp only [norm_smul, norm_fourierChar, one_mul, ← opNormValue_eq_norm]
    exact hc
  exact hs.hasSum
theorem coordDeriv_eq {f D : AmbientSpace → Matrix (Fin N') (Fin N'') ℂ} {μ : Fin 4}
    (h : HasContinuousPartialDeriv μ f D) : coordDeriv μ f = D := by
  funext q
  ext i j
  exact (h.2 q i j).deriv
theorem hasFourierExpansion_mul [NeZero N'] [NeZero N''] [NeZero N''']
    {c : CoeffFamily N' N''} {d : CoeffFamily N'' N'''} (hP : ProductProps c d) :
    HasFourierExpansion (coeffConv c d) fun q => seriesSum c q * seriesSum d q := by
  intro q
  change HasSum _ (seriesSum c q * seriesSum d q)
  rw [hP.sum_mul_sum q]
  exact hasFourierExpansion_seriesSum hP.conv_summable q
theorem summable_conv_terms [NeZero N'] [NeZero N''] [NeZero N''']
    {c : CoeffFamily N' N''} {d : CoeffFamily N'' N'''} (hP : ProductProps c d)
    (k : Fin 4 → ℤ) : Summable fun p : SumPairs k => c p.1.1 * d p.1.2 := by
  refine Summable.of_norm ?_
  simpa only [opNormValue_eq_norm] using hP.conv_terms_summable k
def derivFactor (w : List (Fin 4)) (k : Fin 4 → ℤ) : ℂ := (w.map fun μ => Complex.I * (k μ : ℂ)).prod
theorem derivCoeffs_mul (w w' : List (Fin 4)) (A : CoeffFamily N' N'')
    (B : CoeffFamily N'' N''') (k l : Fin 4 → ℤ) :
    derivCoeffs w A k * derivCoeffs w' B l = (derivFactor w k * derivFactor w' l) • (A k * B l) := by
  simp only [derivCoeffs, derivFactor, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  exact congrArg (· • (A k * B l)) (mul_comm _ _)
theorem poissonBracket_term (A : CoeffFamily N' N'') (B : CoeffFamily N'' N''')
    (k l : Fin 4 → ℤ) :
    derivCoeffs [0] A k * derivCoeffs [1] B l -
        derivCoeffs [1] A k * derivCoeffs [0] B l =
      (-(symplecticForm k l : ℂ)) • (A k * B l) := by
  rw [derivCoeffs_mul, derivCoeffs_mul, ← sub_smul]
  congr 1
  simp only [derivFactor, symplecticForm, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  push_cast
  linear_combination ((k 0 : ℂ) * (l 1 : ℂ) - (k 1 : ℂ) * (l 0 : ℂ)) * Complex.I_mul_I
theorem secondPoissonBracket_term (A : CoeffFamily N' N'') (B : CoeffFamily N'' N''')
    (k l : Fin 4 → ℤ) :
    derivCoeffs [0, 0] A k * derivCoeffs [1, 1] B l -
        (2 : ℂ) • (derivCoeffs [0, 1] A k * derivCoeffs [0, 1] B l) +
        derivCoeffs [1, 1] A k * derivCoeffs [0, 0] B l =
      ((symplecticForm k l : ℂ) ^ 2) • (A k * B l) := by
  rw [derivCoeffs_mul, derivCoeffs_mul, derivCoeffs_mul, smul_smul, ← sub_smul,
    ← add_smul]
  congr 1
  simp only [derivFactor, symplecticForm, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  push_cast
  linear_combination
    (-((k 0 : ℂ) * (l 1 : ℂ) - (k 1 : ℂ) * (l 0 : ℂ)) ^ 2 * (1 - Complex.I * Complex.I)) *
      Complex.I_mul_I
theorem fourierExpansions_of_sums (hS : YangMills.Construction.Matrices.FourierMatrixSeries.statement)
    [NeZero N'] [NeZero N''] [NeZero N''']
    (A : CoeffFamily N' N'') (B : CoeffFamily N'' N''')
    (hA : AbsSummable A) (hB : AbsSummable B)
    (hA3 : WeightedAbsSummable 3 A) (hB3 : WeightedAbsSummable 3 B) :
    HasFourierExpansion (fun k => ∑' p : SumPairs k, A p.1.1 * B p.1.2)
      (fun q => seriesSum A q * seriesSum B q) ∧
    HasFourierExpansion
      (fun k => ∑' p : SumPairs k, (-(symplecticForm p.1.1 p.1.2 : ℂ)) • (A p.1.1 * B p.1.2))
      (poissonBracket (seriesSum A) (seriesSum B)) ∧
    HasFourierExpansion
      (fun k => ∑' p : SumPairs k, ((symplecticForm p.1.1 p.1.2 : ℂ) ^ 2) • (A p.1.1 * B p.1.2))
      (secondPoissonBracket (seriesSum A) (seriesSum B)) := by
  have tA : TermwiseDiffProps 3 A := (hS N' N'' A hA).2.1 3 (by norm_num) hA3
  have tB : TermwiseDiffProps 3 B := (hS N'' N''' B hB).2.1 3 (by norm_num) hB3
  have P : ∀ w w' : List (Fin 4), w.length ≤ 3 → w'.length ≤ 3 →
      ProductProps (derivCoeffs w A) (derivCoeffs w' B) := fun w w' hw hw' =>
    (hS N' N'' _ (tA.higher_summable w hw).1).2.2 N''' _ (tB.higher_summable w' hw').1
  have dA : ∀ (μ : Fin 4) (w : List (Fin 4)), w.length < 3 →
      coordDeriv μ (seriesSum (derivCoeffs w A)) = seriesSum (derivCoeffs (μ :: w) A) :=
    fun μ w hw => coordDeriv_eq (tA.higher_partial_deriv w hw μ)
  have dB : ∀ (μ : Fin 4) (w : List (Fin 4)), w.length < 3 →
      coordDeriv μ (seriesSum (derivCoeffs w B)) = seriesSum (derivCoeffs (μ :: w) B) :=
    fun μ w hw => coordDeriv_eq (tB.higher_partial_deriv w hw μ)
  have dA1 : ∀ μ : Fin 4, coordDeriv μ (seriesSum A) = seriesSum (derivCoeffs [μ] A) := by
    intro μ
    have h := dA μ [] (by simp)
    rwa [derivCoeffs_nil] at h
  have dB1 : ∀ μ : Fin 4, coordDeriv μ (seriesSum B) = seriesSum (derivCoeffs [μ] B) := by
    intro μ
    have h := dB μ [] (by simp)
    rwa [derivCoeffs_nil] at h
  have dA2 : ∀ μ ν : Fin 4, coordDeriv μ (coordDeriv ν (seriesSum A)) =
      seriesSum (derivCoeffs [μ, ν] A) := by
    intro μ ν
    rw [dA1]
    exact dA μ [ν] (by simp)
  have dB2 : ∀ μ ν : Fin 4, coordDeriv μ (coordDeriv ν (seriesSum B)) =
      seriesSum (derivCoeffs [μ, ν] B) := by
    intro μ ν
    rw [dB1]
    exact dB μ [ν] (by simp)
  refine ⟨?_, ?_, ?_⟩
  · have h := hasFourierExpansion_mul (P [] [] (by simp) (by simp))
    simp only [derivCoeffs_nil] at h
    exact h
  · have P₁ := P [0] [1] (by simp) (by simp)
    have P₂ := P [1] [0] (by simp) (by simp)
    intro q
    have hq := (hasFourierExpansion_mul P₁ q).sub (hasFourierExpansion_mul P₂ q)
    have ht : (fun k => fourierChar k q • ∑' p : SumPairs k,
        (-(symplecticForm p.1.1 p.1.2 : ℂ)) • (A p.1.1 * B p.1.2)) =
        fun k => fourierChar k q • coeffConv (derivCoeffs [0] A) (derivCoeffs [1] B) k -
          fourierChar k q • coeffConv (derivCoeffs [1] A) (derivCoeffs [0] B) k := by
      funext k
      rw [← smul_sub]
      congr 1
      have h := ((summable_conv_terms P₁ k).hasSum).sub ((summable_conv_terms P₂ k).hasSum)
      simp only [poissonBracket_term] at h
      exact h.tsum_eq
    have hb : poissonBracket (seriesSum A) (seriesSum B) q =
        seriesSum (derivCoeffs [0] A) q * seriesSum (derivCoeffs [1] B) q -
          seriesSum (derivCoeffs [1] A) q * seriesSum (derivCoeffs [0] B) q := by
      simp only [poissonBracket, dA1, dB1]
    rw [ht, hb]
    exact hq
  · have P₁ := P [0, 0] [1, 1] (by simp) (by simp)
    have P₂ := P [0, 1] [0, 1] (by simp) (by simp)
    have P₃ := P [1, 1] [0, 0] (by simp) (by simp)
    intro q
    have hq := ((hasFourierExpansion_mul P₁ q).sub
      ((hasFourierExpansion_mul P₂ q).const_smul (2 : ℂ))).add (hasFourierExpansion_mul P₃ q)
    have ht : (fun k => fourierChar k q • ∑' p : SumPairs k,
        ((symplecticForm p.1.1 p.1.2 : ℂ) ^ 2) • (A p.1.1 * B p.1.2)) =
        fun k => fourierChar k q • coeffConv (derivCoeffs [0, 0] A) (derivCoeffs [1, 1] B) k -
          (2 : ℂ) • fourierChar k q •
            coeffConv (derivCoeffs [0, 1] A) (derivCoeffs [0, 1] B) k +
          fourierChar k q • coeffConv (derivCoeffs [1, 1] A) (derivCoeffs [0, 0] B) k := by
      funext k
      rw [smul_comm (2 : ℂ), ← smul_sub, ← smul_add]
      congr 1
      have h := (((summable_conv_terms P₁ k).hasSum).sub
        (((summable_conv_terms P₂ k).hasSum).const_smul (2 : ℂ))).add ((summable_conv_terms P₃ k).hasSum)
      simp only [secondPoissonBracket_term] at h
      exact h.tsum_eq
    have hb : secondPoissonBracket (seriesSum A) (seriesSum B) q =
        seriesSum (derivCoeffs [0, 0] A) q * seriesSum (derivCoeffs [1, 1] B) q -
          (2 : ℂ) • (seriesSum (derivCoeffs [0, 1] A) q * seriesSum (derivCoeffs [0, 1] B) q) +
          seriesSum (derivCoeffs [1, 1] A) q * seriesSum (derivCoeffs [0, 0] B) q := by
      simp only [secondPoissonBracket, dA2, dB2]
    rw [ht, hb]
    exact hq
end BracketExpansion
open YangMills.Construction.Tower.MagneticWeyl YangMills.Construction.Matrices.FourierMatrixSeries
  YangMills.Construction.Tower.BracketExpansion in
theorem symbolBracketSeries_holds (hC : YangMills.Construction.Tower.FourierCoeffsOfSymbol)
    (hS : YangMills.Construction.Matrices.FourierMatrixSeries.statement) :
    YangMills.Construction.Tower.SymbolBracketSeries := by
  intro N' N'' N''' _ _ _ a b ha hb
  obtain ⟨hsa, hwa⟩ := (hC N' N'' a).2 ha
  obtain ⟨hsb, hwb⟩ := (hC N'' N''' b).2 hb
  obtain ⟨hca, hna, -⟩ := (hC N' N'' a).1 hsa
  obtain ⟨hcb, hnb, -⟩ := (hC N'' N''' b).1 hsb
  have ea : seriesSum (fourierCoeff a) = a := funext fun q => (hca q).tsum_eq
  have eb : seriesSum (fourierCoeff b) = b := funext fun q => (hcb q).tsum_eq
  have h := fourierExpansions_of_sums hS (fourierCoeff a) (fourierCoeff b) hna hnb (hwa 3 le_rfl) (hwb 3 le_rfl)
  rw [ea, eb] at h
  exact h
end YangMills.Construction.Tower
end
