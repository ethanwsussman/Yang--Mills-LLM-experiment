import YangMills.Construction.Matrices.SeriesWithSummableMatrixCoefficients
import YangMills.Construction.Towers.CoefficientsOfASymbol
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Tower.UnitLatticeL2 Tower.UnitaryCombinations OneLoopNotation
open InfiniteLattice (AmbientSpace)
open PeriodicOperators (torusAverage castVec toComplexVec bilinDot)
namespace Tower.FourierCoeffsProof
open MagneticWeyl Matrices.FourierMatrixSeries
theorem character_neg (n : Fin 4 → ℤ) (q : AmbientSpace) :
    character (-n) q = Complex.exp (-(Complex.I * MagneticWeyl.intDot n q)) := by
  have h : bilinDot (toComplexVec (castVec (-n))) (toComplexVec q) = -MagneticWeyl.intDot n q := by
    simp only [MagneticWeyl.intDot, bilinDot, toComplexVec, castVec, Pi.neg_apply, Int.cast_neg,
      Complex.ofReal_neg, neg_mul, Finset.sum_neg_distrib]
  simp only [character, h, mul_neg]
theorem fourierCoeff_eq_of_summable (hS : Matrices.FourierMatrixSeries.statement)
    {N' N'' : ℕ} [NeZero N'] [NeZero N''] {a : AmbientSpace → Matrix (Fin N') (Fin N'') ℂ}
    {c : (Fin 4 → ℤ) → Matrix (Fin N') (Fin N'') ℂ} (hsum : HasFourierExpansion c a)
    (hc : Summable fun n => Matrices.RectangularMatrix.opNormValue (c n)) : fourierCoeff a = c := by
  have hU : AbsSummableProps c := (hS N' N'' c hc).1
  have ha : a = seriesSum c := funext fun q => ((hsum q).tsum_eq).symm
  funext n
  ext i k
  rw [hU.coeff_eq_average n i k]
  simp only [MagneticWeyl.fourierCoeff, Matrix.of_apply, character_neg, ha]
theorem fourierCoeffsOfSymbol_holds (hS : Matrices.FourierMatrixSeries.statement) :
    FourierCoeffsOfSymbol := by
  intro N' N'' _ _ a
  refine ⟨?_, ?_⟩
  · rintro ⟨c, hsum, hc⟩
    have h := fourierCoeff_eq_of_summable hS hsum hc
    refine ⟨by rw [h]; exact hsum, by rw [h]; exact hc, fun c' hsum' hc' => ?_⟩
    exact (fourierCoeff_eq_of_summable hS hsum' hc').symm
  · rintro ⟨c, hsum, hw⟩
    have hc : Summable fun n => Matrices.RectangularMatrix.opNormValue (c n) := by
      simpa using hw 0 (by norm_num)
    have h := fourierCoeff_eq_of_summable hS hsum hc
    refine ⟨⟨c, hsum, hc⟩, fun j hj => ?_⟩
    rw [h]
    exact hw j hj
end Tower.FourierCoeffsProof
end YangMills.Construction
end
