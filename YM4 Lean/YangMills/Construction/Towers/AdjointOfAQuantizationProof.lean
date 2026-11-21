import YangMills.Construction.Matrices.NormOfAProductAndOfAnAdjointMatrix
import YangMills.Construction.Towers.AdjointOfAQuantization
import YangMills.Construction.Towers.AlgebraOfMatricesTimesUnitaryOperators
import YangMills.Construction.Towers.CoefficientsOfASymbol
import YangMills.Construction.Towers.QuantizationIsTheSumOfItsSeries
import YangMills.Construction.Towers.RelationsOfTheWeylOperators
import Mathlib
set_option autoImplicit false
open YangMills.Construction.Tower.UnitLatticeL2 YangMills.Construction.Tower.UnitaryCombinations YangMills.Construction.OneLoopNotation
noncomputable section
namespace YangMills.Construction.Tower
open MagneticWeyl
private theorem conj_fourierChar_neg (n : Fin 4 → ℤ) (q : InfiniteLattice.AmbientSpace) :
    (starRingEnd ℂ) (MagneticWeyl.fourierChar (-n) q) = MagneticWeyl.fourierChar n q := by
  simp only [MagneticWeyl.fourierChar, MagneticWeyl.intDot, PeriodicOperators.bilinDot,
    PeriodicOperators.toComplexVec, PeriodicOperators.castVec]
  rw [← Complex.exp_conj]
  congr 1
  simp [map_sum, Finset.sum_neg_distrib]
private theorem euclidNormVec_castVec_neg (n : Fin 4 → ℤ) :
    TorusMetric.euclidNormVec (PeriodicOperators.castVec (-n)) =
      TorusMetric.euclidNormVec (PeriodicOperators.castVec n) := by
  simp [TorusMetric.euclidNormVec, PeriodicOperators.castVec]
theorem weylQuantAdjoint_holds
    (hSum : WeylQuantHasSum)
    (hAlg : MatMulUnitaryOpAlgebra)
    (hRel : MagneticWeylRelations)
    (hCoef : FourierCoeffsOfSymbol)
    (hNorm : Matrices.RectangularMatrix.NormOfProductAndAdjoint.Properties) :
    WeylQuantAdjoint := by
  intro L φ N' N'' _ _ a ha
  have hsc : MagneticWeyl.HasAbsSummableFourier a := ((hCoef N' N'' a).2 ha).1
  have hweight := ((hCoef N' N'' a).2 ha).2
  obtain ⟨hchar, hsumm, -⟩ := (hCoef N' N'' a).1 hsc
  let c' : (Fin 4 → ℤ) → Matrix (Fin N'') (Fin N') ℂ :=
    fun n => (MagneticWeyl.fourierCoeff a (-n)).conjTranspose
  have hnorm : ∀ n, Matrices.RectangularMatrix.opNormValue (c' n) =
      Matrices.RectangularMatrix.opNormValue (MagneticWeyl.fourierCoeff a (-n)) :=
    fun n => (hNorm N' N'' N'' (MagneticWeyl.fourierCoeff a (-n)) 0 0).2
  have hcharb : MagneticWeyl.HasFourierExpansion c' (MagneticWeyl.pointwiseAdjoint a) := by
    intro q
    have h1 := (hchar q).map (Matrix.conjTransposeAddEquiv (Fin N') (Fin N'') ℂ)
      (continuous_id.matrix_conjTranspose)
    have h2 := (Equiv.neg (Fin 4 → ℤ)).hasSum_iff.mpr h1
    have e : (fun n => MagneticWeyl.fourierChar n q • c' n) =
        (⇑(Matrix.conjTransposeAddEquiv (Fin N') (Fin N'') ℂ) ∘
          fun n => MagneticWeyl.fourierChar n q • MagneticWeyl.fourierCoeff a n) ∘
            ⇑(Equiv.neg (Fin 4 → ℤ)) := by
      funext n
      simp [c', Matrix.conjTranspose_smul, conj_fourierChar_neg]
    rw [e]
    exact h2
  have hsumm' : Summable fun n => Matrices.RectangularMatrix.opNormValue (c' n) := by
    have h := (Equiv.neg (Fin 4 → ℤ)).summable_iff.mpr hsumm
    exact h.congr fun n => by simp [hnorm]
  have hbsym : MagneticWeyl.IsWeylSymbol (MagneticWeyl.pointwiseAdjoint a) := by
    refine ⟨c', hcharb, fun j hj => ?_⟩
    have h := (Equiv.neg (Fin 4 → ℤ)).summable_iff.mpr (hweight j hj)
    refine h.congr fun n => ?_
    simp [hnorm, euclidNormVec_castVec_neg]
  have hbsc : MagneticWeyl.HasAbsSummableFourier (MagneticWeyl.pointwiseAdjoint a) :=
    ⟨c', hcharb, hsumm'⟩
  have hcoef : c' = MagneticWeyl.fourierCoeff (MagneticWeyl.pointwiseAdjoint a) :=
    ((hCoef N'' N' (MagneticWeyl.pointwiseAdjoint a)).1 hbsc).2.2 c' hcharb hsumm'
  refine ⟨hbsym, ?_⟩
  have hSa := (hSum L φ N' N'' a hsc).1
  have hSb := (hSum L φ N'' N' (MagneticWeyl.pointwiseAdjoint a) hbsc).1
  rw [← hcoef] at hSb
  have hadj : ∀ n, opAdjoint
      (matMulUnitaryOp (MagneticWeyl.fourierCoeff a n) (MagneticWeyl.magneticWeyl L φ n)) =
      matMulUnitaryOp (MagneticWeyl.fourierCoeff a n).conjTranspose
        (MagneticWeyl.magneticWeyl L φ (-n)) :=
    fun n => (hAlg L N' N'' (MagneticWeyl.magneticWeyl L φ n)
      (MagneticWeyl.magneticWeyl_isUnitary φ n)).2.2.1 _
      (MagneticWeyl.magneticWeyl_isUnitary φ (-n)) (hRel L φ n 0).2.2.1 _
  have h1 := hSa.map
    (ContinuousLinearMap.adjoint :
      BddOpBetween (VectorL2 L N'') (VectorL2 L N') ≃ₗᵢ⋆[ℂ]
        BddOpBetween (VectorL2 L N') (VectorL2 L N''))
    (LinearIsometryEquiv.continuous _)
  have h2 := (Equiv.neg (Fin 4 → ℤ)).hasSum_iff.mpr h1
  have h3 : HasSum (fun n => matMulUnitaryOp (c' n) (MagneticWeyl.magneticWeyl L φ n))
      (opAdjoint (MagneticWeyl.weylQuant L φ a)) := by
    have e : (fun n => matMulUnitaryOp (c' n) (MagneticWeyl.magneticWeyl L φ n)) =
        fun n => opAdjoint
          (matMulUnitaryOp (MagneticWeyl.fourierCoeff a (-n))
            (MagneticWeyl.magneticWeyl L φ (-n))) := by
      funext n
      have h := hadj (-n)
      rw [neg_neg] at h
      exact h.symm
    rw [e]
    exact h2
  exact h3.unique hSb
end YangMills.Construction.Tower
end
