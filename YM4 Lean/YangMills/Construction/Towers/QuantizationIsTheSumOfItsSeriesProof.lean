import YangMills.Construction.Towers.CoefficientsOfASymbol
import YangMills.Construction.Towers.QuantizationIsTheSumOfItsSeries
import Mathlib
set_option autoImplicit false
open Filter Topology
open YangMills.Construction.Tower.UnitLatticeL2 YangMills.Construction.Tower.UnitaryCombinations
open YangMills.Construction.OneLoopNotation
noncomputable section
namespace YangMills.Construction.Tower
open YangMills.Construction.Tower.MagneticWeyl in
theorem weylQuantHasSum_holds (hCoeffs : YangMills.Construction.Tower.FourierCoeffsOfSymbol)
    (hUnitary : YangMills.Construction.Tower.UnitaryOperatorSeriesClaim) :
    YangMills.Construction.Tower.WeylQuantHasSum := by
  intro L φ N' N'' _ _ a ha
  have hc : Summable fun k => YangMills.Construction.Matrices.RectangularMatrix.opNormValue (fourierCoeff a k) :=
    ((hCoeffs N' N'' a).1 ha).2.1
  obtain ⟨hBdd, hConv⟩ := hUnitary L N' N''
  have hU : ∀ k, IsUnitaryOp (magneticWeyl L φ k) :=
    fun k => magneticWeyl_isUnitary φ k
  obtain ⟨hOrder, hNorm⟩ := hConv (fourierCoeff a) (magneticWeyl L φ) hc hU
  have hTerms : Summable fun k =>
      matMulUnitaryOp (fourierCoeff a k) (magneticWeyl L φ k) :=
    Summable.of_norm_bounded hc fun k => (hBdd _ _ (hU k)).2
  obtain ⟨S, hS⟩ := hTerms
  have hInf : Infinite (Fin 4 → ℤ) := Pi.infinite_of_right
  obtain ⟨e⟩ : Nonempty (ℕ+ ≃ (Fin 4 → ℤ)) := nonempty_equiv_of_countable
  have hIcc : Tendsto (fun k : ℕ+ => Finset.Icc 1 k) atTop atTop :=
    tendsto_atTop_finset_of_monotone
      (fun _ _ h => Finset.Icc_subset_Icc_right h)
      (fun x => ⟨x, Finset.mem_Icc.mpr ⟨one_le, le_rfl⟩⟩)
  have hLim := (e.hasSum_iff.mpr hS).comp hIcc
  have hEq : weylQuant L φ a = S := tendsto_nhds_unique (hOrder e) hLim
  refine ⟨hEq ▸ hS, ?_⟩
  have hSum : weightedCoeffNorm 0 a = ∑' k, YangMills.Construction.Matrices.RectangularMatrix.opNormValue (fourierCoeff a k) := by
    simp [weightedCoeffNorm]
  rw [hSum]
  exact hNorm
end YangMills.Construction.Tower
end
