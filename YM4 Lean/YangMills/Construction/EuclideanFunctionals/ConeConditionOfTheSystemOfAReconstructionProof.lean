import YangMills.Construction.EuclideanFunctionals.ConeConditionOfTheSystemOfAReconstruction
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.EuclideanFunctionals.SystemConeCondition
open DefinitionComparison
open YangMills.Construction.SettingsComparison (IsSameMeasure euclideanToCoords)
theorem dot3_basisVec (j : Fin 3) (q : Fin 3 → ℝ) :
    SpectralPoint.dot3 (SpectralPoint.basisVec j) q = q j := by
  simp [SpectralPoint.dot3, SpectralPoint.basisVec, Pi.single_apply]
theorem euclideanToCoords_energyBelowMom (j : Fin 3) :
    euclideanToCoords (energyBelowMom j) =
      SpectralPoint.belowAbsMomentum (SpectralPoint.basisVec j) := by
  refine Subtype.ext ?_
  ext y
  simp [euclideanToCoords, energyBelowMom, SpectralPoint.belowAbsMomentum, dot3_basisVec,
    SpectralPoint.energyOf, SpectralPoint.momentumOf, energyCoord, momCoord]
theorem euclideanToCoords_momentumPyramid :
    euclideanToCoords momentumPyramid = SpectralPoint.pyramid := by
  refine Subtype.ext ?_
  ext y
  simp [euclideanToCoords, momentumPyramid, SpectralPoint.pyramid, SpectralPoint.energyOf,
    SpectralPoint.momentumOf, energyCoord, momCoord]
theorem holds : Holds := by
  intro m S σ s
  have hm : IsSameMeasure σ.jointMeasure s.toSymm.jointSpecMeasure :=
    s.corresponds.measure_eq
  have hj : ∀ j : Fin 3, σ.HamGeAbsMomentum j ↔ s.toSymm.EnergyBoundsMom j := by
    intro j
    have hv := hm (energyBelowMom j)
    rw [euclideanToCoords_energyBelowMom] at hv
    constructor
    · intro h
      have h' : σ.jointMeasure
          (SpectralPoint.belowAbsMomentum (SpectralPoint.basisVec j)) = 0 := h
      exact show s.toSymm.jointSpecMeasure (energyBelowMom j) = 0 from by
        refine LinearMap.ext fun ψ => ?_
        have hψ := congrFun hv ψ
        rw [h'] at hψ
        simpa using hψ
    · intro h
      have h' : s.toSymm.jointSpecMeasure (energyBelowMom j) = 0 := h
      refine ContinuousLinearMap.ext fun ψ => ?_
      have hψ := congrFun hv ψ
      rw [h'] at hψ
      simpa using hψ.symm
  exact ⟨hj, hj 0, euclideanToCoords_momentumPyramid⟩
end YangMills.Construction.EuclideanFunctionals.SystemConeCondition
