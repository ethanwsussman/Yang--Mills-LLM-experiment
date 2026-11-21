import YangMills.Construction.EuclideanFunctionals.MeasureOfTheSystemOfAReconstruction
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.EuclideanFunctionals.ReconSystemMeasure
open DefinitionComparison
open YangMills.Construction.SettingsComparison (IsSameMeasure euclideanToCoords)
theorem reconSystemMeasuresAgree_holds : ReconSystemMeasuresAgree := by
  intro m S σ s
  have hm : IsSameMeasure σ.jointMeasure s.toSymm.jointSpecMeasure :=
    s.corresponds.measure_eq
  refine ⟨rfl, hm, fun B => ?_⟩
  have hc : euclideanToCoords B.compl =
      ⟨(euclideanToCoords B).1ᶜ, (euclideanToCoords B).2.compl⟩ :=
    Subtype.ext (by
      ext y
      simp [euclideanToCoords, YangMills.Construction.EuclideanSpectral.BorelSubset.compl])
  have hv := hm B.compl
  rw [hc] at hv
  constructor
  · intro h
    have h' : s.toSymm.jointSpecMeasure B.compl = 0 := h
    refine ContinuousLinearMap.ext fun ψ => ?_
    have hψ := congrFun hv ψ
    rw [h'] at hψ
    simpa using hψ.symm
  · intro h
    have h' : σ.jointMeasure ⟨(euclideanToCoords B).1ᶜ, (euclideanToCoords B).2.compl⟩ = 0 := h
    refine LinearMap.ext fun ψ => ?_
    have hψ := congrFun hv ψ
    rw [h'] at hψ
    simpa using hψ
end YangMills.Construction.EuclideanFunctionals.ReconSystemMeasure
