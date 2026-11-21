import YangMills.Construction.EuclideanFunctionals.AgreementOfTheTwoSettingsOfTuples
import YangMills.Construction.EuclideanFunctionals.InsertionOfTheSystemOfAReconstruction
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.EuclideanFunctionals.SystemInsertion
open DefinitionComparison
theorem singleComplex_eq_singleComponent (hs : TwoSettings.TwoSettingsAgree) {h : R4 → ℂ}
    (hh : h ∈ C1c ℂ) : singleComplex h = singleComponent h := by
  obtain ⟨-, -, he, -⟩ := hs
  exact (he 1 (fun _ => h)
    ⟨le_rfl, fun _ => hh, fun k l hkl => (hkl (Subsingleton.elim k l)).elim⟩).1
theorem holds (hs : TwoSettings.TwoSettingsAgree) : Holds := by
  intro m S σ s c F A h hc
  refine ⟨rfl, ?_, ?_⟩
  · exact congrArg norm (s.corresponds.cls_eq _)
  · rw [stripInsertion, insertion, freeMul3, flipConj, singleComplex_eq_singleComponent hs hc.mem_C1c]
end YangMills.Construction.EuclideanFunctionals.SystemInsertion
