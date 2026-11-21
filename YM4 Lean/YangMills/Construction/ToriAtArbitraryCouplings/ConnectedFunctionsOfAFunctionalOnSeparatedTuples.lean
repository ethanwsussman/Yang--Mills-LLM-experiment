import YangMills.Construction.ReflectionPositivity.CentredObservableAndFunctionals
import YangMills.Construction.ReflectionPositivity.IsometriesCentringTuplesAndTheTwoFunctionals
import YangMills.Construction.SourcesAndGluing.LogarithmDerivativesPartitionsCumulantsAndConnectedFunctions
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.AxisMirror.Ambient
variable {D : MirrorData} {E : Ambient}
def subSeparated {n : ℕ} (X : separatedN D E n) (J : Finset (Fin X.1.length)) :
    separatedAll D E :=
  ⟨subList X.1 J, separatedN_subset_separatedAll D E J.card (subList_mem_separatedN X.2.2 J)⟩
def connectedOfSeparated (σ : separatedAll D E → ℝ) (n : ℕ)
    (X : separatedN D E n) : ℝ :=
  ∑ π : SetPartition.PartitionsFin X.1.length,
    (-1 : ℝ) ^ (SourcesAndGluing.blockCount π - 1) *
      ((SourcesAndGluing.blockCount π - 1).factorial : ℝ) *
      ∏ J ∈ π.parts, σ (subSeparated X J)
end YangMills.Construction.ReflectionPositivity.AxisMirror.Ambient
end
