import YangMills.Construction.SeparatedSequences.BoundOfTheDifferencesOfTheExtensionKernelAtATopAndAnExpansionProof
import YangMills.Construction.SeparatedSequences.KernelBoundOfTheInverseAtTheSitesOfTheRowsProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Set PeriodicLattice PeriodicLattice.DirichletOperators
namespace SeparatedClasses
namespace InverseAvgOneGreenKernel
open SingleSequence
theorem scaledDist_nonneg {D : GeneralTorus.ScaleData} (B : GeneralTorus.SeparatedChain D)
    (x x' : D.Space) : 0 ≤ B.scaledDist x x' := by apply _root_.YangMills.Construction.SeparatedClasses.ExtensionKernel.scaledDist_nonneg <;> assumption
end InverseAvgOneGreenKernel
end SeparatedClasses
end YangMills.Construction
end
