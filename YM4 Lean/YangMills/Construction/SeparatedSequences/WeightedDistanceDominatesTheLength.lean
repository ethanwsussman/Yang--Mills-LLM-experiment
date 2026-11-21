import YangMills.Construction.SeparatedSequences.ClassesFramesNormsAndKernels
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Set PeriodicLattice PeriodicLattice.DirichletOperators TorusMetric
namespace SeparatedClasses
def LOneDistLeChainDist : Prop :=
  ∀ (C : ClassData), C.L ≤ C.blockSize → ∀ Ω ∈ C.separatedClass,
    ∀ p p' : C.Point,
      ENNReal.ofReal ((C.coarseMesh (C.lastNonempty Ω))⁻¹ * C.lOneDist p p') ≤
        C.chainDist Ω p p'
end SeparatedClasses
end YangMills.Construction
end
