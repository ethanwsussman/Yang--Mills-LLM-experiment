import YangMills.Construction.SeparatedSequences.ClassesFramesNormsAndKernels
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.SeparatedClasses.ClassData
variable (C : ClassData)
def supDist (x x' : C.Point) : ℝ := C.toLevelUnits (TorusMetric.torusSupNorm (x - x'))
end YangMills.Construction.SeparatedClasses.ClassData
end
