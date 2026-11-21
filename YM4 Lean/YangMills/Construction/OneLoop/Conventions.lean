import YangMills.Construction.Conventions.StandingParameters
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace OneLoop
abbrev gaugeGroup : Submonoid Matrices.ComplexMatrix2 :=
  Conventions.StandingParameters.gaugeGroup
def traceForm (X Y : Matrices.ComplexMatrix2.traceless) : ℂ :=
  Matrices.ComplexMatrix2.halfTrace
    ((X : Matrices.ComplexMatrix2) * (Y : Matrices.ComplexMatrix2))
def pauliX : Matrices.ComplexMatrix2 := !![0, 1; 1, 0]
def pauliY : Matrices.ComplexMatrix2 := !![0, -Complex.I; Complex.I, 0]
def pauliZ : Matrices.ComplexMatrix2 := !![1, 0; 0, -1]
end OneLoop
end YangMills.Construction
end
