import YangMills.Construction.Matrices.SpecialUnitaryTwo
import Mathlib
set_option autoImplicit false
open scoped Quaternion
noncomputable section
namespace YangMills.Construction
namespace SoftAverages
def quaternionToMatrix (q : ℍ[ℝ]) : Matrices.ComplexMatrix2 :=
  !![(q.re : ℂ) + Complex.I * q.imI, (q.imJ : ℂ) + Complex.I * q.imK;
    -(q.imJ : ℂ) + Complex.I * q.imK, (q.re : ℂ) - Complex.I * q.imI]
end SoftAverages
end YangMills.Construction
end
