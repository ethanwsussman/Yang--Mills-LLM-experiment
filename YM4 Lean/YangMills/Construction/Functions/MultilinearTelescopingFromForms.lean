import YangMills.Construction.Analysis.MultilinearTelescopingBound
import YangMills.Construction.Functions.MultilinearTelescoping
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.MultilinearTelescoping
theorem telescopingBound_of_multilinearTelescopingBound
    (hforms : YangMills.Construction.Multilinear.MultilinearTelescopingBound) : TelescopingBound :=
  hforms
end YangMills.Construction.MultilinearTelescoping
