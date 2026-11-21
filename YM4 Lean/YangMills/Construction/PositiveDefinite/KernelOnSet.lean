import YangMills.Construction.PositiveDefinite.HalfPlaneKernelDefs
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.PositiveDefinite
abbrev KernelPosSemidefOnSet {Y : Type*} (k : Y → Y → ℂ) : Prop :=
  KernelPosSemidef k
end YangMills.Construction.PositiveDefinite
