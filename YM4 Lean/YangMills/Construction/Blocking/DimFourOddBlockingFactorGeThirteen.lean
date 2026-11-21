import YangMills.Construction.Parameters.ConstructionParameters
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction
namespace Blocking
structure DimFourOddBlockingFactorGeThirteen (d L : ℕ) : Prop where
  dim_eq : d = ParameterChoice.spacetimeDim
  odd_blockingFactor : Odd L
  thirteen_le : 13 ≤ L
end Blocking
end YangMills.Construction
