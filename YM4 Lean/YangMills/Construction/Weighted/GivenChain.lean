import YangMills.Construction.Weighted.SeparatedRegions
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.Weighted
structure GivenChain where
  data : TorusData
  chain : SeparatedChain data
  stage_zero_nonempty : (chain.stage 0).Nonempty
end YangMills.Construction.Weighted
