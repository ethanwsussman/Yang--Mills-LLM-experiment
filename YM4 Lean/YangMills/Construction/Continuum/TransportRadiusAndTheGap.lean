import YangMills.Construction.Continuum.TorusTransportData
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace TorusTransport
namespace TransportData
variable (D : TransportData)
def maxRadius : ℝ := D.side / 4 - 1
end TransportData
end TorusTransport
end YangMills.Construction
end
