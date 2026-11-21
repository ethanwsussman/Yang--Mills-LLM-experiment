import YangMills.Construction.Continuum.ReflectionOfTestFunctionsTensorsAndOrderZero
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TorusTransport.TestFunctionOrders
def tensorMulti {n n' : ℕ} (_h₁ : 1 ≤ n) (_h₂ : 1 ≤ n')
    (F : ComplexFun (Configuration n)) (G : ComplexFun (Configuration n')) :
    ComplexFun (Configuration (n + n')) :=
  tensor (p := n) (q := n') F G
end YangMills.Construction.TorusTransport.TestFunctionOrders
end
