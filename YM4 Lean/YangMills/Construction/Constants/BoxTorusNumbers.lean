import Mathlib
set_option autoImplicit false
namespace YangMills.Construction
namespace Constants
namespace BoxTorus
def layerNumber : ℕ := 4
def anchorNumber : ℕ := 17
def surfaceNumber : ℕ := 12
def tangentNumber : ℕ := 2 * surfaceNumber
def tangentSideNumber : ℕ := tangentNumber * anchorNumber * layerNumber
theorem tangentNumber_eq : tangentNumber = 24 := rfl
theorem tangentSideNumber_eq : tangentSideNumber = 1632 := rfl
end BoxTorus
end Constants
end YangMills.Construction
