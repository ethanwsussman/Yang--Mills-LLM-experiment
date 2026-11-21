import YangMills.Construction.ConfigSpace.MultilinearComplexification
import YangMills.Construction.Continuum.SystemsModesAndScaledNorms
import Mathlib
set_option autoImplicit false
open scoped Classical
noncomputable section
namespace YangMills.Construction
namespace ConfigSpace
variable {n : ℕ}
def PointSystem.modeFamily (Q : PointSystem n) (ξ : Config n) : FnTuple n := fun i => Q.modeFun i ξ
def complexifyAtModes (T : smoothRealTupleSet n → ℝ) (Q : PointSystem n) (ξ : Config n) : ℂ :=
  if h : Q.modeFamily ξ ∈ smoothComplexTupleSet n then complexify T ⟨Q.modeFamily ξ, h⟩ else 0
def localPairing (T : smoothRealTupleSet n → ℝ) (Q : PointSystem n) (Φ : Config n → ℂ) : ℂ :=
  ∑' ξ : Q.freqLattice, Q.fourierCoeff Φ ξ * complexifyAtModes T Q ξ
def localConst : ℝ := 1152 * modeConst
end ConfigSpace
end YangMills.Construction
