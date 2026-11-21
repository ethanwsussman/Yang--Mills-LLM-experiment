import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.SeparatedSequences
def cubeOverlapCount (L : ℕ) : ℕ :=
  60 * (12 * L ^ 2 + 13) ^ 4
def cellsPerCubeCount (L : ℕ) (r : ℕ+) : ℕ :=
  (1 + cubeOverlapCount L) ^ ((r : ℕ) ^ 2)
def cellOverlapCount (L : ℕ) (r : ℕ+) : ℕ :=
  (r : ℕ) * cubeOverlapCount L * cellsPerCubeCount L r
def treeWalkCount (L : ℕ) (r : ℕ+) : ℕ :=
  4 * cellOverlapCount L r
end YangMills.Construction.SeparatedSequences
