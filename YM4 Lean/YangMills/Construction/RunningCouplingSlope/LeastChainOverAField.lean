import YangMills.Construction.Lattice.SiteCoordinates
import YangMills.Construction.RunningCouplingSlope.LogarithmOfTheChain
import YangMills.Construction.RunningCouplingSlope.SoftChainOnATower
import YangMills.Construction.SoftAverages.ModelsOfAStep
import Mathlib
set_option autoImplicit false
open scoped Quaternion
noncomputable section
namespace YangMills.Construction
namespace RunningCouplingSlope
open Tower TorusFields
def torusSideBelow (L : ℕ) : ℕ → ℕ → ℕ
  | 0, N => N
  | s + 1, N => torusSideBelow L s (N * L)
def minimizerBelow (a ρ : ℝ) (L : ℕ) : (k s N : ℕ) → TorusField N → TorusField (torusSideBelow L s N)
  | _, 0, _, V => V
  | k, s + 1, N, V =>
      minimizerBelow a ρ L (k - 1) s (N * L) (SlopeCoefficient.minimizerOnFinerTorus a ρ L (k - 1) N V)
def chainStepLogSum (a ρ : ℝ) (L : ℕ) : ℕ → (N : ℕ) → TorusField N → ℝ
  | 0, _, _ => 0
  | t + 1, N, V => SlopeCoefficient.stepLogAmplitude (F := torusFrame L t N) a ρ
        (readAtLevel (torusFrame L t N) (torusFrame L t N).top V) +
      chainStepLogSum a ρ L t (N * L) (SlopeCoefficient.minimizerOnFinerTorus a ρ L t N V)
variable {L n k : ℕ}
def levelVertexOfTorusSite (j : ℕ) {m : ℕ} (z : TorusSite m) : Vertex L n k j :=
  PeriodicLattice.offsetSite 0 fun μ => ((z μ).cast : ℤ)
def RepresentsAtLevel (j : ℕ) {m : ℕ} (W : Edge L n k j → Matrices.ComplexMatrix2) (V : TorusField m) : Prop :=
  W ∈ fieldSpace L n k j ∧ ∀ (z : TorusSite m) (μ : Fin 4),
    W (PeriodicLattice.Bond.forwardFrom (levelVertexOfTorusSite j z) μ) =
      SoftAverages.quaternionToMatrix ((V z μ : BlockAverages.UnitQuaternion) : ℍ[ℝ])
def RepresentsMinimizerChain (a ρ : ℝ) (V : TorusField (2 * L ^ n)) (X : ChainPoint L n k) : Prop :=
  ∀ j, j ≤ k → RepresentsAtLevel j (levelField X j) (minimizerBelow a ρ L k (k - j) (2 * L ^ n) V)
end RunningCouplingSlope
end YangMills.Construction
end
