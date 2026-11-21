import YangMills.Construction.ClusterExpansionOfAStep.FieldsOnATorus
import YangMills.Construction.Lattice.SiteCoordinates
import YangMills.Construction.RunningCouplingSlope.GaussianNumbersOfTheSoftChain
import YangMills.Construction.SoftAverages.ModelsOfAStep
import Mathlib
set_option autoImplicit false
open scoped Quaternion
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
open Tower
variable {L n k : ℕ}
def topVertexOf (x : TorusFields.TorusSite (2 * L ^ n)) : Vertex L n k k :=
  PeriodicLattice.offsetSite 0 fun μ => ((x μ).cast : ℤ)
def RepresentsTorusField (W : Edge L n k k → Matrices.ComplexMatrix2)
    (V : TorusFields.TorusField (2 * L ^ n)) : Prop :=
  W ∈ fieldSpace L n k k ∧ ∀ (x : TorusFields.TorusSite (2 * L ^ n)) (μ : Fin 4),
    W (PeriodicLattice.Bond.forwardFrom (topVertexOf x) μ) =
      SoftAverages.quaternionToMatrix ((V x μ : BlockAverages.UnitQuaternion) : ℍ[ℝ])
def minimalChainAction (a : ℝ) (W : Edge L n k k → Matrices.ComplexMatrix2) : ℝ :=
  sInf {s | ∃ X : ChainPoint L n k, IsCompactValued X ∧ RunningCouplingSlope.levelField X k = W ∧
    s = RunningCouplingSlope.chainAction a X}
def IsTopLevelGradient (a : ℝ) (W : Edge L n k k → Matrices.ComplexMatrix2)
    (g : edgeFormSpace L n k k) : Prop :=
  ∀ B : edgeFormSpace L n k k,
    (edgeFormPairing (g : Edge L n k k → Matrices.ComplexMatrix2)
      (B : Edge L n k k → Matrices.ComplexMatrix2)).re =
    deriv (fun s : ℝ => minimalChainAction a
      (PeriodicLattice.expTwist (s • (B : Edge L n k k → Matrices.ComplexMatrix2)) W)) 0
def gaugeTransformPoint (v : Vertex L n k 0 → Matrices.ComplexMatrix2) (X : ChainPoint L n k) :
    ChainPoint L n k :=
  ⟨fun b => v b.source * X.fine b * (v b.target)⁻¹, fun i c =>
    restrictVertexFunction (i + 1) v c.1.source * X.noise i c *
      (restrictVertexFunction (i + 1) v c.1.source)⁻¹⟩
end YangMills.Construction.RunningCouplingSlope
end
