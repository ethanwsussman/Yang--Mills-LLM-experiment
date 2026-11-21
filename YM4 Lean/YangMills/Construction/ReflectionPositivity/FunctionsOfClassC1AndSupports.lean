import YangMills.Construction.Lattice.EuclideanIsometries
import YangMills.Construction.Lattice.ObservablesAndTestNorms
import YangMills.Construction.ReflectionPositivity.AxisMirrorData
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace ReflectionPositivity.AxisMirror
namespace MirrorData
variable (D : MirrorData)
def liftChoice (x : D.Torus) : Fin 4 → ℝ := Classical.epsilon fun y => D.projection y = x
end MirrorData
namespace Ambient
variable (D : MirrorData) {𝕜 : Type*} [RCLike 𝕜]
def metric : (E : Ambient) → E.Point D → E.Point D → ℝ
  | .torus => PeriodicLattice.torusEuclidDist D.L D.m
  | .euclidean => InfiniteLattice.euclidDist
def gradR4 (F : (Fin 4 → ℝ) → 𝕜) (y : Fin 4 → ℝ) : Fin 4 → 𝕜 :=
  fun μ => TestFunctions.partialDerivR4 μ F y
def IsC1 : (E : Ambient) → (E.Point D → 𝕜) → Prop
  | .torus, f => TestFunctions.IsC1R4 (f ∘ D.projection)
  | .euclidean, f => TestFunctions.IsC1R4 f
def grad : (E : Ambient) → (E.Point D → 𝕜) → E.Point D → Fin 4 → 𝕜
  | .torus, f, x => gradR4 (f ∘ D.projection) (D.liftChoice x)
  | .euclidean, f, y => gradR4 f y
def closedSupport (E : Ambient) (f : E.Point D → 𝕜) : Set (E.Point D) :=
  MetricNotions.closureWrt (metric D E) {x | f x ≠ 0}
variable (𝕜) in
def compactC1 (E : Ambient) : Set (E.Point D → 𝕜) :=
  {f | IsC1 D E f ∧ MetricNotions.IsCompactWrt (metric D E) (closedSupport D E f)}
end Ambient
end ReflectionPositivity.AxisMirror
end YangMills.Construction
