import YangMills.Construction.SeparatedSequences.SupDistanceInLevelUnits
import Mathlib
set_option autoImplicit false
open Set YangMills.Construction.PeriodicLattice YangMills.Construction.PeriodicLattice.DirichletOperators YangMills.Construction.TorusMetric
noncomputable section
namespace YangMills.Construction.SeparatedClasses
def ApexesNearFineSite : Prop :=
  ∀ (C : ClassData), C.L ≤ C.blockSize → ∀ Ω ∈ C.separatedClass,
    ∀ (y z : C.Apex Ω) (x : C.BareSite), (x : C.Point) ∈ Ω 0 →
      C.supDist x y.point ≤ 2 * y.mesh → (x : C.Point) ∈ z.block →
      (C.L : ℝ)⁻¹ * y.mesh ≤ z.mesh ∧ z.mesh ≤ (C.L : ℝ) * y.mesh ∧
        C.chainDist Ω y.point z.point ≤ ENNReal.ofReal (4 * (2 * (C.L : ℝ) + 1))
end YangMills.Construction.SeparatedClasses
end
