import YangMills.Construction.SeparatedSequences.ClassesFramesNormsAndKernels
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Set PeriodicLattice PeriodicLattice.DirichletOperators TorusMetric
namespace SeparatedClasses
def ExpansionEndpointsDistLe : Prop :=
  ∀ (C : ClassData), C.L ≤ C.blockSize → ∀ Ω ∈ C.separatedClass,
    ∀ (φ : BondFrame), ∀ c ∈ C.expansionSet Ω φ,
      C.chainDist Ω (c.2.1.source : C.Point) (c.2.1.target : C.Point) ≤
        ENNReal.ofReal (((C.L : ℝ) + 1) / 2)
end SeparatedClasses
end YangMills.Construction
end
