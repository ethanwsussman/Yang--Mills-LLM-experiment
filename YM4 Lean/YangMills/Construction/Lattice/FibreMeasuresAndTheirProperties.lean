import YangMills.Construction.Lattice.FlatSetAndAdaptedCoordinatesOfTheAverage
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction
namespace AverageFibres
variable (L m K k : ℕ)
def IsFibreMeasureFamily (μ : PositiveBondField L m K (k + 1) → Measure (PositiveBondField L m K k)) : Prop :=
  (∀ W', μ W' (blockAverageMap k ⁻¹' {W'} ∩ submersionSet L m K k)ᶜ = 0) ∧
    ∀ (W : PositiveBondField L m K (k + 1)) (u : FibreChart k W) (W' : PositiveBondField L m K (k + 1))
      (S : Set (PositiveBondField L m K k)), MeasurableSet S → S ⊆ u.range →
        μ W' S = u.fibreMeasure W' S
def fibreMeasureFamily : PositiveBondField L m K (k + 1) → Measure (PositiveBondField L m K k) :=
  Classical.epsilon (IsFibreMeasureFamily L m K k)
variable {L m K k}
variable (L m K k)
end AverageFibres
end YangMills.Construction
end
