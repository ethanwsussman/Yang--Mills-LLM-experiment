import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Measurability.StandardBorel
universe u v
abbrev subtypeSigma {Ω : Type u} (m : MeasurableSpace Ω) (Y : Set Ω) : MeasurableSpace Y :=
  m.comap Subtype.val
def IsStandard (Ω : Type u) [MeasurableSpace Ω] : Prop :=
  ∃ (X : Type u) (_ : MetricSpace X) (_ : CompleteSpace X)
    (_ : TopologicalSpace.SeparableSpace X) (Y : Set X),
    @MeasurableSet X (borel X) Y ∧
      Nonempty (@MeasurableEquiv Ω Y _ (subtypeSigma (borel X) Y))
end YangMills.Construction.Measurability.StandardBorel
