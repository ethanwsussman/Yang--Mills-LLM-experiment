import YangMills.Construction.InfiniteLattice.PeriodLatticesToriAndTheirWilsonMeasures
import YangMills.Construction.ReflectionPositivity.NormalsHeightsHyperplanesAndLatticeMirrors
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.InfiniteLattice
namespace PeriodSublattice
def toAmbient (Γ : PeriodSublattice 1) : AddSubgroup AmbientSpace :=
  Γ.periods.map (latticeSubgroup 1).subtype
def axialSubgroup (n : AmbientSpace) (z : ℤ) : AddSubgroup AmbientSpace :=
  AddSubgroup.zmultiples ((2 * (z : ℝ)) • ReflectionPositivity.NormalPlanes.normalOverNormSq n)
structure IsTransverseComplement (Γ : PeriodSublattice 1) (n : AmbientSpace) (z : ℤ)
    (P : AddSubgroup AmbientSpace) : Prop where
  le_toAmbient : P ≤ Γ.toAmbient
  sup_eq : P ⊔ axialSubgroup n z = Γ.toAmbient
  inf_eq : P ⊓ axialSubgroup n z = ⊥
  height_eq_zero : ∀ x ∈ P, ReflectionPositivity.NormalPlanes.heightAlong n x = 0
def SplitsAlongWithHalfPeriod (Γ : PeriodSublattice 1) (n : AmbientSpace) (z : ℤ) : Prop :=
  n ∈ ReflectionPositivity.NormalPlanes.admissibleNormals ∧ 2 ≤ z ∧
    ∃ P, Γ.IsTransverseComplement n z P
end PeriodSublattice
end YangMills.Construction.InfiniteLattice
end
