import YangMills.Construction.InfiniteLattice.SpacePlaquettesFunctionsOfPlaquettesAndLatticeIsometries
import YangMills.Construction.ReflectionPositivity.ClassesOfReflectionPositiveMeasures
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
noncomputable section
namespace YangMills.Construction.InfiniteLattice.UnitSymmetriesAndFaces
open ReflectionPositivity.MirrorHyperplanes (basisVec unitPositiveClass)
open CutoffStructure (IsContinuousInLinks)
open CutoffLattice (faceLinks)
def axisAndDiagonalReflections : Set (AmbientSpace ≃ₗ[ℝ] AmbientSpace) :=
  {w | (∃ μ : Fin 4, ⇑w = hyperplaneReflect (basisVec μ) 0) ∨
    ∃ μ κ : Fin 4, μ ≠ κ ∧ ⇑w = hyperplaneReflect (basisVec μ - basisVec κ) 0}
def SymmetriesAreAffineMotions : Prop :=
  (∀ s : AmbientSpace → AmbientSpace,
      (∃ r : UnitLatticeSymmetry, r.toFun = s) ↔ s ∈ affineHyperoctahedralMaps 1) ∧
    hyperoctahedralLinearGroup = Subgroup.closure axisAndDiagonalReflections
def PositiveMeasuresAreSymmetric : Prop :=
  ∀ ν ∈ unitPositiveClass, ∀ r : UnitLatticeSymmetry, IsSymmetricUnder ν r
def FaceEnergyContinuousAndBounded : Prop :=
  ∀ p : ElementaryPlaquette 1,
    IsContinuousInLinks (faceLinks p) (fun U : GaugeField 1 => faceEnergy U p) ∧
      ∀ U : GaugeField 1, 0 ≤ faceEnergy U p ∧ faceEnergy U p ≤ 2
def SymmetriesMapFaces : Prop :=
  ∀ (r : UnitLatticeSymmetry) (p : ElementaryPlaquette 1),
    (∃! q : ElementaryPlaquette 1, q.cornerSet = r.pointMap '' p.cornerSet) ∧
      (r.plaquetteMap p).cornerSet = r.pointMap '' p.cornerSet ∧
      (r.plaquetteMap p).center = r.toFun p.center ∧
      r.actOn (fun U : GaugeField 1 => faceEnergy U p) =
        fun U : GaugeField 1 => faceEnergy U (r.plaquetteMap p)
def SymmetriesActTransitivelyOnFaces : Prop :=
  ∀ p p' : ElementaryPlaquette 1, ∃ r : UnitLatticeSymmetry, r.plaquetteMap p = p'
def FaceEnergyMeansAgree : Prop :=
  ∀ ν ∈ unitPositiveClass, ∀ p p' : ElementaryPlaquette 1,
    ∫ U : GaugeField 1, faceEnergy U p ∂ν =
      ∫ U : GaugeField 1, faceEnergy U p' ∂ν
def Summary : Prop :=
  SymmetriesAreAffineMotions ∧ PositiveMeasuresAreSymmetric ∧ FaceEnergyContinuousAndBounded ∧
    SymmetriesMapFaces ∧ SymmetriesActTransitivelyOnFaces ∧ FaceEnergyMeansAgree
end YangMills.Construction.InfiniteLattice.UnitSymmetriesAndFaces
end
