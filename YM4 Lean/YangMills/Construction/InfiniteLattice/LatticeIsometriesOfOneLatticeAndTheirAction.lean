import YangMills.Construction.InfiniteLattice.LatticeIsometriesMirrorsAndTheClassOfReflectionPositiveMeasures
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Set InfiniteLattice
open scoped ComplexConjugate
namespace LatticePhases.LatticeSymmetryAction
variable (D : Setup)
def SymmetriesAreMotions : Prop :=
  range (LatticeSymmetry.toFun : LatticeSymmetry D.mesh → AmbientSpace → AmbientSpace) =
    latticeMotions D.mesh
def MotionsFormGroup : Prop :=
  id ∈ latticeMotions D.mesh ∧
    (∀ r ∈ latticeMotions D.mesh, ∀ s ∈ latticeMotions D.mesh,
      latticeMotionMul r s ∈ latticeMotions D.mesh) ∧
    ∀ r ∈ latticeMotions D.mesh, ∃ t ∈ latticeMotions D.mesh,
      latticeMotionMul r t = id ∧ latticeMotionMul t r = id
def PullbackIsHomeomorph : Prop :=
  ∀ r s : LatticeSymmetry D.mesh,
    r.toFun ∈ latticeMotions D.mesh → s.toFun ∈ latticeMotions D.mesh →
      IsHomeomorph r.pullbackField ∧
        (r.comp s).pullbackField = s.pullbackField ∘ r.pullbackField ∧
        ∀ t : LatticeSymmetry D.mesh, t.IsInverse r →
          Function.LeftInverse t.pullbackField r.pullbackField ∧
            Function.RightInverse t.pullbackField r.pullbackField
def ActionRules : Prop :=
  ∀ r s : LatticeSymmetry D.mesh,
    r.toFun ∈ latticeMotions D.mesh → s.toFun ∈ latticeMotions D.mesh →
      (∀ F G : GaugeField D.mesh → ℂ,
        r.actOn (F * G) = r.actOn F * r.actOn G) ∧
      (∀ F : GaugeField D.mesh → ℂ,
        r.actOn (fun U => conj (F U)) = fun U => conj (r.actOn F U)) ∧
      (∀ S : Set AmbientSpace,
        (fun F : GaugeField D.mesh → ℂ => r.actOn F) '' regionObservables D.mesh S =
          regionObservables D.mesh (r.setImage S)) ∧
      ∀ F : GaugeField D.mesh → ℂ,
        (r.comp s).actOn F = r.actOn (s.actOn F)
def MirrorReflectionsAreMotions : Prop :=
  ∀ P : LatticeMirror D.mesh, P.symmetry.toFun ∈ latticeMotions D.mesh
def AxisSignChangesSubgroup : Prop :=
  axisSignChanges.ncard = 16 ∧
    ∃ Γ : Subgroup (AmbientSpace ≃ₗ[ℝ] AmbientSpace),
      (∀ γ ∈ Γ, (γ : AmbientSpace →ₗ[ℝ] AmbientSpace) ∈ hypercubicGroup) ∧
      (fun γ : AmbientSpace ≃ₗ[ℝ] AmbientSpace => (γ : AmbientSpace →ₗ[ℝ] AmbientSpace)) ''
          (Γ : Set (AmbientSpace ≃ₗ[ℝ] AmbientSpace)) =
        axisSignChanges ∧
      Γ = Subgroup.closure
        {γ : AmbientSpace ≃ₗ[ℝ] AmbientSpace | ∃ μ : Fin 4, ⇑γ = (axialReflection D.mesh μ).toFun}
def ActionPreservesNormContinuityLocality : Prop :=
  ∀ r : LatticeSymmetry D.mesh, r.toFun ∈ latticeMotions D.mesh →
    ∀ F : GaugeField D.mesh → ℂ, IsBoundedObservable F →
      observableSupNorm (r.actOn F) = observableSupNorm F ∧
        (Continuous F → Continuous (r.actOn F)) ∧
        ∀ S : Set AmbientSpace, F ∈ continuousLocalFunctions D.mesh ∩ regionObservables D.mesh S →
          r.actOn F ∈ continuousLocalFunctions D.mesh ∩ regionObservables D.mesh (r.setImage S)
def SymmetryActionFacts : Prop :=
  ∀ D : Setup,
    (SymmetriesAreMotions D ∧ MotionsFormGroup D) ∧
    (PullbackIsHomeomorph D ∧ ActionRules D) ∧
    MirrorReflectionsAreMotions D ∧
    AxisSignChangesSubgroup D ∧
    ActionPreservesNormContinuityLocality D
end LatticePhases.LatticeSymmetryAction
end YangMills.Construction
