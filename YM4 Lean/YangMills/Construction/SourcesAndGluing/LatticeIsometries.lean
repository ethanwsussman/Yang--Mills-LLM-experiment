import YangMills.Construction.SourcesAndGluing.GridsMirrorGridsCellAlgebrasAndTheChessboardValue
import YangMills.Construction.SourcesAndGluing.LogarithmDerivativesPartitionsCumulantsAndConnectedFunctions
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.SourcesAndGluing
open InfiniteLattice (AmbientSpace)
namespace GluingSetup
variable {D : GluingSetup}
namespace TorusLatticeIsometry
variable (r r' : D.TorusLatticeIsometry)
def comp : D.TorusLatticeIsometry where
  toFun := r.toFun ∘ r'.toFun
  isIsometry := ⟨r.isIsometry.1.comp r'.isIsometry.1, fun x y => by
    rw [Function.comp_apply, Function.comp_apply, r.isIsometry.2, r'.isIsometry.2]⟩
  image_eq := by rw [image_comp, r'.image_eq, r.image_eq]
def invFun : D.Torus → D.Torus := r.toEquiv.symm
theorem linkMap_opposite (b : D.PeriodicLink) : r.linkMap b.opposite = (r.linkMap b).opposite := rfl
theorem pullbackField_mem {U : D.PeriodicLink → Matrices.ComplexMatrix2} (hU : U ∈ D.gaugeFields) :
    r.pullbackField U ∈ D.gaugeFields :=
  ⟨fun b _ => hU.1 (r.linkMap b) (mem_univ _), fun b _ => by
    change U (r.linkMap b.opposite) = (U (r.linkMap b))⁻¹
    rw [r.linkMap_opposite]
    exact hU.2 (r.linkMap b) (mem_univ _)⟩
def pullbackOnGaugeFields (U : D.gaugeFields) : D.gaugeFields :=
  ⟨r.pullbackField U.1, r.pullbackField_mem U.2⟩
end TorusLatticeIsometry
namespace R4LatticeIsometry
variable (r r' : D.R4LatticeIsometry)
def asEquiv : AmbientSpace ≃ AmbientSpace := Equiv.ofBijective r.toFun r.isIsometry.1
def comp : D.R4LatticeIsometry where
  toFun := r.toFun ∘ r'.toFun
  isIsometry := ⟨r.isIsometry.1.comp r'.isIsometry.1, fun x y => by
    rw [Function.comp_apply, Function.comp_apply, r.isIsometry.2, r'.isIsometry.2]⟩
  image_eq := by rw [image_comp, r'.image_eq, r.image_eq]
def invFun : AmbientSpace → AmbientSpace := r.asEquiv.symm
end R4LatticeIsometry
end GluingSetup
namespace IsometryInvariance
variable {D : GluingSetup}
def torusFaceImage (Φ : ScaledLatticeMotion D.trivialExponent)
    (p : PeriodicLattice.Plaquette D.L D.m ((D.K : ℕ) : ℤ)) :
    PeriodicLattice.Plaquette D.L D.m ((D.K : ℕ) : ℤ) :=
  Φ.onTorusPlaquette p
def spaceFaceImage (Φ : ScaledLatticeMotion D.trivialExponent)
    (p : InfiniteLattice.ElementaryPlaquette D.mesh) : InfiniteLattice.ElementaryPlaquette D.mesh :=
  Φ.onPlaquette p
def TorusIsometriesEqScaledMotions (D : GluingSetup) : Prop :=
  ∀ f : D.Torus → D.Torus, (∃ r : D.TorusLatticeIsometry, r.toFun = f) ↔
    ∃ S, IsScaledMotionOfTori D.trivialExponent S f
def SpaceIsometriesEqScaledMotions (D : GluingSetup) : Prop :=
  ∀ f : AmbientSpace → AmbientSpace, (∃ r : D.R4LatticeIsometry, r.toFun = f) ↔
    ∃ S, IsScaledMotionOfSpace D.trivialExponent S f
def MapsStructureOnTorus (r : D.TorusLatticeIsometry) : Prop :=
  Function.Surjective r.linkMap ∧
    (∀ U ∈ D.gaugeFields, r.pullbackField U ∈ D.gaugeFields) ∧
    ∀ Φ : ScaledLatticeMotion D.trivialExponent, Φ.onTorus = r.toFun →
      Function.Surjective (torusFaceImage Φ) ∧
      (∀ p, (torusFaceImage Φ p).vertices = r.pointMap '' p.vertices) ∧
      (∀ p, (torusFaceImage Φ p).barycenter = r.toFun p.barycenter) ∧
      ∀ U ∈ D.gaugeFields, ∀ p,
        PeriodicLattice.plaquetteCost (r.pullbackField U) p =
          PeriodicLattice.plaquetteCost U (torusFaceImage Φ p)
def MapsStructureOnSpace (r : D.R4LatticeIsometry) : Prop :=
  Function.Surjective r.linkMap ∧
    ∀ Φ : ScaledLatticeMotion D.trivialExponent, Φ.onSpace = r.toFun →
      Function.Surjective (spaceFaceImage Φ) ∧
      (∀ p, (spaceFaceImage Φ p).cornerSet = r.toLatticeSymmetry.pointMap '' p.cornerSet) ∧
      (∀ p, (spaceFaceImage Φ p).center = r.toFun p.center) ∧
      ∀ (U : D.GridField) (p : InfiniteLattice.ElementaryPlaquette D.mesh),
        InfiniteLattice.faceEnergy (r.pullbackField U) p =
          InfiniteLattice.faceEnergy U (spaceFaceImage Φ p)
def ExpSmearedOnTorus (r : D.TorusLatticeIsometry) : Prop :=
  ∀ w : D.Torus → ℂ, TestFunctions.IsBoundedFun w → ∀ U ∈ D.gaugeFields,
    r.actOn (fun V => Complex.exp (D.smeared w V)) U =
      Complex.exp (D.smeared (w ∘ r.invFun) U)
def ExpSmearedOnSpace (r : D.R4LatticeIsometry) : Prop :=
  ∀ w : AmbientSpace → ℂ, InfiniteLattice.IsBoundedBorelCompactlySupported w → ∀ U : D.GridField,
    r.actOn (fun V => Complex.exp (InfiniteLattice.smearedEnergy w V)) U =
      Complex.exp (InfiniteLattice.smearedEnergy (w ∘ r.invFun) U)
def ActionCompOnTorus (r r' : D.TorusLatticeIsometry) : Prop :=
  ∀ F : (D.PeriodicLink → Matrices.ComplexMatrix2) → ℂ, InfiniteLattice.IsPeriodicObservable F →
    ∀ U ∈ D.gaugeFields, r.actOn (r'.actOn F) U = (r.comp r').actOn F U
def ActionCompOnSpace (r r' : D.R4LatticeIsometry) : Prop :=
  ∀ F : D.GridField → ℂ, InfiniteLattice.IsBoundedObservable F →
    r.actOn (r'.actOn F) = (r.comp r').actOn F
def ExpectationInvariantOnTorus (r : D.TorusLatticeIsometry) : Prop :=
  (∀ F : (D.PeriodicLink → Matrices.ComplexMatrix2) → ℂ, InfiniteLattice.IsPeriodicObservable F →
    D.expectation (r.actOn F) = D.expectation F) ∧
  ∀ w : D.Torus → ℂ, TestFunctions.IsBoundedFun w →
    PeriodicLattice.generatingFunctionOfSource D.L D.m D.K D.β (w ∘ r.invFun) =
      PeriodicLattice.generatingFunctionOfSource D.L D.m D.K D.β w
def CumulantsInvariantOnTorus (r : D.TorusLatticeIsometry) : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    (∀ X : Fin n → D.gaugeFields → ℝ,
      (∀ i, Probability.IsBoundedRealRV (X i)) →
        cumulant D.wilsonOnGaugeFields (fun i => X i ∘ r.pullbackOnGaugeFields) =
          cumulant D.wilsonOnGaugeFields X) ∧
    ∀ f : Fin n → D.Torus → ℝ, D.TorusTestFamily f →
      D.torusConnected (fun i => f i ∘ r.invFun) = D.torusConnected f
def IsometryInvarianceHolds : Prop :=
  ∀ D : GluingSetup,
    TorusIsometriesEqScaledMotions D ∧ SpaceIsometriesEqScaledMotions D ∧
    (∀ r : D.TorusLatticeIsometry,
      MapsStructureOnTorus r ∧ ExpSmearedOnTorus r ∧ ExpectationInvariantOnTorus r ∧
        CumulantsInvariantOnTorus r) ∧
    (∀ r r' : D.TorusLatticeIsometry, ActionCompOnTorus r r') ∧
    (∀ r : D.R4LatticeIsometry, MapsStructureOnSpace r ∧ ExpSmearedOnSpace r) ∧
    ∀ r r' : D.R4LatticeIsometry, ActionCompOnSpace r r'
end IsometryInvariance
end YangMills.Construction.SourcesAndGluing
end
