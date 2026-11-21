import YangMills.Construction.ClusterExpansionOfAStep.TreesOfABlock
import YangMills.Construction.ColdStepAtMirrorFrames.AdjointOnABond
import YangMills.Construction.ColdStepAtMirrorFrames.ExpansionUnderAGaugeOfTheTopProof
import YangMills.Construction.SummableBoundsOfTheFlow.MoveOfTheTopAlongItsFieldProof
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
open BlockAverages
namespace ColdStepAtMirrorFrames
namespace AdjointActionCoordinates
private def coords (X : imaginaryQuaternions) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 ![(X : ℍ[ℝ]).imI, (X : ℍ[ℝ]).imJ, (X : ℍ[ℝ]).imK]
private theorem toImaginary_coords (X : imaginaryQuaternions) : toImaginary (coords X) = X := by
  have hre : (X : ℍ[ℝ]).re = 0 := X.2
  apply Subtype.ext
  ext <;> simp [toImaginary, coords, hre]
private theorem coords_toImaginary (v : EuclideanSpace ℝ (Fin 3)) : coords (toImaginary v) = v := by
  ext i
  fin_cases i <;> rfl
private theorem toImaginary_add (v w : EuclideanSpace ℝ (Fin 3)) :
    toImaginary (v + w) = toImaginary v + toImaginary w := by apply _root_.YangMills.Construction.Interpolation.TopVariation.toImaginary_add <;> assumption
private theorem toImaginary_smul (c : ℝ) (v : EuclideanSpace ℝ (Fin 3)) :
    toImaginary (c • v) = c • toImaginary v := by apply _root_.YangMills.Construction.Interpolation.TopVariation.toImaginary_smul <;> assumption
private theorem coords_add (X Y : imaginaryQuaternions) : coords (X + Y) = coords X + coords Y := by
  ext i
  fin_cases i <;> simp [coords]
private theorem coords_smul (c : ℝ) (X : imaginaryQuaternions) : coords (c • X) = c • coords X := by
  ext i
  fin_cases i <;> simp [coords]
private theorem adjointAction_add (g : UnitQuaternion) (X Y : imaginaryQuaternions) :
    _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction g (X + Y) = _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction g X + _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction g Y := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.GaugeCovariance.adjointAction_add <;> assumption
private theorem adjointAction_smul (g : UnitQuaternion) (c : ℝ) (X : imaginaryQuaternions) :
    _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction g (c • X) = c • _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction g X := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.GaugeCovariance.adjointAction_smul <;> assumption
private theorem adjointAction_adjointAction_inv (g : UnitQuaternion) (X : imaginaryQuaternions) :
    _root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction g (_root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction g⁻¹ X) = X := by
  apply Subtype.ext
  change (g : ℍ[ℝ]) * (((g⁻¹ : UnitQuaternion) : ℍ[ℝ]) * (X : ℍ[ℝ]) *
    (((g⁻¹)⁻¹ : UnitQuaternion) : ℍ[ℝ])) * ((g⁻¹ : UnitQuaternion) : ℍ[ℝ]) = X
  have hmul : (g : ℍ[ℝ]) * ((g⁻¹ : UnitQuaternion) : ℍ[ℝ]) = 1 := by
    rw [← Submonoid.coe_mul]
    simp
  rw [inv_inv]
  calc (g : ℍ[ℝ]) * (((g⁻¹ : UnitQuaternion) : ℍ[ℝ]) * (X : ℍ[ℝ]) * (g : ℍ[ℝ])) *
        ((g⁻¹ : UnitQuaternion) : ℍ[ℝ])
      = ((g : ℍ[ℝ]) * ((g⁻¹ : UnitQuaternion) : ℍ[ℝ])) * (X : ℍ[ℝ]) *
          ((g : ℍ[ℝ]) * ((g⁻¹ : UnitQuaternion) : ℍ[ℝ])) := by
        noncomm_ring
    _ = X := by rw [hmul, one_mul, mul_one]
private theorem norm_unitQuaternion (g : UnitQuaternion) : ‖(g : ℍ[ℝ])‖ = 1 := by apply _root_.YangMills.Construction.BlockAverages.norm_coe_unitQuaternion <;> assumption
private theorem norm_toImaginary (v : EuclideanSpace ℝ (Fin 3)) :
    ‖((toImaginary v : imaginaryQuaternions) : ℍ[ℝ])‖ = ‖v‖ := by apply _root_.YangMills.Construction.BlockTrees.norm_toImaginary <;> assumption
end AdjointActionCoordinates
open AdjointActionCoordinates in
theorem adjointActionLinearIsometry_holds : AdjointActionLinearIsometry := by
  intro g
  let f : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] EuclideanSpace ℝ (Fin 3) :=
    { toFun := fun v => coords (_root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction g (toImaginary v))
      map_add' := fun v w => by rw [toImaginary_add, AdjointActionCoordinates.adjointAction_add, coords_add]
      map_smul' := fun c v => by rw [toImaginary_smul, AdjointActionCoordinates.adjointAction_smul, coords_smul]; rfl }
  have hnorm : ∀ v, ‖f v‖ = ‖v‖ := fun v => by
    have h1 : ‖f v‖ = ‖((toImaginary (f v) : imaginaryQuaternions) : ℍ[ℝ])‖ := (norm_toImaginary _).symm
    rw [h1]
    change ‖((toImaginary (coords (_root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction g (toImaginary v))) : imaginaryQuaternions) : ℍ[ℝ])‖ = _
    rw [toImaginary_coords]
    change ‖(g : ℍ[ℝ]) * ((toImaginary v : imaginaryQuaternions) : ℍ[ℝ]) *
      ((g⁻¹ : UnitQuaternion) : ℍ[ℝ])‖ = _
    rw [norm_mul, norm_mul, norm_unitQuaternion, norm_unitQuaternion, one_mul, mul_one, norm_toImaginary]
  let fi : EuclideanSpace ℝ (Fin 3) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3) := ⟨f, hnorm⟩
  have hsurj : Function.Surjective fi := fun w => by
    refine ⟨coords (_root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction g⁻¹ (toImaginary w)), ?_⟩
    change coords (_root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction g (toImaginary (coords (_root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction g⁻¹ (toImaginary w))))) = w
    rw [toImaginary_coords, adjointAction_adjointAction_inv, coords_toImaginary]
  refine ⟨LinearIsometryEquiv.ofSurjective fi hsurj, fun v => ?_⟩
  change toImaginary (coords (_root_.YangMills.Construction.ColdStepAtMirrorFrames.adjointAction g (toImaginary v))) = _
  exact toImaginary_coords _
end ColdStepAtMirrorFrames
end YangMills.Construction
end
