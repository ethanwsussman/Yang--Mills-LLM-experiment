import YangMills.Construction.ColdChainAtEveryLevel.ChartsOfCellsAndSites
import YangMills.Construction.ColdStepAtMirrorFrames.LeastActionOfTheCurvedChainProof
import YangMills.Construction.ColdStepAtMirrorFrames.BareActionIsCriticalAtAnAbelianFieldProof
import YangMills.Construction.ColdStepAtMirrorFrames.FirstDerivativeOfAnExpansionAtOneProof
import YangMills.Construction.ColdStepAtMirrorFrames.LinearFieldIsCold
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ColdStepAtMirrorFrames
open YangMills.Construction.BlockAverages
variable {F : BlockFrame}
private abbrev IntPoint : Type := Fin 4 → ℤ
private theorem expUnit_add_smul (X : imaginaryQuaternions) (s t : ℝ) :
    expUnit ((s + t) • X) = expUnit (s • X) * expUnit (t • X) := by apply _root_.YangMills.SharedProofs.p2328 <;> assumption
private theorem expUnit_smul_inv (X : imaginaryQuaternions) (s : ℝ) :
    (expUnit (s • X))⁻¹ = expUnit ((-s) • X) := by apply _root_.YangMills.SharedProofs.p4359 <;> assumption
private theorem norm_expUnit_sub_one_le (w : imaginaryQuaternions) :
    ‖((expUnit w : UnitQuaternion) : Quaternion ℝ) - 1‖ ≤ ‖w‖ := by apply _root_.YangMills.SharedProofs.p28543 <;> assumption
private theorem norm_expUnit_smul_sub_one_le (X : imaginaryQuaternions) (hX : ‖X‖ = 1) (s : ℝ) :
    ‖((expUnit (s • X) : UnitQuaternion) : Quaternion ℝ) - 1‖ ≤ |s| := by
  have := norm_expUnit_sub_one_le (s • X)
  rwa [norm_smul, hX, mul_one, Real.norm_eq_abs] at this
private theorem siteOfCoords_add {H : BlockFrame} (j : ℕ) (a b : IntPoint) :
    (siteOfCoords j (a + b) : H.Site j) = siteOfCoords j a + siteOfCoords j b := by apply _root_.YangMills.Construction.BlockAverages.siteOfCoords_add <;> assumption
private theorem siteOfCoords_siteCoords {H : BlockFrame} {k : ℕ} (y : H.Site k) :
    siteOfCoords k (siteCoords y) = y := by apply _root_.YangMills.Construction.BlockAverages.siteOfCoords_siteCoords <;> assumption
private theorem plaquetteHolonomy_of_linear {j : ℕ} {U : F.GaugeField j} {X : imaginaryQuaternions} {g : ℝ}
    {μ ν : Fin 4} {φ : IntPoint → ℝ}
    (hU : ∀ z i, U (siteOfCoords j z) i = expUnit (linearFluxAngle g μ ν φ z i • X)) (hμν : μ < ν)
    (z : IntPoint) (α β : Fin 4) (hαβ : α < β) :
    plaquetteHolonomy U (siteOfCoords j z, α, β) = expUnit ((if α = μ ∧ β = ν then g else 0) • X) := by apply _root_.YangMills.DeltaSharedProofs.p502334 <;> assumption
private theorem plaquetteDefect_le_of_linear {j : ℕ} {U : F.GaugeField j} {X : imaginaryQuaternions}
    (hX : ‖X‖ = 1) {g : ℝ} {μ ν : Fin 4} {φ : IntPoint → ℝ}
    (hU : ∀ z i, U (siteOfCoords j z) i = expUnit (linearFluxAngle g μ ν φ z i • X)) (hμν : μ < ν)
    (p : F.Site j × Fin 4 × Fin 4) (hp : p.2.1 < p.2.2) : plaquetteDefect U p ≤ |g| := by apply _root_.YangMills.DeltaSharedProofs.p502391 <;> assumption
theorem linearFieldCurvatureBound_holds : LinearFieldCurvatureBound := by
  intro F j U X g μ ν hX hμν ⟨φ, hU⟩
  refine ⟨fun x α β h => ?_, fun p hp => plaquetteDefect_le_of_linear hX hU hμν p hp⟩
  conv_lhs => rw [← siteOfCoords_siteCoords x]
  exact plaquetteHolonomy_of_linear hU hμν _ α β h
end YangMills.Construction.ColdStepAtMirrorFrames
end
