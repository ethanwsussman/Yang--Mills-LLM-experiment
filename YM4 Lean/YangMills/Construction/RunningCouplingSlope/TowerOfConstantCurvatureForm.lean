import YangMills.Construction.ColdStepAtMirrorFrames.IntegrandOfTheColdStep
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
open YangMills.Construction.BlockAverages YangMills.Construction.ColdStepAtMirrorFrames
namespace YangMills.Construction.RunningCouplingSlope
variable {F : BlockFrame}
abbrev LinkComponent (F : BlockFrame) (j : ℕ) : Type := ↥(innerBonds (finiteCells F) j) × Fin 3
abbrev SiteComponent (F : BlockFrame) (j : ℕ) : Type := ↥(sitesOfCells (finiteCells F) j) × Fin 3
def imaginaryBasis (m : Fin 3) : imaginaryQuaternions := toImaginary (EuclideanSpace.single m 1)
def imaginaryCoord (m : Fin 3) (q : ℍ[ℝ]) : ℝ := inner ℝ ((imaginaryBasis m : imaginaryQuaternions) : ℍ[ℝ]) q
def adjointMatrix (g : UnitQuaternion) : Matrix (Fin 3) (Fin 3) ℝ := fun m m' =>
  imaginaryCoord m ((g : ℍ[ℝ]) * ((imaginaryBasis m' : imaginaryQuaternions) : ℍ[ℝ]) * ((g⁻¹ : UnitQuaternion) : ℍ[ℝ]))
open Classical in
def siteTangent {j : ℕ} (g : SiteComponent F j → ℝ) (x : F.Site j) : Fin 3 → ℝ := fun m =>
  if h : x ∈ sitesOfCells (finiteCells F) j then g (⟨x, h⟩, m) else 0
def gaugeDifferential {j : ℕ} (W : F.GaugeField j) : Matrix (LinkComponent F j) (SiteComponent F j) ℝ := fun p s =>
  (if s.1.1 = p.1.1.1 ∧ s.2 = p.2 then 1 else 0) -
    (if s.1.1 = p.1.1.1 + BlockAverages.unitStep j p.1.1.2 then adjointMatrix (W p.1.1.1 p.1.1.2) p.2 s.2 else 0)
def IsBlockCentre (m : ℕ) {j : ℕ} (x : F.Site j) : Prop :=
  ∃ y : F.Site m, x = siteOfCoords j fun i => (F.blockSide : ℤ) ^ (m - j) * siteCoords y i
abbrev OffCentreComponent (F : BlockFrame) (j m : ℕ) : Type := {s : SiteComponent F j // ¬ IsBlockCentre m s.1.1}
end YangMills.Construction.RunningCouplingSlope
end
