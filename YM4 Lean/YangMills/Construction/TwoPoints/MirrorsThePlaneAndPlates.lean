import YangMills.Construction.TwoPoints.FormsOnPairsWithDisjointSupports
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
namespace TwoPoints
open YangMills.Construction.InfiniteLattice (AmbientSpace)
open YangMills.Construction.PeriodicLattice (coordVec)
def reflectAcross (n x : AmbientSpace) : AmbientSpace := x - (2 * euclidDot n x) • n
def reflectFun {E : Type*} (n : AmbientSpace) (f : AmbientSpace → E) : AmbientSpace → E :=
  f ∘ reflectAcross n
def axialNormals : Set AmbientSpace :=
  {v | ∃ (μ : Fin 4) (s : ℝ), (s = 1 ∨ s = -1) ∧ v = s • coordVec μ}
def diagNormals : Set AmbientSpace :=
  {v | ∃ (μ ν : Fin 4) (s t : ℝ), μ < ν ∧ (s = 1 ∨ s = -1) ∧ (t = 1 ∨ t = -1) ∧
    v = (Real.sqrt 2)⁻¹ • (s • coordVec μ + t • coordVec ν)}
def reflectionNormals : Set AmbientSpace := axialNormals ∪ diagNormals
def planeCoords (x : AmbientSpace) : Fin 2 → ℝ := ![x 3, x 0]
def transCoords (x : AmbientSpace) : Fin 2 → ℝ := ![x 1, x 2]
def assemble (y z : Fin 2 → ℝ) : AmbientSpace := ![y 1, z 0, z 1, y 0]
def ofCoords {E : Type*} (F : AmbientSpace → E) (y z : Fin 2 → ℝ) : E := F (assemble y z)
def embedPlane (v : Fin 2 → ℝ) : AmbientSpace := v 0 • coordVec 3 + v 1 • coordVec 0
def coordPlane : Set AmbientSpace := {x | transCoords x = 0}
theorem mem_coordPlane_iff (x : AmbientSpace) : x ∈ coordPlane ↔ ∃ v, x = embedPlane v := by
  constructor
  · intro h
    have h1 : x 1 = 0 := congrFun h 0
    have h2 : x 2 = 0 := congrFun h 1
    refine ⟨planeCoords x, ?_⟩
    funext μ
    fin_cases μ <;>
      simp [embedPlane, planeCoords, coordVec, PeriodicLattice.coordVec, h1, h2]
  · rintro ⟨v, rfl⟩
    funext i
    fin_cases i <;>
      simp [transCoords, embedPlane, coordVec, PeriodicLattice.coordVec]
def planeUnit (t : ℝ) : AmbientSpace :=
  Real.cos t • coordVec 3 + Real.sin t • coordVec 0
def rotateInPlane (t : ℝ) : AmbientSpace →ₗ[ℝ] AmbientSpace :=
  (Pi.basisFun ℝ (Fin 4)).constr ℝ
    ![planeUnit (t + Real.pi / 2), coordVec 1, coordVec 2, planeUnit t]
private theorem rotateInPlane_coordVec (t : ℝ) (μ : Fin 4) :
    rotateInPlane t (coordVec μ) =
      ![planeUnit (t + Real.pi / 2), coordVec 1, coordVec 2, planeUnit t] μ := by
  have h : coordVec μ = Pi.basisFun ℝ (Fin 4) μ := by
    simp [PeriodicLattice.coordVec]
  rw [h, rotateInPlane, Module.Basis.constr_basis]
theorem rotateInPlane_coordVec_three (t : ℝ) : rotateInPlane t (coordVec 3) = planeUnit t :=
  rotateInPlane_coordVec t 3
theorem rotateInPlane_coordVec_zero (t : ℝ) :
    rotateInPlane t (coordVec 0) = planeUnit (t + Real.pi / 2) :=
  rotateInPlane_coordVec t 0
theorem rotateInPlane_coordVec_one (t : ℝ) : rotateInPlane t (coordVec 1) = coordVec 1 :=
  rotateInPlane_coordVec t 1
theorem rotateInPlane_coordVec_two (t : ℝ) : rotateInPlane t (coordVec 2) = coordVec 2 :=
  rotateInPlane_coordVec t 2
def diagNormalPlus : AmbientSpace := (Real.sqrt 2)⁻¹ • (coordVec 3 + coordVec 0)
def diagNormalMinus : AmbientSpace := (Real.sqrt 2)⁻¹ • (coordVec 3 - coordVec 0)
def planeReflectionNormals : Set AmbientSpace := reflectionNormals ∩ coordPlane
def planePerp (v : AmbientSpace) : AmbientSpace := (-(v 0)) • coordVec 3 + v 3 • coordVec 0
def planeOrthoFrame (m : AmbientSpace) : AmbientSpace × AmbientSpace := (m, planePerp m)
def dihedralInPlane : Set (Equiv.Perm AmbientSpace) :=
  {w | w ∈ hyperoctahedralPerms ∧ w (coordVec 1) = coordVec 1 ∧
    w (coordVec 2) = coordVec 2}
def reflectInPlane (m : AmbientSpace) (y : Fin 2 → ℝ) : Fin 2 → ℝ :=
  y - (2 * euclidDot (planeCoords m) y) • planeCoords m
def reflectPlaneFun {E : Type*} (m : AmbientSpace) (α : (Fin 2 → ℝ) → E) : (Fin 2 → ℝ) → E :=
  α ∘ reflectInPlane m
def translatePlaneFun {E : Type*} (v : AmbientSpace) (α : (Fin 2 → ℝ) → E) :
    (Fin 2 → ℝ) → E :=
  fun y => α (y - planeCoords v)
abbrev cc1Plane : Submodule ℂ ((Fin 2 → ℝ) → ℂ) := cc1In univ
abbrev transProfiles : Submodule ℝ ((Fin 2 → ℝ) → ℂ) := realValuedPart cc1Plane
def tensorPlate (α φ : (Fin 2 → ℝ) → ℂ) (x : AmbientSpace) : ℂ :=
  α (planeCoords x) * φ (transCoords x)
def restrictedForm (S : (AmbientSpace → ℂ) → (AmbientSpace → ℂ) → ℝ)
    (φ α α' : (Fin 2 → ℝ) → ℂ) : ℂ :=
  complexifyForm S (tensorPlate α φ) (tensorPlate α' φ)
def profileCorr (φ₁ φ₂ : (Fin 2 → ℝ) → ℂ) (ζ : Fin 2 → ℝ) : ℂ :=
  lebesgueIntegral fun u => φ₁ u * φ₂ (u + ζ)
end TwoPoints
end YangMills.Construction
end
