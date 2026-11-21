import YangMills.Construction.TwoPoints.MirrorsThePlaneAndPlates
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.TwoPoints
open YangMills.Construction.InfiniteLattice (AmbientSpace)
open YangMills.Construction.PeriodicLattice (coordVec)
def IsUnitSign (s : ℝ) : Prop := s = 1 ∨ s = -1
def signedAxis (μ : Fin 4) (s : ℝ) : AmbientSpace := s • coordVec μ
def signedDiagonal (μ ν : Fin 4) (s t : ℝ) : AmbientSpace :=
  (Real.sqrt 2)⁻¹ • (s • coordVec μ + t • coordVec ν)
def normalRepresentatives : Set AmbientSpace :=
  {v | ∃ μ : Fin 4, v = coordVec μ} ∪
    {v | ∃ μ ν : Fin 4, μ < ν ∧
      v = (Real.sqrt 2)⁻¹ • (coordVec μ + coordVec ν)} ∪
    {v | ∃ μ ν : Fin 4, μ < ν ∧
      v = (Real.sqrt 2)⁻¹ • (coordVec μ - coordVec ν)}
def ReflectionNormalsCount : Prop :=
  (∀ (μ : Fin 4) (s : ℝ), IsUnitSign s → euclidNorm (signedAxis μ s) = 1) ∧
  (∀ (μ ν : Fin 4) (s t : ℝ), μ < ν → IsUnitSign s → IsUnitSign t →
    euclidNorm (signedDiagonal μ ν s t) = 1) ∧
  (∀ (μ₁ μ₂ : Fin 4) (s₁ s₂ : ℝ), IsUnitSign s₁ → IsUnitSign s₂ →
    signedAxis μ₁ s₁ = signedAxis μ₂ s₂ → μ₁ = μ₂ ∧ s₁ = s₂) ∧
  (∀ (μ₁ ν₁ μ₂ ν₂ : Fin 4) (s₁ t₁ s₂ t₂ : ℝ), μ₁ < ν₁ → μ₂ < ν₂ →
    IsUnitSign s₁ → IsUnitSign t₁ → IsUnitSign s₂ → IsUnitSign t₂ →
    signedDiagonal μ₁ ν₁ s₁ t₁ = signedDiagonal μ₂ ν₂ s₂ t₂ →
      μ₁ = μ₂ ∧ ν₁ = ν₂ ∧ s₁ = s₂ ∧ t₁ = t₂) ∧
  (∀ (κ μ ν : Fin 4) (r s t : ℝ), μ < ν → IsUnitSign r → IsUnitSign s → IsUnitSign t →
    signedAxis κ r ≠ signedDiagonal μ ν s t) ∧
  reflectionNormals.ncard = 32
def ReflectionNormalsModSign : Prop :=
  normalRepresentatives.ncard = 16 ∧
    ∀ v ∈ reflectionNormals, ∃! n, n ∈ normalRepresentatives ∧ (v = n ∨ v = -n)
def ReflectAcrossTimeAxis : Prop :=
  reflectAcross (coordVec 3) = YangMills.Construction.TimeAxis.timeReflection ∧
    ∀ (E : Type) (f : AmbientSpace → E), reflectFun (coordVec 3) f = timeReflected f
def PlaneNormalsEight : Prop :=
  planeReflectionNormals = {v | ∃ j : ℤ, v = planeUnit ((j : ℝ) * Real.pi / 4)} ∧
  planeReflectionNormals = {coordVec 3, -coordVec 3, coordVec 0, -coordVec 0,
    diagNormalPlus, -diagNormalPlus, diagNormalMinus, -diagNormalMinus} ∧
  planeReflectionNormals.ncard = 8 ∧
  diagNormalPlus = planeUnit (Real.pi / 4) ∧
  diagNormalMinus = planeUnit (-(Real.pi / 4))
def IsPlaneOrthoBasis (b : AmbientSpace × AmbientSpace) : Prop :=
  euclidDot b.1 b.1 = 1 ∧ euclidDot b.2 b.2 = 1 ∧ euclidDot b.1 b.2 = 0 ∧
    ((Submodule.span ℝ ({b.1, b.2} : Set AmbientSpace) : Submodule ℝ AmbientSpace) : Set AmbientSpace) = coordPlane
def PlaneUnitsAndFrames : Prop :=
  (∀ (θ θ' : ℝ) (u : AmbientSpace), u = planeUnit θ →
    planePerp u = planeUnit (θ + Real.pi / 2) ∧
    IsPlaneOrthoBasis (planeOrthoFrame u) ∧
    Real.cos θ' • u + Real.sin θ' • planePerp u = planeUnit (θ + θ') ∧
    rotateInPlane θ' (planeUnit θ) = planeUnit (θ + θ')) ∧
  ∀ v ∈ coordPlane, euclidNorm v = 1 → ∃ θ : ℝ, v = planeUnit θ
def rightAngleRotation : Module.End ℝ AmbientSpace := rotateInPlane (Real.pi / 2)
def DihedralAndRightAngle : Prop :=
  (∃ H : Subgroup (Equiv.Perm AmbientSpace), H ≤ hyperoctahedralPerms ∧
    (H : Set (Equiv.Perm AmbientSpace)) = dihedralInPlane) ∧
  dihedralInPlane.ncard = 8 ∧
  (∀ r ∈ dihedralInPlane, ⇑r '' coordPlane = coordPlane ∧
    ∀ y z : Fin 2 → ℝ, r (assemble y z) = assemble (planeCoords (r (embedPlane y))) z) ∧
  (∃ r ∈ dihedralInPlane, ⇑r = ⇑rightAngleRotation) ∧
  (rightAngleRotation ^ 0) (coordVec 3) = coordVec 3 ∧
  (rightAngleRotation ^ 1) (coordVec 3) = coordVec 0 ∧
  (rightAngleRotation ^ 2) (coordVec 3) = -coordVec 3 ∧
  (rightAngleRotation ^ 3) (coordVec 3) = -coordVec 0 ∧
  (rightAngleRotation ^ 0) diagNormalPlus = diagNormalPlus ∧
  (rightAngleRotation ^ 1) diagNormalPlus = -diagNormalMinus ∧
  (rightAngleRotation ^ 2) diagNormalPlus = -diagNormalPlus ∧
  (rightAngleRotation ^ 3) diagNormalPlus = diagNormalMinus
def TensorPlateSupport : Prop :=
  (∀ α ∈ cc1Plane, ∀ φ ∈ transProfiles,
    tensorPlate α φ ∈ compactC1Complex ∧
      tsupport (tensorPlate α φ) = {x | planeCoords x ∈ tsupport α ∧ transCoords x ∈ tsupport φ}) ∧
  ∀ α ∈ cc1Plane, ∀ α' ∈ cc1Plane, ∀ φ ∈ transProfiles,
    Disjoint (tsupport α) (tsupport α') → DisjointSupports (tensorPlate α φ) (tensorPlate α' φ)
def ProfileCorrProperties : Prop :=
  ∀ φ ∈ transProfiles, ∀ ψ ∈ transProfiles,
    (∀ ζ, (profileCorr φ ψ ζ).im = 0) ∧
      Continuous (profileCorr φ ψ) ∧ IsCompact (tsupport (profileCorr φ ψ))
namespace ReflectionsPlaneFacts
def Statement : Prop :=
  ReflectionNormalsCount ∧ ReflectionNormalsModSign ∧ ReflectAcrossTimeAxis ∧
    PlaneNormalsEight ∧ PlaneUnitsAndFrames ∧ DihedralAndRightAngle ∧
    TensorPlateSupport ∧ ProfileCorrProperties
end ReflectionsPlaneFacts
end YangMills.Construction.TwoPoints
end
