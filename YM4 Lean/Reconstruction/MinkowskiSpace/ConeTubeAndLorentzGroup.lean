import YangMills.Construction.MinkowskiSpace.MinkowskiFormConesLorentzGroupAndEuclideanPoints
import Mathlib
set_option autoImplicit false
open Complex Matrix
noncomputable section
namespace YangMills.Construction.MinkowskiSpace
def conjByWick (M : ComplexMat4) : ComplexMat4 :=
  LinearMap.toMatrix' (wickMap.toLinearMap ∘ₗ M.mulVecLin ∘ₗ
    wickMap.symm.toLinearMap)
def conjByWickInv (M : ComplexMat4) : ComplexMat4 :=
  LinearMap.toMatrix' (wickMap.symm.toLinearMap ∘ₗ M.mulVecLin ∘ₗ
    wickMap.toLinearMap)
def rotationSumOne (R : Matrix.orthogonalGroup (Fin 3) ℝ) : RealMat4 :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv
    (Matrix.fromBlocks (R : Matrix (Fin 3) (Fin 3) ℝ) 0 0 (1 : Matrix (Fin 1) (Fin 1) ℝ))
def euclidTimeUnit : Fin 4 → ℝ := ![0, 0, 0, 1]
def ofSpaceEuclid (v : Fin 3 → ℝ) : Fin 4 → ℝ := ![v 0, v 1, v 2, 0]
def spaceDot (v : Fin 3 → ℝ) (x : Fin 4 → ℝ) : ℝ :=
  v 0 * x 0 + v 1 * x 1 + v 2 * x 2
def imagBoostRotationMap (v : unitSphere3) (a : ℝ) : (Fin 4 → ℝ) →ₗ[ℝ] (Fin 4 → ℝ) where
  toFun x := x +
    (Real.cos a - 1) •
      (x 3 • euclidTimeUnit + spaceDot v x • ofSpaceEuclid v) +
    Real.sin a •
      (spaceDot v x • euclidTimeUnit - x 3 • ofSpaceEuclid v)
  map_add' x y := by
    have hxy : spaceDot v (x + y) =
        spaceDot v x + spaceDot v y := by
      simp only [spaceDot, Pi.add_apply]
      ring
    funext μ
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hxy]
    ring
  map_smul' t x := by
    have htx : spaceDot v (t • x) = t * spaceDot v x := by
      simp only [spaceDot, Pi.smul_apply, smul_eq_mul]
      ring
    funext μ
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, htx, RingHom.id_apply]
    ring
def imagBoostRotation (v : unitSphere3) (a : ℝ) : RealMat4 :=
  LinearMap.toMatrix' (imagBoostRotationMap v a)
theorem imagBoostRotation_mulVec (v : unitSphere3) (a : ℝ) (x : Fin 4 → ℝ) :
    imagBoostRotation v a *ᵥ x = imagBoostRotationMap v a x :=
  LinearMap.toMatrix'_mulVec _ _
def spaceAxisOne : unitSphere3 :=
  ⟨![1, 0, 0], by simp [unitSphere3, spaceNorm, Fin.sum_univ_three]⟩
def poincareInv (g : RealVec4 × RealMat4) : RealVec4 × RealMat4 :=
  (-(g.2⁻¹ *ᵥ g.1), g.2⁻¹)
def IsMatrixGroup {R : Type*} [CommRing R] (S : Set (Matrix (Fin 4) (Fin 4) R)) : Prop :=
  1 ∈ S ∧ (∀ A ∈ S, ∀ B ∈ S, A * B ∈ S) ∧ ∀ A ∈ S, IsUnit A.det ∧ A⁻¹ ∈ S
namespace ConeTubeLorentz
def ConeGapBounds : Prop :=
  (∀ (t : ℝ) (y : RealVec4), 0 ≤ t → coneGap (t • y) = t * coneGap y) ∧
    (∀ y y' : RealVec4, coneGap (y + y') ≥ coneGap y + coneGap y') ∧
    ∀ y y' : RealVec4,
      coneGap (y + y') ≥ coneGap y - |y' 0| - spaceNorm (spacePart y')
def ConesTubeConvex : Prop :=
  Convex ℝ futureCone ∧ (∀ t : ℝ, 0 < t → ∀ y ∈ futureCone, t • y ∈ futureCone) ∧
    Convex ℝ closedFutureCone ∧
    (∀ t : ℝ, 0 < t → ∀ y ∈ closedFutureCone, t • y ∈ closedFutureCone) ∧
    (∀ y ∈ closedFutureCone, ∀ y' ∈ futureCone, y + y' ∈ futureCone) ∧
    Convex ℝ futureTube ∧
    ∀ b : ℕ, Convex ℝ (Set.univ.pi fun _ : Fin b => futureTube)
def FormOnClosedCone : Prop :=
  ∀ y ∈ closedFutureCone, ∀ p ∈ closedFutureCone,
    (minkowskiForm (toComplex y) (toComplex p)).re ≥ coneGap y * p 0 ∧ coneGap y * p 0 ≥ 0 ∧
      TorusMetric.euclidNormVec p ≤ Real.sqrt 2 * p 0
def WickMapFormulas : Prop :=
  (∀ x x' : ComplexVec4,
      minkowskiForm (wickMap x) (wickMap x') = -∑ μ, x μ * x' μ) ∧
    (∀ R : Matrix.orthogonalGroup (Fin 4) ℝ,
      conjByWick (toComplexMatrix (R : RealMat4)) ∈ lorentzGroupC) ∧
    (∀ Z : ComplexMat4, Z ∈ lorentzAlgebraC ↔
      (conjByWickInv Z)ᵀ = -conjByWickInv Z) ∧
    lorentzAlgebraC = Submodule.span ℂ
      {Z | ∃ A : RealMat4, Aᵀ = -A ∧ Z = conjByWick (toComplexMatrix A)} ∧
    (∀ x : ComplexVec4, imPart (wickMap x) =
      mkTimeSpace (x 3).re ![(x 0).im, (x 1).im, (x 2).im]) ∧
    (∀ x : RealVec4, wickMap (toComplex x) ∈ futureTube ↔ x 3 > 0) ∧
    (∀ x : RealVec4, conjPoint (wickMap (toComplex x)) =
      wickMap (toComplex (TestSpaces.timeReflect x))) ∧
    ∀ R : Matrix.orthogonalGroup (Fin 3) ℝ,
      conjByWick (toComplexMatrix (rotationSumOne R)) = rotationMatrix R
def BoostsAndRotations : Prop :=
  (∀ (v : unitSphere3) (β : ℂ), boostMatrix v β ∈ lorentzGroupC) ∧
    (∀ (v : unitSphere3) (β β' : ℂ), boostMatrix v β * boostMatrix v β' = boostMatrix v (β + β')) ∧
    (∃ P : Fin 4 → Fin 4 → MvPolynomial (Fin 5) ℂ,
      ∀ (v : unitSphere3) (β : ℂ) (μ ν : Fin 4), boostMatrix v β μ ν =
        MvPolynomial.aeval
          ![Complex.cosh β, Complex.sinh β, ((v : Fin 3 → ℝ) 0 : ℂ), ((v : Fin 3 → ℝ) 1 : ℂ),
            ((v : Fin 3 → ℝ) 2 : ℂ)] (P μ ν)) ∧
    ∀ (v : unitSphere3) (a : ℝ),
      imagBoostRotation v a ∈ Matrix.specialOrthogonalGroup (Fin 4) ℝ ∧
        ∀ x : ComplexVec4, boostMatrix v (I * a) *ᵥ wickMap x =
          wickMap (toComplexMatrix (imagBoostRotation v a) *ᵥ x)
def TubeGapUnderImagBoosts : Prop :=
  (∀ a : ℝ, 0 ≤ a → a ≤ 1 → ∀ (v : unitSphere3) (ζ : ComplexVec4),
      tubeGap (boostMatrix v (I * a) *ᵥ ζ) ≥ tubeGap ζ - a * l1Norm ζ) ∧
    ∀ (x : RealVec4) (ε a : ℝ), 0 ≤ ε → 0 ≤ a → a ≤ 1 → ∀ v : unitSphere3,
      imPart (boostMatrix v (I * a) *ᵥ (toComplex x + I • toComplex (ε • timeUnit))) =
          (ε * Real.cos a) • timeUnit +
            Real.sin a • (((v : Fin 3 → ℝ) ⬝ᵥ spacePart x) • timeUnit + x 0 • ofSpaceVector v) ∧
        tubeGap (boostMatrix v (I * a) *ᵥ (toComplex x + I • toComplex (ε • timeUnit))) =
          ε * Real.cos a + Real.sin a * ((v : Fin 3 → ℝ) ⬝ᵥ spacePart x - |x 0|)
def RealBoostsRotationsRestricted : Prop :=
  (∀ (v : unitSphere3) (β : ℝ), ∃ Λ ∈ restrictedLorentz, toComplexMatrix Λ = boostMatrix v β ∧
      (fun y => Λ *ᵥ y) '' futureCone = futureCone) ∧
    ∀ R : Matrix.orthogonalGroup (Fin 3) ℝ, (R : Matrix (Fin 3) (Fin 3) ℝ).det = 1 →
      ∃ Λ ∈ restrictedLorentz, toComplexMatrix Λ = rotationMatrix R ∧
        (fun y => Λ *ᵥ y) '' futureCone = futureCone
def RestrictedLorentzDecomposition : Prop :=
  ∀ Λ ∈ restrictedLorentz, ∃ R₁ R₂ : Matrix.orthogonalGroup (Fin 3) ℝ, ∃ β : ℝ,
    (R₁ : Matrix (Fin 3) (Fin 3) ℝ).det = 1 ∧ (R₂ : Matrix (Fin 3) (Fin 3) ℝ).det = 1 ∧ 0 ≤ β ∧
      toComplexMatrix Λ = rotationMatrix R₁ * boostMatrix spaceAxisOne β * rotationMatrix R₂
def RestrictedLorentzGroupPreserves : Prop :=
  IsMatrixGroup restrictedLorentz ∧
    ∀ Λ ∈ restrictedLorentz,
      (fun y => Λ *ᵥ y) '' futureCone = futureCone ∧
        (fun y => Λ *ᵥ y) '' closedFutureCone = closedFutureCone ∧
        (fun ζ => toComplexMatrix Λ *ᵥ ζ) '' futureTube = futureTube ∧
        |Λ.det| = 1
def LorentzGroupCIsGroup : Prop :=
  (∀ Λ ∈ lorentzGroupC, IsUnit Λ) ∧ IsMatrixGroup lorentzGroupC
def PoincareGroupAction : Prop :=
  ((0, 1) : RealVec4 × RealMat4) ∈ restrictedPoincare ∧
    (∀ g ∈ restrictedPoincare, ∀ g' ∈ restrictedPoincare, poincareMul g g' ∈ restrictedPoincare) ∧
    (∀ g ∈ restrictedPoincare, ∀ g' ∈ restrictedPoincare, ∀ g'' ∈ restrictedPoincare,
      poincareMul (poincareMul g g') g'' = poincareMul g (poincareMul g' g'')) ∧
    (∀ g ∈ restrictedPoincare, poincareMul (0, 1) g = g ∧ poincareMul g (0, 1) = g) ∧
    (∀ g ∈ restrictedPoincare, poincareInv g ∈ restrictedPoincare ∧
      poincareMul g (poincareInv g) = (0, 1) ∧
      poincareMul (poincareInv g) g = (0, 1)) ∧
    ∀ g ∈ restrictedPoincare, ∀ g' ∈ restrictedPoincare, ∀ x : RealVec4,
      poincareSMul (poincareMul g g') x = poincareSMul g (poincareSMul g' x)
def SpacelikeSetOpenConnected : Prop :=
  IsOpen spacelikeSet ∧ IsConnected spacelikeSet
def Statement : Prop :=
  ConeGapBounds ∧ ConesTubeConvex ∧ FormOnClosedCone ∧
    WickMapFormulas ∧ BoostsAndRotations ∧ TubeGapUnderImagBoosts ∧
    RealBoostsRotationsRestricted ∧ RestrictedLorentzDecomposition ∧
    RestrictedLorentzGroupPreserves ∧ LorentzGroupCIsGroup ∧
    PoincareGroupAction ∧ SpacelikeSetOpenConnected
end ConeTubeLorentz
end YangMills.Construction.MinkowskiSpace
end
