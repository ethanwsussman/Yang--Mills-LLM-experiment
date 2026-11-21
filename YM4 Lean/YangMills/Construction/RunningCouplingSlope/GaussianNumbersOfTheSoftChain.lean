import YangMills.Construction.RunningCouplingSlope.SoftChainOnATower
import YangMills.Construction.RunningCouplingSlope.VolumeFactorsOfLinearMaps
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
open Tower Matrices
variable {L m k : ℕ}
def fibreMove (X : ChainPoint L m k) (ξ : LevelForms L m k) : ChainPoint L m k :=
  ⟨(expMove ξ X).fine, fun i e =>
    open Classical in
      if i.val + 1 = k then
        levelField X (i + 1) e.1 * (normalizedMean (levelField (expMove ξ X) i) e.1)⁻¹
      else (expMove ξ X).noise i e⟩
def fibreSecondDeriv (a : ℝ) (X : ChainPoint L m k) (ξ ξ' : LevelForms L m k) : ℝ :=
  deriv (fun s : ℝ => deriv (fun t : ℝ => chainAction a (fibreMove X (s • ξ + t • ξ'))) 0) 0
def IsFibreHessian (a : ℝ) (X : ChainPoint L m k)
    (T : QuadraticForm ℝ (LinearMap.ker (topDeriv X))) : Prop :=
  ∀ ξ : LinearMap.ker (topDeriv X), T ξ = fibreSecondDeriv a X ξ ξ
def fibreHessian (a : ℝ) (X : ChainPoint L m k) :
    QuadraticForm ℝ (LinearMap.ker (topDeriv X)) :=
  Classical.epsilon (IsFibreHessian a X)
def IsLevelCore (c : InnerProductSpace.Core ℝ (LevelForms L m k)) : Prop :=
  ∀ ξ ξ' : LevelForms L m k, c.inner ξ ξ' = levelPairing (formValues ξ) (formValues ξ')
def LevelFormsEuclidean (L m k : ℕ) : Prop :=
  FiniteDimensional ℝ (LevelForms L m k) ∧
    ∃ c : InnerProductSpace.Core ℝ (LevelForms L m k), IsLevelCore c
def levelGaussianNumber (M : LevelForms L m k →ₗ[ℝ] edgeFormSpace L m k k)
    (T : QuadraticForm ℝ (LinearMap.ker M)) : ℝ :=
  open Classical in
  if h : LevelFormsEuclidean L m k ∧ EdgeFormsEuclidean L m k k then
    haveI := h.1.1
    haveI := h.2.1
    GaussianConstraint.constrainedGaussianNumberOfCores h.1.2.choose h.2.2.choose M T
  else 0
def levelSaddleDet (X : LevelForms L m k →ₗ[ℝ] LevelForms L m k)
    (M : LevelForms L m k →ₗ[ℝ] edgeFormSpace L m k k) : ℝ :=
  open Classical in
  if h : LevelFormsEuclidean L m k ∧ EdgeFormsEuclidean L m k k then
    haveI := h.1.1
    haveI := h.2.1
    GaussianConstraint.saddleDetOfCores h.1.2.choose h.2.2.choose X M
  else 0
def topVanishingGauges (L m k : ℕ) : Submodule ℝ (vertexFunctionSpace L m k 0) where
  carrier := {l | ∀ y : Vertex L m k k,
    restrictVertexFunction k (l : Vertex L m k 0 → ComplexMatrix2) y = 0}
  add_mem' := by
    intro a b ha hb y
    have h1 := ha y
    have h2 := hb y
    simp only [restrictVertexFunction, PeriodicLattice.restrictGaugeMap] at h1 h2 ⊢
    simp [h1, h2]
  zero_mem' := by
    intro y
    simp [restrictVertexFunction, PeriodicLattice.restrictGaugeMap]
  smul_mem' := by
    intro c a ha y
    have h1 := ha y
    simp only [restrictVertexFunction, PeriodicLattice.restrictGaugeMap] at h1 ⊢
    simp [h1]
def sliceOrbitVolume {Y : Type} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
    [FiniteDimensional ℝ Y] (X : ChainPoint L m k) (l : LevelForms L m k →ₗ[ℝ] Y) : ℝ :=
  open Classical in
  if h : VertexFunctionsEuclidean L m k 0 then
    haveI := h.1
    letI := h.2.choose.toNormedAddCommGroup
    letI := InnerProductSpace.ofCore h.2.choose.toCore
    LinearConstraint.absDetOfMap (l ∘ₗ gaugeOrbitMap X ∘ₗ (topVanishingGauges L m k).subtype)
  else 0
def IsGaugeTransform (X : ChainPoint L m k)
    (T : LevelForms L m k →ₗ[ℝ] LevelForms L m k) : Prop :=
  ∀ ξ, formValues (T ξ) = formValues ξ + gaugeOrbitValues X (gaugeCorrection X ξ)
def gaugeTransform (X : ChainPoint L m k) : LevelForms L m k →ₗ[ℝ] LevelForms L m k :=
  Classical.epsilon (IsGaugeTransform X)
def gaugedFormValue (a : ℝ) (X : ChainPoint L m k) (J : LevelForms L m k)
    (μ : edgeFormSpace L m k k) (ξ : LevelForms L m k) : ℝ :=
  leftSecondDeriv (chainAction a) X ξ ξ +
    2 * levelPairing (formValues J) (chainBracket X (gaugeCorrection X ξ) (formValues ξ)) +
    levelPairing (formValues J)
      (chainBracket X (gaugeCorrection X ξ) (gaugeOrbitValues X (gaugeCorrection X ξ))) -
    (traceFinsumPairing (restrictToPositiveEdges (μ : Edge L m k k → ComplexMatrix2))
      (topSecondVariation X (gaugeTransform X ξ) (gaugeTransform X ξ))).re
def gaugedRightValue (a : ℝ) (X : ChainPoint L m k) (J : LevelForms L m k)
    (μ : edgeFormSpace L m k k) (ξ : LevelForms L m k) : ℝ :=
  gaugedFormValue a X J μ ξ +
    traceFinsumNorm (gaugeSliceResidual X.fine ξ.1 : Vertex L m k 0 → ComplexMatrix2) ^ 2
def IsGaugedOperator (a : ℝ) (X : ChainPoint L m k) (J : LevelForms L m k)
    (μ : edgeFormSpace L m k k) (T : LevelForms L m k →ₗ[ℝ] LevelForms L m k) : Prop :=
  (∀ ξ ξ' : LevelForms L m k,
    levelPairing (formValues ξ) (formValues (T ξ')) =
      levelPairing (formValues (T ξ)) (formValues ξ')) ∧
    ∀ ξ : LevelForms L m k,
      levelPairing (formValues ξ) (formValues (T ξ)) = gaugedRightValue a X J μ ξ
def gaugedOperator (a : ℝ) (X : ChainPoint L m k) (J : LevelForms L m k)
    (μ : edgeFormSpace L m k k) : LevelForms L m k →ₗ[ℝ] LevelForms L m k :=
  Classical.epsilon (IsGaugedOperator a X J μ)
def composedCubeAverageLinear (X : ChainPoint L m k) :
    vertexFunctionSpace L m k 0 →ₗ[ℝ] vertexFunctionSpace L m k k :=
  linearMapWithValues _ _ (composedCubeAverage X k)
def ghostBlockOperator (X : ChainPoint L m k) :
    (vertexFunctionSpace L m k 0 × vertexFunctionSpace L m k k) →ₗ[ℝ]
      vertexFunctionSpace L m k 0 × vertexFunctionSpace L m k k :=
  ((covDiffRealTranspose L m k X.fine ∘ₗ covDiffLinear L m k X.fine).coprod
      (iterAverageRealTranspose L m k X.fine)).prod
    (composedCubeAverageLinear X ∘ₗ LinearMap.fst ℝ _ _)
def chainFreeEnergy (a : ℝ) (X : ChainPoint L m k) (J : LevelForms L m k)
    (μ : edgeFormSpace L m k k) : ℝ :=
  -(1 / 2) * Real.log |levelSaddleDet (gaugedOperator a X J μ) (shiftedGaugeMap X)| +
    3 / 2 * logRadiusSum X + Real.log |LinearMap.det (ghostBlockOperator X)|
def IsCompactValued (X : ChainPoint L m k) : Prop :=
  (∀ i e, X.noise i e ∈ PeriodicLattice.compactGaugeGroup) ∧
    ∀ j ≤ k, levelField X j ∈ fieldSpace L m k j
structure IsMinimizerOver (a : ℝ) (W : Edge L m k k → ComplexMatrix2) (X : ChainPoint L m k) :
    Prop where
  compact : IsCompactValued X
  top_eq : levelField X k = W
  le : ∀ X' : ChainPoint L m k, IsCompactValued X' → levelField X' k = W →
    chainAction a X ≤ chainAction a X'
def IsLevelGradient (F : ChainPoint L m k → ℝ) (X : ChainPoint L m k)
    (J : LevelForms L m k) : Prop :=
  ∀ ξ, levelPairing (formValues J) (formValues ξ) = leftDeriv F X ξ
def IsTopMultiplier (X : ChainPoint L m k) (J : LevelForms L m k)
    (μ : edgeFormSpace L m k k) : Prop :=
  ∀ ξ, levelPairing (formValues J) (formValues ξ) =
    (edgeFormPairing (μ : Edge L m k k → ComplexMatrix2)
      (topDeriv X ξ : Edge L m k k → ComplexMatrix2)).re
def normSqForm {E Y : Type} [AddCommGroup E] [Module ℝ E] [NormedAddCommGroup Y]
    [InnerProductSpace ℝ Y] (l : E →ₗ[ℝ] Y) : QuadraticForm ℝ E :=
  LinearMap.BilinMap.toQuadraticMap ((innerₗ Y).compl₁₂ l l)
def chainLogWeight {Y : Type} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
    [FiniteDimensional ℝ Y] (a : ℝ) (X : ChainPoint L m k) (l : LevelForms L m k →ₗ[ℝ] Y) : ℝ :=
  Real.log (levelGaussianNumber (topDeriv X)
      (fibreHessian a X + (normSqForm l).comp (LinearMap.ker (topDeriv X)).subtype) *
    sliceOrbitVolume X l) + 3 / 2 * logRadiusSum X
def IsTransversalSlice {Y : Type} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
    (X : ChainPoint L m k) (l : LevelForms L m k →ₗ[ℝ] Y) : Prop :=
  Function.Bijective (l ∘ₗ gaugeOrbitMap X ∘ₗ (topVanishingGauges L m k).subtype)
end YangMills.Construction.RunningCouplingSlope
end
