import YangMills.Construction.Continuum.StabiliserOfTheTimeVectorIsometriesAndSymbols
import YangMills.Construction.EuclideanBorel.RepresentationSpectralMeasure
import YangMills.Construction.HilbertSpaces.FormsCompletionsAndExtensionByDensity
import YangMills.Construction.SpectralMeasures.SpectralProjectionsFunctionsAndStrongCommutation
import Mathlib
set_option autoImplicit false
open Set Filter Topology
open scoped NNReal ComplexOrder InnerProductSpace
noncomputable section
namespace YangMills.Construction.PositiveFormReconstruction
open YangMills.Construction.EuclideanBorel (Space BorelSubset IsPVM SpectralIntegralIs
  IsSpectralIntegralOp IsSpectralMeasureOf StronglyCommute CoordOpGeAbs expNegMul zeroExtend
  pushforward spectralIntegral IsSupportedOnPVM jointSpectrum spectralParamCoord liftFromLine
  momentumCoord momentumExpChar momentumVec negLogOnPosRay expIMul openPosRay pvmSupport
  spectralMeasureOf spectralResolution sqIntegrableDomain appendCoords expMomentumOp)
open YangMills.Construction.FormsOperators (TendstoStrongly IsContractive IsSesquilinear
  IsLoewnerGE IsHermitianForm IsInnerProductForm IsNonneg IsOrthProjOnto IsPositiveBounded
  IsPosSemidefForm IsSelfAdj HasCountableDenseSet IsC0Semigroup IsStronglyContUnitaryRep
  IsUnitaryRep UnitaryMap ker complexLine formRadical ofCLM formOnQuotient)
open YangMills.Construction.TimeAxisSymbols (spatialPart spatialBasisVec timeAxisStabilizer)
open YangMills.Construction.SpectralTheory (UnboundedOp)
structure PreHilbertData (V : Type*) [AddCommGroup V] [Module ℂ V] where
  form : V → V → ℂ
  unitVec : V
  semigroupMap : ℝ≥0 → V →ₗ[ℂ] V
  translationMap : Space 3 → V →ₗ[ℂ] V
  rotationMap : timeAxisStabilizer → V →ₗ[ℂ] V
def rotateSpatial (w : timeAxisStabilizer) (a : Space 3) : Space 3 :=
  WithLp.toLp 2 (spatialPart w a.ofLp)
structure PreHilbertData.IsAdmissible {V : Type*} [AddCommGroup V] [Module ℂ V]
    (D : PreHilbertData V) : Prop where
  hermitian : IsHermitianForm D.form
  posSemidef : IsPosSemidefForm D.form
  form_unitVec : D.form D.unitVec D.unitVec = 1
  semigroupMap_zero : D.semigroupMap 0 = LinearMap.id
  translationMap_zero : D.translationMap 0 = LinearMap.id
  rotationMap_one : D.rotationMap 1 = LinearMap.id
  semigroupMap_comp : ∀ s s', D.semigroupMap s ∘ₗ D.semigroupMap s' = D.semigroupMap (s + s')
  translationMap_comp : ∀ b b',
    D.translationMap b ∘ₗ D.translationMap b' = D.translationMap (b + b')
  rotationMap_comp : ∀ w w', D.rotationMap w ∘ₗ D.rotationMap w' = D.rotationMap (w * w')
  translationMap_comm : ∀ b s,
    D.translationMap b ∘ₗ D.semigroupMap s = D.semigroupMap s ∘ₗ D.translationMap b
  rotationMap_comm : ∀ w s,
    D.rotationMap w ∘ₗ D.semigroupMap s = D.semigroupMap s ∘ₗ D.rotationMap w
  rotationMap_translationMap : ∀ w b,
    D.rotationMap w ∘ₗ D.translationMap b = D.translationMap (rotateSpatial w b) ∘ₗ D.rotationMap w
  semigroupMap_unitVec : ∀ s, D.semigroupMap s D.unitVec = D.unitVec
  translationMap_unitVec : ∀ b, D.translationMap b D.unitVec = D.unitVec
  rotationMap_unitVec : ∀ w, D.rotationMap w D.unitVec = D.unitVec
  form_semigroupMap : ∀ s x y, D.form x (D.semigroupMap s y) = D.form (D.semigroupMap s x) y
  form_translationMap : ∀ b x y,
    D.form (D.translationMap b x) (D.translationMap b y) = D.form x y
  form_rotationMap : ∀ w x y, D.form (D.rotationMap w x) (D.rotationMap w y) = D.form x y
  bddAbove_semigroup : ∀ x, BddAbove (range fun s => ‖D.form x (D.semigroupMap s x)‖)
  tendsto_semigroup : ∀ x,
    Tendsto (fun s => D.form x (D.semigroupMap s x)) (𝓝[>] 0) (𝓝 (D.form x x))
  tendsto_translation : ∀ x,
    Tendsto (fun b => D.form x (D.translationMap b x)) (𝓝 0) (𝓝 (D.form x x))
def energyCoordIndex : Fin (1 + 3) := Fin.castAdd 3 0
def momentumCoordIndex (i : Fin 3) : Fin (1 + 3) := Fin.natAdd 1 i
def spatialBasis (i : Fin 3) : Space 3 := WithLp.toLp 2 (spatialBasisVec i)
def energyMomentumChar (τ : ℝ) (a : Space 3) : Space (1 + 3) → ℂ :=
  fun y => Complex.exp (Complex.I * ((τ * y energyCoordIndex + inner ℝ a (momentumVec y) : ℝ) : ℂ))
def expNegEnergy (s : ℝ≥0) : Space (1 + 3) → ℂ :=
  fun y => Complex.exp (-((s : ℝ) : ℂ) * ((y energyCoordIndex : ℝ) : ℂ))
theorem measurable_momentumVec : Measurable momentumVec := by
  refine Continuous.measurable ?_
  unfold EuclideanBorel.momentumVec
  fun_prop
def rotateMomentum (w : timeAxisStabilizer) (y : Space (1 + 3)) : Space (1 + 3) :=
  appendCoords 1 3 (WithLp.toLp 2 fun _ => y energyCoordIndex, rotateSpatial w (momentumVec y))
section Operators
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
def IsExpNegMul (A : UnboundedOp H) (s : ℝ≥0) (B : H →L[ℂ] H) : Prop :=
  sqIntegrableDomain (spectralResolution A)
      (liftFromLine fun x => Complex.exp (-((s : ℝ) : ℂ) * (x : ℂ))) = univ ∧
    ∀ ψ, expNegMul A s ψ = B ψ.1
def IsSemigroupGenerator (B : ℝ≥0 → H →L[ℂ] H) (A : UnboundedOp H) : Prop :=
  IsSelfAdj A ∧ IsNonneg A ∧ ∀ s, IsExpNegMul A s (B s)
def semigroupGenerator (B : ℝ≥0 → H →L[ℂ] H) : UnboundedOp H :=
  Classical.epsilon (IsSemigroupGenerator B)
def IsNegLogOf (A : UnboundedOp H) (B : H →L[ℂ] H) : Prop :=
  IsSupportedOnPVM (spectralResolution (ofCLM B)) openPosRay ∧
    IsSpectralIntegralOp A (spectralResolution (ofCLM B))
      (zeroExtend openPosRay negLogOnPosRay)
def kerProjection (A : UnboundedOp H) : H →L[ℂ] H :=
  Classical.epsilon fun P => IsOrthProjOnto P (ker A)
def toCLM (U : UnitaryMap H H) : H →L[ℂ] H :=
  (U.toContinuousLinearEquiv : H →L[ℂ] H)
def unitaryStar (U : UnitaryMap H H) : H →L[ℂ] H :=
  toCLM U.symm
def IsJointSpectralMeasure (A : UnboundedOp H) (V : Space 3 → UnitaryMap H H)
    (E : BorelSubset (1 + 3) → H →L[ℂ] H) : Prop :=
  IsPVM E ∧ ∀ (τ : ℝ) (a : Space 3),
    sqIntegrableDomain E (energyMomentumChar τ a) = univ ∧
      ∀ ψ : sqIntegrableDomain E (energyMomentumChar τ a),
        ∃ h : V a ψ.1 ∈ sqIntegrableDomain (spectralResolution A)
            (liftFromLine fun x => Complex.exp (Complex.I * (τ : ℂ) * (x : ℂ))),
          spectralIntegral E (energyMomentumChar τ a) ψ =
            expIMul A τ ⟨V a ψ.1, h⟩
def jointSpectralMeasure (A : UnboundedOp H) (V : Space 3 → UnitaryMap H H) :
    BorelSubset (1 + 3) → H →L[ℂ] H :=
  Classical.epsilon (IsJointSpectralMeasure A V)
def momentumOp (E : BorelSubset (1 + 3) → H →L[ℂ] H) (i : Fin 3) : UnboundedOp H :=
  Classical.epsilon fun P => IsSpectralIntegralOp P E (momentumCoord i)
def momentumMarginal (E : BorelSubset (1 + 3) → H →L[ℂ] H) : BorelSubset 3 → H →L[ℂ] H :=
  pushforward E momentumVec measurable_momentumVec
end Operators
section Objects
variable {V : Type*} [AddCommGroup V] [Module ℂ V]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (D : PreHilbertData V) (hs : IsSesquilinear D.form)
  (j : (V ⧸ formRadical D.form hs) →ₗ[ℂ] H)
def embed (x : V) : H := j (Submodule.Quotient.mk x)
def vacuum : H := embed D hs j D.unitVec
def CLMExtends (R : V →ₗ[ℂ] V) (B : H →L[ℂ] H) : Prop :=
  ∀ x, B (embed D hs j x) = embed D hs j (R x)
def UnitaryExtends (R : V →ₗ[ℂ] V) (U : UnitaryMap H H) : Prop :=
  ∀ x, U (embed D hs j x) = embed D hs j (R x)
def transferOp (s : ℝ≥0) : H →L[ℂ] H :=
  Classical.epsilon (CLMExtends D hs j (D.semigroupMap s))
def translationOp (a : Space 3) : UnitaryMap H H :=
  Classical.epsilon (UnitaryExtends D hs j (D.translationMap a))
def rotationOp (w : timeAxisStabilizer) : UnitaryMap H H :=
  Classical.epsilon (UnitaryExtends D hs j (D.rotationMap w))
def hamiltonian : UnboundedOp H := semigroupGenerator (transferOp D hs j)
def jointMeasure : BorelSubset (1 + 3) → H →L[ℂ] H :=
  jointSpectralMeasure (hamiltonian D hs j) (translationOp D hs j)
end Objects
section Requirements
variable {V : Type*} [AddCommGroup V] [Module ℂ V]
  (D : PreHilbertData V) (hs : IsSesquilinear D.form)
def QuotientInnerProduct : Prop :=
  ((formRadical D.form hs : Submodule ℂ V) : Set V) = {x | D.form x x = 0} ∧
    (∀ x y : V, formOnQuotient D.form hs (Submodule.Quotient.mk x) (Submodule.Quotient.mk y) =
      D.form x y) ∧
    IsInnerProductForm (formOnQuotient D.form hs)
def SemigroupMapsContract : Prop :=
  (∀ s x, D.form (D.semigroupMap s x) (D.semigroupMap s x) ≤ D.form x x) ∧
    ∀ s, ∀ x ∈ formRadical D.form hs, D.semigroupMap s x ∈ formRadical D.form hs
def secondDifferenceMap (i : Fin 3) (s : ℝ≥0) : V →ₗ[ℂ] V :=
  LinearMap.id - (4 : ℂ) • D.semigroupMap s + D.semigroupMap (2 * s) +
    D.semigroupMap s ∘ₗ D.translationMap ((s : ℝ) • spatialBasis i) +
    D.semigroupMap s ∘ₗ D.translationMap ((-(s : ℝ)) • spatialBasis i)
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (j : (V ⧸ formRadical D.form hs) →ₗ[ℂ] H)
def VacuumNormSeparable : Prop :=
  ‖vacuum D hs j‖ = 1 ∧
    ∀ V₀ : Set V, V₀.Countable →
      (∀ (x : V) (ε : ℝ), 0 < ε → ∃ x₀ ∈ V₀, D.form (x - x₀) (x - x₀) < (ε : ℂ)) →
      HasCountableDenseSet H
def TransferSemigroupCondition : Prop :=
  (∀ s, CLMExtends D hs j (D.semigroupMap s) (transferOp D hs j s)) ∧
    IsC0Semigroup (transferOp D hs j) ∧
    (∀ s, IsPositiveBounded (transferOp D hs j s) ∧
      IsSelfAdj (ofCLM (transferOp D hs j s)) ∧
      IsContractive (transferOp D hs j s)) ∧
    (∀ s, transferOp D hs j s (vacuum D hs j) = vacuum D hs j) ∧
    (∀ s, ker (ofCLM (transferOp D hs j s)) = {0}) ∧
    ExistsUnique (IsSemigroupGenerator (transferOp D hs j)) ∧
    IsSemigroupGenerator (transferOp D hs j) (hamiltonian D hs j) ∧
    IsNegLogOf (hamiltonian D hs j) (transferOp D hs j 1) ∧
    vacuum D hs j ∈ ker (hamiltonian D hs j) ∧
    IsOrthProjOnto (kerProjection (hamiltonian D hs j))
      (ker (hamiltonian D hs j)) ∧
    TendstoStrongly atTop (transferOp D hs j) (kerProjection (hamiltonian D hs j))
def TranslationCondition : Prop :=
  (∀ a, UnitaryExtends D hs j (D.translationMap a) (translationOp D hs j a)) ∧
    IsStronglyContUnitaryRep (translationOp D hs j) ∧
    (∀ a, translationOp D hs j a (vacuum D hs j) = vacuum D hs j) ∧
    (∀ a s, toCLM (translationOp D hs j a) * transferOp D hs j s =
      transferOp D hs j s * toCLM (translationOp D hs j a)) ∧
    ExistsUnique (IsJointSpectralMeasure (hamiltonian D hs j) (translationOp D hs j)) ∧
    IsJointSpectralMeasure (hamiltonian D hs j) (translationOp D hs j)
      (jointMeasure D hs j) ∧
    IsSpectralIntegralOp (hamiltonian D hs j) (jointMeasure D hs j) spectralParamCoord ∧
    (∀ s, SpectralIntegralIs (jointMeasure D hs j) (expNegEnergy s)
      (transferOp D hs j s)) ∧
    IsSpectralMeasureOf (translationOp D hs j)
      (momentumMarginal (jointMeasure D hs j)) ∧
    momentumMarginal (jointMeasure D hs j) =
      spectralMeasureOf (translationOp D hs j) ∧
    (∀ i, IsSpectralIntegralOp (momentumOp (jointMeasure D hs j) i)
        (jointMeasure D hs j) (momentumCoord i) ∧
      IsSelfAdj (momentumOp (jointMeasure D hs j) i)) ∧
    (∀ a, sqIntegrableDomain (jointMeasure D hs j) (momentumExpChar a) = univ ∧
      ∀ ψ, expMomentumOp (jointMeasure D hs j) a ψ =
        translationOp D hs j a ψ.1) ∧
    StronglyCommute ![hamiltonian D hs j, momentumOp (jointMeasure D hs j) 0,
      momentumOp (jointMeasure D hs j) 1,
      momentumOp (jointMeasure D hs j) 2] ∧
    jointSpectrum (jointMeasure D hs j) =
      pvmSupport (jointMeasure D hs j) ∧
    pvmSupport (jointMeasure D hs j) ⊆ {y | 0 ≤ y energyCoordIndex}
def RotationUnitarity : Prop :=
  (∀ w, UnitaryExtends D hs j (D.rotationMap w) (rotationOp D hs j w)) ∧
    IsUnitaryRep (rotationOp D hs j) ∧
    (∀ w, rotationOp D hs j w (vacuum D hs j) = vacuum D hs j) ∧
    (∀ w s, toCLM (rotationOp D hs j w) * transferOp D hs j s =
      transferOp D hs j s * toCLM (rotationOp D hs j w)) ∧
    (∀ w, FormsOperators.unitaryConjugate (rotationOp D hs j w) (hamiltonian D hs j) =
      hamiltonian D hs j) ∧
    (∀ w a, FormsOperators.unitaryConjugate (rotationOp D hs j w)
        (ofCLM (toCLM (translationOp D hs j a))) =
      ofCLM (toCLM (translationOp D hs j (rotateSpatial w a)))) ∧
    ∀ w, rotateMomentum w '' pvmSupport (jointMeasure D hs j) =
      pvmSupport (jointMeasure D hs j)
def SecondDifferenceBound (i : Fin 3) (s : ℝ≥0) : Prop :=
  IsLoewnerGE ((1 - transferOp D hs j s) ^ 2)
    (transferOp D hs j s *
      ((2 : ℂ) • 1 - toCLM (translationOp D hs j ((s : ℝ) • spatialBasis i)) -
        unitaryStar (translationOp D hs j ((s : ℝ) • spatialBasis i))))
def EnergyBoundsMomentum : Prop :=
  (∀ (i : Fin 3) (s : ℝ≥0), 0 < s → (∀ x, 0 ≤ D.form x (secondDifferenceMap D i s x)) →
    SecondDifferenceBound D hs j i s) ∧
    ∀ (i : Fin 3) (τ : ℕ → ℝ≥0), (∀ k, 0 < τ k) → Antitone τ → Tendsto τ atTop (𝓝 0) →
      (∀ k, SecondDifferenceBound D hs j i (τ k)) →
      CoordOpGeAbs (jointMeasure D hs j) energyCoordIndex (momentumCoordIndex i)
def KerEqVacuumLine : Prop :=
  (∀ x y, Tendsto (fun s => D.form x (D.semigroupMap s y)) atTop
    (𝓝 (D.form x D.unitVec * D.form D.unitVec y))) →
    ker (hamiltonian D hs j) = complexLine (vacuum D hs j)
end Requirements
end YangMills.Construction.PositiveFormReconstruction
