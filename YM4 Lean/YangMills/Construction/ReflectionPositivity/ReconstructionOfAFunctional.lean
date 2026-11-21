import YangMills.Construction.ReflectionPositivity.FormOfAFunctionalOnSeparatedTuples
import YangMills.Construction.SpectralTheory.FunctionsOfSelfAdjointOperators
import Mathlib
set_option autoImplicit false
open MeasureTheory Set Filter Topology
open scoped ComplexOrder InnerProductSpace NNReal
noncomputable section
namespace YangMills.Construction
namespace ReflectionPositivity.Reconstruction
open SeparatedTuples ReflectionPositivity.TupleForm HilbertSpaceBasics
open InfiniteLattice (AmbientSpace)
open BorelSpectral SpectralTheorem SelfAdjointFunctions
open JointSpectral (dirac)
abbrev temporalHyperplane : Mirrors.ReflectingHyperplane :=
  Mirrors.axialHyperplane TimeAxis.timeIdx 0
def timeBasisVec : AmbientSpace := PeriodicLattice.coordVec TimeAxis.timeIdx
def embedSpatial (a : Fin 3 → ℝ) : AmbientSpace := ![a 0, a 1, a 2, 0]
def spatialBasisVec (i : Fin 3) : Fin 3 → ℝ := Pi.single i 1
structure ContractionHypotheses (σ : TupleFunctional) (S : Set ℝ) : Prop where
  continuous : σ.IsAdmissiblyContinuous
  translateInvariant : σ.IsTranslateInvariant
  reflectionPositive : σ.IsReflectionPositive temporalHyperplane
  subset_pos : S ⊆ Ioi 0
  dense : Ioi 0 ⊆ closure S
  contraction : ∀ (F : PositiveSpan), ∀ t ∈ S,
    reflectedCorrelation σ F ((2 * t) • timeBasisVec) ≤ reflectionForm σ F F
section Objects
variable (σ : TupleFunctional) (hσ : IsPosSemidef (reflectionForm σ))
abbrev PhysicalSpace : Type := FormCompletion (reflectionForm σ) hσ
abbrev posClass : PositiveSpan →ₗ[ℂ] PhysicalSpace σ hσ := completionClass (reflectionForm σ) hσ
open Classical in
def spanClass (G : FormalSpan) : PhysicalSpace σ hσ :=
  if hG : G ∈ spanIn TimeAxis.upperHalfSpace then posClass σ hσ ⟨G, hG⟩ else 0
def posTupleVec (X : supportedIn TimeAxis.upperHalfSpace) : PositiveSpan :=
  ⟨basisVec X.1, Submodule.subset_span ⟨X, rfl⟩⟩
def vacuum : PhysicalSpace σ hσ :=
  posClass σ hσ (posTupleVec ⟨SepTuple.nil, nil_mem_supportedIn _⟩)
def IsTimeShiftFamily (T : ℝ≥0 → PhysicalSpace σ hσ →L[ℂ] PhysicalSpace σ hσ) : Prop :=
  ∀ (t : ℝ≥0) (F : PositiveSpan),
    T t (posClass σ hσ F) =
      spanClass σ hσ (pushSpan (translate ((t : ℝ) • timeBasisVec)) F.1)
def timeShift : ℝ≥0 → PhysicalSpace σ hσ →L[ℂ] PhysicalSpace σ hσ :=
  Classical.epsilon (IsTimeShiftFamily σ hσ)
def IsHamiltonianOp (A : UnboundedOp (PhysicalSpace σ hσ)) : Prop :=
  IsNonnegOp A ∧ ∀ t, timeShift σ hσ t = expNeg A t
def hamiltonian : UnboundedOp (PhysicalSpace σ hσ) := Classical.epsilon (IsHamiltonianOp σ hσ)
def IsSpaceShiftFamily (U : (Fin 3 → ℝ) → PhysicalSpace σ hσ →L[ℂ] PhysicalSpace σ hσ) : Prop :=
  ∀ (a : Fin 3 → ℝ) (F : PositiveSpan),
    U a (posClass σ hσ F) =
      spanClass σ hσ (pushSpan (translate (embedSpatial a)) F.1)
def spaceShift : (Fin 3 → ℝ) → PhysicalSpace σ hσ →L[ℂ] PhysicalSpace σ hσ :=
  Classical.epsilon (IsSpaceShiftFamily σ hσ)
def IsMomentumOp (i : Fin 3) (P : UnboundedOp (PhysicalSpace σ hσ)) : Prop :=
  IsSelfAdjointOp P ∧
    ∀ s : ℝ, spaceShift σ hσ (s • spatialBasisVec i) = expI P s
def momentum (i : Fin 3) : UnboundedOp (PhysicalSpace σ hσ) :=
  Classical.epsilon (IsMomentumOp σ hσ i)
def nonnegHalfPlane : Set (Fin 2 → ℝ) := {y | 0 ≤ y 0}
theorem measurableSet_nonnegHalfPlane : MeasurableSet nonnegHalfPlane :=
  measurableSet_le measurable_const (measurable_pi_apply 0)
def IsJointSpectralMeasure (i : Fin 3)
    (E : SpectralMeasure nonnegHalfPlane (PhysicalSpace σ hσ)) : Prop :=
  ∀ (t : ℝ≥0) (s : ℝ),
    expNeg (hamiltonian σ hσ) t * expI (momentum σ hσ i) s =
      E.integralOp fun y =>
        Complex.exp (((-(t : ℝ) * y.1 0 : ℝ) : ℂ) + Complex.I * ((s * y.1 1 : ℝ) : ℂ))
def jointSpectralMeasure (i : Fin 3) : SpectralMeasure nonnegHalfPlane (PhysicalSpace σ hσ) :=
  haveI : Nonempty (SpectralMeasure nonnegHalfPlane (PhysicalSpace σ hσ)) :=
    ⟨dirac (by norm_num) measurableSet_nonnegHalfPlane ⟨0, by simp [nonnegHalfPlane]⟩⟩
  Classical.epsilon (IsJointSpectralMeasure σ hσ i)
def energyBand (B : BorelSubsets ℝ) : BorelSubsets nonnegHalfPlane :=
  ⟨{y | y.1 0 ∈ B.1}, ((measurable_pi_apply 0).comp measurable_subtype_coe) B.2⟩
def momentumBand (B : BorelSubsets ℝ) : BorelSubsets nonnegHalfPlane :=
  ⟨{y | y.1 1 ∈ B.1}, ((measurable_pi_apply 1).comp measurable_subtype_coe) B.2⟩
end Objects
def fivePointCombination (σ : TupleFunctional) (F : PositiveSpan) (t : ℝ) (i : Fin 3) : ℂ :=
  reflectedCorrelation σ F 0 - 4 * reflectedCorrelation σ F (t • timeBasisVec) +
    reflectedCorrelation σ F ((2 * t) • timeBasisVec) +
    reflectedCorrelation σ F (t • timeBasisVec + t • embedSpatial (spatialBasisVec i)) +
    reflectedCorrelation σ F (t • timeBasisVec - t • embedSpatial (spatialBasisVec i))
def VacuumProperties (σ : TupleFunctional) (hσ : IsPosSemidef (reflectionForm σ)) : Prop :=
  IsHermitianForm (reflectionForm σ) ∧ ‖vacuum σ hσ‖ = 1 ∧
    ∀ X : supportedIn TimeAxis.upperHalfSpace,
      ⟪posClass σ hσ (posTupleVec X), vacuum σ hσ⟫_ℂ = ((σ X.1 : ℝ) : ℂ) ∧
      ⟪vacuum σ hσ, posClass σ hσ (posTupleVec X)⟫_ℂ = ((σ X.1 : ℝ) : ℂ)
def SemigroupProperties (σ : TupleFunctional) (hσ : IsPosSemidef (reflectionForm σ)) : Prop :=
  (∃! T, IsTimeShiftFamily σ hσ T) ∧ IsTimeShiftFamily σ hσ (timeShift σ hσ) ∧
    IsStronglyCont (timeShift σ hσ) ∧ IsOpSemigroup (timeShift σ hσ) ∧
    (∀ t, IsSelfAdjoint (timeShift σ hσ t) ∧ IsContraction (timeShift σ hσ t) ∧
      ∀ ψ, timeShift σ hσ t ψ = 0 → ψ = 0) ∧
    (∃! A, IsHamiltonianOp σ hσ A) ∧ IsHamiltonianOp σ hσ (hamiltonian σ hσ) ∧
    ∃ hΩ : vacuum σ hσ ∈ (hamiltonian σ hσ).domain, hamiltonian σ hσ ⟨vacuum σ hσ, hΩ⟩ = 0
def SpatialProperties (σ : TupleFunctional) (hσ : IsPosSemidef (reflectionForm σ)) : Prop :=
  (∃! U, IsSpaceShiftFamily σ hσ U) ∧ IsSpaceShiftFamily σ hσ (spaceShift σ hσ) ∧
    IsStronglyCont (spaceShift σ hσ) ∧
    IsUnitaryRep (spaceShift σ hσ) ∧
    (∀ a t, Commute (spaceShift σ hσ a) (timeShift σ hσ t)) ∧
    (∀ a, spaceShift σ hσ a (vacuum σ hσ) = vacuum σ hσ) ∧
    (∀ i, ∃! P, IsMomentumOp σ hσ i P) ∧ (∀ i, IsMomentumOp σ hσ i (momentum σ hσ i)) ∧
    (∀ i, ∃ hΩ : vacuum σ hσ ∈ (momentum σ hσ i).domain,
      momentum σ hσ i ⟨vacuum σ hσ, hΩ⟩ = 0) ∧
    ∀ (i i' : Fin 3) (s s' : ℝ),
      Commute (expI (momentum σ hσ i) s) (expI (momentum σ hσ i') s')
def MatrixElementFormula (σ : TupleFunctional) (hσ : IsPosSemidef (reflectionForm σ)) : Prop :=
  ∀ (F F' : PositiveSpan) (t : ℝ≥0) (a : Fin 3 → ℝ),
    ⟪posClass σ hσ F,
      timeShift σ hσ t (spaceShift σ hσ a (posClass σ hσ F'))⟫_ℂ =
      σ.spanExtension (formalMul (reflectConj F)
        (pushSpan (translate ((t : ℝ) • timeBasisVec + embedSpatial a)) F'.1))
def JointSpectralProperties (σ : TupleFunctional) (hσ : IsPosSemidef (reflectionForm σ)) :
    Prop :=
  ∀ i : Fin 3,
    (∃! E, IsJointSpectralMeasure σ hσ i E) ∧
    IsJointSpectralMeasure σ hσ i (jointSpectralMeasure σ hσ i) ∧
    (∀ B : BorelSubsets ℝ, jointSpectralMeasure σ hσ i (energyBand B) =
      spectralMeasure (hamiltonian σ hσ) (realLineSet B)) ∧
    (∀ B : BorelSubsets ℝ, jointSpectralMeasure σ hσ i (momentumBand B) =
      spectralMeasure (momentum σ hσ i) (realLineSet B)) ∧
    IsSpectralIntegralOf (hamiltonian σ hσ) (jointSpectralMeasure σ hσ i)
      (fun y => ((y.1 0 : ℝ) : ℂ)) ∧
    IsSpectralIntegralOf (momentum σ hσ i) (jointSpectralMeasure σ hσ i)
      (fun y => ((y.1 1 : ℝ) : ℂ))
def SpectralConeProperties (σ : TupleFunctional) (hσ : IsPosSemidef (reflectionForm σ)) :
    Prop :=
  ∀ (i : Fin 3) (S : Set ℝ), S ⊆ Ioi 0 → (0 : ℝ) ∈ closure S →
    (∀ (F : PositiveSpan), ∀ t ∈ S, 0 ≤ fivePointCombination σ F t i) →
    (jointSpectralMeasure σ hσ i).essSupport ⊆ {y | |y 1| ≤ y 0} ∧
    ((hamiltonian σ hσ).domain : Set (PhysicalSpace σ hσ)) ⊆ (momentum σ hσ i).domain ∧
    (∀ ψ : (hamiltonian σ hσ).domain, ∃ hP : (ψ : PhysicalSpace σ hσ) ∈
      (absOp (momentum σ hσ i)).domain,
      ⟪(ψ : PhysicalSpace σ hσ), absOp (momentum σ hσ i) ⟨ψ, hP⟩⟫_ℂ ≤
        ⟪(ψ : PhysicalSpace σ hσ), hamiltonian σ hσ ψ⟫_ℂ) ∧
    ∀ ψ : (hamiltonian σ hσ).domain, hamiltonian σ hσ ψ = 0 →
      ∀ s : ℝ, expI (momentum σ hσ i) s ψ = ψ
def ReconstructionTheorem : Prop :=
  ∀ (σ : TupleFunctional) (S : Set ℝ), ContractionHypotheses σ S →
    ∃ hσ : IsPosSemidef (reflectionForm σ),
      VacuumProperties σ hσ ∧ SemigroupProperties σ hσ ∧ SpatialProperties σ hσ ∧
        MatrixElementFormula σ hσ ∧ JointSpectralProperties σ hσ ∧
        SpectralConeProperties σ hσ
end ReflectionPositivity.Reconstruction
end YangMills.Construction
