import YangMills.Construction.SpectralTheory.SemigroupsOfSelfAdjointContractions
import YangMills.Construction.SpectralTheory.StronglyContinuousUnitaryGroups
import Mathlib
set_option autoImplicit false
open MeasureTheory Set Filter Topology
open scoped Matrix NNReal
noncomputable section
namespace YangMills.Construction.SemigroupRepresentation
open YangMills.Construction.BorelSpectral YangMills.Construction.HilbertSpaceBasics YangMills.Construction.SpectralTheorem YangMills.Construction.SelfAdjointFunctions YangMills.Construction.ContractionSemigroups YangMills.Construction.UnitaryGroups
variable {n : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
def nonnegHalfSpace (n : ℕ) : Set (Fin (n + 1) → ℝ) := {y | 0 ≤ y 0}
theorem measurableSet_nonnegHalfSpace (n : ℕ) : MeasurableSet (nonnegHalfSpace n) :=
  measurableSet_le measurable_const (measurable_pi_apply 0)
def spatialCoords (y : Fin (n + 1) → ℝ) : Fin n → ℝ := fun i => y i.succ
theorem measurable_spatialCoords : Measurable (spatialCoords (n := n)) :=
  measurable_pi_iff.mpr fun i => measurable_pi_apply i.succ
structure IsCommutingSemigroupRep (T : ℝ≥0 → H →L[ℂ] H) (U : (Fin n → ℝ) → H →L[ℂ] H) :
    Prop where
  isContractionSemigroup : IsSelfAdjointContractionSemigroup T
  isUnitaryRep : IsUnitaryRep U
  tendstoStrongly_zero : TendstoStrongly U (𝓝 0) 1
  commute : ∀ a t, U a * T t = T t * U a
def momentumOp (U : (Fin n → ℝ) → H →L[ℂ] H) (i : Fin n) : UnboundedOp H :=
  stoneGenerator fun s => U (s • Pi.single i 1)
def energyMomentumOps (T : ℝ≥0 → H →L[ℂ] H) (U : (Fin n → ℝ) → H →L[ℂ] H) :
    Fin (n + 1) → UnboundedOp H :=
  Fin.cons (semigroupGenerator T) (momentumOp U)
def IsJointSpectralMeasure (E : SpectralMeasure (nonnegHalfSpace n) H) (T : ℝ≥0 → H →L[ℂ] H)
    (U : (Fin n → ℝ) → H →L[ℂ] H) : Prop :=
  ∀ t a, T t * U a = E.integralOp fun y =>
    Complex.exp (((-(t : ℝ) * y.1 0 : ℝ) : ℂ) + Complex.I * ((a ⬝ᵥ spatialCoords y.1 : ℝ) : ℂ))
def jointSpectralMeasure (T : ℝ≥0 → H →L[ℂ] H) (U : (Fin n → ℝ) → H →L[ℂ] H) :
    SpectralMeasure (nonnegHalfSpace n) H :=
  haveI : Nonempty (SpectralMeasure (nonnegHalfSpace n) H) :=
    ⟨YangMills.Construction.JointSpectral.dirac (Nat.succ_pos n)
      (measurableSet_nonnegHalfSpace n) ⟨0, le_refl (0 : ℝ)⟩⟩
  Classical.epsilon fun E => IsJointSpectralMeasure E T U
def extendToWhole (E : SpectralMeasure (nonnegHalfSpace n) H) :
    SpectralMeasure (FullSpace (n + 1)) H :=
  E.extendCarrier (subset_univ _) MeasurableSet.univ
def IsUnitaryJointMeasure (E' : SpectralMeasure (FullSpace (n + 1)) H)
    (T : ℝ≥0 → H →L[ℂ] H) (U : (Fin n → ℝ) → H →L[ℂ] H) : Prop :=
  ∀ (τ : ℝ) a, expI (semigroupGenerator T) τ * U a = E'.integralOp fun y =>
    Complex.exp (Complex.I * ((τ * y.1 0 + a ⬝ᵥ spatialCoords y.1 : ℝ) : ℂ))
def projSpatial (y : nonnegHalfSpace n) : FullSpace n := ⟨spatialCoords y.1, mem_univ _⟩
theorem measurable_projSpatial : Measurable (projSpatial (n := n)) :=
  (measurable_spatialCoords.comp measurable_subtype_coe).subtype_mk
def spatialMarginal (hn : 1 ≤ n) (E : SpectralMeasure (nonnegHalfSpace n) H) :
    SpectralMeasure (FullSpace n) H :=
  E.pushforward hn MeasurableSet.univ projSpatial measurable_projSpatial
def JointSpectralTheoremForPair : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (n : ℕ)
    (hn : 1 ≤ n),
    (∀ (T : ℝ≥0 → H →L[ℂ] H) (U : (Fin n → ℝ) → H →L[ℂ] H), IsCommutingSemigroupRep T U →
      IsStronglyCont U ∧
      (∃! E : SpectralMeasure (nonnegHalfSpace n) H, IsJointSpectralMeasure E T U) ∧
      IsJointSpectralMeasure (jointSpectralMeasure T U) T U ∧
      IsSpectralIntegralOf (semigroupGenerator T) (jointSpectralMeasure T U)
        (fun y => ((y.1 0 : ℝ) : ℂ)) ∧
      (∀ i, IsSpectralIntegralOf (momentumOp U i) (jointSpectralMeasure T U)
        fun y => ((y.1 i.succ : ℝ) : ℂ)) ∧
      (extendToWhole (jointSpectralMeasure T U)).coordMarginal 0 =
        spectralMeasure (semigroupGenerator T) ∧
      (∀ i, (extendToWhole (jointSpectralMeasure T U)).coordMarginal i.succ =
        spectralMeasure (momentumOp U i)) ∧
      PairwiseStronglyCommute (energyMomentumOps T U) ∧
      (∀ a, U a = jointExpI (momentumOp U) a) ∧
      (∀ B : H →L[ℂ] H, Commute B (T 1) → (∀ a, Commute B (U a)) →
        ∀ Δ, Commute B (jointSpectralMeasure T U Δ)) ∧
      IsUnitaryJointMeasure (extendToWhole (jointSpectralMeasure T U)) T U ∧
      (∀ E' : SpectralMeasure (FullSpace (n + 1)) H, IsUnitaryJointMeasure E' T U →
        E' = extendToWhole (jointSpectralMeasure T U)) ∧
      RepresentsGroup (spatialMarginal hn (jointSpectralMeasure T U)) U ∧
      ∀ E'' : SpectralMeasure (FullSpace n) H, RepresentsGroup E'' U →
        E'' = spatialMarginal hn (jointSpectralMeasure T U)) ∧
    ∀ U : (Fin n → ℝ) → H →L[ℂ] H, IsUnitaryRep U → TendstoStrongly U (𝓝 0) 1 →
      (∃! E : SpectralMeasure (FullSpace n) H, RepresentsGroup E U) ∧
      RepresentsGroup (groupSpectralMeasure hn U) U
end YangMills.Construction.SemigroupRepresentation
