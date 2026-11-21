import YangMills.Construction.SpectralTheory.MatrixMeasuresAndCommutation
import YangMills.Construction.MeasureTheory.FourMeasureIntegral
import Mathlib
set_option autoImplicit false
open MeasureTheory
open scoped ComplexConjugate InnerProductSpace
noncomputable section
namespace YangMills.Construction.SpectralFromScalar
open SetFunctions (CountablyAdditiveFn)
open BorelSpectral
variable {X : Type*}
def AllBoundedMeasurable [MeasurableSpace X] (G : Set (X → ℂ)) : Prop :=
  ∀ g ∈ G, Measurable g ∧ ∃ c : ℝ, ∀ x, ‖g x‖ ≤ c
def SeparatesComplexMeasures [MeasurableSpace X] (G : Set (X → ℂ)) : Prop :=
  ∀ ν : CountablyAdditiveFn X, (∀ g ∈ G, BorelComplexMeasures.integralOf ν.1 g = 0) →
    ∀ S, ν.1 S = 0
structure IsConjClosedUnital (G : Set (X → ℂ)) : Prop where
  contains_one : (fun _ => 1) ∈ G
  closed_mul : ∀ g ∈ G, ∀ h ∈ G, (fun x => g x * h x) ∈ G
  closed_conj : ∀ g ∈ G, (fun x => conj (g x)) ∈ G
structure IsStarHomOn {K : Type*} [NormedAddCommGroup K]
    [InnerProductSpace ℂ K] {G : Set (X → ℂ)} (hG : IsConjClosedUnital G)
    (Φ : G → K →L[ℂ] K) : Prop where
  preserves_one : Φ ⟨_, hG.contains_one⟩ = 1
  preserves_mul : ∀ g h : G, Φ ⟨_, hG.closed_mul g g.2 h h.2⟩ = Φ g * Φ h
  preserves_adjoint : ∀ g : G, OperatorTransport.IsBoundedAdjoint (Φ ⟨_, hG.closed_conj g g.2⟩) (Φ g)
def HasDiagonalMeasures [MeasurableSpace X] {K : Type*} [NormedAddCommGroup K]
    [InnerProductSpace ℂ K] {G : Set (X → ℂ)} (Φ : G → K →L[ℂ] K) (ρ : K → Measure X) : Prop :=
  ∀ v, IsFiniteMeasure (ρ v) ∧ ∀ g : G, ⟪v, Φ g v⟫_ℂ = ∫ x, g.1 x ∂ρ v
def ScalarDeterminationTheorem : Prop :=
  ∀ (K : Type) [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K] (n : ℕ), 1 ≤ n →
    ∀ X : Set (Fin n → ℝ), MeasurableSet X → X.Nonempty →
    ∀ G : Set (X → ℂ), AllBoundedMeasurable G → SeparatesComplexMeasures G →
      (∀ E E' : SpectralMeasure X K,
        (∀ g ∈ G, E.integralOp g = E'.integralOp g) → E = E') ∧
      (∀ (E : SpectralMeasure X K) (T : K →L[ℂ] K),
        (∀ g ∈ G, Commute T (E.integralOp g)) →
          SpectralMeasure.OpCommutes T E) ∧
      ∀ (hG : IsConjClosedUnital G) (Φ : G → K →L[ℂ] K) (ρ : K → Measure X),
        IsStarHomOn hG Φ → HasDiagonalMeasures Φ ρ →
          (∃! E : SpectralMeasure X K, ∀ g : G, Φ g = E.integralOp g) ∧
          ∀ E : SpectralMeasure X K, (∀ g : G, Φ g = E.integralOp g) →
            ∀ v, E.diagMeasure v = ρ v
end YangMills.Construction.SpectralFromScalar
