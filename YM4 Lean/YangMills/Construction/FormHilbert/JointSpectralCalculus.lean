import YangMills.Construction.HilbertSpace.FormCompletionsAndBorelPVMs
import Mathlib
set_option autoImplicit false
open MeasureTheory Set Filter Topology
open scoped ComplexConjugate
noncomputable section
namespace YangMills.Construction.FormHilbert
open JointSpectrum
def levelOneSet (J : Type*) : MeasSubset J :=
  ⟨{p | p.1 = 1}, measurable_fst (measurableSet_singleton _)⟩
def levelZeroSet (J : Type*) : MeasSubset J :=
  ⟨{p | p.1 = 0}, measurable_fst (measurableSet_singleton _)⟩
def positiveLevelSet (J : Type*) : MeasSubset J :=
  ⟨{p | 0 < (p.1 : ℝ)}, measurableSet_lt measurable_const (measurable_subtype_coe.comp measurable_fst)⟩
def phaseOneSet {J : Type*} [Fintype J] (l : J) : MeasSubset J :=
  ⟨{p | p.2 l = 1}, ((measurable_pi_apply l).comp measurable_snd) (measurableSet_singleton _)⟩
section Objects
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {J : Type*} [Fintype J] [Nonempty J]
def HasSpectralMoments (S : CommutingFamily H J) (x : H) (m : Measure (SpectralDomain J)) : Prop :=
  IsFiniteMeasure m ∧ ∀ (n : ℕ) (w : J → ℤ),
    ∫ p, spectralMonomial n w p ∂m = inner ℂ x ((S.A ^ n * S.unitaryMonomial w) x)
def spectralMomentMeasure (S : CommutingFamily H J) (x : H) : Measure (SpectralDomain J) :=
  Classical.epsilon (HasSpectralMoments S x)
def spectralSqrt (E : BorelPVM J H) : H →L[ℂ] H :=
  E.spectralOp fun p => (((p.1 : ℝ) ^ (1 / 2 : ℝ) : ℝ) : ℂ)
structure BoundedFunctionalCalculus (S : CommutingFamily H J) (E : BorelPVM J H) :
    Prop where
  exists_spectralOp : ∀ φ, IsBddMeasurable φ → ∃ A, E.IsSpectralIntegral φ A
  spectralOp_add_smul : ∀ φ φ', IsBddMeasurable φ → IsBddMeasurable φ' → ∀ c : ℂ,
    E.spectralOp (fun p => φ p + c * φ' p) = E.spectralOp φ + c • E.spectralOp φ'
  spectralOp_mul : ∀ φ φ', IsBddMeasurable φ → IsBddMeasurable φ' →
    E.spectralOp (fun p => φ p * φ' p) = E.spectralOp φ * E.spectralOp φ'
  inner_spectralOp : ∀ φ, IsBddMeasurable φ → ∀ x y : H,
    inner ℂ y (E.spectralOp φ x) = inner ℂ (E.spectralOp (fun p => conj (φ p)) y) x
  norm_spectralOp_sq : ∀ φ, IsBddMeasurable φ → ∀ x : H,
    ‖E.spectralOp φ x‖ ^ 2 = ∫ p, ‖φ p‖ ^ 2 ∂(spectralMomentMeasure S x)
  integral_norm_sq_le : ∀ φ, IsBddMeasurable φ → ∀ x : H,
    ∫ p, ‖φ p‖ ^ 2 ∂(spectralMomentMeasure S x) ≤ (⨆ p, ‖φ p‖) ^ 2 * ‖x‖ ^ 2
  spectralOp_monomial : ∀ (n : ℕ) (w : J → ℤ),
    E.spectralOp (spectralMonomial n w) = S.A ^ n * S.unitaryMonomial w
  momentMeasure_spectralOp : ∀ φ, IsBddMeasurable φ → ∀ x : H,
    spectralMomentMeasure S (E.spectralOp φ x) =
      densityMeasure (fun p => ‖φ p‖ ^ 2) (spectralMomentMeasure S x)
  spectralOp_congr : ∀ φ φ', IsBddMeasurable φ → IsBddMeasurable φ' → ∀ Δ : MeasSubset J,
    E Δ = 0 → (∀ p, p ∉ Δ.1 → φ p = φ' p) → E.spectralOp φ = E.spectralOp φ'
def BoundedPointwiseStrongConvergence (E : BorelPVM J H) : Prop :=
  ∀ (φs : ℕ → SpectralDomain J → ℂ) (φ : SpectralDomain J → ℂ),
    (∀ k, Measurable (φs k)) → Measurable φ → (∃ C : ℝ, ∀ k p, ‖φs k p‖ ≤ C) →
    (∀ p, Tendsto (fun k => φs k p) atTop (𝓝 (φ p))) →
    StrongTendsto (fun k => E.spectralOp (φs k)) (E.spectralOp φ)
def RealFunctionalCalculus (E : BorelPVM J H) : Prop :=
  ∀ (φ : SpectralDomain J → ℝ) (hφ : Measurable φ), (∃ C : ℝ, ∀ p, |φ p| ≤ C) →
    IsSelfAdjoint (E.spectralOp fun p => (φ p : ℂ)) ∧
      (0 ≤ E.spectralOp (fun p => (φ p : ℂ)) ↔
        E.IsSupportedOn ⟨{p | 0 ≤ φ p}, measurableSet_le measurable_const hφ⟩)
structure KernelProjections (S : CommutingFamily H J)
    (E : BorelPVM J H) : Prop where
  oneLevel : IsOrthProjOnto (E (levelOneSet J)) {x | (1 - S.A) x = 0}
  zeroLevel : IsOrthProjOnto (E (levelZeroSet J)) {x | S.A x = 0}
  phaseFixed : ∀ l, IsOrthProjOnto (E (phaseOneSet l))
    {x | (1 - (S.B l : H →L[ℂ] H)) x = 0}
  tendsto_pow : StrongTendsto (fun n => S.A ^ n) (E (levelOneSet J))
  tendsto_cesaro : ∀ l, StrongTendsto
    (fun n : ℕ => (n : ℂ)⁻¹ • ∑ k ∈ Finset.range n, (S.B l : H →L[ℂ] H) ^ k)
    (E (phaseOneSet l))
structure SpectralSqrtProperties (S : CommutingFamily H J) (E : BorelPVM J H) :
    Prop where
  selfAdjoint : IsSelfAdjoint (spectralSqrt E)
  sq_eq : spectralSqrt E * spectralSqrt E = S.A
  commute_A : Commute (spectralSqrt E) S.A
  commute_B : ∀ l, Commute (spectralSqrt E) (S.B l : H →L[ℂ] H)
  closure_range_eq : closure (range (spectralSqrt E)) = range (E (positiveLevelSet J))
  positiveLevel_range : range (E (positiveLevelSet J)) = orthSet {x | S.A x = 0}
end Objects
section Transport
variable {H H' : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']
  {J : Type*} [Fintype J] [Nonempty J]
structure IntertwinesIsometrically (S : CommutingFamily H J) (S' : CommutingFamily H' J)
    (W : H' →L[ℂ] H) : Prop where
  inner_map : ∀ x y, inner ℂ (W x) (W y) = inner ℂ x y
  intertwine_A : W ∘L S'.A = S.A ∘L W
  intertwine_B : ∀ l, W ∘L (S'.B l : H' →L[ℂ] H') = (S.B l : H →L[ℂ] H) ∘L W
end Transport
def JointSpectralCalculusTheorem : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (J : Type) [Fintype J] [Nonempty J] (S : CommutingFamily H J),
    (∀ x, (∃! m, HasSpectralMoments S x m) ∧ HasSpectralMoments S x (spectralMomentMeasure S x)) ∧
    (∃! E, IsJointPVM S E) ∧
    ∀ E, IsJointPVM S E →
      (∀ (x : H) (Δ : MeasSubset J),
        inner ℂ x (E Δ x) = (((spectralMomentMeasure S x).real Δ.1 : ℝ) : ℂ)) ∧
      BoundedFunctionalCalculus S E ∧
      BoundedPointwiseStrongConvergence E ∧
      RealFunctionalCalculus E ∧
      KernelProjections S E ∧
      SpectralSqrtProperties S E ∧
      ∀ (H' : Type) [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']
        (S' : CommutingFamily H' J) (E' : BorelPVM J H'),
        IsJointPVM S' E' →
        ∀ W : H' →L[ℂ] H, IntertwinesIsometrically S S' W →
          (∀ x, spectralMomentMeasure S' x = spectralMomentMeasure S (W x)) ∧
          ∀ φ, IsBddMeasurable φ → W ∘L E'.spectralOp φ = E.spectralOp φ ∘L W
end YangMills.Construction.FormHilbert
