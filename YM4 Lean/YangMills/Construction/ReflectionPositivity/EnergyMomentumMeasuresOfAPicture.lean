import YangMills.Construction.ReflectionPositivity.PicturesOfADirectionAndEnergyMomentumMeasures
import YangMills.Construction.ReflectionPositivity.SetOfTheSpectralVariablesThatCarriesTheSpectrum
import Mathlib
set_option autoImplicit false
open MeasureTheory Set Filter Topology
open scoped ENNReal ComplexConjugate
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.DirectionPictures
open YangMills.Construction.ReflectionPositivity.MirrorHyperplanes (unitPositiveClass)
open YangMills.Construction.HilbertSpace (SesqForm)
def coneInSpectral (μ : Fin 4) : Set (EnergyMomentum.SpectralSpace μ) :=
  {x | x.1 ∈ siteCone μ}
def spectralPointOf (μ : Fin 4) (E : ℝ≥0∞) (η : EnergyMomentum.DualTorus μ) :
    EnergyMomentum.SpectralSpace μ :=
  ⟨(E, EnergyMomentum.boxRep μ η), EnergyMomentum.boxRep_mem μ η⟩
def IsBoundedBorelFn {μ : Fin 4} (φ : EnergyMomentum.SpectralSpace μ → ℂ) : Prop :=
  Measurable φ ∧ ∃ C : ℝ, ∀ x, ‖φ x‖ ≤ C
namespace ReflectionPair
variable (p : ReflectionPair) (ν : unitPositiveClass) (μ : Fin 4)
def spectralMeasure (ψ : p.Hilb ν μ) : Measure (EnergyMomentum.SpectralSpace μ) :=
  open Classical in
  if h : ∃ σ, p.IsSpectralMeasure ν μ ψ σ then h.choose else 0
instance isFiniteMeasure_spectralMeasure (ψ : p.Hilb ν μ) :
    IsFiniteMeasure (p.spectralMeasure ν μ ψ) := by
  unfold spectralMeasure
  split_ifs with h
  · exact h.choose_spec.1
  · infer_instance
def spectralIntegral (ψ ψ' : p.Hilb ν μ) (φ : EnergyMomentum.SpectralSpace μ → ℂ) : ℂ :=
  polarIntegral (p.spectralMeasure ν μ) ψ ψ' φ
end ReflectionPair
namespace SpectralMeasures
def SpectralSpaceProps (μ : Fin 4) : Prop :=
  CompactSpace (EnergyMomentum.SpectralSpace μ) ∧
    TopologicalSpace.MetrizableSpace (EnergyMomentum.SpectralSpace μ) ∧
    BorelSpace (EnergyMomentum.SpectralSpace μ) ∧
    (∀ f : EnergyMomentum.SpectralSpace μ → ℂ,
      Continuous f ↔ Continuous (f ∘ (EnergyMomentum.chart μ).symm)) ∧
    (∀ S : Set (EnergyMomentum.SpectralSpace μ),
      MeasurableSet S ↔ MeasurableSet (EnergyMomentum.chart μ '' S)) ∧
    (∀ (n : ℕ) (w : EnergyMomentum.orthLattice μ), Continuous (energyMomentumMonomial μ n w)) ∧
    IsClosed (coneInSpectral μ) ∧
    (∀ f : EnergyMomentum.SpectralSpace μ → ℂ, Continuous f → ∀ E : ℝ≥0∞,
      Continuous fun η : EnergyMomentum.DualTorus μ => f (spectralPointOf μ E η)) ∧
    Measurable (fun x : EnergyMomentum.SpectralSpace μ => ((expNegEnergy x.energy : unitInterval) : ℝ)) ∧
    Measurable (fun x : EnergyMomentum.SpectralSpace μ => x.energy) ∧
    (∀ l : TransverseAxis μ, Measurable fun x : EnergyMomentum.SpectralSpace μ =>
      Complex.exp (Complex.I * (x.momentum l : ℂ))) ∧
    (∀ l : TransverseAxis μ, Measurable fun x : EnergyMomentum.SpectralSpace μ => x.momentum l) ∧
    Measurable (fun x : EnergyMomentum.SpectralSpace μ => EnergyMomentum.torusProj μ x.momentum)
def MonomialDensity (μ : Fin 4) : Prop :=
  (∀ f : EnergyMomentum.SpectralSpace μ → ℂ, Continuous f →
    ∃ q : ℕ → EnergyMomentum.SpectralSpace μ → ℂ, (∀ k, q k ∈ energyMomentumPolys μ) ∧
      TendstoUniformly q f atTop) ∧
  ∀ (m : ℕ) (σ : Fin m → Measure (EnergyMomentum.SpectralSpace μ)) (a : Fin m → ℂ),
    (∀ i, IsFiniteMeasure (σ i)) →
    (∀ (n : ℕ) (w : EnergyMomentum.orthLattice μ),
      ∑ i, a i * ∫ x, energyMomentumMonomial μ n w x ∂σ i = 0) →
    ∀ φ : EnergyMomentum.SpectralSpace μ → ℂ, IsBoundedBorelFn φ →
      ∑ i, a i * ∫ x, φ x ∂σ i = 0
variable (p : ReflectionPair) (ν : unitPositiveClass) (μ : Fin 4)
def PolarizationIdentity : Prop :=
  ∀ b : SesqForm (p.Hilb ν μ), b.IsSesquilinear →
    (∀ ψ ψ' : p.Hilb ν μ, b ψ ψ' =
      (1 / 4) * ∑ k ∈ Finset.range 4, Complex.I ^ k *
        b (ψ' + Complex.I ^ k • ψ) (ψ' + Complex.I ^ k • ψ)) ∧
    ((∀ χ : p.Hilb ν μ, (b χ χ).im = 0) → b.IsConjSymm)
def UniqueSpectralMeasure : Prop :=
  ∀ ψ : p.Hilb ν μ,
    (∃! σ, p.IsSpectralMeasure ν μ ψ σ) ∧
    p.IsSpectralMeasure ν μ ψ (p.spectralMeasure ν μ ψ) ∧
    p.spectralMeasure ν μ ψ univ = ENNReal.ofReal (‖ψ‖ ^ 2) ∧
    ∀ a : ℂ, p.spectralMeasure ν μ (a • ψ) =
      ENNReal.ofReal (‖a‖ ^ 2) • p.spectralMeasure ν μ ψ
def IntegralLinear : Prop :=
  (∀ (ψ ψ' : p.Hilb ν μ) (φ₁ φ₂ : EnergyMomentum.SpectralSpace μ → ℂ),
    IsBoundedBorelFn φ₁ → IsBoundedBorelFn φ₂ →
      p.spectralIntegral ν μ ψ ψ' (φ₁ + φ₂) =
        p.spectralIntegral ν μ ψ ψ' φ₁ + p.spectralIntegral ν μ ψ ψ' φ₂) ∧
  (∀ (ψ ψ' : p.Hilb ν μ) (a : ℂ) (φ : EnergyMomentum.SpectralSpace μ → ℂ),
    IsBoundedBorelFn φ →
      p.spectralIntegral ν μ ψ ψ' (a • φ) = a * p.spectralIntegral ν μ ψ ψ' φ) ∧
  ∀ φ : EnergyMomentum.SpectralSpace μ → ℂ, IsBoundedBorelFn φ →
    SesqForm.IsSesquilinear fun ψ ψ' : p.Hilb ν μ => p.spectralIntegral ν μ ψ ψ' φ
def IntegralDiag : Prop :=
  ∀ (ψ : p.Hilb ν μ) (φ : EnergyMomentum.SpectralSpace μ → ℂ), IsBoundedBorelFn φ →
    p.spectralIntegral ν μ ψ ψ φ = ∫ x, φ x ∂p.spectralMeasure ν μ ψ
def IntegralBound : Prop :=
  ∀ (ψ ψ' : p.Hilb ν μ) (φ : EnergyMomentum.SpectralSpace μ → ℂ), IsBoundedBorelFn φ →
    ∀ C : Set (EnergyMomentum.SpectralSpace μ), MeasurableSet C →
      (∀ χ : p.Hilb ν μ, p.spectralMeasure ν μ χ Cᶜ = 0) →
      ‖p.spectralIntegral ν μ ψ ψ' φ‖ ≤ sSup ((fun x => ‖φ x‖) '' C) * ‖ψ‖ * ‖ψ'‖
def IntegralContinuity : Prop :=
  ∀ (ψ ψ' : p.Hilb ν μ) (φ : EnergyMomentum.SpectralSpace μ → ℂ)
    (f : ℕ → EnergyMomentum.SpectralSpace μ → ℂ),
    IsBoundedBorelFn φ → (∀ k, IsBoundedBorelFn (f k)) →
    TendstoUniformly f φ atTop →
    Tendsto (fun k => p.spectralIntegral ν μ ψ ψ' (f k)) atTop
      (𝓝 (p.spectralIntegral ν μ ψ ψ' φ))
def SupportOnCone : Prop :=
  ∀ ψ : p.Hilb ν μ, p.spectralMeasure ν μ ψ (coneInSpectral μ)ᶜ = 0
def MomentIdentity : Prop :=
  ∀ (ψ ψ' : p.Hilb ν μ) (n : ℕ) (w : EnergyMomentum.orthLattice μ),
    inner ℂ ψ ((p.transferOp ν μ ^ n * p.shiftMonomial ν μ (w : Fin 4 → ℤ)) ψ') =
      p.spectralIntegral ν μ ψ ψ' (energyMomentumMonomial μ n w)
def TranslationInvariance : Prop :=
  ∀ (ψ : p.Hilb ν μ) (w : EnergyMomentum.orthLattice μ),
    p.spectralMeasure ν μ (p.shiftMonomial ν μ (w : Fin 4 → ℤ) ψ) =
      p.spectralMeasure ν μ ψ
end SpectralMeasures
open SpectralMeasures in
def SpectralMeasuresTheorem : Prop :=
  ∀ μ : Fin 4, SpectralSpaceProps μ ∧ MonomialDensity μ ∧
    ∀ (ν : unitPositiveClass) (p : ReflectionPair),
      PolarizationIdentity p ν μ ∧ UniqueSpectralMeasure p ν μ ∧ IntegralLinear p ν μ ∧
        IntegralDiag p ν μ ∧ IntegralBound p ν μ ∧ IntegralContinuity p ν μ ∧
        SupportOnCone p ν μ ∧ MomentIdentity p ν μ ∧ TranslationInvariance p ν μ
end YangMills.Construction.ReflectionPositivity.DirectionPictures
