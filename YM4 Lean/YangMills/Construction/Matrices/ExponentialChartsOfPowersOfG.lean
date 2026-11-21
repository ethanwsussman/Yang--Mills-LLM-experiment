import YangMills.Construction.Lattice.GaugeFieldSpacesAndRealAnalyticMaps
import YangMills.Construction.Matrices.SpecialUnitaryPowerCharts
import YangMills.Construction.OneLoop.Conventions
import Mathlib
set_option autoImplicit false
open Set YangMills.Construction.Matrices.GroupLieProduct
open scoped ContDiff Matrix.Norms.L2Operator Topology
noncomputable section
namespace YangMills.Construction.Matrices.PowerExpCharts
def pauliFamily : Fin 3 → ComplexMatrix2 :=
  ![OneLoop.pauliX, OneLoop.pauliY, OneLoop.pauliZ]
theorem pauliFamily_mem_hermitianTraceless (k : Fin 3) :
    pauliFamily k ∈ ComplexMatrix2.hermitianTraceless := by
  refine ⟨?_, ?_⟩
  · ext i j
    fin_cases k <;> fin_cases i <;> fin_cases j <;>
      simp [pauliFamily, OneLoop.pauliX, OneLoop.pauliY,
        OneLoop.pauliZ, Matrix.conjTranspose_apply]
  · fin_cases k <;>
      simp [pauliFamily, OneLoop.pauliX, OneLoop.pauliY,
        OneLoop.pauliZ, ComplexMatrix2.fullTrace, Matrix.trace_fin_two]
def pauliLie (k : Fin 3) : ComplexMatrix2.LieElement :=
  (⟨pauliFamily k, pauliFamily_mem_hermitianTraceless k⟩ : ComplexMatrix2.hermitianTraceless)
variable {σ τ : Type}
def ofCoeffs [Fintype σ] (y : σ → Fin 3 → ℝ) : σ → ComplexMatrix2.LieElement :=
  fun s => ∑ k, y s k • pauliLie k
def coeffDirection (s : σ) (k : Fin 3) : σ → ComplexMatrix2.LieElement :=
  open Classical in Pi.single s (pauliLie k)
def mulI (Y : σ → ComplexMatrix2.LieElement) : σ → ComplexMatrix2 :=
  fun s => Complex.I • (Y s).toMatrix
def expChart (p₀ A : σ → ComplexMatrix2) : σ → ComplexMatrix2 :=
  fun s => expChartAt (asGroupFactors p₀) (asGroupFactors A) (.inl s)
def expChartI (p₀ : σ → ComplexMatrix2) (Y : σ → ComplexMatrix2.LieElement) :
    σ → ComplexMatrix2 :=
  expChart p₀ (mulI Y)
def smallBall (σ : Type) (ε : ℝ) : Set (σ → ComplexMatrix2.LieElement) :=
  {Y | ∀ s, ComplexMatrix2.operatorNorm (Y s).toMatrix < ε}
def logChart (p₀ X : σ → ComplexMatrix2) : σ → ComplexMatrix2 :=
  fun s => (1 / Complex.I) • ComplexMatrix2.logSeries (X s * (p₀ s)⁻¹)
def logDomain (p₀ : σ → ComplexMatrix2) : Set (σ → ComplexMatrix2) :=
  {X | ∀ s, ComplexMatrix2.operatorNorm (X s * (p₀ s)⁻¹ - 1) < 1}
def IsCoeffChart [Fintype σ] (c : EmbeddedSubmanifold.Chart (specialUnitaryPower σ))
    (e : σ × Fin 3 ≃ Fin c.dim) (p₀ : σ → ComplexMatrix2)
    (B : Set (σ → ComplexMatrix2.LieElement)) : Prop :=
  c.source = {u | ofCoeffs (fun s k => u (e (s, k))) ∈ B} ∧
    ∀ u ∈ c.source,
      c.param u = expChartI p₀ (ofCoeffs fun s k => u (e (s, k)))
def PowerCharts (σ : Type) [Fintype σ] : Prop :=
  ∀ p₀ ∈ specialUnitaryPower σ,
    p₀ ∈ unimodularPi σ ∧
    (∀ Y : σ → ComplexMatrix2.LieElement, mulI Y ∈ tracelessPi σ ∧
      expChartI p₀ Y = (fun s => ComplexMatrix2.matExp (Complex.I • (Y s).toMatrix) * p₀ s) ∧
      expChartI p₀ Y ∈ specialUnitaryPower σ) ∧
    ∀ ε : ℝ, 0 < ε → Real.exp ε ≤ 19 / 10 →
      InjOn (expChartI p₀) (smallBall σ ε) ∧
      specialUnitaryPower.IsOpenSubset (expChartI p₀ '' smallBall σ ε) ∧
      p₀ ∈ expChartI p₀ '' smallBall σ ε ∧
      ContDiffOn ℝ ∞ (expChartI p₀) (smallBall σ ε) ∧
      IsOpen (logDomain p₀) ∧
      ContDiffOn ℝ ∞ (logChart p₀) (logDomain p₀) ∧
      expChartI p₀ '' smallBall σ ε ⊆ logDomain p₀ ∧
      (∀ Y ∈ smallBall σ ε, logChart p₀ (expChartI p₀ Y) = fun s => (Y s).toMatrix) ∧
      ∃ (c : EmbeddedSubmanifold.Chart (specialUnitaryPower σ)) (e : σ × Fin 3 ≃ Fin c.dim),
        IsCoeffChart c e p₀ (smallBall σ ε)
def ChartMapsInto (O : Set (σ → ComplexMatrix2)) (p₀ : σ → ComplexMatrix2)
    (N : Set (σ → ComplexMatrix2.LieElement)) : Prop :=
  MapsTo (expChartI p₀) N O
def tangentVectorAt (p₀ : σ → ComplexMatrix2) (Y : σ → ComplexMatrix2.LieElement) :
    σ → ComplexMatrix2 :=
  fun s => mulI Y s * p₀ s
def ReadInCharts (σ F : Type) [Fintype σ] [NormedAddCommGroup F] [NormedSpace ℝ F] : Prop :=
  ∀ (O : Set (σ → ComplexMatrix2)) (f : (σ → ComplexMatrix2) → F),
    specialUnitaryPower.IsOpenSubset O →
    (∀ p₀ ∈ O, ∃ N ∈ 𝓝 (0 : σ → ComplexMatrix2.LieElement), ChartMapsInto O p₀ N) ∧
    (EmbeddedSubmanifold.DifferentiableOnOpen (specialUnitaryPower σ) O f ↔
      ∀ p₀ ∈ O, ∃ N ∈ 𝓝 (0 : σ → ComplexMatrix2.LieElement), ChartMapsInto O p₀ N ∧
        DifferentiableOn ℝ (f ∘ expChartI p₀) N) ∧
    (EmbeddedSubmanifold.DifferentiableOnOpen (specialUnitaryPower σ) O f →
      ∀ p₀ ∈ O, ∀ Y : σ → ComplexMatrix2.LieElement,
        HasDerivAt (fun t : ℝ => expChartI p₀ (t • Y)) (tangentVectorAt p₀ Y) 0 ∧
        ∃ h : tangentVectorAt p₀ Y ∈ EmbeddedSubmanifold.tangentSpace (specialUnitaryPower σ) p₀,
          HasDerivAt (fun t : ℝ => f (expChartI p₀ (t • Y)))
            (EmbeddedSubmanifold.tangentDifferential (specialUnitaryPower σ) f p₀
              ⟨tangentVectorAt p₀ Y, h⟩) 0) ∧
    ((∀ c : EmbeddedSubmanifold.Chart (specialUnitaryPower σ),
        ContDiffOn ℝ ∞ (c.pullback f) (c.coords O)) ↔
      ∀ p₀ ∈ O, ∃ N ∈ 𝓝 (0 : σ → ComplexMatrix2.LieElement), ChartMapsInto O p₀ N ∧
        ContDiffOn ℝ ∞ (f ∘ expChartI p₀) N)
def DifferentialReadInCharts (σ F : Type) [Fintype σ] [NormedAddCommGroup F]
    [NormedSpace ℝ F] : Prop :=
  ∀ (O : Set (σ → ComplexMatrix2)) (f : (σ → ComplexMatrix2) → F),
    specialUnitaryPower.IsOpenSubset O →
    EmbeddedSubmanifold.DifferentiableOnOpen (specialUnitaryPower σ) O f →
    (EmbeddedSubmanifold.HasDifferentiablePartialsOn (specialUnitaryPower σ) O f ↔
      ∀ p₀ ∈ O, ∃ N ∈ 𝓝 (0 : σ → ComplexMatrix2.LieElement), ChartMapsInto O p₀ N ∧
        ∀ (s : σ) (k : Fin 3), DifferentiableOn ℝ
          (fun Y => fderiv ℝ (f ∘ expChartI p₀) Y (coeffDirection s k)) N)
def PowerMapsReadComponentwise (σ τ : Type) [Fintype σ] [Fintype τ] : Prop :=
  ∀ (O : Set (σ → ComplexMatrix2)) (g : (σ → ComplexMatrix2) → τ → ComplexMatrix2),
    specialUnitaryPower.IsOpenSubset O →
    MapsTo g O (specialUnitaryPower τ) →
    (specialUnitaryPower.IsDifferentiableInto O g ↔
      ∀ t : τ, EmbeddedSubmanifold.DifferentiableOnOpen (specialUnitaryPower σ) O fun p => g p t)
def IsLocallyHolomorphicRestriction {F T : Type}
    (holo : Set (σ ⊕ Empty → ComplexMatrix2) → ((σ ⊕ Empty → ComplexMatrix2) → T) → Prop)
    (val : F → T) (O : Set (σ → ComplexMatrix2)) (f : (σ → ComplexMatrix2) → F) : Prop :=
  ∀ p ∈ O, ∃ (W : Set (σ ⊕ Empty → ComplexMatrix2)) (Φ : (σ ⊕ Empty → ComplexMatrix2) → T),
    asGroupFactors p ∈ W ∧ holo W Φ ∧
      ∀ x ∈ O, asGroupFactors x ∈ W → Φ (asGroupFactors x) = val (f x)
def HasChartPowerSeries {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [Fintype σ]
    (O : Set (σ → ComplexMatrix2)) (f : (σ → ComplexMatrix2) → F) : Prop :=
  (∀ p₀ ∈ O, ∃ N ∈ 𝓝 (0 : σ → ComplexMatrix2.LieElement), ChartMapsInto O p₀ N ∧
    ContDiffOn ℝ ∞ (f ∘ expChartI p₀) N ∧
    ∃ c : (σ → Fin 3 → ℕ) → F, ∀ y : σ → Fin 3 → ℝ, ofCoeffs y ∈ N →
      HasSum (fun m : σ → Fin 3 → ℕ => (∏ s, ∏ k, y s k ^ m s k) • c m)
        (f (expChartI p₀ (ofCoeffs y)))) ∧
  ∀ c : EmbeddedSubmanifold.Chart (specialUnitaryPower σ),
    ContDiffOn ℝ ∞ (c.pullback f) (c.coords O)
def HolomorphicScalar [Fintype σ] (b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless)
    (W : Set (σ ⊕ Empty → ComplexMatrix2)) (Φ : (σ ⊕ Empty → ComplexMatrix2) → ℂ) : Prop :=
  IsHolomorphicToCoords b (Equiv.funUnique (Fin 1) ℂ).symm W Φ
def HolomorphicMatrix [Fintype σ] (b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless)
    (W : Set (σ ⊕ Empty → ComplexMatrix2)) (Φ : (σ ⊕ Empty → ComplexMatrix2) → ComplexMatrix2) :
    Prop :=
  IsHolomorphicToCoords b Coordinates.ComplexCoordinates.matrixEquiv W Φ
def RealAnalyticReadInCharts (σ τ : Type) [Fintype σ] [Fintype τ]
    (b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless) : Prop :=
  ∀ O : Set (σ → ComplexMatrix2), specialUnitaryPower.IsOpenSubset O →
    (∀ f : (σ → ComplexMatrix2) → ℝ,
      IsLocallyHolomorphicRestriction (HolomorphicScalar b) Complex.ofReal O f →
      HasChartPowerSeries O f ∧
        EmbeddedSubmanifold.DifferentiableOnOpen (specialUnitaryPower σ) O f ∧
        EmbeddedSubmanifold.HasDifferentiablePartialsOn (specialUnitaryPower σ) O f) ∧
    (∀ f : (σ → ComplexMatrix2) → ℂ,
      IsLocallyHolomorphicRestriction (HolomorphicScalar b) id O f →
      HasChartPowerSeries O f ∧
        EmbeddedSubmanifold.DifferentiableOnOpen (specialUnitaryPower σ) O f ∧
        EmbeddedSubmanifold.HasDifferentiablePartialsOn (specialUnitaryPower σ) O f) ∧
    (∀ f : (σ → ComplexMatrix2) → ComplexMatrix2,
      IsLocallyHolomorphicRestriction (HolomorphicMatrix b) id O f →
      HasChartPowerSeries O f ∧
        EmbeddedSubmanifold.DifferentiableOnOpen (specialUnitaryPower σ) O f) ∧
    ∀ f : (σ → ComplexMatrix2) → τ → ComplexMatrix2, MapsTo f O (specialUnitaryPower τ) →
      IsLocallyHolomorphicRestriction (IsHolomorphicToProduct b) asGroupFactors O f →
      HasChartPowerSeries O f ∧ specialUnitaryPower.IsDifferentiableInto O f
def RestrictionsRealAnalytic (σ : Type) [Fintype σ]
    (b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless) : Prop :=
  ∀ W : Set (σ ⊕ Empty → ComplexMatrix2),
    ComplexMatrix2.IsRelativelyOpen (GroupLieProduct σ Empty) W →
    specialUnitaryPower.IsOpenSubset (asGroupFactors ⁻¹' W ∩ specialUnitaryPower σ) ∧
    (∀ Φ : (σ ⊕ Empty → ComplexMatrix2) → ℂ, HolomorphicScalar b W Φ →
      IsLocallyHolomorphicRestriction (HolomorphicScalar b) id
        (asGroupFactors ⁻¹' W ∩ specialUnitaryPower σ) (Φ ∘ asGroupFactors)) ∧
    ∀ Φ : (σ ⊕ Empty → ComplexMatrix2) → ComplexMatrix2, HolomorphicMatrix b W Φ →
      IsLocallyHolomorphicRestriction (HolomorphicMatrix b) id
        (asGroupFactors ⁻¹' W ∩ specialUnitaryPower σ) (Φ ∘ asGroupFactors)
def ExpChartsStatement : Prop :=
  ∀ (σ τ : Type) [Fintype σ] [Nonempty σ] [Fintype τ] [Nonempty τ],
    PowerCharts σ ∧
    ReadInCharts σ ℝ ∧ ReadInCharts σ ℂ ∧ ReadInCharts σ ComplexMatrix2 ∧
    DifferentialReadInCharts σ ℝ ∧ DifferentialReadInCharts σ ℂ ∧
    PowerMapsReadComponentwise σ τ ∧
    ∀ b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless,
      RealAnalyticReadInCharts σ τ b ∧ RestrictionsRealAnalytic σ b
end YangMills.Construction.Matrices.PowerExpCharts
