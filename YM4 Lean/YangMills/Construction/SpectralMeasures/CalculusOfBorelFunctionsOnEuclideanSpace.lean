import YangMills.Construction.EuclideanBorel.RepresentationSpectralMeasure
import YangMills.Construction.HilbertSpaces.FormsOperatorsAndFamiliesInAHilbertSpace
import YangMills.Construction.HilbertSpaces.OperatorsAndJointSpectrumOfAProjectionValuedMeasure
import Mathlib
set_option autoImplicit false
open MeasureTheory Set Filter Topology
open scoped ENNReal InnerProductSpace ComplexConjugate ComplexOrder
noncomputable section
namespace YangMills.Construction.EuclideanBorel
section Operators
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {n : ℕ}
def HasSpectralValue (E : BorelSubset n → H →L[ℂ] H) (f : Space n → ℂ) (x w : H) : Prop :=
  ∃ hx : x ∈ sqIntegrableDomain E f, spectralIntegral E f ⟨x, hx⟩ = w
def RealizesSpectralIntegral (E : BorelSubset n → H →L[ℂ] H) (f : Space n → ℂ)
    (T : SpectralTheory.UnboundedOp H) : Prop :=
  (T.domain : Set H) = sqIntegrableDomain E f ∧
    ∀ x : T.domain, HasSpectralValue E f x (T x)
def spectralOp (E : BorelSubset n → H →L[ℂ] H) (f : Space n → ℂ) :
    SpectralTheory.UnboundedOp H :=
  Classical.epsilon (RealizesSpectralIntegral E f)
def HoldsOffNull (E : BorelSubset n → H →L[ℂ] H) (P : Space n → Prop) : Prop :=
  ∃ N : BorelSubset n, IsNull E N ∧ ∀ y, y ∉ N.1 → P y
def EssBounded (E : BorelSubset n → H →L[ℂ] H) (f : Space n → ℂ) : Prop :=
  ∃ C : ℝ, HoldsOffNull E fun y => ‖f y‖ ≤ C
def sublevelSet {f : Space n → ℂ} (hf : Measurable f) (k : ℕ) : BorelSubset n :=
  ⟨{y | ‖f y‖ ≤ k}, measurableSet_le hf.norm measurable_const⟩
def disagreementSet {f g : Space n → ℂ} (hf : Measurable f) (hg : Measurable g) :
    BorelSubset n :=
  ⟨{y | f y ≠ g y}, (measurableSet_eq_fun hf hg).compl⟩
def zeroLocus {f : Space n → ℂ} (hf : Measurable f) : BorelSubset n :=
  ⟨{y | f y = 0}, measurableSet_eq_fun hf measurable_const⟩
structure DomainProperties (E : BorelSubset n → H →L[ℂ] H) {f : Space n → ℂ}
    (hf : Measurable f) : Prop where
  dense : FormsOperators.IsDenseSet (sqIntegrableDomain E f)
  isOp : RealizesSpectralIntegral E f (spectralOp E f)
  value_on_sublevel : ∀ (x : H) (k : ℕ), 1 ≤ k → ∃ w : H,
    HasSpectralValue E f (E (sublevelSet hf k) x) w ∧ HasSpectralValue E (cutoff f k) x w
def LinearityAndNorms (E : BorelSubset n → H →L[ℂ] H) (f g : Space n → ℂ) (c : ℂ) : Prop :=
  ∀ (x : H) (hxf : x ∈ sqIntegrableDomain E f) (hxg : x ∈ sqIntegrableDomain E g),
    HasSpectralValue E (fun y => f y + c * g y) x
      (spectralIntegral E f ⟨x, hxf⟩ + c • spectralIntegral E g ⟨x, hxg⟩) ∧
    ‖spectralIntegral E f ⟨x, hxf⟩ - spectralIntegral E g ⟨x, hxg⟩‖ ^ 2 =
      ∫ y, ‖f y - g y‖ ^ 2 ∂(diagonalMeasure E x) ∧
    ‖spectralIntegral E f ⟨x, hxf⟩‖ ^ 2 = ∫ y, ‖f y‖ ^ 2 ∂(diagonalMeasure E x) ∧
    ⟪x, spectralIntegral E f ⟨x, hxf⟩⟫_ℂ = ∫ y, f y ∂(diagonalMeasure E x)
def AdjointProperties (E : BorelSubset n → H →L[ℂ] H) (f : Space n → ℂ) : Prop :=
  (∃ hd : FormsOperators.IsDenselyDefined (spectralOp E f),
    FormsOperators.adj (spectralOp E f) hd = spectralOp E fun y => conj (f y)) ∧
  ((∀ y, (f y).im = 0) → FormsOperators.IsSelfAdj (spectralOp E f))
def Multiplicativity (E : BorelSubset n → H →L[ℂ] H) (f g : Space n → ℂ) : Prop :=
  ∀ (x : H) (hxg : x ∈ sqIntegrableDomain E g),
    (∀ Δ : BorelSubset n, diagonalMeasure E (spectralIntegral E g ⟨x, hxg⟩) Δ.1 =
      ∫⁻ y, Δ.1.indicator (fun y => ‖g y‖ₑ ^ 2) y ∂(diagonalMeasure E x)) ∧
    (spectralIntegral E g ⟨x, hxg⟩ ∈ sqIntegrableDomain E f ↔
      x ∈ sqIntegrableDomain E fun y => f y * g y) ∧
    ∀ hmem : spectralIntegral E g ⟨x, hxg⟩ ∈ sqIntegrableDomain E f,
      HasSpectralValue E (fun y => f y * g y) x (spectralIntegral E f ⟨_, hmem⟩)
structure EssentialProperties (E : BorelSubset n → H →L[ℂ] H) {f g : Space n → ℂ}
    (hf : Measurable f) (hg : Measurable g) : Prop where
  eq_of_null : IsNull E (disagreementSet hf hg) → spectralOp E f = spectralOp E g
  bounded : ∀ c : ℝ, 0 ≤ c → (HoldsOffNull E fun y => ‖f y‖ ≤ c) →
    ∃ B : H →L[ℂ] H, SpectralIntegralIs E f B ∧ ∀ x, ‖B x‖ ≤ c * ‖x‖
  mul : EssBounded E f → EssBounded E g →
    ∃ B B' : H →L[ℂ] H, SpectralIntegralIs E f B ∧ SpectralIntegralIs E g B' ∧
      SpectralIntegralIs E (fun y => f y * g y) (B * B' : H →L[ℂ] H) ∧
      SpectralIntegralIs E (fun y => f y * g y) (B' * B : H →L[ℂ] H)
  nonneg : (HoldsOffNull E fun y => 0 ≤ f y) →
    ∀ x : sqIntegrableDomain E f, 0 ≤ ⟪(x : H), spectralIntegral E f x⟫_ℂ
  unitary : (HoldsOffNull E fun y => ‖f y‖ = 1) →
    ∃ U : H ≃ₗᵢ[ℂ] H, SpectralIntegralIs E f U ∧
      SpectralIntegralIs E (fun y => conj (f y)) U.symm
def KernelIsZeroLocusRange (E : BorelSubset n → H →L[ℂ] H) {f : Space n → ℂ}
    (hf : Measurable f) : Prop :=
  FormsOperators.ker (spectralOp E f) = range (E (zeroLocus hf))
def BoundedConvergence (E : BorelSubset n → H →L[ℂ] H) (f : Space n → ℂ) : Prop :=
  ∀ (fs : ℕ → Space n → ℂ) (c : ℝ), (∀ j, Measurable (fs j)) → 0 ≤ c →
    (HoldsOffNull E fun y => (∀ j, ‖fs j y‖ ≤ c) ∧
      Tendsto (fun j => fs j y) atTop (𝓝 (f y))) →
    ∀ x : H, ∃ (hx : x ∈ sqIntegrableDomain E f)
      (hxs : ∀ j, x ∈ sqIntegrableDomain E (fs j)),
      Tendsto (fun j => spectralIntegral E (fs j) ⟨x, hxs j⟩) atTop
        (𝓝 (spectralIntegral E f ⟨x, hx⟩))
def PushforwardProperty (E : BorelSubset n → H →L[ℂ] H) (m : ℕ) : Prop :=
  ∀ (φ : Space n → Space m) (hφ : Measurable φ),
    IsPVM (pushforward E φ hφ) ∧
    ∀ u : Space m → ℂ, Measurable u →
      spectralOp (pushforward E φ hφ) u = spectralOp E (u ∘ φ)
def UnitaryConjProperty (E : BorelSubset n → H →L[ℂ] H) (f : Space n → ℂ) : Prop :=
  ∀ U : H ≃ₗᵢ[ℂ] H, IsPVM (unitaryConj U E) ∧
    spectralOp (unitaryConj U E) f = FormsOperators.unitaryConjugate U (spectralOp E f)
def CommutantProperty (E : BorelSubset n → H →L[ℂ] H) (f : Space n → ℂ) : Prop :=
  ∀ B : H →L[ℂ] H, (∀ Δ, FormsOperators.Commutes B (E Δ)) →
    EssBounded E f → ∃ B' : H →L[ℂ] H, SpectralIntegralIs E f B' ∧
      FormsOperators.Commutes B B'
def ofCoordBorel (Δ : SpectralTheory.BorelSubset n) : BorelSubset n :=
  ⟨WithLp.ofLp ⁻¹' Δ.1, (PiLp.continuous_ofLp 2 _).measurable Δ.2⟩
def realPartOnCoords (g : Space n → ℂ) (y : Fin n → ℝ) : ℝ :=
  (g (WithLp.toLp 2 y)).re
theorem measurable_realPartOnCoords {g : Space n → ℂ} (hg : Measurable g) :
    Measurable (realPartOnCoords g) :=
  Complex.measurable_re.comp (hg.comp (PiLp.continuous_toLp 2 _).measurable)
def AgreesWith [NeZero n] (F : SpectralTheory.SpectralMeasure n H)
    (E : BorelSubset n → H →L[ℂ] H) : Prop :=
  ∀ Δ : SpectralTheory.BorelSubset n, F Δ = (E (ofCoordBorel Δ) : H →ₗ[ℂ] H)
def CoordinateCompatibility [NeZero n] (E : BorelSubset n → H →L[ℂ] H) {g : Space n → ℂ}
    (hg : Measurable g) : Prop :=
  (∃ U, IsMaximalOpenNull E U) ∧
  ∃ F : SpectralTheory.SpectralMeasure n H, AgreesWith F E ∧
    (∀ Δ : SpectralTheory.BorelSubset n, IsNull E (ofCoordBorel Δ) ↔ F.IsNull Δ) ∧
    ((∀ y, (g y).im = 0) → spectralOp E g =
      F.realIntegralOp (realPartOnCoords g) (measurable_realPartOnCoords hg))
end Operators
namespace FunctionalCalculus
def Statement : Prop :=
  ∀ (n m : ℕ) [NeZero n] [NeZero m]
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (E : BorelSubset n → H →L[ℂ] H), IsPVM E →
    ∀ (f g : Space n → ℂ) (hf : Measurable f) (hg : Measurable g) (c : ℂ),
      DomainProperties E hf ∧ LinearityAndNorms E f g c ∧ AdjointProperties E f ∧
      Multiplicativity E f g ∧ EssentialProperties E hf hg ∧ KernelIsZeroLocusRange E hf ∧
      BoundedConvergence E f ∧ PushforwardProperty E m ∧ UnitaryConjProperty E f ∧
      CommutantProperty E f ∧ CoordinateCompatibility E hg
end FunctionalCalculus
end YangMills.Construction.EuclideanBorel
