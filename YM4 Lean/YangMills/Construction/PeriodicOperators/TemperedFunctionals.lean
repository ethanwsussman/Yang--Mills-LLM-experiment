import YangMills.Construction.Matrices.ExponentialChartsOfPowersOfG
import YangMills.Construction.Matrices.SpecialUnitaryScalarVectorParts
import YangMills.Construction.PeriodicOperators.PeriodicIndexSetsOperatorsAndSymbols
import YangMills.Construction.Towers.TheLeftChart
import Mathlib
set_option autoImplicit false
open Set Filter
open scoped Topology Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction
namespace PeriodicOperators.Tempered
open InfiniteLattice (AmbientSpace)
abbrev UnitEdge (L n : ℕ) : Type := Tower.Edge L n 0 0
abbrev PositiveUnitEdge (L n : ℕ) : Type := Tower.PositiveEdge L n 0 0
def identityField (L n : ℕ) : UnitEdge L n → Matrices.ComplexMatrix2 := fun _ => 1
def EventuallyForSides (L : ℕ) (P : ℕ → Prop) : Prop :=
  Tower.EventuallyIn (Tower.sideSet L) fun s =>
    ∀ n : ℕ, 0 < n → PeriodicLattice.torusSide L n = s → P n
section Member
variable {L n : ℕ}
def IsAnalyticNearIdentity (f : (UnitEdge L n → Matrices.ComplexMatrix2) → ℝ) : Prop :=
  ∃ (_ : Fintype (PositiveUnitEdge L n)) (O : Set (PositiveUnitEdge L n → Matrices.ComplexMatrix2)),
    Matrices.specialUnitaryPower.IsOpenSubset O ∧ (fun _ => (1 : Matrices.ComplexMatrix2)) ∈ O ∧
      ∀ β : Module.Basis (Fin 3) ℂ Matrices.ComplexMatrix2.traceless,
        Matrices.PowerExpCharts.IsLocallyHolomorphicRestriction
          (Matrices.PowerExpCharts.HolomorphicScalar β) Complex.ofReal O
          fun w => f (Tower.fieldOfPositiveValues (k := 0) (j := 0) w)
def IsLocallyGaugeInvariant (f : (UnitEdge L n → Matrices.ComplexMatrix2) → ℝ) : Prop :=
  ∃ W : Set (Tower.Vertex L n 0 0 → Matrices.ComplexMatrix2),
    Tower.EventuallyNearIdentity (Tower.gaugeGroupAt L n 0 0) (· ∈ W) ∧
    Tower.EventuallyNearIdentity (Tower.fieldSpace L n 0 0) fun U =>
      ∀ v ∈ Tower.gaugeGroupAt L n 0 0, v ∈ W → f (PeriodicLattice.gaugeTransform v U) = f U
def IsGlobalGaugeInvariant (f : (UnitEdge L n → Matrices.ComplexMatrix2) → ℝ) : Prop :=
  Tower.EventuallyNearIdentity (Tower.fieldSpace L n 0 0) fun U =>
    ∀ g ∈ PeriodicLattice.compactGaugeGroup,
      f (PeriodicLattice.gaugeTransform (fun _ : Tower.Vertex L n 0 0 => g) U) = f U
def IsSymmetryInvariant (f : (UnitEdge L n → Matrices.ComplexMatrix2) → ℝ) : Prop :=
  Tower.EventuallyNearIdentity (Tower.fieldSpace L n 0 0) fun U =>
    ∀ σ : PeriodicLattice.FourTorus L n → PeriodicLattice.FourTorus L n,
      Tower.IsDistancePreserving σ →
      Tower.MapsSublatticeOnto 0 0 σ → f (Tower.pushField (k := 0) (j := 0) σ U) = f U
structure IsAdmissibleMember (f : (UnitEdge L n → Matrices.ComplexMatrix2) → ℝ) : Prop where
  analytic : IsAnalyticNearIdentity f
  map_identity : f (identityField L n) = 0
  locallyGauge : IsLocallyGaugeInvariant f
  globalGauge : IsGlobalGaugeInvariant f
  symmetry : IsSymmetryInvariant f
end Member
abbrev FieldFamily (L : ℕ) : Type := ∀ n : ℕ, (UnitEdge L n → Matrices.ComplexMatrix2) → ℝ
def IsLatticeFunctional (L : ℕ) (F : FieldFamily L) : Prop :=
  EventuallyForSides L fun n => IsAdmissibleMember (F n)
section Hessian
variable {L : ℕ}
def realComponent {n : ℕ} (B : UnitEdge L n → Matrices.ComplexMatrix2) :
    UnitEdge L n → Matrices.ComplexMatrix2 :=
  fun b => (2⁻¹ : ℂ) • (B b + (B b).conjTranspose)
def imagComponent {n : ℕ} (B : UnitEdge L n → Matrices.ComplexMatrix2) :
    UnitEdge L n → Matrices.ComplexMatrix2 :=
  fun b => (2 * Complex.I)⁻¹ • (B b - (B b).conjTranspose)
def hessianAtIdentity (F : FieldFamily L) (n : ℕ) (B B' : UnitEdge L n → Matrices.ComplexMatrix2) :
    ℝ :=
  Tower.leftSecondDeriv (k := 0) (j := 0) (F n) (identityField L n) B B'
def complexHessian (F : FieldFamily L) (n : ℕ) (B B' : UnitEdge L n → Matrices.ComplexMatrix2) :
    ℂ :=
  let R := realComponent B
  let S := imagComponent B
  let R' := realComponent B'
  let S' := imagComponent B'
  ((hessianAtIdentity F n R R' - hessianAtIdentity F n S S' : ℝ) : ℂ) +
    Complex.I * ((hessianAtIdentity F n R S' + hessianAtIdentity F n S R' : ℝ) : ℂ)
def phase {n : ℕ} (p : AmbientSpace) (x : PeriodicLattice.FourTorus L n) : ℂ :=
  Classical.epsilon fun z => ∀ y : AmbientSpace,
    (fun μ => (y μ : AddCircle (PeriodicLattice.torusSide L n))) = x →
      Complex.exp (Complex.I * bilinDot (toComplexVec p) (toComplexVec y)) = z
def fourierModeForm (L n : ℕ) (a : Fin 3) (p : AmbientSpace) (μ : Fin 4) :
    UnitEdge L n → Matrices.ComplexMatrix2 :=
  open Classical in
  Tower.extendOddly (k := 0) (j := 0) fun b =>
    if b.target - b.source = PeriodicLattice.unitStep L n _ μ then
      phase p (b.source : PeriodicLattice.FourTorus L n) • Matrices.ComplexMatrix2.pauliFamily a
    else 0
end Hessian
abbrev SymbolArray : Type := Fin 4 → Fin 4 → (Fin 4 → ℂ) → ℂ
structure IsTemperedWitness (L : ℕ) (F : FieldFamily L) (δ : ℝ) (π : SymbolArray) (e : ℕ → ℝ) :
    Prop where
  delta_pos : 0 < δ
  analytic : ∃ O : Set (Fin 4 → ℂ), imStrip δ ⊆ O ∧ ∀ μ ν,
    Coordinates.ComplexCoordinates.IsHolomorphicIn (N := 4) (N' := 1) O (fun κ _ => π μ ν κ) ∧
      ∃ C : ℝ, ∀ κ ∈ O, ‖π μ ν κ‖ ≤ C
  err_nonneg : EventuallyForSides L fun n => 0 ≤ e n
  err_tendsto : Tendsto e atTop (𝓝 0)
  approx : EventuallyForSides L fun n => ∀ p ∈ dualLattice (2 * L ^ n),
    ∀ (a a' : Fin 3) (μ ν : Fin 4),
    ‖(((PeriodicLattice.torusSide L n)⁻¹ ^ 4 : ℝ) : ℂ) *
        complexHessian F n (fourierModeForm L n a p μ) (fourierModeForm L n a' (-p) ν) -
      (if a = a' then π μ ν (toComplexVec p) else 0)‖ ≤ e n
def IsTemperedFunctional (L : ℕ) (F : FieldFamily L) : Prop :=
  IsLatticeFunctional L F ∧ ∃ (δ : ℝ) (π : SymbolArray) (e : ℕ → ℝ), IsTemperedWitness L F δ π e
def symbolDomain (L : ℕ) (F : FieldFamily L) : Set (Fin 4 → ℂ) :=
  {κ | ∃ (δ : ℝ) (π : SymbolArray) (e : ℕ → ℝ), IsTemperedWitness L F δ π e ∧ κ ∈ imStrip δ}
def IsHessianSymbol (L : ℕ) (F : FieldFamily L) (P : SymbolArray) : Prop :=
  ∀ (δ : ℝ) (π : SymbolArray) (e : ℕ → ℝ), IsTemperedWitness L F δ π e →
    ∀ μ ν, EqOn (P μ ν) (π μ ν) (imStrip δ)
def hessianSymbol (L : ℕ) (F : FieldFamily L) : SymbolArray :=
  Classical.epsilon (IsHessianSymbol L F)
end PeriodicOperators.Tempered
end YangMills.Construction
end
