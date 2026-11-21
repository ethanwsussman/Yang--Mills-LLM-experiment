import YangMills.Construction.Towers.TheFunctionalInTheBackgroundGauge
import YangMills.Construction.Towers.TheHolomorphicActionOfATower
import Mathlib
set_option autoImplicit false
open Filter Set
open scoped Topology ContDiff
noncomputable section
namespace YangMills.Construction.Tower
variable {L m k : ℕ}
abbrev FieldTriple (L m k : ℕ) : Type :=
  edgeFormSpace L m k 0 × edgeFormSpace L m k 0 × edgeFormSpace L m k k
abbrev FieldTripleIndex (L m k : ℕ) : Type :=
  (Fin 3 × PositiveEdge L m k 0) ⊕ (Fin 3 × PositiveEdge L m k 0) ⊕ (Fin 3 × PositiveEdge L m k k)
def fieldTripleCoords (x : FieldTriple L m k) : FieldTripleIndex L m k → ℝ :=
  Sum.elim (fun ι => (toPauliCoeffs (restrictToPositiveEdges (x.1 : Edge L m k 0 → Matrices.ComplexMatrix2)) ι).re)
    (Sum.elim (fun ι => (toPauliCoeffs (restrictToPositiveEdges (x.2.1 : Edge L m k 0 → Matrices.ComplexMatrix2)) ι).re)
      fun ι => (toPauliCoeffs (restrictToPositiveEdges (x.2.2 : Edge L m k k → Matrices.ComplexMatrix2)) ι).re)
def ExpChartFunctionalDefined (x : FieldTriple L m k) : Prop :=
  BackgroundFunctionalWellDefined
    (PeriodicLattice.expGaugeField (x.1 : Edge L m k 0 → Matrices.ComplexMatrix2)) x.2.1 x.2.2
def expChartFunctional (x : FieldTriple L m k) : ℝ :=
  backgroundFunctional (PeriodicLattice.expGaugeField (x.1 : Edge L m k 0 → Matrices.ComplexMatrix2)) x.2.1 x.2.2
def expChartFunctionalInCoords (L m k : ℕ) : (FieldTripleIndex L m k → ℝ) → ℝ :=
  fun y => expChartFunctional
    (Function.invFun (fieldTripleCoords (L := L) (m := m) (k := k)) y)
def coordImage {N : ℕ} (e : FieldTripleIndex L m k ≃ Fin N) (W : Set (FieldTriple L m k)) :
    Set (Coordinates.ComplexCoordinates N) :=
  (fun x i => (fieldTripleCoords x (e.symm i) : ℂ)) '' W
def expChartFunctionalComplex {N : ℕ} (e : FieldTripleIndex L m k ≃ Fin N) :
    Coordinates.ComplexCoordinates N → Coordinates.ComplexCoordinates 1 :=
  fun z _ => (expChartFunctionalInCoords L m k fun ι => (z (e ι)).re : ℂ)
section Derivatives
variable [Fintype (PositiveEdge L m k 0)] [Fintype (PositiveEdge L m k k)]
def IsExpChartNhd (W : Set (FieldTriple L m k)) : Prop :=
  IsOpen W ∧ (0 : FieldTriple L m k) ∈ W ∧ (∀ x ∈ W, ExpChartFunctionalDefined x) ∧
    (∀ (N : ℕ) (e : FieldTripleIndex L m k ≃ Fin N),
      Coordinates.ComplexCoordinates.IsRealAnalyticIn (coordImage e W)
        (expChartFunctionalComplex e)) ∧
    ContDiffOn ℝ ∞ (expChartFunctionalInCoords L m k) (fieldTripleCoords '' W)
def expChartFirstDeriv (x : FieldTriple L m k) : ℝ :=
  fderiv ℝ (expChartFunctionalInCoords L m k) 0 (fieldTripleCoords x)
def expChartSecondDeriv (x y : FieldTriple L m k) : ℝ :=
  fderiv ℝ (fderiv ℝ (expChartFunctionalInCoords L m k)) 0 (fieldTripleCoords x)
    (fieldTripleCoords y)
def IsCurveFromZero (γ : ℝ → FieldTriple L m k) (v : FieldTriple L m k) : Prop :=
  γ 0 = 0 ∧ HasDerivAt (fun t => fieldTripleCoords (γ t)) (fieldTripleCoords v) 0
structure ExpChartFunctionalExpansion (L m k : ℕ) [Fintype (PositiveEdge L m k 0)]
    [Fintype (PositiveEdge L m k k)] : Prop where
  exists_nhd : ∃ W : Set (FieldTriple L m k), IsExpChartNhd W
  symmetric : ∃ B : LinearMap.BilinForm ℝ (FieldTriple L m k),
    (∀ x y, B x y = expChartSecondDeriv x y) ∧ ∀ x y, B x y = B y x
  eventually_mem : ∀ W : Set (FieldTriple L m k), IsExpChartNhd W →
    ∀ (γ : ℝ → FieldTriple L m k) (v : FieldTriple L m k), IsCurveFromZero γ v →
      ∀ᶠ t in 𝓝 (0 : ℝ), γ t ∈ W
  isLittleO : ∀ (γ : ℝ → FieldTriple L m k) (v : FieldTriple L m k),
    IsCurveFromZero γ v →
      (fun t : ℝ => expChartFunctional (γ t) -
          (backgroundFunctional (trivialField L m k 0) 0 0 +
            expChartFirstDeriv (γ t) +
            t ^ 2 / 2 * expChartSecondDeriv v v)) =o[𝓝 0]
        fun t : ℝ => t ^ 2
end Derivatives
def ExpChartFunctionalClaim : Prop :=
  ∀ L m k : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < m → 1 ≤ k →
    Module.Finite ℝ (FieldTriple L m k) ∧
      ∀ [Fintype (PositiveEdge L m k 0)] [Fintype (PositiveEdge L m k k)],
        ExpChartFunctionalExpansion L m k
end YangMills.Construction.Tower
end
