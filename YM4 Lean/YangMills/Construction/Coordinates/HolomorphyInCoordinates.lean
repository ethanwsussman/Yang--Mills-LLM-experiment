import YangMills.Construction.Lattice.GaugeConfigurations
import Mathlib
open Filter Set
open scoped Topology
noncomputable section
namespace YangMills.Construction.Coordinates
open YangMills.Construction.Matrices
abbrev ComplexCoordinates (N : ℕ) : Type := Fin N → ℂ
namespace ComplexCoordinates
def stdBasisVector {N : ℕ} (j : Fin N) : ComplexCoordinates N := Pi.single j 1
def realLocus (N : ℕ) : Set (ComplexCoordinates N) := {z | ∀ j, (z j).im = 0}
def IsHolomorphicIn {N N' : ℕ} (O : Set (ComplexCoordinates N))
    (f : ComplexCoordinates N → ComplexCoordinates N') : Prop :=
  IsOpen O ∧ ContinuousOn f O ∧
    ∀ a ∈ O, ∀ j : Fin N, ∀ᶠ ζ in 𝓝 (0 : ℂ),
      DifferentiableAt ℂ (fun ζ : ℂ => f (a + ζ • stdBasisVector j)) ζ
def IsRealAnalyticIn {N N' : ℕ} (D : Set (ComplexCoordinates N))
    (f : ComplexCoordinates N → ComplexCoordinates N') : Prop :=
  ComplexMatrix2.IsRelativelyOpen (realLocus N) D ∧
    ∀ a ∈ D, ∃ c : (Fin N → ℕ) → ComplexCoordinates N', ∀ᶠ z in 𝓝[realLocus N] a,
      HasSum (fun m : Fin N → ℕ => (∏ j, (z j - a j) ^ m j) • c m) (f z)
def entryIndex : Fin 2 × Fin 2 ≃ Fin 4 := finProdFinEquiv
def matrixEquiv : ComplexMatrix2 ≃ ComplexCoordinates 4 where
  toFun X k := X (entryIndex.symm k).1 (entryIndex.symm k).2
  invFun z := Matrix.of fun i j => z (entryIndex (i, j))
  left_inv X := by ext i j; simp
  right_inv z := by ext k; simp
inductive Component : Type
  | matrix
  | scalar
def Component.Carrier : Component → Type
  | .matrix => ComplexMatrix2
  | .scalar => ℂ
def Component.dim : Component → ℕ
  | .matrix => 4
  | .scalar => 1
def Component.equiv : (c : Component) → c.Carrier ≃ ComplexCoordinates c.dim
  | .matrix => matrixEquiv
  | .scalar => (Equiv.funUnique (Fin 1) ℂ).symm
abbrev ComponentProduct {n : ℕ} (s : Fin n → Component) : Type := ∀ i, (s i).Carrier
def productDim {n : ℕ} (s : Fin n → Component) : ℕ := ∑ i, (s i).dim
def productEquiv {n : ℕ} (s : Fin n → Component) :
    ComponentProduct s ≃ ComplexCoordinates (productDim s) :=
  (Equiv.piCongrRight fun i => (s i).equiv).trans <|
    (Equiv.piCurry fun (_ : Fin n) (_ : Fin (s _).dim) => ℂ).symm.trans <|
      Equiv.arrowCongr finSigmaFinEquiv (Equiv.refl ℂ)
def matrixPairComponents : Fin 2 → Component := fun _ => .matrix
def matrixPairEquiv :
    ComplexMatrix2 × ComplexMatrix2 ≃ ComplexCoordinates (productDim matrixPairComponents) :=
  (finTwoArrowEquiv ComplexMatrix2).symm.trans (productEquiv matrixPairComponents)
def IsHolomorphicVia {E E' : Type} {N N' : ℕ} (e : E ≃ ComplexCoordinates N)
    (e' : E' ≃ ComplexCoordinates N') (O : Set E) (f : E → E') : Prop :=
  IsHolomorphicIn (e '' O) (e' ∘ f ∘ e.symm)
def tracelessTuple {n : ℕ} (b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless)
    (w : ComplexCoordinates (n * 3)) (i : Fin n) : ComplexMatrix2 :=
  ∑ c : Fin 3, w (finProdFinEquiv (i, c)) • (b c : ComplexMatrix2)
def expChart {n : ℕ} (X A : Fin n → ComplexMatrix2) : Fin n → ComplexMatrix2 :=
  fun i => ComplexMatrix2.matExp (A i) * X i
def expChartQuotient {n : ℕ} (Φ : (Fin n → ComplexMatrix2) → ComplexMatrix2)
    (X A : Fin n → ComplexMatrix2) : ComplexMatrix2 :=
  Φ (expChart X A) * (Φ X)⁻¹
def IsHolomorphicOnSL2Power {n : ℕ} (b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless)
    (U : Set (Fin n → ComplexMatrix2)) (Φ : (Fin n → ComplexMatrix2) → ComplexMatrix2) : Prop :=
  1 ≤ n ∧
    ComplexMatrix2.IsRelativelyOpen
      (ComplexMatrix2.complexifiedProduct fun _ : Fin n => ComplexMatrix2.FactorKind.group) U ∧
    MapsTo Φ U ComplexMatrix2.unitDeterminant ∧ ContinuousOn Φ U ∧
    ∀ X ∈ U, ∃ W : Set (ComplexCoordinates (n * 3)), 0 ∈ W ∧
      (∀ w ∈ W, expChart X (tracelessTuple b w) ∈ U ∧
        expChartQuotient Φ X (tracelessTuple b w) ∈ ComplexMatrix2.logBall) ∧
      IsHolomorphicIn W fun w =>
        matrixEquiv (ComplexMatrix2.logSeries (expChartQuotient Φ X (tracelessTuple b w)))
end ComplexCoordinates
end YangMills.Construction.Coordinates

namespace YangMills.Construction.Matrices.GroupLieNumberProduct
variable {ι κ τ ι' κ' τ' E V V' : Type}
def basisEquiv [AddCommGroup V] [Module ℂ V] {l : ℕ} (c : Module.Basis (Fin l) ℂ V) :
    V ≃ Coordinates.ComplexCoordinates l :=
  c.equivFun.toEquiv
def IsHolomorphicBetweenModules [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [AddCommGroup V'] [Module ℂ V'] [FiniteDimensional ℂ V'] (O : Set V) (f : V → V') : Prop :=
  ∀ (l l' : ℕ) (c : Module.Basis (Fin l) ℂ V) (c' : Module.Basis (Fin l') ℂ V'),
    Coordinates.ComplexCoordinates.IsHolomorphicVia (basisEquiv c) (basisEquiv c') O f
end YangMills.Construction.Matrices.GroupLieNumberProduct

namespace YangMills.Construction.PeriodicLattice
open YangMills.Construction.Matrices
variable {L m : ℕ} {j : ℤ}
abbrev PositiveBondOf (ℬ : Set (Bond L m j)) : Type :=
  {b : Bond L m j // b ∈ ℬ ∧ b.IsPositivelyOriented}
def complexGaugeFields (ℬ : Set (Bond L m j)) : Set (Bond L m j → ComplexMatrix2) :=
  {U | IsGaugeField complexGaugeGroup ℬ U}
def complexGaugeFieldOfValues (ℬ : Set (Bond L m j)) (v : PositiveBondOf ℬ → complexGaugeGroup)
    (b : Bond L m j) : ComplexMatrix2 :=
  open Classical in
  if h : b ∈ ℬ ∧ b.IsPositivelyOriented then (v ⟨b, h⟩ : ComplexMatrix2)
  else if h' : b.opposite ∈ ℬ ∧ b.opposite.IsPositivelyOriented then
    ((v ⟨b.opposite, h'⟩ : ComplexMatrix2))⁻¹
  else 1
def gaugeFieldAtLevelValues {K k : ℕ} (U : gaugeFieldsAtLevel L m K k) :
    PositivelyOrientedBond L m (levelDepth K k) → ComplexMatrix2.specialUnitary :=
  fun b => ⟨U.1 b.1, (show IsGaugeField compactGaugeGroup univ U.1 from U.2).1 b.1 (mem_univ _)⟩
def gaugeFieldsAtLevelTopology (L m K k : ℕ) : TopologicalSpace (gaugeFieldsAtLevel L m K k) :=
  TopologicalSpace.induced gaugeFieldAtLevelValues inferInstance
end YangMills.Construction.PeriodicLattice
