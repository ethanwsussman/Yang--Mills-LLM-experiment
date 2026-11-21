import YangMills.Construction.Matrices.ExponentialChartsOfPowersOfG
import YangMills.Construction.Matrices.RealAnalyticMapsOnSubspacesOfProducts
import Mathlib
set_option autoImplicit false
open Set
open scoped ContDiff
noncomputable section
namespace YangMills.Construction.Matrices.GroupLieProduct.Subspaces.AnalyticCalculus
open YangMills.Construction.Coordinates YangMills.Construction.Coordinates.ComplexCoordinates
open YangMills.Construction.Matrices YangMills.Construction.Matrices.PowerExpCharts
variable {S R S' R' : Type}
abbrev ParamSpace (n : ℕ) (R : Type) [Fintype R] : Type :=
  ComplexCoordinates (n + 3 * Fintype.card R)
abbrev IndexEnum (R : Type) [Fintype R] : Type := R × Fin 3 ≃ Fin (3 * Fintype.card R)
def linearPart [Fintype R] {n : ℕ} (z : ParamSpace n R) (i : Fin n) : ℂ :=
  z (Fin.castAdd _ i)
def angularPart [Fintype R] {n : ℕ} (σ : IndexEnum R) (z : ParamSpace n R) (r : R)
    (a : Fin 3) : ℂ :=
  z (Fin.natAdd n (σ (r, a)))
def pauliSum (c : R → Fin 3 → ℂ) (r : R) : ComplexMatrix2 := ∑ a, c r a • pauliFamily a
def basisExpChart [Fintype R] {n : ℕ} {E : Submodule ℝ (S → ComplexMatrix2)}
    (b : Module.Basis (Fin n) ℝ E) (σ : IndexEnum R) (p₀ : R ⊕ S → ComplexMatrix2)
    (z : ParamSpace n R) : R ⊕ S → ComplexMatrix2 :=
  ofParts
    (fun r => ComplexMatrix2.matExp (Complex.I • pauliSum (angularPart σ z) r) *
      groupComponent p₀ r)
    (algebraComponent p₀ + ∑ i, linearPart z i • ((b i : E) : S → ComplexMatrix2))
def basisExpChartSource [Fintype R] (n : ℕ) (σ : IndexEnum R) : Set (ParamSpace n R) :=
  {z | z ∈ realLocus (n + 3 * Fintype.card R) ∧
    ∀ r, ∑ a, (angularPart σ z r a).re ^ 2 < Real.log 2 ^ 2}
def ofRealVector {N : ℕ} (u : Fin N → ℝ) : ComplexCoordinates N := fun j => (u j : ℂ)
def IsSmoothOnRealLocus {N l : ℕ} (T : Set (ComplexCoordinates N))
    (g : ComplexCoordinates N → ComplexCoordinates l) : Prop :=
  ContDiffOn ℝ ∞ (g ∘ ofRealVector) (ofRealVector ⁻¹' T)
def HasLocalHolomorphicExtensions {N l : ℕ} (T : Set (ComplexCoordinates N))
    (g : ComplexCoordinates N → ComplexCoordinates l) : Prop :=
  ∀ x ∈ T, ∃ U : Set (ComplexCoordinates N), IsOpen U ∧ x ∈ U ∧ U ∩ realLocus N ⊆ T ∧
    ∃ h : ComplexCoordinates N → ComplexCoordinates l,
      ComplexCoordinates.IsHolomorphicIn U h ∧ EqOn h g (U ∩ realLocus N)
def IsAnalyticInParams {N l : ℕ} (T : Set (ComplexCoordinates N))
    (g : ComplexCoordinates N → ComplexCoordinates l) : Prop :=
  HasLocalHolomorphicExtensions T g ∧ IsSmoothOnRealLocus T g ∧
    ComplexCoordinates.IsRealAnalyticIn T g
def scalarEquiv : ℂ ≃ ComplexCoordinates 1 := (Equiv.funUnique (Fin 1) ℂ).symm
def FiniteDimensionalSubmodules (S : Type) [Fintype S] : Prop :=
  ∀ E : Submodule ℝ (S → ComplexMatrix2), E ≤ hermitianTracelessFunctions S →
    FiniteDimensional ℝ E
def LinearMapsAnalytic [Fintype S] (E : Submodule ℝ (S → ComplexMatrix2))
    (E' : Submodule ℝ (S' → ComplexMatrix2)) : Prop :=
  ∀ (L : E →ₗ[ℝ] E') (f : (S → ComplexMatrix2) → S' → ComplexMatrix2), (∀ x : E, f x = L x) →
    IsAnalyticOnSubspace E E' (E : Set (S → ComplexMatrix2)) f
def ConstantMapsAnalytic [Fintype S] [Fintype R] (E : Submodule ℝ (S → ComplexMatrix2))
    (E' : Submodule ℝ (S' → ComplexMatrix2)) (R' : Type) (W : Set (R ⊕ S → ComplexMatrix2)) :
    Prop :=
  (∀ (l : ℕ) (c : ComplexCoordinates l), IsSubspaceAnalyticToCoords E W fun _ => c) ∧
    ∀ c ∈ subspaceTimesGroup E' R', IsSubspaceAnalyticToProduct E E' W fun _ => c
def ProjectionsAnalytic [Fintype S] (E : Submodule ℝ (S → ComplexMatrix2)) (R : Type)
    [Fintype R] : Prop :=
  IsSubspaceAnalyticToProduct E E (subspaceTimesGroup E R)
      (fun q : R ⊕ S → ComplexMatrix2 =>
        (ofParts (fun x : Empty => x.elim) (algebraComponent q) : Empty ⊕ S → ComplexMatrix2)) ∧
    IsSubspaceAnalyticToProduct E (⊥ : Submodule ℝ (Empty → ComplexMatrix2))
      (subspaceTimesGroup E R)
      fun q : R ⊕ S → ComplexMatrix2 =>
        (ofParts (groupComponent q) (fun x : Empty => x.elim) : R ⊕ Empty → ComplexMatrix2)
def PairingAnalytic [Fintype S] [Fintype R] (E : Submodule ℝ (S → ComplexMatrix2))
    (W : Set (R ⊕ S → ComplexMatrix2)) : Prop :=
  ∀ (S₁ S₂ R₁ R₂ : Type) [Fintype S₁] [Fintype S₂] [Fintype R₁] [Fintype R₂]
    (E₁ : Submodule ℝ (S₁ → ComplexMatrix2)) (E₂ : Submodule ℝ (S₂ → ComplexMatrix2))
    (f₁ : (R ⊕ S → ComplexMatrix2) → R₁ ⊕ S₁ → ComplexMatrix2)
    (f₂ : (R ⊕ S → ComplexMatrix2) → R₂ ⊕ S₂ → ComplexMatrix2),
    IsSubspaceAnalyticToProduct E E₁ W f₁ → IsSubspaceAnalyticToProduct E E₂ W f₂ →
      IsSubspaceAnalyticToProduct E (sumSubmodule E₁ E₂) W fun p => pairPoint (f₁ p) (f₂ p)
def AnalyticIffHolomorphicExtensions [Fintype S] [Fintype R] (S' R' : Type)
    (W : Set (R ⊕ S → ComplexMatrix2)) : Prop :=
  (∀ (l : ℕ) (f : (R ⊕ S → ComplexMatrix2) → ComplexCoordinates l),
    IsSubspaceAnalyticToCoords (hermitianTracelessFunctions S) W f ↔
      HasLocalHolomorphicExtensionToCoords W f) ∧
    ∀ f : (R ⊕ S → ComplexMatrix2) → R' ⊕ S' → ComplexMatrix2,
      MapsTo f W (subspaceTimesGroup (hermitianTracelessFunctions S') R') →
      (IsSubspaceAnalyticToProduct (hermitianTracelessFunctions S)
          (hermitianTracelessFunctions S') W f ↔
        HasLocalHolomorphicExtensionToProduct W f)
def GroupPowerAnalyticity (R R' : Type) [Fintype R] [Fintype R'] : Prop :=
  ∀ W : Set (R ⊕ Empty → ComplexMatrix2),
    IsOpenInSubspaceTimesGroup (hermitianTracelessFunctions Empty) W →
    specialUnitaryPower.IsOpenSubset (asGroupFactors ⁻¹' W) ∧
    ∀ b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless,
      (∀ f : (R → ComplexMatrix2) → ℂ,
        IsSubspaceAnalyticToCoords (hermitianTracelessFunctions Empty) W
            (fun q => scalarEquiv (f (groupComponent q))) ↔
          IsLocallyHolomorphicRestriction (HolomorphicScalar b) id (asGroupFactors ⁻¹' W) f) ∧
      (∀ f : (R → ComplexMatrix2) → ComplexMatrix2,
        IsSubspaceAnalyticToCoords (hermitianTracelessFunctions Empty) W
            (fun q => matrixEquiv (f (groupComponent q))) ↔
          IsLocallyHolomorphicRestriction (HolomorphicMatrix b) id (asGroupFactors ⁻¹' W) f) ∧
      ∀ f : (R → ComplexMatrix2) → R' → ComplexMatrix2,
        MapsTo f (asGroupFactors ⁻¹' W) (specialUnitaryPower R') →
        (IsSubspaceAnalyticToProduct (hermitianTracelessFunctions Empty)
            (hermitianTracelessFunctions Empty) W
            (fun q => asGroupFactors (f (groupComponent q))) ↔
          IsLocallyHolomorphicRestriction (IsHolomorphicToProduct b) asGroupFactors
            (asGroupFactors ⁻¹' W) f)
def CompositionAnalytic [Fintype S] [Fintype R] [Fintype S']
    (E : Submodule ℝ (S → ComplexMatrix2)) (E' : Submodule ℝ (S' → ComplexMatrix2)) (R' : Type)
    [Fintype R'] (W : Set (R ⊕ S → ComplexMatrix2)) : Prop :=
  ∀ f : (R ⊕ S → ComplexMatrix2) → R' ⊕ S' → ComplexMatrix2,
    IsSubspaceAnalyticToProduct E E' W f →
    ContinuousOn f W ∧
    ∀ W' : Set (R' ⊕ S' → ComplexMatrix2), IsOpenInSubspaceTimesGroup E' W' →
      ComplexMatrix2.IsRelativelyOpen (subspaceTimesGroup E R) (W ∩ f ⁻¹' W') ∧
      (∀ (l : ℕ) (g : (R' ⊕ S' → ComplexMatrix2) → ComplexCoordinates l),
        IsSubspaceAnalyticToCoords E' W' g →
          IsSubspaceAnalyticToCoords E (W ∩ f ⁻¹' W') (g ∘ f)) ∧
      ∀ (S'' R'' : Type) [Fintype S''] [Fintype R''] (E'' : Submodule ℝ (S'' → ComplexMatrix2))
        (g : (R' ⊕ S' → ComplexMatrix2) → R'' ⊕ S'' → ComplexMatrix2),
        IsSubspaceAnalyticToProduct E' E'' W' g →
          IsSubspaceAnalyticToProduct E E'' (W ∩ f ⁻¹' W') (g ∘ f)
def BasisExpChartIsChart [Fintype R] {n : ℕ} {E : Submodule ℝ (S → ComplexMatrix2)}
    (b : Module.Basis (Fin n) ℝ E) (σ : IndexEnum R) (p₀ : R ⊕ S → ComplexMatrix2) : Prop :=
  MapsTo (basisExpChart b σ p₀) (realLocus (n + 3 * Fintype.card R)) (subspaceTimesGroup E R) ∧
    basisExpChart b σ p₀ 0 = p₀ ∧
    ComplexMatrix2.IsRelativelyOpen (realLocus (n + 3 * Fintype.card R))
      (basisExpChartSource n σ) ∧
    InjOn (basisExpChart b σ p₀) (basisExpChartSource n σ) ∧
    ∀ T : Set (ParamSpace n R), ComplexMatrix2.IsRelativelyOpen (basisExpChartSource n σ) T →
      ComplexMatrix2.IsRelativelyOpen (subspaceTimesGroup E R) (basisExpChart b σ p₀ '' T)
def AnalyticInChartOfAnalytic [Fintype S] [Fintype R] {n : ℕ}
    {E : Submodule ℝ (S → ComplexMatrix2)} (E' : Submodule ℝ (S' → ComplexMatrix2)) (R' : Type)
    (b : Module.Basis (Fin n) ℝ E) (σ : IndexEnum R) (p₀ : R ⊕ S → ComplexMatrix2) : Prop :=
  ∀ T : Set (ParamSpace n R), ComplexMatrix2.IsRelativelyOpen (basisExpChartSource n σ) T →
    (∀ (l : ℕ) (f : (R ⊕ S → ComplexMatrix2) → ComplexCoordinates l),
      IsSubspaceAnalyticToCoords E (basisExpChart b σ p₀ '' T) f →
        IsAnalyticInParams T (f ∘ basisExpChart b σ p₀)) ∧
    ∀ (k : ℕ) (μ : R' ⊕ S' ≃ Fin k) (f : (R ⊕ S → ComplexMatrix2) → R' ⊕ S' → ComplexMatrix2),
      IsSubspaceAnalyticToProduct E E' (basisExpChart b σ p₀ '' T) f →
        IsAnalyticInParams T (matrixPiEquiv μ ∘ f ∘ basisExpChart b σ p₀)
def AnalyticOfAnalyticInChart [Fintype S] [Fintype R] {n : ℕ}
    {E : Submodule ℝ (S → ComplexMatrix2)} (b : Module.Basis (Fin n) ℝ E) (σ : IndexEnum R)
    (p₀ : R ⊕ S → ComplexMatrix2) : Prop :=
  ∀ T : Set (ParamSpace n R), ComplexMatrix2.IsRelativelyOpen (basisExpChartSource n σ) T →
    ∀ (l : ℕ) (f : (R ⊕ S → ComplexMatrix2) → ComplexCoordinates l),
      ComplexCoordinates.IsRealAnalyticIn T (f ∘ basisExpChart b σ p₀) →
        IsSubspaceAnalyticToCoords E (basisExpChart b σ p₀ '' T) f
def AnalyticIffCoefficientsAnalytic [Fintype S] [Fintype R]
    (E : Submodule ℝ (S → ComplexMatrix2)) (E' : Submodule ℝ (S' → ComplexMatrix2))
    (W : Set (R ⊕ S → ComplexMatrix2)) : Prop :=
  ∀ (m : ℕ) (b' : Module.Basis (Fin m) ℝ E') (f : (R ⊕ S → ComplexMatrix2) → S' → ComplexMatrix2)
    (c : Fin m → (R ⊕ S → ComplexMatrix2) → ℝ),
    (∀ p ∈ W, f p = ∑ i, c i p • ((b' i : E') : S' → ComplexMatrix2)) →
      (IsSubspaceAnalyticToProduct E E' W
          (fun p => (ofParts (fun x : Empty => x.elim) (f p) : Empty ⊕ S' → ComplexMatrix2)) ↔
        ∀ i, IsSubspaceAnalyticToCoords E W fun p => scalarEquiv (c i p : ℂ))
def AnalyticCalculusStatement : Prop :=
  ∀ (S R S' R' : Type) [Fintype S] [Fintype R] [Fintype S'] [Fintype R'],
    FiniteDimensionalSubmodules S ∧
    (∀ W : Set (R ⊕ S → ComplexMatrix2),
      IsOpenInSubspaceTimesGroup (hermitianTracelessFunctions S) W →
      AnalyticIffHolomorphicExtensions S' R' W) ∧
    ([Nonempty R] → [Nonempty R'] → GroupPowerAnalyticity R R') ∧
    ∀ (E : Submodule ℝ (S → ComplexMatrix2)) (E' : Submodule ℝ (S' → ComplexMatrix2)),
      E ≤ hermitianTracelessFunctions S → E' ≤ hermitianTracelessFunctions S' →
      LinearMapsAnalytic E E' ∧ ProjectionsAnalytic E R ∧
      (∀ W : Set (R ⊕ S → ComplexMatrix2), IsOpenInSubspaceTimesGroup E W →
        ConstantMapsAnalytic E E' R' W ∧ PairingAnalytic E W ∧
        CompositionAnalytic E E' R' W ∧ AnalyticIffCoefficientsAnalytic E E' W) ∧
      ∀ (n : ℕ) (b : Module.Basis (Fin n) ℝ E) (σ : IndexEnum R) (p₀ : R ⊕ S → ComplexMatrix2),
        p₀ ∈ subspaceTimesGroup E R →
        BasisExpChartIsChart b σ p₀ ∧ AnalyticInChartOfAnalytic E' R' b σ p₀ ∧
        AnalyticOfAnalyticInChart b σ p₀
end YangMills.Construction.Matrices.GroupLieProduct.Subspaces.AnalyticCalculus
end
