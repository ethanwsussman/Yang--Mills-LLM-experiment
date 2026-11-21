import YangMills.Construction.PeriodicLattice.TriplesOnFiniteBondSets
import YangMills.Construction.PeriodicOperators.Jets
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.PeriodicOperators
section QuotFunctions
variable (P : PeriodicData)
def liftQuotFn (g : P.UnitQuot → ℂ) : P.Carrier → ℂ := liftQuotField P 1 g
def IsQuotInvariant (f : P.Carrier → ℂ) : Prop :=
  ∀ a a', P.mkQuot 1 a = P.mkQuot 1 a' → f a = f a'
def descendFn (f : P.Carrier → ℂ) : P.UnitQuot → ℂ :=
  fun q => Classical.epsilon fun z => ∀ a, P.mkQuot 1 a = q → f a = z
variable {P}
theorem descendFn_mkQuot {f : P.Carrier → ℂ} (hf : IsQuotInvariant P f)
    (a : P.Carrier) : descendFn P f (P.mkQuot 1 a) = f a := by
  have hz : ∃ z, ∀ a', P.mkQuot 1 a' = P.mkQuot 1 a → f a' = z :=
    ⟨f a, fun a' e => hf a' a e⟩
  exact (Classical.epsilon_spec hz a rfl).symm
end QuotFunctions
section KernelEntries
variable {P Q : PeriodicData}
def IsInvertibleQuotHom (A : QuotHom P P) : Prop :=
  ∀ g : P.UnitQuot → ℂ, ∃! f : P.UnitQuot → ℂ, A f = g
theorem IsInvertibleQuotHom.apply_quotHomInverse {A : QuotHom P P}
    (hA : IsInvertibleQuotHom A) (g : P.UnitQuot → ℂ) : A (quotHomInverse A g) = g := by
  have hu : IsUnit (A : Module.End ℂ (P.UnitQuot → ℂ)) := by
    refine (Module.End.isUnit_iff _).2 ⟨fun f f' e => ?_, fun g' => (hA g').exists⟩
    exact (hA (A f)).unique rfl e.symm
  have e := Ring.mul_inverse_cancel (A : Module.End ℂ (P.UnitQuot → ℂ)) hu
  exact LinearMap.congr_fun e g
def carrierEntry (A : QuotHom P Q) (b : Q.Carrier) (a : P.Carrier) : ℂ :=
  linearMapEntry A (Q.mkQuot 1 b) (P.mkQuot 1 a)
theorem linearMapOfEntries_eq_applyKernel {J J' : Type} [Finite J] (K : J' → J → ℂ) (f : J → ℂ) :
    linearMapOfEntries K f = applyKernel K f := by
  classical
  have := Fintype.ofFinite J
  let L₀ : (J → ℂ) →ₗ[ℂ] (J' → ℂ) :=
    { toFun := fun g j' => ∑ j, K j' j * g j
      map_add' := fun g g' => by
        funext j'
        simp [mul_add, Finset.sum_add_distrib]
      map_smul' := fun z g => by
        funext j'
        simp [Finset.mul_sum, mul_left_comm] }
  have hL₀ : linearMapEntry L₀ = K := by
    funext j' j
    simp [linearMapEntry, L₀, Pi.single_apply]
  have hL : linearMapEntry (linearMapOfEntries K) = K :=
    Classical.epsilon_spec (p := fun L => linearMapEntry L = K) ⟨L₀, hL₀⟩
  funext j'
  have hf : f = ∑ j, f j • (Pi.single j 1 : J → ℂ) := by
    funext j
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hf]
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, applyKernel,
    tsum_fintype]
  refine Finset.sum_congr rfl fun j _ => ?_
  have e := congrFun (congrFun hL j') j
  simp only [linearMapEntry] at e
  rw [mul_comm]
  congr 1
def FactorsThroughQuot (F : Q.Carrier → P.Carrier → ℂ) : Prop :=
  ∀ b₁ b₂ a₁ a₂, Q.mkQuot 1 b₁ = Q.mkQuot 1 b₂ → P.mkQuot 1 a₁ = P.mkQuot 1 a₂ →
    F b₁ a₁ = F b₂ a₂
end KernelEntries
section Entrywise
variable {Y E : Type}
def ContinuousOnEntrywise {n : ℕ} (coeff : Y → E → ℂ) (S : Set (Coordinates.ComplexCoordinates n))
    (A : Coordinates.ComplexCoordinates n → Y) : Prop :=
  1 ≤ n ∧ ∀ e, ContinuousOn (fun x => coeff (A x) e) S
def HolomorphicOnEntrywise {n : ℕ} (coeff : Y → E → ℂ) (U : Set (Coordinates.ComplexCoordinates n))
    (A : Coordinates.ComplexCoordinates n → Y) : Prop :=
  1 ≤ n ∧ IsOpen U ∧
    ∀ e, Coordinates.ComplexCoordinates.IsHolomorphicIn (N' := 1) U fun x _ => coeff (A x) e
def BoundedOnEntrywise {X : Type} (coeff : Y → E → ℂ) (S : Set X) (A : X → Y) : Prop :=
  ∀ e, ∃ C : ℝ, ∀ x ∈ S, ‖coeff (A x) e‖ ≤ C
end Entrywise
section CoefficientFamilies
def quotHomEntries {P Q : PeriodicData} (A : QuotHom P Q) (e : Q.UnitQuot × P.UnitQuot) : ℂ :=
  linearMapEntry A e.1 e.2
def matrixCoeffs {a b : ℕ} (A : Matrix (Fin a) (Fin b) ℂ) (e : Fin a × Fin b) : ℂ := A e.1 e.2
def endTracelessCoeffs (T : Module.End ℂ Matrices.ComplexMatrix2.traceless) (e : Fin 3 × Fin 3) : ℂ :=
  OneLoop.pauliCoordinateEquiv (T (OneLoop.pauliBasis e.1)) e.2
def quotFnEntries {P : PeriodicData} (f : P.UnitQuot → ℂ) (q : P.UnitQuot) : ℂ := f q
variable {P Q : PeriodicData}
abbrev QuotHomFamilyContinuousOn {n : ℕ} (S : Set (Coordinates.ComplexCoordinates n))
    (A : Coordinates.ComplexCoordinates n → QuotHom P Q) : Prop :=
  ContinuousOnEntrywise quotHomEntries S A
abbrev QuotHomFamilyHolomorphicOn {n : ℕ} (U : Set (Coordinates.ComplexCoordinates n))
    (A : Coordinates.ComplexCoordinates n → QuotHom P Q) : Prop :=
  HolomorphicOnEntrywise quotHomEntries U A
abbrev QuotHomFamilyBoundedOn {X : Type} (S : Set X) (A : X → QuotHom P Q) : Prop :=
  BoundedOnEntrywise quotHomEntries S A
end CoefficientFamilies
section Concatenation
variable {n n' : ℕ} {Y : Type}
def appendCoords (x : Coordinates.ComplexCoordinates n) (y : Coordinates.ComplexCoordinates n') :
    Coordinates.ComplexCoordinates (n + n') :=
  Fin.append x y
def splitCoords (z : Coordinates.ComplexCoordinates (n + n')) :
    Coordinates.ComplexCoordinates n × Coordinates.ComplexCoordinates n' :=
  (fun i => z (Fin.castAdd n' i), fun i => z (Fin.natAdd n i))
def appendSet (S : Set (Coordinates.ComplexCoordinates n × Coordinates.ComplexCoordinates n')) :
    Set (Coordinates.ComplexCoordinates (n + n')) :=
  (fun p => appendCoords p.1 p.2) '' S
def HoldsOnAppended
    (R : Set (Coordinates.ComplexCoordinates (n + n')) →
      (Coordinates.ComplexCoordinates (n + n') → Y) → Prop)
    (S : Set (Coordinates.ComplexCoordinates n × Coordinates.ComplexCoordinates n'))
    (f : Coordinates.ComplexCoordinates n × Coordinates.ComplexCoordinates n' → Y) : Prop :=
  R (appendSet S) (f ∘ splitCoords)
end Concatenation
section EntireMaps
variable {n : ℕ} {Y E : Type}
def IsEntireFn (f : Coordinates.ComplexCoordinates n → ℂ) : Prop :=
  1 ≤ n ∧ Coordinates.ComplexCoordinates.IsHolomorphicIn (N' := 1) univ fun z _ => f z
def FourierSymbolIsEntire (P Q : PeriodicData) (T : Q.Carrier → P.Carrier → ℂ) : Prop :=
  SymbolSummableOn P Q T univ ∧
    ∀ b a, IsEntireFn (n := 4) fun k => fourierSymbol P Q T k b a
def HasEntireKernelEntries (F P Q : PeriodicData)
    (T : (F.Carrier → ℂ) → Q.Carrier → P.Carrier → ℂ) : Prop :=
  ∀ b a, ∃ (S : Set F.Carrier) (l : ℕ) (e : Fin l ≃ S) (h : Coordinates.ComplexCoordinates l → ℂ),
    IsEntireFn h ∧ ∀ ζ, T ζ b a = h (fieldValues e ζ)
end EntireMaps
section OpenFamilies
variable {A : Type} (IsOp : Set A → Prop)
def IsNhdOf (X N : Set A) : Prop := ∃ U, IsOp U ∧ X ⊆ U ∧ U ⊆ N
def IsInteriorPt (X : Set A) (a : A) : Prop := IsNhdOf IsOp {a} X
def interiorBy (X : Set A) : Set A := {a | IsInteriorPt IsOp X a}
def EventuallyNear (X : Set A) (R : A → Prop) : Prop := ∃ U, IsOp U ∧ X ⊆ U ∧ ∀ a ∈ U, R a
def ExistsOpenNear (X : Set A) (R : Set A → Prop) : Prop := ∃ U, IsOp U ∧ X ⊆ U ∧ R U
end OpenFamilies
def openImStrip (s : ℝ) : Set (Fin 4 → ℂ) := {k | ∀ μ, |(k μ).im| < s}
def IsImStrip (D : Set (Fin 4 → ℂ)) : Prop :=
  ∃ s : ℝ, 0 < s ∧ (D = imStrip s ∨ D = openImStrip s)
end YangMills.Construction.PeriodicOperators
end
