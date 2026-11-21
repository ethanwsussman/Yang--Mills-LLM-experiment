import YangMills.Construction.PeriodicOperators.EntriesAtTheClassesAndMapsIntoHom
import Mathlib
set_option autoImplicit false
open Filter Set
open scoped ENNReal Nat Topology
noncomputable section
namespace YangMills.Construction
namespace PeriodicOperators
section Determinants
variable {I I' : PeriodicData}
open Classical in
def quotIndicator (c : I.UnitQuot) : I.UnitQuot → ℂ := Pi.single c 1
def matrixOfEnum {N : ℕ} (M : QuotHom I I) (e : Fin N ≃ I.UnitQuot) :
    Matrix (Fin N) (Fin N) ℂ :=
  Matrix.of fun α β => linearMapEntry M (e α) (e β)
def quotHomDet (M : QuotHom I I) : ℂ :=
  Classical.epsilon fun z => ∀ e : Fin (Nat.card I.UnitQuot) ≃ I.UnitQuot,
    (matrixOfEnum M e).det = z
end Determinants
namespace EntriesDets
def EntryFormulas (I I' I'' : PeriodicData) : Prop :=
  (∀ (M : QuotHom I I') (f : I.UnitQuot → ℂ) (x : I'.UnitQuot),
    M f x = ∑ᶠ c, linearMapEntry M x c * f c) ∧
  (∀ M : QuotHom I I, IsInvertibleQuotHom M →
    ∀ f g : I.UnitQuot → ℂ, quotHomInverse M g = f ↔ M f = g) ∧
  ∀ (M : QuotHom I I') (M' : QuotHom I'' I) (x : I'.UnitQuot) (y : I''.UnitQuot),
    linearMapEntry (M.comp M') x y = ∑ᶠ c, linearMapEntry M x c * linearMapEntry M' c y
def OfEntriesSpec (I I' : PeriodicData) : Prop :=
  ∀ K : I'.UnitQuot → I.UnitQuot → ℂ,
    (∀ (f : I.UnitQuot → ℂ) (x : I'.UnitQuot), linearMapOfEntries K f x = ∑ᶠ c, K x c * f c) ∧
    ∀ (x : I'.UnitQuot) (c : I.UnitQuot), linearMapEntry (linearMapOfEntries K) x c = K x c
def SymbolOnRealPoints (I : PeriodicData) : Prop :=
  ∀ T : I.Carrier → I.Carrier → ℂ, IsPeriodicKernel I I T →
    (∀ κ ∈ realDualPoints, SymbolSummableAt I I T κ ∧ FactorsThroughQuot (fourierSymbol I I T κ)) ∧
    QuotHomFamilyContinuousOn (n := 4) realDualPoints (symbolHom I I T) ∧
    ((∀ κ ∈ realDualPoints, IsInvertibleQuotHom (symbolHom I I T κ)) →
      QuotHomFamilyContinuousOn (n := 4) realDualPoints fun κ => quotHomInverse (symbolHom I I T κ))
def matrixAsPoint {N : ℕ} (X : Matrix (Fin N) (Fin N) ℂ) : Fin N × Fin N → ℂ :=
  fun e => X e.1 e.2
def permQuotient {N : ℕ} (σ : Equiv.Perm (Fin N)) : ℂ :=
  ∏ α : Fin N, ∏ β ∈ Finset.Ioi α,
    (((σ β : ℕ) : ℂ) - ((σ α : ℕ) : ℂ)) / (((β : ℕ) : ℂ) - ((α : ℕ) : ℂ))
def EmptyMatrixFacts : Prop :=
  (∀ X : Matrix (Fin 0) (Fin 0) ℂ, IsUnit X ∧ X⁻¹ = X ∧ X = 1 ∧ X.det = 1) ∧
    Nat.card (Equiv.Perm (Fin 0)) = 1
def MatrixDetFacts (N : ℕ) : Prop :=
  (∀ X : Matrix (Fin N) (Fin N) ℂ,
    X.det = ∑ σ : Equiv.Perm (Fin N), permQuotient σ * ∏ α, X α (σ α)) ∧
  (1 ≤ N → ∀ σ : Equiv.Perm (Fin N),
    permQuotient σ = ((Equiv.Perm.sign σ : ℤ) : ℂ)) ∧
  (∃ P : MvPolynomial (Fin N × Fin N) ℂ, ∀ X : Matrix (Fin N) (Fin N) ℂ,
    MvPolynomial.eval (matrixAsPoint X) P = X.det) ∧
  (∀ X Y : Matrix (Fin N) (Fin N) ℂ, (X * Y).det = X.det * Y.det) ∧
  (1 : Matrix (Fin N) (Fin N) ℂ).det = 1 ∧
  (∀ X : Matrix (Fin N) (Fin N) ℂ, IsUnit X ↔ X.det ≠ 0) ∧
  ∀ α β : Fin N, ∃ P : MvPolynomial (Fin N × Fin N) ℂ, ∀ X : Matrix (Fin N) (Fin N) ℂ, IsUnit X →
    X⁻¹ α β = MvPolynomial.eval (matrixAsPoint X) P / X.det
def QuotHomDetFacts (I : PeriodicData) : Prop :=
  ∀ M : QuotHom I I,
    (∀ e : Fin (Nat.card I.UnitQuot) ≃ I.UnitQuot,
      (matrixOfEnum M e).det = quotHomDet M) ∧
    (1 ≤ Nat.card I.UnitQuot →
      LinearIndependent ℂ (quotIndicator (I := I)) ∧
      Submodule.span ℂ (range (quotIndicator (I := I))) = ⊤ ∧
      quotHomDet M = LinearMap.det M ∧
      ∀ b : Module.Basis (Fin (Nat.card I.UnitQuot)) ℂ (I.UnitQuot → ℂ),
        (LinearMap.toMatrix b b M).det = quotHomDet M) ∧
    (∀ e : Fin (Nat.card I.UnitQuot) ≃ I.UnitQuot,
      (IsInvertibleQuotHom M ↔ IsUnit (matrixOfEnum M e)) ∧
      (IsInvertibleQuotHom M →
        (matrixOfEnum M e)⁻¹ = matrixOfEnum (quotHomInverse M) e)) ∧
    (IsInvertibleQuotHom M ↔ quotHomDet M ≠ 0)
abbrev HolomorphicFnOn {n : ℕ} (O : Set (Coordinates.ComplexCoordinates n))
    (u : Coordinates.ComplexCoordinates n → ℂ) : Prop :=
  Coordinates.ComplexCoordinates.IsHolomorphicIn (N' := 1) O fun z _ => u z
def MatrixFamilyDetInv (n N : ℕ) : Prop :=
  ∀ (S : Set (Coordinates.ComplexCoordinates n))
    (X : Coordinates.ComplexCoordinates n → Matrix (Fin N) (Fin N) ℂ),
    (∀ z ∈ S, IsUnit (X z)) →
    (ContinuousOnEntrywise matrixCoeffs S X →
      ContinuousOn (fun z => (X z).det) S ∧
        ContinuousOnEntrywise matrixCoeffs S fun z => (X z)⁻¹) ∧
    (IsOpen S → HolomorphicOnEntrywise matrixCoeffs S X →
      HolomorphicFnOn S (fun z => (X z).det) ∧
        HolomorphicOnEntrywise matrixCoeffs S fun z => (X z)⁻¹)
def QuotHomFamilyDetInv (n : ℕ) (I : PeriodicData) : Prop :=
  ∀ (S : Set (Coordinates.ComplexCoordinates n)) (M : Coordinates.ComplexCoordinates n → QuotHom I I),
    (∀ z ∈ S, IsInvertibleQuotHom (M z)) →
    (QuotHomFamilyContinuousOn S M →
      ContinuousOn (fun z => quotHomDet (M z)) S ∧
        QuotHomFamilyContinuousOn S fun z => quotHomInverse (M z)) ∧
    (IsOpen S → QuotHomFamilyHolomorphicOn S M →
      HolomorphicFnOn S (fun z => quotHomDet (M z)) ∧
        QuotHomFamilyHolomorphicOn S fun z => quotHomInverse (M z))
def QuotHomFamilyInvOnDual (I : PeriodicData) : Prop :=
  ∀ (S : Set (Coordinates.ComplexCoordinates 4)) (M : Coordinates.ComplexCoordinates 4 → QuotHom I I),
    (∀ z ∈ S, IsInvertibleQuotHom (M z)) →
    (QuotHomFamilyContinuousOn S M → QuotHomFamilyContinuousOn S fun z => quotHomInverse (M z)) ∧
    (IsOpen S → QuotHomFamilyHolomorphicOn S M →
      QuotHomFamilyHolomorphicOn S fun z => quotHomInverse (M z))
def ExpInvHolomorphic : Prop :=
  HolomorphicFnOn (n := 1) univ (fun z => Complex.exp (z 0)) ∧
  HolomorphicFnOn (n := 1) {z | z 0 ≠ 0} (fun z => (z 0)⁻¹) ∧
  ∀ (n : ℕ), 1 ≤ n → ∀ (O : Set (Coordinates.ComplexCoordinates n))
    (f : Coordinates.ComplexCoordinates n → ℂ),
    HolomorphicFnOn O f →
      HolomorphicFnOn O (fun z => Complex.exp (f z)) ∧
      ((∀ z ∈ O, f z ≠ 0) → HolomorphicFnOn O fun z => 1 / f z)
def HolomorphicTuples (n b : ℕ) (O : Set (Coordinates.ComplexCoordinates n)) : Prop :=
  (∀ u : Fin b → Coordinates.ComplexCoordinates n → ℂ,
    Coordinates.ComplexCoordinates.IsHolomorphicIn O (fun z i => u i z) ↔
      ∀ i, HolomorphicFnOn O (u i)) ∧
  ∀ f : Coordinates.ComplexCoordinates n → Coordinates.ComplexCoordinates b,
    Coordinates.ComplexCoordinates.IsHolomorphicIn O f → ContinuousOn f O
def EntrywiseHolomorphicContinuous {Y E : Type} (entries : Y → E → ℂ) {n : ℕ}
    (O : Set (Coordinates.ComplexCoordinates n)) : Prop :=
  ∀ M : Coordinates.ComplexCoordinates n → Y, HolomorphicOnEntrywise entries O M →
    ContinuousOnEntrywise entries O M
def PolynomialHolomorphic (n : ℕ) (O : Set (Coordinates.ComplexCoordinates n)) : Prop :=
  (∀ (b : ℕ) (u : Fin b → Coordinates.ComplexCoordinates n → ℂ) (P : MvPolynomial (Fin b) ℂ),
    (∀ i, HolomorphicFnOn O (u i)) →
      HolomorphicFnOn O fun z => MvPolynomial.eval (fun i => u i z) P) ∧
  (∀ c : ℂ, HolomorphicFnOn O fun _ => c) ∧
  (∀ (b : ℕ) (u : Fin b → Coordinates.ComplexCoordinates n → ℂ), (∀ i, HolomorphicFnOn O (u i)) →
    HolomorphicFnOn O (fun z => ∑ i, u i z) ∧
      HolomorphicFnOn O fun z => ∏ i, u i z) ∧
  ∀ (c : ℂ) (u : Coordinates.ComplexCoordinates n → ℂ), HolomorphicFnOn O u →
    HolomorphicFnOn O fun z => c * u z
def CoordPolyHolomorphic (n : ℕ) : Prop :=
  (∀ j : Fin n, HolomorphicFnOn univ fun z : Coordinates.ComplexCoordinates n => z j) ∧
  ∀ P : MvPolynomial (Fin n) ℂ,
    HolomorphicFnOn univ fun z : Coordinates.ComplexCoordinates n => MvPolynomial.eval z P
section Partials
variable {n : ℕ}
def partialDeriv (j : Fin n) (u : Coordinates.ComplexCoordinates n → ℂ) :
    Coordinates.ComplexCoordinates n → ℂ :=
  fun z => deriv (fun ζ : ℂ => u (z + ζ • Coordinates.ComplexCoordinates.stdBasisVector j)) 0
def iteratedPartial (l : List (Fin n)) (u : Coordinates.ComplexCoordinates n → ℂ) :
    Coordinates.ComplexCoordinates n → ℂ :=
  l.foldr partialDeriv u
def multiPartial (q : Fin n → ℕ) (u : Coordinates.ComplexCoordinates n → ℂ) :
    Coordinates.ComplexCoordinates n → ℂ :=
  iteratedPartial ((List.finRange n).flatMap fun j => List.replicate (q j) j) u
def linComb {X : Type} [AddCommGroup X] [Module ℂ X] {b : ℕ}
    (u : Fin b → Coordinates.ComplexCoordinates n → ℂ) (v : Fin b → X) :
    Coordinates.ComplexCoordinates n → X :=
  fun z => ∑ i, u i z • v i
def linCombPartial {X : Type} [AddCommGroup X] [Module ℂ X] {b : ℕ} (q : Fin n → ℕ)
    (u : Fin b → Coordinates.ComplexCoordinates n → ℂ) (v : Fin b → X) :
    Coordinates.ComplexCoordinates n → X :=
  linComb (fun i => multiPartial q (u i)) v
def openPolydisc (ρ : Fin n → ℝ) (a : Coordinates.ComplexCoordinates n) :
    Set (Coordinates.ComplexCoordinates n) :=
  {z | ∀ j, ‖z j - a j‖ < ρ j}
def PartialsHolomorphicComm (O : Set (Coordinates.ComplexCoordinates n)) : Prop :=
  ∀ u : Coordinates.ComplexCoordinates n → ℂ, HolomorphicFnOn O u →
    (∀ j, HolomorphicFnOn O (partialDeriv j u)) ∧
    ∀ l l' : List (Fin n), l.Perm l' → ∀ z ∈ O, iteratedPartial l u z = iteratedPartial l' u z
def LinCombPartialWellDefined (O : Set (Coordinates.ComplexCoordinates n)) (X : Type)
    [AddCommGroup X] [Module ℂ X] : Prop :=
  ∀ (b b' : ℕ) (v : Fin b → X) (v' : Fin b' → X) (u : Fin b → Coordinates.ComplexCoordinates n → ℂ)
    (u' : Fin b' → Coordinates.ComplexCoordinates n → ℂ),
    (∀ i, HolomorphicFnOn O (u i)) → (∀ i, HolomorphicFnOn O (u' i)) →
    (∀ z ∈ O, linComb u' v' z = linComb u v z) →
    ∀ (q : Fin n → ℕ), ∀ z ∈ O, linCombPartial q u' v' z = linCombPartial q u v z
def ComplexLinCombPartials (O : Set (Coordinates.ComplexCoordinates n)) : Prop :=
  ∀ (b : ℕ) (v : Fin b → ℂ) (u : Fin b → Coordinates.ComplexCoordinates n → ℂ),
    (∀ i, HolomorphicFnOn O (u i)) →
      HolomorphicFnOn O (linComb u v) ∧
      ∀ (q : Fin n → ℕ), ∀ z ∈ O,
        linCombPartial q u v z = multiPartial q (linComb u v) z
def CauchyEstimate (O : Set (Coordinates.ComplexCoordinates n)) {X : Type} [AddCommGroup X]
    [Module ℂ X] (p : Seminorm ℂ X) : Prop :=
  ∀ (b : ℕ) (v : Fin b → X) (u : Fin b → Coordinates.ComplexCoordinates n → ℂ),
    (∀ i, HolomorphicFnOn O (u i)) →
    ∀ (ρ : Fin n → ℝ) (c : ℝ), (∀ j, 0 < ρ j) → 0 ≤ c →
      (∀ a : Coordinates.ComplexCoordinates n, openPolydisc ρ a ⊆ O →
        (∀ z ∈ openPolydisc ρ a, p (linComb u v z) ≤ c) →
        ∀ q : Fin n → ℕ, p (linCombPartial q u v a) ≤
          c * ∏ j, ((q j)! : ℝ) * ρ j ^ (-(q j : ℤ))) ∧
      ∀ a a' : Coordinates.ComplexCoordinates n,
        (∀ s : ℝ, s ∈ Icc (0 : ℝ) 1 → openPolydisc ρ (a + (s : ℂ) • (a' - a)) ⊆ O ∧
          ∀ z ∈ openPolydisc ρ (a + (s : ℂ) • (a' - a)), p (linComb u v z) ≤ c) →
        p (linComb u v a' - linComb u v a) ≤ c * ∑ j, ‖a' j - a j‖ / ρ j
def WeierstrassLimit (O : Set (Coordinates.ComplexCoordinates n)) : Prop :=
  (∀ (u : ℕ → Coordinates.ComplexCoordinates n → ℂ) (w : Coordinates.ComplexCoordinates n → ℂ),
    (∀ i, HolomorphicFnOn O (u i)) →
    (∀ z ∈ O, ∃ O' : Set (Coordinates.ComplexCoordinates n), IsOpen O' ∧ z ∈ O' ∧ O' ⊆ O ∧
      TendstoUniformlyOn u w atTop O') →
    HolomorphicFnOn O w) ∧
  ∀ (H : Type) [Countable H] (u : H → Coordinates.ComplexCoordinates n → ℂ),
    (∀ y, HolomorphicFnOn O (u y)) →
    (∀ z ∈ O, ∃ O' : Set (Coordinates.ComplexCoordinates n), IsOpen O' ∧ z ∈ O' ∧ O' ⊆ O ∧
      ∑' y, ⨆ x ∈ O', ENNReal.ofReal ‖u y x‖ < ∞) →
    (∀ z ∈ O, Summable fun y => ‖u y z‖) ∧ HolomorphicFnOn O fun z => ∑' y, u y z
end Partials
def entryIntegrand {I I' : PeriodicData} (M : (Fin 4 → ℂ) → QuotHom I I') (x : I'.Carrier)
    (y : I.Carrier) : InfiniteLattice.AmbientSpace → ℂ :=
  fun κ => carrierEntry (M (toComplexVec κ)) x y *
    Complex.exp (-Complex.I * bilinDot (toComplexVec κ) (toComplexVec (I.pos y - I'.pos x)))
def EntryIntegrandFacts (I I' : PeriodicData) : Prop :=
  ∀ M : (Fin 4 → ℂ) → QuotHom I I', QuotHomFamilyContinuousOn (n := 4) realDualPoints M →
    ∀ (x : I'.Carrier) (y : I.Carrier),
      Continuous (entryIntegrand M x y) ∧
      MeasureTheory.IntegrableOn (entryIntegrand M x y)
        (Icc (fun _ : Fin 4 => -Real.pi) fun _ => Real.pi)
def Claim : Prop :=
  (∀ I I' I'' : PeriodicData, IsPeriodic I → IsPeriodic I' → IsPeriodic I'' →
    EntryFormulas I I' I'') ∧
  (∀ I I' : PeriodicData, IsPeriodic I → IsPeriodic I' →
    OfEntriesSpec I I' ∧ EntryIntegrandFacts I I') ∧
  (∀ I : PeriodicData, IsPeriodic I →
    SymbolOnRealPoints I ∧ QuotHomDetFacts I ∧
      QuotHomFamilyInvOnDual I ∧
      ∀ n : ℕ, 1 ≤ n → QuotHomFamilyDetInv n I) ∧
  EmptyMatrixFacts ∧
  (∀ N : ℕ, MatrixDetFacts N ∧
    ∀ n : ℕ, 1 ≤ n → MatrixFamilyDetInv n N) ∧
  ExpInvHolomorphic ∧
  (∀ (n : ℕ) (O : Set (Coordinates.ComplexCoordinates n)), 1 ≤ n → IsOpen O →
    (∀ b : ℕ, 1 ≤ b → HolomorphicTuples n b O) ∧
    (∀ I I' : PeriodicData, IsPeriodic I → IsPeriodic I' →
      EntrywiseHolomorphicContinuous (quotHomEntries (P := I) (Q := I')) O) ∧
    (∀ a b : ℕ, EntrywiseHolomorphicContinuous (matrixCoeffs (a := a) (b := b)) O) ∧
    EntrywiseHolomorphicContinuous endTracelessCoeffs O ∧
    (∀ I : PeriodicData, IsPeriodic I →
      EntrywiseHolomorphicContinuous (quotFnEntries (P := I)) O) ∧
    PolynomialHolomorphic n O ∧
    CoordPolyHolomorphic n ∧
    PartialsHolomorphicComm O ∧
    (∀ (X : Type) [AddCommGroup X] [Module ℂ X] (p : Seminorm ℂ X),
      LinCombPartialWellDefined O X ∧ CauchyEstimate O p) ∧
    ComplexLinCombPartials O ∧
    WeierstrassLimit O) ∧
  Countable (Fin 4 → ℤ) ∧ Infinite (Fin 4 → ℤ)
end EntriesDets
end PeriodicOperators
end YangMills.Construction
end
