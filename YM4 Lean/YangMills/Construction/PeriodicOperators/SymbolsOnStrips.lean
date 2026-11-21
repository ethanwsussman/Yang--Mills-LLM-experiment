import YangMills.Construction.PeriodicOperators.BracketedProducts
import YangMills.Construction.PeriodicOperators.CovariantKernelsOfFiniteRange
import YangMills.Construction.PeriodicOperators.KernelOfAMatrixFunction
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
namespace PeriodicOperators
namespace StripSymbols
abbrev openStripInterior (υ : ℝ) : Set (Fin 4 → ℂ) := interiorBy IsOpen (imStrip υ)
def InteriorOfStripChar (υ : ℝ) : Prop :=
  openStripInterior υ = openImStrip υ ∧ IsOpen (openImStrip υ) ∧
    openImStrip υ ⊆ imStrip υ ∧
    ∀ υ' : ℝ, 0 < υ' → υ' < υ → imStrip υ' ⊆ openImStrip υ
def linCombKernel {A B : Type} (a a' : ℂ) (K K' : B → A → ℂ) : B → A → ℂ :=
  fun y x => a * K y x + a' * K' y x
structure SymbolSummability (P P' : PeriodicData) : Prop where
  finiteRange : ∀ K : P'.Carrier → P.Carrier → ℂ, IsPeriodicKernel P P' K → IsFiniteRange P P' K →
    SymbolSummableOn P P' K univ
  identity : ∀ z : Fin 4 → ℂ, SymbolSummableAt P P (idKernel P) z ∧
    quotSymbol P P (idKernel P) z = quotOne P
  decay : ∀ (υ : ℝ), 0 < υ → ∀ (C : ℝ) (K : P'.Carrier → P.Carrier → ℂ), IsPeriodicKernel P P' K →
    (∀ y x, ‖K y x‖ ≤ C * Real.exp (-υ * TorusMetric.l1NormVec (P'.pos y - P.pos x))) →
      SymbolSummableOn P P' K (openStripInterior υ) ∧
        QuotHomFamilyHolomorphicOn (n := 4) (openStripInterior υ) (symbolHom P P' K)
structure PointwiseCalculus (P P' : PeriodicData) (K : P'.Carrier → P.Carrier → ℂ) (z : Fin 4 → ℂ) : Prop where
  summableAt_of_imVec_eq : ∀ z' : Fin 4 → ℂ, imVec z' = imVec z →
    SymbolSummableAt P P' K z'
  factorsThroughQuot : FactorsThroughQuot (P := P) (Q := P') (fourierSymbol P P' K z)
  carrierEntry_symbolHom : ∀ y x, carrierEntry (symbolHom P P' K z) y x = fourierSymbol P P' K z y x
  symbolHom_addTwoPiInt : ∀ n : Fin 4 → ℤ, symbolHom P P' K (addTwoPiInt z n) =
    (quotHomInverse (phaseMul P' n)).comp
      ((symbolHom P P' K z).comp (phaseMul P n))
  norm_symbolHom_addTwoPiInt : ∀ n : Fin 4 → ℤ,
    quotHomNorm (symbolHom P P' K (addTwoPiInt z n)) = quotHomNorm (symbolHom P P' K z)
  transpose : IsPeriodicKernel P' P (kernelTranspose P P' K) ∧
    SymbolSummableAt P' P (kernelTranspose P P' K) (-z) ∧
    quotSymbol P' P (kernelTranspose P P' K) (-z) = quotTranspose P P' (quotSymbol P P' K z)
  linComb : ∀ K' : P'.Carrier → P.Carrier → ℂ, IsPeriodicKernel P P' K' →
    SymbolSummableAt P P' K' z → ∀ a a' : ℂ,
      IsPeriodicKernel P P' (linCombKernel a a' K K') ∧
        SymbolSummableAt P P' (linCombKernel a a' K K') z ∧
        symbolHom P P' (linCombKernel a a' K K') z =
          a • symbolHom P P' K z + a' • symbolHom P P' K' z
  comp : ∀ (Q : PeriodicData), IsPeriodic Q → ∀ L : P.Carrier → Q.Carrier → ℂ,
    IsPeriodicKernel Q P L → SymbolSummableAt Q P L z →
      (∀ y w, CompSummableAt K L y w) ∧ IsPeriodicKernel Q P' (compKernel K L) ∧
        SymbolSummableAt Q P' (compKernel K L) z ∧
        symbolHom Q P' (compKernel K L) z =
          (symbolHom P P' K z).comp (symbolHom Q P L z)
def chainProd {m : ℕ} (D : Fin (m + 1) → PeriodicData)
    (A : (i : Fin m) → QuotHom (D i.succ) (D i.castSucc)) :
    (j : ℕ) → (hj : j < m + 1) → QuotHom (D ⟨j, hj⟩) (D 0)
  | 0, _ => LinearMap.id
  | j + 1, hj =>
    (chainProd D A j (Nat.lt_of_succ_lt hj)).comp (A ⟨j, Nat.lt_of_succ_lt_succ hj⟩)
structure BracketingsAgree {m : ℕ} (D : Fin (m + 1) → PeriodicData)
    (G : (i : Fin m) → (D i.castSucc).Carrier → (D i.succ).Carrier → ℂ) : Prop where
  periodic : ∀ K, IsBracketing D G 0 (Fin.last m) K →
    IsPeriodicKernel (D (Fin.last m)) (D 0) K
  exists_bracketing : ∃ K, IsBracketing D G 0 (Fin.last m) K
  unique : ∀ K K', IsBracketing D G 0 (Fin.last m) K →
    IsBracketing D G 0 (Fin.last m) K' → K = K'
  symbol : ∀ z : Fin 4 → ℂ, (∀ i, SymbolSummableAt (D i.succ) (D i.castSucc) (G i) z) →
    ∀ K, IsBracketing D G 0 (Fin.last m) K →
      SymbolSummableAt (D (Fin.last m)) (D 0) K z ∧
        symbolHom (D (Fin.last m)) (D 0) K z =
          chainProd D (fun i => symbolHom (D i.succ) (D i.castSucc) (G i) z) m
            (Nat.lt_succ_self m)
def HolomorphicMatFunKernel (P P' : PeriodicData) (υ : ℝ) : Prop :=
  ∀ M : (Fin 4 → ℂ) → QuotHom P P', QuotHomFamilyHolomorphicOn (n := 4) (openStripInterior υ) M →
    (∀ υ' : ℝ, 0 < υ' → υ' < υ → QuotHomFamilyBoundedOn (imStrip υ') M) →
    IsQuasiPeriodic (openStripInterior υ) M →
      realDualPoints ⊆ openStripInterior υ ∧ QuotHomFamilyContinuousOn (n := 4) (openStripInterior υ) M ∧
        QuotHomFamilyContinuousOn (n := 4) realDualPoints M ∧
        IsPeriodicKernel P P' (matFunKernel P P' M) ∧
        SymbolSummableOn P P' (matFunKernel P P' M) (openStripInterior υ) ∧
        ∀ z ∈ openStripInterior υ, symbolHom P P' (matFunKernel P P' M) z = M z
def PeriodicInverseSpec (P : PeriodicData) (υ : ℝ) : Prop :=
  ∀ K : P.Carrier → P.Carrier → ℂ, IsPeriodicKernel P P K →
    SymbolSummableOn P P K (openStripInterior υ) →
    QuotHomFamilyHolomorphicOn (n := 4) (openStripInterior υ) (symbolHom P P K) →
    (∀ z ∈ openStripInterior υ, IsInvertibleQuotHom (symbolHom P P K z)) →
      SymbolInvertibleOnReals P K ∧
        IsPeriodicKernel P P (periodicInverse P K) ∧
        (∀ y x, CompSummableAt (periodicInverse P K) K y x) ∧
        (∀ y x, CompSummableAt K (periodicInverse P K) y x) ∧
        compKernel (periodicInverse P K) K = idKernel P ∧
        compKernel K (periodicInverse P K) = idKernel P ∧
        SymbolSummableOn P P (periodicInverse P K) (openStripInterior υ) ∧
        ∀ z ∈ openStripInterior υ, symbolHom P P (periodicInverse P K) z =
          quotHomInverse (symbolHom P P K z)
def CompKernelAssoc (P P' Q Q' : PeriodicData) : Prop :=
  ∀ (K : P'.Carrier → P.Carrier → ℂ) (L : P.Carrier → Q.Carrier → ℂ) (L' : Q.Carrier → Q'.Carrier → ℂ),
    IsPeriodicKernel P P' K → IsPeriodicKernel Q P L → IsPeriodicKernel Q' Q L' →
      (∀ y w, CompSummableAt K L y w) ∧ IsPeriodicKernel Q P' (compKernel K L) ∧
        (∀ x v, CompSummableAt L L' x v) ∧
        IsPeriodicKernel Q' P (compKernel L L') ∧
        (∀ y v, CompSummableAt (compKernel K L) L' y v) ∧
        IsPeriodicKernel Q' P' (compKernel (compKernel K L) L') ∧
        (∀ y v, CompSummableAt K (compKernel L L') y v) ∧
        IsPeriodicKernel Q' P' (compKernel K (compKernel L L')) ∧
        compKernel (compKernel K L) L' = compKernel K (compKernel L L')
def Claim : Prop :=
  (∀ υ : ℝ, 0 < υ → InteriorOfStripChar υ) ∧
  (∀ P P' : PeriodicData, IsPeriodic P → IsPeriodic P' →
    SymbolSummability P P' ∧
    (∀ (K : P'.Carrier → P.Carrier → ℂ) (z : Fin 4 → ℂ), IsPeriodicKernel P P' K →
      SymbolSummableAt P P' K z → PointwiseCalculus P P' K z) ∧
    (∀ υ : ℝ, 0 < υ → HolomorphicMatFunKernel P P' υ) ∧
    ∀ Q Q' : PeriodicData, IsPeriodic Q → IsPeriodic Q' →
      CompKernelAssoc P P' Q Q') ∧
  (∀ (m : ℕ), 1 ≤ m → ∀ (D : Fin (m + 1) → PeriodicData)
    (G : (i : Fin m) → (D i.castSucc).Carrier → (D i.succ).Carrier → ℂ),
      (∀ i, IsPeriodic (D i)) →
      (∀ i, IsPeriodicKernel (D i.succ) (D i.castSucc) (G i)) →
        BracketingsAgree D G) ∧
  ∀ P : PeriodicData, IsPeriodic P → ∀ υ : ℝ, 0 < υ → PeriodicInverseSpec P υ
end StripSymbols
end PeriodicOperators
end YangMills.Construction
end
