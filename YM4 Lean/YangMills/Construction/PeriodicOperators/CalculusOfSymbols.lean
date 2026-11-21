import YangMills.Construction.PeriodicOperators.CovariantKernelsOfFiniteRange
import YangMills.Construction.PeriodicOperators.KernelOfAMatrixFunction
import YangMills.Construction.PeriodicOperators.QuotientsTransposesAndNorm
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.PeriodicOperators
namespace SymbolCalculus
open Quotients (conjKernel)
open YangMills.Construction.TorusMetric (l1NormVec)
variable (P Q R : PeriodicData)
def HasSymbolOn (K : Q.Carrier → P.Carrier → ℂ) (F : (Fin 4 → ℂ) → QuotHom P Q)
    (U : Set (Fin 4 → ℂ)) : Prop :=
  SymbolSummableOn P Q K U ∧ ∀ z ∈ U, symbolHom P Q K z = F z
def CompSummablePeriodic (K : Q.Carrier → P.Carrier → ℂ) (L : P.Carrier → R.Carrier → ℂ) : Prop :=
  (∀ a c, CompSummableAt K L a c) ∧ IsPeriodicKernel R Q (compKernel K L)
def FiniteRangeSymbolEntire : Prop :=
  ∀ K : Q.Carrier → P.Carrier → ℂ, IsPeriodicKernel P Q K → IsFiniteRange P Q K →
    FourierSymbolIsEntire P Q K
def CompPeriodic : Prop :=
  ∀ (K : Q.Carrier → P.Carrier → ℂ) (L : P.Carrier → R.Carrier → ℂ),
    IsPeriodicKernel P Q K → IsPeriodicKernel R P L → CompSummablePeriodic P Q R K L
def TransposePeriodic : Prop :=
  ∀ K : Q.Carrier → P.Carrier → ℂ, IsPeriodicKernel P Q K →
    (∀ b a, kernelTranspose P Q K b a =
      ((Q.weightOf a * (P.weightOf b)⁻¹ : ℝ) : ℂ) * K a b) ∧
      IsPeriodicKernel Q P (kernelTranspose P Q K)
def RealKernelSymbol : Prop :=
  ∀ K : Q.Carrier → P.Carrier → ℂ, IsPeriodicKernel P Q K → (∀ a b, (K a b).im = 0) →
    ∀ z : Fin 4 → ℂ, SymbolSummableAt P Q K z →
      SymbolSummableAt P Q K (-star z) ∧
        FactorsThroughQuot (fourierSymbol P Q K z) ∧
        FactorsThroughQuot (fourierSymbol P Q K (-star z)) ∧
        conjKernel (linearMapEntry (symbolHom P Q K z)) =
          linearMapEntry (symbolHom P Q K (-star z))
def PhaseMulDiagonalUnitary : Prop :=
  ∀ m : Fin 4 → ℤ,
    (∀ x y, P.mkQuot 1 x = P.mkQuot 1 y →
      Complex.exp (2 * Real.pi * Complex.I *
          bilinDot (toComplexVec (castVec m)) (toComplexVec (P.pos x))) =
        Complex.exp (2 * Real.pi * Complex.I *
          bilinDot (toComplexVec (castVec m)) (toComplexVec (P.pos y)))) ∧
    (∀ p q : P.UnitQuot, p ≠ q → linearMapEntry (phaseMul P m) p q = 0) ∧
    (∀ u v : P.UnitQuot → ℂ,
      wInner (P.quotWeight 1) (phaseMul P m u) (phaseMul P m v) =
        wInner (P.quotWeight 1) u v) ∧
    ∀ u : P.UnitQuot → ℂ,
      wNorm (P.quotWeight 1) (phaseMul P m u) =
        wNorm (P.quotWeight 1) u
def SymbolNormPeriodic : Prop :=
  ∀ K : Q.Carrier → P.Carrier → ℂ, IsPeriodicKernel P Q K →
    ∀ (z : Fin 4 → ℂ) (m : Fin 4 → ℤ), SymbolSummableAt P Q K z →
      SymbolSummableAt P Q K (addTwoPiInt z m) ∧
        quotHomNorm (symbolHom P Q K (addTwoPiInt z m)) = quotHomNorm (symbolHom P Q K z)
def IsSidePeriodic (N : ℕ) (u : P.Carrier → ℂ) : Prop :=
  ∀ (m : Fin 4 → ℤ) x, u (P.translate (N • m) x) = u x
structure TorusProperties (N : ℕ) (K : Q.Carrier → P.Carrier → ℂ) : Prop where
  summable : ∀ a b, PeriodizationSummableAt P Q K N a b
  eq_of_mkQuot_eq : ∀ a₁ a₂ b₁ b₂,
    Q.mkQuot N a₁ = Q.mkQuot N a₂ → P.mkQuot N b₁ = P.mkQuot N b₂ →
      periodization P Q K N a₁ b₁ = periodization P Q K N a₂ b₂
  apply_summable : ∀ u : P.Carrier → ℂ, (∃ B : ℝ, ∀ x, ‖u x‖ ≤ B) →
    IsSidePeriodic P N u → ∀ a, ApplySummableAt K u a
  apply_sidePeriodic : ∀ u : P.Carrier → ℂ, (∃ B : ℝ, ∀ x, ‖u x‖ ≤ B) →
    IsSidePeriodic P N u → IsSidePeriodic Q N (applyKernel K u)
  periodicMatrix_apply : ∀ u : P.Carrier → ℂ, (∃ B : ℝ, ∀ x, ‖u x‖ ≤ B) →
    IsSidePeriodic P N u → ∀ v : P.QuotMod N → ℂ,
      (∀ x, v (P.mkQuot N x) = u x) → ∀ a,
        applyKernel (periodicMatrix P Q K N) v (Q.mkQuot N a) = applyKernel K u a
  comp : ∀ R : PeriodicData, IsPeriodic R → ∀ L : P.Carrier → R.Carrier → ℂ,
    IsPeriodicKernel R P L →
      periodicMatrix R Q (compKernel K L) N =
        compKernel (periodicMatrix P Q K N) (periodicMatrix R P L N)
  transpose : periodicMatrix Q P (kernelTranspose P Q K) N =
    wTranspose (P.quotWeight N) (Q.quotWeight N) (periodicMatrix P Q K N)
  im_eq_zero : (∀ a b, (K a b).im = 0) → ∀ p q, (periodicMatrix P Q K N p q).im = 0
  linComb : ∀ K' : Q.Carrier → P.Carrier → ℂ, IsPeriodicKernel P Q K' → ∀ α β : ℂ,
    IsPeriodicKernel P Q (kernelLinComb α β K K') ∧
      ∀ a b, periodization P Q (kernelLinComb α β K K') N a b =
        α * periodization P Q K N a b + β * periodization P Q K' N a b
open Classical in
def PeriodizationIdKernel (N : ℕ) : Prop :=
  ∀ a b, periodization P P (idKernel P) N a b =
    if P.mkQuot N a = P.mkQuot N b then 1 else 0
def IsStripSymbol (r : ℝ) (F : (Fin 4 → ℂ) → QuotHom P Q) : Prop :=
  IsHolomorphicNbhd (imStrip r) F ∧ QuotHomFamilyBoundedOn (imStrip r) F ∧ IsQuasiPeriodic (imStrip r) F
structure MatFunKernelProperties (r : ℝ) (F : (Fin 4 → ℂ) → QuotHom P Q) : Prop where
  realDualPoints_subset : realDualPoints ⊆ imStrip r ∧ QuotHomFamilyContinuousOn (n := 4) realDualPoints F
  isPeriodicKernel : IsPeriodicKernel P Q (matFunKernel P Q F) ∧
    HasSymbolOn P Q (matFunKernel P Q F) F realDualPoints
  unique : ∀ K : Q.Carrier → P.Carrier → ℂ, IsPeriodicKernel P Q K →
    HasSymbolOn P Q K F realDualPoints → K = matFunKernel P Q F
  norm_le : ∀ a b, ‖matFunKernel P Q F a b‖ ≤
    sSup ((fun z => ‖carrierEntry (F z) a b‖) '' imStrip r) *
      Real.exp (-r * l1NormVec (P.pos b - Q.pos a))
  summable_openImStrip : ∀ z ∈ openImStrip r,
    SymbolSummableAt P Q (matFunKernel P Q F) z ∧
      ∀ a b, fourierSymbol P Q (matFunKernel P Q F) z a b = carrierEntry (F z) a b
  im_eq_zero : (∀ z ∈ imStrip r, conjKernel (linearMapEntry (F z)) = linearMapEntry (F (-star z))) →
    ∀ a b, (matFunKernel P Q F a b).im = 0
def PeriodicInverseEq (r : ℝ) (F : (Fin 4 → ℂ) → QuotHom P P)
    (K : P.Carrier → P.Carrier → ℂ) : Prop :=
  HasSymbolOn P P K F realDualPoints →
  EventuallyNear IsOpen (imStrip r) (fun z => IsInvertibleQuotHom (F z)) →
  QuotHomFamilyBoundedOn (imStrip r) (fun z => quotHomInverse (F z)) →
    SymbolInvertibleOnReals P K ∧
      QuotHomFamilyContinuousOn (n := 4) realDualPoints (fun z => quotHomInverse (F z)) ∧
      periodicInverse P K = matFunKernel P P (fun z => quotHomInverse (F z)) ∧
      IsPeriodicKernel P P (periodicInverse P K) ∧
      (∀ a b, CompSummableAt (periodicInverse P K) K a b) ∧
      (∀ a b, CompSummableAt K (periodicInverse P K) a b) ∧
      compKernel (periodicInverse P K) K = idKernel P ∧
      compKernel K (periodicInverse P K) = idKernel P
def CompIdLaws : Prop :=
  ∀ K : Q.Carrier → P.Carrier → ℂ, IsPeriodicKernel P Q K →
    IsPeriodicKernel P P (idKernel P) ∧ IsPeriodicKernel Q Q (idKernel Q) ∧
      (∀ a b, CompSummableAt K (idKernel P) a b) ∧
      (∀ a b, CompSummableAt (idKernel Q) K a b) ∧
      compKernel K (idKernel P) = K ∧ compKernel (idKernel Q) K = K
def CompLinLaws : Prop :=
  ∀ (K K' : Q.Carrier → P.Carrier → ℂ) (L L' : P.Carrier → R.Carrier → ℂ) (α β : ℂ),
    IsPeriodicKernel P Q K → IsPeriodicKernel P Q K' →
    IsPeriodicKernel R P L → IsPeriodicKernel R P L' →
      IsPeriodicKernel P Q (kernelLinComb α β K K') ∧
      IsPeriodicKernel R P (kernelLinComb α β L L') ∧
      CompSummablePeriodic P Q R K L ∧ CompSummablePeriodic P Q R K' L ∧
      CompSummablePeriodic P Q R K L' ∧
      CompSummablePeriodic P Q R (kernelLinComb α β K K') L ∧
      CompSummablePeriodic P Q R K (kernelLinComb α β L L') ∧
      (∀ a c, compKernel (kernelLinComb α β K K') L a c =
        α * compKernel K L a c + β * compKernel K' L a c) ∧
      (∀ a c, compKernel K (kernelLinComb α β L L') a c =
        α * compKernel K L a c + β * compKernel K L' a c) ∧
      compKernel (kernelLinComb α β K K') L =
        kernelLinComb α β (compKernel K L) (compKernel K' L) ∧
      compKernel K (kernelLinComb α β L L') =
        kernelLinComb α β (compKernel K L) (compKernel K L') ∧
      compKernel (fun a b => α * K a b) L = (fun a c => α * compKernel K L a c) ∧
      compKernel K (fun b c => α * L b c) = (fun a c => α * compKernel K L a c)
def Claim : Prop :=
  ∀ P Q : PeriodicData, IsPeriodic P → IsPeriodic Q →
    FiniteRangeSymbolEntire P Q ∧
    TransposePeriodic P Q ∧
    RealKernelSymbol P Q ∧
    PhaseMulDiagonalUnitary P ∧
    SymbolNormPeriodic P Q ∧
    (∀ N : ℕ, 1 ≤ N → PeriodizationIdKernel P N ∧
      ∀ K : Q.Carrier → P.Carrier → ℂ, IsPeriodicKernel P Q K → TorusProperties P Q N K) ∧
    (∀ r : ℝ, 0 < r →
      (∀ m : Fin 4 → ℤ, IsInvertibleQuotHom (phaseMul P m : QuotHom P P)) ∧
      (∀ F : (Fin 4 → ℂ) → QuotHom P Q, IsStripSymbol P Q r F →
        MatFunKernelProperties P Q r F) ∧
      IsStripSymbol P Q r (fun _ => 0) ∧
      IsStripSymbol P P r (fun _ => linearMapOfEntries (quotOne P)) ∧
      ∀ F : (Fin 4 → ℂ) → QuotHom P P, IsStripSymbol P P r F →
        ∀ K : P.Carrier → P.Carrier → ℂ, IsPeriodicKernel P P K →
          PeriodicInverseEq P r F K) ∧
    CompIdLaws P Q ∧
    ∀ R : PeriodicData, IsPeriodic R →
      CompPeriodic P Q R ∧ CompLinLaws P Q R
end SymbolCalculus
end YangMills.Construction.PeriodicOperators
end
