import YangMills.Construction.PeriodicOperators.LocalOperatorFunctions
import YangMills.Construction.PeriodicOperators.SymbolMatricesAndPlaneWaves
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal
noncomputable section
namespace YangMills.Construction
namespace PeriodicOperators
section LinearMapEntries
variable {J J' : Type}
open Classical in
def linearMapEntry (M : (J → ℂ) →ₗ[ℂ] (J' → ℂ)) : J' → J → ℂ :=
  fun b a => M (Pi.single a 1) b
def linearMapOfEntries (K : J' → J → ℂ) : (J → ℂ) →ₗ[ℂ] (J' → ℂ) :=
  Classical.epsilon fun M => linearMapEntry M = K
end LinearMapEntries
abbrev QuotHom (X Y : PeriodicData) : Type := (X.UnitQuot → ℂ) →ₗ[ℂ] (Y.UnitQuot → ℂ)
def quotHomNorm {X Y : PeriodicData} (M : QuotHom X Y) : ℝ≥0∞ :=
  wOpNorm (X.quotWeight 1) (Y.quotWeight 1) univ fun f => M f
def quotHomTranspose {X Y : PeriodicData} (M : QuotHom X Y) : QuotHom Y X :=
  linearMapOfEntries (wTranspose (X.quotWeight 1) (Y.quotWeight 1) (linearMapEntry M))
def quotHomInverse {X : PeriodicData} (M : QuotHom X X) : QuotHom X X :=
  Ring.inverse (M : Module.End ℂ (X.UnitQuot → ℂ))
def symbolHom (X Y : PeriodicData) (K : Y.Carrier → X.Carrier → ℂ) (k : Fin 4 → ℂ) : QuotHom X Y :=
  linearMapOfEntries (descendMatrix X Y 1 (fourierSymbol X Y K k))
def stripAddShift (r : ℝ) (q : Fin 4 → ℂ) : Set (Fin 4 → ℂ) :=
  {k | k ∈ imStrip (2 * r) ∧ k + q ∈ imStrip (2 * r)}
def stripSubShift (r : ℝ) (q : Fin 4 → ℂ) : Set (Fin 4 → ℂ) :=
  {k | k ∈ imStrip (2 * r) ∧ k - q ∈ imStrip (2 * r)}
abbrev realDualPoints : Set (Fin 4 → ℂ) := Coordinates.ComplexCoordinates.realLocus 4
section Regularity
variable {X Y : PeriodicData}
def IsHolomorphicNbhd (D : Set (Fin 4 → ℂ)) (A : (Fin 4 → ℂ) → QuotHom X Y) : Prop :=
  ∃ U : Set (Fin 4 → ℂ), IsOpen U ∧ D ⊆ U ∧ ∀ b a,
    Coordinates.ComplexCoordinates.IsHolomorphicIn (N' := 1) U fun k _ => linearMapEntry (A k) b a
def IsQuasiPeriodic (D : Set (Fin 4 → ℂ)) (A : (Fin 4 → ℂ) → QuotHom X Y) : Prop :=
  ∀ (n : Fin 4 → ℤ), ∀ k ∈ D,
    A (addTwoPiInt k n) =
      (quotHomInverse (phaseMul Y n)).comp ((A k).comp (phaseMul X n))
end Regularity
@[ext] structure JetQuad (X Y : PeriodicData) where
  f00 : (Fin 4 → ℂ) → QuotHom X Y
  f10 : (Fin 4 → ℂ) → QuotHom X Y
  f01 : (Fin 4 → ℂ) → QuotHom X Y
  f11 : (Fin 4 → ℂ) → QuotHom X Y
namespace JetQuad
variable {X Y Z : PeriodicData}
structure IsJet (r : ℝ) (q : Fin 4 → ℂ) (A : JetQuad X Y) : Prop where
  pos_width : 0 < r
  mem_imStrip : q ∈ imStrip r
  holo_f00 : IsHolomorphicNbhd (imStrip (2 * r)) A.f00
  holo_f10 : IsHolomorphicNbhd (stripAddShift r q) A.f10
  holo_f01 : IsHolomorphicNbhd (stripSubShift r q) A.f01
  holo_f11 : IsHolomorphicNbhd realDualPoints A.f11
  quasiPeriodic_f00 : IsQuasiPeriodic (imStrip (2 * r)) A.f00
  quasiPeriodic_f10 : IsQuasiPeriodic (stripAddShift r q) A.f10
  quasiPeriodic_f01 : IsQuasiPeriodic (stripSubShift r q) A.f01
  quasiPeriodic_f11 : IsQuasiPeriodic realDualPoints A.f11
def EqAsJet (r : ℝ) (q : Fin 4 → ℂ) (A B : JetQuad X Y) : Prop :=
  EqOn A.f00 B.f00 (imStrip (2 * r)) ∧ EqOn A.f10 B.f10 (stripAddShift r q) ∧
    EqOn A.f01 B.f01 (stripSubShift r q) ∧ EqOn A.f11 B.f11 realDualPoints
def jetNorm (r : ℝ) (q : Fin 4 → ℂ) (A : JetQuad X Y) : ℝ≥0∞ :=
  (⨆ k ∈ imStrip (2 * r), quotHomNorm (A.f00 k)) + (⨆ k ∈ stripAddShift r q, quotHomNorm (A.f10 k)) +
    (⨆ k ∈ stripSubShift r q, quotHomNorm (A.f01 k)) + ⨆ k ∈ realDualPoints, quotHomNorm (A.f11 k)
def add (A B : JetQuad X Y) : JetQuad X Y :=
  ⟨A.f00 + B.f00, A.f10 + B.f10, A.f01 + B.f01, A.f11 + B.f11⟩
def smul (c : ℂ) (A : JetQuad X Y) : JetQuad X Y :=
  ⟨c • A.f00, c • A.f10, c • A.f01, c • A.f11⟩
def mul (q : Fin 4 → ℂ) (A : JetQuad X Y) (B : JetQuad Z X) : JetQuad Z Y where
  f00 := fun k => (A.f00 k).comp (B.f00 k)
  f10 := fun k => (A.f10 k).comp (B.f00 k) + (A.f00 (k + q)).comp (B.f10 k)
  f01 := fun k => (A.f01 k).comp (B.f00 k) + (A.f00 (k - q)).comp (B.f01 k)
  f11 := fun k => (A.f11 k).comp (B.f00 k) + (A.f00 k).comp (B.f11 k) +
    (A.f10 (k - q)).comp (B.f01 k) + (A.f01 (k + q)).comp (B.f10 k)
def transposeAt (q : Fin 4 → ℂ) (A : JetQuad X Y) : JetQuad Y X where
  f00 := fun k => quotHomTranspose (A.f00 (-k))
  f10 := fun k => quotHomTranspose (A.f10 (-k - q))
  f01 := fun k => quotHomTranspose (A.f01 (-k + q))
  f11 := fun k => quotHomTranspose (A.f11 (-k))
def ofKernel (X Y : PeriodicData) (K : Y.Carrier → X.Carrier → ℂ) : JetQuad X Y :=
  ⟨symbolHom X Y K, 0, 0, 0⟩
def one (X : PeriodicData) : JetQuad X X :=
  ⟨fun _ => LinearMap.id, 0, 0, 0⟩
def traceNumber (A : JetQuad X X) : ℂ :=
  torusAverage fun k => LinearMap.trace ℂ (X.UnitQuot → ℂ) (A.f11 (toComplexVec k))
structure IsInvertibleJet (r : ℝ) (q : Fin 4 → ℂ) (A : JetQuad X X) : Prop where
  isJet : IsJet r q A
  isUnit_f00 : ∀ k ∈ imStrip (2 * r), IsUnit (A.f00 k : Module.End ℂ (X.UnitQuot → ℂ))
  bdd_inverse : (⨆ k ∈ imStrip (2 * r), quotHomNorm (quotHomInverse (A.f00 k))) < ⊤
def zeroPart (A : JetQuad X Y) : JetQuad X Y :=
  ⟨A.f00, 0, 0, 0⟩
def zeroPartInv (A : JetQuad X X) : JetQuad X X :=
  ⟨fun k => quotHomInverse (A.f00 k), 0, 0, 0⟩
def normalize (q : Fin 4 → ℂ) (A : JetQuad X X) : JetQuad X X :=
  add (mul q (zeroPartInv A) A) (smul (-1) (one X))
def logSeries (q : Fin 4 → ℂ) (A : JetQuad X X) : JetQuad X X :=
  add (normalize q A) (smul (-(1 / 2)) (mul q (normalize q A) (normalize q A)))
def logNumber (q : Fin 4 → ℂ) (A : JetQuad X X) : ℂ :=
  traceNumber (logSeries q A)
def NormalizeWellFormed (r : ℝ) (q : Fin 4 → ℂ) (A : JetQuad X X) : Prop :=
  IsJet r q (zeroPartInv A) ∧ IsJet r q (mul q (zeroPartInv A) A) ∧
    IsJet r q (one X)
def LogNumberWellFormed (r : ℝ) (q : Fin 4 → ℂ) (A : JetQuad X X) : Prop :=
  NormalizeWellFormed r q A ∧ IsJet r q (normalize q A) ∧
    IsJet r q (mul q (normalize q A) (normalize q A)) ∧ IsJet r q (logSeries q A)
end JetQuad
section JetAlong
variable (W X Y : PeriodicData)
def IsActionTriple (K : (W.Carrier → ℂ) → Y.Carrier → X.Carrier → ℂ) (q : Fin 4 → ℂ)
    (vPlus vMinus : W.UnitQuot → ℂ)
    (A : ((Fin 4 → ℂ) → QuotHom X Y) × ((Fin 4 → ℂ) → QuotHom X Y) ×
      ((Fin 4 → ℂ) → QuotHom X Y)) : Prop :=
  ∀ (k : Fin 4 → ℂ) (u : X.UnitQuot → ℂ) (y : Y.Carrier),
    applyKernel (coeffOne W X Y K (blochWave W q vPlus)) (blochWave X k u) y =
        blochWave Y (k + q) (A.1 k u) y ∧
      applyKernel (coeffOne W X Y K (blochWave W (-q) vMinus)) (blochWave X k u) y =
        blochWave Y (k - q) (A.2.1 k u) y ∧
      applyKernel (coeffTwo W X Y K (blochWave W q vPlus) (blochWave W (-q) vMinus))
          (blochWave X k u) y =
        blochWave Y k (A.2.2 k u) y
def ActionTripleUnique (K : (W.Carrier → ℂ) → Y.Carrier → X.Carrier → ℂ) (q : Fin 4 → ℂ)
    (vPlus vMinus : W.UnitQuot → ℂ) : Prop :=
  ∃! A, IsActionTriple W X Y K q vPlus vMinus A
def jetAlong (K : (W.Carrier → ℂ) → Y.Carrier → X.Carrier → ℂ) (q : Fin 4 → ℂ)
    (vPlus vMinus : W.UnitQuot → ℂ) : JetQuad X Y :=
  ⟨symbolHom X Y (coeffZero W X Y K),
    (Classical.epsilon (IsActionTriple W X Y K q vPlus vMinus)).1,
    (Classical.epsilon (IsActionTriple W X Y K q vPlus vMinus)).2.1,
    (Classical.epsilon (IsActionTriple W X Y K q vPlus vMinus)).2.2⟩
end JetAlong
end PeriodicOperators
end YangMills.Construction
end
