import YangMills.Construction.PeriodicOperators.RiemannSumsAndShifts
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.PeriodicOperators
open YangMills.Construction.InfiniteLattice (AmbientSpace)
open YangMills.Construction.TorusMetric (euclidNormVec)
open YangMills.Construction.PeriodicOperators.RiemannSums (DualClasses)
def imVec (κ : Fin 4 → ℂ) : AmbientSpace := fun μ => (κ μ).im
def strictImStrip (r : ℝ) : Set (Fin 4 → ℂ) := {κ | euclidNormVec (imVec κ) < r}
def addTwoPiInt (κ : Fin 4 → ℂ) (e : Fin 4 → ℤ) : Fin 4 → ℂ :=
  fun μ => κ μ + 2 * Real.pi * (e μ : ℂ)
def addIVec (κ : Fin 4 → ℂ) (θ : AmbientSpace) : Fin 4 → ℂ :=
  fun μ => κ μ + Complex.I * (θ μ : ℂ)
def wInner {J : Type} (w : J → ℝ) (f g : J → ℂ) : ℂ :=
  wPairing w (fun i => starRingEnd ℂ (f i)) g
def blochWave (P : PeriodicData) (κ : Fin 4 → ℂ) (φ : P.UnitQuot → ℂ) : P.Carrier → ℂ :=
  fun x => Complex.exp (Complex.I * bilinDot κ (toComplexVec (P.pos x))) * φ (P.mkQuot 1 x)
def blochWaveSubspace (P : PeriodicData) (n : ℕ) (κ : AmbientSpace) :
    Submodule ℂ (P.QuotMod n → ℂ) where
  carrier := {g | ∃ φ : P.UnitQuot → ℂ, ∀ x, g (P.mkQuot n x) = blochWave P (toComplexVec κ) φ x}
  add_mem' := by
    rintro g g' ⟨φ, hg⟩ ⟨φ', hg'⟩
    refine ⟨φ + φ', fun x => ?_⟩
    simp only [Pi.add_apply, hg, hg', blochWave, mul_add]
  zero_mem' := ⟨0, fun x => by simp [blochWave]⟩
  smul_mem' := by
    rintro c g ⟨φ, hg⟩
    refine ⟨c • φ, fun x => ?_⟩
    simp only [Pi.smul_apply, smul_eq_mul, hg, blochWave]
    ring
def IsDualSection (n : ℕ) (σ : DualClasses n → dualLattice n) : Prop :=
  ∀ q, (QuotientAddGroup.mk (σ q) : DualClasses n) = q
section KernelsAndMatrices
variable (P Q : PeriodicData)
def quotSymbol (K : Q.Carrier → P.Carrier → ℂ) (κ : Fin 4 → ℂ) : Q.UnitQuot → P.UnitQuot → ℂ :=
  descendMatrix P Q 1 (fourierSymbol P Q K κ)
def periodicMatrix (K : Q.Carrier → P.Carrier → ℂ) (n : ℕ) : Q.QuotMod n → P.QuotMod n → ℂ :=
  descendMatrix P Q n (periodization P Q K n)
def kernelTranspose (K : Q.Carrier → P.Carrier → ℂ) : P.Carrier → Q.Carrier → ℂ :=
  wTranspose P.weightOf Q.weightOf K
def quotTranspose (A : Q.UnitQuot → P.UnitQuot → ℂ) : P.UnitQuot → Q.UnitQuot → ℂ :=
  wTranspose (P.quotWeight 1) (Q.quotWeight 1) A
def expConj (θ : AmbientSpace) (K : Q.Carrier → P.Carrier → ℂ) : Q.Carrier → P.Carrier → ℂ :=
  fun y x =>
    Complex.exp (bilinDot (toComplexVec θ) (toComplexVec (Q.pos y - P.pos x))) * K y x
def normSummableSet : Set (P.Carrier → ℂ) := {f | NormSummable P.weightOf f}
def kernelOpNorm (K : Q.Carrier → P.Carrier → ℂ) : ℝ≥0∞ :=
  wOpNorm P.weightOf Q.weightOf (normSummableSet P) (applyKernel K)
def quotOpNorm (A : Q.UnitQuot → P.UnitQuot → ℂ) : ℝ≥0∞ :=
  wOpNorm (P.quotWeight 1) (Q.quotWeight 1) univ (applyKernel A)
end KernelsAndMatrices
end YangMills.Construction.PeriodicOperators
end
