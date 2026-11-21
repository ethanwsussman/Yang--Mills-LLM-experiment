import YangMills.Construction.SpectralMeasures.SpectralTheoremOfASelfAdjointOperator
import Mathlib
set_option autoImplicit false
open scoped NNReal
noncomputable section
namespace YangMills.Construction.EuclideanBorel
open YangMills.Construction.FormsOperators (IsSelfAdj Commutes)
open YangMills.Construction.SpectralTheory (UnboundedOp)
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
def liftFromLine (g : ℝ → ℂ) : Space 1 → ℂ :=
  fun y => g (y 0)
def borelCalculus (A : UnboundedOp H) (g : ℝ → ℂ) :
    sqIntegrableDomain (spectralResolution A) (liftFromLine g) → H :=
  spectralIntegral (spectralResolution A) (liftFromLine g)
def expNegMul (A : UnboundedOp H) (t : ℝ≥0) :
    sqIntegrableDomain (spectralResolution A)
      (liftFromLine fun x => Complex.exp (-((t : ℝ) : ℂ) * (x : ℂ))) → H :=
  borelCalculus A fun x => Complex.exp (-((t : ℝ) : ℂ) * (x : ℂ))
def expIMul (A : UnboundedOp H) (s : ℝ) :
    sqIntegrableDomain (spectralResolution A)
      (liftFromLine fun x => Complex.exp (Complex.I * (s : ℂ) * (x : ℂ))) → H :=
  borelCalculus A fun x => Complex.exp (Complex.I * (s : ℂ) * (x : ℂ))
def openPosRay : BorelSubset 1 :=
  ⟨{y | 0 < y 0}, (isOpen_lt continuous_const (by fun_prop)).measurableSet⟩
def negLogOnPosRay : openPosRay.1 → ℂ :=
  fun y => ((-Real.log (y.1 0) : ℝ) : ℂ)
def StronglyCommute {n : ℕ} (A : Fin n → UnboundedOp H) : Prop :=
  (∀ i, IsSelfAdj (A i)) ∧
    ∀ (i k : Fin n) (Δ Δ' : BorelSubset 1),
      Commutes (spectralResolution (A i) Δ) (spectralResolution (A k) Δ')
end YangMills.Construction.EuclideanBorel
