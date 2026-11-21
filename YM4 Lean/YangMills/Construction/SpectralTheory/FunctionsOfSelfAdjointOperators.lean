import YangMills.Construction.SpectralTheory.SelfAdjointSpectralMeasure
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
open scoped Matrix NNReal
noncomputable section
namespace YangMills.Construction
namespace SelfAdjointFunctions
open BorelSpectral HilbertSpaceBasics SpectralTheorem
open JointSpectral (dirac)
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
def fnCalc (A : UnboundedOp H) (f : ℝ → ℂ) : UnboundedOp H :=
  spectralIntegralOp (spectralMeasure A) fun y => f (y.1 0)
def fnCalcOn (A : UnboundedOp H) (Δ : BorelSubsets ℝ) (f : Δ.1 → ℂ) : UnboundedOp H :=
  fnCalc A (zeroExtend Δ.1 f)
def expI (A : UnboundedOp H) (s : ℝ) : H →L[ℂ] H :=
  (spectralMeasure A).integralOp fun y => Complex.exp (Complex.I * s * (y.1 0 : ℝ))
def absOp (A : UnboundedOp H) : UnboundedOp H := fnCalc A fun x => ((|x| : ℝ) : ℂ)
def expNeg (A : UnboundedOp H) (t : ℝ≥0) : H →L[ℂ] H :=
  (spectralMeasure A).integralOp fun y =>
    (Ici (0 : ℝ)).indicator (fun x => Complex.exp ((-(t : ℝ) * x : ℝ) : ℂ)) (y.1 0)
def rpowOp (T : H →L[ℂ] H) (t : ℝ) : H →L[ℂ] H :=
  open Classical in
  if t = 0 then 1 else
    (spectralMeasure (ofBounded T)).integralOp fun y =>
      (Icc (0 : ℝ) 1).indicator (fun x => ((x ^ t : ℝ) : ℂ)) (y.1 0)
def negLogOp (T : H →L[ℂ] H) : UnboundedOp H :=
  fnCalc (ofBounded T) ((Ioc (0 : ℝ) 1).indicator fun x => ((-Real.log x : ℝ) : ℂ))
def PairwiseStronglyCommute {ι : Type*} (A : ι → UnboundedOp H) : Prop :=
  ∀ (i j : ι) (Δ Δ' : BorelSubsets ℝ),
    Commute (spectralMeasure (A i) (realLineSet Δ)) (spectralMeasure (A j) (realLineSet Δ'))
abbrev FullSpace (n : ℕ) : Set (Fin n → ℝ) := univ
variable {n : ℕ}
def coordOperator (E : SpectralMeasure (FullSpace n) H) (i : Fin n) : UnboundedOp H :=
  spectralIntegralOp E fun y => ((y.1 i : ℝ) : ℂ)
def setLtAbs (i k : Fin n) : BorelSubsets (FullSpace n) :=
  ⟨{y | y.1 i < |y.1 k|}, measurableSet_lt
    ((measurable_pi_apply i).comp measurable_subtype_coe)
    (((measurable_pi_apply k).comp measurable_subtype_coe).abs)⟩
def RepresentsGroup (E : SpectralMeasure (FullSpace n) H)
    (U : (Fin n → ℝ) → H →L[ℂ] H) : Prop :=
  ∀ a, U a = E.integralOp fun p => Complex.exp (Complex.I * ((a ⬝ᵥ p.1 : ℝ) : ℂ))
def groupSpectralMeasure (hn : 1 ≤ n) (U : (Fin n → ℝ) → H →L[ℂ] H) :
    SpectralMeasure (FullSpace n) H :=
  haveI : Nonempty (SpectralMeasure (FullSpace n) H) :=
    ⟨dirac hn MeasurableSet.univ ⟨0, mem_univ _⟩⟩
  Classical.epsilon fun E => RepresentsGroup E U
def jointExpI (P : Fin n → UnboundedOp H) (a : Fin n → ℝ) : H →L[ℂ] H :=
  (List.ofFn fun k => expI (P k) (a k)).prod
end SelfAdjointFunctions
end YangMills.Construction
