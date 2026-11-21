import YangMills.Construction.Matrices.NormAndTraceOfAComplexMatrix
import YangMills.Construction.PeriodicOperators.PeriodicIndexSetsOperatorsAndSymbols
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Matrices.FourierMatrixSeries
open YangMills.Construction.PeriodicOperators (castVec toComplexVec bilinDot torusAverage)
open YangMills.Construction.InfiniteLattice (AmbientSpace)
open YangMills.Construction.TorusMetric (euclidNormVec)
abbrev CoeffFamily (m p : ℕ) : Type := (Fin 4 → ℤ) → Matrix (Fin m) (Fin p) ℂ
def character (n : Fin 4 → ℤ) (x : AmbientSpace) : ℂ :=
  Complex.exp (Complex.I * bilinDot (toComplexVec (castVec n)) (toComplexVec x))
def seriesSum {m p : ℕ} (c : CoeffFamily m p) (x : AmbientSpace) : Matrix (Fin m) (Fin p) ℂ :=
  ∑' n, character n x • c n
variable {m p : ℕ} [NeZero m] [NeZero p]
def AbsSummable (c : CoeffFamily m p) : Prop :=
  Summable fun n => YangMills.Construction.Matrices.RectangularMatrix.opNormValue (c n)
def WeightedAbsSummable (k : ℕ) (c : CoeffFamily m p) : Prop :=
  Summable fun n => YangMills.Construction.Matrices.RectangularMatrix.opNormValue (c n) *
    (1 + euclidNormVec (castVec n)) ^ k
def SeriesUnifConverges (c : CoeffFamily m p) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ S₀ : Finset (Fin 4 → ℤ), ∀ S : Finset (Fin 4 → ℤ), S₀ ⊆ S → ∀ x : AmbientSpace,
    YangMills.Construction.Matrices.RectangularMatrix.opNormValue
      ((∑ n ∈ S, character n x • c n) - seriesSum c x) < ε
omit [NeZero m] [NeZero p] in
def HasContinuousPartialDeriv (ν : Fin 4) (f g : AmbientSpace → Matrix (Fin m) (Fin p) ℂ) : Prop :=
  Continuous g ∧ ∀ (x : AmbientSpace) (r : Fin m) (s : Fin p),
    HasDerivAt (fun t : ℝ => f (Function.update x ν t) r s) (g x r s) (x ν)
def derivCoeffs {m p : ℕ} (dirs : List (Fin 4)) (c : CoeffFamily m p) : CoeffFamily m p :=
  fun n => (dirs.map fun ν => Complex.I * (n ν : ℂ)).prod • c n
theorem derivCoeffs_nil {m p : ℕ} (c : CoeffFamily m p) : derivCoeffs [] c = c := by
  funext n
  simp [derivCoeffs]
abbrev SumPairs (n : Fin 4 → ℤ) : Type :=
  {u : (Fin 4 → ℤ) × (Fin 4 → ℤ) // u.1 + u.2 = n}
def coeffConv {m p r : ℕ} (c : CoeffFamily m p) (d : CoeffFamily p r) :
    CoeffFamily m r :=
  fun n => ∑' u : SumPairs n, c u.1.1 * d u.1.2
structure AbsSummableProps (c : CoeffFamily m p) : Prop where
  unif_converges : SeriesUnifConverges c
  continuous_sum : Continuous (seriesSum c)
  coeff_eq_average : ∀ (n : Fin 4 → ℤ) (r : Fin m) (s : Fin p),
    c n r s = torusAverage fun x => seriesSum c x r s * character (-n) x
  sum_injective : ∀ d : CoeffFamily m p, AbsSummable d → seriesSum d = seriesSum c → d = c
structure TermwiseDiffProps (k : ℕ) (c : CoeffFamily m p) : Prop where
  partial_deriv : ∀ ν : Fin 4, ∃ g : AmbientSpace → Matrix (Fin m) (Fin p) ℂ,
    HasContinuousPartialDeriv ν (seriesSum c) g ∧
      ∀ x, (-Complex.I) • g x = seriesSum (fun n => (n ν : ℂ) • c n) x
  weighted_summable_deriv : ∀ ν : Fin 4,
    WeightedAbsSummable (k - 1) fun n => (n ν : ℂ) • c n
  higher_summable : ∀ dirs : List (Fin 4), dirs.length ≤ k →
    AbsSummable (derivCoeffs dirs c) ∧ Continuous (seriesSum (derivCoeffs dirs c))
  higher_partial_deriv : ∀ dirs : List (Fin 4), dirs.length < k → ∀ ν : Fin 4,
    HasContinuousPartialDeriv ν (seriesSum (derivCoeffs dirs c)) (seriesSum (derivCoeffs (ν :: dirs) c))
structure ProductProps {r : ℕ} [NeZero r] (c : CoeffFamily m p)
    (d : CoeffFamily p r) : Prop where
  inner_norms_summable : ∀ n : Fin 4 → ℤ, Summable fun u : SumPairs n =>
    YangMills.Construction.Matrices.RectangularMatrix.opNormValue (c u.1.1) *
      YangMills.Construction.Matrices.RectangularMatrix.opNormValue (d u.1.2)
  hasSum_norms : HasSum (fun n : Fin 4 → ℤ => ∑' u : SumPairs n,
      YangMills.Construction.Matrices.RectangularMatrix.opNormValue (c u.1.1) *
        YangMills.Construction.Matrices.RectangularMatrix.opNormValue (d u.1.2))
    ((∑' n, YangMills.Construction.Matrices.RectangularMatrix.opNormValue (c n)) *
      ∑' n, YangMills.Construction.Matrices.RectangularMatrix.opNormValue (d n))
  conv_terms_summable : ∀ n : Fin 4 → ℤ, Summable fun u : SumPairs n =>
    YangMills.Construction.Matrices.RectangularMatrix.opNormValue (c u.1.1 * d u.1.2)
  conv_summable : AbsSummable (coeffConv c d)
  sum_mul_sum : ∀ x : AmbientSpace, seriesSum c x * seriesSum d x = seriesSum (coeffConv c d) x
def statement : Prop :=
  ∀ (m p : ℕ) [NeZero m] [NeZero p] (c : CoeffFamily m p), AbsSummable c →
    AbsSummableProps c ∧
    (∀ k : ℕ, 1 ≤ k → WeightedAbsSummable k c → TermwiseDiffProps k c) ∧
    ∀ (r : ℕ) [NeZero r] (d : CoeffFamily p r), AbsSummable d → ProductProps c d
end YangMills.Construction.Matrices.FourierMatrixSeries
end
