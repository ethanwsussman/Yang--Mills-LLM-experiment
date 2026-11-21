import YangMills.Construction.SpectralMeasures.BoundedBorelCalculus
import Mathlib
set_option autoImplicit false
open Filter
noncomputable section
namespace YangMills.Construction.EuclideanBorel
section SpectralIntegrals
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {n : ℕ}
def spectralIntegral (E : BorelSubset n → H →L[ℂ] H) (f : Space n → ℂ) :
    sqIntegrableDomain E f → H :=
  fun v => limUnder atTop fun k : ℕ => boundedCalculus E (cutoff f k) v.1
omit [CompleteSpace H] in
theorem spectralIntegral_eq_boundedCalculus {E : BorelSubset n → H →L[ℂ] H}
    (hE : CutoffsConverge E) {f : Space n → ℂ} (hf : IsBoundedMeasurableFn f)
    (v : sqIntegrableDomain E f) :
    spectralIntegral E f v = boundedCalculus E f v.1 :=
  ((hE.2 f hf).2 v.1).limUnder_eq
open Classical in
def zeroExtend (S : BorelSubset n) (f : S.1 → ℂ) : Space n → ℂ :=
  fun y => if hy : y ∈ S.1 then f ⟨y, hy⟩ else 0
end SpectralIntegrals
def coordFn {n : ℕ} (i : Fin n) : Space n → ℂ :=
  fun y => ((y i : ℝ) : ℂ)
def lineCoord : Space 1 → ℂ :=
  coordFn 0
def spectralParamCoord : Space (1 + 3) → ℂ :=
  coordFn (Fin.castAdd 3 0)
def momentumCoord (i : Fin 3) : Space (1 + 3) → ℂ :=
  coordFn (Fin.natAdd 1 i)
def momentumVec (y : Space (1 + 3)) : Space 3 :=
  WithLp.toLp 2 fun i => y (Fin.natAdd 1 i)
end YangMills.Construction.EuclideanBorel
