import YangMills.Construction.EuclideanFunctionals.SymmetricEuclideanFunctionalWithReconstruction
import YangMills.Construction.Functions.EuclideanCompactSupport
import Mathlib
set_option autoImplicit false
open MeasureTheory
open scoped Pointwise
noncomputable section
namespace YangMills.Construction.EuclideanFunctionals.Smearing
def PreservesEuclidNorm (V : Submodule ℝ R4)
    (L : (Fin (Module.finrank ℝ V) → ℝ) →ₗ[ℝ] V) : Prop :=
  Function.Surjective L ∧
    ∀ y, EuclideanFunctions.euclideanNorm (L y : R4) =
      EuclideanFunctions.euclideanNorm y
def IsLebesgueOn (V : Submodule ℝ R4) (ν : Measure V) : Prop :=
  (Module.finrank ℝ V = 0 ∧ ν = Measure.dirac 0) ∨
    (Module.finrank ℝ V ≠ 0 ∧
      ∃ L, PreservesEuclidNorm V L ∧ ν = Measure.map L volume)
def conv {V : Submodule ℝ R4} (ν : Measure V) (g : V → ℂ) (f : R4 → ℂ) : R4 → ℂ :=
  fun x => ∫ y, g y * f (x - (y : R4)) ∂ν
def suppIn {V : Submodule ℝ R4} (g : V → ℂ) : Set R4 :=
  Subtype.val '' tsupport g
def convEntries {V : Submodule ℝ R4} {r k : ℕ} (ν : Measure V) (g : Fin r → V → ℂ)
    (f : Fin k → R4 → ℂ) : Fin k → R4 → ℂ :=
  fun i => if hi : (i : ℕ) < r then conv ν (g ⟨i, hi⟩) (f i) else f i
def shiftSmearingTuple {V : Submodule ℝ R4} {r k : ℕ} (y : Fin r → V)
    (f : Fin k → R4 → ℂ) : Fin k → R4 → ℂ :=
  fun i => if hi : (i : ℕ) < r then (EuclidMotion.transl (y ⟨i, hi⟩ : R4)).actFn (f i)
    else f i
def valueAt (T : ConnFamily) {k : ℕ} (f : Fin k → R4 → ℂ) : ℂ :=
  centeredFnFree T (complexTuple f)
def integrand (T : ConnFamily) {V : Submodule ℝ R4} {r k : ℕ} (g : Fin r → V → ℂ)
    (f : Fin k → R4 → ℂ) : (Fin r → V) → ℂ :=
  fun y => (∏ i, g i (y i)) * valueAt T (shiftSmearingTuple y f)
structure Data {V : Submodule ℝ R4} {r k : ℕ} (K : Fin k → Set R4)
    (f : Fin k → R4 → ℂ) (g : Fin r → V → ℂ) : Prop where
  compact : ∀ i, IsCompact (K i)
  pairwise_disjoint : Pairwise fun i j => Disjoint (K i) (K j)
  mem_C1c : ∀ i, f i ∈ C1c ℂ
  cont : ∀ i, Continuous (g i)
  compactSupport : ∀ i, HasCompactSupport (g i)
  conv_supp : ∀ (i : Fin k) (hi : (i : ℕ) < r),
    supp (f i) + suppIn (g ⟨i, hi⟩) ⊆ K i
  rest_supp : ∀ i : Fin k, ¬ (i : ℕ) < r → supp (f i) ⊆ K i
def ConvInSets {V : Submodule ℝ R4} {r k : ℕ} (ν : Measure V)
    (K : Fin k → Set R4) (f : Fin k → R4 → ℂ) (g : Fin r → V → ℂ) : Prop :=
  ∀ (i : Fin k) (hi : (i : ℕ) < r),
    conv ν (g ⟨i, hi⟩) (f i) ∈ C1c ℂ ∧
      supp (conv ν (g ⟨i, hi⟩) (f i)) ⊆ K i
def ShiftsContinuous (T : ConnFamily) {V : Submodule ℝ R4} {r k : ℕ}
    (f : Fin k → R4 → ℂ) (g : Fin r → V → ℂ) : Prop :=
  IsCompact (Set.pi Set.univ fun i => tsupport (g i)) ∧
    (∀ y ∈ Set.pi Set.univ (fun i => tsupport (g i)), ComplexComponents (shiftSmearingTuple y f)) ∧
    ContinuousOn (fun y : Fin r → V => valueAt T (shiftSmearingTuple y f))
      (Set.pi Set.univ fun i => tsupport (g i))
def Formula (T : ConnFamily) {V : Submodule ℝ R4} {r k : ℕ} (ν : Measure V)
    (f : Fin k → R4 → ℂ) (g : Fin r → V → ℂ) : Prop :=
  valueAt T (convEntries ν g f) =
      ∫ y, integrand T g f y ∂(Measure.pi fun _ : Fin r => ν) ∧
    Continuous (integrand T g f) ∧ HasCompactSupport (integrand T g f)
def Holds : Prop :=
  (∀ (V : Submodule ℝ R4) (ν ν' : Measure V),
    IsLebesgueOn V ν → IsLebesgueOn V ν' → ν = ν') ∧
  ∀ (s : SharpScale) (T : ConnFamily), EuclidFunctionalWithRecon s T →
    ∀ (k r : ℕ), 2 ≤ k → 1 ≤ r → r ≤ k →
      ∀ (V : Submodule ℝ R4) (ν : Measure V), IsLebesgueOn V ν →
        ∀ (K : Fin k → Set R4) (f : Fin k → R4 → ℂ) (g : Fin r → V → ℂ),
          Data K f g →
            ConvInSets ν K f g ∧ ShiftsContinuous T f g ∧
              Formula T ν f g
end YangMills.Construction.EuclideanFunctionals.Smearing
