import YangMills.Construction.Lattice.AxisBivectorBasis
import YangMills.Construction.Lattice.RingsAndRingKernels
import YangMills.Construction.LinearAlgebra.FreeCurvaturePropagator
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.FreeRingKernels
variable {n : ℕ}
def cyclicPropagatorProduct (σ : Fin n → Fin n) (x : Fin n → Fin 4 → ℝ) :
    Module.End ℝ Exterior.Bivector :=
  (List.ofFn fun i : Fin n =>
    (Exterior.freeCurvaturePropagator (x (σ i) - x (σ (finRotate n i))) :
      Module.End ℝ Exterior.Bivector)).prod
def cyclicTrace (σ : Fin n → Fin n) (x : Fin n → Fin 4 → ℝ) : ℝ :=
  PeriodicLattice.bivectorTrace (cyclicPropagatorProduct σ x)
def IsAdmissibleTestFamily (f : Fin n → (Fin 4 → ℝ) → ℝ) : Prop :=
  (∀ j, Measurable (f j)) ∧ (∀ j, ∃ C : ℝ, ∀ y, |f j y| ≤ C) ∧
    (∀ j, HasCompactSupport (f j)) ∧
      Pairwise fun i j => Disjoint (tsupport (f i)) (tsupport (f j))
def freeRingKernelAlong (σ : Fin n → Fin n) (f : Fin n → (Fin 4 → ℝ) → ℝ) : ℝ :=
  ∫ x : Fin n → Fin 4 → ℝ, (∏ j, f j (x j)) * cyclicTrace σ x
open Classical in
def freeRingKernel (R : Set (Fin n → Fin n)) (f : Fin n → (Fin 4 → ℝ) → ℝ) : ℝ :=
  if h : R.Nonempty then freeRingKernelAlong h.some f else 0
def freeBoxDensity (x : Fin 4 → Fin 4 → ℝ) : ℝ :=
  ∑ r : Fin 3, cyclicTrace (Tuples.standardFourTuple r) x
def freeBoxKernel (f : Fin 4 → (Fin 4 → ℝ) → ℝ) : ℝ :=
  ∑ r : Fin 3, freeRingKernel (Tuples.standardFourRing r) f
end YangMills.Construction.FreeRingKernels
end
