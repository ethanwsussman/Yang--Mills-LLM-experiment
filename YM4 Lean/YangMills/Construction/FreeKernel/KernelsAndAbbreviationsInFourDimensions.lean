import YangMills.Construction.FreeKernel.DiscreteTorusAsClassesOfVectors
import YangMills.Construction.FreeKernel.OneDimensionalLatticeKernels
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.FourDimKernel
open PeriodicLattice.ShortDistanceTwoPoint PeriodicLattice.VectorClasses
def latticeHeatKernel4 (t : ℝ) (z : Fin 4 → ℤ) : ℂ :=
  ∏ μ, LatticeKernel.discreteHeatKernel t (z μ)
def gaussianHeatKernel4 (t : ℝ) (u : Fin 4 → ℝ) : ℝ :=
  ∏ μ, LatticeKernel.gaussianHeatKernel t (u μ)
def torusHeatKernel (n : ℕ) (t : ℝ) (z : Fin 4 → ℤ) : ℂ :=
  (1 / (n : ℂ) ^ 4) *
    ∑ᶠ k ∈ PeriodicLattice.ShortDistanceTwoPoint.momentumSet n,
      PeriodicLattice.ShortDistanceTwoPoint.expWave k z *
        ((Real.exp (-t * PeriodicLattice.ShortDistanceTwoPoint.laplacianSymbol k) : ℝ) : ℂ)
theorem isClassFunction_torusHeatKernel {n : ℕ} [NeZero n] (t : ℝ) :
    PeriodicLattice.VectorClasses.IsClassFunction n (torusHeatKernel n t) := by
  intro N w
  have hcls : PeriodicLattice.ShortDistanceTwoPoint.zmodClass n (N + (n : ℤ) • w) =
      PeriodicLattice.ShortDistanceTwoPoint.zmodClass n N :=
    ((PeriodicLattice.VectorClasses.zmodClass_eq_zmodClass_iff N (N + (n : ℤ) • w)).2
      ⟨w, rfl⟩).symm
  simp only [torusHeatKernel]
  congr 1
  refine finsum_mem_congr rfl fun k hk => ?_
  rw [← PeriodicLattice.ShortDistanceTwoPoint.expWaveOnTorus_zmodClass hk,
    ← PeriodicLattice.ShortDistanceTwoPoint.expWaveOnTorus_zmodClass hk N, hcls]
section Differences
variable {A R : Type*} [Ring A] [AddCommGroup R]
def mixedSecondDiff (ν ν' : Fin 4) (f : (Fin 4 → A) → R) : (Fin 4 → A) → R :=
  PeriodicLattice.ShortDistanceTwoPoint.forwardDiff ν
    (PeriodicLattice.ShortDistanceTwoPoint.backwardDiff ν' f)
end Differences
def mixedSecondPartial {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (ν ν' : Fin 4)
    (f : (Fin 4 → ℝ) → E) : (Fin 4 → ℝ) → E :=
  FourVector.coordPartialDeriv ν (FourVector.coordPartialDeriv ν' f)
def intVecNorm (z : Fin 4 → ℤ) : ℝ :=
  FourVector.euclidNorm fun μ => (z μ : ℝ)
abbrev realVecNorm (u : Fin 4 → ℝ) : ℝ :=
  FourVector.euclidNorm u
def bracketOnePlus (y : ℝ) : ℝ := 1 + y
end YangMills.Construction.FourDimKernel
end
