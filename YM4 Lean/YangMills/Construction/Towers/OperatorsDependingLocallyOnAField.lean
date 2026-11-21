import YangMills.Construction.Towers.DecayOfTheResolventOfAKernelOfRangeAtMostTwo
import YangMills.Construction.Towers.LogarithmsSectorsAndDensityDefs
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open OperatorCalculus Tower.UnitLatticeL2 Tower.AbelianFieldDensity
open Tower.ResolventDecay OneLoopNotation
namespace Tower.LocalFamilies
variable {J B : Type}
abbrev IndexL2 (J : Type) : Type := lp (fun _ : J => ℂ) 2
open Classical in
def bondIndicator (b : B) : B → ℝ := fun c => if c = b then 1 else 0
def twoBondField (b b' : B) (s t : ℝ) : B → ℝ := fun c => s * bondIndicator b c + t * bondIndicator b' c
structure IsIntegerPlacement (pos : J → InfiniteLattice.AmbientSpace) (m : ℕ) : Prop where
  on_lattice : ∀ i, ∃ n : Fin 4 → ℤ, pos i = PeriodicOperators.castVec n
  fibre_bounded : ∀ y, {i | pos i = y}.Finite ∧ {i | pos i = y}.ncard ≤ m
structure IsIndexedL2Space (pos : J → InfiniteLattice.AmbientSpace) (m : ℕ) (z C : ℝ) : Prop where
  placement : IsIntegerPlacement pos m
  entryFacts : MatrixEntryProperties J
  kernelOps : BoundedKernelOperator pos
  trace_bounded : ∀ n : Fin 4 → ℤ, IsBoundedLinearTrace
    (fun A : BddOp (IndexL2 J) =>
      traceAt pos A (PeriodicOperators.castVec n)) m
  trace_integral : ∀ n : Fin 4 → ℤ, CommutesWithIntegral
    (fun A : BddOp (IndexL2 J) =>
      traceAt pos A (PeriodicOperators.castVec n)) m
  logShifted : SectorDecomposition.LogShiftedProps (IndexL2 J) z
  log_eq_integral : SectorDecomposition.LogEqIntegralIoi (IndexL2 J) z
  resolventDecay : ResolventKernelDecays pos z C
structure IsLocallySmoothFamily (pos : J → InfiniteLattice.AmbientSpace)
    (src : B → InfiniteLattice.AmbientSpace) (C : ℝ)
    (T : (B → ℝ) → BddOp (IndexL2 J)) : Prop where
  selfAdjoint : ∀ θ, IsSelfAdjointOp (T θ)
  finite_range : ∀ θ i' i, ¬ TorusMetric.euclidNormVec (pos i' - pos i) ≤ 2 →
    matrixEntry (T θ) i' i = 0
  entry_smooth : ∀ i' i, ∃ (E : Finset B) (Q : (E → ℝ) → ℂ),
    (∀ b ∈ E, TorusMetric.euclidNormVec (src b - pos i') ≤ 2) ∧
    ContDiff ℝ 3 Q ∧
    (∀ j : ℕ, j ≤ 3 → ∀ φ, ‖iteratedFDeriv ℝ j Q φ‖ ≤ C) ∧
    ∀ θ, matrixEntry (T θ) i' i = Q fun b => θ b.1
structure IsLocalExpansionSetting (pos : J → InfiniteLattice.AmbientSpace)
    (src : B → InfiniteLattice.AmbientSpace)
    (m m' : ℕ) (z C : ℝ) (T : (B → ℝ) → BddOp (IndexL2 J)) : Prop where
  space : IsIndexedL2Space pos m z C
  edges : IsIntegerPlacement src m'
  family : IsLocallySmoothFamily pos src C T
  lower_bound : ∃ r : ℝ, 0 < r ∧ ∀ θ : B → ℝ, (∀ b, |θ b| ≤ r) →
    IsBoundedBelowBy (addScalar (T θ) z) (z / 2)
def logTraceAt (pos : J → InfiniteLattice.AmbientSpace)
    (T : (B → ℝ) → BddOp (IndexL2 J)) (z : ℝ) (θ : B → ℝ)
    (x : InfiniteLattice.AmbientSpace) : ℂ :=
  traceAt pos (opLog (addScalar (T θ) z)) x
def logTraceHessian (pos : J → InfiniteLattice.AmbientSpace)
    (T : (B → ℝ) → BddOp (IndexL2 J)) (z : ℝ) (x : InfiniteLattice.AmbientSpace)
    (b b' : B) : ℂ :=
  deriv (fun s : ℝ => deriv (fun t : ℝ => logTraceAt pos T z (twoBondField b b' s t) x) 0) 0
def firstVar (T : (B → ℝ) → BddOp (IndexL2 J)) (b : B) :
    BddOp (IndexL2 J) :=
  deriv (fun s : ℝ => T fun c => s * bondIndicator b c) 0
def secondVar (T : (B → ℝ) → BddOp (IndexL2 J)) (b b' : B) :
    BddOp (IndexL2 J) :=
  deriv (fun s : ℝ => deriv (fun t : ℝ => T (twoBondField b b' s t)) 0) 0
def baseResolvent (T : (B → ℝ) → BddOp (IndexL2 J)) (z w : ℝ) :
    BddOp (IndexL2 J) :=
  inverseOp (addScalar (addScalar (T fun _ => 0) z) w)
def secondOrderResolvent (T : (B → ℝ) → BddOp (IndexL2 J)) (z : ℝ) (b b' : B) (w : ℝ) :
    BddOp (IndexL2 J) :=
  (baseResolvent T z w).comp ((secondVar T b b').comp (baseResolvent T z w)) -
    (baseResolvent T z w).comp ((firstVar T b).comp ((baseResolvent T z w).comp
      ((firstVar T b').comp (baseResolvent T z w)))) -
    (baseResolvent T z w).comp ((firstVar T b').comp ((baseResolvent T z w).comp
      ((firstVar T b).comp (baseResolvent T z w))))
end Tower.LocalFamilies
end YangMills.Construction
end
