import YangMills.Construction.InfiniteLattice.MirrorGridsCopiesAndChessboardValuesOfMultipleReflections
import YangMills.Construction.InfiniteLattice.TransferOperatorWithAnInsertion
import Mathlib
set_option autoImplicit false
open Filter
open scoped ComplexConjugate
noncomputable section
namespace YangMills.Construction
open InfiniteLattice (AmbientSpace timeAxis halfSpacingTimes equalTimeMirror timeReflect shift
  timeStep positiveMultiples)
namespace MultipleReflections.Setup
def IncreasesToInfinity (D : Setup) (ℓ : ℕ+ → PeriodicLattice.torusSides D.L) : Prop :=
  (∀ m, (ℓ m : ℝ) ≤ ℓ (m + 1)) ∧ Tendsto (fun m => (ℓ m : ℝ)) atTop atTop
namespace Grid
variable {D : Setup} (G : D.Grid) (k : Fin 4 → ℤ)
def baseTime : ℝ := G.tileCenter k timeAxis - 1 / 2 * G.edge
theorem baseTime_eq :
    G.baseTime k = G.shift timeAxis + k timeAxis * G.edge := by
  have h0 : timeAxis ≠ (0 : Fin 4) := by decide
  have h1 : timeAxis ≠ (1 : Fin 4) := by decide
  have h2 : timeAxis ≠ (2 : Fin 4) := by decide
  simp [baseTime, InfiniteLattice.ReflectionGrid.tileCenter, InfiniteLattice.ReflectionGrid.cornerAt,
    InfiniteLattice.ReflectionGrid.basisVec, Fin.sum_univ_four, h0, h1, h2]
  ring
def wallTime (n : ℤ) : ℝ := G.baseTime k + n * G.edge
theorem wallTime_mem (n : ℤ) : ∃ i : ℤ, G.wallTime k n = D.mesh * ((i : ℝ) + 1 / 2) := by
  obtain ⟨i, hi⟩ := G.shift_mem timeAxis
  obtain ⟨N, hN⟩ :=
    InfiniteLattice.ReflectionGrid.exists_edge_eq_natCast_mul_spacingAt G D.isAdmissible
  have ha : CutoffLattice.spacingAt D.L (D.K : ℕ) = D.mesh := rfl
  rw [ha] at hi hN
  refine ⟨i + (k timeAxis + n) * N, ?_⟩
  rw [wallTime, baseTime_eq, hi, hN]
  push_cast
  ring
def wallTimeHalf (n : ℤ) : halfSpacingTimes D.mesh :=
  ⟨G.wallTime k n, by
    obtain ⟨i, hi⟩ := G.wallTime_mem k n
    refine ⟨2 * i + 1, ?_⟩
    rw [hi]
    push_cast
    ring⟩
theorem wallTimeHalf_zero : (G.wallTimeHalf k 0 : ℝ) = G.baseTime k := by
  simp [wallTimeHalf, wallTime]
def stackReflect (n : ℤ) (B : D.GaugeField → ℂ) : D.GaugeField → ℂ :=
  fun U => conj ((timeReflect (G.wallTimeHalf k n)).actOn B U)
def edgeMultiple : positiveMultiples D.mesh :=
  ⟨G.edge, by
    obtain ⟨N, hN⟩ :=
      InfiniteLattice.ReflectionGrid.exists_edge_eq_natCast_mul_spacingAt G D.isAdmissible
    have ha : CutoffLattice.spacingAt D.L (D.K : ℕ) = D.mesh := rfl
    rw [ha] at hN
    have hpos := G.edge_pos
    refine ⟨N, ?_, hN⟩
    rcases Nat.eq_zero_or_pos N with h | h
    · rw [hN, h] at hpos
      simp at hpos
    · exact h⟩
def stackShift (i : ℤ) : D.LatticeSymmetry := shift (i • timeStep G.edgeMultiple)
theorem stackShift_apply (i : ℤ) (x : AmbientSpace) :
    (G.stackShift i).toFun x =
      x + ((i : ℝ) * G.edge) • (Pi.single timeAxis 1 : AmbientSpace) := by
  funext μ
  by_cases h : μ = timeAxis
  · subst h
    simp [stackShift, shift, timeStep, edgeMultiple]
  · simp [stackShift, shift, timeStep, edgeMultiple, Pi.single_eq_of_ne h]
theorem stackShift_zero (A : D.GaugeField → ℂ) : (G.stackShift 0).actOn A = A := by
  funext U
  change A ((G.stackShift 0).pullbackField U) = A U
  congr 1
  apply Subtype.ext
  funext b
  change U.1 ((G.stackShift 0).linkMap b) = U.1 b
  apply congrArg U.1
  cases b with
  | mk x y h =>
    simp only [InfiniteLattice.LatticeSymmetry.linkMap, InfiniteLattice.Link.mk.injEq]
    constructor <;> apply Subtype.ext
    · change (G.stackShift 0).toFun x = x
      rw [stackShift_apply]
      simp
    · change (G.stackShift 0).toFun y = y
      rw [stackShift_apply]
      simp
theorem stackShift_add (i i' : ℤ) (A : D.GaugeField → ℂ) :
    (G.stackShift (i + i')).actOn A =
      (G.stackShift i).actOn ((G.stackShift i').actOn A) := by
  funext U
  change A ((G.stackShift (i + i')).pullbackField U) =
    A ((G.stackShift i').pullbackField ((G.stackShift i).pullbackField U))
  congr 1
  apply Subtype.ext
  funext b
  change U.1 ((G.stackShift (i + i')).linkMap b) =
    U.1 ((G.stackShift i).linkMap ((G.stackShift i').linkMap b))
  apply congrArg U.1
  have hx : ∀ x : AmbientSpace, (G.stackShift (i + i')).toFun x =
      (G.stackShift i).toFun ((G.stackShift i').toFun x) := by
    intro x
    rw [stackShift_apply, stackShift_apply, stackShift_apply]
    push_cast
    module
  cases b with
  | mk x y h =>
    simp only [InfiniteLattice.LatticeSymmetry.linkMap, InfiniteLattice.Link.mk.injEq]
    constructor <;> apply Subtype.ext
    · exact hx x
    · exact hx y
def stackIndex (i : ℤ) : Fin 4 → ℤ := k + (i - 1) • Pi.single timeAxis 1
theorem stackIndex_one : stackIndex k 1 = k := by
  simp [stackIndex]
def stackCopy (F : D.GaugeField → ℂ) (i : ℤ) : D.GaugeField → ℂ :=
  G.reflectedCopy k (stackIndex k i) F
def stackProd (F : D.GaugeField → ℂ) (i₁ i₂ : ℤ) : D.GaugeField → ℂ :=
  fun U => ∏ i ∈ Finset.Icc i₁ i₂, G.stackCopy k F i U
theorem stackProd_empty (F : D.GaugeField → ℂ) (i₁ : ℤ) :
    G.stackProd k F i₁ (i₁ - 1) = 1 := by
  funext U
  simp [stackProd]
def stackCorrelation (μ : MeasureTheory.Measure D.GaugeField) (F A : D.GaugeField → ℂ) (n : ℕ) :
    ℂ :=
  ∫ U, G.stackReflect k 0 A U * G.stackProd k F 1 (2 * n) U *
    (G.stackShift (2 * n)).actOn A U ∂μ
def IsStackSideSequence (ℓ : ℕ+ → PeriodicLattice.torusSides D.L) : Prop :=
  D.IncreasesToInfinity ℓ ∧ ∀ m, 2 * G.edge ≤ ℓ m
def limsupStackNorm (ℓ : ℕ+ → PeriodicLattice.torusSides D.L) (F : D.GaugeField → ℂ) : ℝ :=
  limsup (fun m => G.chessboardNormAt (ℓ m) (ℓ m).2 k F) atTop
end Grid
end MultipleReflections.Setup
end YangMills.Construction
end
