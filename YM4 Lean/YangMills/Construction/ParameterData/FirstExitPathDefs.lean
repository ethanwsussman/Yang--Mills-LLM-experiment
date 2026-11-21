import YangMills.Construction.SummableBoundsOfTheFlow.SummabilityBounds
import YangMills.Construction.WindowOfTheParameters.FirstPassageOfASequenceForm
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TrajectoryData
structure TrajectoryParameters (T : RenormalizationStepParameters.ParameterAssignment) (y : ℝ) where
  cH : ℝ
  Md : ℝ
  R : ℝ
  X₀ : ℝ
  Cr : ℝ
  mw : ℕ
  v₀ : ℝ
  shift : ℝ
  lam : ℝ
def lengthScale (x : ℝ) : ℝ := x ^ (-(1 / 2) : ℝ)
def logSlope : ℝ := 11 / (3 * Real.pi ^ 2)
namespace TrajectoryParameters
variable {T : RenormalizationStepParameters.ParameterAssignment} {y : ℝ} (D : TrajectoryParameters T y)
def c₀ (_ : TrajectoryParameters T y) : ℝ := CouplingFlow.slopeConst T.side
def c₅ : ℝ := 2 * D.cH
def rateBound : ℝ := 3 / 4 * D.c₀
def coupling (_ : TrajectoryParameters T y) (β : ℝ) (k : ℕ) : ℝ :=
  CouplingFlow.couplingAt (T.stepParameters y) β k
def numberFlow (_ : TrajectoryParameters T y) (β : ℝ) (k : ℕ) : ℝ :=
  CouplingFlow.flow (FamilyNorms.ParameterAssignment.oneLoop T) (FamilyNorms.ParameterAssignment.secondStep T) β k
def threshold (g : ℝ) : ℝ := SequencePassage.passageThreshold D.shift g
def floorStar : ℝ := max (max D.X₀ (2 ^ 10 * T.B)) (max D.v₀ (16 * D.cH))
def passageWindow (K : ℕ) (g : ℝ) : Set ℝ := SequencePassage.passageWindow D.shift g D.coupling K
def windowCount : ℕ := 1 + ⌊(16 * D.cH + 5) / (3 * D.c₀)⌋₊
def lineGap (m : ℕ) : ℝ :=
  2 * D.cH + D.Cr + 8 * D.Md / (3 * D.c₀) * Real.log (1 + 3 * D.c₀ * m / (4 * D.X₀))
def ratioError (g : ℝ) (K : ℕ) : ℝ := (D.threshold g + D.lineGap K) / (K * Real.log T.side)
def withShift (shift lam : ℝ) : TrajectoryParameters T y := { D with shift := shift, lam := lam }
structure Admissible : Prop where
  errorMargin : CouplingFlow.FlowEstimateAt T y D.cH D.Md D.R D.X₀ D.Cr D.mw D.v₀
  shift_ge : 2 * T.B ≤ D.shift
  lam_pos : 0 < D.lam
  lam_le : D.lam ≤ D.rateBound
structure IsDatum (g : ℝ) (K : ℕ) (β : ℝ) : Prop where
  two_le : 2 ≤ K
  coupling_ge : y ≤ g ^ (-2 : ℤ)
  threshold_le : D.threshold g ≤ β
  passage : SequencePassage.IsFirstPassageIndex D.shift g (D.coupling β) K
  floor : ∀ j ≤ K, y ≤ D.coupling β j
  floor_bound : ∀ j ≤ K, D.X₀ ≤ D.coupling β j
  le_threshold : D.coupling β K ≤ D.threshold g
  room : y + 2 * T.B ≤ D.threshold g
end TrajectoryParameters
end YangMills.Construction.TrajectoryData
end
