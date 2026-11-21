import YangMills.Construction.RotationInvariance.KernelOfTheHarmonicsTopHarmonicAndLinesOfThePlane
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.EuclideanFunctionals.TopCoeffLinePositivity
open RealPlane
abbrev InjectiveConfigs (A : Set RealPlane) (k : ℕ) : Type :=
  {c : LabelledPoints k // c.IsInjectiveIn A}
abbrev AllInjectiveConfigs (A : Set RealPlane) : Type :=
  Σ k : ℕ, InjectiveConfigs A k
def topCoeffMapAppend (S : ConnFamily) (α : openingAngles) {k : ℕ}
    (a : RealPlane → RealPlane) (x y : LabelledPoints k) : ℂ :=
  topCoeff S α k (tupleTwoMul (Fin.append x.labelVec y.labelVec))
    (tupleTwoMul (mapAppend a x.points y.points))
def GramKernelPosSemidef (S : ConnFamily) (α : openingAngles) : Prop :=
  ∀ s : ℝ, PositiveDefinite.KernelPosSemidef
    fun x y : AllInjectiveConfigs openRightHalf =>
      harmonicGramKernel S α s x.2.1 y.2.1
def ReflectFirstPosSemidef (S : ConnFamily) (α : openingAngles) : Prop :=
  ∀ k : ℕ, 1 ≤ k → PositiveDefinite.KernelPosSemidef
    fun x y : InjectiveConfigs openRightHalf k =>
      topCoeffMapAppend S α RealPlane.reflectFirst x.1 y.1
def LineReflectionPosSemidef (S : ConnFamily) (α : openingAngles) : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∀ L : Set RealPlane, IsLine L →
    ∀ H : Set RealPlane, IsOpenSide L H →
      ∀ θ : ℝ, NormalPointsInto L (RealPlane.rotate θ unitX) H →
        PositiveDefinite.KernelPosSemidef fun x y : InjectiveConfigs H k =>
          Complex.exp (4 * Complex.I * (topIndex S α k : ℂ) * (θ : ℂ)) *
            topCoeffMapAppend S α (lineReflection L) x.1 y.1
def DiagonalZeroImpliesRowZero (S : ConnFamily) (α : openingAngles) : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∀ L : Set RealPlane, IsLine L →
    ∀ H : Set RealPlane, IsOpenSide L H →
      ∀ x : InjectiveConfigs H k,
        topCoeffMapAppend S α (lineReflection L) x.1 x.1 = 0 →
          ∀ y : InjectiveConfigs H k,
            topCoeffMapAppend S α (lineReflection L) x.1 y.1 = 0
def AllPositivity : Prop :=
  ∀ (M : SharpScale) (S : ConnFamily) (d : PlaneDataWithAperture M S),
    GramKernelPosSemidef S d.angle ∧
    ReflectFirstPosSemidef S d.angle ∧
    LineReflectionPosSemidef S d.angle ∧
    DiagonalZeroImpliesRowZero S d.angle
end YangMills.Construction.EuclideanFunctionals.TopCoeffLinePositivity
end
