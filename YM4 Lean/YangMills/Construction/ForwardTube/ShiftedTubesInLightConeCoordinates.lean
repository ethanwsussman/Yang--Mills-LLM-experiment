import YangMills.Construction.EuclideanFunctionals.PlateVectorsAndFunctionsOnTheShiftedTubes
import YangMills.Construction.ForwardTube.TubeMargin
import YangMills.Construction.RotationInvariance.SettingOfTheHarmonicsAtDistinctPoints
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ForwardTube
def forwardTubePow (q : ℕ) : Set (Fin q → ℂ × ℂ) := Set.univ.pi fun _ => forwardTube
def conjTuple {p : ℕ} (z : Fin p → ℂ × ℂ) : Fin p → ℂ × ℂ := fun i => conjPair (z i)
def orderedTimeTuples (p : ℕ) (η : ℝ) : Set (Fin p → RealPlane) :=
  {w | (∀ hp : 0 < p, w ⟨0, hp⟩ 0 > η / 4) ∧
    ∀ (k : ℕ) (hk : k + 1 < p), w ⟨k + 1, hk⟩ 0 - w ⟨k, by omega⟩ 0 > η / 2}
namespace ShiftedTubeCoords
def PowOpenConvex (q : ℕ) (η : ℝ) : Prop :=
  shiftedForwardTubePow q η =
      {v | ∀ i, (lightConePlus (v i)).re > η / 2 ∧ (lightConeMinus (v i)).re > η / 2} ∧
  IsOpen (shiftedForwardTubePow q η) ∧ Convex ℝ (shiftedForwardTubePow q η) ∧
  IsOpen (forwardTubePow q) ∧ Convex ℝ (forwardTubePow q)
def PowNested (q : ℕ) (η : ℝ) : Prop :=
  (∀ ε : ℝ, 0 < ε → ε ≤ η →
    shiftedForwardTubePow q η ⊆ shiftedForwardTubePow q ε ∧
      shiftedForwardTubePow q ε ⊆ forwardTubePow q) ∧
  ∀ v ∈ forwardTubePow q, tubeMargin v ∈ Set.Ioc (0 : ℝ) 1 ∧
    v ∈ shiftedForwardTubePow q (tubeMargin v)
def PowRealLocus (q : ℕ) (η : ℝ) : Prop :=
  realLocus (shiftedForwardTubePow q η) = embedPlaneTuple '' {w | ∀ i, w i 0 > η / 2} ∧
  realLocus (forwardTubePow q) = embedPlaneTuple '' {w | ∀ i, w i 0 > 0} ∧
  forwardTubePow q ∩ Set.range embedPlaneTuple =
    embedPlaneTuple '' Set.univ.pi fun _ => RealPlane.openRightHalf
def ShiftedTubeRealLocus (p : ℕ) (η : ℝ) : Prop :=
  shiftedForwardTube p η =
    {z | (∀ hp : 0 < p, (lightConePlus (z ⟨0, hp⟩)).re > η / 4 ∧
          (lightConeMinus (z ⟨0, hp⟩)).re > η / 4) ∧
      ∀ (k : ℕ) (hk : k + 1 < p),
        (lightConePlus (z ⟨k + 1, hk⟩ - z ⟨k, by omega⟩)).re > η / 2 ∧
        (lightConeMinus (z ⟨k + 1, hk⟩ - z ⟨k, by omega⟩)).re > η / 2} ∧
  conjTuple '' shiftedForwardTube p η = shiftedForwardTube p η ∧
  realLocus (shiftedForwardTube p η) = embedPlaneTuple '' orderedTimeTuples p η ∧
  (orderedTimeTuples p η).Nonempty ∧ IsOpen (orderedTimeTuples p η)
def Holds : Prop :=
  ∀ q : ℕ, 1 ≤ q → ∀ η : ℝ, 0 < η → η ≤ 1 →
    PowOpenConvex q η ∧ PowNested q η ∧ PowRealLocus q η ∧
    ∀ p : ℕ, 1 ≤ p → ShiftedTubeRealLocus p η
end ShiftedTubeCoords
end YangMills.Construction.ForwardTube
end
