import YangMills.Construction.SummableBoundsOfTheFlow.ExpansionAlongAMotion
import YangMills.Construction.SummableBoundsOfTheFlow.FramesBetweenAndTheirLaws
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace Estimates
open scoped Topology
open BlockAverages ColdStepAtMirrorFrames Interpolation
variable {F : BlockFrame}
inductive Perturbation (F : BlockFrame) : Type
  | bulk (b : ↥(chordBonds (finiteCells F))) (u : EuclideanSpace ℝ (Fin 3)) : Perturbation F
  | top (c : F.Site F.top × Fin 4) (X : imaginaryQuaternions) : Perturbation F
open Classical in
def Perturbation.variableDirection : Perturbation F → StepVariable (finiteCells F)
  | .bulk b u => Pi.single b u
  | .top _ _ => 0
def Perturbation.topBond : Perturbation F → F.Site F.top × Fin 4
  | .bulk _ _ => (0, 0)
  | .top c _ => c
def Perturbation.topDirection : Perturbation F → imaginaryQuaternions
  | .bulk _ _ => 0
  | .top _ X => X
def Perturbation.IsUnit : Perturbation F → Prop
  | .bulk _ u => ‖u‖ = 1
  | .top _ X => ‖X‖ = 1
open Classical in
def Perturbation.decayWeight (r : ℝ) (x : F.Site F.depth) (i : Fin 4) : Perturbation F → ℝ
  | .bulk b _ => if b.1 = (x, i) then 1 else 0
  | .top c _ => Real.exp (-(r * cellSupDist (enclosingCell x) c.1))
def perturbedTop {p : ℕ} (V : F.GaugeField F.top) (w : Fin p → Perturbation F) (τ : Fin p → ℝ) :
    F.GaugeField F.top :=
  leftTranslate (ColdStepAtMirrorFrames.bondSpread (fun l => (w l).topBond) (fun l => (w l).topDirection) τ) V
def perturbedVariable {p : ℕ} (η : StepVariable (finiteCells F)) (w : Fin p → Perturbation F)
    (τ : Fin p → ℝ) : StepVariable (finiteCells F) :=
  η + ∑ l, τ l • (w l).variableDirection
open Classical in
def bondResponse (s a A : ℝ) (m : ℕ) (V : F.GaugeField F.top) (c : F.Site F.top × Fin 4)
    (X : imaginaryQuaternions) (x : F.Site F.depth) (i : Fin 4) : imaginaryQuaternions :=
  bondDeriv (interpolatedFrame s a A m (x, i)) V (fun _ : Fin 1 => c) (fun _ => X) +
    if IsCrossingBond (x, i) ∧ c = (enclosingCell x, i) then X else 0
def motionAboveFrameStatement : Prop :=
  ∀ (n : ℕ) (K : ℕ → ℝ), (∀ k, 0 ≤ K k) → ∃ M : ℕ → ℝ, (∀ q, 0 ≤ M q) ∧
    ∀ (F : BlockFrame) (s a A r : ℝ) (m p : ℕ) (V : F.GaugeField F.top)
      (η : StepVariable (finiteCells F)) (w : Fin p → Perturbation F),
      (∀ i, F.period F.depth i ≠ 0) → 0 ≤ r →
      (∀ d, ¬ IsAxialTreeBond d → d ∈ chordBonds (finiteCells F)) →
      (∀ x i, ¬ IsAxialTreeBond (x, i) → ‖interpolatedCoords s a A m V η x i‖ ≤ 1) →
      (∀ d ∈ chordBonds (finiteCells F), IsBondAnalyticAt (interpolatedFrame s a A m d) V) →
      (∀ d ∈ chordBonds (finiteCells F), ∀ (k : ℕ) (c' : Fin k → F.Site F.top × Fin 4)
        (X' : Fin k → imaginaryQuaternions),
        1 ≤ k → AreUnitVectors X' →
        ‖bondDeriv (interpolatedFrame s a A m d) V c' X'‖ ≤
          K k * Real.exp (-(r * bondListDistance (enclosingCell d.1) c'))) →
      (∀ l, (w l).IsUnit) →
      ∃ α : (Fin p → ℝ) → F.Site F.depth → Fin 4 → imaginaryQuaternions, (∀ x i, α 0 x i = 0) ∧
        (∀ x i, ContDiffAt ℝ n (fun τ => α τ x i) 0) ∧
        (∀ x i, IsAxialTreeBond (x, i) → ∀ τ, α τ x i = 0) ∧
        (∀ᶠ τ in 𝓝 0, interpolatedField s a A m (perturbedTop V w τ) (perturbedVariable η w τ) =
          leftTranslate (α τ) (interpolatedField s a A m V η)) ∧
        (∀ (q : ℕ) (e : Fin q → Fin p) (x : F.Site F.depth) (i : Fin 4) (l : Fin q), q ≤ n →
          ‖motionComponent α e x i‖ ≤ M q * (w (e l)).decayWeight r x i) ∧
        ∀ (l : Fin p) (c : F.Site F.top × Fin 4) (X : imaginaryQuaternions) (x : F.Site F.depth)
          (i : Fin 4), 1 ≤ n →
          w l = .top c X → ¬ IsAxialTreeBond (x, i) →
          ‖motionComponent α (fun _ : Fin 1 => l) x i - bondResponse s a A m V c X x i‖ ≤
            M 0 * ‖interpolatedCoords s a A m V η x i‖
end Estimates
end YangMills.Construction
end
