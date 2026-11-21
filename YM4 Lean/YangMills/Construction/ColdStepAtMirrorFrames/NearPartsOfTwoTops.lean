import YangMills.Construction.SummableBoundsOfTheFlow.ExpansionAlongAMotion
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Topology
open YangMills.Construction.BlockAverages YangMills.Construction.Estimates
namespace YangMills.Construction.ColdStepAtMirrorFrames
variable {F : BlockFrame}
open Classical in
def crossingMove (c : Fin 2 → F.Site F.top × Fin 4) (X : Fin 2 → imaginaryQuaternions)
    (x : F.Site F.depth) (i : Fin 4) (τ : Fin 2 → ℝ) : imaginaryQuaternions :=
  if IsCrossingBond (x, i) then bondSpread c X τ (enclosingCell x) i else 0
def NearMotionComponentsOfTwoTops : Prop :=
  ∀ K : ℝ, 1 ≤ K → ∃ C : ℝ, 0 ≤ C ∧ ∀ (F F' : BlockFrame)
    (w : F.GaugeField F.top → F.Site F.depth → Fin 4 → imaginaryQuaternions)
    (w' : F'.GaugeField F'.top → F'.Site F'.depth → Fin 4 → imaginaryQuaternions)
    (V : F.GaugeField F.top) (V' : F'.GaugeField F'.top)
    (c : Fin 2 → F.Site F.top × Fin 4) (c' : Fin 2 → F'.Site F'.top × Fin 4)
    (X : Fin 2 → imaginaryQuaternions)
    (α : (Fin 2 → ℝ) → F.Site F.depth → Fin 4 → imaginaryQuaternions)
    (α' : (Fin 2 → ℝ) → F'.Site F'.depth → Fin 4 → imaginaryQuaternions)
    (x : F.Site F.depth) (x' : F'.Site F'.depth) (i : Fin 4) (ε : ℝ), 0 ≤ ε → AreUnitVectors X →
    ¬ IsAxialTreeBond (x, i) → ¬ IsAxialTreeBond (x', i) →
    (∀ z j, α 0 z j = 0) → (∀ z j, α' 0 z j = 0) →
    ContDiffAt ℝ 3 (fun τ => α τ x i) 0 → ContDiffAt ℝ 3 (fun τ => α' τ x' i) 0 →
    ContDiffAt ℝ 3 (fun τ => w (leftTranslate (bondSpread c X τ) V) x i) 0 →
    ContDiffAt ℝ 3 (fun τ => w' (leftTranslate (bondSpread c' X τ) V') x' i) 0 →
    ‖w V x i‖ ≤ 1 → ‖w' V' x' i‖ ≤ 1 →
    (∀ᶠ τ in 𝓝 (0 : Fin 2 → ℝ),
      chartedField (w (leftTranslate (bondSpread c X τ) V)) (leftTranslate (bondSpread c X τ) V) =
        leftTranslate (α τ) (chartedField (w V) V)) →
    (∀ᶠ τ in 𝓝 (0 : Fin 2 → ℝ),
      chartedField (w' (leftTranslate (bondSpread c' X τ) V')) (leftTranslate (bondSpread c' X τ) V') =
        leftTranslate (α' τ) (chartedField (w' V') V')) →
    crossingMove c X x i = crossingMove c' X x' i →
    (∀ l, ‖bondDeriv (fun U => w U x i) V ![c l] ![X l]‖ ≤ K) →
    (∀ l, ‖bondDeriv (fun U => w' U x' i) V' ![c' l] ![X l]‖ ≤ K) →
    ‖bondDeriv (fun U => w U x i) V c X‖ ≤ K → ‖bondDeriv (fun U => w' U x' i) V' c' X‖ ≤ K →
    ‖w V x i - w' V' x' i‖ ≤ ε →
    (∀ l, ‖bondDeriv (fun U => w U x i) V ![c l] ![X l] -
      bondDeriv (fun U => w' U x' i) V' ![c' l] ![X l]‖ ≤ ε) →
    ‖bondDeriv (fun U => w U x i) V c X - bondDeriv (fun U => w' U x' i) V' c' X‖ ≤ ε →
    (∀ l, ‖motionComponent α ![l] x i - motionComponent α' ![l] x' i‖ ≤ C * ε) ∧
      ‖motionComponent α ![0, 1] x i - motionComponent α' ![0, 1] x' i‖ ≤ C * ε
end YangMills.Construction.ColdStepAtMirrorFrames
end
