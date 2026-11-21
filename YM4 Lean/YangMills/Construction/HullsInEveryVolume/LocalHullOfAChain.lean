import YangMills.Construction.HullsInEveryVolume.HullDefs
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.HullTrees
open TorusFields TorusLumps StepSettings WeightedResponses
variable {ℓ : StepParameters}
open Classical in
def localHullData (T : StageTower ℓ) (s₁ : ℝ) : (j n : ℕ) → [NeZero n] → MarkedSample ℓ j n → Finset (TorusSite n) →
    Finset (TorusSite n) × (TorusSite n → ℝ)
  | 0, n, _, w, Q => (hullSet T 0 n w ∩ Q, fun _ => 0)
  | j + 1, n, _, w, Q =>
    let R := (T.stage j).toStepSetup
    let lo := localHullData T s₁ j (n * ℓ.side) w.1 (sitesInBlocks ℓ.side Q)
    let bad : Finset (TorusBond (n * ℓ.side)) :=
      (show Finset (TorusBond (n * ℓ.side)) from w.2.2.2).filter fun b => b.1 ∈ sitesInBlocks ℓ.side Q
    let C := hotCoreSites R w.2.2.1 ∩ Q
    let Z := C ∪ (coreBlocks ℓ.side R.range (attachedSites ℓ.side R.range bad lo.1 C) ∩ Q)
    let Y := thickening (R.nextRange / 2) Z ∩ Q
    (Y, fun y => if y ∈ Z then s₁ + ∑ z ∈ sitesInBlocks ℓ.side {y} ∩ lo.1, lo.2 z else if y ∈ Y then s₁ else 0)
open Classical in
def localCoreZone (T : StageTower ℓ) (s₁ : ℝ) (j n : ℕ) [NeZero n] (w : MarkedSample ℓ (j + 1) n)
    (Q : Finset (TorusSite n)) : Finset (TorusSite n) :=
  (hotCoreSites (T.stage j).toStepSetup w.2.2.1 ∩ Q) ∪
    (coreBlocks ℓ.side (T.stage j).toStepSetup.range (attachedSites ℓ.side (T.stage j).toStepSetup.range
      ((show Finset (TorusBond (n * ℓ.side)) from w.2.2.2).filter fun b => b.1 ∈ sitesInBlocks ℓ.side Q)
      (localHullData T s₁ j (n * ℓ.side) w.1 (sitesInBlocks ℓ.side Q)).1
      (hotCoreSites (T.stage j).toStepSetup w.2.2.1 ∩ Q)) ∩ Q)
def coreZone (T : StageTower ℓ) (j n : ℕ) [NeZero n] (w : MarkedSample ℓ (j + 1) n) : Finset (TorusSite n) :=
  storedBlocks ℓ.side (T.stage j).toStepSetup.range (show Finset (TorusBond (n * ℓ.side)) from w.2.2.2)
    (hullSet T j (n * ℓ.side) w.1) (hotCoreSites (T.stage j).toStepSetup w.2.2.1)
def localHullBox {n : ℕ} [NeZero n] (T : StageTower ℓ) (u : ℕ) (y : TorusSite n) (D : ℝ) : Finset (TorusSite n) :=
  box y (⌊2 * D⌋₊ + stageRange T u)
open Classical in
def localScoreMoment (T : StageTower ℓ) (s₁ : ℝ) (u n : ℕ) [NeZero n] (y : TorusSite n) (D : ℝ) (k : ℕ)
    (w : MarkedSample ℓ u n) : ℝ :=
  if y ∈ (localHullData T s₁ u n w (localHullBox T u y D)).1 then
    ((localHullData T s₁ u n w (localHullBox T u y D)).2 y) ^ k else 0
end YangMills.Construction.HullTrees
end
