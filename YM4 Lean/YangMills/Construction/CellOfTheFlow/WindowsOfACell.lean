import YangMills.Construction.ClusterExpansionOfAStep.FreeClassesOfAStep
import YangMills.Construction.ResponseInTheExpansion.TowerAtTheParameters
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.CellWindows
open TorusFields TorusLumps StepSettings RenormalizationStepParameters WeightedResponses ResponseInTheExpansion
variable {ℓ : TorusLumps.StepParameters}
def stageRange (T : StageTower ℓ) (j : ℕ) : ℕ := clusterRange (T.stage j).coupling
def ceilDiv (a L : ℕ) : ℕ := (a + L - 1) / L
def windowLength (T : StageTower ℓ) (k j : ℕ) : ℕ := 2 ^ 12 * stageRange T j * (k - j)
def windowDepth (T : StageTower ℓ) (k : ℕ) : ℕ → ℕ
  | 0 => 4 * stageRange T 0
  | j + 1 => max (4 * stageRange T (j + 1)) (ceilDiv (windowDepth T k j) ℓ.side + 1) +
      ceilDiv (windowLength T k j) ℓ.side + stageRange T (j + 1)
def blockDepth (T : StageTower ℓ) (k j : ℕ) : ℕ :=
  max (4 * stageRange T (j + 1)) (ceilDiv (windowDepth T k j) ℓ.side + 1)
section Interiors
variable {n : ℕ} [NeZero n]
open Classical in
def interiorAtDepth (m : ℕ) (c : Finset (TorusSite n)) : Finset (TorusSite n) :=
  c.filter fun v => ∀ w, w ∉ c → m ≤ supDist v w
end Interiors
def cellBelow (L : ℕ) [NeZero L] : (d n : ℕ) → [NeZero n] → Finset (TorusSite n) →
    Finset (TorusSite (fineSide L d n))
  | 0, _, _, c => c
  | d + 1, n, _, c => cellBelow L d (n * L) (sitesInBlocks L c)
def baseCellSide (L r : ℕ) : ℕ := L ^ Nat.clog L (2 ^ 7 * r)
structure CellGrid where
  side : ℕ
  offset : Fin 4 → ℤ
namespace CellGrid
variable (G : CellGrid)
def refine (L : ℕ) : CellGrid :=
  ⟨G.side * L, fun i => (L : ℤ) * G.offset i - ((L : ℤ) - 1) / 2⟩
def refineBy (L : ℕ) : ℕ → CellGrid → CellGrid
  | 0, G => G
  | d + 1, G => refineBy L d (G.refine L)
def cell (n : ℕ) [NeZero n] (κ : Fin 4 → ℤ) : Finset (TorusSite n) :=
  open Classical in
  Finset.univ.filter fun x => ∃ h : Fin 4 → ℤ, (∀ i, 0 ≤ h i ∧ h i < G.side) ∧
    x = siteOfInt fun i => G.offset i + (G.side : ℤ) * κ i + h i
def indices (n : ℕ) : Finset (Fin 4 → ℤ) :=
  Fintype.piFinset fun _ => Finset.Ico (0 : ℤ) ((n / G.side : ℕ) : ℤ)
structure Compatible (n : ℕ) : Prop where
  side_pos : 0 < G.side
  two_mul_side_dvd : 2 * G.side ∣ n
def sameParityIndices (n : ℕ) (κ : Fin 4 → ℤ) : Finset (Fin 4 → ℤ) :=
  open Classical in (G.indices n).filter fun κ' => ∀ i, (2 : ℤ) ∣ κ' i - κ i
def shift (A : Finset (Fin 4)) : CellGrid :=
  ⟨G.side, fun i => G.offset i + (open Classical in if i ∈ A then ((G.side : ℤ) - 1) / 2 else 0)⟩
end CellGrid
section Attachment
variable {n : ℕ} [NeZero n] (L : ℕ) [NeZero L]
def windowSeeds (bad : Finset (TorusBond (n * L))) (Yw : Finset (TorusSite (n * L)))
    (C : Finset (TorusSite n)) (Rw : Finset (TorusSite (n * L))) : Finset (TorusSite (n * L)) :=
  (bad.image Prod.fst ∪ Yw ∪ sitesInBlocks L C) ∩ Rw
open Classical in
def lowerAttached (r : ℕ) (X LC : Finset (TorusSite (n * L))) : Finset (TorusSite (n * L)) :=
  ((chainComponents (10 * r) X).filter fun K => (K ∩ LC).Nonempty).biUnion id
open Classical in
def upperAttached (r : ℕ) (X LC Rw : Finset (TorusSite (n * L))) : Finset (TorusSite (n * L)) :=
  ((chainComponents (10 * r) X).filter fun K =>
    (K ∩ LC).Nonempty ∨ ∃ u ∈ K, ∃ v, v ∉ Rw ∧ supDist u v ≤ 10 * r).biUnion id
open Classical in
def windowZone (r : ℕ) (θ : Finset (TorusSite (n * L))) (C deep : Finset (TorusSite n)) :
    Finset (TorusSite n) :=
  (C ∪ coreBlocks L r θ) ∩ deep
end Attachment
section Windows
variable (T : StageTower ℓ) (k : ℕ)
def upperZone (s : ℕ) {n : ℕ} [NeZero n] (C : Finset (TorusSite n))
    (bad : Finset (TorusBond (n * ℓ.side))) (Yw : Finset (TorusSite (n * ℓ.side)))
    (c : Finset (TorusSite n)) : Finset (TorusSite n) :=
  windowZone ℓ.side (stageRange T s)
    (upperAttached ℓ.side (stageRange T s)
      (windowSeeds ℓ.side bad Yw C (sitesInBlocks ℓ.side (interiorAtDepth (blockDepth T k s) c)))
      (sitesInBlocks ℓ.side C) (sitesInBlocks ℓ.side (interiorAtDepth (blockDepth T k s) c)))
    C (interiorAtDepth (blockDepth T k s) c)
def lowerZone (s : ℕ) {n : ℕ} [NeZero n] (C : Finset (TorusSite n))
    (bad : Finset (TorusBond (n * ℓ.side))) (Yw : Finset (TorusSite (n * ℓ.side)))
    (c : Finset (TorusSite n)) : Finset (TorusSite n) :=
  windowZone ℓ.side (stageRange T s)
    (lowerAttached ℓ.side (stageRange T s)
      (windowSeeds ℓ.side bad Yw C (sitesInBlocks ℓ.side (interiorAtDepth (blockDepth T k s) c)))
      (sitesInBlocks ℓ.side C))
    C (interiorAtDepth (blockDepth T k s) c)
def upperHull : (s n : ℕ) → [NeZero n] → MarkedSample ℓ s n → Finset (TorusSite n) →
    Finset (TorusSite n)
  | 0, n, _, W, c => (stageState T 0 n W).2.1 ∩ interiorAtDepth (windowDepth T k 0) c
  | s + 1, n, _, u, c =>
      interiorAtDepth (windowDepth T k (s + 1)) c ∩ thickening (stageRange T (s + 1) / 2)
        (upperZone T k s (hotCoreSites (T.stage s).toStepSetup u.2.2.1) u.2.2.2
          (upperHull s (n * ℓ.side) u.1 (sitesInBlocks ℓ.side c)) c)
def lowerHull : (s n : ℕ) → [NeZero n] → MarkedSample ℓ s n → Finset (TorusSite n) →
    Finset (TorusSite n)
  | 0, n, _, W, c => (stageState T 0 n W).2.1 ∩ interiorAtDepth (windowDepth T k 0) c
  | s + 1, n, _, u, c =>
      thickening (stageRange T (s + 1) / 2)
        (lowerZone T k s (hotCoreSites (T.stage s).toStepSetup u.2.2.1) u.2.2.2
          (lowerHull s (n * ℓ.side) u.1 (sitesInBlocks ℓ.side c)) c)
open Classical in
def lowerScore (s₀ s₁ : ℝ) : (s n : ℕ) → [NeZero n] → MarkedSample ℓ s n →
    Finset (TorusSite n) → TorusSite n → ℝ
  | 0, n, _, W, c, y => if y ∈ lowerHull T k 0 n W c then s₀ else 0
  | s + 1, n, _, u, c, y =>
      if y ∈ lowerHull T k (s + 1) n u c then
        s₁ + (if y ∈ lowerZone T k s (hotCoreSites (T.stage s).toStepSetup u.2.2.1) u.2.2.2
              (lowerHull T k s (n * ℓ.side) u.1 (sitesInBlocks ℓ.side c)) c then
            ∑ z ∈ sitesInBlocks ℓ.side {y},
              lowerScore s₀ s₁ s (n * ℓ.side) u.1 (sitesInBlocks ℓ.side c) z else 0)
      else 0
def lowerScoreSum (s₀ s₁ : ℝ) (s n : ℕ) [NeZero n] (u : MarkedSample ℓ s n)
    (c : Finset (TorusSite n)) : ℝ :=
  ∑ y ∈ lowerHull T k s n u c, lowerScore T k s₀ s₁ s n u c y
end Windows
section FreeComponents
variable {n : ℕ} [NeZero n]
open Classical in
def freeSupports (R : StepSetup) (C : Finset (TorusSite n))
    (bad : Finset (TorusBond (n * R.params.side))) (Yt : Finset (TorusSite (n * R.params.side))) :
    Finset (ClusterSupport R.params.side n) :=
  ((clusterComponents R.params.side R.range bad Yt C).filter fun X =>
      ¬ (X ∩ sitesInBlocks R.params.side C).Nonempty).image
    (supportOfComponent R.params.side bad Yt)
def freeSupportsAt (T : StageTower ℓ) (s n : ℕ) [NeZero n] (v : MarkedSample ℓ (s + 1) n) :
    Finset (ClusterSupport ℓ.side n) :=
  freeSupports (T.stage s).toStepSetup (hotCoreSites (T.stage s).toStepSetup v.2.2.1) v.2.2.2
    (stageState T s (n * ℓ.side) v.1).2.1
def IsLongWithin (L : ℕ) [NeZero L] (r g : ℕ) (θ : ClusterSupport L n)
    (Rw : Finset (TorusSite (n * L))) : Prop :=
  open Classical in
  ∃ K : Finset (TorusSite (n * L)), K ⊆ clusterSupportSites L θ ∩ Rw ∧ K.Nonempty ∧
    (∀ y ∈ K, ∀ z ∈ K, ChainConnected (10 * r) K y z) ∧ g ≤ 2 * siteDiameter K
def HasLongSupport (T : StageTower ℓ) (k j : ℕ) : (s n : ℕ) → [NeZero n] → MarkedSample ℓ s n →
    Finset (TorusSite n) → Prop
  | 0, _, _, _, _ => False
  | s + 1, n, _, u, c =>
      (s = j ∧ ∃ θ ∈ freeSupportsAt T s n u, IsLongWithin ℓ.side (stageRange T s)
        (windowLength T k s) θ (sitesInBlocks ℓ.side (interiorAtDepth (blockDepth T k s) c))) ∨
      HasLongSupport T k j s (n * ℓ.side) u.1 (sitesInBlocks ℓ.side c)
end FreeComponents
def stageHull (T : StageTower ℓ) (s n : ℕ) [NeZero n] (u : MarkedSample ℓ s n) :
    Finset (TorusSite n) :=
  (stageState T s n u).2.1
def CellEvent (T : StageTower ℓ) (k n : ℕ) [NeZero n] (u : MarkedSample ℓ k n)
    (c : Finset (TorusSite n)) : Prop :=
  (upperHull T k k n u c ∩ interiorAtDepth (8 * stageRange T k) c).Nonempty
structure IsTowerAtParametersMeasurable (Tb : ParameterAssignment) (y : ℝ) (T : StageTower (Tb.stepParameters y))
    (β : ℝ) (k : ℕ) : Prop where
  onFamily : IsTowerAtParameters Tb y T β k
  measurable : T.MarksMeasurable
end YangMills.Construction.CellWindows
end
