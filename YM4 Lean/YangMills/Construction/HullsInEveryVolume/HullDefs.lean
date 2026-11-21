import YangMills.Construction.FreeEnergiesOfTheFlow.TheFlowLiesInATowerOfImages
import YangMills.Construction.ResponseInTheExpansion.PairsAtALevel
import YangMills.Construction.ResponseInTheExpansion.TheResponseReturns
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.HullTrees
open TorusFields TorusLumps RenormalizationStepParameters StepSettings StepReturn WeightedResponses ColdStepAtMirrorFrames FreeEnergies
def unitDecayRate (Tb : ParameterAssignment) : ℝ := (1 / 4) * min (Tb.κ * Tb.threshold ^ 2) Tb.cE
def separatedUnitRate (Tb : ParameterAssignment) : ℝ := unitDecayRate Tb / (2 ^ 13 * (Tb.side : ℝ) ^ 4)
def hullDecayRate (Tb : ParameterAssignment) : ℝ :=
  min (separatedUnitRate Tb / 10 ^ 4) (Real.log Tb.side / (4 * Tb.B))
def treeBranching (L : ℕ) : ℕ := L / 100
def levelWeight (j : ℕ) : ℝ := 3 / Real.pi ^ 2 / ((j : ℝ) + 1) ^ 2
def minLeafCount (L j : ℕ) : ℕ := ⌈max 1 (levelWeight j * (treeBranching L : ℝ) ^ j)⌉₊
def minLeafCountScaled (L j m : ℕ) : ℕ := minLeafCount L j * ⌈levelWeight j * (m : ℝ)⌉₊
def EventuallyInParameters (P : ParameterAssignment → ResponseParameters → ℝ → Prop) : Prop :=
  ∀ a : ℝ, 1 ≤ a → ∃ (L₀ : ℕ) (rt₀ : ChainParameters → ℝ) (C₀ : ℝ), (∀ c, 0 < rt₀ c) ∧ ∀ L : ℕ, Odd L → L₀ ≤ L →
    ∀ Tb : ParameterAssignment, Tb.coupling = a → Tb.side = L → Tb.Admissible → Tb.ColdStepHolds →
      Tb.HoldsFrom ColdRegimeEstimatesAt → Tb.rt ≤ rt₀ Tb.toChainParameters →
      C₀ ≤ Tb.derivBound → ∃ M : ℝ, ∀ Kr : ResponseParameters, M ≤ Kr.Kc → Kr.η₃ = Tb.η₃ → Kr.N₀ = Tb.N 0 →
        (∀ y : ℝ, Kr.Admissible (Tb.stepParameters y)) →
        (∃ Cs y₁ : ℝ, 0 ≤ Cs ∧ ∀ y : ℝ, y₁ ≤ y → ReturnsAtParameters Tb Kr Cs y) →
        ∃ y₀ : ℝ, ∀ y : ℝ, y₀ ≤ y → ExpansionReturnsAt (Tb.stepParameters y) →
          (∀ β : ℝ, y ≤ β → HasExpansion (Tb.stepParameters y) 0 β (wilsonWeight β)) → P Tb Kr y
def IsFirstCrossing (ℓ : TorusLumps.StepParameters) (Ξ β : ℝ) (K : ℕ) : Prop :=
  (couplingFlow ℓ β K).1 ≤ Ξ ∧ ∀ k < K, Ξ < (couplingFlow ℓ β k).1
def windowUpper (ℓ : TorusLumps.StepParameters) (g : ℝ) : ℝ := (g ^ 2)⁻¹ + 2 * ℓ.B
def torusSideAtLevel (L K m u : ℕ) : ℕ := fineSide L (K - u) (2 * L ^ m)
structure FlowCrossing (Tb : ParameterAssignment) (y g β : ℝ) (K : ℕ) : Prop where
  g_pos : 0 < g
  le_inv_sq : y ≤ (g ^ 2)⁻¹
  upper_le : windowUpper (Tb.stepParameters y) g ≤ β
  isFirst : IsFirstCrossing (Tb.stepParameters y) (windowUpper (Tb.stepParameters y) g) β K
structure CrossingVolume (Tb : ParameterAssignment) (y g β : ℝ) (K m : ℕ) : Prop extends FlowCrossing Tb y g β K where
  volume_le : Tb.side * Tb.n₀ ≤ 2 * Tb.side ^ m
structure HullChain (Tb : ParameterAssignment) (y g β : ℝ) (K m : ℕ) (T : StageTower (Tb.stepParameters y)) : Prop
    extends CrossingVolume Tb y g β K m where
  follows : TowerFollowsFlow T β K
  depth_bottom : T.base.depth = 0
  functional_bottom : T.base.functional = wilsonWeight β
  anchor_bottom : T.base.anchorRadius = Tb.ρA
  cutoff_bottom : IsCutoff ((Tb.stepParameters y).threshold / 64) T.base.barrierFn
  marks : T.MarksMeasurable
  expansions : ∀ j ≤ K, (T.stage j).toStepSetup.HasExpansions
  reads_flow : IsImageTower Tb y T β K
structure HullChainAtLevel (Tb : ParameterAssignment) (y g β : ℝ) (K m : ℕ) (T : StageTower (Tb.stepParameters y))
    (u n : ℕ) : Prop where
  chain : HullChain Tb y g β K m T
  le : u ≤ K
  side_eq : n = torusSideAtLevel Tb.side K m u
variable {ℓ : TorusLumps.StepParameters}
def stageCoupling (T : StageTower ℓ) (u : ℕ) : ℝ := (T.stage u).coupling
def stageRange (T : StageTower ℓ) (u : ℕ) : ℕ := clusterRange (T.stage u).coupling
def hullSet (T : StageTower ℓ) (u n : ℕ) [NeZero n] (w : MarkedSample ℓ u n) : Finset (TorusSite n) :=
  (stageState T u n w).2.1
def labelSize (T : StageTower ℓ) (s₁ : ℝ) : (t : ℕ) → (T.stage t).labels.Ω → ℝ
  | 0, _ => 0
  | t + 1, ω => coarseLabelScore s₁ (labelSize T s₁ t) ω
def siteSize (T : StageTower ℓ) (s₁ : ℝ) (u n : ℕ) [NeZero n] (w : MarkedSample ℓ u n) (y : TorusSite n) : ℝ :=
  siteScore (labelSize T s₁ u) (stageState T u n w).2.1 (stageState T u n w).2.2 y
def totalSize (T : StageTower ℓ) (s₁ : ℝ) (u n : ℕ) [NeZero n] (w : MarkedSample ℓ u n) : ℝ :=
  ∑ y : TorusSite n, siteSize T s₁ u n w y
variable {n : ℕ}
open Classical in
def hullClass (r : ℕ) (Y : Finset (TorusSite n)) (y : TorusSite n) : Finset (TorusSite n) :=
  Y.filter (ChainConnected r Y y)
def supDiam (X : Finset (TorusSite n)) : ℕ := X.sup fun a => X.sup fun b => supDist a b
def box [NeZero n] (y : TorusSite n) (m : ℕ) : Finset (TorusSite n) := thickening m {y}
def ContainsHotPlaquette (ℓ : TorusLumps.StepParameters) [NeZero n] (W : TorusField n) (B : Finset (TorusSite n)) : Prop :=
  ∃ p ∈ plaquettesIn B, ℓ.threshold ≤ curvature W p.1 p.2.1 p.2.2
def ContainsBadBlock (ℓ : TorusLumps.StepParameters) : (u n : ℕ) → MarkedSample ℓ u n → Finset (TorusSite n) → Prop
  | 0, _, _, _ => False
  | _ + 1, n, w, B => ∃ b : TorusBond (n * ℓ.side),
      b ∈ (show Finset (TorusBond (n * ℓ.side)) from w.2.2.2) ∧ parentBlock ℓ.side b.1 ∈ B
def IsUnit (T : StageTower ℓ) (u n : ℕ) [NeZero n] (w : MarkedSample ℓ u n) (z : TorusSite n) : Prop :=
  ContainsHotPlaquette ℓ (topField ℓ u n w) (box z (4 * stageRange T u)) ∨
    ContainsBadBlock ℓ u n w (box z (4 * stageRange T u))
def Separated (d : ℕ) (S : Finset (TorusSite n)) : Prop := ∀ a ∈ S, ∀ b ∈ S, a ≠ b → d ≤ supDist a b
def HasSeparatedChildren (T : StageTower ℓ) (k : ℕ) : (u n : ℕ) → [NeZero n] → MarkedSample ℓ u n → TorusSite n → Prop
  | 0, _, _, _, _ => False
  | u + 1, n, _, w, y => ∃ S : Finset (TorusSite (n * ℓ.side)), S.card = k ∧ S ⊆ hullSet T u (n * ℓ.side) w.1 ∧
      (∀ z ∈ S, parentBlock ℓ.side z ∈ box y (2 * stageRange T (u + 1))) ∧ Separated (40 * stageRange T u) S
inductive SiteTree (L : ℕ) : ℕ → ℕ → Type
  | leaf {u n : ℕ} (y : TorusSite n) : SiteTree L u n
  | node {u n : ℕ} (y : TorusSite n) (k : ℕ) (kids : Fin k → SiteTree L u (n * L)) : SiteTree L (u + 1) n
def SiteTree.root {L u n : ℕ} : SiteTree L u n → TorusSite n
  | .leaf y => y
  | .node y _ _ => y
def SiteTree.Embeds (T : StageTower ℓ) (k : ℕ) : {u n : ℕ} → [NeZero n] → SiteTree ℓ.side u n → MarkedSample ℓ u n → Prop
  | u, n, _, .leaf y, w => y ∈ hullSet T u n w ∧ IsUnit T u n w y
  | u + 1, n, _, .node y k' kids, w => y ∈ hullSet T (u + 1) n w ∧ k' = k ∧
      (∀ i, parentBlock ℓ.side (kids i).root ∈ box y (2 * stageRange T (u + 1))) ∧
      (∀ i i', i ≠ i' → 40 * stageRange T u ≤ supDist (kids i).root (kids i').root) ∧
      ∀ i, SiteTree.Embeds T k (kids i) w.1
def SiteTree.leafWeight {L : ℕ} (k : ℕ) : {u n : ℕ} → SiteTree L u n → ℝ
  | _, _, .leaf _ => 1
  | _, _, .node _ k' kids => (∑ i : Fin k', SiteTree.leafWeight k (kids i)) / (k : ℝ)
def SiteTree.leavesAtDepth {L : ℕ} : {u n : ℕ} → SiteTree L u n → ℕ → ℕ
  | _, _, .leaf _, 0 => 1
  | _, _, .leaf _, _ + 1 => 0
  | _, _, .node _ _ _, 0 => 0
  | _, _, .node _ k' kids, j + 1 => ∑ i : Fin k', SiteTree.leavesAtDepth (kids i) j
open Classical in
def SiteTree.leafSites {L : ℕ} : {u n : ℕ} → SiteTree L u n → (j : ℕ) → Finset (TorusSite (fineSide L j n))
  | _, _, .leaf y, 0 => {y}
  | _, _, .leaf _, _ + 1 => ∅
  | _, _, .node _ _ _, 0 => ∅
  | _, _, .node _ _ kids, j + 1 => Finset.univ.biUnion fun i => SiteTree.leafSites (kids i) j
def UnitsAtDepth (T : StageTower ℓ) :
    (j u n : ℕ) → [NeZero n] → MarkedSample ℓ u n → Finset (TorusSite (fineSide ℓ.side j n)) → Prop
  | 0, u, n, _, w, S => ∀ z ∈ S, IsUnit T u n w z
  | _ + 1, 0, _, _, _, _ => False
  | j + 1, u + 1, n, _, w, S => UnitsAtDepth T j u (n * ℓ.side) w.1 S
end YangMills.Construction.HullTrees
end
