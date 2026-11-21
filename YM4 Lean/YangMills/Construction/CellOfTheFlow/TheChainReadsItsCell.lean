import YangMills.Construction.CellOfTheFlow.NoiseOfTheChain
import YangMills.Construction.ResponseInTheExpansion.PairsAtALevel
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.CellWindows
open TorusLumps TorusFields WeightedResponses RenormalizationStepParameters StepSettings
structure DeterminedDeepIn {q : StepParameters} (T : StageTower q) (S : ChainSampler T) (k s n : ℕ) [NeZero n]
    (c : Finset (TorusSite n)) (U U' : TorusField (fineSide q.side s n)) (ξ ξ' : ChainNoise q s n) : Prop where
  link_eq : ∀ b : TorusBond n, b.1 ∈ interiorAtDepth 8 c → b.1 + unitStep n b.2 ∈ interiorAtDepth 8 c →
    topField q s n (sampleChain T S s n U ξ) b.1 b.2 = topField q s n (sampleChain T S s n U' ξ') b.1 b.2
  hot_iff : ∀ z ∈ interiorAtDepth (stageRange T s) c, (z ∈ torusHotSites q (topField q s n (sampleChain T S s n U ξ)) ↔
    z ∈ torusHotSites q (topField q s n (sampleChain T S s n U' ξ')))
def chainLocalityStatement : Prop :=
  HoldsAtAdmissibleParameters fun P y => ∀ (T : StageTower (P.stepParameters y)) (S : ChainSampler T) (β : ℝ) (k : ℕ),
    IsTowerAtParametersMeasurable P y T β k → (∀ s, (S s).IsFaithful) →
    (∀ (s : ℕ), s ≤ k → ∀ (m : ℕ) [NeZero m] (G : CellGrid) (i : Fin 4 → ℤ), G.Compatible m →
      ∀ (U U' : TorusField (fineSide (P.stepParameters y).side s m)) (ξ ξ' : ChainNoise (P.stepParameters y) s m),
        FieldsAgreeOn (cellBelow (P.stepParameters y).side s m (G.cell m i)) U U' →
        NoiseAgreesOn (P.stepParameters y) s m (G.cell m i) ξ ξ' →
        DeterminedDeepIn T S k s m (G.cell m i) U U' ξ ξ') ∧
    (∀ (m : ℕ) [NeZero m] (G : CellGrid) (i : Fin 4 → ℤ), G.Compatible m → ∀ (U U' : TorusField m),
      FieldsAgreeOn (G.cell m i) U U' → ∀ z ∈ interiorAtDepth (windowDepth T k 0) (G.cell m i),
        (z ∈ stageHull T 0 m U ↔ z ∈ stageHull T 0 m U')) ∧
    ∀ (s : ℕ), s < k → ∀ (m : ℕ) [NeZero m] (G : CellGrid) (i : Fin 4 → ℤ), G.Compatible m →
      ∀ (U U' : TorusField (fineSide (P.stepParameters y).side (s + 1) m))
        (ξ ξ' : ChainNoise (P.stepParameters y) (s + 1) m),
        FieldsAgreeOn (cellBelow (P.stepParameters y).side (s + 1) m (G.cell m i)) U U' →
        NoiseAgreesOn (P.stepParameters y) (s + 1) m (G.cell m i) ξ ξ' →
        (∀ z ∈ interiorAtDepth (4 * stageRange T (s + 1)) (G.cell m i),
          (z ∈ hotCoreSites (T.stage s).toStepSetup (sampleChain T S (s + 1) m U ξ).2.2.1 ↔
            z ∈ hotCoreSites (T.stage s).toStepSetup (sampleChain T S (s + 1) m U' ξ').2.2.1)) ∧
        ∀ b : TorusBond (m * (P.stepParameters y).side),
          b.1 ∈ sitesInBlocks (P.stepParameters y).side (interiorAtDepth (blockDepth T k s) (G.cell m i)) →
          (b ∈ (show Finset (TorusBond (m * (P.stepParameters y).side)) from
              (sampleChain T S (s + 1) m U ξ).2.2.2) ↔
            b ∈ (show Finset (TorusBond (m * (P.stepParameters y).side)) from
              (sampleChain T S (s + 1) m U' ξ').2.2.2))
end YangMills.Construction.CellWindows
end
