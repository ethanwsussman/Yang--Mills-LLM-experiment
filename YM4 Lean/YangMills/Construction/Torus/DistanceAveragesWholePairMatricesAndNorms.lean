import YangMills.Construction.Torus.AveragingOperatorAndMatrices
import YangMills.Construction.Torus.StandardPartitionsLayersBlocksAndBalls
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Weighted
namespace TorusData
variable {T : TorusData}
def bareShift (p : T.BareSite) (v : Fin 4 → ℤ) : T.BareSite :=
  ⟨T.shiftedSite p v, by
    obtain ⟨n, hn⟩ := p.2
    refine ⟨n + v, ?_⟩
    rw [TorusData.shiftedSite, hn]
    funext i
    simp [TorusMetric.torusProj, mul_add]⟩
def bareLap (u : T.BareSite → ℝ) (p : T.BareSite) : ℝ :=
  (T.scale 0 ^ 2)⁻¹ * ∑ i : Fin 4,
    (2 * u p - u (bareShift p (Pi.single i 1)) - u (bareShift p (Pi.single i (-1))))
end TorusData
def AvgWeightClosedForm (L : ℕ) : Prop :=
  (∀ n : ℕ, 1 ≤ n →
    avgWeight L n = (1 - ((L : ℝ) ^ 2)⁻¹) / (1 - ((L : ℝ) ^ (2 * n))⁻¹)) ∧
  ∀ n : ℕ, 1 - ((L : ℝ) ^ 2)⁻¹ < avgWeight L n ∧ avgWeight L n ≤ 1
namespace SeparatedChain
variable {T : TorusData} (C : SeparatedChain T)
def baseStar : Set T.Bond := TorusData.bondsMeeting (T.bareSites (C.stage 0))
def WeightedDistanceSymmTriangle : Prop :=
  (∀ p q : T.Space, C.weightedDistance p q = C.weightedDistance q p) ∧
  ∀ p q r : T.Space,
    C.weightedDistance p r ≤ C.weightedDistance p q + C.weightedDistance q r
def AvgAndAdjointFormulas : Prop :=
  (∀ (u : ↥C.bareSpace) (s : ↥C.allSites),
    C.avgOp u s =
      C.siteScale s ^ (-4 : ℤ) * C.bareInner (C.blockIndicator s) (u : T.BareSite → ℝ)) ∧
  (∀ (u : ↥C.bareSpace) (s : ↥C.allSites) (p : T.BareSite),
    (s : T.Space) ∈ C.layerSites 0 → (p : T.Space) = s →
      C.avgOp u s = (u : T.BareSite → ℝ) p) ∧
  (∀ (u : ↥C.bareSpace) (v : C.LayerFn),
    C.layerInner (C.avgOp u) v =
      C.bareInner (u : T.BareSite → ℝ)
        fun p => ∑ᶠ s : ↥C.allSites, v s * C.blockIndicator s p) ∧
  (∀ (u : ↥C.bareSpace) (v : C.LayerFn),
    C.layerInner (C.avgOp u) v = C.bareInner u (C.avgOpAdjoint v)) ∧
  (∀ v : C.LayerFn,
    (C.avgOpAdjoint v : T.BareSite → ℝ) =
      fun p => ∑ᶠ s : ↥C.allSites, v s * C.blockIndicator s p) ∧
  ∀ v : C.LayerFn, ∀ p ∈ T.bareSites (C.stage 0),
    (C.avgOpAdjoint v : T.BareSite → ℝ) p = C.layerEval v (C.blockCenter p)
def WeightedAvgQuadratic : Prop :=
  (∀ u u' : ↥C.bareSpace,
    C.bareInner u' (C.weightedAvg u) =
      ∑ᶠ s : ↥C.allSites, avgWeight T.L (C.level s) * C.siteScale s ^ 2 *
        (C.avgOp u' s * C.avgOp u s)) ∧
  (∀ u v : ↥C.bareSpace,
    C.bareInner (C.weightedAvg u) v = C.bareInner u (C.weightedAvg v)) ∧
  ∀ u : ↥C.bareSpace, C.avgOp u = 0 → C.weightedAvg u = 0
def DirichletLapOnBase : Prop :=
  ∀ u : ↥C.bareSpace, ∀ p ∈ T.bareSites (C.stage 0),
    (C.dirichletLap u : T.BareSite → ℝ) p = TorusData.bareLap (u : T.BareSite → ℝ) p
def BasePairFacts : Prop :=
  C.IsAdmissiblePair (C.stage 0) C.baseStar ∧
  C.sitesIn (C.stage 0) = C.allSites ∧
  C.bareSpaceOn (C.stage 0) = C.bareSpace ∧
  C.layerSpaceOn (C.stage 0) = ⊤ ∧
  (∀ u : ↥(C.bareSpaceOn (C.stage 0)),
    (C.admissibleOp (C.stage 0) C.baseStar u : T.BareSite → ℝ) =
      C.weightedLap (C.bareSpaceOnIncl (C.stage 0) u)) ∧
  (∀ u : ↥(C.bareSpaceOn (C.stage 0)),
    (C.admissibleGreen (C.stage 0) C.baseStar u : T.BareSite → ℝ) =
      C.greenOp (C.bareSpaceOnIncl (C.stage 0) u)) ∧
  (∀ v : ↥(C.layerSpaceOn (C.stage 0)),
    (C.admissibleAvgGreenSq (C.stage 0) C.baseStar v : C.LayerFn) =
      C.avgGreenSq (v : C.LayerFn)) ∧
  ∀ v : ↥(C.layerSpaceOn (C.stage 0)),
    (C.admissibleScaledGreenSq (C.stage 0) C.baseStar v : C.LayerFn) =
      C.scaledGreenSq (v : C.LayerFn)
def AdmissiblePairSymm : Prop :=
  ∀ (W : Set T.Space) (b : Set T.Bond), C.IsAdmissiblePair W b →
    (∀ u v : ↥(C.bareSpaceOn W),
      C.bareInner (C.admissibleGreen W b u) v =
        C.bareInner u (C.admissibleGreen W b v)) ∧
    (∀ v v' : ↥(C.layerSpaceOn W),
      C.layerInner (C.admissibleAvgGreenSq W b v) v' =
        C.layerInner v (C.admissibleAvgGreenSq W b v')) ∧
    (∀ v v' : ↥(C.layerSpaceOn W),
      C.layerInner (C.admissibleScaledGreenSq W b v) v' =
        C.layerInner v (C.admissibleScaledGreenSq W b v')) ∧
    ∀ s s' : ↥C.allSites, (s : T.Space) ∈ C.sitesIn W → (s' : T.Space) ∈ C.sitesIn W →
      ∃ (hs : C.blockIndicator s ∈ C.bareSpaceOn W)
        (hs' : C.blockIndicator s' ∈ C.bareSpaceOn W),
        C.matrixOf (C.extendByZeroFromBlocks W (C.admissibleScaledGreenSq W b)) s s' =
          C.siteScale s ^ (-4 : ℤ) * C.siteScale s' ^ (-4 : ℤ) *
            C.bareInner (C.admissibleGreen W b ⟨C.blockIndicator s, hs⟩)
              (C.admissibleGreen W b ⟨C.blockIndicator s', hs'⟩)
def LayerMatrixCalculus : Prop :=
  (∀ s : ↥C.allSites, C.layerInner (C.basisVec s) (C.basisVec s) = 1) ∧
  (∀ s s' : ↥C.allSites, s ≠ s' →
    C.layerInner (C.basisVec s) (C.basisVec s') = 0) ∧
  Submodule.span ℝ (range C.basisVec) = ⊤ ∧
  (∀ (K : C.LayerOp) (s s' : ↥C.allSites),
    C.matrixOf K s s' =
      C.siteScale s ^ 2 * C.kernel K s s' * C.siteScale s' ^ (-2 : ℤ)) ∧
  (∀ (K K' : C.LayerOp) (s s' : ↥C.allSites),
    C.matrixOf (K ∘ₗ K') s s' =
      ∑ᶠ s'' : ↥C.allSites, C.matrixOf K s s'' * C.matrixOf K' s'' s') ∧
  (∀ (K : C.LayerOp) (m m' : ↥C.allSites → ℝ) (s s' : ↥C.allSites),
    C.matrixOf (C.mulOp m ∘ₗ K ∘ₗ C.mulOp m') s s' =
      m s * C.matrixOf K s s' * m' s') ∧
  (∀ m m' : ↥C.allSites → ℝ,
    C.mulOp m ∘ₗ C.mulOp m' = C.mulOp m' ∘ₗ C.mulOp m) ∧
  (∀ (m : ↥C.allSites → ℝ) (k : ℕ),
    Commute (C.mulOp m : Module.End ℝ C.LayerFn) (C.scaleOnLayer ^ k)) ∧
  (∀ (m : ↥C.allSites → ℝ) (k : ℕ),
    Commute (C.mulOp m : Module.End ℝ C.LayerFn) (Ring.inverse C.scaleOnLayer ^ k)) ∧
  (∀ K : C.LayerOp,
    (∀ v v' : C.LayerFn, C.layerInner (K v) v' = C.layerInner v (K v')) ↔
      ∀ s s' : ↥C.allSites, C.matrixOf K s s' = C.matrixOf K s' s) ∧
  (∀ (K : C.LayerOp) (v v' : C.LayerFn),
    C.layerInner v (K v') =
      ∑ᶠ s : ↥C.allSites, ∑ᶠ s' : ↥C.allSites,
        (C.siteScale s ^ 2 * v s) * C.matrixOf K s s' *
          (C.siteScale s' ^ 2 * v' s')) ∧
  ∀ v : C.LayerFn,
    ∑ᶠ s : ↥C.allSites, (C.siteScale s ^ 2 * v s) ^ 2 = C.layerSpaceNorm v ^ 2
def MatrixNormRules : Prop :=
  (∀ (M M' : C.LayerMat) (δ δ' : ℝ), 0 ≤ δ' → δ' ≤ δ →
    C.expWeightedMatrixNorm δ (matProd M M') ≤
        C.expWeightedMatrixNorm δ M * C.expWeightedMatrixNorm δ M' ∧
    C.expWeightedMatrixNorm δ' M ≤ C.expWeightedMatrixNorm δ M ∧
    (∀ s s' : ↥C.allSites,
      |M s s'| ≤ C.expWeightedMatrixNorm δ M * Real.exp (-δ * C.weightedDistance s s')) ∧
    ((∀ s s' : ↥C.allSites, |M s s'| ≤ M' s s') →
      C.expWeightedMatrixNorm δ M ≤ C.expWeightedMatrixNorm δ M') ∧
    ∀ a a' : ↥C.allSites → ℝ,
      |∑ᶠ s : ↥C.allSites, ∑ᶠ s' : ↥C.allSites, a s * M s s' * a' s'| ≤
        C.expWeightedMatrixNorm 0 M * Real.sqrt (∑ᶠ s : ↥C.allSites, a s ^ 2) *
          Real.sqrt (∑ᶠ s : ↥C.allSites, a' s ^ 2)) ∧
  ∀ (K : C.LayerOp) (v : C.LayerFn),
    C.layerSpaceNorm (K v) ≤ C.expWeightedOpNorm 0 K * C.layerSpaceNorm v
end SeparatedChain
def DistanceAvgPairMatrixNormFacts : Prop :=
  ∀ (T : TorusData) (C : SeparatedChain T), (C.stage 0).Nonempty →
    C.WeightedDistanceSymmTriangle ∧
    C.AvgAndAdjointFormulas ∧
    C.WeightedAvgQuadratic ∧
    AvgWeightClosedForm T.L ∧
    C.DirichletLapOnBase ∧
    C.BasePairFacts ∧
    C.AdmissiblePairSymm ∧
    C.LayerMatrixCalculus ∧
    C.MatrixNormRules
end YangMills.Construction.Weighted
