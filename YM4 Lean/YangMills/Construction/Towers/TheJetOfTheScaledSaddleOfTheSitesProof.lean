import YangMills.Construction.PeriodicOperators.BlockMatricesOfLocalOperatorFunctionsAndOfJets
import YangMills.Construction.PeriodicOperators.IndexSetsOfATower
import YangMills.Construction.PeriodicOperators.InverseOfAnInvertibleJetProof
import YangMills.Construction.PeriodicOperators.JetOfATransposeOfALocalOperatorFunction
import YangMills.Construction.Towers.AveragesOfTheScaledPictureAreLocal
import YangMills.Construction.Towers.TheJetOfTheScaledSaddleOfTheSites
import YangMills.Construction.Towers.ThreeOperatorsOfTheScaledPictureAreLocal
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.BackgroundJets.VertexSaddleJet
open YangMills.Construction.PeriodicOperators
open YangMills.Construction.PeriodicOperators.JetQuad (EqAsJet)
open RemainderJets
section Jets
variable {I I' : PeriodicData}
theorem eqAsJet_trans {δ : ℝ} {p : Fin 4 → ℂ} {T S R : JetQuad I I'} (hTS : EqAsJet δ p T S)
    (hSR : EqAsJet δ p S R) : EqAsJet δ p T R := by apply _root_.YangMills.Construction.PeriodicOperators.JetInverse.trans_eqAsJet <;> assumption
theorem eqAsJet_refl (δ : ℝ) (p : Fin 4 → ℂ) (T : JetQuad I I') : EqAsJet δ p T T :=
  ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩
theorem quotHom_add_add_neg_smul (M N : QuotHom I I') : M + N + (-1 : ℂ) • N = M := by
  refine LinearMap.ext fun f => funext fun c => ?_
  simp
theorem jetQuad_add_add_neg_smul (A C : JetQuad I I') :
    (A.add C).add (JetQuad.smul (-1) C) = A := by
  ext1 <;> funext κ <;> exact quotHom_add_add_neg_smul _ _
theorem jetQuad_zero_smul (A : JetQuad I I') : JetQuad.smul 0 A = JetQuad.zeroJet I I' := by
  ext1 <;> simp [JetQuad.smul, JetQuad.zeroJet]
end Jets
theorem blockJet_congr {J : Fin 2 → PeriodicData} {δ : ℝ} {p : Fin 4 → ℂ}
    {T S : ∀ i j, JetQuad (J j) (J i)} (h : ∀ i j, EqAsJet δ p (T i j) (S i j)) :
    EqAsJet δ p (blockJet J T) (blockJet J S) := by
  refine ⟨fun κ hκ => ?_, fun κ hκ => ?_, fun κ hκ => ?_, fun κ hκ => ?_⟩
  · show blockQuotHom J _ = blockQuotHom J _
    congr 1
    funext i j
    exact (h i j).1 hκ
  · show blockQuotHom J _ = blockQuotHom J _
    congr 1
    funext i j
    exact (h i j).2.1 hκ
  · show blockQuotHom J _ = blockQuotHom J _
    congr 1
    funext i j
    exact (h i j).2.2.1 hκ
  · show blockQuotHom J _ = blockQuotHom J _
    congr 1
    funext i j
    exact (h i j).2.2.2 hκ
abbrev vertexPair (L k : ℕ) : Fin 2 → PeriodicData := pairData (colourVertices L k 0) (colourVertices L k k)
def saddleEntries (L k : ℕ) : ∀ i j : Fin 2, ((remainderIndex L k).Carrier → ℂ) →
    (vertexPair L k i).Carrier → (vertexPair L k j).Carrier → ℂ
  | 0, 0 => fun f => (rescaledOperators L k (gaugeFieldOfForm L k f)).Delta
  | 0, 1 => fun f => (rescaledOperators L k (gaugeFieldOfForm L k f)).Rt
  | 1, 0 => fun f => (rescaledOperators L k (gaugeFieldOfForm L k f)).R
  | 1, 1 => fun _ _ _ => 0
theorem readOnSigma_eq_blockKernelFun (L k : ℕ) :
    readOnSigma (rescaledVertexSaddle L k) = blockKernelFun (vertexPair L k) (saddleEntries L k) := by
  funext f ι' ι
  obtain ⟨i, x⟩ := ι'
  obtain ⟨j, y⟩ := ι
  match i, j, x, y with
  | 0, 0, _, _ => rfl
  | 0, 1, _, _ => rfl
  | 1, 0, _, _ => rfl
  | 1, 1, _, _ => rfl
def smoothingKernelFun (L k : ℕ) : ((remainderIndex L k).Carrier → ℂ) →
    (colourVertices L k k).Carrier → (colourVertices L k 0).Carrier → ℂ :=
  fun f => (rescaledOperators L k (gaugeFieldOfForm L k f)).R
theorem localWithBlockJet_holds (hBlock : YangMills.Construction.PeriodicOperators.BlockJets.AllConditions)
    (hLocal : YangMills.Construction.PeriodicOperators.JetDomains.OpFunJetTheory)
    (hTranspose : YangMills.Construction.PeriodicOperators.TransposeJet.Claim)
    (hIndex : YangMills.Construction.PeriodicOperators.TowerIndexSets.Claim)
    (hThree : YangMills.Construction.Tower.FullSpace.ThreeLocalOperators.LocalEntireOperators)
    (hMeans : YangMills.Construction.Tower.FullSpace.ScaledMeansLocality.MeansAreLocal)
    (hConstants : YangMills.Construction.Tower.IteratedSmallFieldMeans.IteratedMeansClaim) :
    LocalWithBlockJet := by
  intro L hs k hk
  have hF : IsPeriodic (remainderIndex L k) := (hIndex L hs k 0 (Nat.zero_le k)).2.1
  have hS₀ : IsPeriodic (colourVertices L k 0) := (hIndex L hs k 0 (Nat.zero_le k)).1
  have hSk : IsPeriodic (colourVertices L k k) := (hIndex L hs k k le_rfl).1
  have hJ : ∀ b, IsPeriodic (vertexPair L k b) := fun b =>
    match b with
    | 0 => hS₀
    | 1 => hSk
  have hDelta := (hThree L hs k hk).2.2.1
  have hR : IsLocalOpFun (remainderIndex L k) (colourVertices L k 0)
      (colourVertices L k k) (smoothingKernelFun L k) := by
    obtain ⟨ρ, R, h, -⟩ := (hMeans L hs k hk _ _ (hConstants.1 L hs)).2
    exact ⟨ρ, R, h⟩
  have hRt := (hLocal.1 _ _ _ _ hF hS₀ hSk hSk).2.2 _ hR
  have hSquare := (hLocal.1 _ _ _ _ hF hS₀ hSk hSk).2.1 _ _ hR hRt
  have hAt : ∀ (δ : ℝ) (p : Fin 4 → ℂ), 0 < δ → p ∈ imStrip δ →
      ∀ εPlus εMinus : (remainderIndex L k).UnitQuot → ℂ,
      (∀ i j, IsLocalOpFun (remainderIndex L k) (vertexPair L k j) (vertexPair L k i)
        (saddleEntries L k i j)) ∧
      (∀ i j, EqAsJet δ p (jetAlong (remainderIndex L k) (vertexPair L k j) (vertexPair L k i)
        (saddleEntries L k i j) p εPlus εMinus)
        (saddleBlocks p (jetAlong (remainderIndex L k) (colourVertices L k 0) (colourVertices L k 0)
            (fun f => (rescaledOperators L k (gaugeFieldOfForm L k f)).Delta) p εPlus εMinus)
          (jetAlong (remainderIndex L k) (colourVertices L k 0) (colourVertices L k k)
            (smoothingKernelFun L k) p εPlus εMinus) i j)) := by
    intro δ p hδ hp εPlus εMinus
    have hMul := (hBlock.2 _ hF δ p hδ hp εPlus εMinus).1 _ _ hSk hSk _ hSquare 0
    have hZero : (fun ζ => (0 : ℂ) • opFunComp (smoothingKernelFun L k)
        (opFunTranspose (smoothingKernelFun L k)) ζ) = saddleEntries L k 1 1 := by
      funext ζ
      rw [zero_smul]
      rfl
    rw [hZero] at hMul
    refine ⟨fun i j => ?_, fun i j => ?_⟩
    · match i, j with
      | 0, 0 => exact hDelta
      | 0, 1 => exact hRt
      | 1, 0 => exact hR
      | 1, 1 => exact hMul.1
    · match i, j with
      | 0, 0 => exact eqAsJet_refl _ _ _
      | 0, 1 => exact hTranspose δ p hδ hp _ _ _ hF hSk hS₀ εPlus εMinus _ hR
      | 1, 0 => exact eqAsJet_refl _ _ _
      | 1, 1 =>
        have h := hMul.2
        rw [jetQuad_zero_smul] at h
        exact h
  have hBlocks : ∀ (δ : ℝ) (p : Fin 4 → ℂ), 0 < δ → p ∈ imStrip δ →
      ∀ εPlus εMinus : (remainderIndex L k).UnitQuot → ℂ,
      IsLocalOpFun (remainderIndex L k) (PeriodicData.sigma (vertexPair L k))
        (PeriodicData.sigma (vertexPair L k)) (readOnSigma (rescaledVertexSaddle L k)) ∧
      EqAsJet δ p (jetAlong (remainderIndex L k) (PeriodicData.sigma (vertexPair L k))
          (PeriodicData.sigma (vertexPair L k)) (readOnSigma (rescaledVertexSaddle L k)) p εPlus εMinus)
        (saddleJet p (jetAlong (remainderIndex L k) (colourVertices L k 0) (colourVertices L k 0)
            (fun f => (rescaledOperators L k (gaugeFieldOfForm L k f)).Delta) p εPlus εMinus)
          (jetAlong (remainderIndex L k) (colourVertices L k 0) (colourVertices L k k)
            (smoothingKernelFun L k) p εPlus εMinus)) := by
    intro δ p hδ hp εPlus εMinus
    obtain ⟨hl, hj⟩ := hAt δ p hδ hp εPlus εMinus
    have h := (hBlock.2 _ hF δ p hδ hp εPlus εMinus).2.1 _ hJ |>.2.2 (saddleEntries L k) hl
    rw [readOnSigma_eq_blockKernelFun]
    exact ⟨h.1, eqAsJet_trans h.2 (blockJet_congr hj)⟩
  refine ⟨(hBlocks 1 0 one_pos (by simp [imStrip]) 0 0).1, ?_⟩
  intro δ p μPlus μMinus hδ hp
  have h := (hBlocks δ p hδ hp (scaledResponseField L k p μPlus) (scaledResponseField L k (-p) μMinus)).2
  have hY : subGramJet p (vertexMiddleJet L k p μPlus μMinus) (vertexSmoothingJet L k p μPlus μMinus) =
      vertexOperatorJet L k p μPlus μMinus :=
    jetQuad_add_add_neg_smul _ _
  rw [hY]
  exact h
end YangMills.Construction.Tower.FullSpace.BackgroundJets.VertexSaddleJet
end
