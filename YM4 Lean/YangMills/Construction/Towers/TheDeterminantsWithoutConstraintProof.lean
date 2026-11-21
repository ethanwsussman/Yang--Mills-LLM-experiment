import YangMills.Construction.PeriodicOperators.JetOfALocalOperatorFunctionIsEntire
import YangMills.Construction.Towers.TheDeterminantsWithoutConstraint
import YangMills.Construction.Towers.TheMiddleJetsOfTheRemainderAreInvertible
import YangMills.Construction.Towers.TheNumbersOfTheStripOfTheFreeOperatorsAreAdmitted
import YangMills.Construction.Towers.TheOperatorFunctionsOfTheScaledPictureAndTheirJets
import YangMills.Construction.Towers.TheOperatorJetsAreSaddleJets
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.BackgroundJets.RemainderJets.UnconstrainedDeterminants
open YangMills.Construction.PeriodicOperators
open YangMills.Construction.PeriodicOperators.JetQuad
theorem stripHalfWidth_nonneg
    (h : YangMills.Construction.Tower.FreeStrip.ConstantsAdmissible.ConstantsAreAdmissible) :
    0 ≤ stripHalfWidth := by
  obtain ⟨-, -, δ₀, hδ₀, C₀, -, hI, -, -⟩ := h
  have hdom := Part.dom_iff_mem.mpr ⟨δ₀, hδ₀⟩
  rw [Part.mem_unique (stripHalfWidth_mem hdom) hδ₀]
  exact hI.1.le
theorem saddleBlocks_invertible_and_logNumber_add
    (hMid : YangMills.Construction.Tower.FullSpace.BackgroundJets.RemainderJets.MiddleJetsInvertible.MiddleJetsInvertibleClaim)
    (hSad : YangMills.Construction.PeriodicOperators.SaddleJetNumber.Claim)
    (hOp : YangMills.Construction.Tower.FullSpace.ScaledOperatorFunctions.ScaledOperatorFunctionsClaim)
    (hIter : YangMills.Construction.Tower.IteratedSmallFieldMeans.IteratedMeansClaim)
    (hEnt : YangMills.Construction.PeriodicOperators.LocalJetEntire.Claim)
    {L k : ℕ} (hs : YangMills.Construction.Conventions.IsAdmissibleBlockingFactor L) (hk : 1 ≤ k)
    {p : Fin 4 → ℂ} (hp : p ∈ momentumPolydisc stripHalfWidth) (μPlus μMinus : Fin 4) :
    (IsInvertibleJet stripHalfWidth p (edgeSaddleJet L k p μPlus μMinus) ∧
        logNumber p (edgeSaddleJet L k p μPlus μMinus) =
          logNumber p (edgeMiddleJet L k p μPlus μMinus) +
            logNumber p (edgeConstraintJet L k p μPlus μMinus)) ∧
      IsInvertibleJet stripHalfWidth p (vertexSaddleJet L k p μPlus μMinus) ∧
        logNumber p (vertexSaddleJet L k p μPlus μMinus) =
          logNumber p (vertexMiddleJet L k p μPlus μMinus) +
            logNumber p (vertexConstraintJet L k p μPlus μMinus) := by
  obtain ⟨C, hC⟩ := hMid
  obtain ⟨-, hΞ, hY, hCb, hCs⟩ := hC L hs k hk p hp μPlus μMinus
  have hδ : 0 < stripHalfWidth := hΞ.1.isJet.pos_width
  have hpS : p ∈ imStrip stripHalfWidth := hΞ.1.isJet.mem_imStrip
  obtain ⟨hO, -⟩ := hOp.1 L hs k hk
  obtain ⟨hS0, hB0, -, hSk, hBk⟩ := hO.periodic
  have hN := hIter.1 L hs
  obtain ⟨ρ, R, hB, -⟩ := hO.Q_local _ _ hN
  obtain ⟨ρ', R', hR, -⟩ := hO.R_local _ _ hN
  have hQ : JetQuad.IsJet stripHalfWidth p (edgeSmoothingJet L k p μPlus μMinus) :=
    (hEnt _ _ _ hB0 hB0 hBk _ ⟨ρ, R, hB⟩).2.2.2 _ hδ p hpS _ _
  have hRj : JetQuad.IsJet stripHalfWidth p (vertexSmoothingJet L k p μPlus μMinus) :=
    (hEnt _ _ _ hB0 hS0 hSk _ ⟨ρ', R', hR⟩).2.2.2 _ hδ p hpS _ _
  exact ⟨hSad _ _ hB0 hBk _ p hδ hpS _ _ hΞ.1 hQ hCb.1, hSad _ _ hS0 hSk _ p hδ hpS _ _ hY.1 hRj hCs.1⟩
theorem polarizationLogDetFormula_holds
    (hMid : YangMills.Construction.Tower.FullSpace.BackgroundJets.RemainderJets.MiddleJetsInvertible.MiddleJetsInvertibleClaim)
    (hSad : YangMills.Construction.PeriodicOperators.SaddleJetNumber.Claim)
    (hOps : YangMills.Construction.Tower.FullSpace.BackgroundJets.RemainderJets.OperatorJetsSaddle.Claim)
    (hOp : YangMills.Construction.Tower.FullSpace.ScaledOperatorFunctions.ScaledOperatorFunctionsClaim)
    (hIter : YangMills.Construction.Tower.IteratedSmallFieldMeans.IteratedMeansClaim)
    (hEnt : YangMills.Construction.PeriodicOperators.LocalJetEntire.Claim)
    (hNum : YangMills.Construction.Tower.FreeStrip.ConstantsAdmissible.ConstantsAreAdmissible) :
    PolarizationLogDetFormula := by
  intro L hL hs k hk
  have hz : (0 : Fin 4 → ℂ) ∈ momentumPolydisc stripHalfWidth := fun μ => by
    simpa using stripHalfWidth_nonneg hNum
  obtain ⟨⟨b₀, -⟩, s₀, -⟩ := saddleBlocks_invertible_and_logNumber_add hMid hSad hOp hIter hEnt hs hk hz 0 0
  refine ⟨(hOps L hL hs k hk 0 hz 0 0 b₀ s₀).1, fun p hp μPlus μMinus => ?_⟩
  obtain ⟨⟨b₁, b₂⟩, s₁, s₂⟩ :=
    saddleBlocks_invertible_and_logNumber_add hMid hSad hOp hIter hEnt hs hk hp μPlus μMinus
  obtain ⟨-, hv, hg⟩ := hOps L hL hs k hk p hp μPlus μMinus b₁ s₁
  have e : freePolarizationEntry L k hL μPlus μMinus p =
      -(1 / 2) * logNumber p
          (vectorJet L k hL p (backgroundTriple L k hL p μPlus)
            (backgroundTriple L k hL (-p) μMinus)) +
        logNumber p
          (ghostJet L k hL p (backgroundTriple L k hL p μPlus)
            (backgroundTriple L k hL (-p) μMinus)) := rfl
  rw [e, hv, hg, b₂, s₂]
  ring
end YangMills.Construction.Tower.FullSpace.BackgroundJets.RemainderJets.UnconstrainedDeterminants
end
