import YangMills.Construction.PeriodicOperators.BoundsOfTheNumbersOfAJet
import YangMills.Construction.PeriodicOperators.IndexSetsOfATower
import YangMills.Construction.PeriodicOperators.TheFibresAtTheTopOfATower
import YangMills.Construction.Towers.BoundsOfTheSiteTermsOfTheRemainder
import YangMills.Construction.Towers.TheMiddleJetsOfTheRemainderAreInvertible
import YangMills.Construction.Towers.TheSiteJetsBetweenTheRootsOfTheFreePropagator
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.BackgroundJets.RemainderJets
open YangMills.Construction.PeriodicOperators
open YangMills.Construction.PeriodicOperators.JetQuad
theorem vertexTermsBounded_holds (hRem : RootInterpolation.RemainderBoundClaim)
    (hJets : VertexRootJets.VertexJetsInterpolate)
    (hFib : PeriodicOperators.TopFibreDimension.Claim)
    (hTr : ResolventTrace.ThreeResolventTraceBound)
    (hNum : PeriodicOperators.JetNumberBounds.Claim)
    (hMid : MiddleJetsInvertible.MiddleJetsInvertibleClaim)
    (hIdx : PeriodicOperators.TowerIndexSets.Claim) : VertexTermsBounded := by
  intro L hL
  obtain ⟨a, b, g, ha, hb, hg, hdata⟩ := hJets L hL
  obtain ⟨Cm, hCm⟩ := hMid
  obtain ⟨hγ, hγL⟩ := hTr
  have hc : 0 ≤ max Cm 0 := le_max_right _ _
  have hD : 0 ≤ a ^ 2 * b := by positivity
  refine ⟨max ((3 + 3) * a ^ 2 * b * (1 + g * b + g ^ 2 * b ^ 2) +
      ResolventTrace.threeResolventTraceConst * b ^ 3)
    (3 * (max Cm 0 * (a ^ 2 * b) + max Cm 0 ^ 2 * (a ^ 2 * b) ^ 2)), ?_⟩
  intro k hk p hp μPlus μMinus
  have data := hdata k hk p hp μPlus μMinus
  have hI0 := hIdx L hL k 0 (Nat.zero_le k)
  have hIk := hIdx L hL k k le_rfl
  have hfib := hFib L hL k hk
  obtain ⟨h1, h2⟩ := hRem (colourVertices L k 0) (colourVertices L k k) (colourVertices L k k) hI0.1
    hIk.1 hIk.1 ResolventTrace.threeResolventTraceConst (Tower.FreeResolvents.vertexResolvent L k) hγ
    (hγL L hL k hk).2 p _ _ _ _ _ _ a b g ha hb hg data
  constructor
  · refine le_trans ?_ (le_max_left _ _)
    have hvert : RootInterpolation.fiberDim (colourVertices L k k) = 3 := by
      simp [RootInterpolation.fiberDim, hfib.2]
    rw [hvert] at h1
    exact h1
  · refine le_trans ?_ (le_max_right _ _)
    have hinv := (hCm L hL k hk p hp μPlus μMinus).2.2.2.2
    have hl := (hNum stripHalfWidth p data.isJet_A.pos_width data.isJet_A.mem_imStrip _ hIk.1
      (vertexConstraintJet L k p μPlus μMinus)).2 hinv.1
    rw [hfib.2] at hl
    have hι : (⨆ κ ∈ imStrip (2 * stripHalfWidth), quotHomNorm
        (quotHomInverse ((vertexConstraintJet L k p μPlus μMinus).f00 κ))) ≤
          ENNReal.ofReal (max Cm 0) :=
      iSup₂_le fun κ hκ =>
        (hinv.2 κ hκ).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
    have hn : jetNorm stripHalfWidth p (vertexConstraintJet L k p μPlus μMinus) ≤
        ENNReal.ofReal (a ^ 2 * b) := h2
    have hfinal : ENNReal.ofReal ‖logNumber p (vertexConstraintJet L k p μPlus μMinus)‖ ≤
        ENNReal.ofReal (3 * (max Cm 0 * (a ^ 2 * b) + max Cm 0 ^ 2 * (a ^ 2 * b) ^ 2)) := by
      refine hl.trans ?_
      have e : ∀ c D : ℝ, 0 ≤ c → 0 ≤ D → ENNReal.ofReal (3 * (c * D + c ^ 2 * D ^ 2)) =
          ((3 : ℕ) : ℝ≥0∞) * (ENNReal.ofReal c * ENNReal.ofReal D +
            ENNReal.ofReal c ^ 2 * ENNReal.ofReal D ^ 2) := by
        intro c D hc hD
        rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_add (by positivity) (by positivity),
          ENNReal.ofReal_mul hc, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow hc,
          ENNReal.ofReal_pow hD]
        norm_num
      rw [e _ _ hc hD]
      gcongr
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hfinal
end YangMills.Construction.Tower.FullSpace.BackgroundJets.RemainderJets
end
