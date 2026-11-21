import YangMills.Construction.ColdStepAtMirrorFrames.ClassicalChainAtGivenNumbers
import YangMills.Construction.SummableBoundsOfTheFlow.TheSharesAtDrawnParametersProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PlaneFieldAction
open BlockAverages ColdStepAtMirrorFrames TopLevelSites TorusFields TorusLumps PlaneFields
theorem period_torusFrame_top {L t n : ℕ} (i : Fin 4) :
    (torusFrame L t n).period (torusFrame L t n).top i = n := period_top i
theorem readAtLevel_restrictToTorus {L t n : ℕ} [NeZero n]
    (W : (torusFrame L t n).GaugeField (torusFrame L t n).top) :
    readAtLevel (torusFrame L t n) (t + 1) (restrictToTorus n W) = W := by
  funext x i
  have h := torusSiteInFrame_toTorusSite (period_torusFrame_top (L := L) (t := t) (n := n)) x
  exact congrArg (fun z => W z i) h
theorem cellsOfSites_univ {L t n : ℕ} [NeZero n] :
    cellsOfSites (torusFrame L t n) (Finset.univ : Finset (TorusSite n)) = finiteCells (torusFrame L t n) := by apply _root_.YangMills.SharedProofs.p810 <;> assumption
theorem leastActionAtPlaneField_of (hmin : constantCurvatureMinimalActionStatement)
    (hab : TopOfConstantCurvatureChainIsAbelian) (hpar : AdmissibleParametersExist) :
    LeastActionAtPlaneField := by
  intro T hD
  obtain ⟨c, -, -, -, -, -, -, -, hc⟩ :=
    hpar T.coupling T.δ₁ T.side T.lam T.ρA T.σA T.cg T.N hD.a_ge hD.L_odd hD.chain
  obtain ⟨γ₀, hγ₀, hLA⟩ := hmin T.coupling T.side c hD.a_ge hD.L_odd hc
  obtain ⟨γ₁, hγ₁, hAb⟩ := hab T.side hD.L_odd
  refine ⟨min γ₀ γ₁, lt_min hγ₀ hγ₁, fun t n l _ X μ ν hn hX hμν hg => ?_⟩
  refine ⟨restrictToTorus n (constantCurvatureChain (torusFrame T.side t n) X μ ν l (torusFrame T.side t n).top),
    hAb (torusFrame T.side t n) X μ ν n l rfl (fun _ => rfl) hn hX hμν (hg.trans (min_le_right _ _)), ?_⟩
  have h := (hLA (torusFrame T.side t n) X μ ν n l rfl (fun _ => rfl) hn hX hμν (hg.trans (min_le_left _ _))).2
  show minimalAction T.coupling (cellsOfSites (torusFrame T.side t n) (Finset.univ : Finset (TorusSite n))) (t + 1)
    (readAtLevel (torusFrame T.side t n) (t + 1) _) = _
  rw [cellsOfSites_univ, readAtLevel_restrictToTorus]
  exact h
end YangMills.Construction.PlaneFieldAction
end
