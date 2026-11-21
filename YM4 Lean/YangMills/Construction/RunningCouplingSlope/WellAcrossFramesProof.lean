import YangMills.Construction.ColdChainAtEveryLevel.LinesOfTheBlocksOfABond
import YangMills.Construction.RunningCouplingSlope.WellAcrossFrames
import Mathlib
set_option autoImplicit false
open Filter
open scoped Topology Quaternion
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
open BlockAverages ColdStepAtMirrorFrames
private theorem analyticAt_component {F : BlockFrame} {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] {k : ℕ}
    [Fintype (F.Site k)]
    {q : X → F.Site k → Fin 4 → ℍ[ℝ]} {e : X} (h : AnalyticAt ℝ q e) (x : F.Site k) (i : Fin 4) :
    AnalyticAt ℝ (fun y => q y x i) e :=
  analyticAt_pi_iff.1 (analyticAt_pi_iff.1 h x) i
private theorem transferSite_siteOfCoords {F G : BlockFrame} {K : ℕ} (hp : ∀ i, F.period K i = G.period K i)
    (z : Fin 4 → ℤ) :
    transferSite F (siteOfCoords (F := G) K z) = siteOfCoords (F := F) K z := by
  funext i
  show ((siteCoords (siteOfCoords (F := G) K z) i : ℤ) : ZMod (F.period K i)) = ((z i : ℤ) : ZMod (F.period K i))
  rw [BlockLines.siteCoords_siteOfCoords, ← hp i, ZMod.intCast_mod]
theorem nondegenerateAcrossFrames_holds (hA : MinimalActionTransfer) : NondegenerateAcrossFrames := by
  intro F G K a _ _ hP hG
  obtain ⟨h1, _, _, h4, _, _, _, _⟩ := hA F G K a hP
  have hper : ∀ i, F.period K i = G.period K i := hP.period_eq K le_rfl
  have hact : ∀ W : F.GaugeField K,
      minimalAction a (finiteCells F) K W = minimalAction a (finiteCells G) K (transferField G W) :=
    fun W => h1 K W le_rfl
  refine ⟨fun W => ?_, ?_, ?_, fun W hW => ?_, ?_, fun B hB => ?_⟩
  · rw [hact]
    exact hG.nonneg _
  · rw [hact]
    exact hG.trivial_eq_zero
  · have e : minimalAction a (finiteCells F) K = fun W => minimalAction a (finiteCells G) K (transferField G W) :=
      funext hact
    rw [e]
    exact hG.continuous.comp (continuous_pi fun x => continuous_pi fun i =>
      (continuous_apply i).comp (continuous_apply _))
  · rw [hact] at hW
    obtain ⟨g, hg⟩ := hG.isPureGauge_of_eq_zero _ hW
    exact ⟨g, fun z i => by rw [← h4 K W z i le_rfl]; exact hg z i⟩
  · have hR : AnalyticAt ℝ (fun (Y : F.Site K → Fin 4 → ℍ[ℝ]) (x : G.Site K) (i : Fin 4) => Y (transferSite F x) i)
        (quaternionsOfField (trivialBlockField F K)) :=
      AnalyticAt.pi fun x => AnalyticAt.pi fun i =>
        analyticAt_component analyticAt_id (transferSite F x) i
    have h2 := AnalyticAt.comp (g := fun Y => minimalAction a (finiteCells G) K (fieldOfQuaternions Y))
      (f := fun (Y : F.Site K → Fin 4 → ℍ[ℝ]) (x : G.Site K) (i : Fin 4) => Y (transferSite F x) i)
      hG.analyticAt_trivial hR
    refine h2.congr (Eventually.of_forall fun Y => ?_)
    show minimalAction a (finiteCells G) K (transferField G (fieldOfQuaternions Y)) =
      minimalAction a (finiteCells F) K (fieldOfQuaternions Y)
    exact (hact _).symm
  · have e : (fun τ : ℝ => minimalAction a (finiteCells F) K (fieldAlongLine B τ)) =
        fun τ => minimalAction a (finiteCells G) K (fieldAlongLine (fun x i => B (transferSite F x) i) τ) :=
      funext fun τ => hact _
    rw [e] at hB
    obtain ⟨l, hl⟩ := hG.isExactForm_of_deriv _ hB
    refine ⟨l, fun z i => ?_⟩
    have := hl z i
    simp only [transferSite_siteOfCoords hper] at this
    exact this
end YangMills.Construction.RunningCouplingSlope
end
