import YangMills.Construction.SummableBoundsOfTheFlow.TheReferenceIsAFamilyBelowProof
import YangMills.Construction.SummableBoundsOfTheFlow.TheReferenceIsReadBelowAtItsLevel
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Topology
open Filter
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames TorusFields TorusLumps FamilyNorms
namespace ReferenceTransfer
section ZModCasts
variable {a b : ℕ}
private theorem zmod_recast_recast (h : a = b) (u : ZMod b) :
    (((((u.cast : ℤ) : ZMod a)).cast : ℤ) : ZMod b) = u := by apply _root_.YangMills.Construction.FrameTorusAction.intCast_cast_roundTrip <;> assumption
end ZModCasts
section FrameToTorus
variable {F : BlockFrame} {m : ℕ}
private def frameSite (x : TorusSite m) : F.Site F.depth :=
  BlockAverages.siteOfCoords F.depth fun k => ((x k).cast : ℤ)
private theorem toTorusSite_frameSite (hp : ∀ i, F.period F.depth i = m) (x : TorusSite m) :
    toTorusSite m (frameSite (F := F) x) = x :=
  funext fun k => zmod_recast_recast (hp k) (x k)
private theorem frameSite_toTorusSite (hp : ∀ i, F.period F.depth i = m) (y : F.Site F.depth) :
    frameSite (toTorusSite m y) = y :=
  funext fun k => zmod_recast_recast (hp k).symm (y k)
private theorem siteSupDist_eq (hp : ∀ i, F.period F.depth i = m) (y z : F.Site F.depth) :
    siteSupDist y z = TorusFields.supDist (toTorusSite m y) (toTorusSite m z) := by apply _root_.YangMills.Construction.FrameTorus.siteSupDist_eq <;> assumption
private def torusBond (m : ℕ) (c : F.Site F.depth × Fin 4) : TorusBond m := (toTorusSite m c.1, c.2)
private theorem bondSpan_eq (hp : ∀ i, F.period F.depth i = m) {k : ℕ} (y : F.Site F.depth)
    (c : Fin k → F.Site F.depth × Fin 4) :
    bondSpan y c = supportDiam (toTorusSite m y) fun l => torusBond m (c l) := by apply _root_.YangMills.Construction.FrameTorus.bondSpan_eq <;> assumption
private theorem isCold_restrictToTorus (hp : ∀ i, F.period F.depth i = m) {s : ℝ}
    {W : F.GaugeField F.depth} (h : IsSmallCurvature s W) : IsCold s (restrictToTorus m W) := by apply _root_.YangMills.Construction.FrameTorus.isCold_restrictToTorus <;> assumption
private theorem bondSpread_eq (hp : ∀ i, F.period F.depth i = m) {k : ℕ}
    (c : Fin k → F.Site F.depth × Fin 4) (X : Fin k → imaginaryQuaternions) (τ : Fin k → ℝ)
    (x : TorusSite m) (i : Fin 4) :
    bondSpread c X τ (frameSite x) i = ∑ l, if torusBond m (c l) = (x, i) then τ l • X l else 0 := by apply _root_.YangMills.Construction.FrameTorus.bondSpread_eq <;> assumption
private theorem restrictToTorus_leftTranslate (hp : ∀ i, F.period F.depth i = m) {k : ℕ}
    (c : Fin k → F.Site F.depth × Fin 4) (X : Fin k → imaginaryQuaternions) (τ : Fin k → ℝ)
    (W : F.GaugeField F.depth) :
    restrictToTorus m (leftTranslate (bondSpread c X τ) W) =
      perturb (fun l => torusBond m (c l)) X τ (restrictToTorus m W) := by apply _root_.YangMills.Construction.FrameTorus.restrictToTorus_leftTranslate <;> assumption
private theorem bondDeriv_eq_mixedDeriv (hp : ∀ i, F.period F.depth i = m)
    {G : F.GaugeField F.depth → ℝ} {G' : TorusField m → ℝ}
    (hG : ∀ W, G W = G' (restrictToTorus m W)) {k : ℕ} (W : F.GaugeField F.depth)
    (c : Fin k → F.Site F.depth × Fin 4) (X : Fin k → imaginaryQuaternions) :
    bondDeriv G W c X = mixedDeriv G' (restrictToTorus m W) (fun l => torusBond m (c l)) X := by apply _root_.YangMills.Construction.FrameTorus.bondDeriv_eq <;> assumption
end FrameToTorus
private theorem period_facts_of_cubic {L t n₀ : ℕ} {F : BlockFrame} (h : IsCubicTorusAbove L t n₀ F) :
    (∀ i, F.period F.depth i = F.period F.depth 0) ∧ n₀ ≤ F.period F.depth 0 := by apply _root_.YangMills.Construction.FrameTorus.period_eq_of_isCubicTorusAbove <;> assumption
end ReferenceTransfer
open ReferenceTransfer in
theorem StepDensities.referenceBoundsBelow_of_localFamilyNorm (hB : localFamilyNormStatement) :
    StepDensities.ReferenceBoundsBelow := by
  intro T ℓ Eh t hT hm hfits hb
  have hE1 : (1 : ℝ) ≤ T.E := hT.one_le_E
  have hη := hT.η₃_pos
  have hE₃E : T.E ≤ T.energyRatio := by
    unfold ColdStepAtMirrorFrames.StepParameters.energyRatio
    rw [le_div_iff₀ hη]
    nlinarith [hT.η₃_le_one]
  have hn₁ : ℓ.n₁ = (ℓ.side : ℝ) ^ (1 / 640 : ℝ) := by
    rw [hm.n₁_eq, hm.side_eq]
  have hrate : ℓ.weightRate = T.decayRate := by
    unfold TorusLumps.StepParameters.weightRate ColdStepAtMirrorFrames.StepParameters.decayRate
    rw [hm.rt_eq]
  have hw : ∀ s : ℕ, torusDecayFactor T.L T.decayRate s = ℓ.weight s := by
    intro s
    unfold torusDecayFactor TorusLumps.StepParameters.weight
    rw [hn₁, hm.side_eq, hrate]
  have hwp : ∀ s : ℝ, 0 < torusDecayFactor T.L T.decayRate s := by
    intro s
    unfold torusDecayFactor
    exact mul_pos (lt_of_lt_of_le one_pos (le_max_left _ _)) (Real.exp_pos _)
  have hn : 1 ≤ T.n₀ := by
    have h := hfits.n₀_ge
    rw [hm.n₀_eq] at h
    omega
  have hpos : ∀ {t : ℕ} {F : BlockFrame}, IsCubicTorusAbove T.L t T.n₀ F →
      NeZero (F.period F.depth 0) := by
    intro t F h
    have := (period_facts_of_cubic h).2
    exact ⟨by omega⟩
  have hlow : IsNormBoundedLocalFamily T.L t T.n₀ T.σ T.decayRate (T.E / 2) (T.energyRatio / 2)
      (T.localReference t) := by
    have h1 := hB ℓ t _ _ _ hfits hn₁ hb.family
    rw [hm.side_eq, hm.n₀_eq, hm.threshold_eq, hrate] at h1
    exact h1
  refine ⟨⟨hlow.smooth, hlow.gauge_invariant, hlow.translation_invariant, ?_, ?_⟩, ?_, hlow.gauge_invariant, ?_⟩
  · intro F hF y W k c X hW h1 h3 hX
    refine (hlow.decay F hF y W k c X hW h1 h3 hX).trans ?_
    apply div_le_div_of_nonneg_right _ (hwp _).le
    split_ifs <;> linarith
  · intro F F' hF hF' y y' W W' r k h X hW hW' hA hk hbx hX
    refine (hlow.locality F F' hF hF' y y' W W' r k h X hW hW' hA hk hbx hX).trans ?_
    apply div_le_div_of_nonneg_right _ (hwp _).le
    linarith
  · intro F hF y W hW j c X
    obtain ⟨hp, hmm⟩ := period_facts_of_cubic hF
    have := hpos hF
    have h := hb.analytic _ hmm (toTorusSite _ y) _ (isCold_restrictToTorus hp hW) j
      (fun l => torusBond _ (c l)) X
    simp only [ColdStepAtMirrorFrames.StepParameters.localReference, localFamilyOfDensity,
      restrictToTorus_leftTranslate hp]
    exact h.contDiffAt
  · intro F hF y W j c X hW h1 h6 hX
    by_cases h3 : j ≤ 3
    · refine (hlow.decay F hF y W j c X hW h1 h3 hX).trans ?_
      apply div_le_div_of_nonneg_right _ (hwp _).le
      rw [if_pos h3]
      split_ifs <;> linarith
    · obtain ⟨hp, hmm⟩ := period_facts_of_cubic hF
      have := hpos hF
      rw [if_neg h3]
      rw [bondDeriv_eq_mixedDeriv hp (G := T.localReference t F y)
          (G' := T.referenceDensity t _ (toTorusSite _ y)) (fun _ => rfl),
        bondSpan_eq hp, hw]
      exact hb.higherDeriv_le _ hmm _ _ (isCold_restrictToTorus hp hW) j _ X (by omega) h6 hX
end YangMills.Construction
end
