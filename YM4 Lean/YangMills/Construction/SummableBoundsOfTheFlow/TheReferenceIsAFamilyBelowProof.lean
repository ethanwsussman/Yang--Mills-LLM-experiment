import YangMills.Construction.ClusterExpansionOfAStep.TopFieldOffTheHull
import YangMills.Construction.SummableBoundsOfTheFlow.FamiliesReadBelow
import YangMills.Construction.SummableBoundsOfTheFlow.TheReferenceIsAFamilyBelow
import YangMills.Construction.SummableBoundsOfTheFlow.TheReferenceIsSmooth
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Topology
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames TorusFields TorusLumps FamilyNorms Filter
namespace FrameTorus
section Casts
variable {a b : ℕ}
theorem intCast_cast_add (h : a = b) (u v : ZMod a) :
    (((u + v).cast : ℤ) : ZMod b) = ((u.cast : ℤ) : ZMod b) + ((v.cast : ℤ) : ZMod b) := by apply _root_.YangMills.Construction.FrameTorusAction.intCast_cast_add <;> assumption
theorem intCast_cast_neg (h : a = b) (u : ZMod a) :
    (((-u).cast : ℤ) : ZMod b) = -((u.cast : ℤ) : ZMod b) := by apply _root_.YangMills.Construction.FrameTorusAction.intCast_cast_neg <;> assumption
theorem intCast_cast_intCast (h : a = b) (z : ℤ) :
    (((z : ZMod a).cast : ℤ) : ZMod b) = (z : ZMod b) := by apply _root_.YangMills.Construction.FrameTorusAction.intCast_cast_intCast <;> assumption
theorem intCast_cast_intCast_cast (h : a = b) (u : ZMod b) :
    (((((u.cast : ℤ) : ZMod a)).cast : ℤ) : ZMod b) = u := by apply _root_.YangMills.Construction.FrameTorusAction.intCast_cast_roundTrip <;> assumption
theorem valMinAbs_intCast_cast (h : a = b) (u : ZMod a) :
    (((u.cast : ℤ) : ZMod b)).valMinAbs = u.valMinAbs := by apply _root_.YangMills.Construction.TopLevelSites.valMinAbs_intCast_cast <;> assumption
end Casts
section Sites
variable {F : BlockFrame} {m : ℕ}
def siteOfTorus (x : TorusSite m) : F.Site F.depth :=
  siteOfCoords F.depth fun k => ((x k).cast : ℤ)
theorem toTorusSite_siteOfTorus (hp : ∀ i, F.period F.depth i = m) (x : TorusSite m) :
    toTorusSite m (siteOfTorus (F := F) x) = x :=
  funext fun k => intCast_cast_intCast_cast (hp k) (x k)
theorem siteOfTorus_toTorusSite (hp : ∀ i, F.period F.depth i = m) (y : F.Site F.depth) :
    siteOfTorus (toTorusSite m y) = y :=
  funext fun k => intCast_cast_intCast_cast (hp k).symm (y k)
theorem toTorusSite_add (hp : ∀ i, F.period F.depth i = m) (x y : F.Site F.depth) :
    toTorusSite m (x + y) = toTorusSite m x + toTorusSite m y :=
  funext fun k => intCast_cast_add (hp k) (x k) (y k)
theorem toTorusSite_neg (hp : ∀ i, F.period F.depth i = m) (x : F.Site F.depth) :
    toTorusSite m (-x) = -toTorusSite m x :=
  funext fun k => intCast_cast_neg (hp k) (x k)
theorem toTorusSite_sub (hp : ∀ i, F.period F.depth i = m) (x y : F.Site F.depth) :
    toTorusSite m (x - y) = toTorusSite m x - toTorusSite m y := by
  rw [sub_eq_add_neg, toTorusSite_add hp, toTorusSite_neg hp, sub_eq_add_neg]
theorem toTorusSite_siteOfCoords (hp : ∀ i, F.period F.depth i = m) (z : Fin 4 → ℤ) :
    toTorusSite m (siteOfCoords (F := F) F.depth z) = siteOfInt z :=
  funext fun k => intCast_cast_intCast (hp k) (z k)
theorem siteOfInt_single (i : Fin 4) :
    (siteOfInt (Pi.single i 1) : TorusSite m) = TorusFields.unitStep m i := by apply _root_.YangMills.Construction.FrameTorusAction.siteOfInt_single <;> assumption
theorem toTorusSite_unitStep (hp : ∀ i, F.period F.depth i = m) (i : Fin 4) :
    toTorusSite m (BlockAverages.unitStep (F := F) F.depth i) = TorusFields.unitStep m i := by
  rw [BlockAverages.unitStep, toTorusSite_siteOfCoords hp, siteOfInt_single]
theorem restrictToTorus_apply (hp : ∀ i, F.period F.depth i = m) (W : F.GaugeField F.depth)
    (y : F.Site F.depth) (i : Fin 4) :
    restrictToTorus m W (toTorusSite m y) i = W y i :=
  congrFun (congrArg W (siteOfTorus_toTorusSite hp y)) i
theorem siteSupDist_eq (hp : ∀ i, F.period F.depth i = m) (y z : F.Site F.depth) :
    siteSupDist y z = TorusFields.supDist (toTorusSite m y) (toTorusSite m z) := by
  unfold siteSupDist TorusFields.supDist
  refine congrArg (fun g : Fin 4 → ℕ => Finset.univ.sup g) (funext fun i => ?_)
  have h := congrFun (toTorusSite_sub hp y z) i
  simp only [Pi.sub_apply] at h
  rw [← h]
  exact (congrArg Int.natAbs (valMinAbs_intCast_cast (hp i) ((y - z) i))).symm
def torusBond (m : ℕ) (c : F.Site F.depth × Fin 4) : TorusBond m := (toTorusSite m c.1, c.2)
theorem bondSpan_eq (hp : ∀ i, F.period F.depth i = m) {k : ℕ} (y : F.Site F.depth)
    (c : Fin k → F.Site F.depth × Fin 4) :
    bondSpan y c = supportDiam (toTorusSite m y) fun l => torusBond m (c l) := by
  unfold bondSpan supportDiam
  simp only [siteSupDist_eq hp, torusBond]
theorem plaquetteHolonomy_eq (hp : ∀ i, F.period F.depth i = m) (W : F.GaugeField F.depth)
    (y : F.Site F.depth) (μ ν : Fin 4) :
    plaquetteHolonomy W (y, μ, ν) =
      TorusFields.holonomy (restrictToTorus m W) (toTorusSite m y) μ ν := by
  have h1 : toTorusSite m y + TorusFields.unitStep m μ =
      toTorusSite m (y + BlockAverages.unitStep F.depth μ) := by
    rw [toTorusSite_add hp, toTorusSite_unitStep hp]
  have h2 : toTorusSite m y + TorusFields.unitStep m ν =
      toTorusSite m (y + BlockAverages.unitStep F.depth ν) := by
    rw [toTorusSite_add hp, toTorusSite_unitStep hp]
  have h3 : y + BlockAverages.unitStep F.depth μ + BlockAverages.unitStep F.depth ν -
      BlockAverages.unitStep F.depth μ = y + BlockAverages.unitStep F.depth ν := by abel
  have h4 : y + BlockAverages.unitStep F.depth μ + BlockAverages.unitStep F.depth ν +
      -BlockAverages.unitStep F.depth μ - BlockAverages.unitStep F.depth ν = y := by abel
  simp only [plaquetteHolonomy, pathHolonomy, linkValue, stepDisplacement, if_true,
    Bool.false_eq_true, if_false, TorusFields.holonomy, h1, h2, restrictToTorus_apply hp, h3, h4,
    mul_one, mul_assoc]
theorem isCold_restrictToTorus (hp : ∀ i, F.period F.depth i = m) {s : ℝ}
    {W : F.GaugeField F.depth} (h : IsSmallCurvature s W) : IsCold s (restrictToTorus m W) := by
  intro x μ ν hμν
  have h1 := h (siteOfTorus x, μ, ν) hμν
  unfold plaquetteDefect at h1
  rw [plaquetteHolonomy_eq hp, toTorusSite_siteOfTorus hp] at h1
  exact h1
theorem bondSpread_eq (hp : ∀ i, F.period F.depth i = m) {k : ℕ}
    (c : Fin k → F.Site F.depth × Fin 4) (X : Fin k → imaginaryQuaternions) (τ : Fin k → ℝ)
    (x : TorusSite m) (i : Fin 4) :
    ColdStepAtMirrorFrames.bondSpread c X τ (siteOfTorus x) i =
      ∑ l, if torusBond m (c l) = (x, i) then τ l • X l else 0 := by
  unfold ColdStepAtMirrorFrames.bondSpread
  refine Finset.sum_congr rfl fun l _ => ?_
  have hiff : c l = (siteOfTorus x, i) ↔ torusBond m (c l) = (x, i) := by
    constructor
    · intro h
      rw [torusBond, h]
      simp [toTorusSite_siteOfTorus hp]
    · intro h
      have h1 : toTorusSite m (c l).1 = x := congrArg Prod.fst h
      have h2 : (c l).2 = i := congrArg Prod.snd h
      refine Prod.ext ?_ h2
      rw [← h1, siteOfTorus_toTorusSite hp]
  simp only [hiff]
theorem restrictToTorus_leftTranslate (hp : ∀ i, F.period F.depth i = m) {k : ℕ}
    (c : Fin k → F.Site F.depth × Fin 4) (X : Fin k → imaginaryQuaternions) (τ : Fin k → ℝ)
    (W : F.GaugeField F.depth) :
    restrictToTorus m (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X τ) W) =
      perturb (fun l => torusBond m (c l)) X τ (restrictToTorus m W) := by
  funext x i
  show expUnit (ColdStepAtMirrorFrames.bondSpread c X τ (siteOfTorus x) i) * W (siteOfTorus x) i = _
  rw [bondSpread_eq hp]
  rfl
theorem bondDeriv_eq (hp : ∀ i, F.period F.depth i = m) {G : F.GaugeField F.depth → ℝ}
    {G' : TorusField m → ℝ} (hG : ∀ W, G W = G' (restrictToTorus m W)) {k : ℕ}
    (W : F.GaugeField F.depth) (c : Fin k → F.Site F.depth × Fin 4)
    (X : Fin k → imaginaryQuaternions) :
    bondDeriv G W c X = mixedDeriv G' (restrictToTorus m W) (fun l => torusBond m (c l)) X := by
  unfold bondDeriv mixedDeriv
  congr 2
  funext τ
  rw [hG, restrictToTorus_leftTranslate hp]
end Sites
theorem period_eq_of_isCubicTorusAbove {L t n₀ : ℕ} {F : BlockFrame}
    (h : IsCubicTorusAbove L t n₀ F) :
    (∀ i, F.period F.depth i = F.period F.depth 0) ∧ n₀ ≤ F.period F.depth 0 := by
  obtain ⟨hL, _, n, hs, hn⟩ := h
  have hper : ∀ i, F.period F.depth i = n * L := by
    intro i
    simp [BlockFrame.period, BlockFrame.top, hs, hL]
  exact ⟨fun i => by rw [hper, hper], by rw [hper]; exact hn⟩
end FrameTorus
open FrameTorus in
theorem ReferenceDensity.localReferenceBoundedFamily_of_smooth
    (hR : StepDensities.referenceSmoothStatement) (hB : localFamilyNormStatement) :
    ReferenceDensity.localReferenceBoundedFamily := by
  refine EventuallyOrdered.mono hR ?_
  intro T hT hn cR hroom
  obtain ⟨Eh, gR⟩ := cR hroom
  obtain ⟨-, ℓ, hm, hfits⟩ := hroom
  have hE : 0 ≤ T.E := by
    have h1 : (1 : ℝ) ≤ T.E := hT.one_le_E
    linarith
  have hE₃ : 0 ≤ T.energyRatio := by
    have h2 := hT.η₃_pos
    unfold ColdStepAtMirrorFrames.StepParameters.energyRatio
    positivity
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
  have hpos : ∀ {t : ℕ} {F : BlockFrame}, IsCubicTorusAbove T.L t T.n₀ F →
      NeZero (F.period F.depth 0) := by
    intro t F h
    have := (period_eq_of_isCubicTorusAbove h).2
    exact ⟨by omega⟩
  refine ⟨fun j => if j ≤ 3 then T.energyRatio + T.E else Eh j, fun t => ?_⟩
  have hb := gR ℓ hm hfits t
  have hlow : IsNormBoundedLocalFamily T.L t T.n₀ T.σ T.decayRate (T.E / 2)
      (T.energyRatio / 2) (T.localReference t) := by
    have h1 := hB ℓ t _ _ _ hfits hn₁ hb.family
    rw [hm.side_eq, hm.n₀_eq, hm.threshold_eq, hrate] at h1
    exact h1
  refine ⟨⟨hlow.smooth, hlow.gauge_invariant, hlow.translation_invariant, ?_, ?_⟩, ?_,
    hlow.gauge_invariant, ?_⟩
  · intro F hF y W k c X hW h1 h3 hX
    refine (hlow.decay F hF y W k c X hW h1 h3 hX).trans ?_
    apply div_le_div_of_nonneg_right _ (hwp _).le
    split_ifs <;> linarith
  · intro F F' hF hF' y y' W W' r k h X hW hW' hA hk hbox hX
    refine (hlow.locality F F' hF hF' y y' W W' r k h X hW hW' hA hk hbox hX).trans ?_
    apply div_le_div_of_nonneg_right _ (hwp _).le
    linarith
  · intro F hF y W hW j c X
    obtain ⟨hp, hmm⟩ := period_eq_of_isCubicTorusAbove hF
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
    · obtain ⟨hp, hmm⟩ := period_eq_of_isCubicTorusAbove hF
      have := hpos hF
      rw [if_neg h3]
      rw [bondDeriv_eq hp (G := T.localReference t F y)
          (G' := T.referenceDensity t _ (toTorusSite _ y)) (fun _ => rfl),
        bondSpan_eq hp, hw]
      exact hb.higherDeriv_le _ hmm _ _ (isCold_restrictToTorus hp hW) j _ X (by omega) h6 hX
end YangMills.Construction
end
