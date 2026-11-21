import YangMills.Construction.ColdStepAtMirrorFrames.ColdExpansionIsAnExpansionBelowProof
import YangMills.Construction.SummableBoundsOfTheFlow.TheReferenceIsAFamilyBelowProof
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Topology
namespace YangMills.Construction
open BlockAverages TorusFields TorusLumps ColdStepAtMirrorFrames Filter
namespace FamilyNorms
namespace OnTori
section Casts
variable {a b : ℕ}
theorem intCast_cast_add (h : a = b) (u v : ZMod a) :
    (((u + v).cast : ℤ) : ZMod b) = ((u.cast : ℤ) : ZMod b) + ((v.cast : ℤ) : ZMod b) := by apply _root_.YangMills.Construction.FrameTorusAction.intCast_cast_add <;> assumption
theorem intCast_cast_intCast_cast (h : a = b) (u : ZMod b) :
    (((((u.cast : ℤ) : ZMod a)).cast : ℤ) : ZMod b) = u := by apply _root_.YangMills.Construction.FrameTorusAction.intCast_cast_roundTrip <;> assumption
end Casts
section Sites
variable {F : BlockFrame} {m : ℕ}
def siteOfTorus (x : TorusSite m) : F.Site F.depth := siteOfCoords F.depth fun k => ((x k).cast : ℤ)
theorem toTorusSite_siteOfTorus (hp : ∀ i, F.period F.depth i = m) (x : TorusSite m) :
    toTorusSite m (siteOfTorus (F := F) x) = x :=
  funext fun k => intCast_cast_intCast_cast (hp k) (x k)
theorem siteOfTorus_toTorusSite (hp : ∀ i, F.period F.depth i = m) (y : F.Site F.depth) :
    siteOfTorus (toTorusSite m y) = y :=
  funext fun k => intCast_cast_intCast_cast (hp k).symm (y k)
theorem toTorusSite_add (hp : ∀ i, F.period F.depth i = m) (x y : F.Site F.depth) :
    toTorusSite m (x + y) = toTorusSite m x + toTorusSite m y :=
  funext fun k => intCast_cast_add (hp k) (x k) (y k)
theorem toTorusSite_sub (hp : ∀ i, F.period F.depth i = m) (x y : F.Site F.depth) :
    toTorusSite m (x - y) = toTorusSite m x - toTorusSite m y := by apply _root_.YangMills.Construction.FrameTorus.toTorusSite_sub <;> assumption
theorem toTorusSite_siteOfCoords (hp : ∀ i, F.period F.depth i = m) (z : Fin 4 → ℤ) :
    toTorusSite m (siteOfCoords (F := F) F.depth z) = siteOfInt z := by apply _root_.YangMills.Construction.FrameTorus.toTorusSite_siteOfCoords <;> assumption
theorem siteOfInt_single (i : Fin 4) :
    (siteOfInt (Pi.single i 1) : TorusSite m) = TorusFields.unitStep m i := by apply _root_.YangMills.Construction.FrameTorusAction.siteOfInt_single <;> assumption
theorem toTorusSite_unitStep (hp : ∀ i, F.period F.depth i = m) (i : Fin 4) :
    toTorusSite m (BlockAverages.unitStep (F := F) F.depth i) = TorusFields.unitStep m i := by
  rw [BlockAverages.unitStep, toTorusSite_siteOfCoords hp, siteOfInt_single]
theorem toTorusSite_injective (hp : ∀ i, F.period F.depth i = m) :
    Function.Injective (toTorusSite m : F.Site F.depth → TorusSite m) := fun x y h => by
  rw [← siteOfTorus_toTorusSite hp x, h, siteOfTorus_toTorusSite hp y]
theorem restrictToTorus_apply (hp : ∀ i, F.period F.depth i = m) (W : F.GaugeField F.depth)
    (y : F.Site F.depth) (i : Fin 4) :
    restrictToTorus m W (toTorusSite m y) i = W y i := by apply _root_.YangMills.Construction.FrameTorus.restrictToTorus_apply <;> assumption
def torusBond (m : ℕ) (c : F.Site F.depth × Fin 4) : TorusBond m := (toTorusSite m c.1, c.2)
theorem bondSpan_eq_supportDiam (hp : ∀ i, F.period F.depth i = m) {k : ℕ} (y : F.Site F.depth)
    (c : Fin k → F.Site F.depth × Fin 4) :
    bondSpan y c = supportDiam (toTorusSite m y) fun l => torusBond m (c l) := by apply _root_.YangMills.Construction.FrameTorus.bondSpan_eq <;> assumption
theorem isCold_restrictToTorus (hp : ∀ i, F.period F.depth i = m) {s : ℝ} {W : F.GaugeField F.depth}
    (h : IsSmallCurvature s W) : IsCold s (restrictToTorus m W) := by apply _root_.YangMills.Construction.FrameTorus.isCold_restrictToTorus <;> assumption
theorem restrictToTorus_leftTranslate (hp : ∀ i, F.period F.depth i = m) {k : ℕ}
    (c : Fin k → F.Site F.depth × Fin 4) (X : Fin k → imaginaryQuaternions) (τ : Fin k → ℝ)
    (W : F.GaugeField F.depth) :
    restrictToTorus m (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X τ) W) =
      perturb (fun l => torusBond m (c l)) X τ (restrictToTorus m W) := by apply _root_.YangMills.Construction.FrameTorus.restrictToTorus_leftTranslate <;> assumption
theorem bondDeriv_eq_mixedDeriv (hp : ∀ i, F.period F.depth i = m) {G : F.GaugeField F.depth → ℝ}
    {G' : TorusField m → ℝ} (hG : ∀ W, G W = G' (restrictToTorus m W)) {k : ℕ} (W : F.GaugeField F.depth)
    (c : Fin k → F.Site F.depth × Fin 4) (X : Fin k → imaginaryQuaternions) :
    bondDeriv G W c X = mixedDeriv G' (restrictToTorus m W) (fun l => torusBond m (c l)) X := by apply _root_.YangMills.Construction.FrameTorus.bondDeriv_eq <;> assumption
theorem restrictToTorus_gaugeTransform (hp : ∀ i, F.period F.depth i = m) (γ : F.Site F.depth → UnitQuaternion)
    (W : F.GaugeField F.depth) :
    restrictToTorus m (BlockAverages.gaugeTransform γ W) =
      TorusFields.gaugeTransform (fun x => γ (siteOfTorus x)) (restrictToTorus m W) := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.TorusCoordinates.restrictToTorus_gaugeTransform <;> assumption
theorem restrictToTorus_translateField (hp : ∀ i, F.period F.depth i = m) (h : F.Site F.depth)
    (W : F.GaugeField F.depth) :
    restrictToTorus m (translateField h W) = TorusFields.translate (-toTorusSite m h) (restrictToTorus m W) := by
  funext x i
  have h1 : siteOfTorus (F := F) (x + -toTorusSite m h) = siteOfTorus x - h := by
    apply toTorusSite_injective hp
    rw [toTorusSite_siteOfTorus hp, toTorusSite_sub hp, toTorusSite_siteOfTorus hp, sub_eq_add_neg]
  show W (siteOfTorus x - h) i = W (siteOfTorus (x + -toTorusSite m h)) i
  rw [h1]
end Sites
theorem period_facts_of_isCubicTorusAbove {L t n₀ : ℕ} {F : BlockFrame} (h : IsCubicTorusAbove L t n₀ F) :
    (∀ i, F.period F.depth i = F.period F.depth 0) ∧ n₀ ≤ F.period F.depth 0 := by apply _root_.YangMills.Construction.FrameTorus.period_eq_of_isCubicTorusAbove <;> assumption
end OnTori
open OnTori in
theorem localFamilyNormStatement_holds : localFamilyNormStatement := by
  intro ℓ t ε ε₃ f hF hn₁ hR
  have hw : ∀ s : ℕ, torusDecayFactor ℓ.side ℓ.weightRate s = ℓ.weight s := by
    intro s
    unfold torusDecayFactor StepParameters.weight
    rw [hn₁]
  have hpos : ∀ {F : BlockFrame}, IsCubicTorusAbove ℓ.side t ℓ.n₀ F → NeZero (F.period F.depth 0) := by
    intro F h
    have := (period_facts_of_isCubicTorusAbove h).2
    have := hF.n₀_ge
    exact ⟨by omega⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro F hFr y W hW k c X
    obtain ⟨hp, hm⟩ := period_facts_of_isCubicTorusAbove hFr
    have := hpos hFr
    have h := hR.admissible.smooth _ hm (toTorusSite _ y) _ (isCold_restrictToTorus hp hW) k
      (fun l => torusBond _ (c l)) X
    simp only [localFamilyOfDensity, restrictToTorus_leftTranslate hp]
    exact h
  · intro F hFr y W γ hW
    obtain ⟨hp, hm⟩ := period_facts_of_isCubicTorusAbove hFr
    have := hpos hFr
    show f _ (toTorusSite _ y) (restrictToTorus _ (BlockAverages.gaugeTransform γ W)) =
      f _ (toTorusSite _ y) (restrictToTorus _ W)
    rw [restrictToTorus_gaugeTransform hp]
    exact hR.admissible.gauge _ hm _ _ _ (isCold_restrictToTorus hp hW)
  · intro F hFr y h W hW
    obtain ⟨hp, hm⟩ := period_facts_of_isCubicTorusAbove hFr
    have := hpos hFr
    show f _ (toTorusSite _ (y + h)) (restrictToTorus _ (translateField h W)) =
      f _ (toTorusSite _ y) (restrictToTorus _ W)
    rw [restrictToTorus_translateField hp, hR.admissible.translation _ hm _ _ _ (isCold_restrictToTorus hp hW),
      toTorusSite_add hp, add_neg_cancel_right]
  · intro F hFr y W k c X hW h1 h3 hX
    obtain ⟨hp, hm⟩ := period_facts_of_isCubicTorusAbove hFr
    have := hpos hFr
    rw [bondDeriv_eq_mixedDeriv hp (G := localFamilyOfDensity f F y) (G' := f _ (toTorusSite _ y))
      (fun _ => rfl), bondSpan_eq_supportDiam hp, hw]
    exact hR.decay _ hm _ _ (isCold_restrictToTorus hp hW) k _ X h1 h3 hX
  · intro F F' hFr hFr' y y' W W' r k h X hW hW' hA hk hbox hX
    obtain ⟨hp, hm⟩ := period_facts_of_isCubicTorusAbove hFr
    obtain ⟨hp', hm'⟩ := period_facts_of_isCubicTorusAbove hFr'
    have := hpos hFr
    have := hpos hFr'
    rw [bondDeriv_eq_mixedDeriv hp (G := subtractTrivial (localFamilyOfDensity f) F y)
      (G' := centeredFamily f _ (toTorusSite _ y)) (fun _ => rfl),
      bondDeriv_eq_mixedDeriv hp' (G := subtractTrivial (localFamilyOfDensity f) F' y')
        (G' := centeredFamily f _ (toTorusSite _ y')) (fun _ => rfl), hw]
    have hb : ∀ {E : BlockFrame} (hq : ∀ i, E.period E.depth i = E.period E.depth 0) (z : E.Site E.depth),
        (fun l => torusBond (E.period E.depth 0) (bondsAt z h l)) =
          fun l => bondFrom (toTorusSite (E.period E.depth 0) z) (h l) := by
      intro E hq z
      funext l
      simp only [torusBond, bondsAt, bondFrom, toTorusSite_add hq, toTorusSite_siteOfCoords hq]
    rw [hb hp, hb hp']
    have hagree : FieldsAgreeNear (restrictToTorus (F.period F.depth 0) W)
        (restrictToTorus (F'.period F'.depth 0) W') (toTorusSite _ y) (toTorusSite _ y') r := by
      intro b hbb
      have e1 : (bondFrom (toTorusSite (F.period F.depth 0) y) b).1 =
          toTorusSite (F.period F.depth 0) (y + siteOfCoords F.depth b.1) := by
        simp only [bondFrom, toTorusSite_add hp, toTorusSite_siteOfCoords hp]
      have e2 : (bondFrom (toTorusSite (F'.period F'.depth 0) y') b).1 =
          toTorusSite (F'.period F'.depth 0) (y' + siteOfCoords F'.depth b.1) := by
        simp only [bondFrom, toTorusSite_add hp', toTorusSite_siteOfCoords hp']
      rw [e1, e2, restrictToTorus_apply hp, restrictToTorus_apply hp']
      exact hA.2.2 b hbb
    exact hR.comparison _ _ hm hm' _ _ _ _ r (hA.1 0) (hA.2.1 0) (isCold_restrictToTorus hp hW)
      (isCold_restrictToTorus hp' hW') hagree k h X hk hbox hX
end FamilyNorms
end YangMills.Construction
end
