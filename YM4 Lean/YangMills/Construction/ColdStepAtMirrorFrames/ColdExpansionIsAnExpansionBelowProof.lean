import YangMills.Construction.ColdStepAtMirrorFrames.ColdExpansionIsAnExpansionBelow
import YangMills.Construction.ColdStepAtMirrorFrames.LimitFormOfAColdExpansion
import YangMills.Construction.SummableBoundsOfTheFlow.TheReferenceIsAFamilyBelowProof
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Topology
namespace YangMills.Construction.ColdStepAtMirrorFrames
open YangMills.Construction.BlockAverages YangMills.Construction.TorusFields YangMills.Construction.TorusLumps Filter
namespace TorusCoordinates
section Casts
variable {a b : ℕ}
theorem castInt_add (h : a = b) (u v : ZMod a) :
    (((u + v).cast : ℤ) : ZMod b) = ((u.cast : ℤ) : ZMod b) + ((v.cast : ℤ) : ZMod b) := by apply _root_.YangMills.Construction.FrameTorusAction.intCast_cast_add <;> assumption
theorem castInt_castInt (h : a = b) (u : ZMod b) :
    (((((u.cast : ℤ) : ZMod a)).cast : ℤ) : ZMod b) = u := by apply _root_.YangMills.Construction.FrameTorusAction.intCast_cast_roundTrip <;> assumption
end Casts
section Sites
variable {F : BlockFrame} {m : ℕ}
def ofTorusSite (x : TorusSite m) : F.Site F.depth := siteOfCoords F.depth fun k => ((x k).cast : ℤ)
theorem toTorusSite_ofTorusSite (hp : ∀ i, F.period F.depth i = m) (x : TorusSite m) :
    toTorusSite m (ofTorusSite (F := F) x) = x :=
  funext fun k => castInt_castInt (hp k) (x k)
theorem ofTorusSite_toTorusSite (hp : ∀ i, F.period F.depth i = m) (y : F.Site F.depth) :
    ofTorusSite (toTorusSite m y) = y :=
  funext fun k => castInt_castInt (hp k).symm (y k)
theorem toTorusSite_add (hp : ∀ i, F.period F.depth i = m) (x y : F.Site F.depth) :
    toTorusSite m (x + y) = toTorusSite m x + toTorusSite m y :=
  funext fun k => castInt_add (hp k) (x k) (y k)
theorem toTorusSite_sub (hp : ∀ i, F.period F.depth i = m) (x y : F.Site F.depth) :
    toTorusSite m (x - y) = toTorusSite m x - toTorusSite m y := by apply _root_.YangMills.Construction.FrameTorus.toTorusSite_sub <;> assumption
theorem toTorusSite_siteOfCoords (hp : ∀ i, F.period F.depth i = m) (z : Fin 4 → ℤ) :
    toTorusSite m (siteOfCoords (F := F) F.depth z) = siteOfInt z := by apply _root_.YangMills.Construction.FrameTorus.toTorusSite_siteOfCoords <;> assumption
theorem toTorusSite_zero (hp : ∀ i, F.period F.depth i = m) :
    toTorusSite m (0 : F.Site F.depth) = 0 := by
  have h := toTorusSite_add hp (0 : F.Site F.depth) 0
  rw [add_zero] at h
  exact left_eq_add.mp h
theorem siteOfInt_single (i : Fin 4) :
    (siteOfInt (Pi.single i 1) : TorusSite m) = TorusFields.unitStep m i := by apply _root_.YangMills.Construction.FrameTorusAction.siteOfInt_single <;> assumption
theorem toTorusSite_unitStep (hp : ∀ i, F.period F.depth i = m) (i : Fin 4) :
    toTorusSite m (BlockAverages.unitStep (F := F) F.depth i) = TorusFields.unitStep m i := by
  rw [BlockAverages.unitStep, toTorusSite_siteOfCoords hp, siteOfInt_single]
theorem toTorusSite_injective (hp : ∀ i, F.period F.depth i = m) :
    Function.Injective (toTorusSite m : F.Site F.depth → TorusSite m) := fun x y h => by
  rw [← ofTorusSite_toTorusSite hp x, h, ofTorusSite_toTorusSite hp y]
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
    restrictToTorus m (leftTranslate (bondSpread c X τ) W) =
      perturb (fun l => torusBond m (c l)) X τ (restrictToTorus m W) := by apply _root_.YangMills.Construction.FrameTorus.restrictToTorus_leftTranslate <;> assumption
theorem bondDeriv_eq_mixedDeriv (hp : ∀ i, F.period F.depth i = m) {G : F.GaugeField F.depth → ℝ}
    {G' : TorusField m → ℝ} (hG : ∀ W, G W = G' (restrictToTorus m W)) {k : ℕ}
    (W : F.GaugeField F.depth) (c : Fin k → F.Site F.depth × Fin 4)
    (X : Fin k → imaginaryQuaternions) :
    bondDeriv G W c X = mixedDeriv G' (restrictToTorus m W) (fun l => torusBond m (c l)) X := by apply _root_.YangMills.Construction.FrameTorus.bondDeriv_eq <;> assumption
theorem restrictToTorus_gaugeTransform (hp : ∀ i, F.period F.depth i = m)
    (γ : F.Site F.depth → UnitQuaternion) (W : F.GaugeField F.depth) :
    restrictToTorus m (BlockAverages.gaugeTransform γ W) =
      TorusFields.gaugeTransform (fun x => γ (ofTorusSite x)) (restrictToTorus m W) := by
  funext x i
  have h : ofTorusSite (F := F) (x + TorusFields.unitStep m i) =
      ofTorusSite x + BlockAverages.unitStep F.depth i := by
    apply toTorusSite_injective hp
    rw [toTorusSite_ofTorusSite hp, toTorusSite_add hp, toTorusSite_ofTorusSite hp,
      toTorusSite_unitStep hp]
  show γ (ofTorusSite x) * W (ofTorusSite x) i *
      (γ (ofTorusSite x + BlockAverages.unitStep F.depth i))⁻¹ =
    γ (ofTorusSite x) * W (ofTorusSite x) i * (γ (ofTorusSite (x + TorusFields.unitStep m i)))⁻¹
  rw [h]
theorem restrictToTorus_translateField (hp : ∀ i, F.period F.depth i = m) (h : F.Site F.depth)
    (W : F.GaugeField F.depth) :
    restrictToTorus m (translateField h W) =
      TorusFields.translate (-toTorusSite m h) (restrictToTorus m W) := by
  funext x i
  have h1 : ofTorusSite (F := F) (x + -toTorusSite m h) = ofTorusSite x - h := by
    apply toTorusSite_injective hp
    rw [toTorusSite_ofTorusSite hp, toTorusSite_sub hp, toTorusSite_ofTorusSite hp, sub_eq_add_neg]
  show W (ofTorusSite x - h) i = W (ofTorusSite (x + -toTorusSite m h)) i
  rw [h1]
end Sites
theorem period_eq_of_isCubicTorusAbove {L t n₀ : ℕ} {F : BlockFrame} (h : IsCubicTorusAbove L t n₀ F) :
    (∀ i, F.period F.depth i = F.period F.depth 0) ∧ n₀ ≤ F.period F.depth 0 := by apply _root_.YangMills.Construction.FrameTorus.period_eq_of_isCubicTorusAbove <;> assumption
end TorusCoordinates
open TorusCoordinates in
theorem coldExpansionRegular_of_limitForm (hL : LimitFormVanishesOnLinearPotentials) :
    ColdExpansionRegular := by
  intro ℓ t x D f hF hn₁ hR
  have hw : ∀ s : ℕ, torusDecayFactor ℓ.side ℓ.weightRate (s : ℝ) = ℓ.weight s := by
    intro s
    unfold torusDecayFactor StepParameters.weight
    rw [hn₁]
  have hpos : ∀ {F : BlockFrame}, IsCubicTorusAbove ℓ.side t ℓ.n₀ F →
      NeZero (F.period F.depth 0) := by
    intro F h
    have := (period_eq_of_isCubicTorusAbove h).2
    have := hF.n₀_ge
    exact ⟨by omega⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro F hFr y W hW k c X
    obtain ⟨hp, hm⟩ := period_eq_of_isCubicTorusAbove hFr
    haveI := hpos hFr
    have h := hR.smooth _ hm (toTorusSite _ y) _ (isCold_restrictToTorus hp hW) k
      (fun l => torusBond _ (c l)) X
    simp only [localFamilyOfDensity, restrictToTorus_leftTranslate hp]
    exact h
  · intro F hFr y W γ hW
    obtain ⟨hp, hm⟩ := period_eq_of_isCubicTorusAbove hFr
    haveI := hpos hFr
    show f _ (toTorusSite _ y) (restrictToTorus _ (BlockAverages.gaugeTransform γ W)) =
      f _ (toTorusSite _ y) (restrictToTorus _ W)
    rw [restrictToTorus_gaugeTransform hp]
    exact hR.gauge _ hm _ _ _ (isCold_restrictToTorus hp hW)
  · intro F hFr y h W hW
    obtain ⟨hp, hm⟩ := period_eq_of_isCubicTorusAbove hFr
    haveI := hpos hFr
    show f _ (toTorusSite _ (y + h)) (restrictToTorus _ (translateField h W)) =
      f _ (toTorusSite _ y) (restrictToTorus _ W)
    rw [restrictToTorus_translateField hp, hR.translation _ hm _ _ _ (isCold_restrictToTorus hp hW),
      toTorusSite_add hp, add_neg_cancel_right]
  · intro F hFr y W k c X hW h1 h3 hX
    obtain ⟨hp, hm⟩ := period_eq_of_isCubicTorusAbove hFr
    haveI := hpos hFr
    rw [bondDeriv_eq_mixedDeriv hp (G := localFamilyOfDensity f F y) (G' := f _ (toTorusSite _ y))
      (fun _ => rfl), bondSpan_eq_supportDiam hp, hw]
    exact hR.decay _ hm _ _ (isCold_restrictToTorus hp hW) k _ X h1 h3 hX
  · intro F F' hFr hFr' y y' W W' r k h X hW hW' hA hk hbox hX
    obtain ⟨hp, hm⟩ := period_eq_of_isCubicTorusAbove hFr
    obtain ⟨hp', hm'⟩ := period_eq_of_isCubicTorusAbove hFr'
    haveI := hpos hFr
    haveI := hpos hFr'
    rw [bondDeriv_eq_mixedDeriv hp (G := subtractTrivial (localFamilyOfDensity f) F y)
        (G' := centered f _ (toTorusSite _ y)) (fun _ => rfl),
      bondDeriv_eq_mixedDeriv hp' (G := subtractTrivial (localFamilyOfDensity f) F' y')
        (G' := centered f _ (toTorusSite _ y')) (fun _ => rfl), hw]
    have hb : ∀ {E : BlockFrame} (hq : ∀ i, E.period E.depth i = E.period E.depth 0)
        (z : E.Site E.depth),
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
    exact hR.local_density _ _ hm hm' _ _ _ _ r (hA.1 0) (hA.2.1 0) (isCold_restrictToTorus hp hW)
      (isCold_restrictToTorus hp' hW') hagree k h X hk hbox hX
  · obtain ⟨q, hq, hq2⟩ := hL ℓ t x D f hF hR
    refine ⟨q, fun b b' X X' => ?_, hq2⟩
    have hL1 : 0 < ℓ.side := by
      have := hF.L_ge
      omega
    have hm : Tendsto (fun n => (cubicTorusFrame ℓ.side t n).period
        (cubicTorusFrame ℓ.side t n).depth 0) atTop atTop := by
      have hc : ∀ n, (cubicTorusFrame ℓ.side t n).period (cubicTorusFrame ℓ.side t n).depth 0 =
          n * ℓ.side := by
        intro n
        simp [BlockFrame.period, BlockFrame.top, cubicTorusFrame]
      simp only [hc]
      exact tendsto_atTop_mono (fun n => Nat.le_mul_of_pos_right n hL1) tendsto_id
    refine ((hq b b' X X').comp hm).congr' ?_
    filter_upwards [eventually_ge_atTop ℓ.n₀] with n hn
    have hFr : IsCubicTorusAbove ℓ.side t ℓ.n₀ (cubicTorusFrame ℓ.side t n) :=
      ⟨rfl, rfl, n, fun _ => rfl, hn.trans (Nat.le_mul_of_pos_right n hL1)⟩
    obtain ⟨hp, hm'⟩ := period_eq_of_isCubicTorusAbove hFr
    haveI := hpos hFr
    unfold hessianAtTrivial
    rw [bondDeriv_eq_mixedDeriv hp (G := localFamilyOfDensity f (cubicTorusFrame ℓ.side t n) 0)
      (G' := f _ (toTorusSite _ 0)) (fun _ => rfl), toTorusSite_zero hp]
    have hb : (fun l => torusBond ((cubicTorusFrame ℓ.side t n).period
        (cubicTorusFrame ℓ.side t n).depth 0)
        (bondsAt (0 : (cubicTorusFrame ℓ.side t n).Site (cubicTorusFrame ℓ.side t n).depth)
          ![b, b'] l)) =
        ![bondFrom 0 b, bondFrom 0 b'] := by
      funext l
      fin_cases l <;>
        simp [torusBond, bondsAt, bondFrom, toTorusSite_add hp, toTorusSite_siteOfCoords hp,
          toTorusSite_zero hp]
    rw [hb]
    rfl
end YangMills.Construction.ColdStepAtMirrorFrames
end
