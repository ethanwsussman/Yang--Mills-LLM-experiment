import YangMills.Construction.RunningCouplingSlope.DensityOfTheStepOnTwoToriAtParametersProof
import YangMills.Construction.SummableBoundsOfTheFlow.LeastActionOfAFrameOnItsTorus
import YangMills.Construction.ColdStepAtMirrorFrames.LowerFamiliesReadOnTori
import YangMills.Construction.SummableBoundsOfTheFlow.DerivativesOfATopFamilyOnToriProof
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Topology
namespace YangMills.Construction
open BlockAverages TorusFields TorusLumps Filter
namespace ColdStepAtMirrorFrames
namespace TorusSites
section Casts
variable {a b : ℕ}
theorem intCast_cast_neg (h : a = b) (u : ZMod a) :
    (((-u).cast : ℤ) : ZMod b) = -((u.cast : ℤ) : ZMod b) := by apply _root_.YangMills.Construction.FrameTorusAction.intCast_cast_neg <;> assumption
theorem intCast_cast_intCast (h : a = b) (z : ℤ) : (((z : ZMod a).cast : ℤ) : ZMod b) = (z : ZMod b) := by apply _root_.YangMills.Construction.FrameTorusAction.intCast_cast_intCast <;> assumption
end Casts
section Sites
variable {F : BlockFrame} {m j : ℕ}
def frameSite (j : ℕ) (x : TorusSite m) : F.Site j := siteOfCoords j fun k => ((x k).cast : ℤ)
theorem toTorusSite_frameSite (hp : ∀ i, F.period j i = m) (x : TorusSite m) :
    toTorusSite m (frameSite (F := F) j x) = x := by apply _root_.YangMills.Construction.FrameTorusAction.toTorusSite_siteOfTorusSite <;> assumption
theorem frameSite_toTorusSite (hp : ∀ i, F.period j i = m) (y : F.Site j) :
    frameSite j (toTorusSite m y) = y := by apply _root_.YangMills.Construction.FrameTorusAction.siteOfTorusSite_toTorusSite <;> assumption
theorem toTorusSite_add' (hp : ∀ i, F.period j i = m) (x y : F.Site j) :
    toTorusSite m (x + y) = toTorusSite m x + toTorusSite m y := by apply _root_.YangMills.Construction.FrameTorusAction.toTorusSite_add <;> assumption
theorem toTorusSite_neg' (hp : ∀ i, F.period j i = m) (x : F.Site j) :
    toTorusSite m (-x) = -toTorusSite m x :=
  funext fun k => intCast_cast_neg (hp k) (x k)
theorem toTorusSite_sub' (hp : ∀ i, F.period j i = m) (x y : F.Site j) :
    toTorusSite m (x - y) = toTorusSite m x - toTorusSite m y := by
  rw [sub_eq_add_neg, toTorusSite_add' hp, toTorusSite_neg' hp, sub_eq_add_neg]
theorem toTorusSite_siteOfCoords' (hp : ∀ i, F.period j i = m) (z : Fin 4 → ℤ) :
    toTorusSite m (siteOfCoords (F := F) j z) = siteOfInt z :=
  funext fun k => intCast_cast_intCast (hp k) (z k)
theorem toTorusSite_zero' (hp : ∀ i, F.period j i = m) : toTorusSite m (0 : F.Site j) = 0 := by
  have h := toTorusSite_add' hp (0 : F.Site j) 0
  rw [add_zero] at h
  exact left_eq_add.mp h
theorem toTorusSite_blockUnitStep (hp : ∀ i, F.period j i = m) (i : Fin 4) :
    toTorusSite m (BlockAverages.unitStep (F := F) j i) = TorusFields.unitStep m i := by apply _root_.YangMills.Construction.FrameTorusAction.toTorusSite_unitStep <;> assumption
theorem toTorusSite_injective' (hp : ∀ i, F.period j i = m) :
    Function.Injective (toTorusSite m : F.Site j → TorusSite m) := by apply _root_.YangMills.Construction.RunningCouplingSlope.TorusComparison.toTorusSite_injective <;> assumption
theorem siteSupDist_eq_torus (hp : ∀ i, F.period j i = m) (y z : F.Site j) :
    siteSupDist y z = supDist (toTorusSite m y) (toTorusSite m z) := by apply _root_.YangMills.SharedProofs.p2088 <;> assumption
def torusBond (m : ℕ) (c : F.Site j × Fin 4) : TorusBond m := (toTorusSite m c.1, c.2)
theorem bondSpan_eq_torus (hp : ∀ i, F.period j i = m) {k : ℕ} (y : F.Site j)
    (c : Fin k → F.Site j × Fin 4) :
    bondSpan y c = supportDiam (toTorusSite m y) fun l => torusBond m (c l) := by apply _root_.YangMills.DeltaSharedProofs.p501818 <;> assumption
theorem restrictToTorus_leftTranslate' (hp : ∀ i, F.period j i = m) {k : ℕ}
    (c : Fin k → F.Site j × Fin 4) (X : Fin k → imaginaryQuaternions) (τ : Fin k → ℝ)
    (W : F.GaugeField j) :
    restrictToTorus m (leftTranslate (bondSpread c X τ) W) =
      perturb (fun l => torusBond m (c l)) X τ (restrictToTorus m W) := by apply _root_.YangMills.Construction.RunningCouplingSlope.TorusComparison.restrictToTorus_leftTranslate <;> assumption
theorem restrictToTorus_gauge (hp : ∀ i, F.period j i = m) (γ : F.Site j → UnitQuaternion)
    (W : F.GaugeField j) :
    restrictToTorus m (BlockAverages.gaugeTransform γ W) =
      TorusFields.gaugeTransform (fun x => γ (frameSite j x)) (restrictToTorus m W) := by
  funext x i
  have h : frameSite (F := F) j (x + TorusFields.unitStep m i) =
      frameSite j x + BlockAverages.unitStep j i := by
    apply toTorusSite_injective' hp
    rw [toTorusSite_frameSite hp, toTorusSite_add' hp, toTorusSite_frameSite hp,
      toTorusSite_blockUnitStep hp]
  show γ (frameSite j x) * W (frameSite j x) i * (γ (frameSite j x + BlockAverages.unitStep j i))⁻¹ =
    γ (frameSite j x) * W (frameSite j x) i * (γ (frameSite j (x + TorusFields.unitStep m i)))⁻¹
  rw [h]
theorem restrictToTorus_translateField' (hp : ∀ i, F.period j i = m) (h : F.Site j) (W : F.GaugeField j) :
    restrictToTorus m (translateField h W) = TorusFields.translate (-toTorusSite m h) (restrictToTorus m W) := by
  funext x i
  have h1 : frameSite (F := F) j (x + -toTorusSite m h) = frameSite j x - h := by
    apply toTorusSite_injective' hp
    rw [toTorusSite_frameSite hp, toTorusSite_sub' hp, toTorusSite_frameSite hp, sub_eq_add_neg]
  show W (frameSite j x - h) i = W (frameSite j (x + -toTorusSite m h)) i
  rw [h1]
theorem readAtLevel_restrict (hp : ∀ i, F.period j i = m) (W : F.GaugeField j) :
    readAtLevel F j (restrictToTorus m W) = W := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.SecondOrderAtConstantCurvature.readAtLevel_restrictToTorus <;> assumption
theorem restrict_readAtLevel (hp : ∀ i, F.period j i = m) (V : TorusField m) :
    restrictToTorus m (readAtLevel F j V) = V := by apply _root_.YangMills.Construction.RunningCouplingSlope.TorusComparison.restrictToTorus_readAtLevel <;> assumption
theorem readAtLevel_gauge (hp : ∀ i, F.period j i = m) (γ : TorusSite m → UnitQuaternion)
    (V : TorusField m) :
    readAtLevel F j (TorusFields.gaugeTransform γ V) =
      BlockAverages.gaugeTransform (fun x => γ (toTorusSite m x)) (readAtLevel F j V) := by
  have h : TorusFields.gaugeTransform γ V = restrictToTorus m
      (BlockAverages.gaugeTransform (fun x => γ (toTorusSite m x)) (readAtLevel F j V)) := by
    rw [restrictToTorus_gauge hp, restrict_readAtLevel hp]
    funext x i
    simp only [TorusFields.gaugeTransform, toTorusSite_frameSite hp]
  rw [h, readAtLevel_restrict hp]
theorem readAtLevel_translate' (hp : ∀ i, F.period j i = m) (u : TorusSite m) (V : TorusField m) :
    readAtLevel F j (TorusFields.translate u V) = translateField (-frameSite j u) (readAtLevel F j V) := by
  have h : TorusFields.translate u V =
      restrictToTorus m (translateField (-frameSite (F := F) j u) (readAtLevel F j V)) := by
    rw [restrictToTorus_translateField' hp, restrict_readAtLevel hp, toTorusSite_neg' hp, neg_neg,
      toTorusSite_frameSite hp]
  rw [h, readAtLevel_restrict hp]
theorem isSmallCurvature_readAtLevel' (hp : ∀ i, F.period j i = m) {s : ℝ} {V : TorusField m}
    (h : IsCold s V) : IsSmallCurvature s (readAtLevel F j V) := by apply _root_.YangMills.Construction.RunningCouplingSlope.TorusComparison.isSmallCurvature_readAtLevel <;> assumption
def frameBond (j : ℕ) (c : TorusBond m) : F.Site j × Fin 4 := (frameSite j c.1, c.2)
theorem torusBond_frameBond (hp : ∀ i, F.period j i = m) (c : TorusBond m) :
    torusBond (F := F) (j := j) m (frameBond j c) = c := by apply _root_.YangMills.Construction.RunningCouplingSlope.TorusComparison.torusBondOfBond_bondOfTorusBond <;> assumption
theorem mixedDeriv_eq_frame (hp : ∀ i, F.period j i = m) {G : F.GaugeField j → ℝ}
    {G' : TorusField m → ℝ} (hG : ∀ V, G' V = G (readAtLevel F j V)) {k : ℕ} (V : TorusField m)
    (c : Fin k → TorusBond m) (X : Fin k → imaginaryQuaternions) :
    mixedDeriv G' V c X = bondDeriv G (readAtLevel F j V) (fun l => frameBond j (c l)) X := by apply _root_.YangMills.Construction.RunningCouplingSlope.TorusComparison.mixedDeriv_eq_bondDeriv <;> assumption
end Sites
end TorusSites
open TorusSites in
theorem localFamilyOnTori_holds : LocalFamilyOnTori := by
  intro ℓ t δ E E₃ f hfits hn₁ hδ hE hE₃ hrow
  have hLpos : 0 < ℓ.side := hfits.L_odd.pos
  have hper : ∀ n : ℕ, ℓ.side ∣ n → ∀ i,
      (torusFrame ℓ.side t (n / ℓ.side)).period (torusFrame ℓ.side t (n / ℓ.side)).depth i = n := by
    intro n hn i
    have : (torusFrame ℓ.side t (n / ℓ.side)).top - (torusFrame ℓ.side t (n / ℓ.side)).depth = 1 := by
      simp [BlockFrame.top]
    simp only [BlockFrame.period, this, pow_one]
    exact Nat.div_mul_cancel hn
  have hlow : ∀ n : ℕ, ℓ.n₀ ≤ n → ℓ.side ∣ n →
      IsCubicTorusAbove ℓ.side t ℓ.n₀ (torusFrame ℓ.side t (n / ℓ.side)) := by
    intro n hn hd
    exact ⟨rfl, rfl, n / ℓ.side, fun _ => rfl, by rw [Nat.div_mul_cancel hd]; exact hn⟩
  have hG : ∀ (n : ℕ) (y : TorusSite n) (V : TorusField n), readOnMultiples ℓ.side t f n y V =
      f (torusFrame ℓ.side t (n / ℓ.side)) (frameSite _ y)
        (readAtLevel (torusFrame ℓ.side t (n / ℓ.side)) (torusFrame ℓ.side t (n / ℓ.side)).depth V) :=
    fun _ _ _ => rfl
  have hweight : ∀ v : ℕ, torusDecayFactor ℓ.side δ (v : ℝ) = ℓ.weight v := by
    intro v
    unfold torusDecayFactor StepParameters.weight
    rw [hn₁, hδ]
  have hhat : ∀ (n : ℕ) (y : TorusSite n) (V : TorusField n), centered (readOnMultiples ℓ.side t f) n y V =
      subtractTrivial f (torusFrame ℓ.side t (n / ℓ.side)) (frameSite _ y)
        (readAtLevel (torusFrame ℓ.side t (n / ℓ.side)) (torusFrame ℓ.side t (n / ℓ.side)).depth V) :=
    fun _ _ _ => rfl
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · intro n _ hn hd y V hV k c X
    have h := hrow.smooth _ (hlow n hn hd) (frameSite _ y) _ (isSmallCurvature_readAtLevel' (hper n hd) hV) k
      (fun l => frameBond _ (c l)) X
    have hfun : (fun τ : Fin k → ℝ => readOnMultiples ℓ.side t f n y (perturb c X τ V)) =
        fun τ => f (torusFrame ℓ.side t (n / ℓ.side)) (frameSite _ y)
          (leftTranslate (bondSpread (fun l => frameBond (F := torusFrame ℓ.side t (n / ℓ.side)) _ (c l)) X τ)
            (readAtLevel (torusFrame ℓ.side t (n / ℓ.side)) (torusFrame ℓ.side t (n / ℓ.side)).depth V)) := by
      funext τ
      rw [hG]
      congr 1
      have h1 := restrictToTorus_leftTranslate' (hper n hd)
        (fun l => frameBond (F := torusFrame ℓ.side t (n / ℓ.side)) _ (c l)) X τ
        (readAtLevel (torusFrame ℓ.side t (n / ℓ.side)) (torusFrame ℓ.side t (n / ℓ.side)).depth V)
      rw [restrict_readAtLevel (hper n hd)] at h1
      simp only [torusBond_frameBond (hper n hd)] at h1
      rw [← h1, readAtLevel_restrict (hper n hd)]
    rw [hfun]
    exact h
  · intro n _ hn hd y γ V hV
    rw [hG, hG, readAtLevel_gauge (hper n hd)]
    exact hrow.gauge_invariant _ (hlow n hn hd) _ _ _ (isSmallCurvature_readAtLevel' (hper n hd) hV)
  · intro n _ hn hd y u V hV
    rw [hG, hG, readAtLevel_translate' (hper n hd)]
    have h := hrow.translation_invariant _ (hlow n hn hd) (frameSite _ (y + u)) (-frameSite _ u)
      (readAtLevel (torusFrame ℓ.side t (n / ℓ.side)) (torusFrame ℓ.side t (n / ℓ.side)).depth V)
      (isSmallCurvature_readAtLevel' (hper n hd) hV)
    have hsum : frameSite (F := torusFrame ℓ.side t (n / ℓ.side)) (torusFrame ℓ.side t (n / ℓ.side)).depth
        (y + u) + -frameSite _ u = frameSite _ y := by
      apply toTorusSite_injective' (hper n hd)
      rw [toTorusSite_add' (hper n hd), toTorusSite_neg' (hper n hd), toTorusSite_frameSite (hper n hd),
        toTorusSite_frameSite (hper n hd), toTorusSite_frameSite (hper n hd)]
      abel
    rw [hsum] at h
    exact h
  · intro n _ hn hd y V hV k c X h1 h3 hX
    rw [mixedDeriv_eq_frame (hper n hd) (hG n y)]
    have h := hrow.decay _ (hlow n hn hd) (frameSite _ y)
      (readAtLevel (torusFrame ℓ.side t (n / ℓ.side)) (torusFrame ℓ.side t (n / ℓ.side)).depth V) k
      (fun l => frameBond _ (c l)) X (isSmallCurvature_readAtLevel' (hper n hd) hV) h1 h3 hX
    rw [bondSpan_eq_torus (hper n hd), hweight] at h
    simp only [toTorusSite_frameSite (hper n hd), torusBond_frameBond (hper n hd)] at h
    refine h.trans ?_
    have hw : 0 < ℓ.weight (supportDiam y c) := by
      unfold StepParameters.weight
      positivity
    apply div_le_div_of_nonneg_right _ hw.le
    split_ifs
    · exact le_rfl
    · exact hE₃
  · intro n n' _ _ hn hn' hd hd' y y' V V' m h1 h2 hV hV' hA k h X hk hbox hX
    rw [mixedDeriv_eq_frame (hper n hd) (hhat n y), mixedDeriv_eq_frame (hper n' hd') (hhat n' y')]
    have hb : ∀ {n : ℕ} (hd : ℓ.side ∣ n) (z : TorusSite n),
        (fun l => frameBond (F := torusFrame ℓ.side t (n / ℓ.side)) (torusFrame ℓ.side t (n / ℓ.side)).depth
          (bondFrom z (h l))) = bondsAt (frameSite _ z) h := by
      intro n hd z
      funext l
      refine Prod.ext ?_ rfl
      apply toTorusSite_injective' (hper n hd)
      simp only [frameBond, bondFrom, bondsAt]
      rw [toTorusSite_frameSite (hper n hd), toTorusSite_add' (hper n hd), toTorusSite_frameSite (hper n hd),
        toTorusSite_siteOfCoords' (hper n hd)]
    rw [hb hd y, hb hd' y']
    have hagree : AgreeOnBox
        (readAtLevel (torusFrame ℓ.side t (n / ℓ.side)) (torusFrame ℓ.side t (n / ℓ.side)).depth V)
        (readAtLevel (torusFrame ℓ.side t (n' / ℓ.side)) (torusFrame ℓ.side t (n' / ℓ.side)).depth V')
        (frameSite _ y) (frameSite _ y') m := by
      refine ⟨fun i => by rw [hper n hd]; exact h1, fun i => by rw [hper n' hd']; exact h2, fun b hbb => ?_⟩
      have hq := hA b hbb
      have e1 : toTorusSite n (frameSite (F := torusFrame ℓ.side t (n / ℓ.side))
          (torusFrame ℓ.side t (n / ℓ.side)).depth y + siteOfCoords _ b.1) = (bondFrom y b).1 := by
        rw [toTorusSite_add' (hper n hd), toTorusSite_frameSite (hper n hd),
          toTorusSite_siteOfCoords' (hper n hd)]
        rfl
      have e2 : toTorusSite n' (frameSite (F := torusFrame ℓ.side t (n' / ℓ.side))
          (torusFrame ℓ.side t (n' / ℓ.side)).depth y' + siteOfCoords _ b.1) = (bondFrom y' b).1 := by
        rw [toTorusSite_add' (hper n' hd'), toTorusSite_frameSite (hper n' hd'),
          toTorusSite_siteOfCoords' (hper n' hd')]
        rfl
      show V (toTorusSite n _) b.2 = V' (toTorusSite n' _) b.2
      rw [e1, e2]
      exact hq
    have hl := hrow.locality _ _ (hlow n hn hd) (hlow n' hn' hd') _ _ _ _ m k h X
      (isSmallCurvature_readAtLevel' (hper n hd) hV) (isSmallCurvature_readAtLevel' (hper n' hd') hV')
      hagree hk hbox hX
    rw [hweight] at hl
    refine hl.trans ?_
    have hw : 0 < ℓ.weight m := by
      unfold StepParameters.weight
      positivity
    exact div_le_div_of_nonneg_right hE₃ hw.le
  · intro m b b' X X' hm
    have hd : ℓ.side ∣ ℓ.side * m := Dvd.intro m rfl
    unfold flatSecondDeriv
    have hfn : ∀ V : TorusField (ℓ.side * m), readOnMultiples ℓ.side t f (ℓ.side * m) 0 V =
        f (torusFrame ℓ.side t (ℓ.side * m / ℓ.side)) (frameSite _ 0)
          (readAtLevel (torusFrame ℓ.side t (ℓ.side * m / ℓ.side))
            (torusFrame ℓ.side t (ℓ.side * m / ℓ.side)).depth V) := fun _ => rfl
    rw [mixedDeriv_eq_frame (hper _ hd) (G := f (torusFrame ℓ.side t (ℓ.side * m / ℓ.side)) (frameSite _ 0)) hfn]
    have h0 : frameSite (F := torusFrame ℓ.side t (ℓ.side * m / ℓ.side))
        (torusFrame ℓ.side t (ℓ.side * m / ℓ.side)).depth (0 : TorusSite (ℓ.side * m)) = 0 := by
      apply toTorusSite_injective' (hper _ hd)
      rw [toTorusSite_frameSite (hper _ hd), toTorusSite_zero' (hper _ hd)]
    have hbd : (fun l => frameBond (F := torusFrame ℓ.side t (ℓ.side * m / ℓ.side))
        (torusFrame ℓ.side t (ℓ.side * m / ℓ.side)).depth
        ((![bondFrom 0 b, bondFrom 0 b'] : Fin 2 → TorusBond (ℓ.side * m)) l)) = bondsAt 0 ![b, b'] := by
      funext l
      refine Prod.ext ?_ ?_
      · apply toTorusSite_injective' (hper _ hd)
        fin_cases l <;>
          simp [frameBond, bondFrom, bondsAt, toTorusSite_frameSite (hper _ hd), toTorusSite_add' (hper _ hd),
            toTorusSite_siteOfCoords' (hper _ hd), toTorusSite_zero' (hper _ hd)]
      · fin_cases l <;> rfl
    rw [hbd, h0]
    have key : ∀ G : BlockFrame, G = cubicTorusFrame ℓ.side t m →
        bondDeriv (f G 0) (uniformField G G.depth) (bondsAt 0 ![b, b']) ![X, X'] =
          hessianAtTrivial f ℓ.side t m b b' X X' := by
      intro G hGe
      subst hGe
      rfl
    exact key _ (by
      show (⟨ℓ.side, t, fun _ => ℓ.side * m / ℓ.side⟩ : BlockFrame) = ⟨ℓ.side, t, fun _ => m⟩
      rw [Nat.mul_div_cancel_left m hLpos])
  · intro n y W hn
    have hM : ∀ i, (torusFrame ℓ.side t n).period (torusFrame ℓ.side t n).depth i = n * ℓ.side := by
      intro i
      have : (torusFrame ℓ.side t n).top - (torusFrame ℓ.side t n).depth = 1 := by simp [BlockFrame.top]
      simp only [BlockFrame.period, this, pow_one]
      rfl
    have key : ∀ G : BlockFrame, G = torusFrame ℓ.side t n → ∀ (hG : ∀ i, G.period G.depth i = n * ℓ.side)
        (y' : G.Site G.depth) (W' : G.GaugeField G.depth),
        subtractTrivial f G (frameSite _ (toTorusSite (n * ℓ.side) y'))
          (readAtLevel G G.depth (restrictToTorus (n * ℓ.side) W')) = subtractTrivial f G y' W' := by
      intro G _ hG y' W'
      rw [frameSite_toTorusSite hG, readAtLevel_restrict hG]
    have hframe : torusFrame ℓ.side t (n * ℓ.side / ℓ.side) = torusFrame ℓ.side t n := by
      rw [Nat.mul_div_cancel n hLpos]
    have hdvd : ℓ.side ∣ n * ℓ.side := Dvd.intro_left n rfl
    show subtractTrivial f (torusFrame ℓ.side t (n * ℓ.side / ℓ.side)) (frameSite _ (toTorusSite _ y))
        (readAtLevel (torusFrame ℓ.side t (n * ℓ.side / ℓ.side))
          (torusFrame ℓ.side t (n * ℓ.side / ℓ.side)).depth (restrictToTorus _ W)) = _
    have hgen : ∀ G : BlockFrame, G = torusFrame ℓ.side t n →
        subtractTrivial f G (frameSite _ (toTorusSite (n * ℓ.side) y))
          (readAtLevel G G.depth (restrictToTorus (n * ℓ.side) W)) =
          subtractTrivial f (torusFrame ℓ.side t n) y W := by
      intro G hGe
      subst hGe
      exact key _ rfl hM y W
    exact hgen _ hframe
end ColdStepAtMirrorFrames
end YangMills.Construction
end
