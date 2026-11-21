import YangMills.Construction.ColdStepAtMirrorFrames.ColdExpansionIsAnExpansionBelowProof
import YangMills.Construction.ResponseInTheExpansion.RemaindersOfAResponseOnOneTorus
import YangMills.Construction.SummableBoundsOfTheFlow.TheReferenceIsAFamilyBelowProof
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Topology
namespace YangMills.Construction
open BlockAverages TorusFields TorusLumps ColdStepAtMirrorFrames WeightedResponses
namespace ResponseInTheExpansion
namespace TorusComponents
section Casts
variable {a b : ℕ}
theorem intCast_cast_add (h : a = b) (u v : ZMod a) :
    (((u + v).cast : ℤ) : ZMod b) = ((u.cast : ℤ) : ZMod b) + ((v.cast : ℤ) : ZMod b) := by apply _root_.YangMills.Construction.FrameTorusAction.intCast_cast_add <;> assumption
theorem intCast_cast_cast (h : a = b) (u : ZMod b) :
    (((((u.cast : ℤ) : ZMod a)).cast : ℤ) : ZMod b) = u := by apply _root_.YangMills.Construction.FrameTorusAction.intCast_cast_roundTrip <;> assumption
end Casts
section Sites
variable {F : BlockFrame} {m : ℕ}
def frameSite (x : TorusSite m) : F.Site F.depth := siteOfCoords F.depth fun k => ((x k).cast : ℤ)
theorem toTorusSite_frameSite (hp : ∀ i, F.period F.depth i = m) (x : TorusSite m) :
    toTorusSite m (frameSite (F := F) x) = x :=
  funext fun k => intCast_cast_cast (hp k) (x k)
theorem frameSite_toTorusSite (hp : ∀ i, F.period F.depth i = m) (y : F.Site F.depth) :
    frameSite (toTorusSite m y) = y :=
  funext fun k => intCast_cast_cast (hp k).symm (y k)
theorem toTorusSite_add (hp : ∀ i, F.period F.depth i = m) (x y : F.Site F.depth) :
    toTorusSite m (x + y) = toTorusSite m x + toTorusSite m y :=
  funext fun k => intCast_cast_add (hp k) (x k) (y k)
theorem toTorusSite_siteOfCoords (hp : ∀ i, F.period F.depth i = m) (z : Fin 4 → ℤ) :
    toTorusSite m (siteOfCoords (F := F) F.depth z) = siteOfInt z := by apply _root_.YangMills.Construction.FrameTorus.toTorusSite_siteOfCoords <;> assumption
theorem siteOfInt_single (i : Fin 4) :
    (siteOfInt (Pi.single i 1) : TorusSite m) = TorusFields.unitStep m i := by apply _root_.YangMills.Construction.FrameTorusAction.siteOfInt_single <;> assumption
theorem toTorusSite_unitStep (hp : ∀ i, F.period F.depth i = m) (i : Fin 4) :
    toTorusSite m (BlockAverages.unitStep (F := F) F.depth i) = TorusFields.unitStep m i := by
  rw [BlockAverages.unitStep, toTorusSite_siteOfCoords hp, siteOfInt_single]
theorem toTorusSite_injective (hp : ∀ i, F.period F.depth i = m) :
    Function.Injective (toTorusSite m : F.Site F.depth → TorusSite m) := fun x y h => by
  rw [← frameSite_toTorusSite hp x, h, frameSite_toTorusSite hp y]
theorem restrictToTorus_apply (hp : ∀ i, F.period F.depth i = m) (W : F.GaugeField F.depth)
    (y : F.Site F.depth) (i : Fin 4) :
    restrictToTorus m W (toTorusSite m y) i = W y i := by apply _root_.YangMills.Construction.FrameTorus.restrictToTorus_apply <;> assumption
def torusBondOf (m : ℕ) (c : F.Site F.depth × Fin 4) : TorusBond m := (toTorusSite m c.1, c.2)
theorem bondSpan_eq_supportDiam (hp : ∀ i, F.period F.depth i = m) {k : ℕ} (y : F.Site F.depth)
    (c : Fin k → F.Site F.depth × Fin 4) :
    bondSpan y c = supportDiam (toTorusSite m y) fun l => torusBondOf m (c l) := by apply _root_.YangMills.Construction.FrameTorus.bondSpan_eq <;> assumption
theorem isCold_restrictToTorus (hp : ∀ i, F.period F.depth i = m) {s : ℝ} {W : F.GaugeField F.depth}
    (h : IsSmallCurvature s W) : IsCold s (restrictToTorus m W) := by apply _root_.YangMills.Construction.FrameTorus.isCold_restrictToTorus <;> assumption
theorem restrictToTorus_leftTranslate (hp : ∀ i, F.period F.depth i = m) {k : ℕ}
    (c : Fin k → F.Site F.depth × Fin 4) (X : Fin k → imaginaryQuaternions) (τ : Fin k → ℝ)
    (W : F.GaugeField F.depth) :
    restrictToTorus m (leftTranslate (bondSpread c X τ) W) =
      perturb (fun l => torusBondOf m (c l)) X τ (restrictToTorus m W) := by apply _root_.YangMills.Construction.FrameTorus.restrictToTorus_leftTranslate <;> assumption
theorem bondDeriv_eq_mixedDeriv (hp : ∀ i, F.period F.depth i = m) {G : F.GaugeField F.depth → ℝ}
    {G' : TorusField m → ℝ} (hG : ∀ W, G W = G' (restrictToTorus m W)) {k : ℕ} (W : F.GaugeField F.depth)
    (c : Fin k → F.Site F.depth × Fin 4) (X : Fin k → imaginaryQuaternions) :
    bondDeriv G W c X = mixedDeriv G' (restrictToTorus m W) (fun l => torusBondOf m (c l)) X := by apply _root_.YangMills.Construction.FrameTorus.bondDeriv_eq <;> assumption
theorem restrictToTorus_gaugeTransform (hp : ∀ i, F.period F.depth i = m)
    (γ : F.Site F.depth → UnitQuaternion) (W : F.GaugeField F.depth) :
    restrictToTorus m (BlockAverages.gaugeTransform γ W) =
      TorusFields.gaugeTransform (fun x => γ (frameSite x)) (restrictToTorus m W) := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.TorusCoordinates.restrictToTorus_gaugeTransform <;> assumption
theorem restrictToTorus_flatTopField :
    restrictToTorus m (fun _ _ => 1 : F.GaugeField F.depth) = TorusFields.trivialField m := rfl
end Sites
section Calculus
variable {n : ℕ}
theorem mixedDeriv_const_mul (a : ℝ) {k : ℕ} {G : TorusField n → ℝ} {W : TorusField n}
    {c : Fin k → TorusBond n} {X : Fin k → imaginaryQuaternions}
    (hG : ContDiffAt ℝ k (fun σ : Fin k → ℝ => G (perturb c X σ W)) 0) :
    mixedDeriv (fun W => a * G W) W c X = a * mixedDeriv G W c X := by
  unfold mixedDeriv
  have e : (fun σ : Fin k → ℝ => a * G (perturb c X σ W)) =
      a • fun σ : Fin k → ℝ => G (perturb c X σ W) := by
    funext σ
    simp
  rw [e, iteratedFDeriv_const_smul_apply hG]
  simp
theorem mixedDeriv_sub_const (d : ℝ) {k : ℕ} (hk : k ≠ 0) {G : TorusField n → ℝ} {W : TorusField n}
    {c : Fin k → TorusBond n} {X : Fin k → imaginaryQuaternions}
    (hG : ContDiffAt ℝ k (fun σ : Fin k → ℝ => G (perturb c X σ W)) 0) :
    mixedDeriv (fun W => G W - d) W c X = mixedDeriv G W c X := by
  unfold mixedDeriv
  have e : (fun σ : Fin k → ℝ => G (perturb c X σ W) - d) =
      (fun σ : Fin k → ℝ => G (perturb c X σ W)) + fun _ => -d := by
    funext σ
    simp [sub_eq_add_neg]
  rw [e, iteratedFDeriv_add_apply hG contDiffAt_const, iteratedFDeriv_const_of_ne hk]
  simp
end Calculus
theorem natCast_le_three {k : ℕ} (hk : k ≤ 3) : (k : WithTop ℕ∞) ≤ 3 := by
  exact_mod_cast hk
end TorusComponents
open TorusComponents in
theorem responseRemaindersOnTorus : ResponseRemaindersOnTorus := by
  intro ℓ t F m _ δ hw hp hm
  have hb : ∀ {k : ℕ} (z : F.Site F.depth) (h : Fin k → (Fin 4 → ℤ) × Fin 4),
      (fun l => torusBondOf m (bondsAt z h l)) = fun l => bondFrom (toTorusSite m z) (h l) := by
    intro k z h
    funext l
    simp only [torusBondOf, bondsAt, bondFrom, toTorusSite_add hp, toTorusSite_siteOfCoords hp]
  have hagree : ∀ {W W' : F.GaugeField F.depth} {y : F.Site F.depth} {r : ℕ}, AgreeOnBox W W' y y r →
      FieldsAgreeNear (restrictToTorus m W) (restrictToTorus m W') (toTorusSite m y) (toTorusSite m y) r := by
    intro W W' y r hA b hbb
    have e1 : (bondFrom (toTorusSite m y) b).1 = toTorusSite m (y + siteOfCoords F.depth b.1) := by
      simp only [bondFrom, toTorusSite_add hp, toTorusSite_siteOfCoords hp]
    rw [e1, restrictToTorus_apply hp, restrictToTorus_apply hp]
    exact hA.2.2 b hbb
  refine ⟨fun K P hg hC h => ⟨⟨?_, ?_, ?_⟩, ?_⟩, fun E E₃ B f w hf hB hwB => ⟨⟨?_, ?_, ?_⟩, ?_⟩⟩
  · intro y W hW k c X
    have h1 := hC.smooth m hm (toTorusSite m y) _ (isCold_restrictToTorus hp hW) h k
      (fun l => torusBondOf m (c l)) X
    simp only [remainderOnFrame, restrictToTorus_leftTranslate hp]
    exact h1
  · intro y W γ hW
    show responseRemainder P m _ h (restrictToTorus m (BlockAverages.gaugeTransform γ W)) =
      responseRemainder P m _ h (restrictToTorus m W)
    rw [restrictToTorus_gaugeTransform hp]
    unfold responseRemainder
    rw [hg _ _ _ (isCold_restrictToTorus hp hW), hg _ _ _ (isCold_restrictToTorus hp hW)]
  · intro y W k c X hW h1 h3 hX
    rw [bondDeriv_eq_mixedDeriv hp (G := remainderOnFrame P F m h y)
      (G' := responseRemainder P m (toTorusSite m y) h) (fun _ => rfl), bondSpan_eq_supportDiam hp, hw]
    have h2 := hC.decay m hm (toTorusSite m y) _ (isCold_restrictToTorus hp hW) h k
      (fun l => torusBondOf m (c l)) X h1 h3 hX
    split_ifs at h2 ⊢
    · rwa [div_mul_eq_mul_div] at h2
    · exact h2
  · intro y W W' r k hh X hW hW' hA hk hbox hX
    rw [bondDeriv_eq_mixedDeriv hp (G := remainderHat (remainderOnFrame P F m h) y)
      (G' := centeredRemainder P m (toTorusSite m y) h) (fun _ => rfl),
      bondDeriv_eq_mixedDeriv hp (G := remainderHat (remainderOnFrame P F m h) y)
      (G' := centeredRemainder P m (toTorusSite m y) h) (fun _ => rfl), hb, hw]
    have h0 : 2 * r + 2 < m := hp 0 ▸ hA.1 0
    exact hC.compare m hm _ _ _ r h0 (isCold_restrictToTorus hp hW) (isCold_restrictToTorus hp hW')
      (hagree hA) h k hh X hk hbox hX
  · intro y W hW k c X
    have h1 := hf.smooth m hm (toTorusSite m y) _ (isCold_restrictToTorus hp hW) k
      (fun l => torusBondOf m (c l)) X
    simp only [weightedCenteredOnFrame, restrictToTorus_leftTranslate hp, centered]
    exact contDiffAt_const.mul (h1.sub contDiffAt_const)
  · intro y W γ hW
    show w y * centered f m _ (restrictToTorus m (BlockAverages.gaugeTransform γ W)) =
      w y * centered f m _ (restrictToTorus m W)
    rw [restrictToTorus_gaugeTransform hp]
    unfold centered
    rw [hf.gauge m hm _ _ _ (isCold_restrictToTorus hp hW)]
  · intro y W k c X hW h1 h3 hX
    have hs := (hf.smooth m hm (toTorusSite m y) _ (isCold_restrictToTorus hp hW) k
      (fun l => torusBondOf m (c l)) X).of_le (natCast_le_three h3)
    rw [bondDeriv_eq_mixedDeriv hp (G := weightedCenteredOnFrame f F m w y)
      (G' := fun W' => w y * centered f m (toTorusSite m y) W') (fun _ => rfl), bondSpan_eq_supportDiam hp,
      hw, mixedDeriv_const_mul _ (by simpa only [centered] using hs.sub contDiffAt_const)]
    have hk : k ≠ 0 := by omega
    have e : mixedDeriv (centered f m (toTorusSite m y)) (restrictToTorus m W)
        (fun l => torusBondOf m (c l)) X =
        mixedDeriv (f m (toTorusSite m y)) (restrictToTorus m W) (fun l => torusBondOf m (c l)) X :=
      mixedDeriv_sub_const _ hk hs
    rw [e, abs_mul]
    have h2 := hf.decay m hm (toTorusSite m y) _ (isCold_restrictToTorus hp hW) k
      (fun l => torusBondOf m (c l)) X h1 h3 hX
    have hG : 0 < ℓ.weight (supportDiam (toTorusSite m y) fun l => torusBondOf m (c l)) := by
      rw [← hw]
      unfold torusDecayFactor
      exact mul_pos (lt_of_lt_of_le one_pos (le_max_left _ _)) (Real.exp_pos _)
    have h4 := mul_le_mul (hwB y) h2 (abs_nonneg _) hB
    refine h4.trans (le_of_eq ?_)
    split_ifs <;> ring
  · intro y W W' r k hh X hW hW' hA hk hbox hX
    have hs : ∀ V : F.GaugeField F.depth, IsSmallCurvature ℓ.threshold V →
        ContDiffAt ℝ k (fun σ : Fin k → ℝ => centered f m (toTorusSite m y)
          (perturb (fun l => torusBondOf m (bondsAt y hh l)) X σ (restrictToTorus m V))) 0 := by
      intro V hV
      have h1 := (hf.smooth m hm (toTorusSite m y) _ (isCold_restrictToTorus hp hV) k
        (fun l => torusBondOf m (bondsAt y hh l)) X).of_le (natCast_le_three (show k ≤ 3 by omega))
      simpa only [centered] using h1.sub contDiffAt_const
    have e : ∀ V, remainderHat (weightedCenteredOnFrame f F m w) y V =
        w y * centered f m (toTorusSite m y) (restrictToTorus m V) := by
      intro V
      have e0 : centered f m (toTorusSite m y) (restrictToTorus m (fun _ _ => 1 : F.GaugeField F.depth)) = 0 := by
        show f m _ _ - f m _ _ = 0
        rw [restrictToTorus_flatTopField]
        ring
      simp only [remainderHat, weightedCenteredOnFrame, e0]
      ring
    rw [bondDeriv_eq_mixedDeriv hp (G := remainderHat (weightedCenteredOnFrame f F m w) y)
      (G' := fun V => w y * centered f m (toTorusSite m y) V) e,
      bondDeriv_eq_mixedDeriv hp (G := remainderHat (weightedCenteredOnFrame f F m w) y)
      (G' := fun V => w y * centered f m (toTorusSite m y) V) e,
      mixedDeriv_const_mul _ (hs W hW), mixedDeriv_const_mul _ (hs W' hW'), ← mul_sub, abs_mul, hb, hw]
    have h0 : 2 * r + 2 < m := hp 0 ▸ hA.1 0
    have h2 := hf.local_density m m hm hm _ _ _ _ r h0 h0 (isCold_restrictToTorus hp hW)
      (isCold_restrictToTorus hp hW') (hagree hA) k hh X hk hbox hX
    have h4 := mul_le_mul (hwB y) h2 (abs_nonneg _) hB
    exact h4.trans (le_of_eq (by ring))
end ResponseInTheExpansion
end YangMills.Construction
end
