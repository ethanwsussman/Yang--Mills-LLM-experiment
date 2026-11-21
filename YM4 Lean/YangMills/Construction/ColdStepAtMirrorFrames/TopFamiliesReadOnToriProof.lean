import YangMills.Construction.RunningCouplingSlope.DensityOfTheStepOnTwoToriAtParametersProof
import YangMills.Construction.SummableBoundsOfTheFlow.DerivativesOfATopFamilyOnToriProof
import YangMills.Construction.SummableBoundsOfTheFlow.LeastActionOfAFrameOnItsTorus
import YangMills.Construction.ColdStepAtMirrorFrames.LowerFamiliesRestrictToToriProofForm
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Topology
open YangMills.Construction.BlockAverages YangMills.Construction.TorusFields YangMills.Construction.TorusLumps Filter
namespace YangMills.Construction.ColdStepAtMirrorFrames
namespace TorusComponents
section Casts
variable {a b : ℕ}
theorem intCast_cast_neg (h : a = b) (u : ZMod a) :
    (((-u).cast : ℤ) : ZMod b) = -((u.cast : ℤ) : ZMod b) := by apply _root_.YangMills.Construction.FrameTorusAction.intCast_cast_neg <;> assumption
theorem intCast_cast_intCast (h : a = b) (z : ℤ) :
    (((z : ZMod a).cast : ℤ) : ZMod b) = (z : ZMod b) := by apply _root_.YangMills.Construction.FrameTorusAction.intCast_cast_intCast <;> assumption
end Casts
section Sites
variable {F : BlockFrame} {m j : ℕ}
def siteOfTorus (j : ℕ) (x : TorusSite m) : F.Site j := siteOfCoords j fun k => ((x k).cast : ℤ)
theorem toTorusSite_siteOfTorus (hp : ∀ i, F.period j i = m) (x : TorusSite m) :
    toTorusSite m (siteOfTorus (F := F) j x) = x := by apply _root_.YangMills.Construction.FrameTorusAction.toTorusSite_siteOfTorusSite <;> assumption
theorem siteOfTorus_toTorusSite (hp : ∀ i, F.period j i = m) (y : F.Site j) :
    siteOfTorus j (toTorusSite m y) = y := by apply _root_.YangMills.Construction.FrameTorusAction.siteOfTorusSite_toTorusSite <;> assumption
theorem toTorusSite_add (hp : ∀ i, F.period j i = m) (x y : F.Site j) :
    toTorusSite m (x + y) = toTorusSite m x + toTorusSite m y := by apply _root_.YangMills.Construction.FrameTorusAction.toTorusSite_add <;> assumption
theorem toTorusSite_neg (hp : ∀ i, F.period j i = m) (x : F.Site j) :
    toTorusSite m (-x) = -toTorusSite m x :=
  funext fun k => intCast_cast_neg (hp k) (x k)
theorem toTorusSite_siteOfCoords (hp : ∀ i, F.period j i = m) (z : Fin 4 → ℤ) :
    toTorusSite m (siteOfCoords (F := F) j z) = siteOfInt z :=
  funext fun k => intCast_cast_intCast (hp k) (z k)
theorem toTorusSite_zero (hp : ∀ i, F.period j i = m) : toTorusSite m (0 : F.Site j) = 0 := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.TorusSites.toTorusSite_zero' <;> assumption
theorem toTorusSite_injective (hp : ∀ i, F.period j i = m) :
    Function.Injective (toTorusSite m : F.Site j → TorusSite m) := by apply _root_.YangMills.Construction.RunningCouplingSlope.TorusComparison.toTorusSite_injective <;> assumption
def bondToTorus (m : ℕ) (c : F.Site j × Fin 4) : TorusBond m := (toTorusSite m c.1, c.2)
theorem bondSpan_eq_supportDiam (hp : ∀ i, F.period j i = m) {k : ℕ} (y : F.Site j)
    (c : Fin k → F.Site j × Fin 4) :
    bondSpan y c = supportDiam (toTorusSite m y) fun l => bondToTorus m (c l) := by apply _root_.YangMills.DeltaSharedProofs.p501818 <;> assumption
theorem restrictToTorus_leftTranslate (hp : ∀ i, F.period j i = m) {k : ℕ}
    (c : Fin k → F.Site j × Fin 4) (X : Fin k → imaginaryQuaternions) (τ : Fin k → ℝ)
    (W : F.GaugeField j) :
    restrictToTorus m (leftTranslate (bondSpread c X τ) W) =
      perturb (fun l => bondToTorus m (c l)) X τ (restrictToTorus m W) := by apply _root_.YangMills.Construction.RunningCouplingSlope.TorusComparison.restrictToTorus_leftTranslate <;> assumption
theorem bondDeriv_eq_mixedDeriv (hp : ∀ i, F.period j i = m) {G : F.GaugeField j → ℝ}
    {G' : TorusField m → ℝ} (hG : ∀ W, G W = G' (restrictToTorus m W)) {k : ℕ}
    (W : F.GaugeField j) (c : Fin k → F.Site j × Fin 4) (X : Fin k → imaginaryQuaternions) :
    bondDeriv G W c X = mixedDeriv G' (restrictToTorus m W) (fun l => bondToTorus m (c l)) X := by apply _root_.YangMills.Construction.RunningCouplingSlope.TorusComparison.bondDeriv_eq_mixedDeriv <;> assumption
theorem restrictToTorus_translateField (hp : ∀ i, F.period j i = m) (h : F.Site j)
    (W : F.GaugeField j) :
    restrictToTorus m (translateField h W) =
      TorusFields.translate (-toTorusSite m h) (restrictToTorus m W) := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.TorusSites.restrictToTorus_translateField' <;> assumption
theorem readAtLevel_restrictToTorus (hp : ∀ i, F.period j i = m) (W : F.GaugeField j) :
    readAtLevel F j (restrictToTorus m W) = W := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.SecondOrderAtConstantCurvature.readAtLevel_restrictToTorus <;> assumption
theorem restrictToTorus_readAtLevel (hp : ∀ i, F.period j i = m) (V : TorusField m) :
    restrictToTorus m (readAtLevel F j V) = V := by apply _root_.YangMills.Construction.RunningCouplingSlope.TorusComparison.restrictToTorus_readAtLevel <;> assumption
theorem readAtLevel_gaugeTransform (hp : ∀ i, F.period j i = m) (γ : TorusSite m → UnitQuaternion)
    (V : TorusField m) :
    readAtLevel F j (TorusFields.gaugeTransform γ V) =
      BlockAverages.gaugeTransform (fun x => γ (toTorusSite m x)) (readAtLevel F j V) := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.TorusSites.readAtLevel_gauge <;> assumption
theorem readAtLevel_translate (hp : ∀ i, F.period j i = m) (u : TorusSite m) (V : TorusField m) :
    readAtLevel F j (TorusFields.translate u V) = translateField (-siteOfTorus j u) (readAtLevel F j V) := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.TorusSites.readAtLevel_translate' <;> assumption
theorem isSmallCurvature_readAtLevel (hp : ∀ i, F.period j i = m) {s : ℝ} {V : TorusField m}
    (h : IsCold s V) : IsSmallCurvature s (readAtLevel F j V) := by apply _root_.YangMills.Construction.RunningCouplingSlope.TorusComparison.isSmallCurvature_readAtLevel <;> assumption
def bondOfTorus (j : ℕ) (c : TorusBond m) : F.Site j × Fin 4 := (siteOfTorus j c.1, c.2)
theorem bondToTorus_bondOfTorus (hp : ∀ i, F.period j i = m) (c : TorusBond m) :
    bondToTorus (F := F) (j := j) m (bondOfTorus j c) = c := by apply _root_.YangMills.Construction.RunningCouplingSlope.TorusComparison.torusBondOfBond_bondOfTorusBond <;> assumption
theorem mixedDeriv_eq_bondDeriv (hp : ∀ i, F.period j i = m) {G : F.GaugeField j → ℝ}
    {G' : TorusField m → ℝ} (hG : ∀ V, G' V = G (readAtLevel F j V)) {k : ℕ} (V : TorusField m)
    (c : Fin k → TorusBond m) (X : Fin k → imaginaryQuaternions) :
    mixedDeriv G' V c X = bondDeriv G (readAtLevel F j V) (fun l => bondOfTorus j (c l)) X := by apply _root_.YangMills.Construction.RunningCouplingSlope.TorusComparison.mixedDeriv_eq_bondDeriv <;> assumption
theorem mem_finiteCells (F : BlockFrame) (hs : ∀ i, 0 < F.extent i) (z : F.Cell) :
    z ∈ finiteCells F := by apply _root_.YangMills.Construction.FrameTorusAction.mem_finiteCells <;> assumption
end Sites
theorem torusFrame_period (L t n : ℕ) (i : Fin 4) :
    (torusFrame L t n).period (torusFrame L t n).top i = n := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.SecondOrderAtConstantCurvature.torusFrame_period_top <;> assumption
end TorusComponents
open TorusComponents in
theorem topFamilyOnTori_holds : TopFamilyOnTori := by
  intro L t n₀ s g hn₀
  have hT : ∀ n : ℕ, n₀ ≤ n → IsCubicTopTorus L t n₀ (torusFrame L t n) := fun n hn =>
    ⟨rfl, rfl, n, fun _ => rfl, hn⟩
  have hp : ∀ n, ∀ i, (torusFrame L t n).period (torusFrame L t n).top i = n := torusFrame_period L t
  have hG : ∀ (n : ℕ) (y : TorusSite n) (V : TorusField n), densityOfTopFamily L t g n y V =
      g (torusFrame L t n) (siteOfTorus _ y)
        (readAtLevel (torusFrame L t n) (torusFrame L t n).top V) := fun _ _ _ => rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro hD
    refine ⟨?_, ?_, ?_⟩
    · intro n _ hn y V hV k c X
      have h := hD.smooth _ (hT n hn) (siteOfTorus _ y) _ (isSmallCurvature_readAtLevel (hp n) hV) k
        (fun l => bondOfTorus _ (c l)) X
      have hfun : (fun τ : Fin k → ℝ => densityOfTopFamily L t g n y (perturb c X τ V)) =
          fun τ => g (torusFrame L t n) (siteOfTorus _ y)
            (leftTranslate (bondSpread (fun l => bondOfTorus (F := torusFrame L t n) _ (c l)) X τ)
              (readAtLevel (torusFrame L t n) (torusFrame L t n).top V)) := by
        funext τ
        rw [hG]
        congr 1
        have h1 := restrictToTorus_leftTranslate (hp n)
          (fun l => bondOfTorus (F := torusFrame L t n) _ (c l)) X τ
          (readAtLevel (torusFrame L t n) (torusFrame L t n).top V)
        rw [restrictToTorus_readAtLevel (hp n)] at h1
        simp only [bondToTorus_bondOfTorus (hp n)] at h1
        rw [← h1, readAtLevel_restrictToTorus (hp n)]
      rw [hfun]
      exact h
    · intro n _ hn y γ V hV
      rw [hG, hG, readAtLevel_gaugeTransform (hp n)]
      exact hD.gauge_invariant _ (hT n hn) _ _ _ (isSmallCurvature_readAtLevel (hp n) hV)
    · intro n _ hn y u V hV
      rw [hG, hG, readAtLevel_translate (hp n)]
      have h := hD.translation_invariant _ (hT n hn) (siteOfTorus _ (y + u)) (-siteOfTorus _ u)
        (readAtLevel (torusFrame L t n) (torusFrame L t n).top V)
        (isSmallCurvature_readAtLevel (hp n) hV)
      have hsum : siteOfTorus (F := torusFrame L t n) (torusFrame L t n).top (y + u) +
          -siteOfTorus _ u = siteOfTorus _ y := by
        apply toTorusSite_injective (hp n)
        rw [toTorusSite_add (hp n), toTorusSite_neg (hp n), toTorusSite_siteOfTorus (hp n),
          toTorusSite_siteOfTorus (hp n), toTorusSite_siteOfTorus (hp n)]
        abel
      rw [hsum] at h
      exact h
  · intro e hD n _ hn y V hV k c X h1 h3 hX
    rw [mixedDeriv_eq_bondDeriv (hp n) (hG n y)]
    have h := hD _ (hT n hn) (siteOfTorus _ y)
      (readAtLevel (torusFrame L t n) (torusFrame L t n).top V) k
      (fun l => bondOfTorus _ (c l)) X (isSmallCurvature_readAtLevel (hp n) hV) h1 h3 hX
    rw [bondSpan_eq_supportDiam (hp n)] at h
    simpa only [toTorusSite_siteOfTorus (hp n), bondToTorus_bondOfTorus (hp n)] using h
  · intro e hC n n' _ _ hn hn' y y' V V' m h1 h2 hV hV' hA k h X hk hbox hX
    rw [mixedDeriv_eq_bondDeriv (hp n) (hG n y), mixedDeriv_eq_bondDeriv (hp n') (hG n' y')]
    have hnpos : 0 < n := by omega
    have hnpos' : 0 < n' := by omega
    have hb : ∀ {n : ℕ} (z : TorusSite n),
        (fun l => bondOfTorus (F := torusFrame L t n) (torusFrame L t n).top (bondFrom z (h l))) =
          bondsAt (siteOfTorus _ z) h := by
      intro n z
      funext l
      refine Prod.ext ?_ rfl
      apply toTorusSite_injective (hp n)
      simp only [bondOfTorus, bondFrom, bondsAt]
      rw [toTorusSite_siteOfTorus (hp n), toTorusSite_add (hp n), toTorusSite_siteOfTorus (hp n),
        toTorusSite_siteOfCoords (hp n)]
    rw [hb y, hb y']
    have hagree : AgreeOnBall (finiteCells (torusFrame L t n))
        (readAtLevel (torusFrame L t n) (torusFrame L t n).top V)
        (finiteCells (torusFrame L t n')) (readAtLevel (torusFrame L t n') (torusFrame L t n').top V')
        (siteOfTorus _ y) (siteOfTorus _ y') m := by
      refine ⟨fun _ => Or.inr h1, fun _ => Or.inr h2, fun z _ => ?_, fun b hbb => ?_⟩
      · exact iff_of_true (mem_finiteCells _ (fun _ => hnpos) _)
          (mem_finiteCells _ (fun _ => hnpos') _)
      · have hq := hA b hbb
        have e1 : toTorusSite n (siteOfTorus (F := torusFrame L t n) (torusFrame L t n).top y +
            siteOfCoords _ b.1) = (bondFrom y b).1 := by
          rw [toTorusSite_add (hp n), toTorusSite_siteOfTorus (hp n), toTorusSite_siteOfCoords (hp n)]
          rfl
        have e2 : toTorusSite n' (siteOfTorus (F := torusFrame L t n') (torusFrame L t n').top y' +
            siteOfCoords _ b.1) = (bondFrom y' b).1 := by
          rw [toTorusSite_add (hp n'), toTorusSite_siteOfTorus (hp n'),
            toTorusSite_siteOfCoords (hp n')]
          rfl
        show V (toTorusSite n _) b.2 = V' (toTorusSite n' _) b.2
        rw [e1, e2]
        exact hq
    exact hC _ _ (hT n hn) (hT n' hn') _ _ _ _ m k h X (isSmallCurvature_readAtLevel (hp n) hV)
      (isSmallCurvature_readAtLevel (hp n') hV') hagree hk hbox hX
  · intro n _ y V
    rfl
  · intro n _ b b' X X'
    rw [mixedDeriv_eq_bondDeriv (hp n) (G := g (torusFrame L t n) (siteOfTorus _ 0)) (hG n 0)]
    have h0 : siteOfTorus (F := torusFrame L t n) (torusFrame L t n).top (0 : TorusSite n) = 0 := by
      apply toTorusSite_injective (hp n)
      rw [toTorusSite_siteOfTorus (hp n), toTorusSite_zero (hp n)]
    have hb : (fun l => bondOfTorus (F := torusFrame L t n) (torusFrame L t n).top
        ((![bondFrom 0 b, bondFrom 0 b'] : Fin 2 → TorusBond n) l)) = bondsAt 0 ![b, b'] := by
      funext l
      refine Prod.ext ?_ ?_
      · apply toTorusSite_injective (hp n)
        fin_cases l <;>
          simp [bondOfTorus, bondFrom, bondsAt, toTorusSite_siteOfTorus (hp n),
            toTorusSite_siteOfCoords (hp n)]
      · fin_cases l <;> rfl
    rw [hb, h0]
    rfl
end YangMills.Construction.ColdStepAtMirrorFrames
end
