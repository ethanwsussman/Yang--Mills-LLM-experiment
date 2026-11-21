import YangMills.Construction.SummableBoundsOfTheFlow.LeastActionOfAFrameOnItsTorus
import YangMills.Construction.RunningCouplingSlope.DensityOfTheStepOnTwoToriAtParametersProof
import YangMills.Construction.SummableBoundsOfTheFlow.DerivativesOfATopFamilyOnTori
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames TorusFields TorusLumps
namespace Estimates
section Casts
variable {a b : ℕ}
private theorem cast_neg_of_eq (h : a = b) (u : ZMod a) :
    (((-u).cast : ℤ) : ZMod b) = -((u.cast : ℤ) : ZMod b) := by apply _root_.YangMills.Construction.FrameTorusAction.intCast_cast_neg <;> assumption
private theorem cast_cast_of_eq (h : a = b) (u : ZMod b) :
    (((((u.cast : ℤ) : ZMod a)).cast : ℤ) : ZMod b) = u := by apply _root_.YangMills.Construction.FrameTorusAction.intCast_cast_roundTrip <;> assumption
private theorem valMinAbs_cast_of_eq (h : a = b) (u : ZMod a) :
    (((u.cast : ℤ) : ZMod b)).valMinAbs = u.valMinAbs := by apply _root_.YangMills.Construction.TopLevelSites.valMinAbs_intCast_cast <;> assumption
end Casts
section Sites
variable {F : BlockFrame} {m j : ℕ}
private def siteOfTorus (j : ℕ) (x : TorusSite m) : F.Site j := siteOfCoords j fun k => ((x k).cast : ℤ)
private theorem toTorusSite_siteOfTorus (hp : ∀ i, F.period j i = m) (x : TorusSite m) :
    toTorusSite m (siteOfTorus (F := F) j x) = x := by apply _root_.YangMills.Construction.FrameTorusAction.toTorusSite_siteOfTorusSite <;> assumption
private theorem siteOfTorus_toTorusSite (hp : ∀ i, F.period j i = m) (y : F.Site j) :
    siteOfTorus j (toTorusSite m y) = y := by apply _root_.YangMills.Construction.FrameTorusAction.siteOfTorusSite_toTorusSite <;> assumption
private theorem toTorusSite_add (hp : ∀ i, F.period j i = m) (x y : F.Site j) :
    toTorusSite m (x + y) = toTorusSite m x + toTorusSite m y := by apply _root_.YangMills.Construction.FrameTorusAction.toTorusSite_add <;> assumption
private theorem toTorusSite_neg (hp : ∀ i, F.period j i = m) (x : F.Site j) :
    toTorusSite m (-x) = -toTorusSite m x :=
  funext fun k => cast_neg_of_eq (hp k) (x k)
private theorem toTorusSite_sub (hp : ∀ i, F.period j i = m) (x y : F.Site j) :
    toTorusSite m (x - y) = toTorusSite m x - toTorusSite m y := by
  rw [sub_eq_add_neg, toTorusSite_add hp, toTorusSite_neg hp, sub_eq_add_neg]
private theorem siteSupDist_eq (hp : ∀ i, F.period j i = m) (y z : F.Site j) :
    siteSupDist y z = supDist (toTorusSite m y) (toTorusSite m z) := by
  unfold siteSupDist supDist
  refine congrArg (fun g : Fin 4 → ℕ => Finset.univ.sup g) (funext fun i => ?_)
  have h := congrFun (toTorusSite_sub hp y z) i
  simp only [Pi.sub_apply] at h
  rw [← h]
  exact (congrArg Int.natAbs (valMinAbs_cast_of_eq (hp i) ((y - z) i))).symm
abbrev _root_.YangMills.SharedProofs.p2088 := @siteSupDist_eq
private def torusBondOf (m : ℕ) (c : F.Site j × Fin 4) : TorusBond m := (toTorusSite m c.1, c.2)
private theorem bondSpan_eq (hp : ∀ i, F.period j i = m) {k : ℕ} (y : F.Site j)
    (c : Fin k → F.Site j × Fin 4) :
    bondSpan y c = supportDiam (toTorusSite m y) fun l => torusBondOf m (c l) := by
  unfold bondSpan supportDiam
  simp only [siteSupDist_eq hp, torusBondOf]
abbrev _root_.YangMills.DeltaSharedProofs.p501818 := @bondSpan_eq
private theorem bondSpread_eq (hp : ∀ i, F.period j i = m) {k : ℕ} (c : Fin k → F.Site j × Fin 4)
    (X : Fin k → imaginaryQuaternions) (τ : Fin k → ℝ) (x : TorusSite m) (i : Fin 4) :
    bondSpread c X τ (siteOfTorus j x) i = ∑ l, if torusBondOf m (c l) = (x, i) then τ l • X l else 0 := by apply _root_.YangMills.Construction.RunningCouplingSlope.TorusComparison.bondSpread_siteOfTorusSite <;> assumption
private theorem restrictToTorus_leftTranslate (hp : ∀ i, F.period j i = m) {k : ℕ}
    (c : Fin k → F.Site j × Fin 4) (X : Fin k → imaginaryQuaternions) (τ : Fin k → ℝ) (W : F.GaugeField j) :
    restrictToTorus m (leftTranslate (bondSpread c X τ) W) =
      perturb (fun l => torusBondOf m (c l)) X τ (restrictToTorus m W) := by apply _root_.YangMills.Construction.RunningCouplingSlope.TorusComparison.restrictToTorus_leftTranslate <;> assumption
private theorem bondDeriv_eq (hp : ∀ i, F.period j i = m) {G : F.GaugeField j → ℝ} {G' : TorusField m → ℝ}
    (hG : ∀ W, G W = G' (restrictToTorus m W)) {k : ℕ} (W : F.GaugeField j)
    (c : Fin k → F.Site j × Fin 4) (X : Fin k → imaginaryQuaternions) :
    bondDeriv G W c X = mixedDeriv G' (restrictToTorus m W) (fun l => torusBondOf m (c l)) X := by apply _root_.YangMills.Construction.RunningCouplingSlope.TorusComparison.bondDeriv_eq_mixedDeriv <;> assumption
private theorem readAtLevel_restrictToTorus (hp : ∀ i, F.period j i = m) (W : F.GaugeField j) :
    readAtLevel F j (restrictToTorus m W) = W := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.SecondOrderAtConstantCurvature.readAtLevel_restrictToTorus <;> assumption
private theorem restrictToTorus_readAtLevel (hp : ∀ i, F.period j i = m) (V : TorusField m) :
    restrictToTorus m (readAtLevel F j V) = V := by apply _root_.YangMills.Construction.RunningCouplingSlope.TorusComparison.restrictToTorus_readAtLevel <;> assumption
private theorem isSmallCurvature_readAtLevel (hp : ∀ i, F.period j i = m) {s : ℝ} {V : TorusField m}
    (h : IsCold s V) : IsSmallCurvature s (readAtLevel F j V) := by apply _root_.YangMills.Construction.RunningCouplingSlope.TorusComparison.isSmallCurvature_readAtLevel <;> assumption
private def bondOfTorus (j : ℕ) (c : TorusBond m) : F.Site j × Fin 4 := (siteOfTorus j c.1, c.2)
private theorem torusBondOf_bondOfTorus (hp : ∀ i, F.period j i = m) (c : TorusBond m) :
    torusBondOf (F := F) (j := j) m (bondOfTorus j c) = c := by apply _root_.YangMills.Construction.RunningCouplingSlope.TorusComparison.torusBondOfBond_bondOfTorusBond <;> assumption
private theorem mixedDeriv_eq (hp : ∀ i, F.period j i = m) {G : F.GaugeField j → ℝ} {G' : TorusField m → ℝ}
    (hG : ∀ V, G' V = G (readAtLevel F j V)) {k : ℕ} (V : TorusField m) (c : Fin k → TorusBond m)
    (X : Fin k → imaginaryQuaternions) :
    mixedDeriv G' V c X = bondDeriv G (readAtLevel F j V) (fun l => bondOfTorus j (c l)) X := by apply _root_.YangMills.Construction.RunningCouplingSlope.TorusComparison.mixedDeriv_eq_bondDeriv <;> assumption
end Sites
private theorem torusFrame_period (L t n : ℕ) (i : Fin 4) :
    (torusFrame L t n).period (torusFrame L t n).top i = n := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.SecondOrderAtConstantCurvature.torusFrame_period_top <;> assumption
theorem topFamilyDerivBoundsOnTori_holds : TopFamilyDerivBoundsOnTori := by
  intro L t n₀ K s g e hD n _ hn y V hV k c X h1 h3 hX
  have hT : IsCubicTopTorus L t n₀ (torusFrame L t n) := ⟨rfl, rfl, n, fun _ => rfl, hn⟩
  have hp : ∀ i, (torusFrame L t n).period (torusFrame L t n).top i = n := torusFrame_period L t n
  have hG : ∀ (V : TorusField n), densityOfTopFamily L t g n y V =
      g (torusFrame L t n) (siteOfTorus _ y) (readAtLevel (torusFrame L t n) (torusFrame L t n).top V) :=
    fun _ => rfl
  rw [mixedDeriv_eq hp hG]
  have h := hD _ hT (siteOfTorus _ y) (readAtLevel (torusFrame L t n) (torusFrame L t n).top V) k
    (fun l => bondOfTorus _ (c l)) X (isSmallCurvature_readAtLevel hp hV) h1 h3 hX
  rw [bondSpan_eq hp] at h
  simpa only [toTorusSite_siteOfTorus hp, torusBondOf_bondOfTorus hp] using h
end Estimates
end YangMills.Construction
end
