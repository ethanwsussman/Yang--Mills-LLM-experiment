import YangMills.Construction.ClusterExpansionOfAStep.TopFamiliesOnTori
import YangMills.Construction.RunningCouplingSlope.HessianOfAStepIsPositiveProof
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.TopFamilyEvaluations
open BlockAverages hiding bondSpread IsCold
open ColdStepAtMirrorFrames TopLevelSites TorusFields TorusLumps StepCosts
variable {L t n : ℕ}
theorem period_torusFrame_top (i : Fin 4) :
    (torusFrame L t n).period (torusFrame L t n).top i = n := period_top i
def frameBonds {k : ℕ} (L t : ℕ) (c : Fin k → TorusBond n) :
    Fin k → (torusFrame L t n).Site (torusFrame L t n).top × Fin 4 :=
  fun l => (torusSiteInFrame (torusFrame L t n) (torusFrame L t n).top (c l).1, (c l).2)
theorem readAtLevel_perturb [NeZero n] {k : ℕ} (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions)
    (σ : Fin k → ℝ) (V : TorusField n) :
    readAtLevel (torusFrame L t n) (torusFrame L t n).top (perturb c X σ V) =
      leftTranslate (bondSpread (frameBonds L t c) X σ) (readAtLevel (torusFrame L t n) (torusFrame L t n).top V) := by
  funext x i
  have e : (∑ l, if c l = (toTorusSite n x, i) then σ l • X l else 0) =
      bondSpread (frameBonds L t c) X σ x i := by
    unfold bondSpread
    refine Finset.sum_congr rfl fun l _ => ?_
    have : c l = (toTorusSite n x, i) ↔ frameBonds L t c l = (x, i) := by
      constructor
      · intro h
        simp only [frameBonds, h, torusSiteInFrame_toTorusSite period_torusFrame_top]
      · intro h
        have h1 := congrArg Prod.fst h
        have h2 := congrArg Prod.snd h
        simp only [frameBonds] at h1 h2
        refine Prod.ext ?_ h2
        rw [← h1, toTorusSite_torusSiteInFrame period_torusFrame_top]
    simp only [this]
  show expUnit (∑ l, if c l = (toTorusSite n x, i) then σ l • X l else 0) * V (toTorusSite n x) i = _
  rw [e]
  rfl
theorem densityOfTopFamily_eq (g : TopLevelFamily) (y : TorusSite n) :
    densityOfTopFamily L t g n y = fun V => g (torusFrame L t n)
      (torusSiteInFrame (torusFrame L t n) (torusFrame L t n).top y)
      (readAtLevel (torusFrame L t n) (torusFrame L t n).top V) := rfl
theorem mixedDeriv_readAtLevel [NeZero n]
    (G : (torusFrame L t n).GaugeField (torusFrame L t n).top → ℝ) {k : ℕ}
    (V : TorusField n) (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions) :
    mixedDeriv (fun W => G (readAtLevel (torusFrame L t n) (torusFrame L t n).top W)) V c X =
      bondDeriv G (readAtLevel (torusFrame L t n) (torusFrame L t n).top V) (frameBonds L t c) X := by
  unfold mixedDeriv bondDeriv
  have e : (fun σ : Fin k → ℝ => G (readAtLevel (torusFrame L t n) (torusFrame L t n).top (perturb c X σ V))) =
      fun σ => G (leftTranslate (bondSpread (frameBonds L t c) X σ)
        (readAtLevel (torusFrame L t n) (torusFrame L t n).top V)) := by
    funext σ
    rw [readAtLevel_perturb]
  rw [e]
theorem natAbs_valMinAbs_cast_sub {m : ℕ} [NeZero n] (h : m = n) (u v : ZMod n) :
    (((((u.cast : ℤ) : ZMod m) - ((v.cast : ℤ) : ZMod m))).valMinAbs).natAbs =
      ((u - v).valMinAbs).natAbs := by
  subst h
  simp
theorem siteSupDist_torusSiteInFrame [NeZero n] (y z : TorusSite n) :
    siteSupDist (F := torusFrame L t n) (j := (torusFrame L t n).top)
      (torusSiteInFrame (torusFrame L t n) (torusFrame L t n).top y)
      (torusSiteInFrame (torusFrame L t n) (torusFrame L t n).top z) = supDist y z := by
  unfold siteSupDist supDist
  refine Finset.sup_congr rfl fun i _ => ?_
  exact natAbs_valMinAbs_cast_sub (period_torusFrame_top i) (y i) (z i)
theorem bondSpan_frameBonds [NeZero n] {k : ℕ} (y : TorusSite n) (c : Fin k → TorusBond n) :
    bondSpan (torusSiteInFrame (torusFrame L t n) (torusFrame L t n).top y) (frameBonds L t c) =
      supportDiam y c := by
  unfold bondSpan supportDiam
  simp only [frameBonds, siteSupDist_torusSiteInFrame]
theorem isSmallCurvature_readAtLevel [NeZero n] {s : ℝ} {V : TorusField n} (hV : IsCold s V) :
    IsSmallCurvature (F := torusFrame L t n) s (readAtLevel (torusFrame L t n) (torusFrame L t n).top V) := by apply _root_.YangMills.SharedProofs.p2155 <;> assumption
theorem isCold_mono {s s' : ℝ} {V : TorusField n} (hs : s ≤ s') (hV : IsCold s V) : IsCold s' V :=
  fun x μ ν h => lt_of_lt_of_le (hV x μ ν h) hs
theorem isCubicTopTorus_torusFrame [NeZero n] {n₀ : ℕ} (hn : n₀ ≤ n) :
    IsCubicTopTorus L t n₀ (torusFrame L t n) :=
  ⟨rfl, rfl, n, fun _ => rfl, hn⟩
theorem isCold_translate [NeZero n] {s : ℝ} {W : TorusField n} (hW : IsCold s W) (u : TorusSite n) :
    IsCold s (TorusFields.translate u W) := by
  intro x μ ν h
  have e : curvature (TorusFields.translate u W) x μ ν = curvature W (x + u) μ ν := by
    simp only [curvature, holonomy, TorusFields.translate, add_right_comm]
  rw [e]
  exact hW _ μ ν h
theorem mem_finiteCells_torusFrame [NeZero n] (z : (torusFrame L t n).Cell) :
    z ∈ finiteCells (torusFrame L t n) :=
  mem_finiteCells (fun _ => Nat.pos_of_ne_zero (NeZero.ne n)) z
theorem agreeOnBall_readAtLevel {n' : ℕ} [NeZero n] [NeZero n'] {W : TorusField n} {W' : TorusField n'}
    {y : TorusSite n} {y' : TorusSite n'}
    {m : ℕ} (h1 : 2 * m + 2 < n) (h2 : 2 * m + 2 < n') (hA : FieldsAgreeNear W W' y y' m) :
    AgreeOnBall (finiteCells (torusFrame L t n)) (readAtLevel (torusFrame L t n) (torusFrame L t n).top W)
      (finiteCells (torusFrame L t n')) (readAtLevel (torusFrame L t n') (torusFrame L t n').top W')
      (torusSiteInFrame (torusFrame L t n) (torusFrame L t n).top y)
      (torusSiteInFrame (torusFrame L t n') (torusFrame L t n').top y') m := by
  refine ⟨fun _ => Or.inr h1, fun _ => Or.inr h2,
    fun _ _ => ⟨fun _ => mem_finiteCells_torusFrame _, fun _ => mem_finiteCells_torusFrame _⟩, fun c hc => ?_⟩
  have := hA c hc
  show W (toTorusSite n _) c.2 = W' (toTorusSite n' _) c.2
  rw [toTorusSite_add period_torusFrame_top, toTorusSite_add period_torusFrame_top,
    toTorusSite_torusSiteInFrame period_torusFrame_top, toTorusSite_torusSiteInFrame period_torusFrame_top,
    toTorusSite_siteOfCoords period_torusFrame_top, toTorusSite_siteOfCoords period_torusFrame_top]
  exact this
theorem frameBonds_bondFrom [NeZero n] {k : ℕ} (v : TorusSite n) (b : Fin k → (Fin 4 → ℤ) × Fin 4) :
    (frameBonds L t fun l => bondFrom v (b l)) =
      bondsAt (torusSiteInFrame (torusFrame L t n) (torusFrame L t n).top v) b := by
  funext l
  refine Prod.ext ?_ rfl
  show torusSiteInFrame (torusFrame L t n) (torusFrame L t n).top (v + siteOfInt (b l).1) =
    _ + siteOfCoords _ (b l).1
  rw [torusSiteInFrame_add period_torusFrame_top, torusSiteInFrame_siteOfInt period_torusFrame_top]
theorem topFamilyOnTori_holds : TopFamilyOnTori := by
  intro ℓ hF t s g hs
  have hn₀ := hF.n₀_ge
  have compare : ∀ (G : TopLevelFamily) (e : ℕ → ℝ), IsLocalOnTori ℓ.side t ℓ.n₀ s G e →
      LocalComparison ℓ (densityOfTopFamily ℓ.side t G) e := by
    intro G e hc n n' _ _ hn hn' y y' W W' m h1 h2 hW hW' hA k b X hk hb hX
    have := hc (torusFrame ℓ.side t n) (torusFrame ℓ.side t n')
      (isCubicTopTorus_torusFrame hn) (isCubicTopTorus_torusFrame hn')
      (torusSiteInFrame _ _ y) (torusSiteInFrame _ _ y') (readAtLevel _ _ W) (readAtLevel _ _ W') m k b X
      (isSmallCurvature_readAtLevel (isCold_mono hs hW)) (isSmallCurvature_readAtLevel (isCold_mono hs hW'))
      (agreeOnBall_readAtLevel h1 h2 hA) hk hb hX
    rw [densityOfTopFamily_eq, densityOfTopFamily_eq, mixedDeriv_readAtLevel, mixedDeriv_readAtLevel,
      frameBonds_bondFrom, frameBonds_bondFrom]
    exact this
  refine ⟨fun hd => ⟨?_, ?_, ?_⟩, fun e hd => ?_, compare g, fun e hc => ?_, fun b b' X X' n hn => ?_⟩
  · intro n _ hn y W hW k c X
    have h1 := hd.smooth (torusFrame ℓ.side t n) (isCubicTopTorus_torusFrame hn) (torusSiteInFrame _ _ y)
      (readAtLevel _ _ W) (isSmallCurvature_readAtLevel (isCold_mono hs hW)) k (frameBonds ℓ.side t c) X
    have e : (fun σ : Fin k → ℝ => densityOfTopFamily ℓ.side t g n y (perturb c X σ W)) =
        fun σ => g (torusFrame ℓ.side t n) (torusSiteInFrame _ _ y)
          (leftTranslate (bondSpread (frameBonds ℓ.side t c) X σ)
            (readAtLevel (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).top W)) := by
      funext σ
      rw [densityOfTopFamily_eq]
      beta_reduce
      rw [readAtLevel_perturb]
    show ContDiffAt ℝ 3 (fun σ : Fin k → ℝ => densityOfTopFamily ℓ.side t g n y (perturb c X σ W)) 0
    rw [e]
    exact h1
  · intro n _ hn y γ W hW
    have e : readAtLevel (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).top (TorusFields.gaugeTransform γ W) =
        BlockAverages.gaugeTransform (fun x => γ (toTorusSite n x))
          (readAtLevel (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).top W) := by
      funext x i
      show γ (toTorusSite n x) * W (toTorusSite n x) i * (γ (toTorusSite n x + TorusFields.unitStep n i))⁻¹ =
        γ (toTorusSite n x) * W (toTorusSite n x) i *
          (γ (toTorusSite n (x + BlockAverages.unitStep (torusFrame ℓ.side t n).top i)))⁻¹
      rw [toTorusSite_add period_torusFrame_top, toTorusSite_unitStep period_torusFrame_top]
    rw [densityOfTopFamily_eq]
    beta_reduce
    rw [e]
    exact hd.gauge_invariant _ (isCubicTopTorus_torusFrame hn) _ _ _ (isSmallCurvature_readAtLevel (isCold_mono hs hW))
  · intro n _ hn y u W hW
    have h1 := hd.translation_invariant (torusFrame ℓ.side t n) (isCubicTopTorus_torusFrame hn)
      (torusSiteInFrame _ _ y) (torusSiteInFrame _ _ u)
      (readAtLevel _ _ (TorusFields.translate u W)) (isSmallCurvature_readAtLevel (isCold_mono hs (isCold_translate hW u)))
    have e : translateField (torusSiteInFrame (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).top u)
        (readAtLevel (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).top (TorusFields.translate u W)) =
        readAtLevel (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).top W := by
      funext x i
      show W (toTorusSite n (x - torusSiteInFrame (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).top u) + u) i =
        W (toTorusSite n x) i
      rw [sub_eq_add_neg, toTorusSite_add period_torusFrame_top, toTorusSite_neg period_torusFrame_top,
        toTorusSite_torusSiteInFrame period_torusFrame_top]
      simp
    rw [e] at h1
    rw [densityOfTopFamily_eq, densityOfTopFamily_eq]
    beta_reduce
    rw [torusSiteInFrame_add period_torusFrame_top]
    exact h1.symm
  · intro n _ hn y W hW k c X hk1 hk3 hX
    have h1 := hd (torusFrame ℓ.side t n) (isCubicTopTorus_torusFrame hn) (torusSiteInFrame _ _ y)
      (readAtLevel _ _ W) k (frameBonds ℓ.side t c) X
      (isSmallCurvature_readAtLevel (isCold_mono hs hW)) hk1 hk3 hX
    rw [bondSpan_frameBonds] at h1
    rw [densityOfTopFamily_eq, mixedDeriv_readAtLevel]
    exact h1
  · have e0 : centeredFamily (densityOfTopFamily ℓ.side t g) = densityOfTopFamily ℓ.side t (centredFamily g) := by
      funext n y V
      rfl
    rw [e0]
    exact compare _ e hc
  · have : NeZero n := ⟨by omega⟩
    have e1 : torusSiteInFrame (torusFrame ℓ.side t n) (torusFrame ℓ.side t n).top (0 : TorusSite n) = 0 := by
      apply toTorusSite_injective period_torusFrame_top
      rw [toTorusSite_torusSiteInFrame period_torusFrame_top]
      funext k
      simp [toTorusSite, siteCoords]
    have e2 : (![bondFrom 0 b, bondFrom 0 b'] : Fin 2 → TorusBond n) =
        fun l => bondFrom (0 : TorusSite n) ((![b, b'] : Fin 2 → LatticeBond) l) := by
      funext l
      fin_cases l <;> rfl
    rw [densityOfTopFamily_eq, mixedDeriv_readAtLevel, e2, frameBonds_bondFrom, e1]
    unfold secondDerivAtUniform
    rfl
end YangMills.Construction.TopFamilyEvaluations
end
