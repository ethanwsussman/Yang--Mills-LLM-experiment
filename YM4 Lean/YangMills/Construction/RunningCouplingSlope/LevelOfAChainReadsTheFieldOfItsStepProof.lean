import YangMills.Construction.RunningCouplingSlope.LevelOfAChainReadsTheFieldOfItsStep
import YangMills.Construction.SummableBoundsOfTheFlow.LeastActionOfAFrameOnItsTorus
import Mathlib
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped Quaternion
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
open BlockAverages ColdStepAtMirrorFrames TorusFields
namespace StepMinimizerEvaluation
private theorem torusSideBelow_succ (L : ℕ) :
    ∀ s N : ℕ, torusSideBelow L (s + 1) N = torusSideBelow L s N * L := by
  intro s
  induction s with
  | zero => intro N; rfl
  | succ s ih =>
    intro N
    show torusSideBelow L (s + 1) (N * L) = torusSideBelow L s (N * L) * L
    exact ih _
private theorem minimizerBelow_succ (a ρ : ℝ) (L : ℕ) : ∀ (s t N : ℕ) (V : TorusField N),
    HEq (minimizerBelow a ρ L t (s + 1) N V)
      (SlopeCoefficient.minimizerOnFinerTorus a ρ L (t - (s + 1)) (torusSideBelow L s N)
        (minimizerBelow a ρ L t s N V)) := by
  intro s
  induction s with
  | zero => intro t N V; exact HEq.rfl
  | succ s ih =>
    intro t N V
    have h := ih (t - 1) (N * L) (SlopeCoefficient.minimizerOnFinerTorus a ρ L (t - 1) N V)
    have e : t - 1 - (s + 1) = t - (s + 1 + 1) := by omega
    rw [e] at h
    exact h
private theorem apply_eq_of_heq {m m' : ℕ} (h : m = m') {V : TorusField m} {V' : TorusField m'}
    (hV : HEq V V') (c : Fin 4 → ℤ) :
    V (fun i => (c i : ZMod m)) = V' (fun i => (c i : ZMod m')) := by
  subst h
  obtain rfl := eq_of_heq hV
  rfl
private theorem intCast_cast_roundtrip {P m : ℕ} (h : P = m) (x : ZMod P) :
    ((((x.cast : ℤ) : ZMod m)).cast : ℤ) = x.cast := by apply _root_.YangMills.Construction.FrameTorusAction.cast_intCast_cast <;> assumption
end StepMinimizerEvaluation
open StepMinimizerEvaluation in
theorem chainLevelIsStepMinimizer_holds : ChainLevelIsStepMinimizer := by
  intro a ρ L hL k n hn V X hR j hj b
  have hread := (hR j hj.le).2
  have hs : k - j = (k - (j + 1)) + 1 := by omega
  rw [hs] at hread
  have hheq := minimizerBelow_succ a ρ L (k - (j + 1)) k (2 * L ^ n) V
  have ej : k - (k - (j + 1) + 1) = j := by omega
  rw [ej] at hheq
  have hper : ∀ i, (frameAtStep L n k j).period (frameAtStep L n k j).depth i =
      torusSideBelow L (k - (j + 1)) (2 * L ^ n) * L := by
    intro i
    simp [BlockFrame.period, frameAtStep, torusFrame, sideAtStep]
  have hm : torusSideBelow L (k - (j + 1) + 1) (2 * L ^ n) =
      torusSideBelow L (k - (j + 1)) (2 * L ^ n) * L :=
    torusSideBelow_succ L _ _
  obtain ⟨x, μ⟩ := b
  have h₁ := hread (fun i => (siteCoords x i : ZMod _)) μ
  have h₂ : levelVertexOfTorusSite (L := L) (n := n) (k := k) j
      (fun i => ((siteCoords x i : ℤ) : ZMod (torusSideBelow L (k - (j + 1) + 1) (2 * L ^ n)))) =
      PeriodicLattice.offsetSite 0 (siteCoords x) := by
    unfold levelVertexOfTorusSite
    congr 1
    funext i
    exact intCast_cast_roundtrip ((hper i).trans hm.symm) (x i)
  rw [h₂] at h₁
  refine h₁.trans ?_
  congr 2
  rw [congrFun (apply_eq_of_heq hm hheq (siteCoords x)) μ]
  show fieldAboveFrame true a ρ 0 (topFieldAtStep a ρ L n k j V) 0 _ μ = _
  congr 1
  funext i
  exact (congrArg
    (fun c : ℤ => (c : ZMod ((frameAtStep L n k j).period (frameAtStep L n k j).depth i)))
    (intCast_cast_roundtrip (hper i) (x i))).trans (ZMod.intCast_zmod_cast (x i))
end YangMills.Construction.RunningCouplingSlope
end
