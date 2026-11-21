import YangMills.Construction.ClusterExpansionOfAStep.AdmissionEqualInBoxes
import YangMills.Construction.SummableBoundsOfTheFlow.LeastActionOfAFrameOnItsTorus
import YangMills.Construction.ClusterExpansionOfAStep.SharesAndCostsOfAStep
import YangMills.Construction.ColdStepAtMirrorFrames.SecondOrderOfADensityAtConstantCurvatureProof
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames TorusFields TorusLumps StepCosts
namespace TorusLevels
section Casts
variable {a b : ℕ}
theorem intCast_cast_cast_of_eq (h : a = b) (u : ZMod b) :
    (((((u.cast : ℤ) : ZMod a)).cast : ℤ) : ZMod b) = u := by apply _root_.YangMills.Construction.FrameTorusAction.intCast_cast_roundTrip <;> assumption
end Casts
section Sites
variable {F F' : BlockFrame} {m j j' : ℕ}
theorem toTorusSite_torusSiteInFrame (hp : ∀ i, F.period j i = m) (x : TorusSite m) :
    toTorusSite m (torusSiteInFrame F j x) = x := by apply _root_.YangMills.Construction.FrameTorusAction.toTorusSite_siteOfTorusSite <;> assumption
theorem torusSiteInFrame_toTorusSite (hp : ∀ i, F.period j i = m) (y : F.Site j) :
    torusSiteInFrame F j (toTorusSite m y) = y := by apply _root_.YangMills.Construction.FrameTorusAction.siteOfTorusSite_toTorusSite <;> assumption
def bondInFrame (F : BlockFrame) (j : ℕ) (c : TorusBond m) : F.Site j × Fin 4 :=
  (torusSiteInFrame F j c.1, c.2)
theorem bondSpread_bondInFrame (hp : ∀ i, F.period j i = m) {k : ℕ} (c : Fin k → TorusBond m)
    (X : Fin k → imaginaryQuaternions) (τ : Fin k → ℝ) (y : F.Site j) (i : Fin 4) :
    bondSpread (fun l => bondInFrame F j (c l)) X τ y i =
      ∑ l, if c l = (toTorusSite m y, i) then τ l • X l else 0 := by
  unfold ColdStepAtMirrorFrames.bondSpread
  refine Finset.sum_congr rfl fun l _ => ?_
  have hiff : bondInFrame F j (c l) = (y, i) ↔ c l = (toTorusSite m y, i) := by
    constructor
    · intro h
      have h1 : torusSiteInFrame F j (c l).1 = y := congrArg Prod.fst h
      have h2 : (c l).2 = i := congrArg Prod.snd h
      refine Prod.ext ?_ h2
      rw [← h1, toTorusSite_torusSiteInFrame hp]
    · intro h
      have h1 : (c l).1 = toTorusSite m y := congrArg Prod.fst h
      have h2 : (c l).2 = i := congrArg Prod.snd h
      refine Prod.ext ?_ h2
      show torusSiteInFrame F j (c l).1 = y
      rw [h1, torusSiteInFrame_toTorusSite hp]
  simp only [hiff]
theorem readAtLevel_perturb (hp : ∀ i, F.period j i = m) {k : ℕ} (c : Fin k → TorusBond m)
    (X : Fin k → imaginaryQuaternions) (τ : Fin k → ℝ) (V : TorusField m) :
    readAtLevel F j (perturb c X τ V) =
      leftTranslate (bondSpread (fun l => bondInFrame F j (c l)) X τ) (readAtLevel F j V) := by
  funext y i
  show expUnit _ * V _ i = expUnit _ * V _ i
  rw [bondSpread_bondInFrame hp]
  rfl
end Sites
theorem torusFrame_period_depth (L t n : ℕ) (i : Fin 4) :
    (torusFrame L t n).period (torusFrame L t n).depth i = n * L := by apply _root_.YangMills.Construction.CongruentAdmission.torusFrame_period_depth <;> assumption
theorem torusFrame_period_top (L t n : ℕ) (i : Fin 4) :
    (torusFrame L t n).period (torusFrame L t n).top i = n := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.SecondOrderAtConstantCurvature.torusFrame_period_top <;> assumption
end TorusLevels
end YangMills.Construction
end
