import YangMills.Construction.ClusterExpansionOfAStep.AdmissionAtAStepProof
import YangMills.Construction.ClusterExpansionOfAStep.AdmissionIsAProduct
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
open MeasureTheory Set
namespace YangMills.Construction.ClusterExpansionOfAStep
open TorusFields TorusLumps StepSettings StepCosts BlockPlaces TorusBalls LumpContours
variable {R : StepSetup} {n : ℕ} [NeZero n]
theorem frameHotLumpSites_eq_hotLumpsOn (ℓ : StepParameters) (S : Finset (TorusSite (n * ℓ.side)))
    (W : TorusField (n * ℓ.side)) : frameHotLumpSites ℓ S W = hotLumpsOn ℓ S W := by apply _root_.YangMills.Construction.CongruentAdmission.frameHotLumpSites_eq_hotLumpsOn <;> assumption
theorem curvature_congr {m : ℕ} {W W' : TorusField m} {x : TorusSite m} {μ ν : Fin 4}
    (h1 : W x μ = W' x μ) (h2 : W (x + unitStep m μ) ν = W' (x + unitStep m μ) ν)
    (h3 : W (x + unitStep m ν) μ = W' (x + unitStep m ν) μ)
    (h4 : W x ν = W' x ν) : curvature W x μ ν = curvature W' x μ ν := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.ComponentAdmission.curvature_congr <;> assumption
theorem fieldWithStoredLinks_restrict (q : CoarseState R n) (X : Finset (TorusSite n))
    (W : TorusField (n * R.params.side)) (x : TorusSite (n * R.params.side)) (i : Fin 4)
    (hx : parentBlock R.params.side x ∈ X) :
    (q.restrict X).fieldWithStoredLinks W x i = q.fieldWithStoredLinks W x i := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.ComponentAdmission.fieldWithStoredLinks_restrict <;> assumption
section Forward
variable (hR : R.IsWellPosed) (hLn : R.params.side ∣ n) (V : TorusField n)
  (W : TorusField (n * R.params.side)) (Yt : Finset (TorusSite (n * R.params.side)))
  (ωt : Yt → R.labels.Ω) (bad : Finset (TorusBond (n * R.params.side)))
  (b : BaseChoice R.params.side n)
include hR
theorem supDist_parentBlock_le_nextRange {u v : TorusSite (n * R.params.side)}
    (h : supDist u v ≤ 10 * R.range) :
    supDist (parentBlock R.params.side u) (parentBlock R.params.side v) ≤ R.nextRange := by
  have h1 := supDist_parentBlock_le_div_add_one R.params.side u v
  have hL := hR.admissible.L_ge
  have h2 : supDist u v / R.params.side ≤ supDist u v / 16 :=
    Nat.div_le_div_left (by omega) (by norm_num)
  have h3 := hR.range_le
  have h4 := hR.nextRange_ge
  omega
theorem side_le_six_mul_range : R.params.side ≤ 6 * R.range := by
  have := hR.range_ge_side
  omega
include hLn in
theorem restrict_coarseStateOf_isAdmissibleState
    (hbad : bad ⊆ markedBonds R (hotCoreSites R V)) (hW : IsHullState R.params R.range W Yt)
    {X : Finset (TorusSite n)}
    (hX : X ∈ chainComponents R.nextRange
      (coarseHull R.params.side R.range R.nextRange bad Yt (hotCoreSites R V))) :
    ((coarseStateOf R (hotCoreSites R V) W Yt ωt bad b).restrict X).IsAdmissibleCoarseState
      (hotNeighbourhoodOn R X V) X := by
  exact ComponentAdmission.restrict_coarseStateOf_isAdmissibleState
    ⟨hR.hasExpansions, hR.admissible, hR.range_le, hR.nextRange_ge, hR.range_ge_side⟩
    hLn V W Yt ωt bad b hbad hW hX
end Forward
section Backward
variable (hR : R.IsWellPosed) (hLn : R.params.side ∣ n) (V : TorusField n)
  (W : TorusField (n * R.params.side)) (Yt : Finset (TorusSite (n * R.params.side)))
  (ωt : Yt → R.labels.Ω) (bad : Finset (TorusBond (n * R.params.side)))
  (b : BaseChoice R.params.side n)
include hR hLn
theorem coarseStateOf_eq_of_isAdmissibleState (q : CoarseState R n)
    (hq : IsHullState R.params R.nextRange V q.1)
    (hadm : ∀ X ∈ chainComponents R.nextRange q.1,
      (q.restrict X).IsAdmissibleCoarseState (hotNeighbourhoodOn R X V) X)
    (hc : q.IsExtension (hotCoreSites R V) W Yt ωt bad b) :
    coarseStateOf R (hotCoreSites R V) W Yt ωt bad b = q := by
  exact ComponentAdmission.coarseStateOf_eq_of_isAdmissibleState
    ⟨hR.hasExpansions, hR.admissible, hR.range_le, hR.nextRange_ge, hR.range_ge_side⟩
    hLn V W Yt ωt bad b q hq hadm hc
end Backward
theorem admissionIsProduct_holds : AdmissionIsProduct := by
  intro R hR n _ hside V q hq W Yt ωt bad b hbad hW
  constructor
  · intro h
    subst h
    exact ⟨fun X hX => restrict_coarseStateOf_isAdmissibleState hR hside.1 V W Yt ωt bad b hbad hW hX,
      coarseStateOf_isExtension _ _ _ _ _ _ (side_le_six_mul_range hR)⟩
  · rintro ⟨h1, h2⟩
    exact coarseStateOf_eq_of_isAdmissibleState hR hside.1 V W Yt ωt bad b q hq h1 h2
end YangMills.Construction.ClusterExpansionOfAStep
end
