import YangMills.Construction.CellOfTheFlow.TheCellEventReadsItsCellProof
import YangMills.Construction.ClusterExpansionOfAStep.ImageStateIsBorelProof
import YangMills.Construction.ResponseInTheExpansion.CoinsOfAStepAreBorel
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
open MeasureTheory
namespace YangMills.Construction.ResponseInTheExpansion
open TorusFields TorusLumps StepSettings StepCosts StepFrames StateMeasurability RenormalizationStepParameters ColdChain
  BlockAverages ColdStepAtMirrorFrames WeightedResponses
namespace MarkLawMeasurability
variable {S : StepSetup} {n : ℕ} [NeZero n]
private theorem measurable_markProduct {α : Type} [MeasurableSpace α] (hcut : IsCutoff S.ballRadius S.barrierFn)
    (hchart : ChartCoordMeasurable) (C : Finset (TorusSite n)) {U : α → TorusField n} (hU : Measurable U)
    {W : α → TorusField (n * S.params.side)} (hW : Measurable W) (bad : Finset (TorusBond (n * S.params.side)))
    (hframe : ∀ b ∈ markedBonds S C, MeasurableQuaternion fun a =>
      ((frameCoord S.params S.anchorRadius S.depth S.frameReach (U a) b : imaginaryQuaternions) : ℍ[ℝ])) :
    Measurable fun a => markProduct S C (U a) (W a) bad := by apply _root_.YangMills.Construction.CoarseMeasurability.measurable_markProduct <;> assumption
private theorem MeasurableQuaternion.of_continuousOn {s : Set (TorusField n)} {f : TorusField n → ℍ[ℝ]}
    (hf : ContinuousOn f s) {α : Type} [MeasurableSpace α] {U : α → TorusField n} (hU : Measurable U)
    (hs : ∀ a, U a ∈ s) : MeasurableQuaternion fun a => f (U a) := by apply _root_.YangMills.Construction.CoarseMeasurability.measurableQuaternion_of_continuousOn <;> assumption
private theorem coldNearSite_of_not_mem (hadm : S.params.Admissible) (hdvd : S.params.side ∣ n)
    (hreach : S.frameReach ≤ 2 * S.nextRange) {V : TorusField n} {y : TorusSite n}
    (hy : y ∉ hotCoreSites S V) : ColdNearSite S.params.threshold S.frameReach y V := by apply _root_.YangMills.Construction.CoarseMeasurability.coldNearSite_of_not_mem_hotCoreSites <;> assumption
private theorem isCold_of_small_torus (hadm : S.params.Admissible) (hdvd : S.params.side ∣ n)
    (hsmall : n ≤ 4 * S.nextRange) {V : TorusField n} {y : TorusSite n} (hy : y ∉ hotCoreSites S V) :
    IsCold S.params.threshold V := by apply _root_.YangMills.Construction.CoarseMeasurability.isCold_of_not_mem_hotCoreSites_of_small <;> assumption
private theorem measurableSet_hotCoreSites_eq (hadm : S.params.Admissible) (hdvd : S.params.side ∣ n)
    (C : Finset (TorusSite n)) : MeasurableSet {V : TorusField n | hotCoreSites S V = C} := by apply _root_.YangMills.SharedProofs.p8979 <;> assumption
end MarkLawMeasurability
open MarkLawMeasurability in
theorem markLawMeasurable (hchart : ChartCoordMeasurable)
    (hframe : continuousOn_frameCoord_of_cold) : MarkLawMeasurable := by
  classical
  intro T hT y S hparams hadm hball hcut hreach₁₆ hreach₂ n _ hdvd hn bad
  have hcoupling : S.params.coupling = T.coupling := by rw [hparams]; rfl
  have hside : S.params.side = T.side := by rw [hparams]; rfl
  have hthreshold : S.params.threshold = T.threshold := by rw [hparams]; rfl
  have hchain : ColdChainConstants S.params.coupling T.δ₁ S.params.side T.lam S.anchorRadius T.σA T.cg T.N := by
    rw [hcoupling, hside, hball]
    exact hT.chain
  have hσA : S.params.threshold ≤ T.σA := by
    rw [hthreshold]
    linarith [hT.σ_le, hT.σ_pos]
  have hcont : ∀ (C : Finset (TorusSite n)), ∀ b ∈ markedBonds S C,
      ContinuousOn (fun V : TorusField n =>
        ((frameCoord S.params S.anchorRadius S.depth S.frameReach V b : imaginaryQuaternions) : ℍ[ℝ]))
        {V | hotCoreSites S V = C} := by
    intro C b hb
    have hb' := Finset.mem_filter.mp hb
    obtain ⟨hlarge, hsmall⟩ := hframe S.params T.δ₁ T.lam S.anchorRadius T.σA T.cg T.N hadm hchain hσA S.depth
      S.frameReach n hreach₁₆ hn b hb'.1
    by_cases hsize : 4 * S.frameReach + 5 < n
    · refine (hlarge hsize).mono fun V hV => ?_
      have hV' : hotCoreSites S V = C := hV
      exact coldNearSite_of_not_mem hadm hdvd (by omega) (by rw [hV']; exact hb'.2)
    · refine (hsmall hsize).mono fun V hV => ?_
      have hV' : hotCoreSites S V = C := hV
      exact isCold_of_small_torus hadm hdvd (by omega) (y := parentBlock S.params.side b.1) (by rw [hV']; exact hb'.2)
  refine measurable_of_countable_cover (fun C : Finset (TorusSite n) =>
    {p : TorusField (n * S.params.side) × TorusField n | hotCoreSites S p.2 = C})
    (fun C => measurable_snd (measurableSet_hotCoreSites_eq hadm hdvd C))
    (fun p => ⟨_, rfl⟩) fun C => ?_
  have hU : Measurable fun a : {p : TorusField (n * S.params.side) × TorusField n | hotCoreSites S p.2 = C} =>
      a.1.2 :=
    measurable_snd.comp measurable_subtype_coe
  have hW : Measurable fun a : {p : TorusField (n * S.params.side) × TorusField n | hotCoreSites S p.2 = C} =>
      a.1.1 :=
    measurable_fst.comp measurable_subtype_coe
  have hquat : ∀ b ∈ markedBonds S C, MeasurableQuaternion
      fun a : {p : TorusField (n * S.params.side) × TorusField n | hotCoreSites S p.2 = C} =>
        ((frameCoord S.params S.anchorRadius S.depth S.frameReach a.1.2 b : imaginaryQuaternions) : ℍ[ℝ]) :=
    fun b hb => MeasurableQuaternion.of_continuousOn (hcont C b hb) hU fun a => a.2
  have key : (fun a : {p : TorusField (n * S.params.side) × TorusField n | hotCoreSites S p.2 = C} =>
      markLaw S a.1.1 a.1.2 bad) =
      fun a => if bad ⊆ markedBonds S C then markProduct S C a.1.2 a.1.1 bad else 0 := by
    funext a
    have hC : hotCoreSites S a.1.2 = C := a.2
    unfold markLaw
    rw [if_pos ⟨hdvd, hn⟩, hC]
  rw [key]
  by_cases hsub : bad ⊆ markedBonds S C
  · simp only [if_pos hsub]
    exact measurable_markProduct hcut hchart C hU hW bad hquat
  · simp only [if_neg hsub]
    exact measurable_const
end YangMills.Construction.ResponseInTheExpansion
end
