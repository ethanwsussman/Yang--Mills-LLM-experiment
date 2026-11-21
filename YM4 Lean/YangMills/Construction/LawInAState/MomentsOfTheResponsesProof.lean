import YangMills.Construction.SixteenPointsOnASmallTorus.SixteenCopiesAtEveryDatumProof
import YangMills.Construction.LawInAState.MomentsOfTheCentredResponsesProof
import YangMills.Construction.LawInAState.MomentsOfTheResponses
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped ENNReal
namespace YangMills.Construction.StateLaws
open TorusLumps TorusFields RenormalizationStepParameters StepReturn ClusterExpansionOfAStep WeightedResponses ResponseInTheExpansion FreeEnergies BoxResponses BoxMarks
open InfiniteLattice (AmbientSpace)
open TorusMetric (euclidNormVec)
open TestFunctions (euclidDistR4 closedBallR4 uniformNorm bestLipschitzConstant IsLipschitzFor)
private lemma abs_sub_le_bestLipschitz {g : AmbientSpace → ℝ} (h : IsLipschitzFor euclidDistR4 g) (x y : AmbientSpace) :
    |g x - g y| ≤ bestLipschitzConstant euclidDistR4 g * euclidDistR4 x y := by apply _root_.YangMills.DeltaSharedProofs.p2429 <;> assumption
private lemma abs_le_of_uniformNorm_eq_one {g : AmbientSpace → ℝ} (h : uniformNorm g = 1) (x : AmbientSpace) : |g x| ≤ 1 := by
  have hb : BddAbove (Set.range fun x => ‖g x‖) := by
    by_contra hn
    have e := Real.iSup_of_not_bddAbove hn
    unfold uniformNorm at h
    rw [e] at h
    exact zero_ne_one h
  have := le_ciSup hb x
  unfold uniformNorm at h
  rw [h] at this
  simpa [Real.norm_eq_abs] using this
theorem responseMoments_holds (h₂ : ResponseInTheExpansion.TwoPointByTotalCovarianceStatement)
    (h₃ : ResponseInTheExpansion.StageStatesMeasurableStatement) (h₄ : WeightedResponses.ResponsesBounded)
    (h₅ : FreeEnergies.fittedResponseIsConditionalMeanStatement) (h₅' : FreeEnergies.flowStatesAreGroundsStatement)
    (h₅'' : FreeEnergies.conditionalProductMeansStatement)
    (h₅''' : ResponseInTheExpansion.ResponseIsConditionalExpectation) (h₆ : WeightedObservables.majorantMomentsStatement)
    (h₇ : translateSitesStatement) (h₈ : separationLevelStatement) (h₉ : couplingAtSeparation_tendsto_statement) :
    responseMomentsStatement := by
  unfold responseMomentsStatement
  refine (translatedResponseMoments_holds h₂ h₃ h₄ h₅ h₅' h₅'' h₅''' h₆ h₇ h₈ h₉).mono ?_
  rintro Tb y Kr Xi vt ⟨C, d₀, hC, hd₀, h⟩
  refine ⟨C, d₀, hC, hd₀, ?_⟩
  intro d hd0 hdd K β al T hCh k x hk hx
  obtain ⟨hprob, hstate, one⟩ := h d hd0 hdd K β al T hCh k x hk hx
  refine ⟨hprob, hstate, ?_⟩
  intro f g hpair v
  have ht := hpair.mem_class
  simp only [TestFunctions.separatedPairsR4, TestFunctions.separatedPairs, Set.mem_setOf_eq] at ht
  obtain ⟨xf, xg, bf, bg, -, -⟩ := ht
  have bound : ∀ (q : AmbientSpace → ℝ) (c : AmbientSpace),
      IsLipschitzFor euclidDistR4 q → tsupport q ⊆ closedBallR4 c d →
      bestLipschitzConstant euclidDistR4 q ≤ uniformNorm q / (vt * d) →
      uniformNorm q = 1 →
      MemLp (centeredBoxResponse T β al K k (translateBy (Tb.stepParameters y).side K k v q)) 64
        (stageLaw T β K k) ∧
      eLpNorm (centeredBoxResponse T β al K k (translateBy (Tb.stepParameters y).side K k v q)) 64
        (stageLaw T β K k) ≤ ENNReal.ofReal (x ^ C) := by
    intro q c hl hb hlc hn
    refine one q c ?_ hb (abs_le_of_uniformNorm_eq_one hn) v
    intro a b
    have h := abs_sub_le_bestLipschitz hl a b
    rw [hn] at hlc
    calc
      |q a - q b| ≤ bestLipschitzConstant euclidDistR4 q * euclidDistR4 a b := h
      _ ≤ (1 / (vt * d)) * euclidNormVec (a - b) :=
        mul_le_mul_of_nonneg_right hlc (Real.sqrt_nonneg _)
      _ = euclidNormVec (a - b) / (vt * d) := by ring
  exact ⟨bound f xf bf.1 bf.2.2.2.1 bf.2.2.2.2.2 hpair.norm_left,
    bound g xg bg.1 bg.2.2.2.1 bg.2.2.2.2.2 hpair.norm_right⟩

end YangMills.Construction.StateLaws
end
