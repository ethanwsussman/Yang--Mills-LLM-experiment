import YangMills.Construction.FreeEnergiesOfTheFlow.CasesOfAGroundHaveMass
import YangMills.Construction.FreeEnergiesOfTheFlow.FunctionsOfTheLabelsAreIntegrable
import YangMills.Construction.FreeEnergiesOfTheFlow.MeanOfTheVariableOfAStep
import YangMills.Construction.FreeEnergiesOfTheFlow.MeanScoresOverAStep
import YangMills.Construction.FreeEnergiesOfTheFlow.MeansOverTheCases
import YangMills.Construction.ResponseInTheExpansion.ImageResponseIsAMeanOfTheGas
import YangMills.Construction.ResponseInTheExpansion.ManyLevelsOfSeveralSupportsProof
import YangMills.Construction.ResponseInTheExpansion.MeansOfAWeight
import YangMills.Construction.ResponseInTheExpansion.StoredScoresOfAGround
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
namespace YangMills.Construction.FreeEnergies
open BlockAverages ColdStepAtMirrorFrames WeightedResponses ResponseInTheExpansion StepSettings StepGas TorusLumps
  TorusFields RenormalizationStepParameters StepCosts FreeEnergiesOfTheFlow LumpContours
section Weights
variable {L : ℕ} [NeZero L]
private theorem mem_weightSupportSites_iff {t n : ℕ} [NeZero n] {w : PlaquetteWeight (fineSide L t n)} {y : TorusSite n} :
    y ∈ weightSupportSites L t n w ↔ ∃ p, IsPlaquetteAt L t y p ∧ w p ≠ 0 := by
  simp [weightSupportSites]
private theorem mem_sitesInBlocks_iff {n : ℕ} [NeZero n] {S : Finset (TorusSite n)} {x : TorusSite (n * L)} :
    x ∈ sitesInBlocks L S ↔ parentBlock L x ∈ S := by
  simp [sitesInBlocks]
abbrev _root_.YangMills.SharedProofs.p74636 := @mem_sitesInBlocks_iff
private theorem image_parentBlock_weightSupportSites (t n : ℕ) [NeZero n] (w : PlaquetteWeight (fineSide L (t + 1) n)) :
    (open Classical in (weightSupportSites L t (n * L) w).image (parentBlock L)) = weightSupportSites L (t + 1) n w := by apply _root_.YangMills.SharedProofs.p19152 <;> assumption
private theorem abs_le_weightSup {m : ℕ} [NeZero m] (w : PlaquetteWeight m) (p : OrientedPlaquette m) : |w p.1| ≤ weightSup w :=
  le_ciSup (f := fun p : OrientedPlaquette m => |w p.1|) (Set.finite_range _).bddAbove p
private theorem abs_blockMean_le (hM : BlockMeanIsLinearAndLocal) (hodd : Odd L) :
    ∀ (t n : ℕ) [NeZero n] (y : TorusSite n) (w : PlaquetteWeight (fineSide L t n)) (B : ℝ),
      (∀ p : OrientedPlaquette (fineSide L t n), |w p.1| ≤ B) → |blockMean L t n y w| ≤ B := by
  intro t
  induction t with
  | zero =>
    intro n _ y w B hB
    have hone := (hM L hodd 0 n y).1
    have e1 : (1 / 24 : ℝ) * ∑ p ∈ plaquettesIn Finset.univ, vertexMultiplicity y p * 1 = 1 := hone
    show |(1 / 24 : ℝ) * ∑ p ∈ plaquettesIn Finset.univ, vertexMultiplicity y p * w p| ≤ B
    have hc : ∀ p : TorusPlaquette n, 0 ≤ vertexMultiplicity y p := fun p => Nat.cast_nonneg _
    calc |(1 / 24 : ℝ) * ∑ p ∈ plaquettesIn Finset.univ, vertexMultiplicity y p * w p|
        = (1 / 24 : ℝ) * |∑ p ∈ plaquettesIn Finset.univ, vertexMultiplicity y p * w p| := by
          rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 24)]
      _ ≤ (1 / 24 : ℝ) * ∑ p ∈ plaquettesIn Finset.univ, vertexMultiplicity y p * B := by
          refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
          refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun p hp => ?_)
          rw [abs_mul, abs_of_nonneg (hc p)]
          have hord : p.2.1 < p.2.2 := by
            simp only [plaquettesIn, Finset.mem_filter] at hp
            exact hp.2.1
          exact mul_le_mul_of_nonneg_left (hB ⟨p, hord⟩) (hc p)
      _ = B * ((1 / 24 : ℝ) * ∑ p ∈ plaquettesIn Finset.univ, vertexMultiplicity y p * 1) := by
          rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun p _ => ?_
          ring
      _ = B := by rw [e1, mul_one]
  | succ t ih =>
    intro n _ Y w B hB
    have hone := (hM L hodd (t + 1) n Y).1
    have e1 : ((L : ℝ) ^ 4)⁻¹ * ∑ y ∈ sitesInBlocks L {Y}, blockMean L t (n * L) y (constOneWeight _) = 1 := hone
    have e2 : ∀ y : TorusSite (n * L), blockMean L t (n * L) y (constOneWeight _) = 1 := fun y => (hM L hodd t (n * L) y).1
    simp only [e2] at e1
    show |((L : ℝ) ^ 4)⁻¹ * ∑ y ∈ sitesInBlocks L {Y}, blockMean L t (n * L) y w| ≤ B
    have hL : (0 : ℝ) ≤ ((L : ℝ) ^ 4)⁻¹ := by positivity
    calc |((L : ℝ) ^ 4)⁻¹ * ∑ y ∈ sitesInBlocks L {Y}, blockMean L t (n * L) y w|
        = ((L : ℝ) ^ 4)⁻¹ * |∑ y ∈ sitesInBlocks L {Y}, blockMean L t (n * L) y w| := by
          rw [abs_mul, abs_of_nonneg hL]
      _ ≤ ((L : ℝ) ^ 4)⁻¹ * ∑ y ∈ sitesInBlocks L {Y}, B := by
          refine mul_le_mul_of_nonneg_left ?_ hL
          exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun y _ => ih (n * L) y w B hB)
      _ = B * (((L : ℝ) ^ 4)⁻¹ * ∑ y ∈ sitesInBlocks L {Y}, (1 : ℝ)) := by
          rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun p _ => ?_
          ring
      _ = B := by rw [e1, mul_one]
end Weights
section Cutoff
private theorem cutoff_nonneg {ρ : ℝ} {p : ℝ → ℝ} (h : IsCutoff ρ p) {u : ℝ} (hu : 0 ≤ u) (hρ : u < ρ) : 0 ≤ p u := by
  have hρ0 : 0 < ρ := lt_of_le_of_lt hu hρ
  by_cases hc : u ≤ 5 * ρ / 8
  · exact (h.vanish_small u hu hc).ge
  · rw [not_le] at hc
    have hu0 : 0 < u := lt_trans (by positivity) hc
    have hb : 0 < 5 * ρ / 8 / u := by positivity
    have hb1 : 5 * ρ / 8 / u ≤ 1 := by
      rw [div_le_one hu0]
      exact hc.le
    have h2 := h.convex.2
    have key := @h2 0 (Set.mem_Ico.2 ⟨le_rfl, hρ0⟩) u (Set.mem_Ico.2 ⟨hu, hρ⟩)
      (1 - 5 * ρ / 8 / u) (5 * ρ / 8 / u) (by linarith) hb.le (by ring)
    have e : (1 - 5 * ρ / 8 / u) • (0 : ℝ) + (5 * ρ / 8 / u) • u = 5 * ρ / 8 := by
      simp only [smul_eq_mul, mul_zero, zero_add]
      field_simp
    rw [e, h.vanish_small _ (by positivity) le_rfl, h.vanish_small 0 le_rfl (by positivity)] at key
    simp only [smul_eq_mul, mul_zero, zero_add] at key
    exact nonneg_of_mul_nonneg_right key hb
private theorem cutoffFactor_nonneg_and_le_one {ρ : ℝ} {p : ℝ → ℝ} (h : IsCutoff ρ p) {u : ℝ} (hu : 0 ≤ u) :
    0 ≤ cutoffFactor ρ p u ∧ cutoffFactor ρ p u ≤ 1 := by
  unfold cutoffFactor
  split_ifs with hc
  · refine ⟨(Real.exp_pos _).le, ?_⟩
    rw [Real.exp_le_one_iff]
    linarith [cutoff_nonneg h hu hc]
  · exact ⟨le_rfl, zero_le_one⟩
abbrev _root_.YangMills.SharedProofs.p2957 := @cutoffFactor_nonneg_and_le_one
end Cutoff
section Combine
private theorem holdsAtEveryStep_and {P Q : ParameterAssignment → ∀ R : StepSetup, ResponseSetup R → Prop} (hP : HoldsAtEveryStep P)
    (hQ : HoldsAtEveryStep Q) : HoldsAtEveryStep fun T R A => P T R A ∧ Q T R A := by
  obtain ⟨r₁, h₁, H₁⟩ := hP
  obtain ⟨r₂, h₂, H₂⟩ := hQ
  refine ⟨fun c => min (r₁ c) (r₂ c), fun c => lt_min (h₁ c) (h₂ c), fun T hT hr K => ?_⟩
  obtain ⟨y₁, Y₁⟩ := H₁ T hT (hr.trans (min_le_left _ _)) K
  obtain ⟨y₂, Y₂⟩ := H₂ T hT (hr.trans (min_le_right _ _)) K
  refine ⟨max y₁ y₂, fun y hy R A hK hA => ⟨Y₁ y ((le_max_left _ _).trans hy) R A hK hA,
    Y₂ y ((le_max_right _ _).trans hy) R A hK hA⟩⟩
abbrev _root_.YangMills.SharedProofs.p19358 := @holdsAtEveryStep_and
end Combine
section Sums
variable {R : StepSetup} {n : ℕ} [NeZero n] {C : Finset (TorusSite n)} {V : TorusField n} {q : CoarseState R n}
private theorem caseMean_finset_sum
    (hadd : ∀ F F' : CaseFunction R n, CaseIntegrable R C V q F → CaseIntegrable R C V q F' →
      CaseIntegrable R C V q (fun W Yt ωt bad b => F W Yt ωt bad b + F' W Yt ωt bad b) ∧
      caseMean R C V q (fun W Yt ωt bad b => F W Yt ωt bad b + F' W Yt ωt bad b) =
        caseMean R C V q F + caseMean R C V q F')
    (h0 : CaseIntegrable R C V q (fun _ _ _ _ _ => 0) ∧ caseMean R C V q (fun _ _ _ _ _ => 0) = 0)
    {ι : Type} (s : Finset ι) (F : ι → CaseFunction R n) (hF : ∀ i ∈ s, CaseIntegrable R C V q (F i)) :
    CaseIntegrable R C V q (fun W Yt ωt bad b => ∑ i ∈ s, F i W Yt ωt bad b) ∧
      caseMean R C V q (fun W Yt ωt bad b => ∑ i ∈ s, F i W Yt ωt bad b) = ∑ i ∈ s, caseMean R C V q (F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using h0
  | insert a s ha ih =>
    have ih' := ih fun i hi => hF i (Finset.mem_insert_of_mem hi)
    have e : (fun W Yt ωt bad b => ∑ i ∈ insert a s, F i W Yt ωt bad b) =
        fun W Yt ωt bad b => F a W Yt ωt bad b + ∑ i ∈ s, F i W Yt ωt bad b := by
      funext W Yt ωt bad b
      exact Finset.sum_insert ha
    rw [e, Finset.sum_insert ha]
    have h := hadd _ _ (hF a (Finset.mem_insert_self _ _)) ih'.1
    exact ⟨h.1, h.2.trans (by rw [ih'.2])⟩
abbrev _root_.YangMills.SharedProofs.p34211 := @caseMean_finset_sum
end Sums
section Step
variable {R : StepSetup} {A : ResponseSetup R} {n : ℕ} [NeZero n]
private theorem hull_eq_zero_of_not_mem
    (hrow : ResponseBounds R.params A.responseParams R.depth R.coupling A.coeff R.labels R.labelWeight A.score A.cold A.hull
      A.siteRemainder A.totalRemainder)
    (hbs : IsBlockTorusSide R.params (n * R.params.side)) {W : TorusField (n * R.params.side)}
    {Yt : Finset (TorusSite (n * R.params.side))} {ωt : Yt → R.labels.Ω}
    (hl : IsLiveState R.params R.coupling R.labelWeight W Yt ωt) (f : PlaquetteWeight (fineSide R.params.side (R.depth + 1) n))
    {y : TorusSite (n * R.params.side)}
    (hy : y ∉ weightSupportSites R.params.side R.depth (n * R.params.side) f) :
    A.hull (n * R.params.side) y W Yt ωt f = 0 := by
  have h1 : A.hull (n * R.params.side) y W Yt ωt f = A.hull (n * R.params.side) y W Yt ωt 0 :=
    hrow.hull_reads (n * R.params.side) hbs y W Yt ωt hl f 0 (fun p hp => by
      by_contra hne
      exact hy (mem_weightSupportSites_iff.2 ⟨p, hp, hne⟩))
  have h2 := hrow.hull_linear (n * R.params.side) hbs y W Yt ωt hl (-1) 0 0
  simp only [smul_zero, add_zero] at h2
  rw [h1]
  linarith
private theorem sum_sitesInBlocks_image {L : ℕ} [NeZero L] (St : Finset (TorusSite (n * L))) (g : TorusSite (n * L) → ℝ)
    (hg : ∀ y, y ∉ St → g y = 0) :
    ∑ Y ∈ (open Classical in St.image (parentBlock L)), ∑ y ∈ sitesInBlocks L {Y}, g y = ∑ y ∈ St, g y := by
  classical
  have e := Finset.sum_fiberwise_of_maps_to (s := St) (t := St.image (parentBlock L)) (g := parentBlock L)
    (fun y hy => Finset.mem_image_of_mem _ hy) g
  rw [← e]
  refine Finset.sum_congr rfl fun Y _ => ?_
  symm
  refine Finset.sum_subset (fun y hy => ?_) (fun y hy hn => ?_)
  · exact mem_sitesInBlocks_iff.2 (Finset.mem_singleton.2 (Finset.mem_filter.1 hy).2)
  · refine hg y fun hS => hn (Finset.mem_filter.2 ⟨hS, ?_⟩)
    exact Finset.mem_singleton.1 (mem_sitesInBlocks_iff.1 hy)
private theorem supportResponseSum_split
    (hrow : ResponseBounds R.params A.responseParams R.depth R.coupling A.coeff R.labels R.labelWeight A.score A.cold A.hull
      A.siteRemainder A.totalRemainder)
    (hbs : IsBlockTorusSide R.params (n * R.params.side)) (f : PlaquetteWeight (fineSide R.params.side (R.depth + 1) n))
    (V : TorusField n) {W : TorusField (n * R.params.side)} {Yt : Finset (TorusSite (n * R.params.side))}
    {ωt : Yt → R.labels.Ω} (bad : Finset (TorusBond (n * R.params.side)))
    (b : BaseChoice R.params.side n) (hl : IsLiveState R.params R.coupling R.labelWeight W Yt ωt) :
    ∑ Y ∈ weightSupportSites R.params.side (R.depth + 1) n f, caseResponse A V Y f W Yt ωt bad b +
        -(∑ y ∈ weightSupportSites R.params.side R.depth (n * R.params.side) f,
          A.cold (n * R.params.side) y (trivialField (n * R.params.side)) f) * 1 =
      supportResponseSum A V f W Yt ωt bad b := by
  classical
  have hs := sum_sitesInBlocks_image (L := R.params.side) (weightSupportSites R.params.side R.depth (n * R.params.side) f)
    (fun y => A.hull (n * R.params.side) y W Yt ωt f) (fun y hy => hull_eq_zero_of_not_mem hrow hbs hl f hy)
  rw [image_parentBlock_weightSupportSites] at hs
  unfold caseResponse supportResponseSum centeredHullResponse
  rw [Finset.sum_add_distrib, hs, Finset.sum_sub_distrib, Finset.mul_sum]
  have e : ∑ Y ∈ weightSupportSites R.params.side (R.depth + 1) n f,
      R.params.coupling / 2 * A.coeff * blockMean R.params.side (R.depth + 1) n Y f * blockBondScores W V b Y =
      ∑ Y ∈ weightSupportSites R.params.side (R.depth + 1) n f,
        R.params.coupling / 2 * A.coeff * (blockMean R.params.side (R.depth + 1) n Y f * blockBondScores W V b Y) :=
    Finset.sum_congr rfl fun Y _ => by ring
  rw [e]
  ring
abbrev _root_.YangMills.SharedProofs.p48742 := @supportResponseSum_split
end Step
section Main
variable {R : StepSetup} {n : ℕ} [NeZero n]
private theorem stepWeight_nonneg_and_live (hrow : R.HasExpansions) (hK : BondKernelProperties)
    (hcut : IsCutoff R.ballRadius R.barrierFn)
    (hbs : IsBlockTorusSide R.params (n * R.params.side)) (C : Finset (TorusSite n)) (V : TorusField n)
    {W : TorusField (n * R.params.side)} {Yt : Finset (TorusSite (n * R.params.side))} (ωt : Yt → R.labels.Ω)
    (bad : Finset (TorusBond (n * R.params.side))) (b : BaseChoice R.params.side n)
    (hh : IsHullState R.params R.range W Yt) :
    0 ≤ stepWeight R C V W Yt ωt bad b ∧
      (0 < stepWeight R C V W Yt ωt bad b → IsLiveState R.params R.coupling R.labelWeight W Yt ωt) := by
  classical
  have hD : 0 ≤ R.labelWeight (n * R.params.side) W Yt ωt := hrow.2.nonneg _ hbs W Yt ωt hh
  constructor
  · unfold stepWeight
    refine mul_nonneg (mul_nonneg (mul_nonneg hD ?_) ?_) ?_
    · unfold baseLaw
      split_ifs
      · positivity
      · exact le_rfl
    · exact Finset.prod_nonneg fun c _ => (hK.2 _ _ _ _ _ _ _).1.le
    · unfold markProduct
      refine Finset.prod_nonneg fun β' _ => ?_
      have h := cutoffFactor_nonneg_and_le_one hcut
        (u := ‖((chartCoord R.params V W β' : imaginaryQuaternions) : Quaternion ℝ) -
        ((frameCoord R.params R.anchorRadius R.depth R.frameReach V β' : imaginaryQuaternions) : Quaternion ℝ)‖)
        (norm_nonneg _)
      split_ifs
      · unfold bondMark
        linarith [h.2]
      · exact h.1
  · intro hw
    refine ⟨hh, lt_of_le_of_ne hD fun h0 => hw.ne' ?_⟩
    unfold stepWeight
    rw [← h0]
    ring
abbrev _root_.YangMills.SharedProofs.p15922 := @stepWeight_nonneg_and_live
end Main
theorem supportResponseMeanStatement_holds (hC : caseMeanProperties) (hMS : meanSiteScoresStepBound)
    (hFL : labelFunctionsIntegrableStatement) (hMass : CoarseStateWeightNeZeroOnGround)
    (hIR : coldStepIntegralEqGasMean) (hSc : BondScoreProperties)
    (hMW : BlockMeanIsLinearAndLocal) (hK : BondKernelProperties) : supportResponseMeanStatement := by
  classical
  obtain ⟨rt₀, hrt₀, H⟩ := holdsAtEveryStep_and (holdsAtEveryStep_and hMS hFL) (holdsAtEveryStep_and hMass hIR)
  refine ⟨rt₀, hrt₀, fun T hT hr K => ?_⟩
  obtain ⟨y₀, Y₀⟩ := H T hT hr K
  refine ⟨max y₀ T.floorMin, fun y hy R A hKA hA n _ f => ?_⟩
  obtain ⟨⟨ms, fl⟩, mass, ir⟩ := Y₀ y ((le_max_left _ _).trans hy) R A hKA hA
  have hy' : T.floorMin ≤ y := (le_max_right _ _).trans hy
  have hparams := hA.onFamily.params_eq
  have hfit : R.params.Admissible := hparams ▸ hT.fits y hy'
  have hrow := hA.onFamily.isStep.1
  have hresp := hA.admissible.bounds
  have hLpos : 0 < R.params.side := Nat.pos_of_ne_zero (NeZero.ne _)
  have hcut : IsCutoff R.ballRadius R.barrierFn := by
    have hρ : R.ballRadius = T.ballRadius := by
      unfold StepSetup.ballRadius
      rw [hparams]
      rfl
    rw [hρ, hA.onFamily.barrierFn_eq]
    exact hT.cut
  have hbsn : R.params.n₀ ≤ n → IsBlockTorusSide R.params (n * R.params.side) := fun hn =>
    ⟨Dvd.intro_left _ rfl, by rw [mul_comm]; exact Nat.mul_le_mul_right _ hn⟩
  have hn₀ : ∀ G : GasGround R n, G.IsAdmissibleGround → R.params.n₀ ≤ n := by
    rintro G (h | h)
    · exact h.n₀_le
    · exact (Nat.le_mul_of_pos_left _ hLpos).trans h.isBlockSide.2
  have resp : ∀ G : GasGround R n, G.IsAdmissibleGround →
      CaseIntegrable R G.cut G.coarse G.state (supportResponseSum A G.coarse f) ∧
      CaseIntegrable R G.cut G.coarse G.state (fun _ _ _ _ _ => 1) ∧
      caseMean R G.cut G.coarse G.state (fun _ _ _ _ _ => 1) = 1 ∧
      caseMean R G.cut G.coarse G.state (supportResponseSum A G.coarse f) =
        ∑ Y ∈ weightSupportSites R.params.side (R.depth + 1) n f,
            caseMean R G.cut G.coarse G.state (caseResponse A G.coarse Y f) -
          ∑ y ∈ weightSupportSites R.params.side R.depth (n * R.params.side) f,
            A.cold (n * R.params.side) y (trivialField (n * R.params.side)) f := by
    intro G hG
    have hbs := hbsn (hn₀ G hG)
    have hp := hC R n G.cut G.coarse G.state
      (fun W Yt ωt bad b hh => (stepWeight_nonneg_and_live hrow hK hcut hbs G.cut G.coarse ωt bad b hh).1)
    have h1 : CaseIntegrable R G.cut G.coarse G.state (fun _ _ _ _ _ => 1) :=
      fl n G hG ∅ (fun _ _ => 1) (fun _ => measurable_const) (fun Yt ωt => by simp [scoreSumOn])
    have hone := hp.2.2.2.2.1 h1 (mass n G hG)
    have h0 : CaseIntegrable R G.cut G.coarse G.state (fun _ _ _ _ _ => 0) ∧
        caseMean R G.cut G.coarse G.state (fun _ _ _ _ _ => 0) = 0 := by
      have h := hp.2.2.1 0 _ h1
      simpa only [zero_mul] using h
    have hs := caseMean_finset_sum hp.2.1 h0 (weightSupportSites R.params.side (R.depth + 1) n f)
      (fun Y => caseResponse A G.coarse Y f) (fun Y _ => (ir n G hG Y f).1)
    have hc := hp.2.2.1 (-(∑ y ∈ weightSupportSites R.params.side R.depth (n * R.params.side) f,
      A.cold (n * R.params.side) y (trivialField (n * R.params.side)) f)) _ h1
    have ha := hp.2.1 _ _ hs.1 hc.1
    have he := hp.1 _ (supportResponseSum A G.coarse f) (fun W Yt ωt bad b hh hw =>
      supportResponseSum_split hresp hbs f G.coarse bad b
        ((stepWeight_nonneg_and_live hrow hK hcut hbs G.cut G.coarse ωt bad b hh).2 hw))
    refine ⟨he.1 ha.1, h1, hone, ?_⟩
    rw [← he.2, ha.2, hs.2, hc.2, hone]
    ring
  refine ⟨fun G hG => ?_, fun hn hs1 hs2 W V b => ?_⟩
  · obtain ⟨hsr, h1, hone, hmean⟩ := resp G hG
    have hG0 : (coldCaseGround R (trivialField n)).IsAdmissibleGround :=
      coldCaseGround_trivialField_isAdmissible R n (hn₀ G hG) hfit
    have hmean0 : caseMean R ∅ (trivialField n) (emptyCoarseState R) (supportResponseSum A (trivialField n) f) =
        ∑ Y ∈ weightSupportSites R.params.side (R.depth + 1) n f,
            caseMean R ∅ (trivialField n) (emptyCoarseState R) (caseResponse A (trivialField n) Y f) -
          ∑ y ∈ weightSupportSites R.params.side R.depth (n * R.params.side) f,
            A.cold (n * R.params.side) y (trivialField (n * R.params.side)) f :=
      (resp _ hG0).2.2.2
    have hp := hC R n G.cut G.coarse G.state (fun W Yt ωt bad b hh =>
      (stepWeight_nonneg_and_live hrow hK hcut (hbsn (hn₀ G hG)) G.cut G.coarse ωt bad b hh).1)
    have hc := hp.2.2.1
      (-(caseMean R ∅ (trivialField n) (emptyCoarseState R) (supportResponseSum A (trivialField n) f))) _ h1
    have ha := hp.2.1 _ _ hsr hc.1
    have e : centeredSupportResponse A G.coarse f = fun W Yt ωt bad b =>
        supportResponseSum A G.coarse f W Yt ωt bad b +
          -(caseMean R ∅ (trivialField n) (emptyCoarseState R) (supportResponseSum A (trivialField n) f)) * 1 := by
      funext W Yt ωt bad b
      simp only [centeredSupportResponse, mul_one, sub_eq_add_neg]
    rw [e]
    refine ⟨ha.1, ?_⟩
    rw [ha.2, hc.2, hone, hmean, hmean0, Finset.sum_sub_distrib]
    ring
  · have hbs := hbsn hn
    have hG0 : (coldCaseGround R (trivialField n)).IsAdmissibleGround :=
      coldCaseGround_trivialField_isAdmissible R n hn hfit
    obtain ⟨hsr₀, h1₀, hone₀, -⟩ := resp _ hG0
    have hone : caseMean R ∅ (trivialField n) (emptyCoarseState R) (fun _ _ _ _ _ => 1) = 1 := hone₀
    have hsr : CaseIntegrable R ∅ (trivialField n) (emptyCoarseState R) (supportResponseSum A (trivialField n) f) := hsr₀
    have h1 : CaseIntegrable R ∅ (trivialField n) (emptyCoarseState R) (fun _ _ _ _ _ => 1) := h1₀
    have hKf := hA.admissible.params_admissible
    have ha1 : 1 ≤ R.params.coupling := hfit.a_ge
    have hC₀ : 32 * R.params.coupling + 2 ≤ A.responseParams.C₀ := by
      rw [hKf.C₀_eq]
      linarith [hKf.N₀_nonneg, hKf.Kc_ge]
    have hal : |A.coeff| ≤ 2 := hA.admissible.abs_coeff_le
    have himg : (weightSupportSites R.params.side (R.depth + 1) n f) =
        (weightSupportSites R.params.side R.depth (n * R.params.side) f).image (parentBlock R.params.side) :=
      (image_parentBlock_weightSupportSites _ _ f).symm
    have hcard : (((weightSupportSites R.params.side (R.depth + 1) n f)).card : ℝ) ≤
        ((weightSupportSites R.params.side R.depth (n * R.params.side) f)).card := by
      rw [himg]
      exact_mod_cast Finset.card_image_le
    have hc0 : (0 : ℝ) ≤ ((weightSupportSites R.params.side R.depth (n * R.params.side) f)).card := Nat.cast_nonneg _
    have hmeanle : ∀ Y, |blockMean R.params.side (R.depth + 1) n Y f| ≤ 1 := fun Y =>
      abs_blockMean_le hMW hfit.L_odd _ _ Y f 1 fun p => (abs_le_weightSup f p).trans ((le_max_left _ _).trans hs2)
    have hsc : ∀ (W : TorusField (n * R.params.side)) (V : TorusField n) (b : BaseChoice R.params.side n) (Y : TorusSite n),
        |blockBondScores W V b Y| ≤ 16 := by
      intro W V b Y
      unfold blockBondScores
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      have h : ∀ i ∈ (Finset.univ : Finset (Fin 4)),
          |bondScore R.params R.coupling W V b (Y, i) + bondScore R.params R.coupling W V b (Y - TorusFields.unitStep n i, i)| ≤ 4 := by
        intro i _
        have h2 := (hSc R.params hfit R.coupling n b (Y, i)).2.2.1 W V
        have h3 := (hSc R.params hfit R.coupling n b (Y - TorusFields.unitStep n i, i)).2.2.1 W V
        exact (abs_add_le _ _).trans (by linarith)
      refine (Finset.sum_le_sum h).trans ?_
      simp
      norm_num
    have hmb : ∀ (W : TorusField (n * R.params.side)) (V : TorusField n) (b : BaseChoice R.params.side n),
        |R.params.coupling / 2 * A.coeff * ∑ Y ∈ (weightSupportSites R.params.side (R.depth + 1) n f),
            blockMean R.params.side (R.depth + 1) n Y f * blockBondScores W V b Y| ≤
          16 * R.params.coupling * ((weightSupportSites R.params.side R.depth (n * R.params.side) f)).card := by
      intro W V b
      have h1' : |R.params.coupling / 2 * A.coeff| ≤ R.params.coupling := by
        rw [abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ R.params.coupling / 2)]
        nlinarith [abs_nonneg A.coeff]
      have h2' : |∑ Y ∈ (weightSupportSites R.params.side (R.depth + 1) n f),
            blockMean R.params.side (R.depth + 1) n Y f * blockBondScores W V b Y| ≤
          16 * ((weightSupportSites R.params.side R.depth (n * R.params.side) f)).card := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        have h3 : ∀ Y ∈ (weightSupportSites R.params.side (R.depth + 1) n f),
            |blockMean R.params.side (R.depth + 1) n Y f * blockBondScores W V b Y| ≤ 16 := by
          intro Y _
          rw [abs_mul]
          calc _ ≤ 1 * 16 := mul_le_mul (hmeanle Y) (hsc W V b Y) (abs_nonneg _) zero_le_one
            _ = 16 := one_mul _
        refine (Finset.sum_le_sum h3).trans ?_
        rw [Finset.sum_const, nsmul_eq_mul]
        linarith
      rw [abs_mul]
      calc _ ≤ R.params.coupling * (16 * (((weightSupportSites R.params.side R.depth (n * R.params.side) f)).card : ℝ)) :=
            mul_le_mul h1' h2' (abs_nonneg _) (by linarith)
        _ = _ := by ring
    have hv : |caseMean R ∅ (trivialField n) (emptyCoarseState R) (supportResponseSum A (trivialField n) f)| ≤
        (A.responseParams.C₀ + 16 * R.params.coupling + 2) *
          ((weightSupportSites R.params.side R.depth (n * R.params.side) f)).card := by
      have hp := hC R n ∅ (trivialField n) (emptyCoarseState R) (fun W Yt ωt bad b hh =>
        (stepWeight_nonneg_and_live hrow hK hcut hbs ∅ (trivialField n) ωt bad b hh).1)
      by_cases hne : (weightSupportSites R.params.side R.depth (n * R.params.side) f).Nonempty
      · have hN := ms n (coldCaseGround R (trivialField n)) hG0 1
          (fun _ => (weightSupportSites R.params.side R.depth (n * R.params.side) f)) (fun _ => hne)
          (fun i j hij => absurd (Subsingleton.elim i j) hij)
        have eN : prodMeanSiteScores A (fun _ : Fin 1 => (weightSupportSites R.params.side R.depth (n * R.params.side) f)) =
            fun _ Yt ωt _ _ => meanSiteScore A.score (weightSupportSites R.params.side R.depth (n * R.params.side) f) Yt ωt := by
          funext W Yt ωt bad b
          simp [prodMeanSiteScores]
        rw [eN] at hN
        have hch : 0 ≤ T.gasRate := by
          have h2 := hT.fits y hy'
          have hκ : 0 < T.κ := h2.κ_pos
          have hκ₁ : 0 < T.κ₁ := h2.κ₁_pos
          have hσ : 0 < T.threshold := h2.σ_pos
          unfold ParameterAssignment.gasRate
          exact mul_nonneg (by positivity) (le_min hT.cE_pos.le (le_min (by positivity) (by positivity)))
        have hx : 0 ≤ R.coupling := by
          have h2 : (0 : ℝ) ≤ T.floorMin := le_trans (by positivity) (le_max_right T.yC ((2 : ℝ) ^ 1600))
          linarith [hA.onFamily.le_coupling]
        have hN1 : caseMean R ∅ (trivialField n) (emptyCoarseState R)
            (fun _ Yt ωt _ _ => meanSiteScore A.score (weightSupportSites R.params.side R.depth (n * R.params.side) f) Yt ωt) ≤ 3 := by
          refine hN.2.trans ?_
          have hs0 : ∀ y : TorusSite n, siteScore (coarseLabelScore A.responseParams.s₁ A.score)
              (coldCaseGround R (trivialField n)).state.1 (coldCaseGround R (trivialField n)).state.2 y = 0 := by
            intro y
            unfold siteScore
            exact dif_neg (Finset.notMem_empty y)
          have h1' : ∏ _i : Fin 1, meanSiteScore (coarseLabelScore A.responseParams.s₁ A.score)
              (parentBlocks (weightSupportSites R.params.side R.depth (n * R.params.side) f))
              (coldCaseGround R (trivialField n)).state.1 (coldCaseGround R (trivialField n)).state.2 = 1 := by
            simp [meanSiteScore, hs0]
          rw [h1', mul_one]
          have h2 : Real.exp (-(7 * T.gasRate * R.coupling)) ≤ 1 := Real.exp_le_one_iff.2 (by
            have : 0 ≤ 7 * T.gasRate * R.coupling := by positivity
            linarith)
          have h3 : ((1 : ℕ) : ℝ) * Real.exp (-(7 * T.gasRate * R.coupling)) ≤ 1 := by
            simpa using h2
          calc _ ≤ Real.exp 1 := Real.exp_le_exp.2 h3
            _ ≤ 3 := by linarith [Real.exp_one_lt_d9]
        have hf1 := hp.2.2.1 (((weightSupportSites R.params.side R.depth (n * R.params.side) f)).card : ℝ) _ hN.1
        have hf2 := hp.2.2.1 ((A.responseParams.C₀ + 16 * R.params.coupling - 1) *
          ((weightSupportSites R.params.side R.depth (n * R.params.side) f)).card) _ h1
        have hφ := hp.2.1 _ _ hf1.1 hf2.1
        have hle : ∀ (W : TorusField (n * R.params.side)) (Yt : Finset (TorusSite (n * R.params.side))) (ωt : Yt → R.labels.Ω)
            (bad : Finset (TorusBond (n * R.params.side))) (b : BaseChoice R.params.side n), IsHullState R.params R.range W Yt →
            0 < stepWeight R ∅ (trivialField n) W Yt ωt bad b →
            |supportResponseSum A (trivialField n) f W Yt ωt bad b| ≤
              (((weightSupportSites R.params.side R.depth (n * R.params.side) f)).card : ℝ) *
                  meanSiteScore A.score (weightSupportSites R.params.side R.depth (n * R.params.side) f) Yt ωt +
                (A.responseParams.C₀ + 16 * R.params.coupling - 1) *
                  ((weightSupportSites R.params.side R.depth (n * R.params.side) f)).card * 1 := by
          intro W Yt ωt bad b hh hw
          have hl := (stepWeight_nonneg_and_live hrow hK hcut hbs ∅ (trivialField n) ωt bad b hh).2 hw
          have hsum : |∑ y ∈ (weightSupportSites R.params.side R.depth (n * R.params.side) f),
                centeredHullResponse A.cold A.hull (n * R.params.side) y W Yt ωt f| ≤
              ∑ y ∈ (weightSupportSites R.params.side R.depth (n * R.params.side) f),
                (A.responseParams.C₀ + siteScore A.score Yt ωt y) := by
            refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun y _ => ?_)
            have h2 := hresp.size_hull (n * R.params.side) hbs y W Yt ωt hl f
            have h3 : 0 ≤ siteScore A.score Yt ωt y := by
              unfold siteScore
              split_ifs
              · exact hA.admissible.price.nonneg _
              · exact le_rfl
            have h4 : 0 ≤ A.responseParams.C₀ + siteScore A.score Yt ωt y := by linarith
            calc _ ≤ (A.responseParams.C₀ + siteScore A.score Yt ωt y) * weightNorm R.params.side R.depth f := h2
              _ ≤ (A.responseParams.C₀ + siteScore A.score Yt ωt y) * 1 := mul_le_mul_of_nonneg_left hs1 h4
              _ = _ := mul_one _
          have hcne : (((weightSupportSites R.params.side R.depth (n * R.params.side) f)).card : ℝ) ≠ 0 := by
            exact_mod_cast (Finset.card_pos.2 hne).ne'
          have hN' : (((weightSupportSites R.params.side R.depth (n * R.params.side) f)).card : ℝ) *
                meanSiteScore A.score (weightSupportSites R.params.side R.depth (n * R.params.side) f) Yt ωt =
              ((weightSupportSites R.params.side R.depth (n * R.params.side) f)).card +
                ∑ y ∈ (weightSupportSites R.params.side R.depth (n * R.params.side) f), siteScore A.score Yt ωt y := by
            unfold meanSiteScore
            rw [mul_add, mul_one, mul_inv_cancel_left₀ hcne]
          have hsum' : ∑ y ∈ (weightSupportSites R.params.side R.depth (n * R.params.side) f),
                (A.responseParams.C₀ + siteScore A.score Yt ωt y) =
              A.responseParams.C₀ * ((weightSupportSites R.params.side R.depth (n * R.params.side) f)).card +
                ∑ y ∈ (weightSupportSites R.params.side R.depth (n * R.params.side) f), siteScore A.score Yt ωt y := by
            rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
            ring
          have hm := hmb W (trivialField n) b
          show |∑ y ∈ (weightSupportSites R.params.side R.depth (n * R.params.side) f),
              centeredHullResponse A.cold A.hull (n * R.params.side) y W Yt ωt f + R.params.coupling / 2 * A.coeff *
            ∑ Y ∈ (weightSupportSites R.params.side (R.depth + 1) n f),
              blockMean R.params.side (R.depth + 1) n Y f * blockBondScores W (trivialField n) b Y| ≤ _
          refine (abs_add_le _ _).trans ?_
          rw [hN']
          nlinarith
        have hm1 := hp.2.2.2.1 _ _ hsr hφ.1
          (fun W Yt ωt bad b hh hw => (le_abs_self _).trans (hle W Yt ωt bad b hh hw))
        have hneg := hp.2.2.1 (-1) _ hsr
        have hm2 := hp.2.2.2.1 _ _ hneg.1 hφ.1 (fun W Yt ωt bad b hh hw => by
          have h2 := neg_abs_le (supportResponseSum A (trivialField n) f W Yt ωt bad b)
          have h3 := hle W Yt ωt bad b hh hw
          show -1 * supportResponseSum A (trivialField n) f W Yt ωt bad b ≤ _
          linarith)
        have hE : caseMean R ∅ (trivialField n) (emptyCoarseState R) (fun W Yt ωt bad b =>
            (((weightSupportSites R.params.side R.depth (n * R.params.side) f)).card : ℝ) *
                meanSiteScore A.score (weightSupportSites R.params.side R.depth (n * R.params.side) f) Yt ωt +
              (A.responseParams.C₀ + 16 * R.params.coupling - 1) *
                ((weightSupportSites R.params.side R.depth (n * R.params.side) f)).card * 1) ≤
            (A.responseParams.C₀ + 16 * R.params.coupling + 2) *
              ((weightSupportSites R.params.side R.depth (n * R.params.side) f)).card := by
          have e1 := hφ.2
          rw [hf1.2, hf2.2, hone] at e1
          refine e1.le.trans ?_
          nlinarith
        rw [hneg.2] at hm2
        have h3 := hm2.trans hE
        rw [abs_le]
        exact ⟨by linarith, hm1.trans hE⟩
      · have hSe : (weightSupportSites R.params.side R.depth (n * R.params.side) f) = ∅ :=
          Finset.not_nonempty_iff_eq_empty.1 hne
        have hSne : (weightSupportSites R.params.side (R.depth + 1) n f) = ∅ := by
          rw [himg, hSe]
          simp
        have e : supportResponseSum A (trivialField n) f = fun _ _ _ _ _ => 0 * 1 := by
          funext W Yt ωt bad b
          simp [supportResponseSum, hSe, hSne]
        rw [e, (hp.2.2.1 0 _ h1).2]
        simp [hSe]
    calc _ ≤ |R.params.coupling / 2 * A.coeff * ∑ Y ∈ (weightSupportSites R.params.side (R.depth + 1) n f),
            blockMean R.params.side (R.depth + 1) n Y f * blockBondScores W V b Y| +
          |caseMean R ∅ (trivialField n) (emptyCoarseState R) (supportResponseSum A (trivialField n) f)| := abs_sub _ _
      _ ≤ 16 * R.params.coupling * ((weightSupportSites R.params.side R.depth (n * R.params.side) f)).card +
          (A.responseParams.C₀ + 16 * R.params.coupling + 2) *
            ((weightSupportSites R.params.side R.depth (n * R.params.side) f)).card := add_le_add (hmb W V b) hv
      _ ≤ _ := by nlinarith
end YangMills.Construction.FreeEnergies
end
