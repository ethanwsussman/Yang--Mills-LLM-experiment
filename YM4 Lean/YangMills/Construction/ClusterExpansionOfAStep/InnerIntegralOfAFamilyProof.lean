import YangMills.Construction.ClusterExpansionOfAStep.CaseFunctionIsBorel
import YangMills.Construction.ClusterExpansionOfAStep.FactorsOfAFamilyProof
import YangMills.Construction.ClusterExpansionOfAStep.GaugeOfACase
import YangMills.Construction.ClusterExpansionOfAStep.InnerIntegralOfAFamily
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open scoped Quaternion ENNReal
open MeasureTheory
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames BlockZones SpinFamilies FamilyZones StepGas StepSettings TorusLumps
  TorusFields RenormalizationStepParameters StepCosts
namespace ClusterExpansionOfAStep
namespace FamilyInner
variable {R : StepSetup} {n : ℕ} [NeZero n] {G : GasGround R n} {Γ : Finset G.GasSpin}
theorem cutoffFactor_nonneg (ρ : ℝ) (p : ℝ → ℝ) (u : ℝ) : 0 ≤ cutoffFactor ρ p u := by apply _root_.YangMills.Construction.CoarseFactorLocality.cutoffFactor_nonneg <;> assumption
theorem bondMark_nonneg (V : TorusField n) (W : TorusField (n * R.params.side)) (b : TorusBond (n * R.params.side)) :
    0 ≤ bondMark R V W b :=
  cutoffFactor_nonneg _ _ _
theorem caseIntegrand_eq_restIntegrand_mul (F : CaseFunctional R n) {bad : Finset (TorusBond (n * R.params.side))}
    {Yt : Finset (TorusSite (n * R.params.side))} {b : BaseChoice R.params.side n}
    {free : Finset (TorusBond (n * R.params.side))}
    (hf : free ⊆ markedBonds R G.cut) (hb : Disjoint free bad) (W : TorusField (n * R.params.side))
    (ν : G.state.unlabelled Yt → R.labels.Ω) :
    G.caseIntegrand F bad Yt b W ν =
      G.restIntegrand F bad Yt b free ν (G.state.fieldWithStoredLinks W) *
        ∏ β : free, ENNReal.ofReal (bondMark R G.coarse (G.state.fieldWithStoredLinks W) β.1) := by
  classical
  unfold GasGround.caseIntegrand GasGround.restIntegrand
  by_cases ht : IsHullState R.params R.range (G.state.fieldWithStoredLinks W) Yt ∧
      coarseStateOf R G.cut (G.state.fieldWithStoredLinks W) Yt (G.state.fillLabels Yt ν) bad b = G.state
  · rw [if_pos ht, if_pos ht, mul_assoc]
    congr 1
    have hsplit : markProduct R G.cut G.coarse (G.state.fieldWithStoredLinks W) bad =
        G.remainingMarks free bad (G.state.fieldWithStoredLinks W) *
          ∏ β : free, bondMark R G.coarse (G.state.fieldWithStoredLinks W) β.1 := by
      unfold markProduct GasGround.remainingMarks
      rw [← Finset.prod_sdiff hf]
      congr 1
      rw [Finset.prod_coe_sort free (fun β => bondMark R G.coarse (G.state.fieldWithStoredLinks W) β)]
      refine Finset.prod_congr rfl fun β hβ => ?_
      rw [if_neg (Finset.disjoint_left.mp hb hβ)]
    unfold stepWeight
    rw [hsplit, ← mul_assoc, ENNReal.ofReal_mul' (Finset.prod_nonneg fun β _ => bondMark_nonneg _ _ _),
      ENNReal.ofReal_prod_of_nonneg fun β _ => bondMark_nonneg _ _ _]
  · rw [if_neg ht, if_neg ht, zero_mul]
section Point
variable (F : CaseFunctional R n) (c : FamilyState G Γ) (ν : G.state.unlabelled (G.familySites Γ) → R.labels.Ω)
theorem restIntegrand_mul_cutoff_eq (hsep : (G.familyData c).CoresDisjoint)
    (hν : ∀ (i : Γ) (z : TorusSite (n * R.params.side)) (hz : z ∈ i.1.1.2)
      (hr : z ∈ G.state.unlabelled (G.familySites Γ)),
      ν ⟨z, hr⟩ = (c i).2.1 ⟨z, hz⟩)
    (hset : (∀ i : Γ, G.IsAllowed i.1.1 (c i)) → (G.familySetting c).IsAdmissible)
    (hpot : (G.familySetting c).IsAdmissible → ∀ η, (G.familySetting c).InBalls η →
      0 < R.functional (n * R.params.side) (trivialField (n * R.params.side)) ∧
        0 < (G.familySetting c).haarJacobian η ∧
        R.labelWeight (n * R.params.side) ((G.familySetting c).field η) (G.familySetting c).support
              (G.familySetting c).labelling *
            (G.familySetting c).kernelProduct η * (G.familySetting c).haarJacobian η =
          R.functional (n * R.params.side) (trivialField (n * R.params.side)) *
            (∏ X ∈ chainComponents R.range (G.familySetting c).support,
              R.clusterFactor (n * R.params.side) ((G.familySetting c).field η) (G.familySetting c).support
                (G.familySetting c).labelling X) *
            Real.exp (-(G.familySetting c).potential η))
    (htest : (∀ i : Γ, G.IsAllowed i.1.1 (c i)) → ∀ η, (G.familySetting c).InBalls η →
      coarseStateOf R G.cut ((G.familySetting c).field η) (G.familySites Γ)
        (G.state.fillLabels (G.familySites Γ) ν) (G.familyBadBonds Γ) (G.familySetting c).bases = G.state)
    (hfac : (∀ i : Γ, G.IsAllowed i.1.1 (c i)) → ∀ η, (G.familySetting c).InBalls η →
      (∏ X ∈ chainComponents R.range (G.familySetting c).support,
          R.clusterFactor (n * R.params.side) ((G.familySetting c).field η) (G.familySetting c).support
            (G.familySetting c).labelling X) *
        baseLaw (R := R) ((G.familySetting c).field η) (G.familySetting c).bases *
        G.remainingMarks (G.familySetting c).free (G.familyBadBonds Γ) ((G.familySetting c).field η) =
      (∏ X ∈ chainComponents R.nextRange G.state.1, coarseFactor G.coarse G.state X) *
        ∏ i : Γ, G.activity i.1.1 (c i))
    (hallow : ∀ η, G.HasWeightAt (G.familyData c) η → ∀ i : Γ, G.IsAllowed i.1.1 (c i))
    (hform : ∀ (W : TorusField (n * R.params.side)) (Y : Finset (TorusSite (n * R.params.side)))
      (ω : Y → R.labels.Ω), IsHullState R.params R.range W Y →
      R.labelWeight (n * R.params.side) W Y ω = 0 ∨
        ∀ X ∈ chainComponents R.range Y, R.clusterFactor (n * R.params.side) W Y ω X ≠ 0)
    (hP : (∀ i : Γ, G.IsAllowed i.1.1 (c i)) →
      0 ≤ ∏ X ∈ chainComponents R.nextRange G.state.1, coarseFactor G.coarse G.state X)
    (hclass : (∀ i : Γ, G.IsAllowed i.1.1 (c i)) → ∀ i : Γ, 0 ≤ G.activity i.1.1 (c i))
    (hbad : G.familyBadBonds Γ ⊆ (G.familySetting c).bad)
    (hcut : ∀ b ∈ chartBonds R.params.side n, b ∉ (G.familySetting c).bad → b ∈ markedBonds R G.cut)
    (η : FreeCoords (G.familySetting c).free) :
    G.restIntegrand F (G.familyBadBonds Γ) (G.familySites Γ) (G.familySetting c).bases (G.familySetting c).free ν
          ((G.familySetting c).field η) *
        ENNReal.ofReal ((G.familySetting c).cutoffProduct η * (G.familySetting c).haarJacobian η) =
      (ENNReal.ofReal (R.functional (n * R.params.side) (trivialField (n * R.params.side))) *
          ENNReal.ofReal (∏ X ∈ chainComponents R.nextRange G.state.1, coarseFactor G.coarse G.state X) *
          ∏ i : Γ, G.allowedActivity i.1 (c i)) *
        (F ((G.familySetting c).field η) (G.familySetting c).support (G.familySetting c).labelling
            (G.familyBadBonds Γ) (G.familySetting c).bases *
          ENNReal.ofReal ((G.familySetting c).cutoffProduct η * Real.exp (-(G.familySetting c).potential η))) := by
  classical
  by_cases hc : (G.familySetting c).cutoffProduct η = 0
  · rw [hc, zero_mul, zero_mul, ENNReal.ofReal_zero, mul_zero, mul_zero, mul_zero]
  have hlt : ∀ b, coordNorm (η b) < R.ballRadius := fun b => by
    have h1 := Finset.prod_ne_zero_iff.mp hc b (Finset.mem_univ b)
    by_contra h
    unfold cutoffFactor at h1
    rw [if_neg h] at h1
    exact h1 rfl
  have hin : (G.familySetting c).InBalls η := fun b => (hlt b).le
  have hcpos : 0 < (G.familySetting c).cutoffProduct η := Finset.prod_pos fun b _ => by
    unfold cutoffFactor
    rw [if_pos (hlt b)]
    exact Real.exp_pos _
  have hsig := familySites_fillLabels_eq c ν hsep hν
  have hDq : ∀ w, R.labelWeight (n * R.params.side) w (G.familySites Γ) (G.state.fillLabels _ ν) =
      R.labelWeight (n * R.params.side) w (G.familySetting c).support (G.familySetting c).labelling := fun w =>
    congrArg (fun p : Σ Y : Finset (TorusSite (n * R.params.side)), Y → R.labels.Ω =>
      R.labelWeight (n * R.params.side) w p.1 p.2) hsig
  have hFe : ∀ w, F w (G.familySites Γ) (G.state.fillLabels _ ν) (G.familyBadBonds Γ) (G.familySetting c).bases =
      F w (G.familySetting c).support (G.familySetting c).labelling (G.familyBadBonds Γ) (G.familySetting c).bases :=
    fun w => congrArg (fun p : Σ Y : Finset (TorusSite (n * R.params.side)), Y → R.labels.Ω =>
      F w p.1 p.2 (G.familyBadBonds Γ) (G.familySetting c).bases) hsig
  by_cases hall : ∀ i : Γ, G.IsAllowed i.1.1 (c i)
  · obtain ⟨hD, hj, he⟩ := hpot (hset hall) η hin
    have hull : IsHullState R.params R.range ((G.familySetting c).field η) (G.familySites Γ) := by
      have := (hset hall).isHull η hin
      rwa [support_familySetting] at this
    have ht : IsHullState R.params R.range ((G.familySetting c).field η) (G.familySites Γ) ∧
        coarseStateOf R G.cut ((G.familySetting c).field η) (G.familySites Γ)
          (G.state.fillLabels (G.familySites Γ) ν) (G.familyBadBonds Γ) (G.familySetting c).bases = G.state :=
      ⟨hull, htest hall η hin⟩
    unfold GasGround.restIntegrand
    rw [if_pos ht, hDq, hFe]
    have hfa := hfac hall η hin
    have hkey : R.labelWeight (n * R.params.side) ((G.familySetting c).field η) (G.familySetting c).support
            (G.familySetting c).labelling *
          baseLaw ((G.familySetting c).field η) (G.familySetting c).bases * (G.familySetting c).kernelProduct η *
          G.remainingMarks (G.familySetting c).free (G.familyBadBonds Γ) ((G.familySetting c).field η) *
          ((G.familySetting c).cutoffProduct η * (G.familySetting c).haarJacobian η) =
        R.functional (n * R.params.side) (trivialField (n * R.params.side)) *
          (((∏ X ∈ chainComponents R.nextRange G.state.1, coarseFactor G.coarse G.state X) *
              ∏ i : Γ, G.activity i.1.1 (c i)) *
            ((G.familySetting c).cutoffProduct η * Real.exp (-(G.familySetting c).potential η))) := by
      rw [← hfa]
      linear_combination (baseLaw (R := R) ((G.familySetting c).field η) (G.familySetting c).bases *
        G.remainingMarks (G.familySetting c).free (G.familyBadBonds Γ) ((G.familySetting c).field η) *
        (G.familySetting c).cutoffProduct η) * he
    have hprod : ∏ i : Γ, G.allowedActivity i.1 (c i) = ENNReal.ofReal (∏ i : Γ, G.activity i.1.1 (c i)) := by
      rw [ENNReal.ofReal_prod_of_nonneg fun i _ => hclass hall i]
      refine Finset.prod_congr rfl fun i _ => ?_
      unfold GasGround.allowedActivity
      rw [if_pos (hall i)]
    have hCJ : 0 ≤ (G.familySetting c).cutoffProduct η * (G.familySetting c).haarJacobian η := (mul_pos hcpos hj).le
    have hker : (∏ e : (stepBlockFrame R.params.side n).Cell × Fin 4,
        bondKernel R.params R.coupling (readAtLevel (stepBlockFrame R.params.side n) 0 ((G.familySetting c).field η))
          (readAtLevel (stepBlockFrame R.params.side n) 1 G.coarse) (G.familySetting c).bases e) =
        (G.familySetting c).kernelProduct η := rfl
    rw [hker, mul_assoc, ← ENNReal.ofReal_mul' hCJ, hkey, hprod, ENNReal.ofReal_mul hD.le,
      ENNReal.ofReal_mul (mul_nonneg (hP hall) (Finset.prod_nonneg fun i _ => hclass hall i)),
      ENNReal.ofReal_mul (hP hall)]
    ring
  · push Not at hall
    obtain ⟨i, hi⟩ := hall
    have hz : ∏ i : Γ, G.allowedActivity i.1 (c i) = 0 := Finset.prod_eq_zero (Finset.mem_univ i) (by
      unfold GasGround.allowedActivity
      rw [if_neg hi])
    rw [hz]
    simp only [mul_zero, zero_mul]
    have h0 : G.restIntegrand F (G.familyBadBonds Γ) (G.familySites Γ) (G.familySetting c).bases
        (G.familySetting c).free ν ((G.familySetting c).field η) = 0 := by
      by_contra hne
      unfold GasGround.restIntegrand at hne
      by_cases ht : IsHullState R.params R.range ((G.familySetting c).field η) (G.familySites Γ) ∧
          coarseStateOf R G.cut ((G.familySetting c).field η) (G.familySites Γ)
            (G.state.fillLabels (G.familySites Γ) ν) (G.familyBadBonds Γ) (G.familySetting c).bases = G.state
      · rw [if_pos ht] at hne
        have hx := (mul_ne_zero_iff.mp hne).2
        have hpos := ENNReal.ofReal_pos.mp (pos_iff_ne_zero.mpr hx)
        have hne4 := hpos.ne'
        rw [hDq] at hne4
        obtain ⟨h1, h4⟩ := mul_ne_zero_iff.mp hne4
        obtain ⟨h2, h3⟩ := mul_ne_zero_iff.mp h1
        obtain ⟨h5, h6⟩ := mul_ne_zero_iff.mp h2
        have hull' : IsHullState R.params R.range ((G.familySetting c).field η) (G.familySetting c).support := by
          rw [support_familySetting]
          exact ht.1
        refine hi (hallow η ⟨hlt, hull', ?_, h6, ?_⟩ i)
        · exact (hform _ _ _ hull').resolve_left h5
        · intro b hb hnf hnb
          have hm := hcut b hb hnb
          have hmem : b ∈ markedBonds R G.cut \ (G.familySetting c).free := Finset.mem_sdiff.mpr ⟨hm, hnf⟩
          have := Finset.prod_ne_zero_iff.mp h4 b hmem
          rwa [if_neg fun h => hnb (hbad h)] at this
      · rw [if_neg ht] at hne
        exact hne rfl
    rw [h0, zero_mul]
end Point
section Facts
theorem cutoffFactor_le_one {ρ : ℝ} {p : ℝ → ℝ} (hc : IsCutoff ρ p) {u : ℝ} (hu : 0 ≤ u) :
    cutoffFactor ρ p u ≤ 1 := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.FamilyFactors.cutoffFactor_le_one <;> assumption
theorem bondMark_le_one (hc : IsCutoff R.ballRadius R.barrierFn) (V : TorusField n)
    (W : TorusField (n * R.params.side)) (b : TorusBond (n * R.params.side)) :
    bondMark R V W b ≤ 1 := cutoffFactor_le_one hc (norm_nonneg _)
theorem activity_nonneg (hc : IsCutoff R.ballRadius R.barrierFn) (hrow : R.HasExpansions)
    (hside : IsBlockTorusSide R.params (n * R.params.side))
    (θ : GasSupport R n) (s : SupportState θ) : 0 ≤ G.activity θ s := by
  classical
  unfold GasGround.activity GasGround.supportMarks
  refine mul_nonneg (mul_nonneg (Finset.prod_nonneg fun b _ => ?_) (Finset.prod_nonneg fun X _ => ?_))
    (Finset.prod_nonneg fun y _ => ?_)
  · split_ifs
    · exact sub_nonneg.mpr (bondMark_le_one hc _ _ _)
    · exact bondMark_nonneg _ _ _
  · exact hrow.2.factor_nonneg _ hside _ _ _ _
  · unfold baseUniformWeight
    split_ifs
    · positivity
    · exact le_rfl
theorem n₀_le_of_isAdmissibleGround (hG : G.IsAdmissibleGround) (hfit : R.params.Admissible) :
    R.params.n₀ ≤ n := by
  rcases hG with h | h
  · exact h.n₀_le
  · have h1 := h.isBlockSide.2
    have hL : 1 ≤ R.params.side := Nat.one_le_iff_ne_zero.mpr (NeZero.ne _)
    calc R.params.n₀ ≤ R.params.side * R.params.n₀ := Nat.le_mul_of_pos_left _ hL
      _ ≤ n := h1
theorem isGasFamily_familyData (hΓ : G.IsPairwiseFarApart Γ) (c : FamilyState G Γ) :
    G.IsGasFamily (G.familyData c) := by
  refine ⟨fun θ h => ?_, fun θ θ' h h' e => ?_⟩
  · obtain ⟨i, rfl⟩ := (occupies_familyData_iff c).mp h
    exact i.1.2
  · obtain ⟨i, rfl⟩ := (occupies_familyData_iff c).mp h
    obtain ⟨j, rfl⟩ := (occupies_familyData_iff c).mp h'
    exact hΓ i.1 i.2 j.1 j.2 fun h => e (congrArg Subtype.val h)
theorem familyBadBonds_subset_bad (c : FamilyState G Γ) : G.familyBadBonds Γ ⊆ (G.familySetting c).bad := by
  classical
  intro b hb
  show b ∈ G.recordedBad ∪ (Finset.univ.filter fun θ => (G.familyData c).Occupies θ).biUnion Prod.fst ∪
    (chartBonds R.params.side n).filter fun b => parentBlock R.params.side b.1 ∈ G.cut
  rcases Finset.mem_union.mp hb with h | h
  · exact Finset.mem_union_left _ (Finset.mem_union_left _ h)
  · obtain ⟨i, hi, hbi⟩ := Finset.mem_biUnion.mp h
    exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_biUnion.mpr
      ⟨i.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, (occupies_familyData_iff c).mpr ⟨⟨i, hi⟩, rfl⟩⟩, hbi⟩))
theorem mem_markedBonds_of_not_mem_bad (c : FamilyState G Γ) {b : TorusBond (n * R.params.side)}
    (hb : b ∈ chartBonds R.params.side n)
    (hn : b ∉ (G.familySetting c).bad) : b ∈ markedBonds R G.cut := by
  classical
  refine Finset.mem_filter.mpr ⟨hb, fun hC => hn ?_⟩
  exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hb, hC⟩)
end Facts
end FamilyInner
open FamilyInner in
theorem familyInnerLintegral_proof (hA : StatesAllowedOfWeight) (hFa : FamilyFactorization)
    (hTe : FamilyRecoversState) (hGa : RestIntegrandGaugeInvariant) (hBo : CaseIntegrandMeasurable)
    (hCf : GasConfigIsAdmissibleSetting) (hPo : PotentialFactorization)
    (hFr : HaarInChartCoordinates)
    (hf1 : CouplingFloorExists) : FamilyInnerLintegral := by
  classical
  intro T hT
  obtain ⟨y₁, hA⟩ := hA T hT
  obtain ⟨y₂, hFa⟩ := hFa T hT
  obtain ⟨y₃, hTe⟩ := hTe T hT
  obtain ⟨y₄, hGa⟩ := hGa T hT
  obtain ⟨y₅, hBo⟩ := hBo T hT
  obtain ⟨y₆, hCf⟩ := hCf T hT
  obtain ⟨y₈, hf1⟩ := hf1 1 (64 * T.side) T.rt one_pos
  refine ⟨max y₁ (max y₂ (max y₃ (max y₄ (max y₅ (max y₆ (max y₈ T.floorMin)))))),
    fun y hy R hR hx' n _ G hG F hF Γ hΓ c ν hν => ?_⟩
  have b₁ : y₁ ≤ y := le_trans (by simp) hy
  have b₂ : y₂ ≤ y := le_trans (by simp) hy
  have b₃ : y₃ ≤ y := le_trans (by simp) hy
  have b₄ : y₄ ≤ y := le_trans (by simp) hy
  have b₅ : y₅ ≤ y := le_trans (by simp) hy
  have b₆ : y₆ ≤ y := le_trans (by simp) hy
  have b₈ : y₈ ≤ y := le_trans (by simp) hy
  have b₉ : T.floorMin ≤ y := le_trans (by simp) hy
  have hfit : R.params.Admissible := by rw [hR.params_eq]; exact hT.fits y b₉
  have eL : R.params.side = T.side := by rw [hR.params_eq]; rfl
  have eσ : R.params.threshold = T.threshold := by rw [hR.params_eq]; rfl
  have hfar : 64 * R.params.side ≤ R.range := by
    have := (hf1 R.coupling (b₈.trans hR.le_coupling)).1
    rw [eL]
    exact this
  have hL1 : 1 ≤ R.params.side := Nat.one_le_iff_ne_zero.mpr (NeZero.ne _)
  have hbig : 1 ≤ R.range := by omega
  have hr2 : R.params.side ≤ 2 * R.range := by omega
  have hcut : IsCutoff R.ballRadius R.barrierFn := by
    have e : R.ballRadius = T.ballRadius := by
      unfold StepSetup.ballRadius ParameterAssignment.ballRadius
      rw [eσ]
    rw [e, hR.barrierFn_eq]
    exact hT.cut
  have hrow : R.HasExpansions := hR.isStep.1
  have hn₀ := n₀_le_of_isAdmissibleGround hG hfit
  have hn2 : 2 ≤ n := by
    have := hfit.n₀_ge
    omega
  have hside : IsBlockTorusSide R.params (n * R.params.side) :=
    ⟨Dvd.intro_left n rfl, by rw [Nat.mul_comm]; exact Nat.mul_le_mul_right _ hn₀⟩
  obtain ⟨Z, hZ⟩ := exists_isAdmissibleZone G hG
  have hsep := coresDisjoint_familyData hΓ hr2 c
  have hsub : (G.familySetting c).free ⊆ markedBonds R G.cut := fun b hb => (mem_free_settingOf hb).1
  have hdis : Disjoint (G.familySetting c).free (G.familyBadBonds Γ) := by
    refine Finset.disjoint_left.mpr fun b hb hb' => ?_
    have h1 := far_of_mem_bad hZ hb (familyBadBonds_subset_bad c hb')
    rw [supDist_self] at h1
    omega
  have e1 : ∀ W, G.caseIntegrand F (G.familyBadBonds Γ) (G.familySites Γ) (G.familySetting c).bases
        (G.overwriteField c W) ν =
      G.restIntegrand F (G.familyBadBonds Γ) (G.familySites Γ) (G.familySetting c).bases (G.familySetting c).free ν
        ((G.familySetting c).glueOver (G.freeBlocks Γ) W) *
        ∏ β : (G.familySetting c).free, ENNReal.ofReal
          ((G.familySetting c).bondCutoff ((G.familySetting c).glueOver (G.freeBlocks Γ) W) β) := by
    intro W
    rw [caseIntegrand_eq_restIntegrand_mul F hsub hdis, fieldWithStoredLinks_overwriteField hZ hbig hfar c hsep]
    rfl
  simp only [e1]
  have hHm := (hBo y b₅ R hR hx' n G hG).2.1 F hF (G.familyBadBonds Γ) (G.familySetting c).free (G.familySites Γ)
    (G.familySetting c).bases ν
  rw [hFr R hfit.L_odd hcut n hn2 (G.familySetting c) (G.freeBlocks Γ) (isChartCover_familySetting hZ hbig c hsep) _ hHm
    (fun g hg W => hGa y b₄ R hR hx' n G hG F hF Γ hΓ c ν g hg W)]
  have hset : (∀ i : Γ, G.IsAllowed i.1.1 (c i)) → (G.familySetting c).IsAdmissible := by
    intro hall
    have h := hCf y b₆ R hR hx' n G hG (valuesOn (S := fun i : G.GasSpin => G.SpinState i) Γ
      fun i => ⟨c i, hall i⟩) (isAdmissible_valuesOn hΓ _)
    rwa [familyOf_valuesOn] at h
  have hpos : 0 < R.anchorRadius ∧ R.anchorRadius + R.ballRadius < Real.pi := by
    have h1 := hT.chain.2.2.2.1
    have h2 := hT.chain.2.2.2.2.1
    have h3 := hT.σ_one
    have h4 := Real.pi_gt_three
    rw [hR.anchorRadius_eq]
    refine ⟨h1, ?_⟩
    have e : R.ballRadius = T.threshold / 64 := by
      unfold StepSetup.ballRadius
      rw [eσ]
    rw [e]
    linarith
  have hpt := fun η => restIntegrand_mul_cutoff_eq F c ν hsep hν hset
    (fun hs η hin => by
      obtain ⟨a1, -, a3, a4, -⟩ := hPo R hfit hrow hpos.1 hpos.2 n hn₀ (G.familySetting c) hs η hin
      exact ⟨a1, a3, a4⟩)
    (fun hall η hin => hTe y b₃ R hR hx' n G hG Γ hΓ c hall η hin ν hν)
    (fun hall η hin => (hFa y b₂ R hR hx' n G hG Γ hΓ c hall).2 η hin)
    (fun η hw i => by
      have h := hA y b₁ R hR hx' n G hG (G.familyData c) (isGasFamily_familyData hΓ c) η hw i.1.1
        ((occupies_familyData_iff c).mpr ⟨i, rfl⟩)
      rwa [state_familyData] at h)
    (fun W Y ω hY => by
      by_cases h0 : R.labelWeight (n * R.params.side) W Y ω = 0
      · exact Or.inl h0
      · refine Or.inr fun X hX => ?_
        rw [hrow.2.form _ hside W Y ω hY] at h0
        exact Finset.prod_ne_zero_iff.mp (mul_ne_zero_iff.mp h0).2 X hX)
    (fun hall => (hFa y b₂ R hR hx' n G hG Γ hΓ c hall).1)
    (fun _ i => activity_nonneg hcut hrow hside _ _) (familyBadBonds_subset_bad c)
    (fun b hb hn => mem_markedBonds_of_not_mem_bad c hb hn) η
  simp only [hpt]
  have hfin : ENNReal.ofReal (R.functional (n * R.params.side) (trivialField (n * R.params.side))) *
      ENNReal.ofReal (∏ X ∈ chainComponents R.nextRange G.state.1, coarseFactor G.coarse G.state X) *
        ∏ i : Γ, G.allowedActivity i.1 (c i) ≠ ⊤ := by
    refine ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
      (ENNReal.prod_ne_top fun i _ => ?_)
    unfold GasGround.allowedActivity
    split_ifs
    · exact ENNReal.ofReal_ne_top
    · exact ENNReal.zero_ne_top
  rw [lintegral_const_mul' _ _ hfin,
    mul_assoc (ENNReal.ofReal (R.functional (n * R.params.side) (trivialField (n * R.params.side))) *
      ENNReal.ofReal (∏ X ∈ chainComponents R.nextRange G.state.1, coarseFactor G.coarse G.state X))]
  rfl
end ClusterExpansionOfAStep
end YangMills.Construction
end
