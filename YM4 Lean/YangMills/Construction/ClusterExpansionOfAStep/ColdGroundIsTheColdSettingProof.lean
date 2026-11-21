import YangMills.Construction.ClusterExpansionOfAStep.AllowedStatesReadTheirBoxProof
import YangMills.Construction.ClusterExpansionOfAStep.ColdGroundIsTheColdSetting
import YangMills.Construction.ClusterExpansionOfAStep.ZetaOfAGroundIsBorelProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages LumpContours ColdStepAtMirrorFrames
open TorusFields TorusLumps StepSettings StepGas StepCosts BlockOffsets
namespace ColdCaseGround
variable {R : StepSetup} {n : ℕ} [NeZero n]
omit [NeZero n] in
theorem chartSetting_eq_of {s s' : ChartSetting R n} (hV : s.coarse = s'.coarse)
    (hreg : s.region = s'.region) (hfine : s.fine = s'.fine)
    (hY : s.support = s'.support)
    (hω : ∀ z (h : z ∈ s.support) (h' : z ∈ s'.support), s.labelling ⟨z, h⟩ = s'.labelling ⟨z, h'⟩)
    (hb : s.bases = s'.bases) (hf : s.free = s'.free) (hd : s.bad = s'.bad) : s = s' := by
  obtain ⟨V, reg, fine, Y, ω, bases, free, bad⟩ := s
  obtain ⟨V', reg', fine', Y', ω', bases', free', bad'⟩ := s'
  change V = V' at hV
  change reg = reg' at hreg
  change fine = fine' at hfine
  change Y = Y' at hY
  change bases = bases' at hb
  change free = free' at hf
  change bad = bad' at hd
  subst hV hreg hfine hY hb hf hd
  have hω' : ω = ω' := funext fun z => hω z.1 z.2 z.2
  rw [hω']
theorem blockActivity_eq_of_field_eq (s : ChartSetting R n) (b : TorusField (n * R.params.side))
    (h : ∀ η, ({ s with fine := b } : ChartSetting R n).field η = s.field η) (lam : ℝ)
    (Y : TorusSite n) :
    ({ s with fine := b } : ChartSetting R n).blockActivity lam Y = s.blockActivity lam Y := by
  have hcost : ∀ Y η, ({ s with fine := b } : ChartSetting R n).blockCostAt Y η =
      s.blockCostAt Y η := fun Y η => by
    unfold ChartSetting.blockCostAt
    rw [h]
  have hj : ∀ Y η, ({ s with fine := b } : ChartSetting R n).logJacobianAt Y η =
      s.logJacobianAt Y η := fun Y η => by
    unfold ChartSetting.logJacobianAt
    rw [h]
    rfl
  have hphi : ∀ Y η, ({ s with fine := b } : ChartSetting R n).blockDensityAt Y η =
      s.blockDensityAt Y η := fun Y η => by
    unfold ChartSetting.blockDensityAt
    rw [h]
    rfl
  have hsum : ∀ η, ({ s with fine := b } : ChartSetting R n).totalCost η = s.totalCost η :=
    fun η => by
    unfold ChartSetting.totalCost
    exact Finset.sum_congr rfl fun Y _ => hcost Y η
  have hpsi : ∀ Y η, ({ s with fine := b } : ChartSetting R n).blockInteraction Y η =
      s.blockInteraction Y η := fun Y η => by
    unfold ChartSetting.blockInteraction
    simp only [hsum, hj]
    rfl
  have hpsum : ∀ η, ({ s with fine := b } : ChartSetting R n).totalInteraction η =
      s.totalInteraction η := fun η => by
    unfold ChartSetting.totalInteraction
    exact Finset.sum_congr rfl fun Y _ => hpsi Y η
  have htau : ∀ τ η, ({ s with fine := b } : ChartSetting R n).interpolatedDensity lam τ η =
      s.interpolatedDensity lam τ η := fun τ η => by
    unfold ChartSetting.interpolatedDensity
    rw [hpsum]
    rfl
  have hnu : ∀ ν η, ({ s with fine := b } : ChartSetting R n).perturbedDensity ν η =
      s.perturbedDensity ν η := fun ν η => by
    unfold ChartSetting.perturbedDensity
    rw [hpsum]
    simp only [hphi]
    rfl
  have hf1 : (fun η => ({ s with fine := b } : ChartSetting R n).blockInteraction Y η -
      ({ s with fine := b } : ChartSetting R n).blockGaussian lam Y η) =
      fun η => s.blockInteraction Y η - s.blockGaussian lam Y η :=
    funext fun η => by rw [hpsi]; rfl
  have hτ : ∀ τ, ({ s with fine := b } : ChartSetting R n).interpolatedDensity lam τ =
      s.interpolatedDensity lam τ := fun τ => funext (htau τ)
  have hν : ∀ ν, ({ s with fine := b } : ChartSetting R n).perturbedDensity ν =
      s.perturbedDensity ν := fun ν => funext (hnu ν)
  have hp : ({ s with fine := b } : ChartSetting R n).blockDensityAt Y = s.blockDensityAt Y :=
    funext (hphi Y)
  unfold ChartSetting.blockActivity
  rw [hcost Y 0, hj Y 0, hf1, hp]
  simp only [hτ, hν]
  rfl
theorem field_fine_field_zero (s : ChartSetting R n) (hodd : Odd R.params.side) (hn : 2 ≤ n)
    (hf : s.free ⊆ chartBonds R.params.side n) (η : FreeCoords s.free) :
    ({ s with fine := s.field 0 } : ChartSetting R n).field η = s.field η := by
  classical
  have hstored : ∀ b : TorusBond (n * R.params.side), b ∉ s.free →
      s.field 0 b.1 b.2 = s.fine b.1 b.2 := by
    intro b hb
    unfold ChartSetting.field
    rw [dif_neg hb]
  have hgauge : ∀ x, gaugeAt (R := R) (s.field 0) x = gaugeAt (R := R) s.fine x := by
    intro x
    obtain ⟨A, o, ho, hA⟩ := exists_block_offset (L := R.params.side) hodd fun i => ((x i).cast : ℤ)
    have hx : x = siteOfInt (blockPoint R.params.side A o) := by
      rw [eq_siteOfInt_cast x]
      congr 1
      funext i
      exact hA i
    rw [hx, gaugeAt_blockPoint hodd _ A o ho, gaugeAt_blockPoint hodd _ A o ho]
    have hc := (_root_.YangMills.Construction.BlockOffsets.mem_centredCube_iff o).mp ho
    have key := pathHolonomy_congr (L := R.params.side) (s.field 0) s.fine
      (fun i => (R.params.side : ℤ) * A i) (fun i => (R.params.side : ℤ) * A i) (axisPath o 1) 0 ?_
    · simpa only [add_zero] using key
    · intro b hb
      obtain ⟨g1, g2, g3⟩ := isAxialBond_of_mem_axisPath hc b hb
      have hb1 : b.1 ∈ centredCube R.params.side := (_root_.YangMills.Construction.BlockOffsets.mem_centredCube_iff _).mpr g1
      have hb2 : b.1 + Pi.single b.2 1 ∈ centredCube R.params.side := (_root_.YangMills.Construction.BlockOffsets.mem_centredCube_iff _).mpr g2
      exact hstored (siteOfInt (blockPoint R.params.side A b.1), b.2)
        (blockPoint_not_mem_free s hodd hn hf A b.1 b.2 hb1 hb2 g3)
  funext x i
  unfold ChartSetting.field
  by_cases hb : (x, i) ∈ s.free
  · rw [dif_pos hb, dif_pos (show (x, i) ∈ ({ s with fine := s.field 0 } : ChartSetting R n).free from hb)]
    show (gaugeAt (R := R) (s.field 0) x)⁻¹ * _ *
      gaugeAt (R := R) (s.field 0) (x + TorusFields.unitStep (n * R.params.side) i) = _
    rw [hgauge, hgauge]
    rfl
  · rw [dif_neg hb, dif_neg (show (x, i) ∉ ({ s with fine := s.field 0 } : ChartSetting R n).free from hb)]
    exact hstored (x, i) hb
omit [NeZero n] in
theorem markAt_emptyCoarseState (y : TorusSite n) :
    (emptyCoarseState R : CoarseState R n).markAt y = none := by
  classical
  unfold CoarseState.markAt
  exact dif_neg (Finset.notMem_empty y)
theorem not_occupies_empty (θ : GasSupport R n) : ¬ (GasFamily.empty : GasFamily R n).Occupies θ := by apply _root_.YangMills.Construction.InBoxTransfer.not_occupies_empty <;> assumption
theorem fieldAt_empty (b : TorusBond (n * R.params.side)) :
    (GasFamily.empty : GasFamily R n).fieldAt b = Sum.inl () := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.BlockActivityMeasurability.fieldAt_empty <;> assumption
theorem baseAt_empty (y : TorusSite n) : (GasFamily.empty : GasFamily R n).baseAt y = Sum.inl () := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.BlockActivityMeasurability.baseAt_empty <;> assumption
theorem sites_empty : (GasFamily.empty : GasFamily R n).sites = ∅ := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.BlockActivityMeasurability.sites_empty <;> assumption
theorem settingWithFamily_empty_coldCaseGround (V : TorusField n) :
    (coldCaseGround R V).settingWithFamily GasFamily.empty = coldChartSetting R V := by
  classical
  have hlabel : ∀ z : TorusSite (n * R.params.side),
      (emptyCoarseState R : CoarseState R n).labelAt z = Sum.inl () := by
    intro z
    unfold CoarseState.labelAt
    rw [markAt_emptyCoarseState]
  have hstate : (coldCaseGround R V).recordedSites = ∅ := by
    unfold GasGround.recordedSites
    refine Finset.filter_false_of_mem fun z _ => ?_
    show ¬ ((emptyCoarseState R : CoarseState R n).labelAt z).isRight = true
    rw [hlabel]
    simp
  have hbad : (coldCaseGround R V).recordedBad = ∅ := by
    unfold GasGround.recordedBad
    refine Finset.filter_false_of_mem fun b _ => ?_
    rintro ⟨s, h, _⟩
    have h' : (emptyCoarseState R : CoarseState R n).markAt
        (parentBlock R.params.side b.1) = some s := h
    rw [markAt_emptyCoarseState] at h'
    exact absurd h' (by simp)
  have hY : ((coldCaseGround R V).settingWithFamily GasFamily.empty).support = ∅ := by
    show (coldCaseGround R V).recordedSites ∪ GasFamily.empty.sites = ∅
    rw [hstate, sites_empty, Finset.union_empty]
  refine chartSetting_eq_of rfl rfl ?_ hY ?_ ?_ ?_ ?_
  · funext x i
    show (match (GasFamily.empty : GasFamily R n).fieldAt (x, i) with
      | Sum.inr g => g
      | Sum.inl _ => (emptyCoarseState R : CoarseState R n).fieldWithStoredLinks (trivialField _) x i) = 1
    rw [fieldAt_empty]
    show (emptyCoarseState R : CoarseState R n).fieldWithStoredLinks (trivialField _) x i = 1
    unfold CoarseState.fieldWithStoredLinks
    rw [markAt_emptyCoarseState]
    rfl
  · intro z _ h'
    exact absurd h' (Finset.notMem_empty z)
  · funext c
    show (match (GasFamily.empty : GasFamily R n).baseAt _ with
      | Sum.inr o => _
      | Sum.inl _ => (coldCaseGround R V).groundBases c) = _
    rw [baseAt_empty]
    show (coldCaseGround R V).groundBases c = _
    unfold GasGround.groundBases
    have : (coldCaseGround R V).state.markAt
        (toTorusSite (F := stepBlockFrame R.params.side n) (j := 1) n c) = none :=
      markAt_emptyCoarseState _
    rw [this]
    rfl
  · show (coldCaseGround R V).freeBonds.filter (fun b => GasFamily.empty.fieldAt b = Sum.inl ()) =
      chartBonds R.params.side n
    ext b
    simp only [GasGround.freeBonds, markedBonds, Finset.mem_filter, fieldAt_empty, and_true]
    constructor
    · rintro ⟨⟨h, _⟩, _⟩
      exact h
    · intro h
      refine ⟨⟨h, Finset.notMem_empty _⟩, ?_⟩
      rintro ⟨s, hs, _⟩
      have h' : (emptyCoarseState R : CoarseState R n).markAt
          (parentBlock R.params.side b.1) = some s := hs
      rw [markAt_emptyCoarseState] at h'
      exact absurd h' (by simp)
  · show (coldCaseGround R V).recordedBad ∪ _ ∪ _ = ∅
    rw [hbad]
    have h1 : (Finset.univ.filter fun θ => (GasFamily.empty : GasFamily R n).Occupies θ) = ∅ :=
      Finset.filter_false_of_mem fun θ _ => not_occupies_empty θ
    rw [h1, Finset.biUnion_empty, Finset.empty_union, Finset.empty_union]
    exact Finset.filter_false_of_mem fun b _ => Finset.notMem_empty _
omit [NeZero n] in
theorem fine_field_zero_congr {s s' : ChartSetting R n} (h : s = s') :
    ({ s with fine := s.field 0 } : ChartSetting R n) =
      ({ s' with fine := s'.field 0 } : ChartSetting R n) := by
  subst h
  rfl
end ColdCaseGround
open ColdCaseGround in
theorem StepGas.coldCaseGroundActivityEq_holds : StepGas.ColdCaseGroundActivityEq := by
  intro R n _ V lam Y hodd hn
  have hs : (coldCaseGround R V).groundSetting =
      ({ coldChartSetting R V with fine := (coldChartSetting R V).field 0 } : ChartSetting R n) :=
    fine_field_zero_congr (s := (coldCaseGround R V).settingWithFamily GasFamily.empty)
      (s' := coldChartSetting R V) (settingWithFamily_empty_coldCaseGround V)
  have hsub : (coldChartSetting R V).free ⊆ chartBonds R.params.side n := Finset.Subset.refl _
  have hz := blockActivity_eq_of_field_eq (coldChartSetting R V) ((coldChartSetting R V).field 0)
    (fun η => field_fine_field_zero (coldChartSetting R V) hodd hn hsub η) lam Y
  rw [← hz]
  exact congrArg (fun s : ChartSetting R n => s.blockActivity lam Y) hs
end YangMills.Construction
end
