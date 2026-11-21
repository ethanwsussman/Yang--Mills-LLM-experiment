import YangMills.Construction.Continuum.RingsRingTracesAndTheirIntegrals
import YangMills.Construction.Lattice.RingsOnThreeAndFourIndicesAndRingKernelsOfOrdersFourAndTwo
import YangMills.Construction.LinearAlgebra.FreeCurvaturePropagatorIsSymmetricEvenAndContinuous
import YangMills.Construction.SystemOfAdmissibleConstants.TheLawAtALevelProof
import YangMills.Construction.Torus.CellsOfATranslatedLatticeAndBallsOfTheTorus
import YangMills.Construction.Torus.FactsOfTheCoveringMapAndTheDistanceOfTheStandingData
import YangMills.Construction.Torus.LiftOfABallAndOfAFunction
import YangMills.Construction.Torus.TranslationsAndTwoLiftsOfATuple
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Set MeasureTheory
open YangMills.Construction.Tuples YangMills.Construction.TorusMetric
open YangMills.Construction.TestFunctions YangMills.Construction.PeriodicLattice
open YangMills.Construction.Exterior YangMills.Construction.PropagatorRings
namespace FreeRingKernels.RingIntegrals
theorem exists_eq_ringClass {m : ℕ} {J : Type*} {R : Set (Fin m → J)} (h : IsRingOfTuples R) :
    ∃ w : Fin m → J, IsBijectiveTuple w ∧ R = ringClass w := by
  obtain ⟨O, ⟨w, hw, rfl⟩, rfl⟩ := h
  exact ⟨w, hw, rfl⟩
theorem ringMembership : RingMembership := by
  intro J _ m _ _
  refine ⟨?_, ?_, ?_⟩
  · intro R hR σ hσ
    obtain ⟨w, -, rfl⟩ := exists_eq_ringClass hR
    exact ringClass_eq_of_mem hσ
  · intro R R' hR hR'
    obtain ⟨w, -, rfl⟩ := exists_eq_ringClass hR
    obtain ⟨w', -, rfl⟩ := exists_eq_ringClass hR'
    by_cases h : Disjoint (ringClass w) (ringClass w')
    · exact Or.inr h
    · obtain ⟨σ, h₁, h₂⟩ := Set.not_disjoint_iff.1 h
      exact Or.inl ((ringClass_eq_of_mem h₁).symm.trans (ringClass_eq_of_mem h₂))
  · intro R hR σ hσ σ' hσ'
    obtain ⟨w, -, rfl⟩ := exists_eq_ringClass hR
    rw [cyclicEdges_eq_of_mem_ringClass hσ, cyclicEdges_eq_of_mem_ringClass hσ']
theorem exists_zpow_finRotate_eq_add (k : ℕ) (t : ℤ) :
    ∃ a : Fin (k + 2), ∀ i, (finRotate (k + 2) ^ t) i = i + a := by
  induction t using Int.induction_on with
  | zero => exact ⟨0, fun i => by simp⟩
  | succ j ih =>
    obtain ⟨a, ha⟩ := ih
    refine ⟨a + 1, fun i => ?_⟩
    rw [zpow_add_one, Equiv.Perm.mul_apply, ha, finRotate_apply]
    abel
  | pred j ih =>
    obtain ⟨a, ha⟩ := ih
    refine ⟨a - 1, fun i => ?_⟩
    rw [zpow_sub_one, Equiv.Perm.mul_apply, ha]
    have hinv : ∀ u : Fin (k + 2), (finRotate (k + 2))⁻¹ u = u - 1 := by
      intro u
      rw [Equiv.Perm.inv_eq_iff_eq, finRotate_apply]
      abel
    rw [hinv]
    abel
theorem val_rev_add_last (k : ℕ) (i : Fin (k + 2)) :
    ((Fin.rev (i + Fin.last (k + 1)) : Fin (k + 2)) : ℕ) = (k + 2 - (i : ℕ)) % (k + 2) := by
  have hi := i.isLt
  rw [Fin.val_rev, Fin.val_add, Fin.val_last]
  rcases Nat.eq_zero_or_pos (i : ℕ) with h | h
  · rw [h, Nat.zero_add, Nat.mod_eq_of_lt (by omega), Nat.sub_zero, Nat.mod_self]
    omega
  · have e : (i : ℕ) + (k + 1) = ((i : ℕ) - 1) + (k + 2) := by omega
    rw [e, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    omega
theorem reverseTail_eq (k : ℕ) {J : Type*} (σ : Fin (k + 2) → J) :
    reverseTail σ = fun i => σ (Fin.rev (i + Fin.last (k + 1))) := by
  funext i
  simp only [reverseTail]
  congr 1
  exact Fin.ext (val_rev_add_last k i).symm
theorem reverseTail_mem_ringClass (k : ℕ) {J : Type*} (σ : Fin (k + 2) → J) :
    reverseTail σ ∈ ringClass σ := by
  rw [ringClass_eq_union]
  refine Or.inr ⟨-1, ?_⟩
  rw [reverseTail_eq]
  funext i
  simp only [rotateBy, reversed, zpow_neg, zpow_one]
  congr 2
  rw [Equiv.Perm.inv_eq_iff_eq, finRotate_apply]
  have : Fin.last (k + 1) + 1 = 0 := by simp
  rw [add_assoc, this, add_zero]
theorem fixesZero_iff (k : ℕ) (σ : Fin (k + 2) → Fin (k + 2)) :
    FixesZero σ ↔ σ 0 = 0 := by
  constructor
  · intro h
    exact Fin.ext (h 0 rfl)
  · intro h i hi
    have : i = 0 := Fin.ext hi
    rw [this, h]
    rfl
theorem ringTuplesFixingZero : RingTuplesFixingZero := by
  intro m hm R hR σ hσ hb
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
  obtain ⟨w, hw, rfl⟩ := exists_eq_ringClass hR
  have hring := ringClass_eq_of_mem hσ
  have hbij : IsBijectiveTuple σ := by
    rw [ringClass_eq_union] at hσ
    rcases hσ with ⟨t, rfl⟩ | ⟨t, rfl⟩
    · exact hw.rotateBy t
    · exact hw.reversed.rotateBy t
  rw [← hring]
  have hb0 := (fixesZero_iff k σ).1 hb
  ext σ'
  simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hmem, hb'⟩
    have hb'0 := (fixesZero_iff k σ').1 hb'
    rw [ringClass_eq_union] at hmem
    rcases hmem with ⟨t, rfl⟩ | ⟨t, rfl⟩
    · left
      obtain ⟨a, ha⟩ := exists_zpow_finRotate_eq_add k t
      have h0 : σ a = σ 0 := by
        have := hb'0
        simp only [rotateBy, ha, zero_add] at this
        rw [this, hb0]
      have ha0 : a = 0 := hbij.1 h0
      funext i
      simp only [rotateBy, ha, ha0, add_zero]
    · right
      obtain ⟨a, ha⟩ := exists_zpow_finRotate_eq_add k t
      have h0 : σ (Fin.rev a) = σ 0 := by
        have := hb'0
        simp only [rotateBy, reversed, ha, zero_add] at this
        rw [this, hb0]
      have ha0 : Fin.rev a = 0 := hbij.1 h0
      have hal : a = Fin.last (k + 1) := by
        have := congrArg Fin.val ha0
        simp only [Fin.val_rev, Fin.val_zero] at this
        have hlt := a.isLt
        exact Fin.ext (by simp only [Fin.val_last]; omega)
      rw [reverseTail_eq]
      funext i
      simp only [rotateBy, reversed, ha, hal]
  · rintro (rfl | rfl)
    · exact ⟨Or.inl (mem_rotationClass_self _), hb⟩
    · refine ⟨reverseTail_mem_ringClass k σ, (fixesZero_iff k _).2 ?_⟩
      rw [reverseTail_eq]
      have : Fin.rev ((0 : Fin (k + 2)) + Fin.last (k + 1)) = 0 := by simp
      simp only [this, hb0]
theorem cyclicEdges_four (σ : Fin 4 → Fin 4) :
    cyclicEdges σ = Set.range fun i : Fin 4 => s(σ i, σ (i + 1)) := by
  simp only [cyclicEdges, finRotate_apply]
theorem ringsOnThreeAndFour (h : RingsOfOrderThreeFourAndKernels) :
    RingsOnThreeAndFour := by
  obtain ⟨⟨h₁, h₂, h₃⟩, -⟩ := h
  refine ⟨h₁, h₂, h₃, ?_, ?_, ?_⟩ <;> rw [cyclicEdges_four] <;> refine Set.ext (Sym2.ind ?_) <;>
    simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff] <;> decide
theorem cyclicTrace_add_const {m : ℕ} (σ : Fin m → Fin m) (x : Fin m → Fin 4 → ℝ)
    (v : Fin 4 → ℝ) : cyclicTrace σ (fun i => x i + v) = cyclicTrace σ x := by
  simp only [cyclicTrace, cyclicPropagatorProduct, add_sub_add_right_eq_sub]
theorem cyclicTraceInvariance (h : CyclicTraceProperties) : CyclicTraceInvariance := by
  intro m hm σ hσ x hx
  have hnb : ∀ i, x (σ i) ≠ x (σ (finRotate m i)) := fun i => hx _ _ ⟨i, rfl⟩
  exact ⟨((h m hm σ hσ).1 x hnb).2.2, fun v => cyclicTrace_add_const σ x v⟩
def cyclicFactor {m : ℕ} (σ : Fin m → Fin m) (x : Fin m → Fin 4 → ℝ) (i : Fin m) :
    Module.End ℝ Bivector :=
  freeCurvaturePropagator (x (σ i) - x (σ (finRotate m i)))
theorem cyclicPropagatorProduct_eq_prod {m : ℕ} (σ : Fin m → Fin m) (x : Fin m → Fin 4 → ℝ) :
    cyclicPropagatorProduct σ x = (List.ofFn (cyclicFactor σ x)).prod := rfl
theorem continuous_cyclicTrace (h : FreeCurvaturePropagatorSymmEvenContinuous)
    {m : ℕ} (σ : Fin m → Fin m) (S : Set (Fin m → Fin 4 → ℝ))
    (hS : ∀ x ∈ S, ∀ i, x (σ i) ≠ x (σ (finRotate m i))) :
    Continuous fun x : S => cyclicTrace σ x := by
  classical
  let toMat := LinearMap.toMatrixAlgEquiv (R := ℝ) axisBivectorBasis.toBasis
  have hentry : ∀ (T : Module.End ℝ Bivector) (P Q : AxisPlane),
      toMat T P Q = bivectorMatrixEntry T P Q := by
    intro T P Q
    simp [toMat, bivectorMatrixEntry, LinearMap.toMatrixAlgEquiv_apply,
      OrthonormalBasis.repr_apply_apply]
  have hfac : ∀ i, Continuous fun x : S => toMat (cyclicFactor σ x i) := by
    intro i
    refine continuous_matrix fun P Q => ?_
    simp only [hentry, cyclicFactor]
    have hv : Continuous fun x : S => (x : Fin m → Fin 4 → ℝ) (σ i) -
        (x : Fin m → Fin 4 → ℝ) (σ (finRotate m i)) :=
      ((continuous_apply _).comp continuous_subtype_val).sub
        ((continuous_apply _).comp continuous_subtype_val)
    exact (h.2.2 P Q).comp_continuous hv fun x => sub_ne_zero.2 (hS x x.2 i)
  have hprod : Continuous fun x : S => toMat (cyclicPropagatorProduct σ x) := by
    have hl : ∀ x : S, toMat (cyclicPropagatorProduct σ x) =
        ((List.finRange m).map fun i => toMat (cyclicFactor σ x i)).prod := by
      intro x
      rw [cyclicPropagatorProduct_eq_prod, map_list_prod, List.ofFn_eq_map, List.map_map]
      rfl
    simp only [hl]
    exact continuous_list_prod _ fun i _ => hfac i
  have htr : ∀ x : S, cyclicTrace σ x = ∑ P, toMat (cyclicPropagatorProduct σ x) P P := by
    intro x
    simp only [cyclicTrace, bivectorTrace, hentry]
  simp only [htr]
  refine continuous_finsetSum _ fun P _ => ?_
  exact (continuous_apply P).comp ((continuous_apply P).comp hprod)
theorem ne_apply_finRotate {m : ℕ} (hm : 2 ≤ m) {σ : Fin m → Fin m} (hσ : IsBijectiveTuple σ)
    (i : Fin m) : σ i ≠ σ (finRotate m i) := by
  intro e
  have hi := hσ.1 e
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
  rw [finRotate_apply] at hi
  have h10 : (1 : Fin (k + 2)) = 0 :=
    add_left_cancel (a := i) (by rw [add_zero]; exact hi.symm)
  exact one_ne_zero h10
theorem cyclicTraceOnSupportBox (hT : CyclicTraceProperties)
    (hK : FreeCurvaturePropagatorSymmEvenContinuous) : CyclicTraceOnSupportBox := by
  intro m hm σ hσ f hf
  have hI := (hT m hm σ hσ).2 f hf
  have hdisj : Pairwise fun i j => Disjoint (tsupport (f i)) (tsupport (f j)) := hf.2.2.2
  have hS : IsCompact (supportBox f) := hI.2.1
  have hne : ∀ x ∈ supportBox f, ∀ i j, i ≠ j → x i ≠ x j := by
    intro x hx i j hij e
    exact Set.disjoint_left.1 (hdisj hij) (hx i (Set.mem_univ _)) (e ▸ hx j (Set.mem_univ _))
  have hedge : ∀ x ∈ supportBox f, DistinctOnEdges σ x := by
    intro x hx i j he
    obtain ⟨a, ha⟩ := he
    rcases Sym2.eq_iff.1 ha with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hne x hx _ _ (ne_apply_finRotate hm hσ a)
    · exact hne x hx _ _ (ne_apply_finRotate hm hσ a).symm
  have hnb : ∀ x ∈ supportBox f, ∀ i, x (σ i) ≠ x (σ (finRotate m i)) :=
    fun x hx i => hne x hx _ _ (ne_apply_finRotate hm hσ i)
  have hcontOn : ContinuousOn (cyclicTrace σ) (supportBox f) :=
    continuousOn_iff_continuous_domRestrict.2 (continuous_cyclicTrace hK σ _ hnb)
  obtain ⟨C, hC⟩ := hS.exists_bound_of_continuousOn hcontOn
  refine ⟨hS, hedge, hcontOn, ⟨C, fun x hx => by simpa using hC x hx⟩, ?_⟩
  rw [weightedOnSupports_cyclicTrace]
  exact hI.2.2.2.2
theorem isCompact_closedBallR4 (c : Fin 4 → ℝ) (r : ℝ) : IsCompact (closedBallR4 c r) := by apply _root_.YangMills.SharedProofs.p20989 <;> assumption
theorem isCompact_image_of_continuous {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} {A : Set X} (hA : IsCompact A) (hf : Continuous f) : IsCompact (f '' A) :=
  hA.image hf
theorem ballLiftIsometric (hB : BallLift.BallAndFunctionLift)
    (hCells : TorusMeasure.TranslatedLatticeCells.CellsAndBallsStatement)
    (hF : Conventions.StandingParameters.CoveringAndDistanceFacts)
    (s : Conventions.StandingParameters) : BallLiftIsometric s := by
  intro z r c hr hc
  obtain ⟨⟨iso, bij⟩, -⟩ := hB s z r c hr hc
  have hcont : @Continuous _ _ _ (metricTopology s.L s.m) (torusProj (torusSide s.L s.m)) :=
    (hF s).2.2.2.2.2.2.2.1
  have hcpt : @IsCompact _ (metricTopology s.L s.m) (closedBallTorus z r) := by
    rw [← bij.image_eq]
    exact @isCompact_image_of_continuous (Fin 4 → ℝ) s.Torus _ (metricTopology s.L s.m) _ _
      (isCompact_closedBallR4 c r) hcont
  exact ⟨bij, iso, hcpt, ((hCells s).2.1 z r hr.1).2.2.1⟩
theorem liftSupport (hB : BallLift.BallAndFunctionLift)
    (s : Conventions.StandingParameters) : LiftSupport s := by
  intro z r c f g hl
  obtain ⟨⟨-, bij⟩, hf, -⟩ := hB s z r c hl.1 hl.2.1
  obtain ⟨-, hsb, hcpt, hball, -⟩ := hf f g hl
  refine ⟨Set.Subset.antisymm (fun y hy => ⟨hball hy, hsb.mapsTo hy⟩) ?_, hcpt⟩
  rintro y ⟨hy, hyf⟩
  obtain ⟨y', hy', e⟩ := hsb.surjOn (Set.mem_preimage.1 hyf)
  have hyy : y' = y := bij.injOn (hball hy') hy e
  exact hyy ▸ hy'
theorem weightedOnSupports_eq {m : ℕ} (f : Fin m → (Fin 4 → ℝ) → ℝ)
    (k : (Fin m → Fin 4 → ℝ) → ℝ) :
    weightedOnSupports f k = fun x => (∏ j, f j (x j)) * k x := by
  funext x
  by_cases hx : x ∈ supportBox f
  · rw [weightedOnSupports, Set.indicator_of_mem hx]
  · have hex : ∃ j, x j ∉ tsupport (f j) := by
      by_contra hcon
      push Not at hcon
      exact hx (Set.mem_univ_pi.2 hcon)
    obtain ⟨j, hj⟩ := hex
    have h0 : f j (x j) = 0 := image_eq_zero_of_notMem_tsupport hj
    have hp : ∏ j, f j (x j) = 0 := Finset.prod_eq_zero (Finset.mem_univ j) h0
    rw [weightedOnSupports, Set.indicator_of_notMem hx, hp, zero_mul]
theorem integral_comp_sub_cyclicTrace {m : ℕ} (σ : Fin m → Fin m)
    (g : Fin m → (Fin 4 → ℝ) → ℝ) (v : Fin 4 → ℝ) :
    ∫ x : Fin m → Fin 4 → ℝ, (∏ j, g j (x j - v)) * cyclicTrace σ x =
      ∫ x : Fin m → Fin 4 → ℝ, (∏ j, g j (x j)) * cyclicTrace σ x := by
  rw [← integral_add_right_eq_self
    (fun x : Fin m → Fin 4 → ℝ => (∏ j, g j (x j - v)) * cyclicTrace σ x) (fun _ => v)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  have h := cyclicTrace_add_const σ x v
  simp only [Pi.add_apply, add_sub_cancel_right]
  exact congrArg _ h
theorem liftsOfFamilyAgree (hLF : TranslationInvariance.Statement)
    (s : Conventions.StandingParameters) : LiftsOfFamilyAgree s := by
  intro m hm f z z' r r' hz hz' c hc c' hc'
  obtain ⟨k, hk⟩ := hLF.2.1 s m (by omega) f z z' r r' hz hz' c hc c' hc'
  refine ⟨⟨k, hk⟩, fun hb hd => ?_⟩
  have hT : IsTorusKernelFamily f := ⟨hb, hd, z, r, hz⟩
  have hg : IsTupleLift f (fun i => ballIndicatorLift c r (f i)) :=
    ⟨z, r, hz, c, hc, fun _ => rfl⟩
  have hg' : IsTupleLift f (fun i => ballIndicatorLift c' r' (f i)) :=
    ⟨z', r', hz', c', hc', fun _ => rfl⟩
  have hK := (hLF.2.2.1 s m hm f hT).1
  refine ⟨hK _ hg, hK _ hg', fun σ _ => ?_⟩
  rw [weightedOnSupports_eq, weightedOnSupports_eq]
  have hv : ∀ i y, ballIndicatorLift c' r' (f i) y =
      ballIndicatorLift c r (f i) (y - fun α => torusSide s.L s.m * (k α : ℝ)) :=
    fun i y => congrFun (hk i) y
  simp only [hv]
  exact integral_comp_sub_cyclicTrace σ (fun j => ballIndicatorLift c r (f j)) _
theorem toLevelUnits_self (L K : ℕ) (r : ℝ) : toLevelUnits L K K r = r := by
  simp [toLevelUnits, levelDepth]
theorem norm_le_torusEuclidNorm {S : ℝ} (x : Torus4 S) : ‖x‖ ≤ torusEuclidNorm x := by apply _root_.YangMills.Construction.TorusAnalysis.pi_norm_le_torusEuclidNorm <;> assumption
theorem isClosedMap_of_continuous {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [CompactSpace X] [T2Space Y] {f : X → Y} (hf : Continuous f) : IsClosedMap f :=
  hf.isClosedMap
theorem metricTopology_eq (hF : Conventions.StandingParameters.CoveringAndDistanceFacts)
    (s : Conventions.StandingParameters) :
    (inferInstance : TopologicalSpace s.Torus) = metricTopology s.L s.m := by
  have hopen : ∀ O : Set s.Torus, IsOpen O → IsMetricOpen O := by
    intro O hO y hy
    obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.1 hO y hy
    refine ⟨r, hr, fun y' hy' => hsub ?_⟩
    rw [Metric.mem_ball, dist_eq_norm]
    exact (norm_le_torusEuclidNorm _).trans_lt hy'
  have hcont : @Continuous _ _ (metricTopology s.L s.m) _ (id : s.Torus → s.Torus) := by
    refine (@continuous_def _ _ (metricTopology s.L s.m) _ _).2 fun O hO => ?_
    rw [Set.preimage_id]
    exact hopen O hO
  have hcl : @IsClosedMap _ _ (metricTopology s.L s.m) _ (id : s.Torus → s.Torus) :=
    @isClosedMap_of_continuous s.Torus s.Torus (metricTopology s.L s.m) _
      (hF s).2.2.2.2.2.2.2.2 _ _ hcont
  refine TopologicalSpace.ext ?_
  funext O
  refine propext ⟨hopen O, fun hO => ?_⟩
  have hc : @IsClosed _ (metricTopology s.L s.m) Oᶜ :=
    (@isClosed_compl_iff _ (metricTopology s.L s.m) O).2 hO
  have hcc := hcl Oᶜ hc
  rw [Set.image_id] at hcc
  exact isClosed_compl_iff.1 hcc
theorem torusConventionsAgree (hF : Conventions.StandingParameters.CoveringAndDistanceFacts)
    (s : Conventions.StandingParameters) : TorusConventionsAgree s := by
  refine ⟨rfl, fun u t => ?_, fun _ _ => rfl, rfl, fun f => ?_, fun _ => rfl⟩
  · constructor
    · rintro ⟨v, hv, ht⟩
      show torusProj (torusSide s.L s.m) t = u
      funext μ
      show ((t μ : ℝ) : AddCircle (torusSide s.L s.m)) = u μ
      rw [ht μ, toLevelUnits_self]
      exact hv μ
    · intro h
      have h' : torusProj (torusSide s.L s.m) t = u := h
      exact ⟨t, fun μ => congrFun h' μ, fun μ => (toLevelUnits_self _ _ _).symm⟩
  · exact congrArg (fun τ : TopologicalSpace s.Torus => @closure _ τ (Function.support f))
      (metricTopology_eq hF s)
theorem ln (hT : CyclicTraceProperties)
    (hC : RingsOfOrderThreeFourAndKernels)
    (hLF : TranslationInvariance.Statement)
    (hB : BallLift.BallAndFunctionLift)
    (hCells : TorusMeasure.TranslatedLatticeCells.CellsAndBallsStatement)
    (hF : Conventions.StandingParameters.CoveringAndDistanceFacts)
    (hK : FreeCurvaturePropagatorSymmEvenContinuous) : Statement :=
  ⟨ringMembership, ringTuplesFixingZero, ringsOnThreeAndFour hC,
    cyclicTraceInvariance hT, cyclicTraceOnSupportBox hT hK, fun s =>
      ⟨ballLiftIsometric hB hCells hF s, liftSupport hB s, liftsOfFamilyAgree hLF s,
        torusConventionsAgree hF s⟩⟩
end FreeRingKernels.RingIntegrals
end YangMills.Construction
end
