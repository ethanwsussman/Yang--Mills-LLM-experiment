import YangMills.Construction.ChessboardTori.ObservablesMeasurableInASetAndTheirRestrictionToATorusProof
import YangMills.Construction.InfiniteLattice.CountableProductsOfCopiesOfTheGroup
import YangMills.Construction.Matrices.HaarExpChartDensity
import Mathlib
set_option autoImplicit false
open MeasureTheory Set Filter
open scoped Topology Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.InfiniteLattice.CountableProduct
open YangMills.Construction.Matrices
theorem groupDist_nonneg (g h : ComplexMatrix2.specialUnitary) : 0 ≤ groupDist g h := norm_nonneg _
theorem groupDist_comm (g h : ComplexMatrix2.specialUnitary) : groupDist g h = groupDist h g :=
  norm_sub_rev _ _
theorem groupDist_triangle (g h k : ComplexMatrix2.specialUnitary) :
    groupDist g k ≤ groupDist g h + groupDist h k :=
  norm_sub_le_norm_sub_add_norm_sub _ _ _
theorem groupDist_self (g : ComplexMatrix2.specialUnitary) : groupDist g g = 0 := by
  simp [groupDist]
theorem eq_of_groupDist_eq_zero {g h : ComplexMatrix2.specialUnitary} (hz : groupDist g h = 0) :
    g = h :=
  Subtype.ext (sub_eq_zero.1 (norm_eq_zero.1 hz))
theorem groupDist_le_two (g h : ComplexMatrix2.specialUnitary) : groupDist g h ≤ 2 := by
  have hnorm : ∀ u : ComplexMatrix2.specialUnitary, ‖(u : ComplexMatrix2)‖ = 1 := fun u =>
    CStarRing.norm_of_mem_unitary (Matrix.specialUnitaryGroup_le_unitaryGroup u.2)
  calc groupDist g h = ‖(g : ComplexMatrix2) - (h : ComplexMatrix2)‖ := rfl
    _ ≤ ‖(g : ComplexMatrix2)‖ + ‖(h : ComplexMatrix2)‖ := norm_sub_le _ _
    _ = 2 := by rw [hnorm, hnorm]; norm_num
section Series
variable {J : Type} {D : Set ℕ}
theorem enumDistTerm_eq (j : D → J) (g h : LinkVariables J) (n : D) :
    enumDistTerm j g h n = ((1 : ℝ) / 2) ^ (n : ℕ) * groupDist (g (j n)) (h (j n)) := by
  rw [enumDistTerm, zpow_neg, zpow_natCast, one_div, inv_pow]
theorem enumDistTerm_nonneg (j : D → J) (g h : LinkVariables J) (n : D) :
    0 ≤ enumDistTerm j g h n := by
  rw [enumDistTerm_eq]
  exact mul_nonneg (by positivity) (groupDist_nonneg _ _)
theorem enumDistTerm_le (j : D → J) (g h : LinkVariables J) (n : D) :
    enumDistTerm j g h n ≤ 2 * ((1 : ℝ) / 2) ^ (n : ℕ) := by
  rw [enumDistTerm_eq, mul_comm]
  exact mul_le_mul_of_nonneg_right (groupDist_le_two _ _) (by positivity)
theorem summable_two_mul_half_pow : Summable fun n : ℕ => 2 * ((1 : ℝ) / 2) ^ n :=
  summable_geometric_two.mul_left 2
theorem summable_enumDistTerm (j : D → J) (g h : LinkVariables J) :
    Summable (enumDistTerm j g h) :=
  Summable.of_nonneg_of_le (enumDistTerm_nonneg j g h) (enumDistTerm_le j g h)
    (summable_two_mul_half_pow.subtype D)
theorem enumDistTerm_le_enumDist (j : D → J) (g h : LinkVariables J) (n : D) :
    enumDistTerm j g h n ≤ enumDist j g h :=
  (summable_enumDistTerm j g h).le_tsum n fun m _ => enumDistTerm_nonneg j g h m
theorem enumDist_le_tsum_of_le (j : D → J) (g h : LinkVariables J) {c : ℕ → ℝ} (hc : Summable c)
    (hc₀ : ∀ n, 0 ≤ c n) (hle : ∀ n : D, enumDistTerm j g h n ≤ c n) :
    enumDist j g h ≤ ∑' n, c n :=
  ((summable_enumDistTerm j g h).tsum_le_tsum hle (hc.subtype D)).trans
    (hc.tsum_subtype_le c D hc₀)
def geomTail (n₀ n : ℕ) : ℝ := if n₀ < n then 2 * ((1 : ℝ) / 2) ^ n else 0
theorem geomTail_nonneg (n₀ n : ℕ) : 0 ≤ geomTail n₀ n := by
  unfold geomTail
  split_ifs <;> positivity
theorem summable_geomTail (n₀ : ℕ) : Summable (geomTail n₀) := by
  refine Summable.of_nonneg_of_le (geomTail_nonneg n₀) (fun n => ?_) summable_two_mul_half_pow
  unfold geomTail
  split_ifs
  · exact le_rfl
  · positivity
theorem tsum_geomTail (n₀ : ℕ) : ∑' n, geomTail n₀ n = (2 : ℝ) ^ (1 - (n₀ : ℤ)) := by
  have hsplit := (summable_geomTail n₀).sum_add_tsum_nat_add (n₀ + 1)
  have hinit : ∑ i ∈ Finset.range (n₀ + 1), geomTail n₀ i = 0 := by
    refine Finset.sum_eq_zero fun i hi => ?_
    have : ¬ n₀ < i := by
      have := Finset.mem_range.1 hi
      omega
    simp [geomTail, this]
  have hshift : ∀ i, geomTail n₀ (i + (n₀ + 1)) = ((1 : ℝ) / 2) ^ n₀ * ((1 : ℝ) / 2) ^ i := by
    intro i
    have : n₀ < i + (n₀ + 1) := by omega
    simp only [geomTail, this, if_true]
    rw [pow_add, pow_add]
    ring
  rw [← hsplit, hinit, zero_add, tsum_congr hshift, tsum_mul_left, tsum_geometric_two,
    zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_one, zpow_natCast, one_div, inv_pow]
  field_simp
theorem enumDist_le_of_eq_initial (j : D → J) (n₀ : ℕ) (g h : LinkVariables J)
    (heq : ∀ n : D, (n : ℕ) ≤ n₀ → g (j n) = h (j n)) :
    enumDist j g h ≤ (2 : ℝ) ^ (1 - (n₀ : ℤ)) := by
  rw [← tsum_geomTail]
  refine enumDist_le_tsum_of_le j g h (summable_geomTail n₀) (geomTail_nonneg n₀) fun n => ?_
  by_cases hn : (n : ℕ) ≤ n₀
  · rw [enumDistTerm_eq, heq n hn, groupDist_self, mul_zero]
    exact geomTail_nonneg _ _
  · have : n₀ < (n : ℕ) := not_le.1 hn
    simpa [geomTail, this] using enumDistTerm_le j g h n
theorem enumDist_nonneg (j : D → J) (g h : LinkVariables J) : 0 ≤ enumDist j g h :=
  tsum_nonneg (enumDistTerm_nonneg j g h)
theorem enumDist_comm (j : D → J) (g h : LinkVariables J) :
    enumDist j g h = enumDist j h g := by
  refine tsum_congr fun n => ?_
  rw [enumDistTerm_eq, enumDistTerm_eq, groupDist_comm]
theorem enumDist_triangle (j : D → J) (g h k : LinkVariables J) :
    enumDist j g k ≤ enumDist j g h + enumDist j h k := by
  unfold enumDist
  rw [← (summable_enumDistTerm j g h).tsum_add (summable_enumDistTerm j h k)]
  refine (summable_enumDistTerm j g k).tsum_le_tsum (fun n => ?_)
    ((summable_enumDistTerm j g h).add (summable_enumDistTerm j h k))
  simp only [enumDistTerm_eq]
  rw [← mul_add]
  exact mul_le_mul_of_nonneg_left (groupDist_triangle _ _ _) (by positivity)
theorem enumDist_eq_zero_iff (j : D ≃ J) (g h : LinkVariables J) :
    enumDist j g h = 0 ↔ g = h := by
  constructor
  · intro hz
    funext i
    have hle := enumDistTerm_le_enumDist j g h (j.symm i)
    rw [hz, enumDistTerm_eq, Equiv.apply_symm_apply] at hle
    have hpos : (0 : ℝ) < ((1 : ℝ) / 2) ^ ((j.symm i : D) : ℕ) := by positivity
    have hzero : groupDist (g i) (h i) = 0 :=
      le_antisymm (nonpos_of_mul_nonpos_right hle hpos) (groupDist_nonneg _ _)
    exact eq_of_groupDist_eq_zero hzero
  · rintro rfl
    refine (tsum_congr fun n => ?_).trans tsum_zero
    rw [enumDistTerm_eq, groupDist_self, mul_zero]
theorem nhds_hasBasis_enumDist (j : D ≃ J) (x : LinkVariables J) :
    (𝓝 x).HasBasis (fun ε : ℝ => 0 < ε) fun ε => {y | enumDist j x y < ε} := by
  refine Filter.hasBasis_iff.2 fun t => ⟨fun ht => ?_, ?_⟩
  · rw [nhds_pi, Filter.mem_pi] at ht
    obtain ⟨I, hI, s, hs, hsub⟩ := ht
    have hsmall : ∀ i, ∃ e : ℝ, 0 < e ∧ {h | groupDist (x i) h < e} ⊆ s i := fun i =>
      (nhds_basis_groupDist (x i)).mem_iff.1 (hs i)
    choose e he hes using hsmall
    have hweight : ∀ i, (0 : ℝ) < ((1 : ℝ) / 2) ^ ((j.symm i : D) : ℕ) := fun i => by positivity
    have hbelow : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ i ∈ I, ε < ((1 : ℝ) / 2) ^ ((j.symm i : D) : ℕ) * e i :=
      (Filter.eventually_all_finite hI).2 fun i _ =>
        eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds (mul_pos (hweight i) (he i)))
    have hpos : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε := self_mem_nhdsWithin
    obtain ⟨ε, hε, hlt⟩ := (hpos.and hbelow).exists
    refine ⟨ε, hε, fun y hy => hsub fun i hi => hes i ?_⟩
    have hle := enumDistTerm_le_enumDist j x y (j.symm i)
    rw [enumDistTerm_eq, Equiv.apply_symm_apply] at hle
    exact lt_of_mul_lt_mul_left (hle.trans_lt (lt_trans hy (hlt i hi))) (hweight i).le
  · rintro ⟨ε, hε, hsub⟩
    refine mem_of_superset ?_ hsub
    obtain ⟨n₀, hn₀⟩ := exists_pow_lt_of_lt_one (show 0 < ε / 4 by positivity)
      (show (1 : ℝ) / 2 < 1 by norm_num)
    have hfin : {n : D | (n : ℕ) ≤ n₀}.Finite :=
      (Set.finite_Iic n₀).preimage Subtype.val_injective.injOn
    have hnear : ∀ᶠ y : LinkVariables J in 𝓝 x, ∀ n ∈ {n : D | (n : ℕ) ≤ n₀},
        groupDist (x (j n)) (y (j n)) < ε / 4 :=
      (Filter.eventually_all_finite hfin).2 fun n _ =>
        ((continuous_apply (j n)).tendsto x).eventually
          ((nhds_basis_groupDist (x (j n))).mem_of_mem (by positivity))
    filter_upwards [hnear] with y hy
    have hsc : Summable fun n : ℕ => ε / 4 * ((1 : ℝ) / 2) ^ n := summable_geometric_two.mul_left _
    have hbound := enumDist_le_tsum_of_le j x y (hsc.add (summable_geomTail n₀))
      (fun n => add_nonneg (by positivity) (geomTail_nonneg n₀ n)) fun n => ?_
    · rw [hsc.tsum_add (summable_geomTail n₀), tsum_mul_left, tsum_geometric_two,
        tsum_geomTail] at hbound
      have htwo : (2 : ℝ) ^ (1 - (n₀ : ℤ)) = 2 * ((1 : ℝ) / 2) ^ n₀ := by
        rw [zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_one, zpow_natCast, one_div, inv_pow]
        rfl
      rw [htwo] at hbound
      show enumDist j x y < ε
      linarith
    · by_cases hn : (n : ℕ) ≤ n₀
      · have h1 := (hy n hn).le
        have h2 := geomTail_nonneg n₀ (n : ℕ)
        have h3 : ((1 : ℝ) / 2) ^ (n : ℕ) * groupDist (x (j n)) (y (j n)) ≤
            ((1 : ℝ) / 2) ^ (n : ℕ) * (ε / 4) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
        rw [enumDistTerm_eq]
        linarith
      · have h1 := enumDistTerm_le j x y n
        have h2 : geomTail n₀ (n : ℕ) = 2 * ((1 : ℝ) / 2) ^ (n : ℕ) := by
          simp [geomTail, not_le.1 hn]
        have h3 : 0 ≤ ε / 4 * ((1 : ℝ) / 2) ^ (n : ℕ) := by positivity
        linarith
end Series
instance instSecondCountableSpecialUnitary :
    SecondCountableTopology ComplexMatrix2.specialUnitary := by
  have : SecondCountableTopology ComplexMatrix2 :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → ℂ))
  exact TopologicalSpace.Subtype.secondCountableTopology _
theorem compactMetrizableWithEnumDist (J : Type) [Countable J] :
    CompactMetrizableWithEnumDist J := by
  refine ⟨⟨inferInstance, inferInstance⟩, fun D j _ _ => ⟨summable_enumDistTerm j, ⟨enumDist_nonneg j,
    enumDist_eq_zero_iff j, enumDist_comm j, enumDist_triangle j, nhds_hasBasis_enumDist j⟩, ?_⟩⟩
  exact fun n₀ g h heq => enumDist_le_of_eq_initial j n₀ g h heq
theorem borel_eq_pi (J : Type) [Countable J] : borel (LinkVariables J) = MeasurableSpace.pi := by apply _root_.YangMills.Construction.ChessboardTori.MeasurableObservables.borel_linkVariables <;> assumption
theorem cylinderBoxes_isInterClosed (J : Type) : IsInterClosed (cylinderBoxes J) := by
  classical
  rintro _ ⟨J', E, hJ', hE, rfl⟩ _ ⟨J'', E', hJ'', hE', rfl⟩
  refine ⟨J' ∪ J'', fun j => (if j ∈ J' then E j else univ) ∩ (if j ∈ J'' then E' j else univ),
    hJ'.union hJ'', fun j _ => ?_, ?_⟩
  · refine MeasurableSet.inter ?_ ?_
    · split_ifs with h
      exacts [hE j h, MeasurableSet.univ]
    · split_ifs with h
      exacts [hE' j h, MeasurableSet.univ]
  · ext g
    simp only [mem_inter_iff, mem_ofPred_eq, mem_union]
    constructor
    · rintro ⟨h₁, h₂⟩ j _
      refine ⟨?_, ?_⟩
      · split_ifs with h
        exacts [h₁ j h, mem_univ _]
      · split_ifs with h
        exacts [h₂ j h, mem_univ _]
    · intro h
      refine ⟨fun j hj => ?_, fun j hj => ?_⟩
      · simpa [hj] using (h j (Or.inl hj)).1
      · simpa [hj] using (h j (Or.inr hj)).2
theorem coord_preimage_mem_cylinderBoxes {J : Type} (j : J) {E : Set ComplexMatrix2.specialUnitary}
    (hE : MeasurableSet E) : {g : LinkVariables J | g j ∈ E} ∈ cylinderBoxes J := by
  refine ⟨{j}, fun _ => E, finite_singleton j, fun _ _ => hE, ?_⟩
  ext g
  simp
theorem borel_eq_generateFrom_cylinderBoxes (J : Type) [Countable J] :
    borel (LinkVariables J) = MeasurableSpace.generateFrom (cylinderBoxes J) := by
  rw [borel_eq_pi]
  refine le_antisymm ?_ ?_
  · refine iSup_le fun j => ?_
    rintro _ ⟨E, hE, rfl⟩
    exact MeasurableSpace.measurableSet_generateFrom (coord_preimage_mem_cylinderBoxes j hE)
  · refine MeasurableSpace.generateFrom_le ?_
    rintro _ ⟨J', E, hJ', hE, rfl⟩
    have : {g : LinkVariables J | ∀ j ∈ J', g j ∈ E j} = ⋂ j ∈ J', {g | g j ∈ E j} := by
      ext g
      simp
    rw [this]
    exact hJ'.measurableSet_biInter fun j hj => measurable_pi_apply j (hE j hj)
theorem borelGeneratedByCoordinates (J : Type) [Countable J] : BorelGeneratedByCoordinates J :=
  ⟨⟨cylinderBoxes_isInterClosed J, ⟨∅, fun _ => univ, finite_empty, by simp, by simp⟩,
    borel_eq_generateFrom_cylinderBoxes J⟩, borel_eq_pi J⟩
theorem continuous_restrictTo {J : Type} (J' : Set J) :
    Continuous (restrictFamily J' : LinkVariables J → LinkVariables J') :=
  continuous_pi fun j => continuous_apply (j : J)
theorem splitsAlongPartition {J : Type} [Countable J] (J₁ J₂ : Set J) (hd : Disjoint J₁ J₂)
    (hu : J₁ ∪ J₂ = univ) : SplitsAlongPartition J₁ J₂ := by
  classical
  have hmem : ∀ j, j ∈ J₁ ∨ j ∈ J₂ := fun j => by
    have : j ∈ J₁ ∪ J₂ := hu ▸ mem_univ j
    exact this
  refine ⟨?_, ⟨?_, ?_, ?_⟩, ?_⟩
  · refine isHomeomorph_iff_continuous_bijective.2
      ⟨(continuous_restrictTo J₁).prodMk (continuous_restrictTo J₂), ?_, ?_⟩
    · intro g h he
      funext j
      rcases hmem j with hj | hj
      · exact congrFun (congrArg Prod.fst he) ⟨j, hj⟩
      · exact congrFun (congrArg Prod.snd he) ⟨j, hj⟩
    · rintro ⟨a, b⟩
      refine ⟨fun j => if h : j ∈ J₁ then a ⟨j, h⟩ else
        if h' : j ∈ J₂ then b ⟨j, h'⟩ else 1, Prod.ext ?_ ?_⟩
      · funext j
        simp [restrictFamily, j.2]
      · funext j
        have : (j : J) ∉ J₁ := fun h => disjoint_left.1 hd h j.2
        simp [restrictFamily, this, j.2]
  · rintro _ ⟨B₁, B₂, h₁, h₂, rfl⟩ _ ⟨B₁', B₂', h₁', h₂', rfl⟩
    refine ⟨B₁ ∩ B₁', B₂ ∩ B₂', ?_, ?_, ?_⟩
    · exact @MeasurableSet.inter _ (borel _) _ _ h₁ h₁'
    · exact @MeasurableSet.inter _ (borel _) _ _ h₂ h₂'
    · ext g
      simp only [mem_inter_iff, mem_ofPred_eq]
      tauto
  · exact ⟨univ, univ, @MeasurableSet.univ _ (borel _), @MeasurableSet.univ _ (borel _), by simp⟩
  · refine le_antisymm ?_ ?_
    · rw [borel_eq_pi]
      refine iSup_le fun j => ?_
      rintro _ ⟨E, hE, rfl⟩
      refine MeasurableSpace.measurableSet_generateFrom ?_
      rcases hmem j with h | h
      · refine ⟨{g | g ⟨j, h⟩ ∈ E}, univ, ?_, @MeasurableSet.univ _ (borel _), ?_⟩
        · rw [borel_eq_pi]
          exact measurable_pi_apply _ hE
        · ext g
          simp [restrictFamily]
      · refine ⟨univ, {g | g ⟨j, h⟩ ∈ E}, @MeasurableSet.univ _ (borel _), ?_, ?_⟩
        · rw [borel_eq_pi]
          exact measurable_pi_apply _ hE
        · ext g
          simp [restrictFamily]
    · rw [borel_eq_pi]
      refine MeasurableSpace.generateFrom_le ?_
      rintro _ ⟨B₁, B₂, h₁, h₂, rfl⟩
      rw [borel_eq_pi] at h₁ h₂
      have hm : ∀ J' : Set J,
          Measurable (restrictFamily J' : LinkVariables J → LinkVariables J') := fun J' =>
        measurable_pi_lambda _ fun j => measurable_pi_apply (j : J)
      exact (hm J₁ h₁).inter (hm J₂ h₂)
  · have hp := (Prod.borelSpace (α := LinkVariables J₁) (β := LinkVariables J₂)).measurable_eq
    rw [borel_eq_pi, borel_eq_pi, ← hp]
    rfl
theorem continuousApproxByCylinderFunctions (J : Type) : ContinuousApproxByCylinderFunctions J := by
  classical
  intro F hF ε hε
  have hnearby : ∀ g : LinkVariables J, ∃ I : Set J, I.Finite ∧
      ∃ s : J → Set ComplexMatrix2.specialUnitary,
      (∀ j, s j ∈ 𝓝 (g j)) ∧ I.pi s ⊆ {h | ‖F h - F g‖ < ε / 2} := fun g => by
    have hball : {h | ‖F h - F g‖ < ε / 2} ∈ 𝓝 g := by
      have := (hF.tendsto g) (Metric.ball_mem_nhds (F g) (half_pos hε))
      simpa [Metric.ball, dist_eq_norm] using this
    rw [nhds_pi, Filter.mem_pi] at hball
    obtain ⟨I, hI, s, hs, hsub⟩ := hball
    exact ⟨I, hI, s, hs, hsub⟩
  choose I hI s hs hsub using hnearby
  obtain ⟨t, -, hcover⟩ := isCompact_univ.elim_nhds_subcover (fun g => (I g).pi (s g))
    fun g _ => set_pi_mem_nhds (hI g) fun j _ => hs g j
  obtain ⟨K, hK, hIK⟩ : ∃ K : Set J, K.Finite ∧ ∀ g ∈ t, I g ⊆ K :=
    ⟨⋃ g ∈ t, I g, t.finite_toSet.biUnion fun g _ => hI g, fun g hg =>
      subset_biUnion_of_mem (u := I) (Finset.mem_coe.2 hg)⟩
  let c : LinkVariables J → LinkVariables J := fun g j => if j ∈ K then g j else 1
  have hc : Continuous c := continuous_pi fun j => by
    by_cases h : j ∈ K
    · have he : (fun g => c g j) = fun g => g j := by
        funext g
        simp [c, h]
      rw [he]
      exact continuous_apply j
    · have he : (fun g => c g j) = fun _ => 1 := by
        funext g
        simp [c, h]
      rw [he]
      exact continuous_const
  refine ⟨K, hK, F ∘ c, hF.comp hc, fun g h he => ?_, ?_⟩
  · have : c g = c h := by
      funext j
      by_cases hj : j ∈ K
      · have := congrFun he ⟨j, hj⟩
        simpa [c, hj, restrictFamily] using this
      · simp only [c, if_neg hj]
    simp [this]
  · have : Nonempty (LinkVariables J) := ⟨fun _ => 1⟩
    refine ciSup_le fun g => ?_
    obtain ⟨g', hg', hin⟩ := mem_iUnion₂.1 (hcover (mem_univ g))
    have hcg : c g ∈ (I g').pi (s g') := fun i hi => by
      have hi' : i ∈ K := hIK g' hg' hi
      simpa [c, hi'] using hin i hi
    have h₁ : ‖F g - F g'‖ < ε / 2 := hsub g' hin
    have h₂ : ‖F (c g) - F g'‖ < ε / 2 := hsub g' hcg
    have h₃ := norm_sub_le_norm_sub_add_norm_sub (F g) (F g') (F (c g))
    rw [norm_sub_rev (F g') (F (c g))] at h₃
    simp only [Pi.sub_apply, Function.comp_apply]
    linarith
theorem haarInvariantUnderReindexInvert
    (hinv : Measure.map (fun U : ComplexMatrix2.specialUnitary => U⁻¹) ComplexMatrix2.haarProb =
      ComplexMatrix2.haarProb) (J : Type) [Finite J] : HaarInvariantUnderReindexInvert J := by
  classical
  have : Fintype J := Fintype.ofFinite J
  refine ⟨⟨inferInstance, ?_⟩, fun J₀ _ ρ M => ?_⟩
  · show IsProbabilityMeasure (Measure.infinitePi fun _ : J => ComplexMatrix2.haarProb)
    infer_instance
  have : Fintype J₀ := Fintype.ofFinite J₀
  have hcont : Continuous (reindexInvert ρ M) := continuous_pi fun i => by
    by_cases h : ρ.symm i ∈ M
    · have he : (fun g : LinkVariables J => reindexInvert ρ M g i) =
          fun g => (g (ρ.symm i))⁻¹ := by
        funext g
        simp [reindexInvert, h]
      rw [he]
      exact (continuous_apply _).inv
    · have he : (fun g : LinkVariables J => reindexInvert ρ M g i) =
          fun g => g (ρ.symm i) := by
        funext g
        simp [reindexInvert, h]
      rw [he]
      exact continuous_apply _
  have hmeas : Measurable (reindexInvert ρ M) := hcont.measurable
  have hmap : Measure.map (reindexInvert ρ M) (LinkVariables.haarMeasure J) =
      LinkVariables.haarMeasure J₀ := by
    rw [haarMeasure_eq_pi, haarMeasure_eq_pi]
    symm
    refine Measure.pi_eq fun S hS => ?_
    rw [Measure.map_apply hmeas (MeasurableSet.univ_pi hS)]
    let T : J → Set ComplexMatrix2.specialUnitary := fun j =>
      if j ∈ M then (fun U : ComplexMatrix2.specialUnitary => U⁻¹) ⁻¹' S (ρ j) else S (ρ j)
    have hpre : reindexInvert ρ M ⁻¹' univ.pi S = univ.pi T := by
      ext g
      simp only [mem_preimage, mem_univ_pi]
      constructor
      · intro h j
        have := h (ρ j)
        by_cases hj : j ∈ M
        · simpa [T, hj, reindexInvert] using this
        · simpa [T, hj, reindexInvert] using this
      · intro h i
        obtain ⟨j, rfl⟩ := ρ.surjective i
        have := h j
        by_cases hj : j ∈ M
        · simpa [T, hj, reindexInvert] using this
        · simpa [T, hj, reindexInvert] using this
    have hT : ∀ j, ComplexMatrix2.haarProb (T j) = ComplexMatrix2.haarProb (S (ρ j)) := by
      intro j
      by_cases hj : j ∈ M
      · simp only [T, if_pos hj]
        rw [← Measure.map_apply continuous_inv.measurable (hS (ρ j)), hinv]
      · simp only [T, if_neg hj]
    rw [hpre, Measure.pi_pi, Finset.prod_congr rfl fun j _ => hT j]
    exact Equiv.prod_comp ρ fun i => ComplexMatrix2.haarProb (S i)
  refine ⟨hcont, fun Φ => ?_⟩
  have hΦ : Measurable (Φ : LinkVariables J₀ → ℂ) := by
    obtain ⟨h, -⟩ := Φ.2
    rwa [borel_eq_pi] at h
  rw [← hmap, integral_map hmeas.aemeasurable hΦ.aestronglyMeasurable]
theorem countableProductTheorem_holds (h : ComplexMatrix2.HaarExpChartProperties) :
    CountableProductTheorem :=
  ⟨fun J hJ => by
    have := (isAtMostCountable_iff_countable J).1 hJ
    exact ⟨compactMetrizableWithEnumDist J, borelGeneratedByCoordinates J,
      fun J₁ J₂ hd hu => splitsAlongPartition J₁ J₂ hd hu, continuousApproxByCylinderFunctions J⟩,
   fun J _ => haarInvariantUnderReindexInvert h.2.2.2 J⟩
end YangMills.Construction.InfiniteLattice.CountableProduct
