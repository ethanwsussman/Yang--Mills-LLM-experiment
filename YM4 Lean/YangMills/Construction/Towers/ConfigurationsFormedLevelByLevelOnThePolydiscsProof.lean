import YangMills.Construction.Towers.ComplexAveragesFormedLevelByLevelProof
import YangMills.Construction.Towers.ConfigurationsFormedLevelByLevelOnThePolydiscs
import Mathlib
set_option autoImplicit false
open Set Filter
open scoped Topology Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.Tower.IteratedMeans
open YangMills.Construction.Matrices
theorem inv_mem_unitDeterminant {X : ComplexMatrix2} (h : X ∈ ComplexMatrix2.unitDeterminant) :
    X⁻¹ ∈ ComplexMatrix2.unitDeterminant := by apply _root_.YangMills.SharedProofs.p413 <;> assumption
theorem inv_inv_of_mem_unitDeterminant {X : ComplexMatrix2}
    (h : X ∈ ComplexMatrix2.unitDeterminant) : X⁻¹⁻¹ = X := by apply _root_.YangMills.Construction.Tower.LevelwiseMeans.inv_inv_of_mem_unitDeterminant <;> assumption
theorem mem_complexGaugeGroup_of_mem_compact {X : ComplexMatrix2}
    (h : X ∈ PeriodicLattice.compactGaugeGroup) : X ∈ PeriodicLattice.complexGaugeGroup :=
  (Matrix.mem_specialUnitaryGroup_iff.1 h).2
section Periodic
open YangMills.Construction.Tower.MeanStableFields
variable {L m k : ℕ}
theorem opposite_isPositivelyOriented_of_not {i : ℕ} (b : Edge L m k i)
    (h : ¬ b.IsPositivelyOriented) : b.opposite.IsPositivelyOriented := by
  obtain ⟨μ, h₁ | h₁⟩ := b.isNeighbour
  · exact absurd ⟨μ, h₁⟩ h
  · refine ⟨μ, ?_⟩
    show b.source - b.target = _
    rw [← neg_sub, h₁, neg_neg]
theorem not_isPositivelyOriented_opposite (hA : QuotientLattices.TorusAndSpaceLatticeProperties)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) {i : ℕ} (hi : i ≤ k)
    (b : Edge L m k i) (h : b.IsPositivelyOriented) : ¬ b.opposite.IsPositivelyOriented := by
  rintro ⟨ν, hν⟩
  obtain ⟨μ, hμ⟩ := h
  have nine := (hA L hL m i k hm hi).2.2.2.2.2.1
  have s₁ : QuotientLattices.IsSignedAxisStep
      (QuotientLattices.torusAxisSteps L m k i)
      (b.source : PeriodicLattice.FourTorus L m) (b.target : PeriodicLattice.FourTorus L m) 1 μ := by
    have e := congrArg Subtype.val hμ
    simpa [QuotientLattices.IsSignedAxisStep,
      QuotientLattices.torusAxisSteps] using e
  have s₂ : QuotientLattices.IsSignedAxisStep
      (QuotientLattices.torusAxisSteps L m k i)
      (b.target : PeriodicLattice.FourTorus L m) (b.source : PeriodicLattice.FourTorus L m) 1 ν := by
    have e := congrArg Subtype.val hν
    simpa [QuotientLattices.IsSignedAxisStep,
      QuotientLattices.torusAxisSteps, PeriodicLattice.Bond.opposite] using e
  rcases ((nine.2.2 _ b.source.2 _ b.target.2).2 1 μ s₁).2 with ⟨_, h₂⟩ | ⟨_, h₂⟩
  · exact h₂ ⟨ν, s₂⟩
  · exact h₂ ⟨μ, s₁⟩
theorem complexBlockAverage_of_positive {i : ℕ} (V : Edge L m k i → ComplexMatrix2)
    {c : Edge L m k (i + 1)} (h : c.IsPositivelyOriented) :
    PeriodicLattice.complexBlockAverage V c = PeriodicLattice.complexBlockAverageOnPositive V c := by
  simp only [PeriodicLattice.complexBlockAverage, if_pos h]
theorem complexBlockAverage_of_not_positive {i : ℕ} (V : Edge L m k i → ComplexMatrix2)
    {c : Edge L m k (i + 1)} (h : ¬ c.IsPositivelyOriented) :
    PeriodicLattice.complexBlockAverage V c =
      (PeriodicLattice.complexBlockAverageOnPositive V c.opposite)⁻¹ := by
  simp only [PeriodicLattice.complexBlockAverage, if_neg h]
theorem complexBlockAverage_mem_of_positive (hS : SmoothingNearIdentity)
    (hV : ComplexMeanLiesInComplexGaugeGroup)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) {i : ℕ} (hi : i < k)
    {V : Edge L m k i → ComplexMatrix2} (hw : V ∈ fieldsNearOne L m k i)
    {c : Edge L m k (i + 1)} (hc : c.IsPositivelyOriented) :
    PeriodicLattice.complexBlockAverage V c ∈ PeriodicLattice.complexGaugeGroup := by
  have hp : V ∈ nearIdentityPolydisc (polydiscRadius L) c :=
    ⟨⟨fun b _ => hw.1.1 b (mem_univ _), fun b _ => hw.1.2 b (mem_univ _)⟩, fun b _ => hw.2 b⟩
  have hd := ((hS.1 L hL).2.2.periodic m k i hm hi c hc).subset_complexDomain hp
  exact ((hV.2 L k (i + 1) hL (Nat.succ_pos i) hi).1 m hm c V hc hd).2
theorem meanStep_mem (hS : SmoothingNearIdentity)
    (hV : ComplexMeanLiesInComplexGaugeGroup)
    (hA : QuotientLattices.TorusAndSpaceLatticeProperties)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) {i : ℕ} (hi : i < k)
    {V : Edge L m k i → ComplexMatrix2} (hw : V ∈ fieldsNearOne L m k i) :
    meanStep V ∈ fieldsIn L m k (i + 1) PeriodicLattice.complexGaugeGroup := by
  have hpos : ∀ c : Edge L m k (i + 1), c.IsPositivelyOriented →
      PeriodicLattice.complexBlockAverageOnPositive V c ∈ PeriodicLattice.complexGaugeGroup := by
    intro c hc
    rw [← complexBlockAverage_of_positive V hc]
    exact complexBlockAverage_mem_of_positive hS hV hL hm hi hw hc
  refine ⟨fun c _ => ?_, fun c _ => ?_⟩
  · show PeriodicLattice.complexBlockAverage V c ∈ PeriodicLattice.complexGaugeGroup
    by_cases hc : c.IsPositivelyOriented
    · exact complexBlockAverage_mem_of_positive hS hV hL hm hi hw hc
    · rw [complexBlockAverage_of_not_positive V hc]
      exact inv_mem_unitDeterminant (hpos _ (opposite_isPositivelyOriented_of_not c hc))
  · show PeriodicLattice.complexBlockAverage V c.opposite =
      (PeriodicLattice.complexBlockAverage V c)⁻¹
    by_cases hc : c.IsPositivelyOriented
    · have hr := not_isPositivelyOriented_opposite hA hL hm (Nat.succ_le_of_lt hi) c hc
      rw [complexBlockAverage_of_not_positive V hr, complexBlockAverage_of_positive V hc]
      rfl
    · have hr := opposite_isPositivelyOriented_of_not c hc
      rw [complexBlockAverage_of_positive V hr, complexBlockAverage_of_not_positive V hc,
        inv_inv_of_mem_unitDeterminant (hpos _ hr)]
theorem eq_meanStep_iff {i : ℕ} {V : Edge L m k i → ComplexMatrix2}
    {V' : Edge L m k (i + 1) → ComplexMatrix2}
    (hV' : V' ∈ fieldsIn L m k (i + 1) PeriodicLattice.complexGaugeGroup) :
    (∀ c : Edge L m k (i + 1), c.IsPositivelyOriented →
        V' c = PeriodicLattice.complexBlockAverage V c) ↔
      V' = meanStep V := by
  constructor
  · intro h
    funext b
    show V' b = PeriodicLattice.complexBlockAverage V b
    by_cases hb : b.IsPositivelyOriented
    · exact h b hb
    · have hr := opposite_isPositivelyOriented_of_not b hb
      have e : V' b.opposite.opposite = (V' b.opposite)⁻¹ := hV'.2 b.opposite (mem_univ _)
      have e' : V' b = (V' b.opposite)⁻¹ := e
      rw [e', h _ hr, complexBlockAverage_of_positive V hr, complexBlockAverage_of_not_positive V hb]
  · rintro rfl c _
    rfl
theorem iteratedMean_succ_eq_some {W : Edge L m k 0 → ComplexMatrix2} {i : ℕ}
    {U : Edge L m k (i + 1) → ComplexMatrix2} (h : iteratedMean W (i + 1) = some U) :
    ∃ U' : Edge L m k i → ComplexMatrix2, iteratedMean W i = some U' ∧
      U' ∈ fieldsNearOne L m k i ∧ U = meanStep U' := by
  cases hU : iteratedMean W i with
  | none => simp [iteratedMean, hU] at h
  | some U' =>
    by_cases hw : U' ∈ fieldsNearOne L m k i
    · refine ⟨U', rfl, hw, ?_⟩
      simp [iteratedMean, hU, hw] at h
      exact h.symm
    · simp [iteratedMean, hU, hw] at h
theorem iteratedMean_isSome_of_le {W : Edge L m k 0 → ComplexMatrix2} :
    ∀ l : ℕ, (iteratedMean W l).isSome → ∀ i ≤ l, (iteratedMean W i).isSome := by
  intro l
  induction l with
  | zero =>
    intro h i hi
    obtain rfl : i = 0 := by omega
    exact h
  | succ l ih =>
    intro h i hi
    rcases Nat.lt_or_ge i (l + 1) with h₁ | h₁
    · obtain ⟨U, hU⟩ := Option.isSome_iff_exists.1 h
      obtain ⟨U', h', -, -⟩ := iteratedMean_succ_eq_some hU
      exact ih (by rw [h']; rfl) i (by omega)
    · obtain rfl : i = l + 1 := by omega
      exact h
theorem mem_fieldsIn_of_iteratedMean
    (hM : ∀ i < k, ∀ V ∈ fieldsNearOne L m k i,
      meanStep V ∈ fieldsIn L m k (i + 1) PeriodicLattice.complexGaugeGroup)
    {W : Edge L m k 0 → ComplexMatrix2}
    (hW : W ∈ fieldsIn L m k 0 PeriodicLattice.complexGaugeGroup) :
    ∀ l ≤ k, ∀ U : Edge L m k l → ComplexMatrix2, iteratedMean W l = some U →
      U ∈ fieldsIn L m k l PeriodicLattice.complexGaugeGroup := by
  intro l
  cases l with
  | zero =>
    intro _ U h
    obtain rfl : W = U := Option.some.inj h
    exact hW
  | succ l =>
    intro hl U h
    obtain ⟨U', -, hw, rfl⟩ := iteratedMean_succ_eq_some h
    exact hM l (by omega) U' hw
theorem mem_meanStableFields_of_isSome
    (hM : ∀ i < k, ∀ V ∈ fieldsNearOne L m k i,
      meanStep V ∈ fieldsIn L m k (i + 1) PeriodicLattice.complexGaugeGroup)
    {W : Edge L m k 0 → ComplexMatrix2}
    (hW : W ∈ fieldsIn L m k 0 PeriodicLattice.complexGaugeGroup)
    {l : ℕ} (hl : l ≤ k) (h : (iteratedMean W l).isSome) :
    W ∈ meanStableFields L m k l := by
  have getD_eq : ∀ {i : ℕ} {U : Edge L m k i → ComplexMatrix2}, iteratedMean W i = some U →
      (iteratedMean W i).getD (fun _ => 1) = U := by
    intro i U hU
    rw [hU]
    rfl
  refine ⟨fun i => (iteratedMean W i).getD (fun _ => 1), ⟨⟨?_, ?_, ?_⟩, rfl⟩⟩
  · intro i hi
    obtain ⟨U, hU⟩ := Option.isSome_iff_exists.1 (iteratedMean_isSome_of_le l h i hi)
    show (iteratedMean W i).getD (fun _ => 1) ∈ _
    rw [getD_eq hU]
    exact mem_fieldsIn_of_iteratedMean hM hW i (by omega) U hU
  · intro i hi b
    obtain ⟨U, hU⟩ := Option.isSome_iff_exists.1 (iteratedMean_isSome_of_le l h (i + 1) hi)
    obtain ⟨U', h', hw, -⟩ := iteratedMean_succ_eq_some hU
    show ComplexMatrix2.operatorNorm ((iteratedMean W i).getD (fun _ => 1) b - 1) < _
    rw [getD_eq h']
    exact hw.2 b
  · intro i hi c _
    obtain ⟨U, hU⟩ := Option.isSome_iff_exists.1 (iteratedMean_isSome_of_le l h (i + 1) hi)
    obtain ⟨U', h', -, rfl⟩ := iteratedMean_succ_eq_some hU
    show (iteratedMean W (i + 1)).getD (fun _ => 1) c =
      PeriodicLattice.complexBlockAverage ((iteratedMean W i).getD (fun _ => 1)) c
    rw [getD_eq hU, getD_eq h']
    rfl
theorem iteratedMean_eq_of_isMeanSequenceFrom {l : ℕ} {W : Edge L m k 0 → ComplexMatrix2}
    {V : ∀ i : ℕ, Edge L m k i → ComplexMatrix2}
    (h : IsMeanSequenceFrom l W V) : ∀ i ≤ l, iteratedMean W i = some (V i) := by
  intro i
  induction i with
  | zero =>
    intro _
    rw [h.2]
    rfl
  | succ i ih =>
    intro hi
    have hprev := ih (by omega)
    have hw : V i ∈ fieldsNearOne L m k i :=
      ⟨h.1.mem_fields i (by omega), h.1.norm_sub_one_lt i (by omega)⟩
    have hV : V (i + 1) = meanStep (V i) :=
      (eq_meanStep_iff (h.1.mem_fields _ hi)).1 (h.1.eq_mean i (by omega))
    rw [hV]
    simp [iteratedMean, hprev, hw]
theorem eventually_norm_sub_one_lt (hS : SmoothingNearIdentity)
    (hA : QuotientLattices.TorusAndSpaceLatticeProperties)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) {i : ℕ} (hi : i < k) :
    EventuallyNearIdentity (fieldSpace L m k i) fun V =>
      ∀ b, ComplexMatrix2.operatorNorm (V b - 1) < polydiscRadius L := by
  have hρ : 0 < polydiscRadius L := (hS.1 L hL).2.2.pos
  have : Finite (Edge L m k i) :=
    (hA L hL m i k hm hi.le).2.1.2.2.2.2.2.2.2.2.2.2.2.1
  refine Filter.Eventually.filter_mono nhdsWithin_le_nhds ?_
  refine Filter.eventually_all.2 fun b => ?_
  have hc : ContinuousAt (fun V : Edge L m k i → ComplexMatrix2 =>
      ComplexMatrix2.operatorNorm (V b - 1)) (fun _ => (1 : ComplexMatrix2)) :=
    ((continuous_apply b).sub continuous_const).norm.continuousAt
  have h₀ : ComplexMatrix2.operatorNorm
      ((fun _ => (1 : ComplexMatrix2) : Edge L m k i → ComplexMatrix2) b - 1) <
      polydiscRadius L := by
    simpa using hρ
  exact hc.tendsto.eventually (Iio_mem_nhds h₀)
theorem torusConditions (hS : SmoothingNearIdentity)
    (hV : ComplexMeanLiesInComplexGaugeGroup)
    (hA : QuotientLattices.TorusAndSpaceLatticeProperties)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) : TorusConditions L m k := by
  have hM : ∀ i < k, ∀ V ∈ fieldsNearOne L m k i,
      meanStep V ∈ fieldsIn L m k (i + 1) PeriodicLattice.complexGaugeGroup :=
    fun i hi V hw => meanStep_mem hS hV hA hL hm hi hw
  refine ⟨hM, fun i _ V _ V' hV' => eq_meanStep_iff hV', ?_, ?_, ?_, ?_⟩
  · intro l hl W hW
    constructor
    · exact mem_meanStableFields_of_isSome hM hW hl
    · rintro ⟨V, hb⟩
      rw [iteratedMean_eq_of_isMeanSequenceFrom hb l le_rfl]
      rfl
  · intro l _ W _ V hb
    exact iteratedMean_eq_of_isMeanSequenceFrom hb
  · intro i hi
    exact eventually_norm_sub_one_lt hS hA hL hm hi
  · intro i _ V hV'
    exact ⟨fun b hb => mem_complexGaugeGroup_of_mem_compact (hV'.1 b hb), hV'.2⟩
end Periodic
namespace Unbounded
open YangMills.Construction.Tower.MeanStableFields.Infinite
variable {L k : ℕ}
theorem opposite_isPositivelyOriented_of_not {a : ℝ} (b : InfiniteLattice.Link a)
    (h : ¬ b.IsPositivelyOriented) : b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.InfiniteLattice.PeriodSublattice.isPositivelyOriented_opposite_of_not <;> assumption
theorem not_isPositivelyOriented_opposite {a : ℝ} (ha : 0 < a) (b : InfiniteLattice.Link a)
    (h : b.IsPositivelyOriented) : ¬ b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.InfiniteLattice.Link.opposite_not_isPositivelyOriented <;> assumption
theorem meshAt_pos (hL : Conventions.IsAdmissibleBlockingFactor L) (i : ℕ) :
    0 < meshAt L k i := by apply _root_.YangMills.Construction.Tower.LevelwiseMeans.Unbounded.meshAt_pos <;> assumption
theorem complexSmoothing_of_positive {i : ℕ} (V : FullSpace.Edge L k i → ComplexMatrix2)
    {c : FullSpace.Edge L k (i + 1)} (h : c.IsPositivelyOriented) :
    FullSpace.complexSmoothing L V c = FullSpace.complexSmoothingPositive L V c := by
  simp only [FullSpace.complexSmoothing, if_pos h]
theorem complexSmoothing_of_not_positive {i : ℕ} (V : FullSpace.Edge L k i → ComplexMatrix2)
    {c : FullSpace.Edge L k (i + 1)} (h : ¬ c.IsPositivelyOriented) :
    FullSpace.complexSmoothing L V c =
      (FullSpace.complexSmoothingPositive L V c.opposite)⁻¹ := by
  simp only [FullSpace.complexSmoothing, if_neg h]
theorem complexSmoothing_mem_of_positive (hS : SmoothingNearIdentity)
    (hV : ComplexMeanLiesInComplexGaugeGroup)
    (hL : Conventions.IsAdmissibleBlockingFactor L) {i : ℕ} (hi : i < k)
    {V : FullSpace.Edge L k i → ComplexMatrix2} (hw : V ∈ fieldsNearOne L k i)
    {c : FullSpace.Edge L k (i + 1)} (hc : c.IsPositivelyOriented) :
    FullSpace.complexSmoothing L V c ∈ PeriodicLattice.complexGaugeGroup := by
  have hp : V ∈ FullSpace.nearIdentityPolydisc L k i (polydiscRadius L) c :=
    ⟨⟨fun b _ => hw.1.1 b, fun b _ => hw.1.2 b⟩, fun b _ => hw.2 b⟩
  have hd := ((hS.1 L hL).2.2.fullSpace k i hi c hc).subset_complexDomain hp
  exact ((hV.2 L k (i + 1) hL (Nat.succ_pos i) hi).2 c V hc hd).2
theorem meanStep_mem (hS : SmoothingNearIdentity)
    (hV : ComplexMeanLiesInComplexGaugeGroup)
    (hL : Conventions.IsAdmissibleBlockingFactor L) {i : ℕ} (hi : i < k)
    {V : FullSpace.Edge L k i → ComplexMatrix2} (hw : V ∈ fieldsNearOne L k i) :
    meanStep V ∈ FullSpace.fieldsValuedIn L k (i + 1) PeriodicLattice.complexGaugeGroup := by
  have hpos : ∀ c : FullSpace.Edge L k (i + 1), c.IsPositivelyOriented →
      FullSpace.complexSmoothingPositive L V c ∈ PeriodicLattice.complexGaugeGroup := by
    intro c hc
    rw [← complexSmoothing_of_positive V hc]
    exact complexSmoothing_mem_of_positive hS hV hL hi hw hc
  refine ⟨fun c => ?_, fun c => ?_⟩
  · show FullSpace.complexSmoothing L V c ∈ PeriodicLattice.complexGaugeGroup
    by_cases hc : c.IsPositivelyOriented
    · exact complexSmoothing_mem_of_positive hS hV hL hi hw hc
    · rw [complexSmoothing_of_not_positive V hc]
      exact inv_mem_unitDeterminant (hpos _ (opposite_isPositivelyOriented_of_not c hc))
  · show FullSpace.complexSmoothing L V c.opposite =
      (FullSpace.complexSmoothing L V c)⁻¹
    by_cases hc : c.IsPositivelyOriented
    · have hr := not_isPositivelyOriented_opposite (meshAt_pos hL (i + 1)) c hc
      rw [complexSmoothing_of_not_positive V hr, complexSmoothing_of_positive V hc]
      rfl
    · have hr := opposite_isPositivelyOriented_of_not c hc
      rw [complexSmoothing_of_positive V hr, complexSmoothing_of_not_positive V hc,
        inv_inv_of_mem_unitDeterminant (hpos _ hr)]
theorem eq_meanStep_iff {i : ℕ} {V : FullSpace.Edge L k i → ComplexMatrix2}
    {V' : FullSpace.Edge L k (i + 1) → ComplexMatrix2}
    (hV' : V' ∈ FullSpace.fieldsValuedIn L k (i + 1) PeriodicLattice.complexGaugeGroup) :
    (∀ c : FullSpace.Edge L k (i + 1), c.IsPositivelyOriented →
        V' c = FullSpace.complexSmoothing L V c) ↔
      V' = meanStep V := by
  constructor
  · intro h
    funext b
    show V' b = FullSpace.complexSmoothing L V b
    by_cases hb : b.IsPositivelyOriented
    · exact h b hb
    · have hr := opposite_isPositivelyOriented_of_not b hb
      have e : V' b.opposite.opposite = (V' b.opposite)⁻¹ := hV'.2 b.opposite
      have e' : V' b = (V' b.opposite)⁻¹ := e
      rw [e', h _ hr, complexSmoothing_of_positive V hr, complexSmoothing_of_not_positive V hb]
  · rintro rfl c _
    rfl
theorem iteratedMean_succ_eq_some {W : FullSpace.Edge L k 0 → ComplexMatrix2} {i : ℕ}
    {U : FullSpace.Edge L k (i + 1) → ComplexMatrix2} (h : iteratedMean W (i + 1) = some U) :
    ∃ U' : FullSpace.Edge L k i → ComplexMatrix2, iteratedMean W i = some U' ∧
      U' ∈ fieldsNearOne L k i ∧ U = meanStep U' := by
  cases hU : iteratedMean W i with
  | none => simp [iteratedMean, hU] at h
  | some U' =>
    by_cases hw : U' ∈ fieldsNearOne L k i
    · refine ⟨U', rfl, hw, ?_⟩
      simp [iteratedMean, hU, hw] at h
      exact h.symm
    · simp [iteratedMean, hU, hw] at h
theorem iteratedMean_isSome_of_le {W : FullSpace.Edge L k 0 → ComplexMatrix2} :
    ∀ l : ℕ, (iteratedMean W l).isSome → ∀ i ≤ l, (iteratedMean W i).isSome := by
  intro l
  induction l with
  | zero =>
    intro h i hi
    obtain rfl : i = 0 := by omega
    exact h
  | succ l ih =>
    intro h i hi
    rcases Nat.lt_or_ge i (l + 1) with h₁ | h₁
    · obtain ⟨U, hU⟩ := Option.isSome_iff_exists.1 h
      obtain ⟨U', h', -, -⟩ := iteratedMean_succ_eq_some hU
      exact ih (by rw [h']; rfl) i (by omega)
    · obtain rfl : i = l + 1 := by omega
      exact h
theorem mem_fieldsValuedIn_of_iteratedMean
    (hM : ∀ i < k, ∀ V ∈ fieldsNearOne L k i,
      meanStep V ∈ FullSpace.fieldsValuedIn L k (i + 1) PeriodicLattice.complexGaugeGroup)
    {W : FullSpace.Edge L k 0 → ComplexMatrix2}
    (hW : W ∈ FullSpace.fieldsValuedIn L k 0 PeriodicLattice.complexGaugeGroup) :
    ∀ l ≤ k, ∀ U : FullSpace.Edge L k l → ComplexMatrix2, iteratedMean W l = some U →
      U ∈ FullSpace.fieldsValuedIn L k l PeriodicLattice.complexGaugeGroup := by
  intro l
  cases l with
  | zero =>
    intro _ U h
    obtain rfl : W = U := Option.some.inj h
    exact hW
  | succ l =>
    intro hl U h
    obtain ⟨U', -, hw, rfl⟩ := iteratedMean_succ_eq_some h
    exact hM l (by omega) U' hw
theorem mem_meanStableFields_of_isSome
    (hM : ∀ i < k, ∀ V ∈ fieldsNearOne L k i,
      meanStep V ∈ FullSpace.fieldsValuedIn L k (i + 1) PeriodicLattice.complexGaugeGroup)
    {W : FullSpace.Edge L k 0 → ComplexMatrix2}
    (hW : W ∈ FullSpace.fieldsValuedIn L k 0 PeriodicLattice.complexGaugeGroup)
    {l : ℕ} (hl : l ≤ k) (h : (iteratedMean W l).isSome) :
    W ∈ meanStableFields L k l := by
  have getD_eq : ∀ {i : ℕ} {U : FullSpace.Edge L k i → ComplexMatrix2},
      iteratedMean W i = some U → (iteratedMean W i).getD (fun _ => 1) = U := by
    intro i U hU
    rw [hU]
    rfl
  refine ⟨fun i => (iteratedMean W i).getD (fun _ => 1), ⟨⟨?_, ?_, ?_⟩, rfl⟩⟩
  · intro i hi
    obtain ⟨U, hU⟩ := Option.isSome_iff_exists.1 (iteratedMean_isSome_of_le l h i hi)
    show (iteratedMean W i).getD (fun _ => 1) ∈ _
    rw [getD_eq hU]
    exact mem_fieldsValuedIn_of_iteratedMean hM hW i (by omega) U hU
  · intro i hi b
    obtain ⟨U, hU⟩ := Option.isSome_iff_exists.1 (iteratedMean_isSome_of_le l h (i + 1) hi)
    obtain ⟨U', h', hw, -⟩ := iteratedMean_succ_eq_some hU
    show ComplexMatrix2.operatorNorm ((iteratedMean W i).getD (fun _ => 1) b - 1) < _
    rw [getD_eq h']
    exact hw.2 b
  · intro i hi c _
    obtain ⟨U, hU⟩ := Option.isSome_iff_exists.1 (iteratedMean_isSome_of_le l h (i + 1) hi)
    obtain ⟨U', h', -, rfl⟩ := iteratedMean_succ_eq_some hU
    show (iteratedMean W (i + 1)).getD (fun _ => 1) c =
      FullSpace.complexSmoothing L ((iteratedMean W i).getD (fun _ => 1)) c
    rw [getD_eq hU, getD_eq h']
    rfl
theorem iteratedMean_eq_of_isMeanSequenceFrom {l : ℕ}
    {W : FullSpace.Edge L k 0 → ComplexMatrix2}
    {V : ∀ i : ℕ, FullSpace.Edge L k i → ComplexMatrix2}
    (h : IsMeanSequenceFrom l W V) : ∀ i ≤ l, iteratedMean W i = some (V i) := by
  intro i
  induction i with
  | zero =>
    intro _
    rw [h.2]
    rfl
  | succ i ih =>
    intro hi
    have hprev := ih (by omega)
    have hw : V i ∈ fieldsNearOne L k i :=
      ⟨h.1.mem_fields i (by omega), h.1.norm_sub_one_lt i (by omega)⟩
    have hV : V (i + 1) = meanStep (V i) :=
      (eq_meanStep_iff (h.1.mem_fields _ hi)).1 (h.1.eq_mean i (by omega))
    rw [hV]
    simp [iteratedMean, hprev, hw]
theorem eventually_norm_sub_one_lt (hS : SmoothingNearIdentity)
    (hL : Conventions.IsAdmissibleBlockingFactor L) {i : ℕ} :
    FullSpace.EventuallyNearIdentity (FullSpace.fieldSpace L k i) fun V =>
      ∀ b, ComplexMatrix2.operatorNorm (V b - 1) < polydiscRadius L := by
  have hρ : 0 < polydiscRadius L := (hS.1 L hL).2.2.pos
  refine ⟨polydiscRadius L, hρ, fun V _ hd b => ?_⟩
  have h₁ : ENNReal.ofReal (ComplexMatrix2.operatorNorm (V b - 1)) ≤ FullSpace.supDistOne V :=
    le_iSup (fun b => ENNReal.ofReal (ComplexMatrix2.operatorNorm (V b - 1))) b
  exact (ENNReal.ofReal_lt_ofReal_iff hρ).1 (lt_of_le_of_lt h₁ hd)
theorem spaceProperties (hS : SmoothingNearIdentity)
    (hV : ComplexMeanLiesInComplexGaugeGroup)
    (hL : Conventions.IsAdmissibleBlockingFactor L) : SpaceConditions L k := by
  have hM : ∀ i < k, ∀ V ∈ fieldsNearOne L k i,
      meanStep V ∈ FullSpace.fieldsValuedIn L k (i + 1) PeriodicLattice.complexGaugeGroup :=
    fun i hi V hw => meanStep_mem hS hV hL hi hw
  refine ⟨hM, fun i _ V _ V' hV' => eq_meanStep_iff hV', ?_, ?_, ?_, ?_⟩
  · intro l hl W hW
    constructor
    · exact mem_meanStableFields_of_isSome hM hW hl
    · rintro ⟨V, hb⟩
      rw [iteratedMean_eq_of_isMeanSequenceFrom hb l le_rfl]
      rfl
  · intro l _ W _ V hb
    exact iteratedMean_eq_of_isMeanSequenceFrom hb
  · intro i _
    exact eventually_norm_sub_one_lt hS hL
  · intro i _ V hV'
    exact ⟨fun b => mem_complexGaugeGroup_of_mem_compact (hV'.1 b), hV'.2⟩
end Unbounded
theorem iteratedMeansHold (hS : SmoothingNearIdentity)
    (hV : ComplexMeanLiesInComplexGaugeGroup)
    (hA : QuotientLattices.TorusAndSpaceLatticeProperties) : IteratedMeansHold := by
  intro L hL k _
  exact ⟨fun m hm => torusConditions hS hV hA hL hm, Unbounded.spaceProperties hS hV hL⟩
end YangMills.Construction.Tower.IteratedMeans
end
