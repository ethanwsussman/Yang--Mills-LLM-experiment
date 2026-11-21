import YangMills.Construction.Matrices.ExponentialOfLieElements
import YangMills.Construction.Towers.ComplexAveragesFormedLevelByLevelProof
import YangMills.Construction.Towers.CompositesOfTheLiftsAndLayersOfSites
import YangMills.Construction.Towers.ConfigurationsWhoseAveragesStayInThePolydiscs
import YangMills.Construction.Towers.RealAndCovariantDifferentialsOfTheChain
import YangMills.Construction.Towers.SurjectiveDifferentialsNearTheTrivialConfigurationProof
import Mathlib
set_option autoImplicit false
open Set Filter
open scoped Topology Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.Tower.ChainBottomDifferentials
open Matrices Tower Tower.LevelwiseMeans
open Tower.MeanStableFields (meanStableFields IsMeanSequenceFrom)
variable {L m k j : ℕ}
theorem positive_or_opposite (b : Edge L m k j) :
    b.IsPositivelyOriented ∨ b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.Tower.TrivialFieldAverages.edge_positive_or_opposite <;> assumption
theorem not_opposite_positive (hE : BondSetFields.ProductStructureHolds)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) (hj : j ≤ k) (b : Edge L m k j)
    (hb : b.IsPositivelyOriented) : ¬ b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.Tower.NearIdentitySurjectivity.not_isPositivelyOriented_opposite <;> assumption
theorem inv_mem_unitDeterminant {X : ComplexMatrix2} (h : X ∈ ComplexMatrix2.unitDeterminant) :
    X⁻¹ ∈ ComplexMatrix2.unitDeterminant := by apply _root_.YangMills.SharedProofs.p413 <;> assumption
theorem inv_inv_of_mem_unitDeterminant {X : ComplexMatrix2}
    (h : X ∈ ComplexMatrix2.unitDeterminant) : (X⁻¹)⁻¹ = X := by apply _root_.YangMills.Construction.Tower.LevelwiseMeans.inv_inv_of_mem_unitDeterminant <;> assumption
theorem mul_mem_unitDeterminant {X Y : ComplexMatrix2} (h : X ∈ ComplexMatrix2.unitDeterminant)
    (h' : Y ∈ ComplexMatrix2.unitDeterminant) : X * Y ∈ ComplexMatrix2.unitDeterminant := by apply _root_.YangMills.SharedProofs.p36859 <;> assumption
theorem expTwist_of_positive (A U : Edge L m k j → ComplexMatrix2) {b : Edge L m k j}
    (h : b.IsPositivelyOriented) :
    PeriodicLattice.expTwist A U b = ComplexMatrix2.matExp (Complex.I • A b) * U b := if_pos h
theorem expTwist_of_not_positive (A U : Edge L m k j → ComplexMatrix2) {b : Edge L m k j}
    (h : ¬b.IsPositivelyOriented) :
    PeriodicLattice.expTwist A U b =
      (ComplexMatrix2.matExp (Complex.I • A b.opposite) * U b.opposite)⁻¹ := if_neg h
theorem expTwist_mem_complexGaugeGroup (hX : ComplexMatrix2.ExpImaginaryLieMem)
    (hE : BondSetFields.ProductStructureHolds) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hm : 0 < m) (hj : j ≤ k) {B U : Edge L m k j → ComplexMatrix2}
    (hB : ∀ b : Edge L m k j, b.IsPositivelyOriented → B b ∈ PeriodicLattice.complexLieAlgebra)
    (hU : U ∈ fieldsIn L m k j PeriodicLattice.complexGaugeGroup) (t : ℂ) :
    PeriodicLattice.expTwist (t • B) U ∈ fieldsIn L m k j PeriodicLattice.complexGaugeGroup := by
  have hp : ∀ b : Edge L m k j, b.IsPositivelyOriented →
      ComplexMatrix2.matExp (Complex.I • (t • B) b) * U b ∈ ComplexMatrix2.unitDeterminant :=
    fun b hb =>
      mul_mem_unitDeterminant (hX.2 _ (Submodule.smul_mem _ t (hB b hb))) (hU.1 b (mem_univ b))
  refine ⟨fun b _ => ?_, fun b _ => ?_⟩
  · by_cases hb : b.IsPositivelyOriented
    · rw [expTwist_of_positive _ _ hb]
      exact hp b hb
    · rw [expTwist_of_not_positive _ _ hb]
      exact inv_mem_unitDeterminant (hp _ ((positive_or_opposite b).resolve_left hb))
  · by_cases hb : b.IsPositivelyOriented
    · rw [expTwist_of_not_positive _ _ (not_opposite_positive hE hL hm hj b hb),
        expTwist_of_positive _ _ hb]
      rfl
    · have hr := (positive_or_opposite b).resolve_left hb
      rw [expTwist_of_positive _ _ hr, expTwist_of_not_positive _ _ hb,
        inv_inv_of_mem_unitDeterminant (hp _ hr)]
theorem tendsto_expTwist (B U : Edge L m k j → ComplexMatrix2) {b : Edge L m k j}
    (hb : b.IsPositivelyOriented) :
    Tendsto (fun t : ℂ => PeriodicLattice.expTwist (t • B) U b) (𝓝 0) (𝓝 (U b)) := by
  have hc : Continuous fun t : ℂ => ComplexMatrix2.matExp (Complex.I • (t • B b)) * U b := by
    have h1 : Continuous fun t : ℂ => Complex.I • (t • B b) :=
      (continuous_id.smul continuous_const).const_smul Complex.I
    let +nondep : NormedAlgebra ℚ ComplexMatrix2 := .restrictScalars ℚ ℂ ComplexMatrix2
    exact (NormedSpace.exp_continuous.comp h1).mul continuous_const
  have h := hc.tendsto 0
  have e : ComplexMatrix2.matExp (Complex.I • ((0 : ℂ) • B b)) * U b = U b := by
    simp [NormedSpace.exp_zero]
  rw [e] at h
  exact h.congr fun t => (expTwist_of_positive _ _ hb).symm
theorem eq_complexBlockFieldAtLevel {W : Edge L m k 0 → ComplexMatrix2}
    {V : ∀ i : ℕ, Edge L m k i → ComplexMatrix2}
    (hV : IsMeanSequenceFrom k W V) :
    ∀ i, i ≤ k → V i = PeriodicLattice.complexBlockFieldAtLevel i W := by
  intro i
  induction i with
  | zero => exact fun _ => hV.2
  | succ i ih =>
    intro hi
    have e := ih (by omega)
    have hfam := hV.1
    funext c
    show V (i + 1) c =
      PeriodicLattice.complexBlockAverage (PeriodicLattice.complexBlockFieldAtLevel i W) c
    rw [← e]
    by_cases hc : c.IsPositivelyOriented
    · exact hfam.eq_mean i (by omega) c hc
    · have hr := (positive_or_opposite c).resolve_left hc
      have h1 := hfam.eq_mean i (by omega) c.opposite hr
      have h2 : V (i + 1) c = (V (i + 1) c.opposite)⁻¹ :=
        (hfam.mem_fields (i + 1) hi).2 c.opposite (mem_univ _)
      have h3 : PeriodicLattice.complexBlockAverage (V i) c.opposite =
          PeriodicLattice.complexBlockAverageOnPositive (V i) c.opposite := if_pos hr
      have h4 : PeriodicLattice.complexBlockAverage (V i) c =
          (PeriodicLattice.complexBlockAverageOnPositive (V i) c.opposite)⁻¹ := if_neg hc
      rw [h2, h1, h3, h4]
theorem levelwiseMean_of_mem_meanStableFields (hP : MeanStableFields.MeanStableConditions L m k)
    {W : Edge L m k 0 → ComplexMatrix2} (hW : W ∈ meanStableFields L m k k) (hj : j ≤ k)
    (c : Edge L m k j) :
    levelwiseMean W j c = some (PeriodicLattice.complexBlockFieldAtLevel j W c) := by
  obtain ⟨V, hV⟩ := hW
  rw [← eq_complexBlockFieldAtLevel hV j hj]
  exact hP.eq_levelwiseMean k le_rfl W V hV j hj c
theorem mem_fieldsIn_complex {V : Edge L m k j → ComplexMatrix2} (hV : V ∈ fieldSpace L m k j) :
    V ∈ fieldsIn L m k j PeriodicLattice.complexGaugeGroup := by apply _root_.YangMills.Construction.Tower.LevelwiseMeans.mem_fieldsIn_of_mem <;> assumption
theorem mem_meanStableFields_of_levelwise {U : Edge L m k 0 → ComplexMatrix2}
    (hU : ∀ i ≤ k, smoothingIter L m k i U ∈ fieldSpace L m k i ∧
      (∀ b, ComplexMatrix2.operatorNorm (smoothingIter L m k i U b - 1) < polydiscRadius L) ∧
      ∀ c, levelwiseMean U i c = some (smoothingIter L m k i U c)) :
    U ∈ meanStableFields L m k k := by
  refine ⟨fun i => smoothingIter L m k i U,
    ⟨fun i hi => mem_fieldsIn_complex (hU i hi).1, fun i hi => (hU i hi.le).2.1,
      fun i hi c hc => ?_⟩, rfl⟩
  have h1 : meanOfDefined (levelwiseMean U i) c = some (smoothingIter L m k (i + 1) U c) := by
    have h := (hU (i + 1) hi).2.2 c
    rw [levelwiseMean] at h
    beta_reduce at h
    rw [if_pos hc] at h
    exact h
  have h0 : valuesOrOne (levelwiseMean U i) = smoothingIter L m k i U :=
    funext fun b => by simp [valuesOrOne, (hU i hi.le).2.2 b]
  by_cases hcond : (∀ b ∈ (PeriodicLattice.bondsInDoubleBlock c : Set (Edge L m k i)),
      (levelwiseMean U i b).isSome) ∧
      valuesOrOne (levelwiseMean U i) ∈ nearIdentityPolydisc (polydiscRadius L) c
  · rw [meanOfDefined, if_pos hcond, h0] at h1
    exact (Option.some.inj h1).symm
  · rw [meanOfDefined, if_neg hcond] at h1
    exact absurd h1 (by simp)
theorem leftDifferential_eq_holLeftDifferential_apply (hX : ComplexMatrix2.ExpImaginaryLieMem)
    (hE : BondSetFields.ProductStructureHolds) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hm : 0 < m)
    (hF : LevelwiseMeans.PeriodicConditions L m k)
    (hP : MeanStableFields.MeanStableConditions L m k)
    {U : Edge L m k 0 → ComplexMatrix2} (hU0 : U ∈ fieldSpace L m k 0)
    (hS : U ∈ meanStableFields L m k k) (hj : j ≤ k) {B : Edge L m k 0 → ComplexMatrix2}
    (hB : B ∈ edgeFormSpace L m k 0) {c : Edge L m k j} (hc : c.IsPositivelyOriented)
    (hD : ∀ (F : Finset (Edge L m k 0)) (O : Set (F → ComplexMatrix2))
      (f : (F → ComplexMatrix2) → ComplexMatrix2),
      IsHolomorphicRepresentation j c U F O f →
      HasDerivAt (fun t : ℂ => ComplexMatrix2.logSeries
          (f (expChartPoint F (t • B) U) * (f (edgeEntries F U))⁻¹))
        (Complex.I • leftDifferential (smoothingIter L m k j) U B c) 0) :
    leftDifferential (smoothingIter L m k j) U B c =
      holLeftDifferential (PeriodicLattice.complexBlockFieldAtLevel j) U B c := by
  classical
  have hUC := mem_fieldsIn_complex hU0
  have hBC : ∀ b : Edge L m k 0, b.IsPositivelyOriented → B b ∈ PeriodicLattice.complexLieAlgebra :=
    fun b hb => (hB.1 b hb).2
  have hform := levelwiseMean_of_mem_meanStableFields hP hS hj c
  obtain ⟨F, O, f, w⟩ := hF.exists_representation j hj c U hUC (by
    show (levelwiseMean U j c).isSome
    rw [hform]
    rfl)
  have hal := hF.represents_along_curves j hj c U hUC F O f w B hBC
  have hfin : Finite (Edge L m k 0) :=
    Set.finite_univ_iff.1 ((hE L hL k 0 (Nat.zero_le k)).1 m hm).2.1
  have := Fintype.ofFinite (Edge L m k 0)
  obtain ⟨ε, hε, hmove⟩ := hP.small_perturbation U hS
    (Finset.univ.filter fun b => b.IsPositivelyOriented)
    (fun b hb => (Finset.mem_filter.1 hb).2)
  have hnear : ∀ᶠ t : ℂ in 𝓝 0,
      ∀ b ∈ Finset.univ.filter fun b : Edge L m k 0 => b.IsPositivelyOriented,
      ComplexMatrix2.operatorNorm (PeriodicLattice.expTwist (t • B) U b - U b) < ε := by
    refine (Filter.eventually_all_finset _).2 fun b hb => ?_
    have h := (tendsto_expTwist B U (Finset.mem_filter.1 hb).2).sub_const (U b)
    rw [sub_self] at h
    exact h.norm.eventually_lt_const (by simpa using hε)
  have hval : PeriodicLattice.complexBlockFieldAtLevel j U c = f (edgeEntries F U) :=
    Option.some.inj (hform.symm.trans (w.eq_some U hUC w.mem))
  have he : (fun t : ℂ => ComplexMatrix2.logSeries (PeriodicLattice.complexBlockFieldAtLevel j
      (PeriodicLattice.expTwist (algebraMap ℂ ℂ t • B) U) c *
        (PeriodicLattice.complexBlockFieldAtLevel j U c)⁻¹)) =ᶠ[𝓝 0]
      fun t : ℂ => ComplexMatrix2.logSeries
        (f (expChartPoint F (t • B) U) * (f (edgeEntries F U))⁻¹) := by
    filter_upwards [hal, hnear] with t h1 h2
    have hW : PeriodicLattice.expTwist (t • B) U ∈ meanStableFields L m k k :=
      hmove _ (expTwist_mem_complexGaugeGroup hX hE hL hm (Nat.zero_le k) hBC hUC t)
        (fun b hb hb' => absurd (Finset.mem_filter.2 ⟨Finset.mem_univ b, hb⟩) hb') h2
    have e := Option.some.inj ((levelwiseMean_of_mem_meanStableFields hP hW hj c).symm.trans h1.2)
    simp only [Algebra.algebraMap_self, RingHom.id_apply, e, hval]
  have hderiv := ((hD F O f w).congr_of_eventuallyEq he).deriv
  have hpos : holLeftDifferential (PeriodicLattice.complexBlockFieldAtLevel j) U B c =
      logDirectionalDeriv ℂ (fun X => PeriodicLattice.complexBlockFieldAtLevel j
        (PeriodicLattice.expTwist X U) c) (PeriodicLattice.complexBlockFieldAtLevel j U c) B := by
    simp only [holLeftDifferential, extendOddly, if_pos hc]
  rw [hpos, logDirectionalDeriv, hderiv, smul_smul, inv_mul_cancel₀ Complex.I_ne_zero, one_smul]
theorem leftDifferential_eq_holLeftDifferential (hX : ComplexMatrix2.ExpImaginaryLieMem)
    (hE : BondSetFields.ProductStructureHolds) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hm : 0 < m)
    (hF : LevelwiseMeans.PeriodicConditions L m k)
    (hP : MeanStableFields.MeanStableConditions L m k)
    {U : Edge L m k 0 → ComplexMatrix2} (hU0 : U ∈ fieldSpace L m k 0)
    (hS : U ∈ meanStableFields L m k k) (hj : j ≤ k) {B : Edge L m k 0 → ComplexMatrix2}
    (hB : B ∈ edgeFormSpace L m k 0)
    (hD : ∀ c : Edge L m k j, c.IsPositivelyOriented →
      ∀ (F : Finset (Edge L m k 0)) (O : Set (F → ComplexMatrix2))
        (f : (F → ComplexMatrix2) → ComplexMatrix2),
      IsHolomorphicRepresentation j c U F O f →
      HasDerivAt (fun t : ℂ => ComplexMatrix2.logSeries
          (f (expChartPoint F (t • B) U) * (f (edgeEntries F U))⁻¹))
        (Complex.I • leftDifferential (smoothingIter L m k j) U B c) 0) :
    leftDifferential (smoothingIter L m k j) U B =
      holLeftDifferential (PeriodicLattice.complexBlockFieldAtLevel j) U B := by
  have key := fun (c : Edge L m k j) (hc : c.IsPositivelyOriented) =>
    leftDifferential_eq_holLeftDifferential_apply hX hE hL hm hF hP hU0 hS hj hB hc (hD c hc)
  funext c
  by_cases hc : c.IsPositivelyOriented
  · exact key c hc
  · have hr := (positive_or_opposite c).resolve_left hc
    have h := key _ hr
    simp only [leftDifferential, holLeftDifferential, extendOddly, if_pos hr] at h
    simp only [leftDifferential, holLeftDifferential, extendOddly, if_neg hc]
    rw [h]
theorem realDerivEqComplexAtChainBottom_holds
    (hC : ProlongCompositesAndVertexLayers.Statement)
    (hF : LevelwiseMeans.LevelwiseMeansHold)
    (hP : MeanStableFields.MeanStableFieldsHold)
    (hE : BondSetFields.ProductStructureHolds)
    (hX : ComplexMatrix2.ExpImaginaryLieMem) : RealDerivEqComplexAtChainBottom := by
  intro L m k hL hm hk
  obtain ⟨hcomp, hobj, -⟩ := hC.1 L m k hL hm hk
  have hF' := (hF L hL k hk).1 m hm
  have hP' := (hP L hL k hk).1 m hm
  have hlin : ∀ᶠ U in 𝓝[fieldSpace L m k 0] (fun _ => (1 : ComplexMatrix2)), ∀ j ≤ k,
      ∃ T : edgeFormSpace L m k 0 →ₗ[ℝ] edgeFormSpace L m k j, ∀ B : edgeFormSpace L m k 0,
        (T B : Edge L m k j → ComplexMatrix2) =
          leftDifferential (smoothingIter L m k j) U (B : Edge L m k 0 → ComplexMatrix2) := by
    have hfin : ∀ j ∈ Finset.range (k + 1), ∀ᶠ U in 𝓝[fieldSpace L m k 0]
        (fun _ => (1 : ComplexMatrix2)), j ≤ k →
          ∃ T : edgeFormSpace L m k 0 →ₗ[ℝ] edgeFormSpace L m k j,
          ∀ B : edgeFormSpace L m k 0, (T B : Edge L m k j → ComplexMatrix2) =
            leftDifferential (smoothingIter L m k j) U (B : Edge L m k 0 → ComplexMatrix2) := by
      intro j hj
      have hj' : j ≤ k := by simpa [Nat.lt_succ_iff] using hj
      exact (hobj.iterDifferential_linear j hj').mono fun U h _ => h
    filter_upwards [(Filter.eventually_all_finset _).2 hfin] with U h j hj
    exact h j (by simpa [Nat.lt_succ_iff] using hj) hj
  have hgood := (hF'.iterates_defined.and hlin).and
    (eventually_mem_nhdsWithin (a := fun _ => (1 : ComplexMatrix2)) (s := fieldSpace L m k 0))
  filter_upwards [(hcomp.tendsto 0 (Nat.zero_le k)).eventually hgood, hcomp.comp_zero_eq]
    with W hW hz j hj B
  rw [chainBottom_eq, ← hz]
  obtain ⟨⟨hI, hL'⟩, hU0⟩ := hW
  have hS := mem_meanStableFields_of_levelwise (U := chosenProlongIter L m k (Nat.zero_le k) W)
    fun i hi => ⟨(hI i hi).1, (hI i hi).2.1, (hI i hi).2.2.1⟩
  have hsp := Classical.epsilon_spec (hL' j hj)
  show ((leftDifferentialLinear (smoothingIter L m k j) _ B : edgeFormSpace L m k j) :
      Edge L m k j → ComplexMatrix2) = _
  rw [leftDifferentialLinear]
  refine (hsp B).trans ?_
  exact leftDifferential_eq_holLeftDifferential hX hE hL hm hF' hP' hU0 hS hj B.2
    fun c hc F O f w => ((hI j hj).2.2.2 B B.2 c hc).2 F O f w
end YangMills.Construction.Tower.ChainBottomDifferentials
end
