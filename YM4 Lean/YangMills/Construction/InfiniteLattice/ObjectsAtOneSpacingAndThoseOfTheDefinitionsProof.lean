import YangMills.Construction.InfiniteLattice.CoveringOfTheTorusLatticeAtOneSpacingProof
import YangMills.Construction.InfiniteLattice.DenseSequenceOfContinuousLocalFunctions
import YangMills.Construction.InfiniteLattice.ObjectsAtOneSpacingAndThoseOfTheDefinitions
import YangMills.Construction.InfiniteLattice.TorusStatesAreTheVolumeLimitPointsProof
import YangMills.Construction.InfiniteLattice.WeakTopologyAndSequentialCompactnessOfTheStates
import YangMills.Construction.Lattice.NumbersAndConfigurationsOfTheTorusLattices
import YangMills.Construction.LawInAState.TheLeastTorusLawUnderLatticeIsometriesProof
import YangMills.Construction.Torus.RescalingLiftsAndFunctionNorms
import Mathlib
set_option autoImplicit false
open MeasureTheory Filter Set
open scoped Topology
noncomputable section
namespace YangMills.Construction.InfiniteLattice.FixedSpacing
open YangMills.Construction.GibbsAtFixedSpacing
open YangMills.Construction.InfiniteLattice
open YangMills.Construction.PeriodicLattice (torusSide torusSides meshSize FourTorus sublattice
  torusProjHom torusDist CompactGaugeField wilsonGibbsMeasure observableExpanded
  torusUrsellFunction IsBoundedFamily)
open YangMills.Construction.TorusMetric (Torus4 torusProj euclidNormVec torusEuclidNorm)
open YangMills.Construction.TestFunctions (latticeTranslate HasSeparatedSupportsTorus IsLipschitzFor)
open YangMills.Construction.LiftFormation (torusWilson)
theorem torusSide_pos_of_pos {L : ℕ} (hL : 0 < L) (m : ℕ) : 0 < torusSide L m := by apply _root_.YangMills.SharedProofs.p34445 <;> assumption
theorem meshSize_pos_of_pos {L : ℕ} (hL : 0 < L) (j : ℤ) : 0 < meshSize L j := by apply _root_.YangMills.SharedProofs.p6250 <;> assumption
theorem torusProjHom_surjective (L m : ℕ) :
    Function.Surjective (torusProjHom L m) := by
  intro u
  have h : ∀ μ, ∃ x : ℝ, (x : AddCircle (torusSide L m)) = u μ := fun μ =>
    QuotientAddGroup.mk_surjective (u μ)
  choose x hx using h
  exact ⟨x, funext hx⟩
theorem torusProjHom_ker_eq (L m : ℕ) :
    (torusProjHom L m).ker = latticeSubgroup (2 * (L : ℝ) ^ m) := by
  ext x
  constructor
  · intro hx
    have h : ∀ μ, ∃ n : ℤ, x μ = (n : ℝ) * (2 * (L : ℝ) ^ m) := fun μ => by
      have h0 : ((x μ : ℝ) : AddCircle (torusSide L m)) = 0 := congrFun hx μ
      obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff (torusSide L m)).mp h0
      exact ⟨n, by rw [← hn, zsmul_eq_mul]; rfl⟩
    choose n hn using h
    exact ⟨n, hn⟩
  · rintro ⟨n, hn⟩
    refine funext fun μ => ?_
    change ((x μ : ℝ) : AddCircle (torusSide L m)) = 0
    exact (AddCircle.coe_eq_zero_iff (torusSide L m)).mpr ⟨n μ, by
      rw [hn, zsmul_eq_mul]; rfl⟩
theorem torusAndLatticeIdentification_holds {L : ℕ} (hL : 0 < L) (m K : ℕ) :
    TorusAndLatticeIdentification L m K := by
  refine ⟨rfl, torusProjHom_surjective L m, torusProjHom_ker_eq L m,
    fun x y => ⟨PeriodicLattice.isLeast_torusDist_torusProj hL x y, rfl⟩, ?_⟩
  rw [PeriodicLattice.sublattice_eq_map_latticeSubgroup]
  rfl
theorem torusDist_le_two_mul_norm (L m : ℕ) (u v : FourTorus L m) :
    torusDist L m u v ≤ 2 * ‖u - v‖ :=
  TorusAnalysis.torusEuclidNorm_le_two_mul_pi_norm (u - v)
theorem norm_le_half_torusSide {L : ℕ} (hL : 0 < L) (m : ℕ) (u : FourTorus L m) :
    ‖u‖ ≤ torusSide L m / 2 := by
  refine (pi_norm_le_iff_of_nonneg (by have := torusSide_pos_of_pos hL m; positivity)).mpr
    fun μ => ?_
  have h := AddCircle.norm_le_half_period (torusSide L m) (x := u μ)
    (torusSide_pos_of_pos hL m).ne'
  rwa [abs_of_pos (torusSide_pos_of_pos hL m)] at h
theorem isBoundedFun_of_isLipschitzFor {L m : ℕ} (hL : 0 < L) {h : FourTorus L m → ℝ}
    (hh : IsLipschitzFor (torusDist L m) h) : TestFunctions.IsBoundedFun h := by
  obtain ⟨C, hC, hb⟩ := hh
  refine ⟨‖h 0‖ + C * torusSide L m, fun u => ?_⟩
  have h₁ := hb u 0
  have h₂ := torusDist_le_two_mul_norm L m u 0
  have h₃ := norm_le_half_torusSide hL m (u - 0)
  have h₄ : torusDist L m u 0 ≤ torusSide L m := by linarith
  have h₅ : ‖h u‖ ≤ ‖h 0‖ + ‖h u - h 0‖ := by
    have := norm_add_le (h 0) (h u - h 0)
    simpa using this
  have h₆ := mul_le_mul_of_nonneg_left h₄ hC
  linarith
theorem continuous_of_isLipschitzFor {L m : ℕ} {h : FourTorus L m → ℝ}
    (hh : IsLipschitzFor (torusDist L m) h) : Continuous h := by
  obtain ⟨C, hC, hb⟩ := hh
  refine (LipschitzWith.of_dist_le_mul (K := (C * 2).toNNReal) fun u v => ?_).continuous
  rw [Real.coe_toNNReal _ (by positivity), dist_eq_norm, dist_eq_norm]
  have h₂ := torusDist_le_two_mul_norm L m u v
  calc ‖h u - h v‖ ≤ C * torusDist L m u v := hb u v
    _ ≤ C * (2 * ‖u - v‖) := mul_le_mul_of_nonneg_left h₂ hC
    _ = C * 2 * ‖u - v‖ := by ring
theorem torusUrsellIdentification_holds {L : ℕ} (hL : 0 < L) (m K : ℕ) (β : ℝ) :
    TorusUrsellIdentification L m K β := by
  refine ⟨fun n h _ => rfl, fun n h _ hLip hsep =>
    ⟨⟨fun i => isBoundedFun_of_isLipschitzFor hL (hLip i), fun i => ?_, hsep⟩, rfl⟩⟩
  have : Fact (0 < torusSide L m) := ⟨torusSide_pos_of_pos hL m⟩
  exact (continuous_of_isLipschitzFor (hLip i)).measurable
theorem torusSide_injective {L : ℕ} (hL : 2 ≤ L) : Function.Injective (torusSide L) := by
  intro m m' h
  have h₁ : (L : ℝ) ^ m = (L : ℝ) ^ m' := by
    unfold torusSide at h
    linarith
  have h₂ : L ^ m = L ^ m' := by exact_mod_cast h₁
  exact Nat.pow_right_injective hL h₂
theorem bijOn_torusSide {L : ℕ} (hL : 2 ≤ L) : BijOn (torusSide L) {m | 0 < m} (torusSides L) :=
  ⟨fun m hm => ⟨m, hm, rfl⟩, (torusSide_injective hL).injOn,
    fun _ ⟨m, hm, h⟩ => ⟨m, hm, h.symm⟩⟩
theorem tendsto_iff_tendstoWeak {a : ℝ} (ν : ℕ → BorelProb a) (ν₀ : BorelProb a) :
    Tendsto ν atTop (𝓝 ν₀) ↔ BorelProb.TendstoWeak ν ν₀ := by
  have h : (𝓝 ν₀ : Filter (BorelProb a)) = ⨅ F : continuousFns a,
      Filter.comap (fun ν : BorelProb a => ν.integral F.1) (𝓝 (ν₀.integral F.1)) := by
    change @nhds _ (⨅ F : continuousFns a,
      TopologicalSpace.induced (fun ν : BorelProb a => ν.integral F.1) inferInstance) ν₀ = _
    rw [nhds_iInf]
    exact iInf_congr fun F => nhds_induced _ _
  rw [h, tendsto_iInf]
  constructor
  · intro H F hF
    exact tendsto_comap_iff.mp (H ⟨F, hF⟩)
  · intro H F
    exact tendsto_comap_iff.mpr (H F.1 F.2)
theorem infiniteLatticeSpaceIdentification_holds (L K : ℕ) :
    InfiniteLatticeSpaceIdentification L K :=
  ⟨rfl, Topology.IsEmbedding.subtypeVal, Subtype.range_coe, tendsto_iff_tendstoWeak⟩
section Covering
variable {L m : ℕ} {j : ℤ}
theorem projectPoint_map_add (x y : LatticePoint (meshSize L j)) :
    projectPoint L m j (x + y) = projectPoint L m j x + projectPoint L m j y := by apply _root_.YangMills.Construction.InfiniteLattice.TorusCovering.projectPoint_add <;> assumption
theorem exists_projectPoint_eq (z : PeriodicLattice.Site L m j) :
    ∃ x : LatticePoint (meshSize L j), projectPoint L m j x = z := by apply _root_.YangMills.Construction.InfiniteLattice.TorusCovering.exists_projectPoint_eq <;> assumption
theorem exists_projectLink_eq (c : PeriodicLattice.Bond L m j) :
    ∃ b : Link (meshSize L j), projectLink L m j b = c := by
  obtain ⟨x, hx⟩ := exists_projectPoint_eq c.source
  obtain ⟨μ, h | h⟩ := c.isNeighbour
  · refine ⟨⟨x, x + axisStep _ μ, μ, Or.inl (by abel)⟩, PeriodicLattice.Bond.ext hx ?_⟩
    change projectPoint L m j (x + axisStep _ μ) = c.target
    rw [projectPoint_map_add, projectPoint_axisStep, hx, ← h]
    abel
  · refine ⟨⟨x, x - axisStep _ μ, μ, Or.inr (by abel)⟩, PeriodicLattice.Bond.ext hx ?_⟩
    change projectPoint L m j (x - axisStep _ μ) = c.target
    rw [projectPoint_sub, projectPoint_axisStep, hx, sub_eq_add_neg, ← h]
    abel
theorem exists_torusSide_multiple_of_projectPoint_eq (x y : LatticePoint (meshSize L j))
    (h : projectPoint L m j x = projectPoint L m j y) :
    ∃ n : Fin 4 → ℤ, ∀ μ, ((y - x : LatticePoint (meshSize L j)) : AmbientSpace) μ =
      (n μ : ℝ) * torusSide L m := by
  have h₁ : torusProj (torusSide L m) (y : AmbientSpace) =
      torusProj (torusSide L m) (x : AmbientSpace) :=
    congrArg Subtype.val h.symm
  obtain ⟨k, hk⟩ := TestFunctions.exists_latticeTranslate_of_torusProj_eq h₁
  refine ⟨k, fun μ => ?_⟩
  have h₂ := congrFun hk μ
  simp only [Pi.add_apply, TestFunctions.latticeTranslate] at h₂
  simp only [AddSubgroup.coe_sub, Pi.sub_apply, h₂]
  ring
theorem projectLink_shift_linkMap (v : LatticePoint (meshSize L j))
    (hv : ∃ n : Fin 4 → ℤ, ∀ μ, (v : AmbientSpace) μ = (n μ : ℝ) * torusSide L m)
    (b : Link (meshSize L j)) :
    projectLink L m j ((shift v).linkMap b) = projectLink L m j b := by
  obtain ⟨n, hn⟩ := hv
  have hvec : (v : AmbientSpace) = latticeTranslate (torusSide L m) n := funext fun μ => by
    simp only [latticeTranslate, hn, mul_comm]
  have hpt : ∀ x : LatticePoint (meshSize L j),
      projectPoint L m j ((shift v).pointMap x) = projectPoint L m j x := fun x =>
    Subtype.ext (by
      change torusProj (torusSide L m) ((x : AmbientSpace) + (v : AmbientSpace)) = _
      rw [hvec]
      exact TestFunctions.torusProj_add_latticeTranslate _ _ _)
  exact PeriodicLattice.Bond.ext (hpt b.initial) (hpt b.terminal)
theorem abs_terminal_sub_initial_le (hL : 0 < L) (b : Link (meshSize L j)) (κ : Fin 4) :
    |((b.terminal - b.initial : LatticePoint (meshSize L j)) : AmbientSpace) κ| ≤ meshSize L j := by
  have hstep : ∀ μ, |((axisStep (meshSize L j) μ : LatticePoint (meshSize L j)) : AmbientSpace) κ| ≤
      meshSize L j := fun μ => by
    have ha := meshSize_pos_of_pos hL j
    change |(Pi.single μ (meshSize L j) : AmbientSpace) κ| ≤ _
    by_cases h : κ = μ
    · subst h
      simp [abs_of_pos ha]
    · simp [Pi.single_eq_of_ne h, ha.le]
  obtain ⟨μ, h | h⟩ := b.isAdjacent
  · rw [h]
    exact hstep μ
  · rw [h]
    simpa using hstep μ
theorem exists_shift_linkMap_eq (hL : 0 < L) (hs : meshSize L j < torusSide L m / 2)
    {b b' : Link (meshSize L j)} (h : projectLink L m j b = projectLink L m j b') :
    ∃ v : LatticePoint (meshSize L j),
      (∃ n : Fin 4 → ℤ, ∀ μ, (v : AmbientSpace) μ = (n μ : ℝ) * torusSide L m) ∧
        (shift v).linkMap b = b' := by
  have ht : projectPoint L m j b.initial = projectPoint L m j b'.initial :=
    congrArg PeriodicLattice.Bond.source h
  have hh : projectPoint L m j b.terminal = projectPoint L m j b'.terminal :=
    congrArg PeriodicLattice.Bond.target h
  refine ⟨b'.initial - b.initial, exists_torusSide_multiple_of_projectPoint_eq _ _ ht, ?_⟩
  have hd : projectPoint L m j (b'.terminal - b'.initial) =
      projectPoint L m j (b.terminal - b.initial) := by
    rw [projectPoint_sub, projectPoint_sub, ht, hh]
  obtain ⟨n, hn⟩ := exists_torusSide_multiple_of_projectPoint_eq _ _ hd.symm
  have hzero : ∀ μ, n μ = 0 := fun μ => by
    by_contra hne
    obtain ⟨a₁, a₂⟩ := abs_le.mp (abs_terminal_sub_initial_le hL b μ)
    obtain ⟨a₃, a₄⟩ := abs_le.mp (abs_terminal_sub_initial_le hL b' μ)
    have h₃ : ((b'.terminal - b'.initial : LatticePoint (meshSize L j)) : AmbientSpace) μ -
        ((b.terminal - b.initial : LatticePoint (meshSize L j)) : AmbientSpace) μ =
        (n μ : ℝ) * torusSide L m := hn μ
    have h₄ : |(n μ : ℝ) * torusSide L m| ≤ 2 * meshSize L j := by
      rw [← h₃, abs_le]
      constructor <;> linarith
    have h₅ : (1 : ℝ) ≤ |(n μ : ℝ)| := by
      have := Int.one_le_abs hne
      exact_mod_cast this
    have hp := torusSide_pos_of_pos hL m
    rw [abs_mul, abs_of_pos hp] at h₄
    nlinarith
  have he : b'.terminal - b'.initial = b.terminal - b.initial := by
    refine Subtype.ext (funext fun μ => ?_)
    have h₃ : ((b'.terminal - b'.initial : LatticePoint (meshSize L j)) : AmbientSpace) μ -
        ((b.terminal - b.initial : LatticePoint (meshSize L j)) : AmbientSpace) μ =
        (n μ : ℝ) * torusSide L m := hn μ
    rw [hzero μ] at h₃
    simp only [Int.cast_zero, zero_mul] at h₃
    linarith
  refine Link.ext (Subtype.ext ?_) (Subtype.ext ?_)
  · change (b.initial : AmbientSpace) +
      ((b'.initial - b.initial : LatticePoint (meshSize L j)) : AmbientSpace) =
      (b'.initial : AmbientSpace)
    simp
  · change (b.terminal : AmbientSpace) +
      ((b'.initial - b.initial : LatticePoint (meshSize L j)) : AmbientSpace) =
      (b'.terminal : AmbientSpace)
    have h₆ : b'.terminal = b.terminal + (b'.initial - b.initial) := by
      have : b'.terminal = (b'.terminal - b'.initial) + b'.initial := by abel
      rw [this, he]
      abel
    rw [h₆]
    rfl
end Covering
theorem bijOn_liftCompactField {L m : ℕ} {j : ℤ} (hL : 0 < L)
    (hs : meshSize L j < torusSide L m / 2) :
    BijOn (liftCompactField : CompactGaugeField L m j → _) univ (periodicFields L m j) := by
  refine ⟨fun U _ v hv => Subtype.ext (funext fun b => ?_), fun U _ U' _ h => ?_, fun ω hω => ?_⟩
  · change liftCompactField U ((shift v).linkMap b) = liftCompactField U b
    rw [liftCompactField_apply, liftCompactField_apply, projectLink_shift_linkMap v hv]
  · refine Subtype.ext (funext fun c => ?_)
    obtain ⟨b, rfl⟩ := exists_projectLink_eq c
    have h₁ := congrArg (fun W : GaugeField (meshSize L j) => W b) h
    simp only [liftCompactField_apply] at h₁
    exact congrArg Subtype.val h₁
  · have key : ∀ b b' : Link (meshSize L j),
        projectLink L m j b = projectLink L m j b' → ω b = ω b' := fun b b' h => by
      obtain ⟨v, hv, rfl⟩ := exists_shift_linkMap_eq hL hs h
      have h₁ := congrArg (fun W : GaugeField (meshSize L j) => W b) (hω v hv)
      exact h₁.symm
    choose lift hlift using exists_projectLink_eq (L := L) (m := m) (j := j)
    refine ⟨CompactGaugeField.ofLinkValues (fun c => ω (lift c)) fun c => ?_,
      mem_univ _, Subtype.ext (funext fun b => ?_)⟩
    · rw [← ω.2 (lift c)]
      exact key _ _ (by rw [hlift, projectLink_opposite, hlift])
    · change liftCompactField _ b = ω b
      rw [liftCompactField_apply, CompactGaugeField.linkValue_ofLinkValues]
      exact key _ _ (hlift _)
def standingOf {L K m : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L) (hK : 0 < K)
    (hm : 0 < m) : Conventions.StandingParameters :=
  ⟨L, hL, ⟨K, hK⟩, ⟨m, hm⟩⟩
theorem liftedWilsonMeasureIdentification_holds (hExt : LiftFormation.Statement)
    (hFacts : LatticeCounts.torusLatticeFacts) {L K m : ℕ}
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hK : 0 < K) (hm : 0 < m) {β : ℝ}
    (hβ : 0 < β) : LiftedWilsonMeasureIdentification L m K β := by
  have hL₀ : 0 < L := by have := hL.2; omega
  obtain ⟨-, -, hM⟩ := hExt (standingOf hL hK hm) β hβ
  have hs : meshSize L (K : ℤ) < torusSide L m / 2 := (hFacts (standingOf hL hK hm)).2.2.1.2.2
  exact ⟨liftCompactField_apply, hM.2.2.1, bijOn_liftCompactField hL₀ hs, hM.2.2.2.1⟩
theorem isBoundedOfBoundedSupport_iff_hasCompactSupport (f : AmbientSpace → ℂ)
    (hf : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C) : IsBoundedOfBoundedSupport f ↔ HasCompactSupport f := by
  constructor
  · intro h
    exact Metric.isCompact_of_isClosed_isBounded (isClosed_tsupport f) h.2.closure
  · intro h
    exact ⟨hf, h.isCompact.isBounded.subset (subset_tsupport f)⟩
theorem cutoffSmearedEnergy_eq_smearedEnergy {L K : ℕ} (f : AmbientSpace → ℂ)
    (U : GaugeField (meshSize L (K : ℤ))) :
    cutoffSmearedEnergy (L := L) (K := K) f U = smearedEnergy f U := by
  unfold cutoffSmearedEnergy
  rw [← plaquetteSmearing_eq_smearedEnergy_of_support]
  refine finsum_congr fun p => ?_
  rw [Complex.real_smul, mul_comm]
theorem ursellFunctionOfFamily_eq_mixedLogDerivative {L K n : ℕ}
    (ν : Measure (RefinedGaugeField L K)) (f : Fin n → AmbientSpace → ℝ) :
    ursellFunctionOfFamily ν f = mixedLogDerivative ν f := by
  unfold ursellFunctionOfFamily mixedLogDerivative
  rw [Cumulants.mixedCumulant_eq_iteratedFDeriv]
  have h : (fun z : Fin n → ℂ => Cumulants.principalLog
        (Cumulants.laplaceTransform ν (fun j U => cutoffSmearedEnergyRe (f j) U) z)) =
      fun z => Cumulants.principalLog (Cumulants.expectationC ν fun U =>
        Complex.exp (∑ i, z i * cutoffSmearedEnergy (fun x => (f i x : ℂ)) U)) := by
    funext z
    unfold Cumulants.laplaceTransform
    simp only [ofReal_cutoffSmearedEnergyRe]
  rw [h]
theorem ursellFunctionOfFamily_eq_smearedEnergyCumulant {L K n : ℕ}
    (ν : Measure (RefinedGaugeField L K)) (f : Fin n → AmbientSpace → ℝ) :
    ursellFunctionOfFamily ν f = smearedEnergyCumulant ν f := by
  unfold ursellFunctionOfFamily smearedEnergyCumulant
  congr 1
  funext j U
  exact cutoffSmearedEnergyRe_eq_smearedEnergy (f j) U
theorem observableAndUrsellIdentification_holds (L K : ℕ) :
    ObservableAndUrsellIdentification L K :=
  ⟨isBoundedOfBoundedSupport_iff_hasCompactSupport,
    fun f _ U => cutoffSmearedEnergy_eq_smearedEnergy f U,
    fun _ _ f _ _ => ⟨ursellFunctionOfFamily_eq_mixedLogDerivative _ f,
      (ursellFunctionOfFamily_eq_mixedLogDerivative _ f).symm.trans
        (ursellFunctionOfFamily_eq_smearedEnergyCumulant _ f)⟩⟩
section Limits
variable {a : ℝ}
theorem compactSpace_gaugeField (a : ℝ) : CompactSpace (GaugeField a) := by apply _root_.YangMills.SharedProofs.p823 <;> assumption
theorem exists_norm_bound_of_continuous {F : GaugeField a → ℂ} (hF : Continuous F) :
    ∃ C : ℝ, ∀ U, ‖F U‖ ≤ C := by
  have := compactSpace_gaugeField a
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hF.continuousOn
  exact ⟨C, fun U => hC U (mem_univ U)⟩
theorem integrable_of_continuous_gaugeField (ν : BorelProb a) {F : GaugeField a → ℂ}
    (hF : Continuous F) : Integrable F (ν : GaugeFieldProbability a).1 := by
  have hp : IsProbabilityMeasure (ν : GaugeFieldProbability a).1 :=
    (ν : GaugeFieldProbability a).2
  obtain ⟨C, hC⟩ := exists_norm_bound_of_continuous hF
  exact Integrable.of_bound hF.aestronglyMeasurable C (Filter.Eventually.of_forall hC)
theorem norm_integral_sub_le_of_pointwise (ν : BorelProb a) {F G : GaugeField a → ℂ}
    (hF : Continuous F) (hG : Continuous G) {B : ℝ} (hB : ∀ U, ‖F U - G U‖ ≤ B) :
    ‖ν.integral F - ν.integral G‖ ≤ B := by
  have hp : IsProbabilityMeasure (ν : GaugeFieldProbability a).1 :=
    (ν : GaugeFieldProbability a).2
  have h : ν.integral F - ν.integral G =
      ∫ U, (F U - G U) ∂(ν : GaugeFieldProbability a).1 :=
    (integral_sub (integrable_of_continuous_gaugeField ν hF)
      (integrable_of_continuous_gaugeField ν hG)).symm
  rw [h]
  have h₁ := norm_integral_le_of_norm_le_const (μ := (ν : GaugeFieldProbability a).1)
    (Filter.Eventually.of_forall hB)
  simpa using h₁
theorem norm_le_supNorm {F : GaugeField a → ℂ} (hF : Continuous F) (U : GaugeField a) :
    ‖F U‖ ≤ observableSupNorm F := by
  obtain ⟨C, hC⟩ := exists_norm_bound_of_continuous hF
  exact le_ciSup (f := fun U => ‖F U‖) ⟨C, by rintro _ ⟨U, rfl⟩; exact hC U⟩ U
end Limits
theorem tendsto_torusSide_succ {L : ℕ} (hL : 2 ≤ L) :
    Tendsto (fun i : ℕ => torusSide L (i + 1)) atTop atTop := by
  refine tendsto_atTop_mono (fun i => ?_) tendsto_natCast_atTop_atTop
  have h₁ : i + 1 < L ^ (i + 1) := Nat.lt_pow_self (by omega)
  have h₂ : ((i : ℝ) + 1) < (L : ℝ) ^ (i + 1) := by exact_mod_cast h₁
  unfold torusSide
  linarith
theorem isWeakLimitAlongTorusSides_of_isTorusWeakClusterPoint
    (hDense : CylinderFunctionsHaveDenseSequence)
    (hWeak : WeakTopologyAndSeqCompactness) {L K : ℕ}
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hK : 0 < K) {β : ℝ} (hβ : 0 < β)
    (ν : BorelProb (meshSize L (K : ℤ))) (hν : IsTorusWeakClusterPoint L K β ν) :
    IsWeakLimitAlongTorusSides L K β ν := by
  have hL₂ : 2 ≤ L := by have := hL.2; omega
  have hF' : ∃ F : ℕ+ → GaugeField (meshSize L (K : ℤ)) → ℂ, (∀ k, Continuous (F k)) ∧
      ∀ H : C(GaugeField (meshSize L (K : ℤ)), ℂ), ∀ ε : ℝ, 0 < ε →
        ∃ k, observableSupNorm (fun U => H U - F k U) < ε := by
    obtain ⟨F, h₁, h₂⟩ := hDense ⟨standingOf hL hK one_pos, β, hβ⟩
    exact ⟨F, fun k => (h₁ k).1, h₂⟩
  obtain ⟨F, hFc, hFd⟩ := hF'
  have hW := hWeak (standingOf hL hK one_pos) (meshSize L (K : ℤ)) rfl
  let Fc : ℕ+ → C(GaugeField (meshSize L (K : ℤ)), ℂ) := fun k => ⟨F k, hFc k⟩
  let B : ℕ → Set (BorelProb (meshSize L (K : ℤ))) := fun i =>
    ν.basicWeakSet (q := i + 1) (fun r => Fc ⟨r.1 + 1, Nat.succ_pos _⟩) (1 / ((i : ℝ) + 1))
  have hB : ∀ i, B i ∈ 𝓝 ν := fun i => by
    obtain ⟨ho, hm⟩ := (hW.1 ν).2 (i + 1) (by omega) (fun r => Fc ⟨r.1 + 1, Nat.succ_pos _⟩)
      (1 / ((i : ℝ) + 1)) (by positivity)
    exact ho.mem_nhds hm
  have hchoice := fun i : ℕ => hν (B i) (hB i) (torusSide L (i + 1)) ⟨i + 1, Nat.succ_pos i, rfl⟩
  choose m hm hle ρ hρB hρ using hchoice
  refine ⟨fun i => torusSide L (m i), ρ, ⟨fun i => ⟨m i, hm i, rfl⟩,
    tendsto_atTop_mono hle (tendsto_torusSide_succ hL₂)⟩, fun i => ⟨m i, hm i, rfl, hρ i⟩, ?_⟩
  intro G hG
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hε₃ : 0 < ε / 3 := by positivity
  obtain ⟨k, hk⟩ := hFd ⟨G, hG⟩ (ε / 3) hε₃
  have hGk : ∀ U, ‖G U - F k U‖ ≤ ε / 3 := fun U =>
    (norm_le_supNorm (hG.sub (hFc k)) U).trans hk.le
  have hkG : ∀ U, ‖F k U - G U‖ ≤ ε / 3 := fun U => by
    rw [norm_sub_rev]
    exact hGk U
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hε₃
  refine ⟨max N (k : ℕ), fun i hi => ?_⟩
  have hiN : N ≤ i := (le_max_left _ _).trans hi
  have hik : (k : ℕ) ≤ i := (le_max_right _ _).trans hi
  have hk₀ : 0 < (k : ℕ) := k.pos
  have hr : (k : ℕ) - 1 < i + 1 := by omega
  have h₀ : ‖(ρ i).integral (Fc ⟨((k : ℕ) - 1) + 1, Nat.succ_pos _⟩) -
      ν.integral (Fc ⟨((k : ℕ) - 1) + 1, Nat.succ_pos _⟩)‖ < 1 / ((i : ℝ) + 1) :=
    hρB i ⟨(k : ℕ) - 1, hr⟩
  have he : (⟨((k : ℕ) - 1) + 1, Nat.succ_pos _⟩ : ℕ+) = k :=
    PNat.eq (by change (k : ℕ) - 1 + 1 = k; omega)
  rw [he] at h₀
  have h₁ : ‖(ρ i).integral (F k) - ν.integral (F k)‖ < ε / 3 := by
    refine lt_of_lt_of_le h₀ (le_trans ?_ hN.le)
    refine one_div_le_one_div_of_le (by positivity) ?_
    have : (N : ℝ) ≤ i := by exact_mod_cast hiN
    linarith
  have h₂ := norm_integral_sub_le_of_pointwise (ρ i) hG (hFc k) hGk
  have h₃ := norm_integral_sub_le_of_pointwise ν (hFc k) hG hkG
  rw [dist_eq_norm]
  calc ‖(ρ i).integral G - ν.integral G‖ =
      ‖((ρ i).integral G - (ρ i).integral (F k)) + ((ρ i).integral (F k) - ν.integral (F k)) +
        (ν.integral (F k) - ν.integral G)‖ := by
        congr 1
        abel
    _ ≤ ‖(ρ i).integral G - (ρ i).integral (F k)‖ + ‖(ρ i).integral (F k) - ν.integral (F k)‖ +
        ‖ν.integral (F k) - ν.integral G‖ := norm_add₃_le
    _ < ε := by linarith
theorem isTorusWeakClusterPoint_of_isWeakLimitAlongTorusSides {L K : ℕ} {β : ℝ}
    (ν : BorelProb (meshSize L (K : ℤ))) (hν : IsWeakLimitAlongTorusSides L K β ν) :
    IsTorusWeakClusterPoint L K β ν := by
  obtain ⟨ℓ, ρ, hT, hmem, hconv⟩ := hν
  intro 𝒰 h𝒰 ℓ₀ _
  have h₁ := (tendsto_iff_tendstoWeak ρ ν).mpr hconv
  have h₂ := h₁.eventually h𝒰
  have h₃ := hT.2.eventually_ge_atTop ℓ₀
  obtain ⟨i, hi₁, hi₂⟩ := (h₂.and h₃).exists
  obtain ⟨m, hm, hℓ, hμ⟩ := hmem i
  exact ⟨m, hm, hℓ ▸ hi₂, ρ i, hi₁, hμ⟩
theorem fixedSpacingDictionary_holds (hExt : LiftFormation.Statement)
    (hFacts : LatticeCounts.torusLatticeFacts)
    (hDense : CylinderFunctionsHaveDenseSequence)
    (hWeak : WeakTopologyAndSeqCompactness) : FixedSpacingDictionary := by
  intro L K hL hK β hβ
  have hL₂ : 2 ≤ L := by have := hL.2; omega
  have hL₀ : 0 < L := by omega
  have hlim : ∀ ν : BorelProb (meshSize L (K : ℤ)),
      IsTorusWeakClusterPoint L K β ν ↔ IsWeakLimitAlongTorusSides L K β ν := fun ν =>
    ⟨isWeakLimitAlongTorusSides_of_isTorusWeakClusterPoint hDense hWeak hL hK hβ ν,
      isTorusWeakClusterPoint_of_isWeakLimitAlongTorusSides ν⟩
  exact ⟨⟨fun m _ => ⟨torusAndLatticeIdentification_holds hL₀ m K,
      torusUrsellIdentification_holds hL₀ m K β⟩, bijOn_torusSide hL₂⟩,
    ⟨infiniteLatticeSpaceIdentification_holds L K,
      fun m hm => liftedWilsonMeasureIdentification_holds hExt hFacts hL hK hm hβ,
      observableAndUrsellIdentification_holds L K⟩,
    hlim, Set.ext hlim⟩
end YangMills.Construction.InfiniteLattice.FixedSpacing
end
