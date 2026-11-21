import YangMills.Construction.TransferOperators.ConfigurationsOfACubicTorusByLayersProof
import YangMills.Construction.InfiniteLattice.ElementaryFactsOfBondsSpecificationAndGaugeTransformations
import YangMills.Construction.InfiniteLattice.EquilibriumEquationsGaugeInvarianceAndCompactness
import YangMills.Construction.InfiniteLattice.GibbsStatesByWindowsAndPeriodGroups
import YangMills.Construction.InfiniteLattice.PositivityAtAMirrorExtendsFromContinuousLocalObservablesProof
import YangMills.Construction.InfiniteLattice.TwoMirrorsOfOneFamilyGiveATranslation
import YangMills.Construction.TransferOperators.GaugeAveragesOfFunctionsOfLayers
import YangMills.Construction.TransferOperators.InvarianceOnThePolynomialsOfSymmetricStacks
import YangMills.Construction.TransferOperators.PeriodicGibbsStatesAreInvariantUnderLinkMirrors
import YangMills.Construction.TransferOperators.TemporalGaugeOfAStack
import Mathlib
set_option autoImplicit false
open MeasureTheory Filter Topology
noncomputable section
namespace YangMills.Construction.TransferOperators.PeriodicGibbsLinkSymmetry
open InfiniteLattice SpinHarmonics
open PeriodicLattice (coordVec)
def LinkInCenteredStack {μ : Fin 4} (i k : ℤ) (v : Set (SliceSite μ)) (b : Link 1) : Prop :=
  (∃ (j : ℤ) (c : SliceLink μ), i - k + 1 ≤ j ∧ j ≤ i + k ∧ c ∈ linksWithin v ∧
      b = (spatialLink μ j c).1) ∨
    ∃ (j : ℤ) (y : SliceSite μ), i - k + 1 ≤ j ∧ j < i + k ∧ y ∈ v ∧ b = (temporalLink μ j y).1
theorem LinkInCenteredStack.mono {μ : Fin 4} {i k k' : ℤ} {v v' : Set (SliceSite μ)} {b : Link 1}
    (h : LinkInCenteredStack i k v b) (hk : k ≤ k') (hv : v ⊆ v') : LinkInCenteredStack i k' v' b := by
  rcases h with ⟨j, c, h₁, h₂, h₃, rfl⟩ | ⟨j, y, h₁, h₂, h₃, rfl⟩
  · exact Or.inl ⟨j, c, by omega, by omega, ⟨hv h₃.1, hv h₃.2⟩, rfl⟩
  · exact Or.inr ⟨j, y, by omega, by omega, hv h₃, rfl⟩
theorem level_smul_add_slicePart (μ : Fin 4) (x : LatticePoint 1) :
    level μ x • axisStep 1 μ + (slicePart μ x : LatticePoint 1) = x := by apply _root_.YangMills.Construction.TransferOperators.SliceDecomposition.pointAtLevel_level_slicePart <;> assumption
theorem exists_linkInCenteredStack_of_isPositivelyOriented (μ : Fin 4) (i : ℤ) {b : Link 1}
    (hb : b.IsPositivelyOriented) :
    ∃ (k : ℤ) (v : Set (SliceSite μ)), 1 ≤ k ∧ v.Finite ∧ LinkInCenteredStack i k v b := by
  obtain ⟨ρ, hρ⟩ := hb
  have hx := level_smul_add_slicePart μ b.initial
  generalize level μ b.initial = j at hx
  generalize slicePart μ b.initial = y at hx
  have hterm : b.terminal = b.initial + axisStep 1 ρ := by rw [← hρ]; abel
  have h₁ := le_abs_self (j - i)
  have h₂ := neg_abs_le (j - i)
  have h₃ := abs_nonneg (j - i)
  by_cases h : ρ = μ
  · subst h
    refine ⟨|j - i| + 2, {y}, by omega, Set.finite_singleton _, Or.inr
      ⟨j, y, by omega, by omega, rfl, ?_⟩⟩
    refine Link.ext hx.symm ?_
    change b.terminal = pointAtLevel ρ (j + 1) y
    rw [pointAtLevel_succ, hterm]
    exact congrArg (· + axisStep 1 ρ) hx.symm
  · have hc : (spatialLink μ j (SliceLink.ofAxis y ρ h)).1 = b := by
      refine Link.ext hx ?_
      change j • axisStep 1 μ + ((y : LatticePoint 1) + axisStep 1 ρ) = b.terminal
      rw [← add_assoc, hx, hterm]
    refine ⟨|j - i| + 2, {(SliceLink.ofAxis y ρ h).source, (SliceLink.ofAxis y ρ h).target},
      by omega, Set.toFinite _, Or.inl ⟨j, SliceLink.ofAxis y ρ h, by omega, by omega,
      ⟨by simp, by simp⟩, hc.symm⟩⟩
theorem exists_centeredStack_of_finite (μ : Fin 4) (i : ℤ) (T : Finset (Link 1))
    (hT : ∀ b ∈ T, b.IsPositivelyOriented) :
    ∃ (k : ℤ) (v : Set (SliceSite μ)), 1 ≤ k ∧ v.Finite ∧ (linksWithin v).Nonempty ∧
      ∀ b ∈ T, LinkInCenteredStack i k v b := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    obtain ⟨ρ, hρ⟩ := exists_ne μ
    exact ⟨1, {(SliceLink.ofAxis 0 ρ hρ).source, (SliceLink.ofAxis 0 ρ hρ).target}, le_rfl,
      Set.toFinite _, ⟨SliceLink.ofAxis 0 ρ hρ, by simp, by simp⟩, by simp⟩
  | insert a s ha ih =>
    obtain ⟨k, v, hk, hv, hne, hs⟩ := ih fun b hb => hT b (Finset.mem_insert_of_mem hb)
    obtain ⟨k', v', hk', hv', ha'⟩ :=
      exists_linkInCenteredStack_of_isPositivelyOriented μ i (hT a (Finset.mem_insert_self _ _))
    refine ⟨max k k', v ∪ v', le_trans hk (le_max_left _ _), hv.union hv', ?_, ?_⟩
    · obtain ⟨c, hc⟩ := hne
      exact ⟨c, Or.inl hc.1, Or.inl hc.2⟩
    · intro b hb
      rcases Finset.mem_insert.mp hb with rfl | hb
      · exact ha'.mono (le_max_right _ _) Set.subset_union_right
      · exact (hs b hb).mono (le_max_left _ _) Set.subset_union_left
theorem integrable_of_isBoundedObservable {ρ : Measure (GaugeField 1)} [IsProbabilityMeasure ρ]
    {F : GaugeField 1 → ℂ} (hF : IsBoundedObservable F) : Integrable F ρ := by apply _root_.YangMills.Construction.InfiniteLattice.ReflectionPositivityExtension.integrable_of_isBoundedObservable <;> assumption
theorem tendsto_integral_of_uniform (ρ : Measure (GaugeField 1))
    [IsProbabilityMeasure ρ] {X : ℕ → GaugeField 1 → ℂ} {Y : GaugeField 1 → ℂ}
    (hX : ∀ n, IsBoundedObservable (X n)) (hY : IsBoundedObservable Y)
    (h : TendstoUniformly X Y atTop) :
    Tendsto (fun n => ∫ U, X n U ∂ρ) atTop (𝓝 (∫ U, Y U ∂ρ)) := by
  obtain ⟨-, C, hC⟩ := hY
  have h₁ := Metric.tendstoUniformly_iff.mp h 1 one_pos
  refine tendsto_integral_filter_of_dominated_convergence (fun _ => C + 1) ?_ ?_
    (integrable_const _) ?_
  · exact Eventually.of_forall fun n => (hX n).1.aestronglyMeasurable
  · filter_upwards [h₁] with n hn
    refine ae_of_all _ fun U => ?_
    have h₂ := hn U
    rw [dist_comm, dist_eq_norm] at h₂
    have h₃ := norm_sub_norm_le (X n U) (Y U)
    have h₄ := hC U
    linarith
  · exact ae_of_all _ fun U => h.tendsto_at U
def reflectedMeasure (ν : Measure (GaugeField 1)) (P : NormalFamilies.NormalLevelPair 1) :
    Measure (GaugeField 1) :=
  ν.map P.reflectSymmetry.pullbackField
instance (ν : Measure (GaugeField 1)) [IsProbabilityMeasure ν]
    (P : NormalFamilies.NormalLevelPair 1) : IsProbabilityMeasure (reflectedMeasure ν P) :=
  Measure.isProbabilityMeasure_map
    P.reflectSymmetry.continuous_pullbackField.measurable.aemeasurable
theorem integral_reflectedMeasure (ν : Measure (GaugeField 1))
    (P : NormalFamilies.NormalLevelPair 1) {F : GaugeField 1 → ℂ} (hF : IsBoundedObservable F) :
    ∫ U, F U ∂(reflectedMeasure ν P) = ∫ U, P.reflectObservable F U ∂ν :=
  integral_map P.reflectSymmetry.continuous_pullbackField.measurable.aemeasurable
    hF.1.aestronglyMeasurable
abbrev transportedFamily (μ : Fin 4) (i k : ℤ) (hk : 1 ≤ k) (v : Set (SliceSite μ))
    (U : GaugeField 1) : centeredLinkPairs i k v → Matrices.ComplexMatrix2.specialUnitary :=
  fun p => (centeredStack i k hk).transportedLinkVariable μ U p.1.1 p.1.2
theorem isBoundedObservable_transportedFamily (hTemp : TemporalGauge.MainStatement) {μ : Fin 4}
    {i k : ℤ} (hk : 1 ≤ k) {v : Set (SliceSite μ)} [Finite v] (hv : (linksWithin v).Nonempty)
    {Φ : (centeredLinkPairs i k v → Matrices.ComplexMatrix2.specialUnitary) → ℂ}
    (hc : Continuous Φ) (hinv : IsDiagonalGaugeInvariant (snd_mem_linksWithin i k v) Φ) :
    IsBoundedObservable fun U => Φ (transportedFamily μ i k hk v U) := by
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hc.continuousOn
  exact (((hTemp μ (centeredStack i k hk)).1 v hv).2 Φ hc.measurable
    ⟨C, fun u => hC u (Set.mem_univ _)⟩ hinv).1
theorem integral_eq_reflected_of_real (hAvg : SliceGaugeMeanProperties)
    (hTemp : TemporalGauge.MainStatement)
    (hInd : CenteredStackReflectionInvarianceStatement) {μ : Fin 4} {β : ℝ}
    (hβ : 0 < β) {ν : Measure (GaugeField 1)} (hν : IsPeriodicGibbs β ν)
    (P : NormalFamilies.NormalLevelPair 1) {i : ℤ} (hPv : P.normal = coordVec μ)
    (hPp : P.level = (i : ℝ) + 1 / 2) {k : ℤ} (hk : 1 ≤ k) {v : Set (SliceSite μ)} [Finite v]
    (hv : (linksWithin v).Nonempty)
    (Ψ : C(centeredLinkPairs i k v → Matrices.ComplexMatrix2.specialUnitary, ℂ))
    (hre : IsRealValuedSliceFunction
      (Ψ : (centeredLinkPairs i k v → Matrices.ComplexMatrix2.specialUnitary) → ℂ))
    (hinv : IsDiagonalGaugeInvariant (snd_mem_linksWithin i k v)
      (Ψ : (centeredLinkPairs i k v → Matrices.ComplexMatrix2.specialUnitary) → ℂ)) :
    ∫ U, Ψ (transportedFamily μ i k hk v U) ∂ν =
      ∫ U, Ψ (transportedFamily μ i k hk v U) ∂(reflectedMeasure ν P) := by
  have : IsProbabilityMeasure ν := hν.1.1
  obtain ⟨c, hc⟩ := id hv
  have hvne : v.Nonempty := ⟨_, hc.1⟩
  have hIne : (centeredLinkPairs i k v).Nonempty := ⟨(i, c), by omega, by omega, hc⟩
  obtain ⟨Q, hQ, hu⟩ :=
    (hAvg μ β hβ v (centeredLinkPairs i k v) hvne hIne (snd_mem_linksWithin i k v)).2.2.1 Ψ hre hinv
  have hX : ∀ n, IsBoundedObservable fun U => Q n (transportedFamily μ i k hk v U) := fun n =>
    isBoundedObservable_transportedFamily hTemp hk hv (hQ n).1.1.continuous (hQ n).2
  have hY : IsBoundedObservable fun U => Ψ (transportedFamily μ i k hk v U) :=
    isBoundedObservable_transportedFamily hTemp hk hv Ψ.continuous hinv
  have hlim : TendstoUniformly (fun n U => Q n (transportedFamily μ i k hk v U))
      (fun U => Ψ (transportedFamily μ i k hk v U)) atTop :=
    hu.comp (transportedFamily μ i k hk v)
  have heq : ∀ n, ∫ U, Q n (transportedFamily μ i k hk v U) ∂(reflectedMeasure ν P) =
      ∫ U, Q n (transportedFamily μ i k hk v U) ∂ν := fun n => by
    have hmem : (fun U => Q n (transportedFamily μ i k hk v U)) ∈ centeredStackClass μ i k hk :=
      ⟨v, inferInstance, Q n, hv, (hQ n).1, (hQ n).2, fun U => rfl⟩
    rw [integral_reflectedMeasure ν P (hX n)]
    exact ((hInd μ β hβ ν hν i).2 P hPv hPp k hk _ hmem).symm
  exact tendsto_nhds_unique (tendsto_integral_of_uniform ν hX hY hlim)
    ((tendsto_integral_of_uniform (reflectedMeasure ν P) hX hY hlim).congr heq)
theorem integral_eq_reflected_of_gaugeInvariant
    (hElem : ElementaryLatticeFacts)
    (hAvg : SliceGaugeMeanProperties)
    (hTemp : TemporalGauge.MainStatement)
    (hInd : CenteredStackReflectionInvarianceStatement) {μ : Fin 4} {β : ℝ}
    (hβ : 0 < β) {ν : Measure (GaugeField 1)} (hν : IsPeriodicGibbs β ν)
    (P : NormalFamilies.NormalLevelPair 1) {i : ℤ} (hPv : P.normal = coordVec μ)
    (hPp : P.level = (i : ℝ) + 1 / 2) {F : GaugeField 1 → ℂ}
    (hF : F ∈ continuousLocalFunctions 1) (hg : IsGaugeInvariantFunction F) :
    ∫ U, F U ∂ν = ∫ U, F U ∂(reflectedMeasure ν P) := by
  have : IsProbabilityMeasure ν := hν.1.1
  obtain ⟨hobs, hloc, hcont⟩ := hF
  obtain ⟨-, -, -, hL, -⟩ := hElem 1 β one_pos hβ
  obtain ⟨hdep, hset, hfin, -⟩ := hL.2.2.2.2.2.2.2 F hobs hloc
  obtain ⟨k, v, hk, hvf, hv, hcov⟩ := exists_centeredStack_of_finite μ i hfin.toFinset
    fun b hb => hset (hfin.mem_toFinset.mp hb)
  have : Finite v := hvf.to_subtype
  have hdep' : DependsOnlyOn (Subtype.val '' (centeredStack i k hk).linksOver v) F := by
    intro U U' h
    refine hdep U U' fun b hb => h b ?_
    rcases hcov b (hfin.mem_toFinset.mpr hb) with
      ⟨j, c, h₁, h₂, h₃, hb'⟩ | ⟨j, y, h₁, h₂, h₃, hb'⟩
    · exact ⟨_, Or.inl ⟨j, c, h₁, h₂, h₃, rfl⟩, hb'.symm⟩
    · exact ⟨_, Or.inr ⟨j, y, h₁, h₂, h₃, rfl⟩, hb'.symm⟩
  obtain ⟨-, hval, -, -, hinv, hc, -⟩ :=
    ((hTemp μ (centeredStack i k hk)).1 v hv).1 F hobs hg hdep'
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : (centeredLinkPairs i k v → Matrices.ComplexMatrix2.specialUnitary) → ℂ,
      Φ = (centeredStack i k hk).temporalGaugeValue v F := ⟨_, rfl⟩
  have hΦc : Continuous Φ := hΦ ▸ hc hcont
  have hΦi : IsDiagonalGaugeInvariant (snd_mem_linksWithin i k v) Φ :=
    hΦ ▸ hinv
  have hFU : ∀ U, F U = Φ (transportedFamily μ i k hk v U) := fun U => by
    rw [hΦ]
    exact hval U
  let Φ₁ : C(centeredLinkPairs i k v → Matrices.ComplexMatrix2.specialUnitary, ℂ) :=
    ⟨fun u => ((Φ u).re : ℂ), Complex.continuous_ofReal.comp (Complex.continuous_re.comp hΦc)⟩
  let Φ₂ : C(centeredLinkPairs i k v → Matrices.ComplexMatrix2.specialUnitary, ℂ) :=
    ⟨fun u => ((Φ u).im : ℂ), Complex.continuous_ofReal.comp (Complex.continuous_im.comp hΦc)⟩
  have h₁i : IsDiagonalGaugeInvariant (snd_mem_linksWithin i k v)
      (Φ₁ : (centeredLinkPairs i k v → Matrices.ComplexMatrix2.specialUnitary) → ℂ) := fun g u =>
    congrArg (fun z : ℂ => ((z.re : ℝ) : ℂ)) (hΦi g u)
  have h₂i : IsDiagonalGaugeInvariant (snd_mem_linksWithin i k v)
      (Φ₂ : (centeredLinkPairs i k v → Matrices.ComplexMatrix2.specialUnitary) → ℂ) := fun g u =>
    congrArg (fun z : ℂ => ((z.im : ℝ) : ℂ)) (hΦi g u)
  have h₁r : IsRealValuedSliceFunction
      (Φ₁ : (centeredLinkPairs i k v → Matrices.ComplexMatrix2.specialUnitary) → ℂ) := fun u =>
    Complex.ofReal_im _
  have h₂r : IsRealValuedSliceFunction
      (Φ₂ : (centeredLinkPairs i k v → Matrices.ComplexMatrix2.specialUnitary) → ℂ) := fun u =>
    Complex.ofReal_im _
  have hsplit : ∀ (ρ : Measure (GaugeField 1)) [IsProbabilityMeasure ρ],
      ∫ U, F U ∂ρ = ∫ U, Φ₁ (transportedFamily μ i k hk v U) ∂ρ +
        (∫ U, Φ₂ (transportedFamily μ i k hk v U) ∂ρ) * Complex.I := by
    intro ρ _
    have h₁ := integrable_of_isBoundedObservable (ρ := ρ)
      (isBoundedObservable_transportedFamily hTemp hk hv Φ₁.continuous h₁i)
    have h₂ := integrable_of_isBoundedObservable (ρ := ρ)
      (isBoundedObservable_transportedFamily hTemp hk hv Φ₂.continuous h₂i)
    rw [← integral_mul_const, ← integral_add h₁ (h₂.mul_const _)]
    refine integral_congr_ae (ae_of_all _ fun U => ?_)
    change F U = ((Φ _).re : ℂ) + ((Φ _).im : ℂ) * Complex.I
    rw [Complex.re_add_im, hFU]
  rw [hsplit ν, hsplit (reflectedMeasure ν P),
    integral_eq_reflected_of_real hAvg hTemp hInd hβ hν P hPv hPp hk hv Φ₁ h₁r h₁i,
    integral_eq_reflected_of_real hAvg hTemp hInd hβ hν P hPv hPp hk hv Φ₂ h₂r h₂i]
theorem isSymmetricUnder_linkReflection
    (hElem : ElementaryLatticeFacts)
    (hEq : GibbsClassStructure)
    (hAvg : SliceGaugeMeanProperties)
    (hTemp : TemporalGauge.MainStatement)
    (hInd : CenteredStackReflectionInvarianceStatement) {μ : Fin 4} {β : ℝ}
    (hβ : 0 < β) {ν : Measure (GaugeField 1)} (hν : IsPeriodicGibbs β ν)
    (hG : ν ∈ gibbsClass one_pos β)
    (P : NormalFamilies.NormalLevelPair 1) {i : ℤ} (hPv : P.normal = coordVec μ)
    (hPp : P.level = (i : ℝ) + 1 / 2) : IsSymmetricUnder ν P.reflectSymmetry := by
  have hmem : reflectedMeasure ν P ∈ gibbsClass one_pos β :=
    (((hEq 1 one_pos β hβ).2.2.2.2 ⟨∅, by simp⟩ P.reflectSymmetry).2.2.2.2.2 ν hG).2.2
  have heq : ν = reflectedMeasure ν P := (hEq 1 one_pos β hβ).2.1.2.2 ν hG _ hmem fun F hF hg =>
    integral_eq_reflected_of_gaugeInvariant hElem hAvg hTemp hInd hβ hν P hPv hPp hF hg
  intro A hA
  have h := integral_reflectedMeasure ν P hA
  rw [← heq] at h
  exact h.symm
theorem exists_two_smul_coordVec_mem_periodSubgroup
    (hTrans : NormalFamilies.ReflectionPairShift.ReflectionPairsGiveShift)
    {ν : Measure (GaugeField 1)} [IsProbabilityMeasure ν]
    (hinv : ∀ (μ : Fin 4) (P : NormalFamilies.NormalLevelPair 1) (i : ℤ),
      P.normal = coordVec μ → P.level = (i : ℝ) + 1 / 2 →
      IsSymmetricUnder ν P.reflectSymmetry) (μ : Fin 4) :
    ∃ w : LatticePoint 1, (w : AmbientSpace) = (2 : ℝ) • coordVec μ ∧ w ∈ periodSubgroup ν := by
  have h₀ : ∃ k : ℤ, (1 / 2 : ℝ) = (k : ℝ) + 1 / 2 := ⟨0, by norm_num⟩
  have h₁ : ∃ k : ℤ, (3 / 2 : ℝ) = (k : ℝ) + 1 / 2 := ⟨1, by norm_num⟩
  obtain ⟨w, hw, -, -, -, hm⟩ := hTrans.1 (coordVec μ) (Or.inl ⟨μ, rfl⟩) (1 / 2) (3 / 2)
    (linkReflectionPair μ _ h₀).allowed (linkReflectionPair μ _ h₁).allowed
  refine ⟨w, ?_, hm ν inferInstance (hinv μ _ 0 rfl (by norm_num)) (hinv μ _ 1 rfl (by norm_num))⟩
  rw [hw, NormalFamilies.dualVector, normSq_coordVec]
  norm_num
theorem cubicSublattice_le_of_two_smul {R : AddSubgroup (LatticePoint 1)}
    (h : ∀ μ : Fin 4, ∃ w : LatticePoint 1, (w : AmbientSpace) = (2 : ℝ) • coordVec μ ∧ w ∈ R) :
    cubicSublattice 1 2 ≤ R := by
  choose w hw hmem using h
  intro x hx
  obtain ⟨n, hn⟩ : (x : AmbientSpace) ∈ latticeSubgroup 2 := AddSubgroup.mem_addSubgroupOf.mp hx
  have hx' : x = ∑ μ, n μ • w μ := by
    apply Subtype.ext
    have h₁ : ((∑ μ, n μ • w μ : LatticePoint 1) : AmbientSpace) =
        ∑ μ, (n μ : ℝ) • (w μ : AmbientSpace) := by
      simp [Int.cast_smul_eq_zsmul]
    rw [h₁]
    funext κ
    simp [hw, hn, coordVec, Finset.sum_apply, Pi.single_apply]
  rw [hx']
  exact sum_mem fun μ _ => zsmul_mem (hmem μ) _
def coordsModTwo : LatticePoint 1 →+ (Fin 4 → ZMod 2) :=
  AddMonoidHom.mk' (fun x μ => ((level μ x : ℤ) : ZMod 2)) fun x y => by
    funext μ
    have h : level μ (x + y) = level μ x + level μ y := by
      have h' : ((level μ (x + y) : ℤ) : ℝ) = ((level μ x + level μ y : ℤ) : ℝ) := by
        push_cast
        rw [level_cast, level_cast, level_cast]
        rfl
      exact_mod_cast h'
    simp [h]
theorem finiteIndex_cubicSublattice_two : (cubicSublattice 1 2).FiniteIndex := by
  have hle : coordsModTwo.ker ≤ cubicSublattice 1 2 := by
    intro x hx
    refine AddSubgroup.mem_addSubgroupOf.mpr ?_
    have h : ∀ μ, (2 : ℤ) ∣ level μ x := fun μ =>
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp (congrFun (AddMonoidHom.mem_ker.mp hx) μ)
    choose n hn using h
    exact ⟨n, fun μ => by
      rw [← level_cast μ x, hn μ]
      push_cast
      ring⟩
  exact AddSubgroup.finiteIndex_of_le hle
theorem periodicGibbs_linkSymmetry
    (hElem : ElementaryLatticeFacts)
    (hEq : GibbsClassStructure)
    (hTrans : NormalFamilies.ReflectionPairShift.ReflectionPairsGiveShift)
    (hStates : GibbsHaarKernels.Statement)
    (hAvg : SliceGaugeMeanProperties)
    (hTemp : TemporalGauge.MainStatement)
    (hInd : CenteredStackReflectionInvarianceStatement) : Statement := by
  intro β hβ
  have hClasses := hStates.1 β hβ
  have hcub : ∀ ν : Measure (GaugeField 1), IsPeriodicGibbs β ν →
      ν ∈ gibbsClass one_pos β ∧ ∀ (μ : Fin 4) (P : NormalFamilies.NormalLevelPair 1) (i : ℤ),
        P.normal = coordVec μ → P.level = (i : ℝ) + 1 / 2 →
        IsSymmetricUnder ν P.reflectSymmetry := fun ν hν => by
    have hG : ν ∈ gibbsClass one_pos β := (hClasses ν hν.1.1).1.mp hν.1
    exact ⟨hG, fun μ P i hv hp =>
      isSymmetricUnder_linkReflection hElem hEq hAvg hTemp hInd hβ hν hG P hv hp⟩
  have htwo : ∀ ν : Measure (GaugeField 1), IsPeriodicGibbs β ν →
      cubicSublattice 1 2 ≤ periodSubgroup ν := fun ν hν => by
    have : IsProbabilityMeasure ν := hν.1.1
    exact cubicSublattice_le_of_two_smul
      (exists_two_smul_coordVec_mem_periodSubgroup hTrans (hcub ν hν).2)
  refine ⟨fun ν hν => ⟨fun μ c hc F hF => ?_, fun v hv => htwo ν hν hv⟩, ?_⟩
  · obtain ⟨k, hk⟩ := id hc
    exact (hcub ν hν).2 μ (linkReflectionPair μ c hc) k rfl hk F hF
  · ext ν
    constructor
    · intro hν
      exact ⟨(hcub ν hν).1, fun v hv => htwo ν hν hv⟩
    · intro hν
      have hp : IsProbabilityMeasure ν := hν.1.1
      have hper : ν ∈ periodicGibbsClass one_pos β :=
        ((hClasses ν hp).2.2).mpr ⟨cubicSublattice 1 2, finiteIndex_cubicSublattice_two, hν⟩
      exact ((hClasses ν hp).2.1).mpr hper
end YangMills.Construction.TransferOperators.PeriodicGibbsLinkSymmetry
end
