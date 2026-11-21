import YangMills.Construction.Continuum.SeparatedTuplesOfFourSpace
import YangMills.Construction.InfiniteLattice.ContinuousFunctionsOfFinitelyManyBondsAndPlaquetteEnergies
import YangMills.Construction.InfiniteLattice.ContinuousLocalFunctionsAreDenseAndTestMeasures
import YangMills.Construction.InfiniteLattice.SpaceOfConfigurationsAndLatticeIsometries
import YangMills.Construction.LawInAState.FromSixteenCopiesToOneBoxProof
import Mathlib
set_option autoImplicit false
open MeasureTheory Filter Set
open scoped Topology
noncomputable section
namespace YangMills.Construction.InfiniteLattice
namespace ContinuousLocalDensity
section L2Approximation
variable {X : Type*} [mX : MeasurableSpace X]
def IsBoundedMeasurable (H : X → ℂ) : Prop := Measurable H ∧ ∃ C : ℝ, ∀ x, ‖H x‖ ≤ C
theorem IsBoundedMeasurable.add {H H' : X → ℂ} (hH : IsBoundedMeasurable H)
    (hH' : IsBoundedMeasurable H') : IsBoundedMeasurable (fun x => H x + H' x) := by
  obtain ⟨m, C, hC⟩ := hH
  obtain ⟨m', C', hC'⟩ := hH'
  exact ⟨m.add m', C + C', fun x => (norm_add_le _ _).trans (add_le_add (hC x) (hC' x))⟩
theorem IsBoundedMeasurable.sub {H H' : X → ℂ} (hH : IsBoundedMeasurable H)
    (hH' : IsBoundedMeasurable H') : IsBoundedMeasurable (fun x => H x - H' x) := by
  obtain ⟨m, C, hC⟩ := hH
  obtain ⟨m', C', hC'⟩ := hH'
  exact ⟨m.sub m', C + C', fun x => (norm_sub_le _ _).trans (add_le_add (hC x) (hC' x))⟩
def meanSqNorm (ν : Measure X) (H : X → ℂ) : ℝ := ∫ x, ‖H x‖ ^ 2 ∂ν
variable {ν : Measure X} [IsProbabilityMeasure ν]
omit [IsProbabilityMeasure ν] in
theorem meanSqNorm_nonneg (H : X → ℂ) : 0 ≤ meanSqNorm ν H :=
  integral_nonneg fun _ => by positivity
theorem integrable_sq_norm {H : X → ℂ} (hH : IsBoundedMeasurable H) :
    Integrable (fun x => ‖H x‖ ^ 2) ν := by
  obtain ⟨m, C, hC⟩ := hH
  refine Integrable.of_bound (C := C ^ 2) (m.norm.pow_const 2).aestronglyMeasurable
    (ae_of_all _ fun x => ?_)
  have h0 := norm_nonneg (H x)
  rw [Real.norm_of_nonneg (by positivity)]
  exact pow_le_pow_left₀ h0 (hC x) 2
theorem meanSqNorm_add_le {H H' : X → ℂ} (hH : IsBoundedMeasurable H)
    (hH' : IsBoundedMeasurable H') :
    meanSqNorm ν (fun x => H x + H' x) ≤ 2 * meanSqNorm ν H + 2 * meanSqNorm ν H' := by
  unfold meanSqNorm
  rw [← integral_const_mul, ← integral_const_mul,
    ← integral_add ((integrable_sq_norm hH).const_mul 2) ((integrable_sq_norm hH').const_mul 2)]
  refine integral_mono (integrable_sq_norm (hH.add hH'))
    (((integrable_sq_norm hH).const_mul 2).add ((integrable_sq_norm hH').const_mul 2)) fun x => ?_
  have h1 := norm_add_le (H x) (H' x)
  have h2 := norm_nonneg (H x + H' x)
  show ‖H x + H' x‖ ^ 2 ≤ 2 * ‖H x‖ ^ 2 + 2 * ‖H' x‖ ^ 2
  nlinarith [sq_nonneg (‖H x‖ - ‖H' x‖)]
theorem tendsto_meanSqNorm_sub {H : ℕ → X → ℂ} {F : X → ℂ} {M : ℝ} (hm : ∀ j, Measurable (H j))
    (hF : Measurable F) (hH : ∀ j x, ‖H j x‖ ≤ M) (hFM : ∀ x, ‖F x‖ ≤ M)
    (hlim : ∀ x, Tendsto (fun j => H j x) atTop (𝓝 (F x))) :
    Tendsto (fun j => meanSqNorm ν (fun x => H j x - F x)) atTop (𝓝 0) := by
  have hint : Tendsto (fun j => ∫ x, ‖H j x - F x‖ ^ 2 ∂ν) atTop (𝓝 (∫ _, (0 : ℝ) ∂ν)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => (M + M) ^ 2)
      (fun j => (((hm j).sub hF).norm.pow_const 2).aestronglyMeasurable)
      (integrable_const _) (fun j => ae_of_all _ fun x => ?_) (ae_of_all _ fun x => ?_)
    · have h0 := norm_nonneg (H j x - F x)
      rw [Real.norm_of_nonneg (by positivity)]
      exact pow_le_pow_left₀ h0 ((norm_sub_le _ _).trans (add_le_add (hH j x) (hFM x))) 2
    · have h1 : Tendsto (fun j => H j x - F x) atTop (𝓝 0) := by
        simpa using (hlim x).sub_const (F x)
      simpa using (h1.norm.pow 2)
  simpa [meanSqNorm] using hint
variable (ν)
def IsL2Approximable (𝒞 : Set (X → ℂ)) (F : X → ℂ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ G ∈ 𝒞, meanSqNorm ν (fun x => G x - F x) < ε
variable {ν}
structure IsBoundedMeasurableSubspace (𝒞 : Set (X → ℂ)) : Prop where
  bounded : ∀ G ∈ 𝒞, IsBoundedMeasurable G
  add_mem : ∀ G ∈ 𝒞, ∀ G' ∈ 𝒞, (fun x => G x + G' x) ∈ 𝒞
  smul_mem : ∀ (c : ℂ), ∀ G ∈ 𝒞, (fun x => c * G x) ∈ 𝒞
  one_mem : (fun _ => (1 : ℂ)) ∈ 𝒞
omit [IsProbabilityMeasure ν] in
theorem IsL2Approximable.of_mem {𝒞 : Set (X → ℂ)} {G : X → ℂ} (hG : G ∈ 𝒞) :
    IsL2Approximable ν 𝒞 G := fun ε hε => ⟨G, hG, by simpa [meanSqNorm] using hε⟩
theorem IsL2Approximable.add {𝒞 : Set (X → ℂ)} (h𝒞 : IsBoundedMeasurableSubspace 𝒞)
    {F F' : X → ℂ} (hFb : IsBoundedMeasurable F) (hFb' : IsBoundedMeasurable F')
    (hF : IsL2Approximable ν 𝒞 F) (hF' : IsL2Approximable ν 𝒞 F') :
    IsL2Approximable ν 𝒞 (fun x => F x + F' x) := by
  intro ε hε
  obtain ⟨G, hG, h1⟩ := hF (ε / 4) (by positivity)
  obtain ⟨G', hG', h2⟩ := hF' (ε / 4) (by positivity)
  refine ⟨_, h𝒞.add_mem G hG G' hG', ?_⟩
  have h3 := meanSqNorm_add_le (ν := ν) ((h𝒞.bounded G hG).sub hFb)
    ((h𝒞.bounded G' hG').sub hFb')
  have h4 : (fun x => G x + G' x - (F x + F' x)) = fun x => G x - F x + (G' x - F' x) := by
    funext x; ring
  rw [h4]
  linarith
omit [IsProbabilityMeasure ν] in
theorem IsL2Approximable.const_mul {𝒞 : Set (X → ℂ)} (h𝒞 : IsBoundedMeasurableSubspace 𝒞) (c : ℂ)
    {F : X → ℂ} (hF : IsL2Approximable ν 𝒞 F) :
    IsL2Approximable ν 𝒞 (fun x => c * F x) := by
  intro ε hε
  have hc : 0 < ‖c‖ ^ 2 + 1 := by positivity
  obtain ⟨G, hG, h1⟩ := hF (ε / (‖c‖ ^ 2 + 1)) (by positivity)
  refine ⟨_, h𝒞.smul_mem c G hG, ?_⟩
  have h2 : meanSqNorm ν (fun x => c * G x - c * F x) =
      ‖c‖ ^ 2 * meanSqNorm ν (fun x => G x - F x) := by
    unfold meanSqNorm
    rw [← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    show ‖c * G x - c * F x‖ ^ 2 = ‖c‖ ^ 2 * ‖G x - F x‖ ^ 2
    rw [← mul_sub, norm_mul, mul_pow]
  rw [h2]
  have h3 := meanSqNorm_nonneg (ν := ν) (fun x => G x - F x)
  have h4 : meanSqNorm ν (fun x => G x - F x) * (‖c‖ ^ 2 + 1) < ε := (lt_div_iff₀ hc).mp h1
  nlinarith
theorem IsL2Approximable.of_tendsto {𝒞 : Set (X → ℂ)} (h𝒞 : IsBoundedMeasurableSubspace 𝒞)
    {H : ℕ → X → ℂ} {F : X → ℂ} {M : ℝ} (hm : ∀ j, Measurable (H j)) (hFm : Measurable F)
    (hH : ∀ j x, ‖H j x‖ ≤ M) (hFM : ∀ x, ‖F x‖ ≤ M)
    (hlim : ∀ x, Tendsto (fun j => H j x) atTop (𝓝 (F x)))
    (hHl : ∀ j, IsL2Approximable ν 𝒞 (H j)) : IsL2Approximable ν 𝒞 F := by
  intro ε hε
  have ht := tendsto_meanSqNorm_sub (ν := ν) hm hFm hH hFM hlim
  obtain ⟨j, hj⟩ := (ht.eventually (gt_mem_nhds (show (0 : ℝ) < ε / 4 by positivity))).exists
  obtain ⟨G, hG, h1⟩ := hHl j (ε / 4) (by positivity)
  refine ⟨G, hG, ?_⟩
  have hb : IsBoundedMeasurable (H j) := ⟨hm j, M, hH j⟩
  have h3 := meanSqNorm_add_le (ν := ν) ((h𝒞.bounded G hG).sub hb)
    (hb.sub (⟨hFm, M, hFM⟩ : IsBoundedMeasurable F))
  have h4 : (fun x => G x - H j x + (H j x - F x)) = fun x => G x - F x := by
    funext x; ring
  rw [h4] at h3
  linarith
theorem isBoundedMeasurable_indicator_one {E : Set X} (hE : MeasurableSet E) :
    IsBoundedMeasurable (E.indicator (1 : X → ℂ)) := by
  refine ⟨measurable_one.indicator hE, 1, fun x => ?_⟩
  by_cases h : x ∈ E <;> simp [h]
theorem isL2Approximable_indicator {𝒞 : Set (X → ℂ)} (h𝒞 : IsBoundedMeasurableSubspace 𝒞)
    {𝓢 : Set (Set X)} (hm : MeasurableSpace.generateFrom 𝓢 ≤ mX)
    (hpi : IsPiSystem 𝓢) (hbasic : ∀ E ∈ 𝓢, IsL2Approximable ν 𝒞 (E.indicator 1))
    {E : Set X} (hE : MeasurableSet[MeasurableSpace.generateFrom 𝓢] E) :
    IsL2Approximable ν 𝒞 (E.indicator 1) := by
  have hone : IsL2Approximable ν 𝒞 (fun _ => (1 : ℂ)) := IsL2Approximable.of_mem h𝒞.one_mem
  induction E, hE using MeasurableSpace.induction_on_inter rfl hpi with
  | empty =>
    have : (∅ : Set X).indicator (1 : X → ℂ) = fun x => (0 : ℂ) * 1 := by
      funext x; simp
    rw [this]
    exact hone.const_mul h𝒞 0
  | basic t ht => exact hbasic t ht
  | compl t ht ih =>
    have h1 : tᶜ.indicator (1 : X → ℂ) = fun x => (1 : ℂ) + (-1) * t.indicator 1 x := by
      funext x
      by_cases h : x ∈ t <;> simp [h]
    rw [h1]
    have hb : IsBoundedMeasurable (t.indicator (1 : X → ℂ)) :=
      isBoundedMeasurable_indicator_one (hm _ ht)
    refine IsL2Approximable.add h𝒞 ⟨measurable_const, 1, fun _ => by simp⟩ ?_ hone
      (ih.const_mul h𝒞 (-1))
    obtain ⟨m₁, C, hC⟩ := hb
    exact ⟨m₁.const_mul _, C, fun x => by simpa using hC x⟩
  | iUnion f hd hf ih =>
    have hfm : ∀ i, MeasurableSet (f i) := fun i => hm _ (hf i)
    let T : ℕ → Set X := fun n => ⋃ i ∈ Finset.range n, f i
    have hTm : ∀ n, MeasurableSet (T n) := fun n =>
      Finset.measurableSet_biUnion _ fun i _ => hfm i
    have hT : ∀ n, IsL2Approximable ν 𝒞 ((T n).indicator 1) := by
      intro n
      induction n with
      | zero =>
        have : (T 0).indicator (1 : X → ℂ) = fun x => (0 : ℂ) * 1 := by
          funext x; simp [T]
        rw [this]
        exact hone.const_mul h𝒞 0
      | succ n ihn =>
        have hdisj : Disjoint (T n) (f n) := by
          refine Set.disjoint_iUnion₂_left.mpr fun i hi => hd ?_
          exact (Finset.mem_range.mp hi).ne
        have hU : T (n + 1) = T n ∪ f n := by
          simp only [T, Finset.range_add_one, Finset.set_biUnion_insert]
          exact Set.union_comm _ _
        have h1 : (T (n + 1)).indicator (1 : X → ℂ) =
            fun x => (T n).indicator 1 x + (f n).indicator 1 x := by
          funext x
          rw [hU, Set.indicator_union_of_disjoint hdisj]
        rw [h1]
        exact IsL2Approximable.add h𝒞 (isBoundedMeasurable_indicator_one (hTm n))
          (isBoundedMeasurable_indicator_one (hfm n)) ihn (ih n)
    have hUn : (⋃ n, T n) = ⋃ i, f i := by
      ext x
      simp only [T, Set.mem_iUnion, Finset.mem_range, exists_prop]
      constructor
      · rintro ⟨n, i, _, h⟩; exact ⟨i, h⟩
      · rintro ⟨i, h⟩; exact ⟨i + 1, i, Nat.lt_succ_self i, h⟩
    have hmono : Monotone T := by
      intro n k hnk
      refine Set.biUnion_subset_biUnion_left ?_
      intro i hi
      exact Finset.mem_range.mpr ((Finset.mem_range.mp hi).trans_le hnk)
    refine IsL2Approximable.of_tendsto (M := 1) h𝒞 (H := fun n => (T n).indicator 1)
      (fun n => (isBoundedMeasurable_indicator_one (hTm n)).1)
      (isBoundedMeasurable_indicator_one (MeasurableSet.iUnion hfm)).1 ?_ ?_ ?_ hT
    · intro n x
      by_cases h : x ∈ T n <;> simp [h]
    · intro x
      by_cases h : x ∈ ⋃ i, f i <;> simp [h]
    · intro x
      have := hmono.tendsto_indicator T (1 : X → ℂ) x
      rw [hUn] at this
      exact this.mono_right (pure_le_nhds _)
theorem isL2Approximable_of_measurable {𝒞 : Set (X → ℂ)} (h𝒞 : IsBoundedMeasurableSubspace 𝒞)
    {𝓢 : Set (Set X)} (hm : MeasurableSpace.generateFrom 𝓢 ≤ mX)
    (hpi : IsPiSystem 𝓢) (hbasic : ∀ E ∈ 𝓢, IsL2Approximable ν 𝒞 (E.indicator 1))
    {F : X → ℂ} (hF : Measurable[MeasurableSpace.generateFrom 𝓢] F) {C : ℝ}
    (hC : ∀ x, ‖F x‖ ≤ C) (hC0 : 0 ≤ C) : IsL2Approximable ν 𝒞 F := by
  have hbd : ∀ f : @SimpleFunc X (MeasurableSpace.generateFrom 𝓢) ℂ,
      IsBoundedMeasurable (f : X → ℂ) := by
    intro f
    obtain ⟨K, hK⟩ := @SimpleFunc.exists_forall_norm_le _ _ (MeasurableSpace.generateFrom 𝓢) _ f
    have hfm : Measurable[MeasurableSpace.generateFrom 𝓢] (f : X → ℂ) :=
      @SimpleFunc.measurable X ℂ (MeasurableSpace.generateFrom 𝓢) _ f
    exact ⟨hfm.mono hm le_rfl, K, hK⟩
  have hsimple : ∀ f : @SimpleFunc X (MeasurableSpace.generateFrom 𝓢) ℂ,
      IsL2Approximable ν 𝒞 (f : X → ℂ) := by
    intro f
    refine @SimpleFunc.induction X ℂ (MeasurableSpace.generateFrom 𝓢) _
      (fun f => IsL2Approximable ν 𝒞 (f : X → ℂ)) ?_ ?_ f
    · intro c s hs
      convert (isL2Approximable_indicator h𝒞 hm hpi hbasic hs).const_mul h𝒞 c using 1
      funext x
      by_cases h : x ∈ s <;> simp [h]
    · intro f g _ hf hg
      exact IsL2Approximable.add h𝒞 (hbd f) (hbd g) hf hg
  have hsm : @StronglyMeasurable X ℂ _ (MeasurableSpace.generateFrom 𝓢) F := hF.stronglyMeasurable
  refine IsL2Approximable.of_tendsto (M := C) h𝒞 (H := fun n => hsm.approxBounded C n)
    (fun n => (hbd _).1) (hF.mono hm le_rfl) (fun n x => hsm.norm_approxBounded_le hC0 n x) hC
    (fun x => hsm.tendsto_approxBounded_of_norm_le (hC x)) (fun n => hsimple _)
end L2Approximation
theorem continuous_eval_link (b : Link (1 : ℝ)) :
    Continuous fun U : GaugeField (1 : ℝ) => U b :=
  (continuous_apply b).comp continuous_subtype_val
def closedLinkEvents (b : Link (1 : ℝ)) : Set (Set (GaugeField (1 : ℝ))) :=
  {E | ∃ C : Set Matrices.ComplexMatrix2.specialUnitary, IsClosed C ∧
    (fun U : GaugeField (1 : ℝ) => U b) ⁻¹' C = E}
def closedCylinderSets (S : Set AmbientSpace) : Set (Set (GaugeField (1 : ℝ))) :=
  piiUnionInter closedLinkEvents (positiveLinks 1 ∩ linksWithin S)
theorem preimage_mem_closedCylinderSets {S : Set AmbientSpace} {b : Link (1 : ℝ)}
    (hb : b ∈ positiveLinks 1 ∩ linksWithin S) {C : Set Matrices.ComplexMatrix2.specialUnitary}
    (hC : IsClosed C) :
    (fun U : GaugeField (1 : ℝ) => U b) ⁻¹' C ∈ closedCylinderSets S :=
  subset_piiUnionInter hb (show _ ∈ closedLinkEvents b from ⟨C, hC, rfl⟩)
theorem isPiSystem_closedCylinderSets (S : Set AmbientSpace) :
    IsPiSystem (closedCylinderSets S) := by
  refine isPiSystem_piiUnionInter _ (fun b => ?_) _
  intro s hs t ht hst
  obtain ⟨C, hC, rfl⟩ := hs
  obtain ⟨C', hC', rfl⟩ := ht
  exact ⟨C ∩ C', hC.inter hC', rfl⟩
theorem regionSigma_le (S : Set AmbientSpace) :
    (regionSigma S : MeasurableSpace (GaugeField (1 : ℝ))) ≤
      (inferInstance : MeasurableSpace (GaugeField (1 : ℝ))) :=
  iSup₂_le fun b _ => (continuous_eval_link b).measurable.comap_le
theorem regionSigma_mono {S T : Set AmbientSpace} (h : S ⊆ T) :
    (regionSigma S : MeasurableSpace (GaugeField (1 : ℝ))) ≤ regionSigma T :=
  biSup_mono fun _ hb => ⟨h hb.1, h hb.2⟩
theorem regionSigma_eq_generateFrom (hSpace : FieldSpace.SymmetryProperties)
    (S : Set AmbientSpace) :
    (regionSigma S : MeasurableSpace (GaugeField (1 : ℝ))) =
      MeasurableSpace.generateFrom (closedCylinderSets S) := by
  refine le_antisymm (iSup₂_le fun b hb => ?_) (MeasurableSpace.generateFrom_le ?_)
  · refine Measurable.comap_le (@measurable_of_isClosed Matrices.ComplexMatrix2.specialUnitary
      (GaugeField (1 : ℝ)) _ _ _
      (MeasurableSpace.generateFrom (closedCylinderSets S)) _ fun C hC => ?_)
    by_cases hpos : b ∈ positiveLinks (1 : ℝ)
    · exact MeasurableSpace.measurableSet_generateFrom
        (preimage_mem_closedCylinderSets ⟨hpos, hb⟩ hC)
    · have hrev : b.opposite ∈ positiveLinks (1 : ℝ) :=
        ((hSpace 1 one_pos).2.2.2.2.2.2.2.1 b).elim (fun h => absurd h.1 hpos) (fun h => h.1)
      have hE : (fun U : GaugeField (1 : ℝ) => U b) ⁻¹' C =
          (fun U : GaugeField (1 : ℝ) => U b.opposite) ⁻¹' (Inv.inv ⁻¹' C) := by
        ext U
        show U b ∈ C ↔ (U b.opposite)⁻¹ ∈ C
        rw [U.2 b, inv_inv]
      rw [hE]
      exact MeasurableSpace.measurableSet_generateFrom
        (preimage_mem_closedCylinderSets ⟨hrev, hb.2, hb.1⟩ (hC.preimage continuous_inv))
  · rintro E ⟨t, ht, f, hf, rfl⟩
    refine Finset.measurableSet_biInter _ fun b hb => ?_
    obtain ⟨C, hC, hCf⟩ := hf b hb
    rw [← hCf]
    have hb' : b ∈ linksWithin S := (ht hb).2
    have hmeas : Measurable[regionSigma S] (fun U : GaugeField (1 : ℝ) => U b) :=
      measurable_iff_comap_le.mpr (le_iSup₂_of_le b hb' le_rfl)
    exact hmeas hC.measurableSet
theorem exists_continuous_approx_indicator {C : Set Matrices.ComplexMatrix2.specialUnitary}
    (hC : IsClosed C) :
    ∃ g : ℕ → Matrices.ComplexMatrix2.specialUnitary → ℝ, (∀ k, Continuous (g k)) ∧
      (∀ k u, 0 ≤ g k u ∧ g k u ≤ 1) ∧
      ∀ u, Tendsto (fun k => g k u) atTop
        (𝓝 (C.indicator (1 : Matrices.ComplexMatrix2.specialUnitary → ℝ) u)) := by
  have hmat : TopologicalSpace.PseudoMetrizableSpace Matrices.ComplexMatrix2 :=
    inferInstanceAs (TopologicalSpace.PseudoMetrizableSpace (Fin 2 → Fin 2 → ℂ))
  have hsu : TopologicalSpace.PseudoMetrizableSpace Matrices.ComplexMatrix2.specialUnitary :=
    Topology.IsInducing.subtypeVal.pseudoMetrizableSpace
  have happr : HasOuterApproxClosed Matrices.ComplexMatrix2.specialUnitary := by
    let _ := TopologicalSpace.pseudoMetrizableSpacePseudoMetric
      Matrices.ComplexMatrix2.specialUnitary
    infer_instance
  refine ⟨fun k u => ((hC.apprSeq k u : NNReal) : ℝ), fun k => ?_, fun k u => ?_, fun u => ?_⟩
  · exact NNReal.continuous_coe.comp (hC.apprSeq k).continuous
  · exact ⟨NNReal.coe_nonneg _, by exact_mod_cast HasOuterApproxClosed.apprSeq_apply_le_one hC k u⟩
  · have h := tendsto_pi_nhds.mp (HasOuterApproxClosed.tendsto_apprSeq hC) u
    have h2 := (NNReal.continuous_coe.tendsto _).comp h
    have h3 : ((C.indicator (fun _ => (1 : NNReal)) u : NNReal) : ℝ) =
        C.indicator (1 : Matrices.ComplexMatrix2.specialUnitary → ℝ) u := by
      by_cases hu : u ∈ C <;> simp [hu]
    rw [h3] at h2
    exact h2
theorem exists_local_tendsto_indicator (hLocal : ContinuousLocalAndFaceEnergies.Statement)
    {S : Set AmbientSpace} {E : Set (GaugeField (1 : ℝ))} (hE : E ∈ closedCylinderSets S) :
    ∃ H : ℕ → GaugeField (1 : ℝ) → ℂ,
      (∀ k, H k ∈ regionObservables 1 S ∩ continuousLocalFunctions 1) ∧
      (∀ k U, ‖H k U‖ ≤ 1) ∧
      ∀ U, Tendsto (fun k => H k U) atTop (𝓝 (E.indicator 1 U)) := by
  obtain ⟨t, ht, f, hf, rfl⟩ := hE
  choose! C hC hCf using hf
  have key : ∀ b ∈ t, ∃ g : ℕ → Matrices.ComplexMatrix2.specialUnitary → ℝ,
      (∀ k, Continuous (g k)) ∧ (∀ k u, 0 ≤ g k u ∧ g k u ≤ 1) ∧
      ∀ u, Tendsto (fun k => g k u) atTop
        (𝓝 ((C b).indicator (1 : Matrices.ComplexMatrix2.specialUnitary → ℝ) u)) :=
    fun b hb => exists_continuous_approx_indicator (hC b hb)
  choose! g hgc hgb hgl using key
  refine ⟨fun k U => ∏ b ∈ t, ((g b k (U b) : ℝ) : ℂ), fun k => ?_, fun k U => ?_, fun U => ?_⟩
  · have hcont : Continuous fun U : GaugeField (1 : ℝ) => ∏ b ∈ t, ((g b k (U b) : ℝ) : ℂ) :=
      continuous_finsetProd _ fun b hb =>
        Complex.continuous_ofReal.comp ((hgc b hb k).comp (continuous_eval_link b))
    obtain ⟨h1, h2, -⟩ := hLocal.1 (t : Set (Link (1 : ℝ))) (fun b hb => (ht hb).1)
      t.finite_toSet _ hcont (fun U U' h => Finset.prod_congr rfl fun b hb => by rw [h b hb])
    refine ⟨⟨h2.1, ?_⟩, h1⟩
    refine Measurable.mono h2.2 (regionSigma_mono ?_) le_rfl
    rintro x ⟨b, hb, rfl | rfl⟩
    · exact (ht hb).2.1
    · exact (ht hb).2.2
  · rw [norm_prod]
    refine Finset.prod_le_one (fun _ _ => norm_nonneg _) fun b hb => ?_
    rw [Complex.norm_real, Real.norm_of_nonneg (hgb b hb k _).1]
    exact (hgb b hb k _).2
  · have h := tendsto_finsetProd t fun b hb =>
      (Complex.continuous_ofReal.tendsto _).comp (hgl b hb (U b))
    have h2 : ∏ b ∈ t,
        (((C b).indicator (1 : Matrices.ComplexMatrix2.specialUnitary → ℝ) (U b) : ℝ) : ℂ) =
        (⋂ b ∈ t, f b).indicator 1 U := by
      by_cases hU : U ∈ ⋂ b ∈ t, f b
      · rw [Set.indicator_of_mem hU]
        refine Finset.prod_eq_one fun b hb => ?_
        have : U ∈ f b := Set.mem_iInter₂.mp hU b hb
        rw [← hCf b hb] at this
        have hm : U b ∈ C b := this
        simp [hm]
      · rw [Set.indicator_of_notMem hU]
        simp only [Set.mem_iInter, not_forall] at hU
        obtain ⟨b, hb, hUb⟩ := hU
        refine Finset.prod_eq_zero hb ?_
        rw [← hCf b hb] at hUb
        have hm : U b ∉ C b := hUb
        simp [hm]
    rw [← h2]
    exact h
theorem isBoundedMeasurableSubspace_regionObservables_inter (S : Set AmbientSpace) :
    IsBoundedMeasurableSubspace (regionObservables 1 S ∩ continuousLocalFunctions 1) where
  bounded G hG := hG.1.1
  add_mem G hG G' hG' := by
    obtain ⟨⟨hb, hm⟩, -, ⟨S₁, hS₁, h₁⟩, hc⟩ := hG
    obtain ⟨⟨hb', hm'⟩, -, ⟨S₂, hS₂, h₂⟩, hc'⟩ := hG'
    have hsum : IsBoundedObservable fun U => G U + G' U := IsBoundedMeasurable.add hb hb'
    have hm₁ : Measurable[regionSigma S] G := hm
    have hm₂ : Measurable[regionSigma S] G' := hm'
    have h₁' : Measurable[regionSigma (S₁ ∪ S₂)] G :=
      Measurable.mono h₁ (regionSigma_mono subset_union_left) le_rfl
    have h₂' : Measurable[regionSigma (S₁ ∪ S₂)] G' :=
      Measurable.mono h₂ (regionSigma_mono subset_union_right) le_rfl
    exact ⟨⟨hsum, hm₁.add hm₂⟩, hsum, ⟨S₁ ∪ S₂, hS₁.union hS₂, h₁'.add h₂'⟩, hc.add hc'⟩
  smul_mem c G hG := by
    obtain ⟨⟨⟨hb, K, hK⟩, hm⟩, -, ⟨S₁, hS₁, h₁⟩, hc⟩ := hG
    have hprod : IsBoundedObservable fun U => c * G U :=
      ⟨hb.const_mul c, ‖c‖ * K, fun U => by
        rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hK U) (norm_nonneg c)⟩
    have hm₁ : Measurable[regionSigma S] G := hm
    have h₁' : Measurable[regionSigma S₁] G := h₁
    exact ⟨⟨hprod, hm₁.const_mul c⟩, hprod, ⟨S₁, hS₁, h₁'.const_mul c⟩, continuous_const.mul hc⟩
  one_mem := by
    have hobs : IsBoundedObservable fun _ : GaugeField (1 : ℝ) => (1 : ℂ) :=
      ⟨measurable_const, 1, fun _ => by simp⟩
    exact ⟨⟨hobs, measurable_const⟩, hobs, ⟨∅, Bornology.isBounded_empty, measurable_const⟩,
      continuous_const⟩
theorem exists_l2_approx_of_mem_regionObservables (hSpace : FieldSpace.SymmetryProperties)
    (hLocal : ContinuousLocalAndFaceEnergies.Statement)
    (ν : Measure (GaugeField (1 : ℝ))) [IsProbabilityMeasure ν] (S : Set AmbientSpace)
    {F : GaugeField (1 : ℝ) → ℂ} (hF : F ∈ regionObservables 1 S) :
    ∃ G : ℕ → GaugeField (1 : ℝ) → ℂ,
      (∀ k, 1 ≤ k → G k ∈ regionObservables 1 S ∩ continuousLocalFunctions 1) ∧
      Tendsto (fun k => stateEval ν fun U => ‖G k U - F U‖ ^ 2) atTop (𝓝 (0 : ℝ)) := by
  have h𝒞 := isBoundedMeasurableSubspace_regionObservables_inter S
  have hgen := regionSigma_eq_generateFrom hSpace S
  have hle : MeasurableSpace.generateFrom (closedCylinderSets S) ≤
      (inferInstance : MeasurableSpace (GaugeField (1 : ℝ))) := hgen ▸ regionSigma_le S
  obtain ⟨⟨-, K, hK⟩, hm⟩ := hF
  have hm' : Measurable[MeasurableSpace.generateFrom (closedCylinderSets S)] F := by
    rw [← hgen]; exact hm
  have hlim : IsL2Approximable ν (regionObservables 1 S ∩ continuousLocalFunctions 1) F := by
    refine isL2Approximable_of_measurable (C := max K 0) h𝒞 hle (isPiSystem_closedCylinderSets S)
      (fun E hE => ?_) hm' (fun U => (hK U).trans (le_max_left _ _)) (le_max_right _ _)
    obtain ⟨H, hH, hb, hl⟩ := exists_local_tendsto_indicator hLocal hE
    have hEm : MeasurableSet E := hle _ (MeasurableSpace.measurableSet_generateFrom hE)
    refine IsL2Approximable.of_tendsto (M := 1) h𝒞 (fun k => (hH k).1.1.1)
      (isBoundedMeasurable_indicator_one hEm).1 hb (fun U => ?_) hl
      (fun k => IsL2Approximable.of_mem (hH k))
    by_cases h : U ∈ E <;> simp [h]
  have hseq : ∀ k : ℕ, ∃ G ∈ regionObservables 1 S ∩ continuousLocalFunctions 1,
      meanSqNorm ν (fun U => G U - F U) < 1 / ((k : ℝ) + 1) :=
    fun k => hlim _ (Nat.one_div_pos_of_nat)
  choose G hG hGlt using hseq
  refine ⟨G, fun k _ => hG k, ?_⟩
  show Tendsto (fun k => meanSqNorm ν (fun U => G k U - F U)) atTop (𝓝 0)
  exact squeeze_zero (fun k => meanSqNorm_nonneg _) (fun k => (hGlt k).le)
    tendsto_one_div_add_atTop_nhds_zero_nat
theorem measure_eq_of_stateEval_eq (hSpace : FieldSpace.SymmetryProperties)
    (hLocal : ContinuousLocalAndFaceEnergies.Statement)
    (ν ν' : Measure (GaugeField (1 : ℝ))) [IsProbabilityMeasure ν] [IsProbabilityMeasure ν']
    (h : ∀ F ∈ continuousLocalFunctions 1, stateEval ν' F = stateEval ν F) : ν' = ν := by
  have hborel : (inferInstance : MeasurableSpace (GaugeField (1 : ℝ))) =
      MeasurableSpace.generateFrom (closedCylinderSets univ) := by
    rw [← regionSigma_eq_generateFrom hSpace univ, (hSpace 1 one_pos).1.2.2]
    have : (linksWithin univ : Set (Link (1 : ℝ))) = univ := by
      ext b; simp [linksWithin]
    show linkSigma univ = linkSigma (linksWithin univ)
    rw [this]
  refine ext_of_generate_finite (closedCylinderSets univ) hborel
    (isPiSystem_closedCylinderSets univ) (fun E hE => ?_) (by simp)
  obtain ⟨H, hH, hb, hl⟩ := exists_local_tendsto_indicator hLocal hE
  have hEm : MeasurableSet E := by
    rw [show (MeasurableSet E) =
      (@MeasurableSet _ (MeasurableSpace.generateFrom (closedCylinderSets univ)) E) by
        rw [← hborel]]
    exact MeasurableSpace.measurableSet_generateFrom hE
  have hlim : ∀ (ρ : Measure (GaugeField (1 : ℝ))) [IsProbabilityMeasure ρ],
      Tendsto (fun k => stateEval ρ (H k)) atTop (𝓝 ((ρ.real E : ℝ) : ℂ)) := by
    intro ρ _
    have h1 : Tendsto (fun k => ∫ U, H k U ∂ρ) atTop
        (𝓝 (∫ U, E.indicator (1 : GaugeField (1 : ℝ) → ℂ) U ∂ρ)) :=
      tendsto_integral_of_dominated_convergence (fun _ => 1)
        (fun k => (hH k).1.1.1.aestronglyMeasurable) (integrable_const _)
        (fun k => ae_of_all _ (hb k)) (ae_of_all _ hl)
    have h2 : ∫ U, E.indicator (1 : GaugeField (1 : ℝ) → ℂ) U ∂ρ = ((ρ.real E : ℝ) : ℂ) := by
      have h3 : ∫ U, E.indicator (fun _ => (1 : ℂ)) U ∂ρ = ρ.real E • (1 : ℂ) :=
        integral_indicator_const 1 hEm
      refine Eq.trans h3 ?_
      simp
    rw [h2] at h1
    exact h1
  have h3 := tendsto_nhds_unique (hlim ν')
    ((hlim ν).congr fun k => (h (H k) (hH k).2).symm)
  have h4 : ν'.real E = ν.real E := by exact_mod_cast h3
  exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp h4
theorem norm_le_euclidNormVec (v : AmbientSpace) : ‖v‖ ≤ TorusMetric.euclidNormVec v := by apply _root_.YangMills.Construction.SeparatedTuplesR4.norm_le_euclidNormVec <;> assumption
theorem euclidNormVec_le_two_mul_norm (v : AmbientSpace) :
    TorusMetric.euclidNormVec v ≤ 2 * ‖v‖ := by apply _root_.YangMills.SharedProofs.p8643 <;> assumption
theorem isBounded_imageSet (r : LatticeSymmetry (1 : ℝ)) {S : Set AmbientSpace}
    (hS : Bornology.IsBounded S) : Bornology.IsBounded (r.imageSet S) := by
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp hS
  refine isBounded_iff_forall_norm_le.mpr ⟨2 * C + ‖r.toFun 0‖, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  have h1 := norm_le_euclidNormVec (r.toFun x - r.toFun 0)
  rw [r.preservesDist x 0, sub_zero] at h1
  have h2 := euclidNormVec_le_two_mul_norm x
  have h3 := hC x hx
  have h4 := norm_sub_norm_le (r.toFun x) (r.toFun 0)
  linarith
theorem actOn_mem_continuousLocalFunctions (hSpace : FieldSpace.SymmetryProperties)
    (r : LatticeSymmetry (1 : ℝ)) {F : GaugeField (1 : ℝ) → ℂ}
    (hF : F ∈ continuousLocalFunctions 1) :
    r.actOn F ∈ continuousLocalFunctions 1 := by
  obtain ⟨hobs, ⟨S, hS, hm⟩, hc⟩ := hF
  obtain ⟨hhom, -, -, himg⟩ := (hSpace 1 one_pos).2.1 r r
  have hrm : r.actOn F ∈ regionObservables 1 (r.imageSet S) := by
    rw [← himg S]
    exact ⟨F, ⟨hobs, hm⟩, rfl⟩
  exact ⟨hrm.1, ⟨_, isBounded_imageSet r hS, hrm.2⟩, hc.comp hhom.continuous⟩
theorem isSymmetricUnder_of_stateEval_eq (hSpace : FieldSpace.SymmetryProperties)
    (hLocal : ContinuousLocalAndFaceEnergies.Statement)
    (ν : Measure (GaugeField (1 : ℝ))) [IsProbabilityMeasure ν] (r : LatticeSymmetry (1 : ℝ))
    (h : ∀ F ∈ continuousLocalFunctions 1, stateEval ν (r.actOn F) = stateEval ν F) :
    IsSymmetricUnder ν r := by
  have hrm : Measurable r.pullbackField :=
    ((hSpace 1 one_pos).2.1 r r).1.continuous.measurable
  have : IsProbabilityMeasure (ν.map r.pullbackField) :=
    Measure.isProbabilityMeasure_map hrm.aemeasurable
  have heq : ν.map r.pullbackField = ν := by
    refine measure_eq_of_stateEval_eq hSpace hLocal ν _ fun F hF => ?_
    rw [← h F hF]
    exact integral_map hrm.aemeasurable hF.1.1.aestronglyMeasurable
  intro A hA
  have h1 : ∫ U, A U ∂(ν.map r.pullbackField) = ∫ U, r.actOn A U ∂ν :=
    integral_map hrm.aemeasurable hA.1.aestronglyMeasurable
  rw [← h1, heq]
theorem isWeakClusterPoint_of_subseq (ν : Measure (GaugeField (1 : ℝ)))
    (μ : ℕ → Measure (GaugeField (1 : ℝ))) (κ : ℕ → ℕ) (hκ₁ : ∀ j, 1 ≤ j → 1 ≤ κ j)
    (hκ : ∀ i j, 1 ≤ i → i < j → κ i < κ j)
    (hlim : WeakConvergesUnitSpacing (fun j => μ (κ j)) ν) :
    IsWeakClusterPointUnitSpacing μ ν := by
  intro 𝒞 hfin hcont ε hε k₀ hk₀
  have hev : ∀ᶠ j in atTop, ∀ F ∈ 𝒞, ‖stateEval (μ (κ j)) F - stateEval ν F‖ ≤ ε := by
    rw [Filter.eventually_all_finite hfin]
    intro F hF
    refine ((Metric.tendsto_nhds.mp (hlim F (hcont F hF))) ε hε).mono fun j hj => ?_
    rw [dist_eq_norm] at hj
    exact hj.le
  obtain ⟨j, hjF, hj⟩ := (hev.and (eventually_ge_atTop k₀)).exists
  have hge : ∀ j, 1 ≤ j → j ≤ κ j := by
    intro j hj
    induction j, hj using Nat.le_induction with
    | base => exact hκ₁ 1 le_rfl
    | succ n hn ih =>
      have := hκ n (n + 1) hn (Nat.lt_succ_self n)
      omega
  exact ⟨κ j, hj.trans (hge j (hk₀.trans hj)), hjF⟩
end ContinuousLocalDensity
open ContinuousLocalDensity in
theorem ContinuousLocalDensity.holds (hSpace : FieldSpace.SymmetryProperties)
    (hLocal : ContinuousLocalAndFaceEnergies.Statement) :
    ContinuousLocalDensity.Statement := by
  intro ν _
  refine ⟨fun S F hF => exists_l2_approx_of_mem_regionObservables hSpace hLocal ν S hF,
    fun ν' _ h => measure_eq_of_stateEval_eq hSpace hLocal ν ν' h,
    fun r => ⟨((hSpace 1 one_pos).2.1 r r).1.continuous,
      fun F hF => actOn_mem_continuousLocalFunctions hSpace r hF,
      isSymmetricUnder_of_stateEval_eq hSpace hLocal ν r⟩,
    fun μ _ κ hκ₁ hκ hlim => isWeakClusterPoint_of_subseq ν μ κ hκ₁ hκ hlim⟩
end YangMills.Construction.InfiniteLattice
