import YangMills.Construction.InfiniteLattice.ActionOfTheLatticeIsometriesOnConfigurationsAndFunctions
import YangMills.Construction.InfiniteLattice.EquilibriumEquationInAWindowThatEmbedsInATorus
import YangMills.Construction.InfiniteLattice.MovesOfBondsSupportsAndPlaquettes
import YangMills.Construction.InfiniteLattice.OrbitsAndPeriodicExtensions
import YangMills.Construction.InfiniteLattice.PlaquetteFunctionSeesNeitherCornerNorSense
import YangMills.Construction.InfiniteLattice.PropertiesOfTheKernelsOfBonds
import Mathlib
set_option autoImplicit false
open MeasureTheory YangMills.Construction.InfiniteLattice YangMills.Construction.Matrices
noncomputable section
namespace YangMills.Construction.GibbsAtFixedSpacing.EquilibriumInEmbeddableWindow
open SingleGeneratorArray
section Replacing
variable {ι κ : Type} {e : κ → ι}
instance isProbabilityMeasure_haarPi (ι : Type) [Countable ι] :
    IsProbabilityMeasure (ComplexMatrix2.haarPi ι) := by
  unfold ComplexMatrix2.haarPi
  infer_instance
theorem measurable_extend_pair (he : Function.Injective e) :
    Measurable fun q : (ι → ComplexMatrix2.specialUnitary) × (κ → ComplexMatrix2.specialUnitary) =>
      Function.extend e q.2 q.1 := by
  refine measurable_pi_lambda _ fun i => ?_
  by_cases h : ∃ k, e k = i
  · obtain ⟨k, rfl⟩ := h
    simp only [he.extend_apply]
    exact (measurable_pi_apply k).comp measurable_snd
  · simp only [Function.extend_apply' _ _ _ h]
    exact (measurable_pi_apply i).comp measurable_fst
theorem map_extend_haarPi [Countable ι] [Countable κ] (he : Function.Injective e) :
    Measure.map (fun q : (ι → ComplexMatrix2.specialUnitary) × (κ → ComplexMatrix2.specialUnitary) =>
        Function.extend e q.2 q.1)
      ((ComplexMatrix2.haarPi ι).prod (ComplexMatrix2.haarPi κ)) = ComplexMatrix2.haarPi ι := by
  classical
  refine Measure.eq_infinitePi _ fun s t ht => ?_
  have hpre : (fun q : (ι → ComplexMatrix2.specialUnitary) × (κ → ComplexMatrix2.specialUnitary) =>
      Function.extend e q.2 q.1) ⁻¹' Set.pi (s : Set ι) t =
        Set.pi (s.filter fun i => i ∉ Set.range e : Finset ι) t ×ˢ
          Set.pi (s.preimage e he.injOn : Finset κ) (fun k => t (e k)) := by
    ext ⟨U, V⟩
    simp only [Set.mem_preimage, Set.mem_pi, Finset.mem_coe, Set.mem_prod, Finset.mem_filter,
      Finset.mem_preimage]
    constructor
    · intro h
      refine ⟨fun i hi => ?_, fun k hk => ?_⟩
      · have := h i hi.1
        rwa [Function.extend_apply' _ _ _ (by simpa using hi.2)] at this
      · have := h _ hk
        rwa [he.extend_apply] at this
    · rintro ⟨h₁, h₂⟩ i hi
      by_cases h : ∃ k, e k = i
      · obtain ⟨k, rfl⟩ := h
        rw [he.extend_apply]
        exact h₂ k hi
      · rw [Function.extend_apply' _ _ _ h]
        exact h₁ i ⟨hi, by simpa using h⟩
  rw [Measure.map_apply (measurable_extend_pair he)
    (MeasurableSet.pi s.countable_toSet fun i _ => ht i), hpre, Measure.prod_prod,
    ComplexMatrix2.haarPi, ComplexMatrix2.haarPi, Measure.infinitePi_pi _ fun i _ => ht i,
    Measure.infinitePi_pi _ fun k _ => ht (e k),
    Finset.prod_preimage' e s he.injOn fun i => ComplexMatrix2.haarProb (t i), mul_comm,
    ← Finset.prod_filter_mul_prod_filter_not s (· ∈ Set.range e)]
end Replacing
theorem finsum_eq_finsum_mem_add_compl_image {C X : Type*} [Finite C] (P : Set X) (π : X → C)
    (hπ : Set.InjOn π P) (f : C → ℝ) (g : X → ℝ) (hfg : ∀ x ∈ P, f (π x) = g x) :
    ∑ᶠ c, f c = ∑ᶠ x ∈ P, g x + ∑ᶠ c ∈ (π '' P)ᶜ, f c := by
  have h₁ : ∑ᶠ c ∈ π '' P, f c = ∑ᶠ x ∈ P, g x := by
    rw [finsum_mem_image hπ]
    exact finsum_mem_congr rfl hfg
  rw [← h₁, Set.compl_eq_univ_sdiff,
    finsum_mem_add_sdiff (Set.subset_univ _) Set.finite_univ, finsum_mem_univ]
section Bounded
variable {a : ℝ}
def IsBoundedContinuous (f : GaugeField a → ℝ) : Prop :=
  Continuous f ∧ ∃ C : ℝ, ∀ U, |f U| ≤ C
theorem IsBoundedContinuous.add {f g : GaugeField a → ℝ} (hf : IsBoundedContinuous f)
    (hg : IsBoundedContinuous g) : IsBoundedContinuous fun U => f U + g U := by
  obtain ⟨hf, C, hC⟩ := hf
  obtain ⟨hg, D, hD⟩ := hg
  exact ⟨hf.add hg, C + D, fun U => (abs_add_le _ _).trans (add_le_add (hC U) (hD U))⟩
theorem IsBoundedContinuous.const_mul {f : GaugeField a → ℝ} (hf : IsBoundedContinuous f)
    (c : ℝ) : IsBoundedContinuous fun U => c * f U := by
  obtain ⟨hf, C, hC⟩ := hf
  refine ⟨continuous_const.mul hf, |c| * C, fun U => ?_⟩
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (hC U) (abs_nonneg c)
theorem IsBoundedContinuous.finsum_mem {X : Type*} {s : Set X} (hs : s.Finite)
    {f : X → GaugeField a → ℝ} (hf : ∀ x ∈ s, IsBoundedContinuous (f x)) :
    IsBoundedContinuous fun U => ∑ᶠ x ∈ s, f x U := by
  classical
  simp only [finsum_mem_eq_finite_toFinset_sum _ hs]
  have key : ∀ T : Finset X, (∀ x ∈ T, IsBoundedContinuous (f x)) →
      IsBoundedContinuous fun U => ∑ x ∈ T, f x U := by
    intro T
    induction T using Finset.induction_on with
    | empty => exact fun _ => ⟨by simpa using continuous_const, 0, by simp⟩
    | insert x T hx ih =>
      intro h
      simp only [Finset.sum_insert hx]
      exact (h x (Finset.mem_insert_self _ _)).add
        (ih fun y hy => h y (Finset.mem_insert_of_mem hy))
  exact key _ fun x hx => hf x (by simpa using hx)
theorem isBoundedContinuous_of_isRealLocalContinuous {f : GaugeField a → ℝ}
    (hf : IsRealLocalContinuous f) : IsBoundedContinuous f := by
  obtain ⟨hc, ⟨-, C, hC⟩, -⟩ := hf
  refine ⟨(Complex.continuous_re.comp hc).congr fun U => by simp, C, fun U => ?_⟩
  simpa using hC U
theorem isRealLocalContinuous_of_isBoundedContinuous (ha : 0 < a)
    (hfac : LinkFunctions.LocalObservablesSupports ha)
    {f : GaugeField a → ℝ} (hf : IsBoundedContinuous f) (hl : IsCylinderFunction f) :
    IsRealLocalContinuous f := by
  obtain ⟨hf, C, hC⟩ := hf
  have hc : Continuous fun U => (f U : ℂ) := Complex.continuous_ofReal.comp hf
  have ho : IsBoundedObservable fun U => (f U : ℂ) :=
    ⟨hc.measurable, C, fun U => by simpa using hC U⟩
  refine ⟨hc, ho, (hfac.2.2.1 _ ho).2 ?_⟩
  obtain ⟨W, h₁, h₂, h₃⟩ := hl
  exact ⟨W, h₁, h₂, fun U U' h => congrArg _ (h₃ U U' h)⟩
end Bounded
section Embedding
variable {a : ℝ}
theorem pointMap_shift (v x : LatticePoint a) : (shift v).pointMap x = x + v := Subtype.ext rfl
theorem overwriteLinks_of_mem {𝓢 : Set (Link a)} (h : HasNoOppositePairs 𝓢)
    (V : LinkVariables 𝓢) (U : GaugeField a) {b : Link a} (hb : b ∈ 𝓢) :
    overwriteLinks h V U b = V ⟨b, hb⟩ :=
  dif_pos hb
theorem overwriteLinks_of_notMem {𝓢 : Set (Link a)} (h : HasNoOppositePairs 𝓢)
    (V : LinkVariables 𝓢) (U : GaugeField a) {b : Link a} (hb : b ∉ 𝓢) (hr : b.opposite ∉ 𝓢) :
    overwriteLinks h V U b = U b :=
  (dif_neg hb).trans (dif_neg hr)
variable {Γ : PeriodSublattice a} {𝓛 𝓢 : Finset (Link a)}
def EndpointsWithinMinPeriod (Γ : PeriodSublattice a) (𝓢 : Finset (Link a)) : Prop :=
  ∀ x ∈ linkEndpoints 𝓢, ∀ y ∈ linkEndpoints 𝓢,
    linfNorm ((x : AmbientSpace) - (y : AmbientSpace)) < minPeriodNorm Γ
theorem period_eq_zero_of_endpoints (hd : EndpointsWithinMinPeriod Γ 𝓢) {x γ : LatticePoint a}
    (hγ : γ ∈ Γ.periods) (hx : x ∈ linkEndpoints 𝓢) (hy : x + γ ∈ linkEndpoints 𝓢) : γ = 0 := by
  by_contra h
  have h₁ : minPeriodNorm Γ ≤ linfNorm (γ : AmbientSpace) := by
    refine csInf_le ⟨0, ?_⟩ ⟨γ, hγ, h, rfl⟩
    rintro s ⟨δ, -, -, rfl⟩
    rw [← norm_eq_linfNorm]
    exact norm_nonneg _
  have h₂ := hd _ hy _ hx
  have h₃ : ((x + γ : LatticePoint a) : AmbientSpace) - (x : AmbientSpace) = (γ : AmbientSpace) := by
    simp
  rw [h₃] at h₂
  exact absurd h₂ (not_lt.2 h₁)
theorem positiveLink_translate_zero (b : PositiveLink a) : b.translate 0 = b :=
  Subtype.ext (Link.ext (add_zero _) (add_zero _))
theorem exists_translate_of_linkClass_eq {b c : PositiveLink a}
    (h : Γ.linkClass b = Γ.linkClass c) : ∃ γ ∈ Γ.periods, c = b.translate γ := by
  have h₁ : c ∈ Γ.linkOrbit c := ⟨0, zero_mem _, (positiveLink_translate_zero c).symm⟩
  have h₂ : Γ.linkOrbit b = Γ.linkOrbit c := congrArg Subtype.val h
  rw [← h₂] at h₁
  exact h₁
theorem eq_of_linkClass_eq (hd : EndpointsWithinMinPeriod Γ 𝓢) {b c : PositiveLink a}
    (hb : b.1 ∈ 𝓢) (hc : c.1 ∈ 𝓢) (h : Γ.linkClass b = Γ.linkClass c) : b = c := by
  obtain ⟨γ, hγ, rfl⟩ := exists_translate_of_linkClass_eq h
  have h₀ : γ = 0 := period_eq_zero_of_endpoints hd hγ ⟨b.1, hb, Or.inl rfl⟩ ⟨_, hc, Or.inl rfl⟩
  subst h₀
  exact (positiveLink_translate_zero b).symm
def windowLinkClass (Γ : PeriodSublattice a) (𝓛 : Finset (Link a))
    (hpos : ∀ b ∈ 𝓛, b.IsPositivelyOriented) (b : (𝓛 : Set (Link a))) : Γ.QuotientLink :=
  Γ.linkClass ⟨b.1, hpos b.1 b.2⟩
def replaceOnOrbits (hpos : ∀ b ∈ 𝓛, b.IsPositivelyOriented) (U : Γ.QuotientField)
    (V : LinkVariables (𝓛 : Set (Link a))) : Γ.QuotientField :=
  Function.extend (windowLinkClass Γ 𝓛 hpos) V U
theorem windowLinkClass_injective (hpos : ∀ b ∈ 𝓛, b.IsPositivelyOriented) (hL : 𝓛 ⊆ 𝓢)
    (hd : EndpointsWithinMinPeriod Γ 𝓢) : Function.Injective (windowLinkClass Γ 𝓛 hpos) := by
  intro b c h
  have := eq_of_linkClass_eq hd (b := ⟨b.1, hpos b.1 b.2⟩) (c := ⟨c.1, hpos c.1 c.2⟩)
    (hL b.2) (hL c.2) h
  exact Subtype.ext (congrArg (fun x : PositiveLink a => x.1) this)
theorem lift_of_positive (U : Γ.QuotientField) {b : Link a} (h : b.IsPositivelyOriented) :
    Γ.lift U b = U (Γ.linkClass ⟨b, h⟩) :=
  dif_pos h
theorem lift_replaceOnOrbits_of_not_mem_range (hpos : ∀ b ∈ 𝓛, b.IsPositivelyOriented)
    (U : Γ.QuotientField) (V : LinkVariables (𝓛 : Set (Link a))) (b : PositiveLink a)
    (hb : Γ.linkClass b ∉ Set.range (windowLinkClass Γ 𝓛 hpos)) :
    Γ.lift (replaceOnOrbits hpos U V) b.1 = Γ.lift U b.1 := by
  rw [lift_of_positive _ b.2, lift_of_positive _ b.2]
  exact Function.extend_apply' _ _ _ hb
theorem lift_replaceOnOrbits_eq_overwrite (ha : 0 < a) (hL : 𝓛 ⊆ 𝓢)
    (hS : (𝓢 : Set (Link a)) ⊆ positiveLinkSet a)
    (hpos : ∀ b ∈ 𝓛, b.IsPositivelyOriented) (h : HasNoOppositePairs (𝓛 : Set (Link a)))
    (hd : EndpointsWithinMinPeriod Γ 𝓢) (U : Γ.QuotientField)
    (V : LinkVariables (𝓛 : Set (Link a))) {b : Link a} (hb : b ∈ 𝓢) :
    Γ.lift (replaceOnOrbits hpos U V) b = overwriteLinks h V (Γ.lift U) b := by
  have hp : b ∈ positiveLinkSet a := hS hb
  have hp' : b.IsPositivelyOriented := mem_positiveLinks_iff.1 hp
  by_cases hbL : b ∈ (𝓛 : Set (Link a))
  · rw [overwriteLinks_of_mem h V _ hbL, lift_of_positive _ hp']
    exact (windowLinkClass_injective hpos hL hd).extend_apply V U ⟨b, hbL⟩
  · have hout : Γ.linkClass ⟨b, hp'⟩ ∉ Set.range (windowLinkClass Γ 𝓛 hpos) := by
      rintro ⟨c, hc⟩
      have := eq_of_linkClass_eq hd (b := ⟨c.1, hpos c.1 c.2⟩) (c := ⟨b, hp'⟩)
        (hL c.2) hb hc
      have hcb : c.1 = b := congrArg (fun x : PositiveLink a => x.1) this
      exact hbL (hcb ▸ c.2)
    have hr : b.opposite ∉ (𝓛 : Set (Link a)) := fun hr =>
      opposite_notMem_positiveLinks ha hp (hS (hL hr))
    rw [overwriteLinks_of_notMem h V _ hbL hr]
    exact lift_replaceOnOrbits_of_not_mem_range hpos U V ⟨b, hp'⟩ hout
theorem apply_lift_replaceOnOrbits {E : Type*} (ha : 0 < a) (hL : 𝓛 ⊆ 𝓢)
    (hS : (𝓢 : Set (Link a)) ⊆ positiveLinkSet a)
    (hpos : ∀ b ∈ 𝓛, b.IsPositivelyOriented) (h : HasNoOppositePairs (𝓛 : Set (Link a)))
    (hd : EndpointsWithinMinPeriod Γ 𝓢) {f : GaugeField a → E}
    (hf : DependsOnlyOnLinks (𝓢 : Set (Link a)) f) (U : Γ.QuotientField)
    (V : LinkVariables (𝓛 : Set (Link a))) :
    f (Γ.lift (replaceOnOrbits hpos U V)) = f (overwriteLinks h V (Γ.lift U)) :=
  hf _ _ (funext fun b => lift_replaceOnOrbits_eq_overwrite ha hL hS hpos h hd U V b.2)
end Embedding
section Plaquettes
variable {a : ℝ}
theorem cornerSet_shift (hm : SymmetriesTransportPlaquettes a) (γ : LatticePoint a)
    (p : ElementaryPlaquette a) :
    ((shift γ).plaquetteMap p).cornerSet = (fun x => x + γ) '' p.cornerSet := by
  rw [((hm (shift γ)).1 p).2]
  exact congrArg (· '' p.cornerSet) (funext (pointMap_shift γ))
def CornerSetInjective (a : ℝ) : Prop :=
  ∀ p p' : ElementaryPlaquette a, p.cornerSet = p'.cornerSet → p = p'
theorem plaquetteMap_shift_zero (hm : SymmetriesTransportPlaquettes a) (hc : CornerSetInjective a)
    (p : ElementaryPlaquette a) : (shift (0 : LatticePoint a)).plaquetteMap p = p :=
  hc _ _ (by rw [cornerSet_shift hm]; simp)
theorem plaquetteMap_shift_shift (hm : SymmetriesTransportPlaquettes a) (hc : CornerSetInjective a)
    (δ γ : LatticePoint a) (p : ElementaryPlaquette a) :
    (shift δ).plaquetteMap ((shift γ).plaquetteMap p) = (shift (γ + δ)).plaquetteMap p :=
  hc _ _ (by
    rw [cornerSet_shift hm, cornerSet_shift hm, cornerSet_shift hm, Set.image_image]
    simp only [add_assoc])
variable {Γ : PeriodSublattice a}
theorem mem_plaquetteOrbit_self (hm : SymmetriesTransportPlaquettes a)
    (hc : CornerSetInjective a) (p : ElementaryPlaquette a) : p ∈ Γ.plaquetteOrbit p :=
  ⟨0, zero_mem _, (plaquetteMap_shift_zero hm hc p).symm⟩
theorem plaquetteOrbit_eq_of_mem (hm : SymmetriesTransportPlaquettes a)
    (hc : CornerSetInjective a) {p q : ElementaryPlaquette a} (h : q ∈ Γ.plaquetteOrbit p) :
    Γ.plaquetteOrbit q = Γ.plaquetteOrbit p := by
  obtain ⟨γ, hγ, rfl⟩ := h
  ext x
  constructor
  · rintro ⟨δ, hδ, rfl⟩
    exact ⟨γ + δ, add_mem hγ hδ, plaquetteMap_shift_shift hm hc δ γ p⟩
  · rintro ⟨δ, hδ, rfl⟩
    refine ⟨-γ + δ, add_mem (neg_mem hγ) hδ, ?_⟩
    rw [plaquetteMap_shift_shift hm hc, add_neg_cancel_left]
theorem exists_edge_of_corner (p : ElementaryPlaquette a) {x : LatticePoint a} (hx : x ∈ p.cornerSet) :
    ∃ b ∈ edgesOf p, x = b.initial ∨ x = b.terminal := by
  have h₀ : p.corner ∈ p.cornerSet := by simp [ElementaryPlaquette.cornerSet]
  have h₁ : p.corner + axisStep a p.lowAxis ∈ p.cornerSet := by simp [ElementaryPlaquette.cornerSet]
  have h₂ : p.corner + axisStep a p.lowAxis + axisStep a p.highAxis ∈ p.cornerSet := by
    simp [ElementaryPlaquette.cornerSet]
  have h₃ : p.corner + axisStep a p.highAxis ∈ p.cornerSet := by simp [ElementaryPlaquette.cornerSet]
  rcases hx with rfl | rfl | rfl | hx
  · exact ⟨Link.forwardFrom p.corner p.lowAxis, ⟨⟨_, _, rfl⟩, h₀, h₁⟩, Or.inl rfl⟩
  · exact ⟨Link.forwardFrom p.corner p.lowAxis, ⟨⟨_, _, rfl⟩, h₀, h₁⟩, Or.inr rfl⟩
  · exact ⟨Link.forwardFrom (p.corner + axisStep a p.lowAxis) p.highAxis, ⟨⟨_, _, rfl⟩, h₁, h₂⟩,
      Or.inr rfl⟩
  · have hx' : x = p.corner + axisStep a p.highAxis := hx
    subst hx'
    exact ⟨Link.forwardFrom p.corner p.highAxis, ⟨⟨_, _, rfl⟩, h₀, h₃⟩, Or.inr rfl⟩
variable {𝓛 𝓢 : Finset (Link a)}
theorem corner_mem_linkEndpoints
    (hside : ∀ p ∈ plaquettesTouching 𝓛, edgesOf p ⊆ (𝓢 : Set (Link a)))
    {p : ElementaryPlaquette a} (hp : p ∈ plaquettesTouching 𝓛) {x : LatticePoint a}
    (hx : x ∈ p.cornerSet) : x ∈ linkEndpoints 𝓢 := by
  obtain ⟨b, hb, h⟩ := exists_edge_of_corner p hx
  exact ⟨b, hside p hp hb, h⟩
theorem faceClass_injOn (hm : SymmetriesTransportPlaquettes a) (hc : CornerSetInjective a)
    (hside : ∀ p ∈ plaquettesTouching 𝓛, edgesOf p ⊆ (𝓢 : Set (Link a)))
    (hd : EndpointsWithinMinPeriod Γ 𝓢) :
    Set.InjOn Γ.faceClass (plaquettesTouching 𝓛) := by
  intro p hp q hq h
  have h₂ : Γ.plaquetteOrbit p = Γ.plaquetteOrbit q := congrArg Subtype.val h
  have h₃ : q ∈ Γ.plaquetteOrbit p := h₂ ▸ mem_plaquetteOrbit_self hm hc q
  obtain ⟨γ, hγ, rfl⟩ := h₃
  have hx : p.corner ∈ p.cornerSet := by simp [ElementaryPlaquette.cornerSet]
  have hy : p.corner + γ ∈ ((shift γ).plaquetteMap p).cornerSet := by
    rw [cornerSet_shift hm]
    exact ⟨_, hx, rfl⟩
  have h₀ := period_eq_zero_of_endpoints hd hγ (corner_mem_linkEndpoints hside hp hx)
    (corner_mem_linkEndpoints hside hq hy)
  subst h₀
  exact (plaquetteMap_shift_zero hm hc p).symm
theorem quotientFaceEnergy_faceClass (hm : SymmetriesTransportPlaquettes a)
    (hc : CornerSetInjective a) (ho : PeriodizationOrbitInvariant Γ)
    (U : Γ.QuotientField) (p : ElementaryPlaquette a) :
    Γ.quotientFaceEnergy U (Γ.faceClass p) = faceEnergy (Γ.lift U) p := by
  have hq := (Γ.quotientPlaquette_nonempty (Γ.faceClass p)).some_mem
  exact congrFun (ho.2.1 _ p (plaquetteOrbit_eq_of_mem hm hc hq)) U
theorem quotientFaceEnergy_replace_of_not_mem (hm : SymmetriesTransportPlaquettes a)
    (hc : CornerSetInjective a)
    (hfun : ∀ p : ElementaryPlaquette a, DependsOnlyOnLinks (edgesOf p)
      (fun U : GaugeField a => faceEnergy U p))
    (hpos : ∀ b ∈ 𝓛, b.IsPositivelyOriented) (c : Γ.QuotientPlaquette)
    (hout : c ∉ Γ.faceClass '' plaquettesTouching 𝓛) (U : Γ.QuotientField)
    (V : LinkVariables (𝓛 : Set (Link a))) :
    Γ.quotientFaceEnergy (replaceOnOrbits hpos U V) c = Γ.quotientFaceEnergy U c := by
  have hq := (Γ.quotientPlaquette_nonempty c).some_mem
  set q := (Γ.quotientPlaquette_nonempty c).some with hqdef
  obtain ⟨p₀, hp₀⟩ := c.2
  have hq' : q ∈ Γ.plaquetteOrbit p₀ := by rw [hp₀]; exact hq
  have horb : Γ.plaquetteOrbit q = c.1 := (plaquetteOrbit_eq_of_mem hm hc hq').trans hp₀
  change faceEnergy (Γ.lift (replaceOnOrbits hpos U V)) q = faceEnergy (Γ.lift U) q
  refine hfun q _ _ (funext fun b => ?_)
  have hb : b.1.IsPositivelyOriented := mem_positiveLinks_iff.1 b.2.1
  refine lift_replaceOnOrbits_of_not_mem_range hpos U V ⟨b.1, hb⟩ ?_
  rintro ⟨l, hl⟩
  obtain ⟨γ, hγ, hbl⟩ := exists_translate_of_linkClass_eq hl.symm
  have hbl' : l.1 = (PositiveLink.translate ⟨b.1, hb⟩ γ).1 := congrArg Subtype.val hbl
  refine hout ⟨(shift γ).plaquetteMap q, ⟨l.1, ⟨?_, ?_, ?_⟩, Or.inl l.2⟩, ?_⟩
  · rw [mem_positiveLinks_iff]
    exact hpos l.1 l.2
  · rw [cornerSet_shift hm, hbl']
    exact ⟨_, b.2.2.1, rfl⟩
  · rw [cornerSet_shift hm, hbl']
    exact ⟨_, b.2.2.2, rfl⟩
  · refine Subtype.ext ?_
    exact (plaquetteOrbit_eq_of_mem hm hc ⟨γ, hγ, rfl⟩).trans horb
end Plaquettes
section Terms
variable {a : ℝ} (ha : 0 < a) {A : SingleGeneratorArray a} {Γ : PeriodSublattice a}
  {𝓛 𝓢 : Finset (Link a)}
def cosetOf (A : SingleGeneratorArray a) (Γ : PeriodSublattice a) (v : A.sublattice) :
    A.QuotientClasses Γ :=
  QuotientAddGroup.mk v
theorem linkSupport_translate (hm : SymmetriesTransportLinksAndSupports a ha) (v : A.sublattice) :
    linkSupport ha (A.translate v) = shiftedLinks (linkSupport ha A.gen) v :=
  (hm.2 v).2 ℝ A.gen
theorem cosetOf_eq {v w : A.sublattice} (h : cosetOf A Γ v = cosetOf A Γ w) :
    -(v : LatticePoint a) + w ∈ Γ.periods :=
  AddSubgroup.mem_addSubgroupOf.1 (QuotientAddGroup.eq.1 h)
theorem cosetOf_injOn (hm : SymmetriesTransportLinksAndSupports a ha)
    (hS : (𝓛 : Set (Link a)) ⊆ positiveLinkSet a)
    (hsupp : ∀ v ∈ A.supportIndices ha 𝓛, linkSupport ha (A.translate v) ⊆ (𝓢 : Set (Link a)))
    (hd : EndpointsWithinMinPeriod Γ 𝓢) : Set.InjOn (cosetOf A Γ) (A.supportIndices ha 𝓛) := by
  intro v hv w hw h
  have hγ := cosetOf_eq h
  obtain ⟨b, hbL, hread⟩ := hv
  have hbsupp : b ∈ linkSupport ha (A.translate v) := ⟨hS hbL, hread⟩
  have hbS := hsupp v ⟨b, hbL, hread⟩ hbsupp
  rw [linkSupport_translate ha hm] at hbsupp
  obtain ⟨b₀, hb₀, rfl⟩ := hbsupp
  have hwS : (shift (w : LatticePoint a)).linkMap b₀ ∈ (𝓢 : Set (Link a)) :=
    hsupp w hw (by rw [linkSupport_translate ha hm]; exact ⟨b₀, hb₀, rfl⟩)
  have h₀ := period_eq_zero_of_endpoints hd hγ
    (x := ((shift (v : LatticePoint a)).linkMap b₀).initial)
    ⟨_, hbS, Or.inl rfl⟩ ⟨_, hwS, Or.inl (by
      change b₀.initial + (v : LatticePoint a) + (-(v : LatticePoint a) + w) =
        b₀.initial + (w : LatticePoint a)
      abel)⟩
  exact Subtype.ext (neg_add_eq_zero.1 h₀)
theorem periodize_translate_classRep (ho : PeriodizationOrbitInvariant Γ) (v : A.sublattice) :
    Γ.periodize (A.translate (A.classRep Γ (cosetOf A Γ v))) = Γ.periodize (A.translate v) := by
  have hw : cosetOf A Γ (A.classRep Γ (cosetOf A Γ v)) = cosetOf A Γ v :=
    QuotientAddGroup.out_eq' _
  have hγ := cosetOf_eq hw
  set w := A.classRep Γ (cosetOf A Γ v)
  have hproj : Γ.quotientMap (w : LatticePoint a) = Γ.quotientMap (v : LatticePoint a) :=
    QuotientAddGroup.eq.2 hγ
  refine ho.1 ℝ A.gen _ _ ?_
  ext x
  rw [mem_pointOrbit_iff, mem_pointOrbit_iff, hproj]
theorem periodize_translate_replace_of_not_mem (hm : SymmetriesTransportLinksAndSupports a ha)
    (hΓ : A.PeriodsWithin Γ)
    (hfun : ∀ v : A.sublattice, DependsOnlyOnLinks (linkSupport ha (A.translate v)) (A.translate v))
    (hpos : ∀ b ∈ 𝓛, b.IsPositivelyOriented) (c : A.QuotientClasses Γ)
    (hout : c ∉ cosetOf A Γ '' A.supportIndices ha 𝓛) (U : Γ.QuotientField)
    (V : LinkVariables (𝓛 : Set (Link a))) :
    Γ.periodize (A.translate (A.classRep Γ c)) (replaceOnOrbits hpos U V) =
      Γ.periodize (A.translate (A.classRep Γ c)) U := by
  have hv : cosetOf A Γ (A.classRep Γ c) = c := QuotientAddGroup.out_eq' _
  set v := A.classRep Γ c
  refine hfun v _ _ (funext fun b => ?_)
  have hb : b.1.IsPositivelyOriented := mem_positiveLinks_iff.1 b.2.1
  refine lift_replaceOnOrbits_of_not_mem_range hpos U V ⟨b.1, hb⟩ ?_
  rintro ⟨l, hl⟩
  obtain ⟨γ, hγ, hbl⟩ := exists_translate_of_linkClass_eq hl.symm
  have hbl' : l.1 = (PositiveLink.translate ⟨b.1, hb⟩ γ).1 := congrArg Subtype.val hbl
  obtain ⟨b₀, hb₀, hb₀'⟩ := (Set.ext_iff.1 (linkSupport_translate ha hm v) b.1).1 b.2
  let w : A.sublattice := v + ⟨γ, hΓ hγ⟩
  have hread : l.1 ∈ linkSupport ha (A.translate w) := by
    rw [linkSupport_translate ha hm]
    refine ⟨b₀, hb₀, ?_⟩
    rw [hbl']
    refine Link.ext ?_ ?_
    · change b₀.initial + ((v : LatticePoint a) + γ) = b.1.initial + γ
      rw [← hb₀']
      change _ = b₀.initial + (v : LatticePoint a) + γ
      abel
    · change b₀.terminal + ((v : LatticePoint a) + γ) = b.1.terminal + γ
      rw [← hb₀']
      change _ = b₀.terminal + (v : LatticePoint a) + γ
      abel
  refine hout ⟨w, ⟨l.1, l.2, hread.2⟩, ?_⟩
  refine Eq.trans ?_ hv
  refine QuotientAddGroup.eq.2 (AddSubgroup.mem_addSubgroupOf.2 ?_)
  have : ((-w + v : A.sublattice) : LatticePoint a) = -γ := by
    change -((v : LatticePoint a) + γ) + (v : LatticePoint a) = -γ
    abel
  rw [this]
  exact neg_mem hγ
end Terms
section Energy
variable {a : ℝ} (ha : 0 < a) (A : SingleGeneratorArray a)
theorem translate_isRealLocalContinuous
    (hk : ∀ v : LatticePoint a, (fun F : GaugeField a → ℂ => (shift v).actOn F) ''
      continuousLocal a = continuousLocal a) (v : A.sublattice) :
    IsRealLocalContinuous (A.translate v) := by
  change (fun U => ((A.translate v U : ℝ) : ℂ)) ∈ continuousLocal a
  rw [← hk v]
  exact ⟨_, A.gen_mem, rfl⟩
theorem dependsOnlyOnLinks_linkSupport (hfac : LinkFunctions.LocalObservablesSupports ha)
    {f : GaugeField a → ℝ} (hf : IsRealLocalContinuous f) :
    DependsOnlyOnLinks (linkSupport ha f) f := by
  obtain ⟨-, hobs, hloc⟩ := hf
  obtain ⟨W, hWf, hWs, hWF⟩ := (hfac.2.2.1 _ hobs).1 hloc
  have h₁ := (hfac.2.2.2 _ W hobs hWf hWs hWF).2.1
  have hs : linkSupport ha (fun U => (f U : ℂ)) = linkSupport ha f := by
    ext b
    simp only [linkSupport, DependsOnLink, IsIndependentOfLinks, Complex.ofReal_inj,
      Set.mem_ofPred_eq]
  intro U U' h
  rw [← hs] at h
  exact Complex.ofReal_injective (h₁ U U' h)
variable {Γ : PeriodSublattice a} {𝓛 𝓢 : Finset (Link a)} {β t : ℝ}
theorem tiltedEnergy_dependsOnlyOnLinks
    (hfunP : ∀ p : ElementaryPlaquette a, DependsOnlyOnLinks (edgesOf p)
      (fun U : GaugeField a => faceEnergy U p))
    (hfunT : ∀ v : A.sublattice, DependsOnlyOnLinks (linkSupport ha (A.translate v)) (A.translate v))
    (hW : A.WindowFitsInQuotient ha Γ 𝓛 𝓢) :
    DependsOnlyOnLinks (𝓢 : Set (Link a)) (A.tiltedEnergy ha β t 𝓛) := by
  intro U U' h
  have key : ∀ S : Set (Link a), S ⊆ (𝓢 : Set (Link a)) →
      restrictField U S = restrictField U' S := fun S hS =>
    funext fun b => congrFun h ⟨b.1, hS b.2⟩
  have h₁ : ∑ᶠ p ∈ plaquettesTouching 𝓛, faceEnergy U p =
      ∑ᶠ p ∈ plaquettesTouching 𝓛, faceEnergy U' p :=
    finsum_mem_congr rfl fun p hp => hfunP p U U' (key _ (hW.edges_subset p hp))
  have h₂ : ∑ᶠ v ∈ A.supportIndices ha 𝓛, A.translate v U =
      ∑ᶠ v ∈ A.supportIndices ha 𝓛, A.translate v U' :=
    finsum_mem_congr rfl fun v hv => hfunT v U U' (key _ (hW.linkSupport_subset v hv))
  simp only [tiltedEnergy, wilsonLinkEnergy, h₁, h₂]
theorem tiltedEnergy_isBoundedContinuous
    (hPfin : (plaquettesTouching 𝓛).Finite) (hIfin : (A.supportIndices ha 𝓛).Finite)
    (hP : ∀ p : ElementaryPlaquette a, IsBoundedContinuous fun U : GaugeField a => faceEnergy U p)
    (hT : ∀ v : A.sublattice, IsBoundedContinuous (A.translate v)) :
    IsBoundedContinuous (A.tiltedEnergy ha β t 𝓛) := by
  have h₁ := (IsBoundedContinuous.finsum_mem hPfin fun p _ => hP p).const_mul β
  have h₂ := (IsBoundedContinuous.finsum_mem hIfin fun v _ => hT v).const_mul (-t)
  have h₃ := h₁.add h₂
  have h₄ : A.tiltedEnergy ha β t 𝓛 = fun U : GaugeField a =>
      β * ∑ᶠ p ∈ plaquettesTouching 𝓛, faceEnergy U p +
        -t * ∑ᶠ v ∈ A.supportIndices ha 𝓛, A.translate v U := by
    funext U
    simp only [tiltedEnergy, wilsonLinkEnergy]
    ring
  rw [h₄]
  exact h₃
def logDensity (A : SingleGeneratorArray a) (Γ : PeriodSublattice a) (β t : ℝ)
    (U : Γ.QuotientField) : ℝ :=
  t * A.foldedSum Γ U - β * ∑ᶠ p : Γ.QuotientPlaquette, Γ.quotientFaceEnergy U p
theorem logDensity_add_tiltedEnergy (hm : SymmetriesTransportPlaquettes a)
    (hc : CornerSetInjective a) (ho : PeriodizationOrbitInvariant Γ)
    [Finite (A.QuotientClasses Γ)] [Finite Γ.QuotientPlaquette]
    (hP : Set.InjOn Γ.faceClass (plaquettesTouching 𝓛))
    (hI : Set.InjOn (cosetOf A Γ) (A.supportIndices ha 𝓛)) (U : Γ.QuotientField) :
    logDensity A Γ β t U + A.tiltedEnergy ha β t 𝓛 (Γ.lift U) =
      t * ∑ᶠ c ∈ (cosetOf A Γ '' A.supportIndices ha 𝓛)ᶜ,
          Γ.periodize (A.translate (A.classRep Γ c)) U -
        β * ∑ᶠ c ∈ (Γ.faceClass '' plaquettesTouching 𝓛)ᶜ, Γ.quotientFaceEnergy U c := by
  have h₁ := finsum_eq_finsum_mem_add_compl_image (A.supportIndices ha 𝓛) (cosetOf A Γ) hI
    (fun c => Γ.periodize (A.translate (A.classRep Γ c)) U)
    (fun v => A.translate v (Γ.lift U))
    (fun v _ => congrFun (periodize_translate_classRep ho v) U)
  have h₂ := finsum_eq_finsum_mem_add_compl_image (plaquettesTouching 𝓛) Γ.faceClass hP
    (fun c => Γ.quotientFaceEnergy U c)
    (fun p => faceEnergy (Γ.lift U) p)
    (fun p _ => quotientFaceEnergy_faceClass hm hc ho U p)
  simp only [logDensity, foldedSum, tiltedEnergy, wilsonLinkEnergy, h₁, h₂]
  ring
end Energy
section Integrals
variable {a : ℝ} (A : SingleGeneratorArray a) {Γ : PeriodSublattice a}
theorem integral_liftedTiltMeasure (hΓ : A.PeriodsWithin Γ) {β t : ℝ}
    (hext : Measurable Γ.lift) (hw : Measurable (A.tiltWeight Γ β t))
    {Ψ : GaugeField a → ℂ} (hΨ : Measurable Ψ) :
    ∫ U, Ψ U ∂A.liftedTiltMeasure hΓ β t =
      ((ENNReal.ofReal (A.tiltNormalizer hΓ β t))⁻¹).toReal •
        ∫ U, (A.tiltWeight Γ β t U : ℂ) * Ψ (Γ.lift U) ∂Γ.quotientHaar := by
  unfold liftedTiltMeasure
  rw [integral_map hext.aemeasurable hΨ.aestronglyMeasurable]
  unfold tiltMeasure
  rw [integral_smul_measure, integral_withDensity_eq_integral_toReal_smul hw.ennreal_ofReal
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  congr 1
  refine integral_congr_ae (ae_of_all _ fun U => ?_)
  have h₀ : 0 ≤ A.tiltWeight Γ β t U := (Real.exp_pos _).le
  simp only [ENNReal.toReal_ofReal h₀, Complex.real_smul]
variable {𝓛 : Finset (Link a)}
theorem integral_eq_integral_replaceOnOrbits (hpos : ∀ b ∈ 𝓛, b.IsPositivelyOriented)
    (he : Function.Injective (windowLinkClass Γ 𝓛 hpos)) {Ξ : Γ.QuotientField → ℂ}
    (hΞ : Measurable Ξ) (hb : ∃ C : ℝ, ∀ U, ‖Ξ U‖ ≤ C) :
    ∫ U, Ξ U ∂Γ.quotientHaar =
      ∫ U, ∫ V, Ξ (replaceOnOrbits hpos U V) ∂LinkVariables.haarMeasure (𝓛 : Set (Link a))
        ∂Γ.quotientHaar := by
  obtain ⟨C, hC⟩ := hb
  have hT := measurable_extend_pair (κ := (𝓛 : Set (Link a))) he
  have hmap := map_extend_haarPi (ι := Γ.QuotientLink) (κ := (𝓛 : Set (Link a))) he
  have h₁ : IsProbabilityMeasure Γ.quotientHaar := isProbabilityMeasure_haarPi _
  have h₂ : IsProbabilityMeasure (LinkVariables.haarMeasure (𝓛 : Set (Link a))) :=
    isProbabilityMeasure_haarPi _
  have hint : Integrable (fun q : Γ.QuotientField × LinkVariables (𝓛 : Set (Link a)) =>
      Ξ (replaceOnOrbits hpos q.1 q.2))
      (Γ.quotientHaar.prod (LinkVariables.haarMeasure (𝓛 : Set (Link a)))) := Integrable.of_bound (hΞ.comp hT).aestronglyMeasurable C (ae_of_all _ fun q => hC _)
  calc ∫ U, Ξ U ∂Γ.quotientHaar
      = ∫ U, Ξ U ∂Measure.map (fun q : (Γ.QuotientLink → ComplexMatrix2.specialUnitary) ×
            LinkVariables (𝓛 : Set (Link a)) =>
              Function.extend (windowLinkClass Γ 𝓛 hpos) q.2 q.1)
          ((ComplexMatrix2.haarPi Γ.QuotientLink).prod
            (LinkVariables.haarMeasure (𝓛 : Set (Link a)))) := by
        rw [show LinkVariables.haarMeasure (𝓛 : Set (Link a)) =
            ComplexMatrix2.haarPi (𝓛 : Set (Link a)) from rfl, hmap]
        rfl
    _ = ∫ q, Ξ (replaceOnOrbits hpos q.1 q.2)
          ∂Γ.quotientHaar.prod (LinkVariables.haarMeasure (𝓛 : Set (Link a))) :=
        integral_map hT.aemeasurable hΞ.aestronglyMeasurable
    _ = _ := integral_prod _ hint
end Integrals
theorem holds (hact : LatticeSymmetryActionOnFields)
    (hfac : LinkFunctions.Assertion)
    (hker : LinkKernelProperties)
    (hmov : SymmetriesTransportLinksSupportsAndPlaquettes)
    (horb : PeriodSublatticeQuotientFacts)
    (hpla : FaceEnergyIndependentOfBasepointAndOrientation) : Statement := by
  intro a ha β hβ A t Γ hΓ 𝓛 𝓢 hL hS hW F hFb hFm
  have : SecondCountableTopology ComplexMatrix2.specialUnitary :=
    inferInstanceAs (SecondCountableTopology
      {x : Fin 2 → Fin 2 → ℂ // x ∈ (ComplexMatrix2.specialUnitary : Set ComplexMatrix2)})
  obtain ⟨-, hfacB, hfacC, -⟩ := hfac a ha
  obtain ⟨-, hmB, hmP⟩ := hmov a ha
  obtain ⟨-, hplA⟩ := hpla
  obtain ⟨-, hplS, hdet, -⟩ := hplA a ha
  obtain ⟨hfin, ⟨hextc, -, -⟩, ho⟩ := horb a ha Γ
  have hcorn : CornerSetInjective a := hdet
  have : Finite Γ.QuotientPlaquette := hfin.2.2.2.1
  have : Finite (A.QuotientClasses Γ) := hfin.2.2.2.2 A.sublattice hΓ
  have hd : EndpointsWithinMinPeriod Γ 𝓢 := hW.linfNorm_lt_minPeriodNorm
  have hLS : (𝓛 : Set (Link a)) ⊆ 𝓢 := Finset.coe_subset.2 hL
  have hpos : ∀ b ∈ 𝓛, b.IsPositivelyOriented := fun b hb =>
    mem_positiveLinks_iff.1 (hS (hL hb))
  have hhold := hasNoOppositePairs_of_subset_positiveLinks ha (hLS.trans hS)
  have hk : ∀ v : LatticePoint a, (fun F : GaugeField a → ℂ => (shift v).actOn F) ''
      continuousLocal a = continuousLocal a := fun v =>
    (hact a ha (shift v) (shift v)).2.2.2.2.2.2
  have hTloc : ∀ v : A.sublattice, IsRealLocalContinuous (A.translate v) :=
    translate_isRealLocalContinuous A hk
  have hfunT : ∀ v : A.sublattice,
      DependsOnlyOnLinks (linkSupport ha (A.translate v)) (A.translate v) :=
    fun v => dependsOnlyOnLinks_linkSupport ha hfacC (hTloc v)
  have hfunP : ∀ p : ElementaryPlaquette a, DependsOnlyOnLinks (edgesOf p)
      (fun U : GaugeField a => faceEnergy U p) := fun p => (hplS p).2.2.1
  have hPinj := faceClass_injOn (Γ := Γ) hmP hcorn hW.edges_subset hd
  have hIinj := cosetOf_injOn (A := A) (Γ := Γ) ha hmB (hLS.trans hS) hW.linkSupport_subset hd
  have hPfin : (plaquettesTouching 𝓛).Finite :=
    Set.Finite.of_finite_image (Set.toFinite _) hPinj
  have hIfin : (A.supportIndices ha 𝓛).Finite :=
    Set.Finite.of_finite_image (Set.toFinite _) hIinj
  have hPcb : ∀ p : ElementaryPlaquette a,
      IsBoundedContinuous fun U : GaugeField a => faceEnergy U p := fun p =>
    isBoundedContinuous_of_isRealLocalContinuous (hplS p).2.1
  have hTcb : ∀ v : A.sublattice, IsBoundedContinuous (A.translate v) := fun v =>
    isBoundedContinuous_of_isRealLocalContinuous (hTloc v)
  have hHf : DependsOnlyOnLinks (𝓢 : Set (Link a)) (A.tiltedEnergy ha β t 𝓛) :=
    tiltedEnergy_dependsOnlyOnLinks ha A hfunP hfunT hW
  have hHloc : IsRealLocalContinuous (A.tiltedEnergy ha β t 𝓛) :=
    isRealLocalContinuous_of_isBoundedContinuous ha hfacC
      (tiltedEnergy_isBoundedContinuous ha A hPfin hIfin hPcb hTcb)
      ⟨𝓢, 𝓢.finite_toSet, hS, hHf⟩
  obtain ⟨hFm', hFf⟩ := ((hfacB 𝓢 hS F hFb).1.out 0 1).1 hFm
  have hFo : IsBoundedObservable F := ⟨hFm', hFb⟩
  obtain ⟨hkA, -, hkC, -⟩ := hker a ha 𝓛 hhold _ _ hHloc hHloc
  obtain ⟨-, -, -, hden, hGo, hGread, -, -⟩ := hkA.1 F hFo
  have hGf := hkC.1 𝓢 F hS hFo hHf hFf
  have hexpc : Continuous (logDensity A Γ β t) := by
    have h₁ : Continuous fun U => A.foldedSum Γ U := by
      have := Fintype.ofFinite (A.QuotientClasses Γ)
      simp only [foldedSum, finsum_eq_sum_of_fintype]
      exact continuous_finsetSum _ fun c _ => ho.2.2 ℝ _ (hTcb _).1
    have h₂ : Continuous fun U => ∑ᶠ p : Γ.QuotientPlaquette, Γ.quotientFaceEnergy U p := by
      let := Fintype.ofFinite Γ.QuotientPlaquette
      simp only [finsum_eq_sum_of_fintype]
      exact continuous_finsetSum _ fun c _ => ho.2.2 ℝ _ (hPcb _).1
    exact (continuous_const.mul h₁).sub (continuous_const.mul h₂)
  have hwc : Continuous (A.tiltWeight Γ β t) := Real.continuous_exp.comp hexpc
  have hextm : Measurable Γ.lift := hextc.measurable
  obtain ⟨Cw, hCw⟩ := isCompact_univ.exists_bound_of_continuousOn hwc.continuousOn
  have hΞm : ∀ Ψ : GaugeField a → ℂ, Measurable Ψ → Measurable fun U =>
      (A.tiltWeight Γ β t U : ℂ) * Ψ (Γ.lift U) := fun Ψ hΨ =>
    (Complex.continuous_ofReal.comp hwc).measurable.mul (hΨ.comp hextm)
  have hΞb : ∀ Ψ : GaugeField a → ℂ, (∃ C : ℝ, ∀ U, ‖Ψ U‖ ≤ C) → ∃ C : ℝ, ∀ U,
      ‖(A.tiltWeight Γ β t U : ℂ) * Ψ (Γ.lift U)‖ ≤ C := by
    rintro Ψ ⟨C, hC⟩
    refine ⟨Cw * C, fun U => ?_⟩
    rw [norm_mul, Complex.norm_real]
    exact mul_le_mul (hCw U (Set.mem_univ U)) (hC _) (norm_nonneg _)
      ((norm_nonneg _).trans (hCw U (Set.mem_univ U)))
  have he := windowLinkClass_injective hpos hL hd
  set G := A.tiltedKernel ha β t 𝓛 (hasNoOppositePairs_of_subset_positiveLinks ha (hLS.trans hS)) F
    with hG
  have hGm : Measurable G := hGo.1
  rw [integral_liftedTiltMeasure A hΓ hextm hwc.measurable hGm,
    integral_liftedTiltMeasure A hΓ hextm hwc.measurable hFm']
  congr 1
  rw [integral_eq_integral_replaceOnOrbits hpos he (hΞm G hGm) (hΞb G hGo.2),
    integral_eq_integral_replaceOnOrbits hpos he (hΞm F hFm') (hΞb F hFb)]
  refine integral_congr_ae (ae_of_all _ fun U => ?_)
  set X := Γ.lift U with hX
  set H := A.tiltedEnergy ha β t 𝓛 with hHdef
  have hexp : ∀ V : LinkVariables (𝓛 : Set (Link a)),
      ((A.tiltWeight Γ β t (replaceOnOrbits hpos U V) : ℝ) : ℂ) =
        ((Real.exp (logDensity A Γ β t U + H X) : ℝ) : ℂ) *
          ((Real.exp (-H (overwriteLinks hhold V X)) : ℝ) : ℂ) := by
    intro V
    have h₁ := logDensity_add_tiltedEnergy (β := β) (t := t) ha A hmP hcorn ho hPinj hIinj
      (replaceOnOrbits hpos U V)
    have h₂ := logDensity_add_tiltedEnergy (β := β) (t := t) ha A hmP hcorn ho hPinj hIinj U
    have h₃ : ∑ᶠ c ∈ (cosetOf A Γ '' A.supportIndices ha 𝓛)ᶜ,
        Γ.periodize (A.translate (A.classRep Γ c)) (replaceOnOrbits hpos U V) =
        ∑ᶠ c ∈ (cosetOf A Γ '' A.supportIndices ha 𝓛)ᶜ,
          Γ.periodize (A.translate (A.classRep Γ c)) U :=
      finsum_mem_congr rfl fun c hc =>
        periodize_translate_replace_of_not_mem ha hmB hΓ hfunT hpos c hc U V
    have h₄ : ∑ᶠ c ∈ (Γ.faceClass '' plaquettesTouching 𝓛)ᶜ,
        Γ.quotientFaceEnergy (replaceOnOrbits hpos U V) c =
        ∑ᶠ c ∈ (Γ.faceClass '' plaquettesTouching 𝓛)ᶜ, Γ.quotientFaceEnergy U c :=
      finsum_mem_congr rfl fun c hc =>
        quotientFaceEnergy_replace_of_not_mem hmP hcorn hfunP hpos c hc U V
    have h₅ : H (Γ.lift (replaceOnOrbits hpos U V)) = H (overwriteLinks hhold V X) :=
      apply_lift_replaceOnOrbits ha hL hS hpos hhold hd hHf U V
    rw [h₃, h₄, ← h₂] at h₁
    have h₁' : logDensity A Γ β t (replaceOnOrbits hpos U V) +
        H (Γ.lift (replaceOnOrbits hpos U V)) = logDensity A Γ β t U + H X := h₁
    rw [h₅] at h₁'
    have h₆ : logDensity A Γ β t (replaceOnOrbits hpos U V) =
        logDensity A Γ β t U + H X + -H (overwriteLinks hhold V X) := by linarith
    rw [← Complex.ofReal_mul, ← Real.exp_add, ← h₆]
    rfl
  have hdenpos : kernelDenominator 𝓛 hhold H X ≠ 0 :=
    ((Real.exp_pos _).trans_le (hden X)).ne'
  have hleft : ∫ V, ((A.tiltWeight Γ β t (replaceOnOrbits hpos U V) : ℝ) : ℂ) *
        G (Γ.lift (replaceOnOrbits hpos U V)) ∂LinkVariables.haarMeasure (𝓛 : Set (Link a)) =
      ((Real.exp (logDensity A Γ β t U + H X) : ℝ) : ℂ) * kernelNumerator 𝓛 hhold H F X := by
    have h₁ : ∀ V : LinkVariables (𝓛 : Set (Link a)),
        ((A.tiltWeight Γ β t (replaceOnOrbits hpos U V) : ℝ) : ℂ) *
          G (Γ.lift (replaceOnOrbits hpos U V)) =
        (((Real.exp (logDensity A Γ β t U + H X) : ℝ) : ℂ) * G X) *
          ((Real.exp (-H (overwriteLinks hhold V X)) : ℝ) : ℂ) := by
      intro V
      have h₂ : G (Γ.lift (replaceOnOrbits hpos U V)) = G (overwriteLinks hhold V X) :=
        apply_lift_replaceOnOrbits ha hL hS hpos hhold hd hGf U V
      have h₃ : G (overwriteLinks hhold V X) = G X := hGread V X
      rw [hexp V, h₂, h₃]
      ring
    simp only [h₁]
    rw [integral_const_mul, integral_complex_ofReal]
    have h₄ : G X = kernelNumerator 𝓛 hhold H F X / (kernelDenominator 𝓛 hhold H X : ℂ) := rfl
    have h₅ : ((kernelDenominator 𝓛 hhold H X : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hdenpos
    change _ * ((kernelDenominator 𝓛 hhold H X : ℝ) : ℂ) = _
    rw [h₄]
    field_simp
  have hright : ∫ V, ((A.tiltWeight Γ β t (replaceOnOrbits hpos U V) : ℝ) : ℂ) *
        F (Γ.lift (replaceOnOrbits hpos U V)) ∂LinkVariables.haarMeasure (𝓛 : Set (Link a)) =
      ((Real.exp (logDensity A Γ β t U + H X) : ℝ) : ℂ) * kernelNumerator 𝓛 hhold H F X := by
    have h₁ : ∀ V : LinkVariables (𝓛 : Set (Link a)),
        ((A.tiltWeight Γ β t (replaceOnOrbits hpos U V) : ℝ) : ℂ) *
          F (Γ.lift (replaceOnOrbits hpos U V)) =
        ((Real.exp (logDensity A Γ β t U + H X) : ℝ) : ℂ) *
          (F (overwriteLinks hhold V X) * ((Real.exp (-H (overwriteLinks hhold V X)) : ℝ) : ℂ)) := by
      intro V
      rw [hexp V, apply_lift_replaceOnOrbits ha hL hS hpos hhold hd hFf U V]
      ring
    simp only [h₁]
    rw [integral_const_mul]
    rfl
  exact hleft.trans hright.symm
end YangMills.Construction.GibbsAtFixedSpacing.EquilibriumInEmbeddableWindow
