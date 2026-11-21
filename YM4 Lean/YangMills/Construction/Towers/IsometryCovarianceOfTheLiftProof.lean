import YangMills.Construction.Towers.AveragingCommutesWithIsometriesAtTheSideInfinityProof
import YangMills.Construction.Towers.CompositesOfTheLiftsAndLayersOfSitesProof
import YangMills.Construction.Towers.IsometryCovarianceOfTheLift
import Mathlib
set_option autoImplicit false
open Set Filter YangMills.Construction.Matrices.GroupLieProduct YangMills.Construction.Matrices.GroupLieProduct.Subspaces
open scoped Topology Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.Tower.LiftSymmetryCovariance
theorem eventually_forall_of_finite_index {α X K : Type*} [Finite K] {l : Filter X} (key : α → K)
    {Q : K → X → Prop} (h : ∀ a, ∀ᶠ x in l, Q (key a) x) : ∀ᶠ x in l, ∀ a, Q (key a) x := by
  have hall : ∀ᶠ x in l, ∀ c : K, (∃ a, key a = c) → Q c x := by
    refine Filter.eventually_all.2 fun c => ?_
    by_cases hc : ∃ a, key a = c
    · obtain ⟨a₀, rfl⟩ := hc
      exact (h a₀).mono fun x hx _ => hx
    · exact Eventually.of_forall fun x h' => (hc h').elim
  exact hall.mono fun x hx a => hx _ ⟨a, rfl⟩
theorem eventually_comp_within {ι X : Type*} [Finite ι] [TopologicalSpace X] (x : X)
    {D : Set (ι → X)} {Q : (ι → X) → Prop} (h : ∀ᶠ W in 𝓝[D] (fun _ : ι => x), Q W) :
    ∀ᶠ W in 𝓝[D] (fun _ : ι => x), ∀ g : ι → ι, W ∘ g ∈ D → Q (W ∘ g) := by
  have h' := eventually_nhdsWithin_iff.1 h
  refine eventually_nhdsWithin_of_eventually_nhds (Filter.eventually_all.2 fun g => ?_)
  have hc : Continuous fun W : ι → X => W ∘ g := continuous_pi fun c => continuous_apply (g c)
  have ht : Tendsto (fun W : ι → X => W ∘ g) (𝓝 fun _ => x) (𝓝 fun _ => x) := hc.tendsto' _ _ rfl
  exact ht.eventually h'
theorem exists_pos_iterate_eq_id {ι : Type*} [Finite ι] {g : ι → ι} (hg : Function.Injective g) :
    ∃ m : ℕ, 0 < m ∧ g^[m] = id := by
  let e : Equiv.Perm ι := Equiv.ofBijective g ⟨hg, Finite.surjective_of_injective hg⟩
  refine ⟨orderOf e, orderOf_pos e, ?_⟩
  have h : (⇑e)^[orderOf e] = ⇑(e ^ orderOf e) := Equiv.Perm.iterate_eq_pow e _
  rw [pow_orderOf_eq_one] at h
  exact h
variable {L n k i j : ℕ}
theorem eventually_mem_of_isOpenNhdOfOne {𝒰 : Set (Edge L n k i → Matrices.ComplexMatrix2)}
    (h : IsOpenNhdOfOne 𝒰) :
    ∀ᶠ V in 𝓝[fieldSpace L n k i] trivialField L n k i, V ∈ 𝒰 := by apply _root_.YangMills.Construction.Tower.ProlongCompositesProof.eventually_mem_of_isOpenNhdOfOne <;> assumption
theorem continuousOn_of_isAnalyticFieldMap {𝒰 : Set (Edge L n k j → Matrices.ComplexMatrix2)}
    {m : (Edge L n k j → Matrices.ComplexMatrix2) → Edge L n k i → Matrices.ComplexMatrix2}
    (h : IsAnalyticFieldMap 𝒰 m) : ContinuousOn m 𝒰 := by apply _root_.YangMills.Construction.Tower.ProlongCompositesProof.continuousOn_of_isAnalyticFieldMap <;> assumption
theorem tendsto_of_isAnalyticFieldMap {𝒲 : Set (Edge L n k j → Matrices.ComplexMatrix2)}
    {m : (Edge L n k j → Matrices.ComplexMatrix2) → Edge L n k i → Matrices.ComplexMatrix2}
    (hW : IsOpenNhdOfOne 𝒲) (hA : IsAnalyticFieldMap 𝒲 m)
    (h1 : m (trivialField L n k j) = trivialField L n k i) :
    Tendsto m (𝓝[fieldSpace L n k j] trivialField L n k j)
      (𝓝[fieldSpace L n k i] trivialField L n k i) := by
  have hnear := eventually_mem_of_isOpenNhdOfOne hW
  have hc := continuousOn_of_isAnalyticFieldMap hA _ hW.2
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, hnear.mono fun W hW' => hA.2.1 hW'⟩
  have h := hc.tendsto.mono_left (nhdsWithin_le_of_mem (Filter.mem_of_superset hnear fun _ h => h))
  rwa [h1] at h
section VertexMaps
variable {f : PeriodicLattice.FourTorus L n → PeriodicLattice.FourTorus L n}
theorem coe_vertexImage (hm : MapsSublatticeOnto k j f) (x : Vertex L n k j) :
    (vertexImage (k := k) (j := j) f x : PeriodicLattice.FourTorus L n) = f x := by apply _root_.YangMills.Construction.Tower.BlockStructureProof.coe_torus_vertexImage <;> assumption
theorem vertexImage_surjective (hm : MapsSublatticeOnto k j f) :
    Function.Surjective (vertexImage (k := k) (j := j) f) := by
  intro x
  have hx : (x : PeriodicLattice.FourTorus L n) ∈
      f '' (PeriodicLattice.sublattice L n (PeriodicLattice.levelDepth k j) :
        Set (PeriodicLattice.FourTorus L n)) := by
    rw [hm]
    exact x.2
  obtain ⟨t, ht, e⟩ := hx
  exact ⟨⟨t, ht⟩, Subtype.ext ((coe_vertexImage hm _).trans e)⟩
theorem vertexImage_injective [Finite (Vertex L n k j)] (hm : MapsSublatticeOnto k j f) :
    Function.Injective (vertexImage (k := k) (j := j) f) :=
  Finite.injective_iff_surjective.2 (vertexImage_surjective hm)
theorem apply_vertexPreimage (hm : MapsSublatticeOnto k j f) (x : Vertex L n k j) :
    f (vertexPreimage (k := k) (j := j) f x) = x := by apply _root_.YangMills.Construction.Tower.ScalingInvariance.vertexPreimage_spec <;> assumption
theorem edgePreimage_endpoints [Finite (Vertex L n k j)] (hm : MapsSublatticeOnto k j f)
    (hb : MapsEdgesOnto k j f) (c : Edge L n k j) :
    (edgePreimage (k := k) (j := j) f c).source = vertexPreimage f c.source ∧
      (edgePreimage (k := k) (j := j) f c).target = vertexPreimage f c.target := by apply _root_.YangMills.Construction.Tower.FullSpace.EquivariantSmoothing.torusEdgePreimage_endpoints <;> assumption
theorem edgePreimage_injective [Finite (Vertex L n k j)] (hm : MapsSublatticeOnto k j f)
    (hb : MapsEdgesOnto k j f) : Function.Injective (edgePreimage (k := k) (j := j) f) := by
  intro c c' h
  obtain ⟨t, e⟩ := edgePreimage_endpoints hm hb c
  obtain ⟨t', e'⟩ := edgePreimage_endpoints hm hb c'
  have inj : ∀ x y : Vertex L n k j,
      vertexPreimage (k := k) (j := j) f x = vertexPreimage f y → x = y :=
    fun x y hxy => Subtype.ext (by rw [← apply_vertexPreimage hm x, ← apply_vertexPreimage hm y, hxy])
  refine PeriodicLattice.Bond.ext (inj _ _ ?_) (inj _ _ ?_)
  · rw [← t, ← t', h]
  · rw [← e, ← e', h]
theorem bijOn_blockSitesExceptCenter [Finite (Vertex L n k i)] (hm₀ : MapsSublatticeOnto k i f)
    (hm₁ : MapsSublatticeOnto k (i + 1) f) (y : Vertex L n k (i + 1))
    (hblock : f '' PeriodicLattice.unitBlock y =
      PeriodicLattice.unitBlock (vertexImage (k := k) f y))
    (hsub : PeriodicLattice.unitBlock y ⊆
      (PeriodicLattice.sublattice L n (PeriodicLattice.levelDepth k i) :
        Set (PeriodicLattice.FourTorus L n)))
    (hself : (y : PeriodicLattice.FourTorus L n) ∈ PeriodicLattice.unitBlock y) :
    BijOn (vertexImage (k := k) (j := i) f) (PeriodicLattice.blockSitesExceptCenter k i y)
      (PeriodicLattice.blockSitesExceptCenter k i (vertexImage (k := k) f y)) := by
  let y₀ : Vertex L n k i := ⟨y, hsub hself⟩
  refine ⟨fun z hz => ⟨?_, ?_⟩, (vertexImage_injective hm₀).injOn, fun z' hz' => ?_⟩
  · change (vertexImage (k := k) (j := i) f z : PeriodicLattice.FourTorus L n) ∈
      PeriodicLattice.unitBlock (vertexImage (k := k) f y)
    rw [coe_vertexImage hm₀, ← hblock]
    exact ⟨z, hz.1, rfl⟩
  · rw [coe_vertexImage hm₀, coe_vertexImage hm₁]
    intro h
    have h₀ : vertexImage (k := k) (j := i) f z = vertexImage (k := k) (j := i) f y₀ :=
      Subtype.ext (by rw [coe_vertexImage hm₀, coe_vertexImage hm₀, h])
    exact hz.2 (congrArg Subtype.val (vertexImage_injective hm₀ h₀))
  · have hz'' : (z' : PeriodicLattice.FourTorus L n) ∈ f '' PeriodicLattice.unitBlock y := by
      rw [hblock]
      exact hz'.1
    obtain ⟨t, ht, e⟩ := hz''
    refine ⟨⟨t, hsub ht⟩, ⟨ht, ?_⟩, Subtype.ext ((coe_vertexImage hm₀ _).trans e)⟩
    intro h
    apply hz'.2
    rw [coe_vertexImage hm₁, ← e]
    exact congrArg f h
theorem axialFunction_pushField [Finite (Vertex L n k i)] [Finite (Vertex L n k (i + 1))]
    (hm₀ : MapsSublatticeOnto k i f) (hm₁ : MapsSublatticeOnto k (i + 1) f)
    (hblock : ∀ y : Vertex L n k (i + 1),
      f '' PeriodicLattice.unitBlock y = PeriodicLattice.unitBlock (vertexImage (k := k) f y))
    (hsub : ∀ y : Vertex L n k (i + 1), PeriodicLattice.unitBlock y ⊆
      (PeriodicLattice.sublattice L n (PeriodicLattice.levelDepth k i) :
        Set (PeriodicLattice.FourTorus L n)))
    (hself : ∀ y : Vertex L n k (i + 1),
      (y : PeriodicLattice.FourTorus L n) ∈ PeriodicLattice.unitBlock y)
    {V : Edge L n k i → Matrices.ComplexMatrix2}
    (hc : ∀ y : Vertex L n k (i + 1),
      ∀ x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k i) y,
        PeriodicLattice.meanContourHolonomy (pushField f V) (vertexImage (k := k) f y)
          (vertexImage (k := k) (j := i) f x) = PeriodicLattice.meanContourHolonomy V y x) :
    axialFunction L n k i (pushField f V) = axialFunction L n k i V := by
  unfold axialFunction PeriodicLattice.axialGaugeFunction
  symm
  refine finsum_mem_eq_of_bijOn (vertexImage (k := k) f) ?_ fun y _ => ?_
  · exact ⟨fun _ _ => mem_univ _, (vertexImage_injective hm₁).injOn,
      fun y _ => (vertexImage_surjective hm₁ y).imp fun x hx => ⟨mem_univ _, hx⟩⟩
  · refine finsum_mem_eq_of_bijOn (vertexImage (k := k) (j := i) f)
      (bijOn_blockSitesExceptCenter hm₀ hm₁ y (hblock y) (hsub y) (hself y)) fun z hz => ?_
    rw [hc y z hz.1]
end VertexMaps
theorem statement_holds (hT : SublatticesSymmetriesScalingsAndProjections.Statement)
    (hFinite : QuotientLattices.TorusAndSpaceLatticeProperties)
    (hImages : GaugeAndSymmetryImages.statement)
    (hBlocks : BlockStructure)
    (hAvg : SmoothingEquivariantOnSides) : Statement := by
  intro L n k i hL hn hik b 𝒰 ε p hb hp
  have hL0 : 0 < L := by have := hL.2; omega
  have finite₀ := hFinite L hL n i k hn hik.le
  have finite₁ := hFinite L hL n (i + 1) k hn hik
  obtain ⟨-, ⟨-, -, -, -, -, -, -, -, -, -, hS₀, hB₀, -⟩, -⟩ := finite₀
  obtain ⟨-, ⟨-, -, -, -, -, -, -, -, -, -, hS₁, hB₁, -⟩, -⟩ := finite₁
  have : Finite (Vertex L n k i) := hS₀
  have : Finite (Vertex L n k (i + 1)) := hS₁
  have : Finite (Edge L n k i) := hB₀
  have : Finite (Edge L n k (i + 1)) := hB₁
  have hfacts : ∀ f : PeriodicLattice.FourTorus L n → PeriodicLattice.FourTorus L n,
      IsLevelSymmetry k (i + 1) f →
        MapsSublatticeOnto k i f ∧ MapsEdgesOnto k i f ∧ MapsEdgesOnto k (i + 1) f := by
    intro f hf
    obtain ⟨-, hrest⟩ := (hT L hL0 hL k).2.2.2.1 n hn (i + 1) hik f hf.1 hf.2
    exact ⟨(hrest i (Nat.le_succ i)).1, (hrest i (Nat.le_succ i)).2.1,
      (hrest (i + 1) le_rfl).2.1⟩
  have hblocks := (hBlocks L k (i + 1) hL (by omega) (by omega) hik).1 n hn
  have hself : ∀ y : Vertex L n k (i + 1),
      (y : PeriodicLattice.FourTorus L n) ∈ PeriodicLattice.unitBlock y := by
    intro y
    have h : (y : PeriodicLattice.FourTorus L n) ∈ PeriodicLattice.unitBlock y ∩
        (PeriodicLattice.sublattice L n (PeriodicLattice.levelDepth k (i + 1)) :
          Set (PeriodicLattice.FourTorus L n)) := by
      rw [hblocks.2.1.1 y]
      exact mem_singleton _
    exact h.1
  have hsub : ∀ y : Vertex L n k (i + 1), PeriodicLattice.unitBlock y ⊆
      (PeriodicLattice.sublattice L n (PeriodicLattice.levelDepth k i) :
        Set (PeriodicLattice.FourTorus L n)) :=
    fun y => (hblocks.1 y).2.2.2
  have hmem : ∀ {j : ℕ}, j ≤ k → ∀ f : PeriodicLattice.FourTorus L n → PeriodicLattice.FourTorus L n,
      IsDistancePreserving f → MapsSublatticeOnto k j f → ∀ U ∈ fieldSpace L n k j,
        pushField (k := k) (j := j) f U ∈ fieldSpace L n k j := by
    intro j hj f hf hm U hU
    have hUc : PeriodicLattice.IsGaugeField PeriodicLattice.complexGaugeGroup univ U :=
      ⟨fun c hc => (Matrix.mem_specialUnitaryGroup_iff.1 (hU.1 c hc)).2, hU.2⟩
    have hu : PeriodicLattice.IsGaugeMap PeriodicLattice.complexGaugeGroup
        (fun _ : Vertex L n k j => (1 : Matrices.ComplexMatrix2)) := fun _ => Matrix.det_one
    exact ((hImages L k j hL hj).1 n hn U _ f hUc hu hf hm).2.2.2 hU
  let Key : Type :=
    (Edge L n k i → Edge L n k i) × (Edge L n k (i + 1) → Edge L n k (i + 1)) ×
      (Vertex L n k i → Vertex L n k i) × (Vertex L n k (i + 1) → Vertex L n k (i + 1))
  let Iso : Type := {f : PeriodicLattice.FourTorus L n → PeriodicLattice.FourTorus L n //
    IsLevelSymmetry k (i + 1) f}
  let key : Iso → Key := fun f =>
    (edgePreimage (k := k) (j := i) f.1, edgePreimage (k := k) (j := i + 1) f.1,
      vertexImage (k := k) (j := i) f.1, vertexImage (k := k) (j := i + 1) f.1)
  let Q : Key → (Edge L n k i → Matrices.ComplexMatrix2) → Prop := fun c V =>
    (∀ y : Vertex L n k (i + 1),
      ∀ x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k i) y,
        PeriodicLattice.meanContourHolonomy (V ∘ c.1) (c.2.2.2 y) (c.2.2.1 x) =
          PeriodicLattice.meanContourHolonomy V y x) ∧
    smoothingStep L n k i (V ∘ c.1) = smoothingStep L n k i V ∘ c.2.1
  have : Finite Key := by
    dsimp only [Key]
    infer_instance
  have hQ : ∀ᶠ V in 𝓝[fieldSpace L n k i] (fun _ => (1 : Matrices.ComplexMatrix2)),
      ∀ f : Iso, Q (key f) V :=
    eventually_forall_of_finite_index key fun f => hAvg L hL n k i hn hik f.1 f.2.1 f.2.2
  have hFun : ∀ᶠ V in 𝓝[fieldSpace L n k i] (fun _ => (1 : Matrices.ComplexMatrix2)),
      ∀ f : PeriodicLattice.FourTorus L n → PeriodicLattice.FourTorus L n, IsLevelSymmetry k i f →
        b.energy i (pushField f V) = b.energy i V :=
    hb.energy_symmetry_invariant i le_rfl
  have hGood : ∀ᶠ V in 𝓝[fieldSpace L n k i] (fun _ => (1 : Matrices.ComplexMatrix2)),
      ∀ f : PeriodicLattice.FourTorus L n → PeriodicLattice.FourTorus L n,
        IsLevelSymmetry k (i + 1) f →
        b.gaugeFixedEnergy i (pushField f V) = b.gaugeFixedEnergy i V ∧
          smoothingStep L n k i (pushField f V) = pushField f (smoothingStep L n k i V) := by
    filter_upwards [hQ, hFun] with V h₁ h₂ f hf
    obtain ⟨hm₀, -, -⟩ := hfacts f hf
    obtain ⟨hc, ha⟩ := h₁ ⟨f, hf⟩
    refine ⟨?_, ha⟩
    unfold CriticalBranchData.gaugeFixedEnergy
    rw [h₂ f ⟨hf.1, hm₀⟩, axialFunction_pushField hm₀ hf.2 (hblocks.2.2.2 f hf.1 hf.2) hsub
      hself hc]
  obtain ⟨𝒲, h𝒲, hA⟩ := hp.analytic_section
  have hTend := tendsto_of_isAnalyticFieldMap h𝒲 hA hp.section_trivial
  let G : (Edge L n k (i + 1) → Matrices.ComplexMatrix2) → Prop := fun W =>
    (∀ f : PeriodicLattice.FourTorus L n → PeriodicLattice.FourTorus L n,
      IsLevelSymmetry k (i + 1) f →
      b.gaugeFixedEnergy i (pushField f (p W)) = b.gaugeFixedEnergy i (p W) ∧
        smoothingStep L n k i (pushField f (p W)) = pushField f (smoothingStep L n k i (p W))) ∧
    smoothingStep L n k i (p W) = W ∧
    (∀ V ∈ CriticalBranchData.levelFibre 𝒰 W, V ≠ p W →
      b.gaugeFixedEnergy i (p W) < b.gaugeFixedEnergy i V) ∧
    p W ∈ nearIdentityBall L n k i ε
  have hG : ∀ᶠ W in 𝓝[fieldSpace L n k (i + 1)] (fun _ => (1 : Matrices.ComplexMatrix2)), G W := by
    filter_upwards [hTend.eventually hGood, hp.smoothing_section, hp.isMin_fibre, hp.unique_critical]
      with W h₁ h₂ h₃ h₄
    exact ⟨h₁, h₂, h₃, h₄.1.1⟩
  unfold EventuallyNearIdentity
  filter_upwards [eventually_comp_within (1 : Matrices.ComplexMatrix2) hG, self_mem_nhdsWithin]
    with W hW hWD f hf
  obtain ⟨hm₀, -, hb₁⟩ := hfacts f hf
  have hstep : ∀ X, G X → G (pushField f X) →
      pushField f (p X) ≠ p (pushField f X) →
        b.gaugeFixedEnergy i (p (pushField f X)) < b.gaugeFixedEnergy i (p X) := by
    intro X hX hTX hne
    obtain ⟨hgood, havg, -, hball⟩ := hX
    obtain ⟨-, -, hmin, -⟩ := hTX
    have hU : pushField f (p X) ∈ CriticalBranchData.levelFibre 𝒰 (pushField f X) := by
      refine ⟨hp.ball_subset ⟨hmem hik.le f hf.1 hm₀ _ hball.1, fun c => hball.2 _⟩, ?_⟩
      rw [(hgood f hf).2, havg]
    have h := hmin _ hU hne
    rwa [(hgood f hf).1] at h
  obtain ⟨m, hm, hid⟩ := exists_pos_iterate_eq_id (edgePreimage_injective hf.2 hb₁)
  let X : ℕ → Edge L n k (i + 1) → Matrices.ComplexMatrix2 :=
    fun r => W ∘ (edgePreimage (k := k) (j := i + 1) f)^[r]
  have hXs : ∀ r, pushField f (X r) = X (r + 1) := by
    intro r
    funext c
    change W ((edgePreimage (k := k) (j := i + 1) f)^[r] (edgePreimage f c)) =
      W ((edgePreimage (k := k) (j := i + 1) f)^[r + 1] c)
    rw [Function.iterate_succ_apply]
  have hX0 : X 0 = W := rfl
  have hXm : X m = W := by
    funext c
    change W ((edgePreimage (k := k) (j := i + 1) f)^[m] c) = W c
    rw [hid]
    rfl
  have hXD : ∀ r, X r ∈ fieldSpace L n k (i + 1) := by
    intro r
    induction r with
    | zero => exact hWD
    | succ r ih =>
      rw [← hXs]
      exact hmem hik f hf.1 hf.2 _ ih
  have hGX : ∀ r, G (X r) := fun r => hW _ (hXD r)
  have hanti : Antitone fun r => b.gaugeFixedEnergy i (p (X r)) := by
    refine antitone_nat_of_succ_le fun r => ?_
    have hG₁ := hGX r
    have hG₂ := hGX (r + 1)
    rw [← hXs] at hG₂
    rw [← hXs]
    by_cases e : pushField f (p (X r)) = p (pushField f (X r))
    · rw [← e]
      exact (hG₁.1 f hf).1.le
    · exact (hstep _ hG₁ hG₂ e).le
  have h01 : b.gaugeFixedEnergy i (p (X 1)) ≤ b.gaugeFixedEnergy i (p (X 0)) := hanti (Nat.zero_le 1)
  have h1m : b.gaugeFixedEnergy i (p (X m)) ≤ b.gaugeFixedEnergy i (p (X 1)) := hanti hm
  rw [hXm] at h1m
  have hT1 : pushField f W = X 1 := hXs 0
  have hGW : G W := hGX 0
  have hGT : G (pushField f W) := hT1 ▸ hGX 1
  have hfin : pushField f (p W) = p (pushField f W) := by
    by_contra hne
    have h := hstep _ hGW hGT hne
    rw [hT1] at h
    exact absurd h (not_lt.2 h1m)
  exact ⟨hfin.symm, by rw [← hfin]; exact (hGW.1 f hf).1⟩
end YangMills.Construction.Tower.LiftSymmetryCovariance
end
