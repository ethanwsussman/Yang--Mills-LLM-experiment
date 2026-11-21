import YangMills.Construction.Lattice.BondsOfAContourLieInTheDoubleBlock
import YangMills.Construction.Lattice.ComplexAverageReadsTheDoubleBlock
import YangMills.Construction.Lattice.KernelsOnPositiveBondFamilies
import YangMills.Construction.Towers.LatticesIsometriesDilationsAndQuotientsOfATower
import YangMills.Construction.Towers.PolydiscServesAtTheSideInfinity
import Mathlib
set_option autoImplicit false
open Set Filter Topology
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.Tower.InfiniteSideAdmissibility
theorem isHolomorphicIn_congr {N N' : ℕ} {O : Set (Coordinates.ComplexCoordinates N)}
    {f g : Coordinates.ComplexCoordinates N → Coordinates.ComplexCoordinates N'}
    (h : Coordinates.ComplexCoordinates.IsHolomorphicIn O f)
    (e : EqOn f g O) : Coordinates.ComplexCoordinates.IsHolomorphicIn O g := by
  obtain ⟨ho, hc, hd⟩ := h
  refine ⟨ho, hc.congr e.symm, fun a ha i => ?_⟩
  have hcont : Continuous fun ζ : ℂ => a + ζ • Coordinates.ComplexCoordinates.stdBasisVector i := by
    fun_prop
  have hnear : ∀ᶠ ζ in 𝓝 (0 : ℂ), a + ζ • Coordinates.ComplexCoordinates.stdBasisVector i ∈ O := by
    have : a + (0 : ℂ) • Coordinates.ComplexCoordinates.stdBasisVector i ∈ O := by simpa using ha
    exact hcont.continuousAt.eventually_mem (ho.mem_nhds this)
  filter_upwards [hd a ha i, hnear.eventually_nhds] with ζ h₁ h₂
  refine h₁.congr_of_eventuallyEq ?_
  filter_upwards [h₂] with ξ hξ
  exact (e hξ).symm
theorem isHolomorphicOnSL2Power_congr {n : ℕ}
    {b : Module.Basis (Fin 3) ℂ Matrices.ComplexMatrix2.traceless}
    {U : Set (Fin n → Matrices.ComplexMatrix2)}
    {Φ Ψ : (Fin n → Matrices.ComplexMatrix2) → Matrices.ComplexMatrix2}
    (h : Coordinates.ComplexCoordinates.IsHolomorphicOnSL2Power b U Φ) (e : EqOn Φ Ψ U) :
    Coordinates.ComplexCoordinates.IsHolomorphicOnSL2Power b U Ψ := by
  obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := h
  refine ⟨h₁, h₂, fun X hX => e hX ▸ h₃ hX, h₄.congr e.symm, fun X hX => ?_⟩
  obtain ⟨W, h0, hW, hol⟩ := h₅ X hX
  have hq : ∀ w ∈ W, Coordinates.ComplexCoordinates.expChartQuotient Φ X
        (Coordinates.ComplexCoordinates.tracelessTuple b w) =
      Coordinates.ComplexCoordinates.expChartQuotient Ψ X
        (Coordinates.ComplexCoordinates.tracelessTuple b w) := fun w hw => by
    unfold Coordinates.ComplexCoordinates.expChartQuotient
    rw [e (hW w hw).1, e hX]
  refine ⟨W, h0, fun w hw => ⟨(hW w hw).1, hq w hw ▸ (hW w hw).2⟩, ?_⟩
  exact isHolomorphicIn_congr hol fun w hw => by simp only [hq w hw]
def reindexCLM {ι κ : Type} [Fintype ι] [Fintype κ] (e : ι ≃ κ) :
    (ι → Matrices.ComplexMatrix2) →L[ℂ] (κ → Matrices.ComplexMatrix2) :=
  ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (e.symm i)
theorem isHolomorphicBetween_reindex {ι κ : Type} [Fintype ι] [Fintype κ] (e : ι ≃ κ)
    {R : Set (ι → Matrices.ComplexMatrix2)} {R' : Set (κ → Matrices.ComplexMatrix2)}
    {f : (ι → Matrices.ComplexMatrix2) → Unit → Matrices.ComplexMatrix2}
    {f' : (κ → Matrices.ComplexMatrix2) → Unit → Matrices.ComplexMatrix2}
    (hR : ∀ v, v ∈ R ↔ v ∘ e.symm ∈ R')
    (hf : ∀ v ∈ R, f v = f' (v ∘ e.symm))
    (h : Matrices.ComplexMatrix2.IsHolomorphicBetween
      (fun _ : κ => Matrices.ComplexMatrix2.FactorKind.group)
      (fun _ : Unit => Matrices.ComplexMatrix2.FactorKind.group) R' f') :
    Matrices.ComplexMatrix2.IsHolomorphicBetween
      (fun _ : ι => Matrices.ComplexMatrix2.FactorKind.group)
      (fun _ : Unit => Matrices.ComplexMatrix2.FactorKind.group) R f := by
  obtain ⟨⟨O, hO, rfl⟩, hm, ha⟩ := h
  refine ⟨⟨reindexCLM e ⁻¹' O, hO.preimage (reindexCLM e).continuous, ?_⟩, ?_, ?_⟩
  · ext v
    refine (hR v).trans ⟨fun h => ⟨h.1, fun i => ?_⟩, fun h => ⟨h.1, fun i => h.2 (e.symm i)⟩⟩
    simpa using h.2 (e i)
  · intro v hv
    rw [hf v hv]
    exact hm ((hR v).1 hv)
  · intro v hv
    obtain ⟨F, hF, hev⟩ := ha _ ((hR v).1 hv)
    refine ⟨F ∘ reindexCLM e, AnalyticAt.comp (show AnalyticAt ℂ F (reindexCLM e v) from hF)
      ((reindexCLM e).analyticAt v), ?_⟩
    have ht : Tendsto (reindexCLM e) (𝓝[R] v) (𝓝[O ∩ Matrices.ComplexMatrix2.complexifiedProduct
        fun _ : κ => Matrices.ComplexMatrix2.FactorKind.group] (v ∘ e.symm)) :=
      tendsto_nhdsWithin_iff.2
        ⟨((reindexCLM e).continuous.tendsto v).mono_left nhdsWithin_le_nhds,
          eventually_mem_nhdsWithin.mono fun w hw => (hR w).1 hw⟩
    filter_upwards [ht.eventually hev, eventually_mem_nhdsWithin] with w hw hwR
    rw [hf w hwR]
    exact hw
section AtAnEdge
variable {L k j : ℕ} {c : FullSpace.Edge L k (j + 1)}
abbrev fineLinks (c : FullSpace.Edge L k (j + 1)) : Set (FullSpace.Edge L k j) :=
  FullSpace.doubleCubeLinks L (Tower.meshAt L k j) c
abbrev projLink (c : FullSpace.Edge L k (j + 1)) : Tower.Edge L 1 k (j + 1) :=
  FullSpace.projEdge L 1 k (j + 1) c
abbrev projLinks (c : FullSpace.Edge L k (j + 1)) : Set (Tower.Edge L 1 k j) :=
  PeriodicLattice.bondsInDoubleBlock (projLink c)
abbrev pushField (c : FullSpace.Edge L k (j + 1))
    (V : FullSpace.Edge L k j → Matrices.ComplexMatrix2) :
    Tower.Edge L 1 k j → Matrices.ComplexMatrix2 :=
  FullSpace.projField L 1 k j (fineLinks c) V
def ProjRespectsEdges (L k j : ℕ) : Prop :=
  ∀ b : FullSpace.Edge L k j,
    (FullSpace.projEdge L 1 k j b).source = FullSpace.projVertex L 1 k j b.initial ∧
    (FullSpace.projEdge L 1 k j b).target = FullSpace.projVertex L 1 k j b.terminal ∧
    (b.IsPositivelyOriented → (FullSpace.projEdge L 1 k j b).IsPositivelyOriented) ∧
    (FullSpace.projEdge L 1 k j b).opposite = FullSpace.projEdge L 1 k j b.opposite
theorem fineLinks_opposite {b : FullSpace.Edge L k j} (h : b ∈ fineLinks c) :
    b.opposite ∈ fineLinks c := ⟨h.2, h.1⟩
theorem projLinks_opposite {b : Tower.Edge L 1 k j} (h : b ∈ projLinks c) :
    b.opposite ∈ projLinks c := ⟨h.2, h.1⟩
theorem fullSpace_opposite_isPositivelyOriented {b : FullSpace.Edge L k j}
    (h : ¬b.IsPositivelyOriented) : b.opposite.IsPositivelyOriented := by
  obtain ⟨μ, e | e⟩ := b.isAdjacent
  · exact absurd ⟨μ, e⟩ h
  · refine ⟨μ, ?_⟩
    change b.initial - b.terminal = _
    rw [← neg_sub, e, neg_neg]
theorem periodic_opposite_isPositivelyOriented {b : Tower.Edge L 1 k j}
    (h : ¬b.IsPositivelyOriented) : b.opposite.IsPositivelyOriented := by
  obtain ⟨μ, e | e⟩ := b.isNeighbour
  · exact absurd ⟨μ, e⟩ h
  · refine ⟨μ, ?_⟩
    change b.source - b.target = _
    rw [← neg_sub, e, neg_neg]
theorem projEdge_bijOn (Q : FullSpace.ProjPreservesStructures L 1 k j c)
    (hb : ProjRespectsEdges L k j) :
    BijOn (FullSpace.projEdge L 1 k j) (fineLinks c) (projLinks c) := by
  refine ⟨fun b h => ?_, fun b₁ h₁ b₂ h₂ e => ?_, fun b' h' => ?_⟩
  · show _ ∈ PeriodicLattice.bondsInDoubleBlock (projLink c)
    rw [← Q.doubleCubeLinks_image]
    exact mem_image_of_mem _ h
  · have t : FullSpace.projVertex L 1 k j b₁.initial = FullSpace.projVertex L 1 k j b₂.initial :=
      ((hb b₁).1.symm.trans (congrArg PeriodicLattice.Bond.source e)).trans (hb b₂).1
    have s : FullSpace.projVertex L 1 k j b₁.terminal =
        FullSpace.projVertex L 1 k j b₂.terminal :=
      ((hb b₁).2.1.symm.trans (congrArg PeriodicLattice.Bond.target e)).trans (hb b₂).2.1
    exact InfiniteLattice.Link.ext
      (Subtype.ext (Q.injOn_doubleCube h₁.1 h₂.1 (congrArg Subtype.val t)))
      (Subtype.ext (Q.injOn_doubleCube h₁.2 h₂.2 (congrArg Subtype.val s)))
  · have h'' : b' ∈ PeriodicLattice.bondsInDoubleBlock (projLink c) := h'
    rw [← Q.doubleCubeLinks_image] at h''
    exact h''
theorem pushField_apply
    (hB : BijOn (FullSpace.projEdge L 1 k j) (fineLinks c) (projLinks c))
    (V : FullSpace.Edge L k j → Matrices.ComplexMatrix2) {b : FullSpace.Edge L k j}
    (h : b ∈ fineLinks c) :
    pushField c V (FullSpace.projEdge L 1 k j b) = V b := by
  have hx : ∃ b' ∈ fineLinks c, FullSpace.projEdge L 1 k j b' = FullSpace.projEdge L 1 k j b :=
    ⟨b, h, rfl⟩
  have hc := hx.choose_spec
  have he : hx.choose = b := hB.injOn hc.1 h hc.2
  unfold pushField FullSpace.projField
  rw [dif_pos hx, he]
theorem pushField_of_not_mem
    (hB : BijOn (FullSpace.projEdge L 1 k j) (fineLinks c) (projLinks c))
    (V : FullSpace.Edge L k j → Matrices.ComplexMatrix2) {b' : Tower.Edge L 1 k j}
    (h : b' ∉ projLinks c) : pushField c V b' = 1 := by
  unfold pushField FullSpace.projField
  rw [dif_neg]
  rintro ⟨b, hb, rfl⟩
  exact h (hB.mapsTo hb)
theorem pushField_mem (Q : FullSpace.ProjPreservesStructures L 1 k j c)
    (hB : BijOn (FullSpace.projEdge L 1 k j) (fineLinks c) (projLinks c)) {ρ : ℝ}
    {V : FullSpace.Edge L k j → Matrices.ComplexMatrix2}
    (hV : V ∈ FullSpace.nearIdentityPolydisc L k j ρ c) :
    pushField c V ∈ Tower.nearIdentityPolydisc ρ (projLink c) := by
  refine ⟨(Q.projField_spec V hV.1).2, fun b' hb' => ?_⟩
  obtain ⟨b, hb, rfl⟩ := hB.surjOn hb'
  rw [pushField_apply hB V hb]
  exact hV.2 b hb
def pullField (c : FullSpace.Edge L k (j + 1)) (W : Tower.Edge L 1 k j → Matrices.ComplexMatrix2) :
    FullSpace.Edge L k j → Matrices.ComplexMatrix2 :=
  open Classical in fun b => if b ∈ fineLinks c then W (FullSpace.projEdge L 1 k j b) else 1
theorem pullField_apply (W : Tower.Edge L 1 k j → Matrices.ComplexMatrix2)
    {b : FullSpace.Edge L k j} (h : b ∈ fineLinks c) :
    pullField c W b = W (FullSpace.projEdge L 1 k j b) := by
  unfold pullField
  rw [if_pos h]
theorem pullField_mem (hb : ProjRespectsEdges L k j)
    (hB : BijOn (FullSpace.projEdge L 1 k j) (fineLinks c) (projLinks c)) {ρ : ℝ}
    {W : Tower.Edge L 1 k j → Matrices.ComplexMatrix2}
    (hW : W ∈ Tower.nearIdentityPolydisc ρ (projLink c)) :
    pullField c W ∈ FullSpace.nearIdentityPolydisc L k j ρ c := by
  refine ⟨⟨fun b h => ?_, fun b h => ?_⟩, fun b h => ?_⟩
  · rw [pullField_apply W h]
    exact hW.1.1 _ (hB.mapsTo h)
  · rw [pullField_apply W (fineLinks_opposite h), pullField_apply W h, ← (hb b).2.2.2]
    exact hW.1.2 _ (hB.mapsTo h)
  · rw [pullField_apply W h]
    exact hW.2 _ (hB.mapsTo h)
def positiveEdgeEquiv (hb : ProjRespectsEdges L k j)
    (hB : BijOn (FullSpace.projEdge L 1 k j) (fineLinks c) (projLinks c))
    (hone : ∀ b : Tower.Edge L 1 k j, b.IsPositivelyOriented → ¬b.opposite.IsPositivelyOriented) :
    FullSpace.PositiveEdgeOf (fineLinks c) ≃ PeriodicLattice.PositiveBondOf (projLinks c) :=
  Equiv.ofBijective
    (fun b => ⟨FullSpace.projEdge L 1 k j b.1, hB.mapsTo b.2.1, (hb b.1).2.2.1 b.2.2⟩)
    ⟨fun b₁ b₂ e => Subtype.ext (hB.injOn b₁.2.1 b₂.2.1 (congrArg Subtype.val e)),
      fun ⟨b', h', hp⟩ => by
        obtain ⟨b, hbP, rfl⟩ := hB.surjOn h'
        by_cases hpos : b.IsPositivelyOriented
        · exact ⟨⟨b, hbP, hpos⟩, rfl⟩
        · refine absurd ?_ (hone _ hp)
          rw [(hb b).2.2.2]
          exact (hb b.opposite).2.2.1 (fullSpace_opposite_isPositivelyOriented hpos)⟩
theorem fullSpace_extendFromPositive_restrictPositive
    {V : FullSpace.Edge L k j → Matrices.ComplexMatrix2}
    (hV : FullSpace.IsFieldOn PeriodicLattice.complexGaugeGroup (fineLinks c) V)
    {b : FullSpace.Edge L k j} (h : b ∈ fineLinks c) :
    FullSpace.extendFromPositive (fineLinks c)
      (FullSpace.restrictPositive (fineLinks c) V) b = V b := by
  unfold FullSpace.extendFromPositive
  by_cases hp : b.IsPositivelyOriented
  · rw [dif_pos ⟨h, hp⟩]
    rfl
  · rw [dif_neg fun x => hp x.2,
      dif_pos ⟨fineLinks_opposite h, fullSpace_opposite_isPositivelyOriented hp⟩]
    exact (hV.2 b.opposite (fineLinks_opposite h)).symm
theorem periodic_extendFromPositive_restrictToPositive
    {W : Tower.Edge L 1 k j → Matrices.ComplexMatrix2}
    (hW : PeriodicLattice.IsGaugeField PeriodicLattice.complexGaugeGroup (projLinks c) W)
    {b : Tower.Edge L 1 k j} (h : b ∈ projLinks c) :
    PeriodicLattice.extendFromPositive (projLinks c)
      (PeriodicLattice.restrictToPositive (projLinks c) W) b = W b := by
  unfold PeriodicLattice.extendFromPositive
  by_cases hp : b.IsPositivelyOriented
  · rw [dif_pos ⟨h, hp⟩]
    rfl
  · rw [dif_neg fun x => hp x.2,
      dif_pos ⟨projLinks_opposite h, periodic_opposite_isPositivelyOriented hp⟩]
    exact (hW.2 b.opposite (projLinks_opposite h)).symm
theorem periodic_extendFromPositive_of_not_mem
    {v : PeriodicLattice.PositiveBondOf (projLinks c) → Matrices.ComplexMatrix2}
    {b : Tower.Edge L 1 k j} (h : b ∉ projLinks c) :
    PeriodicLattice.extendFromPositive (projLinks c) v b = 1 := by
  unfold PeriodicLattice.extendFromPositive
  have h' : ¬(b.opposite ∈ projLinks c ∧ b.opposite.IsPositivelyOriented) :=
    fun x => h ⟨x.1.2, x.1.1⟩
  rw [dif_neg fun x => h x.1, dif_neg h']
theorem isHolomorphicOnFields_of_proj (Q : FullSpace.ProjPreservesStructures L 1 k j c)
    (hb : ProjRespectsEdges L k j)
    (hone : ∀ b : Tower.Edge L 1 k j, b.IsPositivelyOriented → ¬b.opposite.IsPositivelyOriented)
    {ρ : ℝ}
    {Φ : (FullSpace.Edge L k j → Matrices.ComplexMatrix2) → Matrices.ComplexMatrix2}
    {Ψ : (Tower.Edge L 1 k j → Matrices.ComplexMatrix2) → Matrices.ComplexMatrix2}
    (hΦ : ∀ V ∈ FullSpace.nearIdentityPolydisc L k j ρ c, Φ V = Ψ (pushField c V))
    (h : PeriodicLattice.IsHolomorphicOnFields (projLinks c)
      (Tower.nearIdentityPolydisc ρ (projLink c)) Ψ) :
    FullSpace.IsHolomorphicOnFields (fineLinks c)
      (FullSpace.nearIdentityPolydisc L k j ρ c) Φ := by
  have hB := projEdge_bijOn Q hb
  set e := positiveEdgeEquiv hb hB hone with he
  have hrestr : ∀ V : FullSpace.Edge L k j → Matrices.ComplexMatrix2,
      FullSpace.restrictPositive (fineLinks c) V ∘ e.symm =
        PeriodicLattice.restrictToPositive (projLinks c) (pushField c V) := fun V => by
    funext b'
    have h₁ := pushField_apply hB V (e.symm b').2.1
    have h₂ : FullSpace.projEdge L 1 k j (e.symm b').1 = b'.1 :=
      congrArg Subtype.val (e.apply_symm_apply b')
    rw [h₂] at h₁
    exact h₁.symm
  have hR : ∀ v, v ∈ FullSpace.restrictPositive (fineLinks c) ''
        FullSpace.nearIdentityPolydisc L k j ρ c ↔
      v ∘ e.symm ∈ PeriodicLattice.restrictToPositive (projLinks c) ''
        Tower.nearIdentityPolydisc ρ (projLink c) := fun v => by
    constructor
    · rintro ⟨V, hV, rfl⟩
      exact ⟨pushField c V, pushField_mem Q hB hV, (hrestr V).symm⟩
    · rintro ⟨W, hW, hv⟩
      refine ⟨pullField c W, pullField_mem hb hB hW, ?_⟩
      funext b
      have h₁ := congrFun hv (e b)
      have h₂ : pullField c W b.1 = W (e b).1 := pullField_apply W b.2.1
      rw [FullSpace.restrictPositive, h₂]
      simpa [PeriodicLattice.restrictToPositive] using h₁
  have hval : ∀ v ∈ FullSpace.restrictPositive (fineLinks c) ''
        FullSpace.nearIdentityPolydisc L k j ρ c,
      Φ (FullSpace.extendFromPositive (fineLinks c) v) =
        Ψ (PeriodicLattice.extendFromPositive (projLinks c) (v ∘ e.symm)) := by
    rintro v ⟨V, hV, rfl⟩
    have hr := fun b (hbP : b ∈ fineLinks c) =>
      fullSpace_extendFromPositive_restrictPositive hV.1 hbP
    have hV₁ : FullSpace.extendFromPositive (fineLinks c)
        (FullSpace.restrictPositive (fineLinks c) V) ∈
          FullSpace.nearIdentityPolydisc L k j ρ c := by
      refine ⟨⟨fun b h => ?_, fun b h => ?_⟩, fun b h => ?_⟩
      · rw [hr b h]
        exact hV.1.1 b h
      · rw [hr _ (fineLinks_opposite h), hr b h]
        exact hV.1.2 b h
      · rw [hr b h]
        exact hV.2 b h
    rw [hΦ _ hV₁, hrestr V]
    congr 1
    funext b'
    by_cases hb' : b' ∈ projLinks c
    · obtain ⟨b, hbP, rfl⟩ := hB.surjOn hb'
      rw [pushField_apply hB _ hbP, hr b hbP,
        periodic_extendFromPositive_restrictToPositive (pushField_mem Q hB hV).1 hb',
        pushField_apply hB _ hbP]
    · rw [pushField_of_not_mem hB _ hb', periodic_extendFromPositive_of_not_mem hb']
  obtain ⟨⟨inst, hh⟩, h₂⟩ := h
  let i₁ : Fintype (FullSpace.PositiveEdgeOf (fineLinks c)) := Fintype.ofEquiv _ e.symm
  refine ⟨⟨i₁, ?_⟩, fun N ν β => ?_⟩
  · exact isHolomorphicBetween_reindex e hR (fun v hv => by simp only [hval v hv]) hh
  · have h₃ := h₂ N (e.symm.trans ν) β
    have hset : (fun v => v ∘ (e.symm.trans ν).symm) '' (PeriodicLattice.restrictToPositive
          (projLinks c) '' Tower.nearIdentityPolydisc ρ (projLink c)) =
        (fun v => v ∘ ν.symm) '' (FullSpace.restrictPositive (fineLinks c) ''
          FullSpace.nearIdentityPolydisc L k j ρ c) := by
      ext X
      constructor
      · rintro ⟨v', hv', rfl⟩
        refine ⟨v' ∘ e, (hR _).2 ?_, ?_⟩
        · have : (v' ∘ e) ∘ e.symm = v' := by
            funext i
            simp
          rwa [this]
        · funext i
          simp
      · rintro ⟨v, hv, rfl⟩
        refine ⟨v ∘ e.symm, (hR v).1 hv, ?_⟩
        funext i
        simp
    rw [hset] at h₃
    refine isHolomorphicOnSL2Power_congr h₃ ?_
    rintro X ⟨v, hv, rfl⟩
    have e₁ : (v ∘ ν.symm) ∘ (e.symm.trans ν) = v ∘ e.symm := by
      funext i
      simp
    have e₂ : (v ∘ ν.symm) ∘ ν = v := by
      funext i
      simp
    show Ψ (PeriodicLattice.extendFromPositive (projLinks c)
        ((v ∘ ν.symm) ∘ (e.symm.trans ν))) =
      Φ (FullSpace.extendFromPositive (fineLinks c) ((v ∘ ν.symm) ∘ ν))
    rw [e₁, e₂, hval v hv]
def gaugeOnQuotient (c : FullSpace.Edge L k (j + 1))
    (u : FullSpace.Vertex L k j → Matrices.ComplexMatrix2) :
    Tower.Vertex L 1 k j → Matrices.ComplexMatrix2 :=
  open Classical in
  fun s => if h : ∃ x : FullSpace.Vertex L k j,
      (x : InfiniteLattice.AmbientSpace) ∈ FullSpace.doubleCube L (Tower.meshAt L k j) c ∧
        FullSpace.projVertex L 1 k j x = s then u h.choose else 1
theorem gaugeOnQuotient_apply (Q : FullSpace.ProjPreservesStructures L 1 k j c)
    (u : FullSpace.Vertex L k j → Matrices.ComplexMatrix2) {x : FullSpace.Vertex L k j}
    (hx : (x : InfiniteLattice.AmbientSpace) ∈ FullSpace.doubleCube L (Tower.meshAt L k j) c) :
    gaugeOnQuotient c u (FullSpace.projVertex L 1 k j x) = u x := by
  have h : ∃ x' : FullSpace.Vertex L k j,
      (x' : InfiniteLattice.AmbientSpace) ∈ FullSpace.doubleCube L (Tower.meshAt L k j) c ∧
        FullSpace.projVertex L 1 k j x' = FullSpace.projVertex L 1 k j x := ⟨x, hx, rfl⟩
  have hs := h.choose_spec
  have he : h.choose = x := Subtype.ext (Q.injOn_doubleCube hs.1 hx (congrArg Subtype.val hs.2))
  unfold gaugeOnQuotient
  rw [dif_pos h, he]
theorem gaugeOnQuotient_mem {u : FullSpace.Vertex L k j → Matrices.ComplexMatrix2}
    (hu : u ∈ FullSpace.gaugeGroupAt L k j) :
    gaugeOnQuotient c u ∈ Tower.gaugeGroupAt L 1 k j := by
  intro s
  unfold gaugeOnQuotient
  split_ifs
  · exact hu _
  · exact one_mem Matrices.ComplexMatrix2.specialUnitary
theorem isFieldOn_gaugeAct {V : FullSpace.Edge L k j → Matrices.ComplexMatrix2}
    (hV : FullSpace.IsFieldOn PeriodicLattice.complexGaugeGroup (fineLinks c) V)
    {u : FullSpace.Vertex L k j → Matrices.ComplexMatrix2}
    (hu : u ∈ FullSpace.gaugeGroupAt L k j) :
    FullSpace.IsFieldOn PeriodicLattice.complexGaugeGroup (fineLinks c)
      (FullSpace.gaugeAct u V) := by
  have hdet : ∀ x, (u x).det = 1 := fun x => (Matrix.mem_specialUnitaryGroup_iff.mp (hu x)).2
  have hinv : ∀ x, ((u x)⁻¹).det = 1 := fun x => by
    rw [Matrix.det_nonsing_inv, hdet]
    simp
  refine ⟨fun b h => ?_, fun b h => ?_⟩
  · have hb : (V b).det = 1 := hV.1 b h
    show (u b.initial * V b * (u b.terminal)⁻¹).det = 1
    rw [Matrix.det_mul, Matrix.det_mul, hdet, hb, hinv]
    simp
  · show u b.terminal * V b.opposite * (u b.initial)⁻¹ =
      (u b.initial * V b * (u b.terminal)⁻¹)⁻¹
    have hunit : IsUnit (u b.terminal).det := by
      rw [hdet]
      exact isUnit_one
    rw [hV.2 b h, Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ hunit,
      mul_assoc]
theorem gaugeTransform_pushField (Q : FullSpace.ProjPreservesStructures L 1 k j c)
    (hb : ProjRespectsEdges L k j)
    (hB : BijOn (FullSpace.projEdge L 1 k j) (fineLinks c) (projLinks c))
    (V : FullSpace.Edge L k j → Matrices.ComplexMatrix2)
    (u : FullSpace.Vertex L k j → Matrices.ComplexMatrix2) :
    ∀ b' ∈ projLinks c, PeriodicLattice.gaugeTransform (gaugeOnQuotient c u) (pushField c V) b' =
      pushField c (FullSpace.gaugeAct u V) b' := by
  intro b' hb'
  obtain ⟨b, hbP, rfl⟩ := hB.surjOn hb'
  rw [pushField_apply hB _ hbP]
  show gaugeOnQuotient c u (FullSpace.projEdge L 1 k j b).source *
      pushField c V (FullSpace.projEdge L 1 k j b) *
      (gaugeOnQuotient c u (FullSpace.projEdge L 1 k j b).target)⁻¹ =
    u b.initial * V b * (u b.terminal)⁻¹
  rw [pushField_apply hB _ hbP, (hb b).1, (hb b).2.1, gaugeOnQuotient_apply Q u hbP.1,
    gaugeOnQuotient_apply Q u hbP.2]
theorem complexMeanContourHolonomy_congr (hC : PeriodicLattice.ContourBondsInDoubleBlock)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hj : j < k)
    {W W' : Tower.Edge L 1 k j → Matrices.ComplexMatrix2}
    (ha : ∀ b ∈ projLinks c, W b = W' b) {y : Tower.Vertex L 1 k (j + 1)}
    (hy : y = (projLink c).source ∨ y = (projLink c).target) {x : Tower.Vertex L 1 k j}
    (hx : x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y) :
    PeriodicLattice.complexMeanContourHolonomy W y x =
      PeriodicLattice.complexMeanContourHolonomy W' y x := by
  unfold PeriodicLattice.complexMeanContourHolonomy
  congr 1
  funext σ
  unfold PeriodicLattice.contourHolonomies PeriodicLattice.pathHolonomy
  congr 1
  exact List.map_congr_left fun b hb =>
    ha b (hC L 1 k j hL one_pos hj (projLink c) y hy x hx _ ⟨σ, rfl⟩ b hb)
theorem self_mem_cube (hL : 0 < L) (y : FullSpace.Vertex L k (j + 1)) :
    (y : InfiniteLattice.AmbientSpace) ∈ FullSpace.cube L (Tower.meshAt L k j) y := by
  refine ⟨0, fun μ => ?_, by simp⟩
  simp
  omega
theorem projVertex_toFiner {y : FullSpace.Vertex L k (j + 1)}
    (hz : ((FullSpace.toFiner (Tower.meshAt L k j) y : FullSpace.Vertex L k j) :
      InfiniteLattice.AmbientSpace) = y) :
    (FullSpace.projVertex L 1 k (j + 1) y).toSublattice (PeriodicLattice.levelDepth k j) =
      FullSpace.projVertex L 1 k j (FullSpace.toFiner (Tower.meshAt L k j) y) := by
  have p : ((FullSpace.projVertex L 1 k j (FullSpace.toFiner (Tower.meshAt L k j) y) :
      Tower.Vertex L 1 k j) : PeriodicLattice.FourTorus L 1) =
        FullSpace.projVertex L 1 k (j + 1) y := by
    show TorusMetric.torusProj _ _ = TorusMetric.torusProj _ _
    rw [hz]
  have h := Classical.epsilon_spec
    (p := fun x : PeriodicLattice.Site L 1 (PeriodicLattice.levelDepth k j) =>
      (x : PeriodicLattice.FourTorus L 1) = FullSpace.projVertex L 1 k (j + 1) y) ⟨_, p⟩
  exact Subtype.ext (h.trans p.symm)
end AtAnEdge
theorem admissible_of_quotient (hF : Tower.SublatticesSymmetriesScalingsAndProjections.Statement)
    (hQ : Tower.EdgeProjectionProperties)
    (hR : PeriodicLattice.ComplexAverageIsLocal)
    (hC : PeriodicLattice.ContourBondsInDoubleBlock)
    {L : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L) {ρ : ℝ}
    (H : ∀ k j : ℕ, j < k → ∀ c : Tower.Edge L 1 k (j + 1), c.IsPositivelyOriented →
      Tower.PolydiscIsAdmissible ρ c)
    {k j : ℕ} (hj : j < k) (c : FullSpace.Edge L k (j + 1)) (hc : c.IsPositivelyOriented) :
    FullSpace.PolydiscIsAdmissible L k j ρ c := by
  have hL0 : 0 < L := by have := hL.2; omega
  have hk : 1 ≤ k := by omega
  have Q : FullSpace.ProjPreservesStructures L 1 k j c :=
    ((hF L hL0 hL k).2.2.2.2.2.2 hk 1 one_pos).2 j hj c hc
  have hb : ProjRespectsEdges L k j := (hQ L 1 k j hL one_pos hj.le).1
  obtain ⟨hdt, hdh, hdp, -⟩ := (hQ L 1 k (j + 1) hL one_pos hj).1 c
  have hB := projEdge_bijOn Q hb
  have hone : ∀ b : Tower.Edge L 1 k j, b.IsPositivelyOriented →
      ¬b.opposite.IsPositivelyOriented := fun b h =>
    PeriodicLattice.Bond.opposite_not_isPositivelyOriented (by have := hL.2; omega)
      (by simp only [PeriodicLattice.levelDepth]; push_cast; omega) h
  have S : Tower.PolydiscIsAdmissible ρ (projLink c) := H k j hj _ (hdp hc)
  have R := hR L 1 k j hL.1 hL.2 one_pos hj (projLink c) (hdp hc)
  have hnest := (hF L hL0 hL k).2.1 j (j + 1) (by omega) hj
  have hz : ∀ y : FullSpace.Vertex L k (j + 1),
      ((FullSpace.toFiner (Tower.meshAt L k j) y : FullSpace.Vertex L k j) :
        InfiniteLattice.AmbientSpace) = y := fun y =>
    Classical.epsilon_spec (p := fun x : FullSpace.Vertex L k j =>
      (x : InfiniteLattice.AmbientSpace) = y) ⟨⟨y, hnest y.2⟩, rfl⟩
  have hdom : ∀ V ∈ FullSpace.nearIdentityPolydisc L k j ρ c,
      V ∈ FullSpace.complexDomainNearOne L c :=
    fun V hV => (Q.mem_complexDomain_iff V hV.1).2
      (S.subset_complexDomain (pushField_mem Q hB hV))
  have hend : ∀ y : FullSpace.Vertex L k (j + 1), y = c.initial ∨ y = c.terminal →
      (y : InfiniteLattice.AmbientSpace) ∈ FullSpace.doubleCube L (Tower.meshAt L k j) c := by
    rintro y (rfl | rfl)
    · exact Or.inl (self_mem_cube hL0 _)
    · exact Or.inr (self_mem_cube hL0 _)
  have hgauge : ∀ (u : FullSpace.Vertex L k j → Matrices.ComplexMatrix2)
      (y : FullSpace.Vertex L k (j + 1)), y = c.initial ∨ y = c.terminal →
      gaugeOnQuotient c u ((FullSpace.projVertex L 1 k (j + 1) y).toSublattice
          (PeriodicLattice.levelDepth k j)) =
        u (FullSpace.toFiner (Tower.meshAt L k j) y) := fun u y hy => by
    rw [projVertex_toFiner (hz y)]
    exact gaugeOnQuotient_apply Q u (by rw [hz y]; exact hend y hy)
  have hsite : ∀ y : FullSpace.Vertex L k (j + 1), y = c.initial ∨ y = c.terminal →
      ∀ x ∈ FullSpace.cubeVertices L (Tower.meshAt L k j) y,
        FullSpace.projVertex L 1 k (j + 1) y ∈
            ({(projLink c).source, (projLink c).target} : Set (Tower.Vertex L 1 k (j + 1))) ∧
          FullSpace.projVertex L 1 k j x ∈
            PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j)
              (FullSpace.projVertex L 1 k (j + 1) y) ∧
          (x : InfiniteLattice.AmbientSpace) ∈ FullSpace.doubleCube L (Tower.meshAt L k j) c := by
    rintro y (rfl | rfl) x hx
    · refine ⟨Or.inl hdt.symm, ?_, Or.inl hx⟩
      have := Q.cube_initial
      rw [← hdt]
      show ((FullSpace.projVertex L 1 k j x : Tower.Vertex L 1 k j) :
          PeriodicLattice.FourTorus L 1) ∈ PeriodicLattice.unitBlock (projLink c).source
      rw [← this]
      exact ⟨_, hx, rfl⟩
    · refine ⟨Or.inr hdh.symm, ?_, Or.inr hx⟩
      have := Q.cube_terminal
      rw [← hdh]
      show ((FullSpace.projVertex L 1 k j x : Tower.Vertex L 1 k j) :
          PeriodicLattice.FourTorus L 1) ∈ PeriodicLattice.unitBlock (projLink c).target
      rw [← this]
      exact ⟨_, hx, rfl⟩
  refine ⟨hdom, ?_, ?_, ?_, ?_, ?_⟩
  · exact isHolomorphicOnFields_of_proj Q hb hone
      (fun V hV => Q.complexSmoothing_eq V (hdom V hV)) S.holomorphic_smoothing
  · intro y hy x hx
    obtain ⟨hyd, hxd, -⟩ := hsite y hy x hx
    exact isHolomorphicOnFields_of_proj Q hb hone
      (fun V hV => Q.complexContourMean_eq V (hdom V hV) y hy x hx)
      (S.holomorphic_contourMean _ hyd _ hxd)
  · intro V hV
    rw [Q.complexSmoothing_eq V (hdom V hV)]
    exact S.smoothing_near_one _ (pushField_mem Q hB hV)
  · intro V hV y hy x hx
    obtain ⟨hyd, hxd, -⟩ := hsite y hy x hx
    rw [Q.complexContourMean_eq V (hdom V hV) y hy x hx]
    exact S.contourMean_near_one _ (pushField_mem Q hB hV) _ hyd _ hxd
  · intro V hV u hu
    have hconf := isFieldOn_gaugeAct hV.1 hu
    have hagree := _root_.YangMills.Construction.Tower.InfiniteSideAdmissibility.gaugeTransform_pushField Q hb hB V u
    obtain ⟨hd, havg, hcont⟩ :=
      S.gauge_covariant _ (pushField_mem Q hB hV) _ (gaugeOnQuotient_mem (c := c) hu)
    have hVu : FullSpace.gaugeAct u V ∈ FullSpace.complexDomainNearOne L c :=
      (Q.mem_complexDomain_iff _ hconf).2 ((R.mem_domain_iff _ _ hagree).1 hd)
    refine ⟨hVu, ?_, fun y hy x hx => ?_⟩
    · have e₁ : PeriodicLattice.complexBlockAverage (pushField c (FullSpace.gaugeAct u V))
            (projLink c) =
          PeriodicLattice.complexBlockAverage
            (PeriodicLattice.gaugeTransform (gaugeOnQuotient c u) (pushField c V))
            (projLink c) := by
        simp only [PeriodicLattice.complexBlockAverage, if_pos (hdp hc)]
        exact (R.average_eq _ _ hagree).symm
      rw [Q.complexSmoothing_eq _ hVu, e₁, havg]
      show gaugeOnQuotient c u ((projLink c).source.toSublattice (PeriodicLattice.levelDepth k j)) *
          PeriodicLattice.complexBlockAverage (pushField c V) (projLink c) *
          (gaugeOnQuotient c u
            ((projLink c).target.toSublattice (PeriodicLattice.levelDepth k j)))⁻¹ =
        u (FullSpace.toFiner (Tower.meshAt L k j) c.initial) * FullSpace.complexSmoothing L V c *
          (u (FullSpace.toFiner (Tower.meshAt L k j) c.terminal))⁻¹
      rw [hdt, hdh, hgauge u _ (Or.inl rfl), hgauge u _ (Or.inr rfl),
        Q.complexSmoothing_eq V (hdom V hV)]
    · obtain ⟨hyd, hxd, hxD⟩ := hsite y hy x hx
      rw [Q.complexContourMean_eq _ hVu y hy x hx,
        Q.complexContourMean_eq V (hdom V hV) y hy x hx,
        ← complexMeanContourHolonomy_congr hC hL hj hagree hyd hxd, hcont _ hyd _ hxd,
        gaugeOnQuotient_apply Q u hxD, hgauge u y hy]
theorem polydiscIsAdmissibleAtInfiniteSide_holds
    (hF : Tower.SublatticesSymmetriesScalingsAndProjections.Statement)
    (hQ : Tower.EdgeProjectionProperties)
    (hR : PeriodicLattice.ComplexAverageIsLocal)
    (hC : PeriodicLattice.ContourBondsInDoubleBlock) :
    Tower.PolydiscIsAdmissibleAtInfiniteSide :=
  fun _ hL _ _ H _ _ hj c hc => admissible_of_quotient hF hQ hR hC hL H hj c hc
end YangMills.Construction.Tower.InfiniteSideAdmissibility
end
