import YangMills.Construction.Lattice.BondsPathsAndAveragesOfADoubleBlock
import YangMills.Construction.Matrices.ExpChartHolomorphy
import YangMills.Construction.Towers.BondsOfADoubleBlockAndTheirImageInATorus
import YangMills.Construction.Towers.PolydiscsOfDoubleBlocks
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Tower.DoubleBlockPolydisc
open Tower.BondSetFields Matrices.GroupLieProduct
theorem finiteOpenPolydisc_of_productStructure {β : Type} {rev : β → β} {pos : β → Prop}
    {IsConf : Set Matrices.ComplexMatrix2 → Set β → (β → Matrices.ComplexMatrix2) → Prop}
    {P : Set β} {ρ : ℝ} (hρ : 0 < ρ)
    (hfin : P.Finite) (hrev : ∀ b ∈ P, rev b ∈ P)
    (hP : Tower.BondSetFields.ProductStructureAt rev pos IsConf P)
    (hmono : ∀ U, IsConf PeriodicLattice.compactGaugeGroup P U →
      IsConf PeriodicLattice.complexGaugeGroup P U) :
    FiniteOpenPolydisc rev pos IsConf P
      {V | IsConf PeriodicLattice.complexGaugeGroup P V ∧
        ∀ b ∈ P, Matrices.ComplexMatrix2.operatorNorm (V b - 1) < ρ} := by
  have hC : restrictTo P ''
      {V | IsConf PeriodicLattice.complexGaugeGroup P V ∧
        ∀ b ∈ P, Matrices.ComplexMatrix2.operatorNorm (V b - 1) < ρ} =
      nearIdentity (fieldsOn (IsConf PeriodicLattice.complexGaugeGroup) P) ρ := by
    ext w
    constructor
    · rintro ⟨V, ⟨hV, hn⟩, rfl⟩
      exact ⟨⟨V, hV, rfl⟩, fun b => hn b.1 b.2⟩
    · rintro ⟨⟨U, hU, rfl⟩, hn⟩
      exact ⟨U, ⟨hU, fun b hb => hn ⟨b, hb⟩⟩, rfl⟩
  have hR : restrictTo P ''
      {V | V ∈ {V | IsConf PeriodicLattice.complexGaugeGroup P V ∧
          ∀ b ∈ P, Matrices.ComplexMatrix2.operatorNorm (V b - 1) < ρ} ∧
        IsConf PeriodicLattice.compactGaugeGroup P V} =
      nearIdentity (fieldsOn (IsConf PeriodicLattice.compactGaugeGroup) P) ρ := by
    ext w
    constructor
    · rintro ⟨V, ⟨⟨_, hn⟩, hr⟩, rfl⟩
      exact ⟨⟨V, hr, rfl⟩, fun b => hn b.1 b.2⟩
    · rintro ⟨⟨U, hU, rfl⟩, hn⟩
      exact ⟨U, ⟨⟨hmono U hU, fun b hb => hn ⟨b, hb⟩⟩, hU⟩, rfl⟩
  refine ⟨hfin, hrev, hP.1.1, hP.1.2.1, hP.2.1.1, ?_, ?_⟩
  · show Matrices.ComplexMatrix2.IsRelativelyOpen _ (readPositive pos P '' (restrictTo P '' _))
    rw [hC]
    exact (hP.2.1.2.2.2.2 ρ hρ).2
  · show Matrices.ComplexMatrix2.IsRelativelyOpen _ (readPositive pos P '' (restrictTo P '' _))
    rw [hR]
    exact (hP.2.2.2.2.2.2 ρ hρ).2
section Reindexing
variable {σ τ : Type}
private def transport (E : σ ≃ τ) (A : σ → Matrices.ComplexMatrix2) :
    τ → Matrices.ComplexMatrix2 := fun i => A (E.symm i)
private theorem continuous_transport (E : σ ≃ τ) : Continuous (transport E) :=
  continuous_pi fun _ => continuous_apply _
private theorem transport_mem_tracelessPi (E : σ ≃ τ) {A : σ → Matrices.ComplexMatrix2} :
    transport E A ∈ tracelessPi τ ↔ A ∈ tracelessPi σ := by
  constructor
  · intro h i
    have := h (E i)
    simpa [transport] using this
  · intro h i
    exact h (E.symm i)
private theorem supNorm_transport (E : σ ≃ τ) (A : σ → Matrices.ComplexMatrix2) :
    supNorm (transport E A) = supNorm A :=
  E.symm.iSup_comp (g := fun i => Matrices.ComplexMatrix2.operatorNorm (A i))
private theorem holomorphicIn_of_enumeration [Fintype τ] {E' : Type} {l : ℕ}
    {b : Module.Basis (Fin 3) ℂ Matrices.ComplexMatrix2.traceless}
    {e : E' ≃ Coordinates.ComplexCoordinates l} {O : Set (τ → Matrices.ComplexMatrix2)}
    {f : (τ → Matrices.ComplexMatrix2) → E'} (h : IsHolomorphicOnTraceless b e O f) {N : ℕ}
    (ν : τ ≃ Fin N) :
    Coordinates.ComplexCoordinates.IsHolomorphicIn
      ((fun w i => Coordinates.ComplexCoordinates.tracelessTuple b w (ν i)) ⁻¹' O)
      (e ∘ f ∘ fun w i => Coordinates.ComplexCoordinates.tracelessTuple b w (ν i)) := by
  have hN : N = Fintype.card τ := by simpa using (Fintype.card_congr ν).symm
  subst hN
  exact h.2 ν
private theorem isHolomorphicOnTraceless_transport [Fintype σ] [Fintype τ] {E' : Type} {l : ℕ}
    {b : Module.Basis (Fin 3) ℂ Matrices.ComplexMatrix2.traceless}
    {e : E' ≃ Coordinates.ComplexCoordinates l} {O : Set (τ → Matrices.ComplexMatrix2)}
    {f : (τ → Matrices.ComplexMatrix2) → E'} (E : σ ≃ τ) (h : IsHolomorphicOnTraceless b e O f) :
    IsHolomorphicOnTraceless b e (transport E ⁻¹' O) (f ∘ transport E) := by
  refine ⟨⟨fun A hA => (transport_mem_tracelessPi E).1 (h.1.1 hA), fun A hA => ?_⟩, fun ν => ?_⟩
  · obtain ⟨s, hs, hB⟩ := h.1.2 _ hA
    refine ⟨s, hs, fun B hB' hn => hB _ ((transport_mem_tracelessPi E).2 hB') ?_⟩
    have : transport E B - transport E A = transport E (B - A) := rfl
    rw [this, supNorm_transport]
    exact hn
  · exact holomorphicIn_of_enumeration h (E.symm.trans ν)
end Reindexing
section Products
variable {A B κ : Type}
private def leftCongr (E : A ≃ B) : A ⊕ κ ≃ B ⊕ κ := Equiv.sumCongr E (Equiv.refl κ)
private theorem transport_mem_groupLieProduct (E : A ≃ B) {p : A ⊕ κ → Matrices.ComplexMatrix2} :
    transport (leftCongr E) p ∈ Matrices.GroupLieProduct B κ ↔
      p ∈ Matrices.GroupLieProduct A κ := by
  constructor
  · intro h i
    rcases i with i | i
    · simpa [transport, leftCongr] using h (.inl (E i))
    · simpa [transport, leftCongr] using h (.inr i)
  · intro h i
    rcases i with i | i
    · exact h (.inl (E.symm i))
    · exact h (.inr i)
private theorem isRelativelyOpen_transport (E : A ≃ B) {W : Set (B ⊕ κ → Matrices.ComplexMatrix2)}
    (h : Matrices.ComplexMatrix2.IsRelativelyOpen (Matrices.GroupLieProduct B κ) W) :
    Matrices.ComplexMatrix2.IsRelativelyOpen (Matrices.GroupLieProduct A κ)
      (transport (leftCongr E) ⁻¹' W) := by
  obtain ⟨O, hO, rfl⟩ := h
  refine ⟨transport (leftCongr E) ⁻¹' O, hO.preimage (continuous_transport _), ?_⟩
  ext p
  exact and_congr_right fun _ => transport_mem_groupLieProduct E
private theorem expChartAt_transport (E : A ≃ B) (p C : A ⊕ κ → Matrices.ComplexMatrix2) :
    expChartAt (transport (leftCongr E) p) (transport (leftCongr E) C) =
      transport (leftCongr E) (expChartAt p C) := by
  funext i
  rcases i with i | i <;> rfl
private theorem isHolomorphicToUnimodular_transport [Fintype A] [Fintype B] [Fintype κ]
    {b : Module.Basis (Fin 3) ℂ Matrices.ComplexMatrix2.traceless} (E : A ≃ B)
    {W : Set (B ⊕ κ → Matrices.ComplexMatrix2)}
    {Φ : (B ⊕ κ → Matrices.ComplexMatrix2) → Matrices.ComplexMatrix2}
    (h : IsHolomorphicToUnimodular b W Φ) :
    IsHolomorphicToUnimodular b (transport (leftCongr E) ⁻¹' W) (Φ ∘ transport (leftCongr E)) := by
  refine ⟨isRelativelyOpen_transport E h.1, fun p hp => h.2.1 hp,
    h.2.2.1.comp (continuous_transport _).continuousOn fun p hp => hp, fun p hp => ?_⟩
  obtain ⟨O, h0, hO, hhol⟩ := h.2.2.2 _ hp
  refine ⟨transport (leftCongr E) ⁻¹' O, h0, fun C hC => ?_, ?_⟩
  · have := hO _ hC
    rw [expChartAt_transport] at this
    exact this
  · have := isHolomorphicOnTraceless_transport (leftCongr E) hhol
    have heq : ((fun C => Matrices.ComplexMatrix2.logSeries
        (Φ (expChartAt (transport (leftCongr E) p) C) *
        (Φ (transport (leftCongr E) p))⁻¹)) ∘ transport (leftCongr E)) =
        fun C => Matrices.ComplexMatrix2.logSeries
          ((Φ ∘ transport (leftCongr E)) (expChartAt p C) *
          ((Φ ∘ transport (leftCongr E)) p)⁻¹) := by
      funext C
      simp only [Function.comp, expChartAt_transport]
    rwa [heq] at this
end Products
private theorem isHolomorphicIn_component {N N' : ℕ} {O : Set (Coordinates.ComplexCoordinates N)}
    {g : Coordinates.ComplexCoordinates N → Coordinates.ComplexCoordinates N'}
    (h : Coordinates.ComplexCoordinates.IsHolomorphicIn O g) (k : Fin N') :
    Coordinates.ComplexCoordinates.IsHolomorphicIn O fun z (_ : Fin 1) => g z k := by
  refine ⟨h.1, continuousOn_pi.2 fun _ => (continuous_apply k).comp_continuousOn h.2.1,
    fun a ha j => ?_⟩
  filter_upwards [h.2.2 a ha j] with ζ hζ
  exact differentiableAt_pi.2 fun _ => differentiableAt_pi.1 hζ k
private theorem entry_isHolomorphicToCoords {ι κ : Type} [Fintype ι] [Fintype κ]
    {b : Module.Basis (Fin 3) ℂ Matrices.ComplexMatrix2.traceless}
    {W : Set (ι ⊕ κ → Matrices.ComplexMatrix2)}
    {Φ : (ι ⊕ κ → Matrices.ComplexMatrix2) → Matrices.ComplexMatrix2}
    (h : IsHolomorphicToCoords b Coordinates.ComplexCoordinates.matrixEquiv W Φ) (r s : Fin 2) :
    IsHolomorphicToCoords b (Equiv.funUnique (Fin 1) ℂ).symm W fun p => Φ p r s := by
  have hk : ∀ X : Matrices.ComplexMatrix2, Coordinates.ComplexCoordinates.matrixEquiv X
      (Coordinates.ComplexCoordinates.entryIndex (r, s)) = X r s := fun X => by
    simp [Coordinates.ComplexCoordinates.matrixEquiv]
  refine ⟨h.1, ?_, fun p hp => ?_⟩
  · refine continuousOn_pi.2 fun _ => ?_
    have := (continuous_apply (Coordinates.ComplexCoordinates.entryIndex (r, s))).comp_continuousOn
      h.2.1
    refine this.congr fun p _ => ?_
    exact (hk (Φ p)).symm
  · obtain ⟨O, h0, hO, hhol⟩ := h.2.2 p hp
    refine ⟨O, h0, hO, hhol.1, fun ν => ?_⟩
    have := isHolomorphicIn_component (hhol.2 ν) (Coordinates.ComplexCoordinates.entryIndex (r, s))
    refine (congrArg _ ?_).mp this
    funext z i
    exact hk _
abbrev _root_.YangMills.DeltaSharedProofs.p501989 := @entry_isHolomorphicToCoords
private theorem isHolomorphicWithEntries_of_powerCharts
    (hH2 : Matrices.GroupLieProduct.ExpChartHolomorphy.ExpChartTheory) {σ : Type} [Fintype σ]
    {n : ℕ} (ν : σ ≃ Fin n) {W : Set (σ → Matrices.ComplexMatrix2)}
    {Φ : (σ → Matrices.ComplexMatrix2) → Matrices.ComplexMatrix2}
    (h : ∀ β : Module.Basis (Fin 3) ℂ Matrices.ComplexMatrix2.traceless,
      Coordinates.ComplexCoordinates.IsHolomorphicOnSL2Power β
      ((fun v => v ∘ ν.symm) '' W) fun X => Φ (X ∘ ν)) :
    IsHolomorphicWithEntries W Φ := by
  have hgroup : ∀ b : Module.Basis (Fin 3) ℂ Matrices.ComplexMatrix2.traceless,
      IsHolomorphicToUnimodular b (leftComponents ⁻¹' W) (Φ ∘ leftComponents) := by
    intro b
    obtain ⟨hn, hopen, hmaps, -, -⟩ := h b
    let r : (Fin n ⊕ Empty → Matrices.ComplexMatrix2) → Fin n → Matrices.ComplexMatrix2 :=
      fun q i => q (.inl i)
    have hr : Continuous r := continuous_pi fun _ => continuous_apply _
    have hW' : Matrices.ComplexMatrix2.IsRelativelyOpen (Matrices.GroupLieProduct (Fin n) Empty)
        (r ⁻¹' ((fun v => v ∘ ν.symm) '' W)) := by
      obtain ⟨O, hO, hOe⟩ := hopen
      refine ⟨r ⁻¹' O, hO.preimage hr, ?_⟩
      rw [hOe]
      ext q
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨h1, fun i => by
          rcases i with i | i
          · exact h2 i
          · exact i.elim⟩
      · rintro ⟨h1, h2⟩
        exact ⟨h1, fun i => h2 (.inl i)⟩
    have key := (hH2.2.2.2.2.2.1 Empty n hn b b (r ⁻¹' ((fun v => v ∘ ν.symm) '' W))
      (fun q => Φ (r q ∘ ν)) hW' fun q hq => hmaps hq).2 (h b)
    have htr := isHolomorphicToUnimodular_transport (κ := Empty) ν key
    have hset : transport (leftCongr (κ := Empty) ν) ⁻¹' (r ⁻¹' ((fun v => v ∘ ν.symm) '' W)) =
        leftComponents ⁻¹' W := by
      ext p
      constructor
      · rintro ⟨v, hv, hvp⟩
        have : v = leftComponents p := by
          funext s
          have := congrFun hvp (ν s)
          simpa [r, transport, leftCongr, leftComponents] using this
        show leftComponents p ∈ W
        rw [← this]
        exact hv
      · intro hp
        refine ⟨_, hp, ?_⟩
        funext i
        rfl
    have hfun : ((fun q => Φ (r q ∘ ν)) ∘ transport (leftCongr (κ := Empty) ν)) =
        Φ ∘ leftComponents := by
      funext p
      show Φ _ = Φ _
      congr 1
      funext s
      simp [r, transport, leftCongr, leftComponents]
    rw [hset, hfun] at htr
    exact htr
  have hmat : ∀ b : Module.Basis (Fin 3) ℂ Matrices.ComplexMatrix2.traceless,
      IsHolomorphicToCoords b Coordinates.ComplexCoordinates.matrixEquiv
        (leftComponents ⁻¹' W) (Φ ∘ leftComponents) := fun b =>
    ((hH2.2.2.2.1 σ Empty).2.1 b _ _ (hgroup b).1 (hgroup b).2.1).1 (hgroup b)
  exact ⟨hgroup, hmat, fun b r s => entry_isHolomorphicToCoords (hmat b) r s⟩
private theorem isHolomorphicWithEntries_periodic
    (hH2 : Matrices.GroupLieProduct.ExpChartHolomorphy.ExpChartTheory)
    {L m : ℕ} {i : ℤ} {P : Set (PeriodicLattice.Bond L m i)}
    {O : Set (PeriodicLattice.Bond L m i → Matrices.ComplexMatrix2)}
    {Φ : (PeriodicLattice.Bond L m i → Matrices.ComplexMatrix2) → Matrices.ComplexMatrix2}
    [Fintype (positivePart PeriodicLattice.Bond.IsPositivelyOriented P)]
    (h : PeriodicLattice.IsHolomorphicOnFields P O Φ) :
    IsHolomorphicWithEntries (positiveImage PeriodicLattice.Bond.IsPositivelyOriented P O)
      fun v => Φ (PeriodicLattice.extendFromPositive P v) := by
  have himg : positiveImage PeriodicLattice.Bond.IsPositivelyOriented P O =
      PeriodicLattice.restrictToPositive P '' O := image_image _ _ _
  refine isHolomorphicWithEntries_of_powerCharts hH2
    (Fintype.equivFin (positivePart PeriodicLattice.Bond.IsPositivelyOriented P)) fun β => ?_
  rw [himg]
  exact h.2 _ _ β
private theorem isHolomorphicWithEntries_infinite
    (hH2 : Matrices.GroupLieProduct.ExpChartHolomorphy.ExpChartTheory)
    {a : ℝ} {P : Set (InfiniteLattice.Link a)} {O : Set (InfiniteLattice.Link a → Matrices.ComplexMatrix2)}
    {Φ : (InfiniteLattice.Link a → Matrices.ComplexMatrix2) → Matrices.ComplexMatrix2}
    [Fintype (positivePart InfiniteLattice.Link.IsPositivelyOriented P)]
    (h : Tower.FullSpace.IsHolomorphicOnFields P O Φ) :
    IsHolomorphicWithEntries (positiveImage InfiniteLattice.Link.IsPositivelyOriented P O)
      fun v => Φ (Tower.FullSpace.extendFromPositive P v) := by
  have himg : positiveImage InfiniteLattice.Link.IsPositivelyOriented P O =
      Tower.FullSpace.restrictPositive P '' O := image_image _ _ _
  refine isHolomorphicWithEntries_of_powerCharts hH2
    (Fintype.equivFin (positivePart InfiniteLattice.Link.IsPositivelyOriented P)) fun β => ?_
  rw [himg]
  exact h.2 _ _ β
private theorem mem_complexGaugeGroup_of_mem_compact {X : Matrices.ComplexMatrix2}
    (h : X ∈ PeriodicLattice.compactGaugeGroup) : X ∈ PeriodicLattice.complexGaugeGroup :=
  (Matrix.mem_specialUnitaryGroup_iff.1 h).2
private theorem bondsInDoubleBlock_nonempty
    (hDL : PeriodicLattice.DoubleBlockStructure.Statement) {L n k j : ℕ}
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hj : j < k)
    (c : Tower.Edge L n k (j + 1)) :
    (PeriodicLattice.bondsInDoubleBlock c : Set (Tower.Edge L n k j)).Nonempty := by
  obtain ⟨b, hb⟩ := (hDL L n k j hL hn hj c).2.2.1.2
  exact ⟨b, Or.inl hb.1, Or.inr hb.2⟩
theorem polydiscsHold_of (hE6 : Tower.BondSetFields.ProductStructureHolds)
    (hAvg : Tower.SmoothingNearIdentity)
    (hH2 : Matrices.GroupLieProduct.ExpChartHolomorphy.ExpChartTheory)
    (hDL : PeriodicLattice.DoubleBlockStructure.Statement)
    (hK : Tower.FullSpace.DoubleCubeLinksAndTorusImage) : PolydiscsHold := by
  intro L hL k j hj
  have hρ := (hAvg.1 L hL).2.2
  have hE := hE6 L hL k j hj.le
  refine ⟨fun n hn c hc => ?_, fun c hc => ?_⟩
  · have hfin : (doubleBlockBonds c).Finite := (hE.1 n hn).2.1.subset (subset_univ _)
    have hrev : PeriodicLattice.IsReversalClosed (doubleBlockBonds c) :=
      (hDL L n k j hL hn hj c).1.2.2.1
    have hP := (hE.1 n hn).1 _ hfin (bondsInDoubleBlock_nonempty hDL hL hn hj c) hrev
    have hs := hρ.periodic n k j hn hj c hc
    have hfo : FiniteOpenPolydisc PeriodicLattice.Bond.opposite
        PeriodicLattice.Bond.IsPositivelyOriented
        PeriodicLattice.IsGaugeField (doubleBlockBonds c)
        (Tower.nearIdentityPolydisc (Tower.polydiscRadius L) c) :=
      finiteOpenPolydisc_of_productStructure hρ.pos hfin hrev hP fun U hU =>
        ⟨fun b hb => mem_complexGaugeGroup_of_mem_compact (hU.1 b hb), hU.2⟩
    refine ⟨rfl, hfo, ⟨hfo.positive_finite.fintype, ?_⟩, fun y hy x hx =>
      ⟨hfo.positive_finite.fintype, ?_⟩⟩
    · let _ := hfo.positive_finite.fintype
      exact isHolomorphicWithEntries_periodic hH2 hs.holomorphic_smoothing
    · let _ := hfo.positive_finite.fintype
      exact isHolomorphicWithEntries_periodic hH2 (hs.holomorphic_contourMean y hy x hx)
  · have hKc := hK L k (j + 1) hL (by omega) (by omega) c hc
    have hbij : BijOn (Tower.FullSpace.projEdge L 1 k j) (Infinite.doubleBlockBonds L k j c)
        (PeriodicLattice.bondsInDoubleBlock (Tower.FullSpace.projEdge L 1 k (j + 1) c)) :=
      (hKc.2 1 Nat.one_pos).2.2.2.2.2.2
    have hfinT : (PeriodicLattice.bondsInDoubleBlock (Tower.FullSpace.projEdge L 1 k (j + 1) c) :
        Set (Tower.Edge L 1 k j)).Finite :=
      ((hE6 L hL k j hj.le).1 1 le_rfl).2.1.subset (subset_univ _)
    have hfin : (Infinite.doubleBlockBonds L k j c).Finite :=
      Set.Finite.of_injOn hbij.mapsTo hbij.injOn hfinT
    have hne : (Infinite.doubleBlockBonds L k j c).Nonempty := by
      obtain ⟨b, hb⟩ := bondsInDoubleBlock_nonempty hDL hL Nat.one_pos hj
        (Tower.FullSpace.projEdge L 1 k (j + 1) c)
      obtain ⟨b', hb', -⟩ := hbij.surjOn hb
      exact ⟨b', hb'⟩
    have hrev : ∀ b ∈ Infinite.doubleBlockBonds L k j c,
        b.opposite ∈ Infinite.doubleBlockBonds L k j c :=
      hKc.1.2
    have hP := hE.2 _ hfin hne hrev
    have hs := hρ.fullSpace k j hj c hc
    have hfo : FiniteOpenPolydisc InfiniteLattice.Link.opposite
        InfiniteLattice.Link.IsPositivelyOriented Tower.FullSpace.IsFieldOn
        (Infinite.doubleBlockBonds L k j c)
        (Tower.FullSpace.nearIdentityPolydisc L k j (Tower.polydiscRadius L) c) :=
      finiteOpenPolydisc_of_productStructure hρ.pos hfin hrev hP fun U hU =>
        ⟨fun b hb => mem_complexGaugeGroup_of_mem_compact (hU.1 b hb), hU.2⟩
    refine ⟨rfl, hfo, ⟨hfo.positive_finite.fintype, ?_⟩, fun y hy x hx =>
      ⟨hfo.positive_finite.fintype, ?_⟩⟩
    · let _ := hfo.positive_finite.fintype
      exact isHolomorphicWithEntries_infinite hH2 hs.holomorphic_smoothing
    · let _ := hfo.positive_finite.fintype
      exact isHolomorphicWithEntries_infinite hH2 (hs.holomorphic_contourMean y hy x hx)
end YangMills.Construction.Tower.DoubleBlockPolydisc
end
