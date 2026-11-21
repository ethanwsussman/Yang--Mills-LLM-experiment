import YangMills.Construction.Towers.AveragedContoursOnThePolydiscs
import YangMills.Construction.Towers.ComplexAveragesFormedLevelByLevelProof
import Mathlib
set_option autoImplicit false
open Set Filter YangMills.Construction.Matrices YangMills.Construction.Matrices.GroupLieProduct YangMills.Construction.Coordinates
open scoped Topology Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.Tower.PolydiscContours
section Coordinates
open YangMills.Construction.Coordinates.ComplexCoordinates
theorem isHolomorphicIn_of_eqOn {N N' : ℕ} {O : Set (ComplexCoordinates N)}
    {f g : ComplexCoordinates N → ComplexCoordinates N'} (h : IsHolomorphicIn O f)
    (hfg : ∀ z ∈ O, f z = g z) : IsHolomorphicIn O g := by apply _root_.YangMills.Construction.Averaging.ComplexLogMean.isHolomorphicIn_congr <;> assumption
end Coordinates
section Rules
open YangMills.Construction.Coordinates.ComplexCoordinates
variable {ι ι' : Type} [Fintype ι] [Fintype ι']
variable (H : ExpChartHolomorphy.ExpChartTheory)
  (β : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless)
include H
theorem isHolomorphicToUnimodular_eval {W : Set (ι ⊕ Empty → ComplexMatrix2)}
    (hW : ComplexMatrix2.IsRelativelyOpen (GroupLieProduct ι Empty) W) (i : ι) :
    IsHolomorphicToUnimodular β W fun p => p (.inl i) := by apply _root_.YangMills.Construction.Tower.LevelwiseMeans.isHolomorphicToUnimodular_component <;> assumption
theorem isHolomorphicToCoords_comp {E : Type} {l : ℕ} (e : E ≃ ComplexCoordinates l)
    {W : Set (ι ⊕ Empty → ComplexMatrix2)} {Ψ : (ι ⊕ Empty → ComplexMatrix2) → ι' ⊕ Empty → ComplexMatrix2}
    (hΨ : IsHolomorphicToProduct β W Ψ) {W' : Set (ι' ⊕ Empty → ComplexMatrix2)}
    {Φ : (ι' ⊕ Empty → ComplexMatrix2) → E} (hΦ : IsHolomorphicToCoords β e W' Φ)
    (hs : MapsTo Ψ W W') {Φ' : (ι ⊕ Empty → ComplexMatrix2) → E} (he : ∀ p ∈ W, Φ (Ψ p) = Φ' p) :
    IsHolomorphicToCoords β e W Φ' := by
  obtain ⟨_, _, hh⟩ := H.2.2.2.2.1 ι Empty ι' Empty β W Ψ hΨ.1 hΨ E l e W' Φ hΦ
  have hW : W ∩ Ψ ⁻¹' W' = W := inter_eq_left.2 fun p hp => hs hp
  rw [hW] at hh
  obtain ⟨ho, hc, hl⟩ := hh
  refine ⟨ho, hc.congr fun p hp => ?_, fun p hp => ?_⟩
  · simp only [Function.comp_apply, he p hp]
  · obtain ⟨O, h0, hO, ht, hhol⟩ := hl p hp
    refine ⟨O, h0, hO, ht, fun ν => isHolomorphicIn_of_eqOn (hhol ν) fun z hz => ?_⟩
    simp only [Function.comp_apply]
    rw [he _ (hO _ hz)]
end Rules
section Points
open DoubleBlockPolydisc
variable {σ : Type}
theorem asGroupFactors_image (O : Set (σ → ComplexMatrix2)) :
    asGroupFactors '' O = leftComponents ⁻¹' O := by apply _root_.YangMills.Construction.Tower.LevelwiseMeans.image_asGroupFactors <;> assumption
theorem isRelativelyOpen_leftComponents_preimage {O : Set (σ → ComplexMatrix2)}
    (h : ComplexMatrix2.IsRelativelyOpen (unimodularPi σ) O) :
    ComplexMatrix2.IsRelativelyOpen (GroupLieProduct σ Empty) (leftComponents ⁻¹' O) := by apply _root_.YangMills.Construction.Tower.LevelwiseMeans.isRelativelyOpen_preimage_leftComponents <;> assumption
end Points
section FiniteSide
open DoubleBlockPolydisc (leftComponents)
variable {L n k i : ℕ}
theorem inv_inv_of_mem_unitDeterminant {X : ComplexMatrix2}
    (h : X ∈ ComplexMatrix2.unitDeterminant) : X⁻¹⁻¹ = X := by apply _root_.YangMills.Construction.Tower.LevelwiseMeans.inv_inv_of_mem_unitDeterminant <;> assumption
theorem pathHolonomy_congr {j : ℤ} {W W' : PeriodicLattice.Bond L n j → ComplexMatrix2}
    {Γ : List (PeriodicLattice.Bond L n j)} (h : ∀ b ∈ Γ, W b = W' b) :
    PeriodicLattice.pathHolonomy W Γ = PeriodicLattice.pathHolonomy W' Γ := by apply _root_.YangMills.Construction.PeriodicLattice.ComplexAverageLocality.pathHolonomy_congr <;> assumption
theorem complexMeanContourHolonomy_congr (hPaths : PeriodicLattice.BlockPaths.Statement)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hi : i < k)
    {c : Edge L n k (i + 1)} (hc : c.IsPositivelyOriented) {y : Vertex L n k (i + 1)}
    (hy : y ∈ ({c.source, c.target} : Set (Vertex L n k (i + 1))))
    {x : Vertex L n k i} (hx : x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k i) y)
    {V V' : Edge L n k i → ComplexMatrix2}
    (he : ∀ b ∈ (PeriodicLattice.bondsInDoubleBlock c : Set (Edge L n k i)), V b = V' b) :
    PeriodicLattice.complexMeanContourHolonomy V y x =
      PeriodicLattice.complexMeanContourHolonomy V' y x := by
  obtain ⟨μ, hμ⟩ := hc
  obtain ⟨-, hcμ⟩ := hPaths L n k hL.1 hL.2 hn i hi
  obtain ⟨-, -, -, -, hp⟩ := hcμ c μ hμ
  have hy' : y = c.source ∨ y = c.target := by simpa using hy
  have hval : PeriodicLattice.contourHolonomies V y x = PeriodicLattice.contourHolonomies V' y x := by
    funext σ
    exact pathHolonomy_congr fun b hb => he b ((hp.1 y hy' x hx).1 _ ⟨σ, rfl⟩ b hb)
  unfold PeriodicLattice.complexMeanContourHolonomy
  rw [hval]
theorem eq_fieldOfValues_of_mem_polydisc
    (hxor : ∀ b : Edge L n k i, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    {c : Edge L n k (i + 1)} {ρ : ℝ} (hpoly : DoubleBlockPolydisc.PolydiscPropertiesAt ρ c)
    {V : Edge L n k i → ComplexMatrix2} (hVp : V ∈ nearIdentityPolydisc ρ c)
    {b : Edge L n k i} (hb : b ∈ (PeriodicLattice.bondsInDoubleBlock c : Set (Edge L n k i))) :
    V b = DoubleBlockPolydisc.fieldOfValues c (fun b => V b.1) b := by
  unfold DoubleBlockPolydisc.fieldOfValues PeriodicLattice.extendFromPositive
  by_cases hp : b.IsPositivelyOriented
  · rw [dif_pos (⟨hb, hp⟩ : b ∈ DoubleBlockPolydisc.doubleBlockBonds c ∧ b.IsPositivelyOriented)]
  · have hrp : b.opposite.IsPositivelyOriented := by
      rcases hxor b with h | h
      · exact absurd h.1 hp
      · exact h.1
    have hrb : b.opposite ∈ DoubleBlockPolydisc.doubleBlockBonds c :=
      hpoly.finite_open.opposite_mem b hb
    rw [dif_neg (fun h : b ∈ DoubleBlockPolydisc.doubleBlockBonds c ∧ b.IsPositivelyOriented =>
        hp h.2),
      dif_pos (⟨hrb, hrp⟩ : b.opposite ∈ DoubleBlockPolydisc.doubleBlockBonds c ∧
        b.opposite.IsPositivelyOriented)]
    have e : (V b.opposite)⁻¹ = ((V b)⁻¹)⁻¹ := congrArg (·⁻¹) (hVp.1.2 b hb)
    exact (e.trans (inv_inv_of_mem_unitDeterminant (hVp.1.1 b hb))).symm
theorem fieldOfPositiveValues_restrictToPositiveEdges
    (hxor : ∀ b : Edge L n k i, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    {U : Edge L n k i → ComplexMatrix2}
    (hU : U ∈ fieldsIn L n k i PeriodicLattice.complexGaugeGroup) :
    fieldOfPositiveValues (restrictToPositiveEdges U) = U := by
  funext b
  rcases hxor b with h | h
  · simp only [fieldOfPositiveValues, dif_pos h.1]
    rfl
  · simp only [fieldOfPositiveValues, dif_neg h.2, dif_pos h.1]
    have e : U b.opposite = (U b)⁻¹ := hU.2 b (mem_univ _)
    show (U b.opposite)⁻¹ = U b
    rw [e]
    exact inv_inv_of_mem_unitDeterminant (hU.1 b (mem_univ _))
theorem isHolomorphicToCoords_of_positiveValues (H : ExpChartHolomorphy.ExpChartTheory)
    (hxor : ∀ b : Edge L n k i, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    [Fintype (PositiveEdge L n k i)] {c : Edge L n k (i + 1)}
    [Fintype (DoubleBlockPolydisc.positiveDoubleBlockBonds c)] {ρ : ℝ}
    (β : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless) {𝔇 : Set (Edge L n k i → ComplexMatrix2)}
    (ho : IsOpenFieldSet PeriodicLattice.complexGaugeGroup 𝔇)
    (hmem : ∀ U ∈ 𝔇, U ∈ nearIdentityPolydisc ρ c)
    {E : Type} {l : ℕ} (e : E ≃ ComplexCoordinates l)
    {Φ : (DoubleBlockPolydisc.positiveDoubleBlockBonds c → ComplexMatrix2) → E}
    (hΦ : IsHolomorphicToCoords β e
      (leftComponents ⁻¹' DoubleBlockPolydisc.polydiscPositive ρ c) fun p => Φ (leftComponents p))
    {h : (Edge L n k i → ComplexMatrix2) → E} (hval : ∀ U ∈ 𝔇, Φ (fun s => U s.1) = h U) :
    IsHolomorphicToCoords β e (asGroupFactors '' (restrictToPositiveEdges '' 𝔇))
      fun p => h (fieldOfPositiveValues fun b => p (.inl b)) := by
  have hW : ComplexMatrix2.IsRelativelyOpen (GroupLieProduct (PositiveEdge L n k i) Empty)
      (asGroupFactors '' (restrictToPositiveEdges '' 𝔇)) := by
    rw [asGroupFactors_image]
    exact isRelativelyOpen_leftComponents_preimage ho.2
  let Ψ : (PositiveEdge L n k i ⊕ Empty → ComplexMatrix2) →
      DoubleBlockPolydisc.positiveDoubleBlockBonds c ⊕ Empty → ComplexMatrix2 :=
    fun p => asGroupFactors fun s => p (.inl ⟨s.1, s.2.2⟩)
  have hΨ : IsHolomorphicToProduct β _ Ψ :=
    ⟨hW, fun s => isHolomorphicToUnimodular_eval H β hW ⟨s.1, s.2.2⟩, fun e => e.elim⟩
  refine isHolomorphicToCoords_comp H β e hΨ hΦ ?_ ?_
  · rintro _ ⟨_, ⟨U, hU, rfl⟩, rfl⟩
    exact ⟨_, ⟨U, hmem U hU, rfl⟩, rfl⟩
  · rintro _ ⟨_, ⟨U, hU, rfl⟩, rfl⟩
    have e1 : fieldOfPositiveValues (fun b => asGroupFactors (restrictToPositiveEdges U) (.inl b)) = U :=
      fieldOfPositiveValues_restrictToPositiveEdges hxor (ho.1 hU)
    show Φ (fun s => U s.1) = h (fieldOfPositiveValues _)
    rw [e1]
    exact hval U hU
theorem contourPropertiesAt_of_side (H : ExpChartHolomorphy.ExpChartTheory)
    (hPaths : PeriodicLattice.BlockPaths.Statement)
    (hxor : ∀ b : Edge L n k i, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    [Fintype (PositiveEdge L n k i)] (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n)
    (hi : i < k) {c : Edge L n k (i + 1)} (hc : c.IsPositivelyOriented)
    (hpoly : DoubleBlockPolydisc.PolydiscPropertiesAt (polydiscRadius L) c)
    (ho : IsOpenFieldSet PeriodicLattice.complexGaugeGroup
      (MeanStableFields.fieldsNearOne L n k i))
    (hmem : ∀ U ∈ MeanStableFields.fieldsNearOne L n k i,
      U ∈ nearIdentityPolydisc (polydiscRadius L) c) : ContourPropertiesAt c := by
  refine ⟨hpoly.finite_open.positive_finite, hpoly.finite_open.positive_nonempty,
    hpoly.finite_open.isRelativelyOpen, hpoly.holomorphic_contourMean, fun y hy x hx => ?_⟩
  obtain ⟨inst, hh⟩ := hpoly.holomorphic_contourMean y hy x hx
  have hval : ∀ U ∈ MeanStableFields.fieldsNearOne L n k i,
      PeriodicLattice.complexMeanContourHolonomy
          (DoubleBlockPolydisc.fieldOfValues c fun s => U s.1) y x =
        PeriodicLattice.complexMeanContourHolonomy U y x := fun U hU =>
    (complexMeanContourHolonomy_congr hPaths hL hn hi hc hy hx fun b hb =>
      eq_fieldOfValues_of_mem_polydisc hxor hpoly (hmem U hU) hb).symm
  refine ⟨fun β => ⟨ho, inferInstance, ?_⟩, inferInstance, fun β r s => ?_⟩
  · have hc' := isHolomorphicToCoords_of_positiveValues H hxor β ho hmem
      ComplexCoordinates.matrixEquiv
      (Φ := fun v => PeriodicLattice.complexMeanContourHolonomy
        (DoubleBlockPolydisc.fieldOfValues c v) y x)
      (h := fun U => PeriodicLattice.complexMeanContourHolonomy U y x) (hh.toMatrices β) hval
    refine ((H.2.2.2.1 (PositiveEdge L n k i) Empty).2.1 β _ _ hc'.1 ?_).2 hc'
    rintro _ ⟨_, ⟨U, hU, rfl⟩, rfl⟩
    have e1 : fieldOfPositiveValues (fun b => asGroupFactors (restrictToPositiveEdges U) (.inl b)) = U :=
      fieldOfPositiveValues_restrictToPositiveEdges hxor (ho.1 hU)
    have hm : asGroupFactors (fun s : DoubleBlockPolydisc.positiveDoubleBlockBonds c => U s.1) ∈
        leftComponents ⁻¹' DoubleBlockPolydisc.polydiscPositive (polydiscRadius L) c :=
      ⟨_, ⟨U, hmem U hU, rfl⟩, rfl⟩
    have hv := (hh.toUnimodular β).2.1 hm
    have eg : leftComponents
        (asGroupFactors fun s : DoubleBlockPolydisc.positiveDoubleBlockBonds c => U s.1) =
        fun s => U s.1 := rfl
    simp only [Function.comp_apply, eg, hval U hU] at hv
    simp only [e1]
    exact hv
  · exact isHolomorphicToCoords_of_positiveValues H hxor β ho hmem (Equiv.funUnique (Fin 1) ℂ).symm
      (Φ := fun v => PeriodicLattice.complexMeanContourHolonomy
        (DoubleBlockPolydisc.fieldOfValues c v) y x r s)
      (h := fun U => PeriodicLattice.complexMeanContourHolonomy U y x r s)
      (hh.entries β r s) fun U hU => congrFun (congrFun (hval U hU) r) s
end FiniteSide
theorem contourHolomorphyHolds_of (H : ExpChartHolomorphy.ExpChartTheory)
    (hP : DoubleBlockPolydisc.PolydiscsHold)
    (hD : MeanStableFields.MeanStableFieldsHold)
    (hPaths : PeriodicLattice.BlockPaths.Statement)
    (hE : PeriodicLattice.BondEndpointsOrientation.Statement)
    (hE6 : BondSetFields.ProductStructureHolds) : ContourHolomorphyHolds := by
  intro L hL k i hi
  have hk : 1 ≤ k := by omega
  refine ⟨fun n hn c hc => ?_, fun c hc => ?_⟩
  · have hS := (hD L hL k hk).1 n hn
    have hbonds : Finite (Edge L n k i) :=
      Set.finite_univ_iff.1 ((hE6 L hL k i hi.le).1 n hn).2.1
    have hfin : Finite (PositiveEdge L n k i) := Subtype.finite
    let _ : Fintype (PositiveEdge L n k i) := Fintype.ofFinite _
    have hxor : ∀ b : Edge L n k i, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented :=
      fun b => ((hE ⟨L, hL, ⟨k, hk⟩, ⟨n, hn⟩⟩ i hi.le).2.2.2 b).2.2.2.2.2
    exact contourPropertiesAt_of_side H hPaths hxor hL hn hi hc
      ((hP L hL k i hi).1 n hn c hc) (hS.isOpen_nearOne i hi) (hS.mem_polydisc i hi c hc)
  · have h := (hP L hL k i hi).2 c hc
    exact ⟨h.finite_open.positive_finite, h.finite_open.positive_nonempty,
      h.finite_open.isRelativelyOpen, h.holomorphic_contourMean⟩
end YangMills.Construction.Tower.PolydiscContours
end
