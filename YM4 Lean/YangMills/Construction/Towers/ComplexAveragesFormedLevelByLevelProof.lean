import YangMills.Construction.Lattice.AverageOfAConfigurationTrivialInsideTwoBlocksProof
import YangMills.Construction.Matrices.LinearMapsCompositesAndCoordinatesOfRealAnalyticMapsProof
import YangMills.Construction.Averaging.MeanInTheComplexGroupProof
import YangMills.Construction.Lattice.BondsPathsAndAveragesOfADoubleBlock
import YangMills.Construction.Lattice.EndPointsAndOrientationOfABond
import YangMills.Construction.Towers.AveragesAtTheSideInfinityNearTheTrivialConfiguration
import YangMills.Construction.Towers.ComplexAverageLiesInTheComplexGroup
import YangMills.Construction.Towers.ComplexAveragesFormedLevelByLevel
import YangMills.Construction.Towers.ConfigurationsUnderTheLeftChart
import YangMills.Construction.Towers.LatticesIsometriesDilationsAndQuotientsOfATower
import YangMills.Construction.Towers.PolydiscsOfDoubleBlocks
import YangMills.Construction.Towers.PropertiesOfTheGaugeFixingFunctions
import YangMills.Construction.Towers.RealAnalyticMapsOfConfigurationsAreDifferentiableProof
import Mathlib
set_option autoImplicit false
open Set Filter
open scoped Topology Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.Tower.LevelwiseMeans
open YangMills.Construction.Matrices YangMills.Construction.Matrices.GroupLieProduct YangMills.Construction.Coordinates
section Coordinates
open YangMills.Construction.Coordinates.ComplexCoordinates
theorem isHolomorphicIn_proj {N N' : ℕ} (τ : Fin N' → Fin N) :
    IsHolomorphicIn univ (fun (z : ComplexCoordinates N) (t : Fin N') => z (τ t)) := by
  refine ⟨isOpen_univ, Continuous.continuousOn (by fun_prop),
    fun a _ j => Eventually.of_forall fun ζ => ?_⟩
  rw [differentiableAt_pi]
  intro t
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  fun_prop
theorem isHolomorphicIn_mono {N N' : ℕ} {O O' : Set (ComplexCoordinates N)}
    {f : ComplexCoordinates N → ComplexCoordinates N'} (h : IsHolomorphicIn O f) (hO' : IsOpen O')
    (hs : O' ⊆ O) : IsHolomorphicIn O' f :=
  ⟨hO', h.2.1.mono hs, fun a ha j => h.2.2 a (hs ha) j⟩
theorem isHolomorphicIn_congr {N N' : ℕ} {O : Set (ComplexCoordinates N)}
    {f g : ComplexCoordinates N → ComplexCoordinates N'} (h : IsHolomorphicIn O f)
    (hfg : ∀ z ∈ O, f z = g z) : IsHolomorphicIn O g := by apply _root_.YangMills.Construction.Averaging.ComplexLogMean.isHolomorphicIn_congr <;> assumption
variable {σ : Type}
def entryIndexOf {k : ℕ} (ν : σ ≃ Fin k) (i : σ) (t : Fin 4) :
    Fin (productDim fun _ : Fin k => Component.matrix) :=
  finSigmaFinEquiv (n := fun i => ((fun _ : Fin k => Component.matrix) i).dim) ⟨ν i, t⟩
theorem matrixPiEquiv_entryIndexOf {k : ℕ} (ν : σ ≃ Fin k) (p : σ → ComplexMatrix2) (i : σ)
    (t : Fin 4) : matrixPiEquiv ν p (entryIndexOf ν i t) = matrixEquiv (p i) t := by
  have key : ∀ u, matrixPiEquiv ν p u = matrixEquiv
      (p (ν.symm ((finSigmaFinEquiv
        (n := fun i => ((fun _ : Fin k => Component.matrix) i).dim)).symm u).1))
      ((finSigmaFinEquiv
        (n := fun i => ((fun _ : Fin k => Component.matrix) i).dim)).symm u).2 := fun _ => rfl
  rw [key, entryIndexOf, Equiv.symm_apply_apply]
  simp
theorem matrixEquiv_matrixPiEquiv_symm {k : ℕ} (ν : σ ≃ Fin k) (z) (i : σ) (t : Fin 4) :
    matrixEquiv ((matrixPiEquiv ν).symm z i) t = z (entryIndexOf ν i t) := by
  rw [← matrixPiEquiv_entryIndexOf, Equiv.apply_symm_apply]
theorem continuous_matrixPiEquiv_symm {k : ℕ} (ν : σ ≃ Fin k) :
    Continuous (matrixPiEquiv ν).symm := by
  refine continuous_pi fun i => continuous_matrix fun a c => ?_
  have h : (fun z => (matrixPiEquiv ν).symm z i a c) =
      fun z => z (entryIndexOf ν i (entryIndex (a, c))) := by
    funext z
    refine Eq.trans ?_ (matrixEquiv_matrixPiEquiv_symm ν z i (entryIndex (a, c)))
    simp [matrixEquiv]
  rw [h]
  exact continuous_apply _
theorem isOpen_matrixPiEquiv_image {k : ℕ} (ν : σ ≃ Fin k) {O : Set (σ → ComplexMatrix2)}
    (hO : IsOpen O) : IsOpen (matrixPiEquiv ν '' O) := by
  rw [Equiv.image_eq_preimage_symm]
  exact hO.preimage (continuous_matrixPiEquiv_symm ν)
theorem component_comp_eq_proj {k : ℕ} (ν : σ ≃ Fin k) (i : σ) :
    matrixEquiv ∘ (fun p : σ → ComplexMatrix2 => p i) ∘ (matrixPiEquiv ν).symm =
      fun z t => z (entryIndexOf ν i t) := by
  funext z t
  exact matrixEquiv_matrixPiEquiv_symm ν z i t
theorem isHolomorphicVia_component {k : ℕ} (ν : σ ≃ Fin k) (i : σ) {O : Set (σ → ComplexMatrix2)}
    (hO : IsOpen O) : IsHolomorphicVia (matrixPiEquiv ν) matrixEquiv O fun p => p i := by
  unfold IsHolomorphicVia
  rw [component_comp_eq_proj]
  exact isHolomorphicIn_mono (isHolomorphicIn_proj _) (isOpen_matrixPiEquiv_image ν hO)
    (subset_univ _)
theorem isOpen_isUnit_component (i : σ) : IsOpen {p : σ → ComplexMatrix2 | IsUnit (p i)} := by
  have h : {p : σ → ComplexMatrix2 | IsUnit (p i)} =
      (fun p : σ → ComplexMatrix2 => (p i).det) ⁻¹' {0}ᶜ := by
    ext p
    simp [Matrix.isUnit_iff_isUnit_det]
  rw [h]
  exact isOpen_compl_singleton.preimage (by fun_prop)
theorem isHolomorphicVia_inv_component (hm : ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    {k : ℕ} (ν : σ ≃ Fin k) (i : σ) :
    IsHolomorphicVia (matrixPiEquiv ν) matrixEquiv
      {p : σ → ComplexMatrix2 | IsUnit (p i)} fun p => (p i)⁻¹ := by
  have hinv := hm.2.2.2.1
  unfold IsHolomorphicVia at hinv ⊢
  have hO := isOpen_matrixPiEquiv_image ν (isOpen_isUnit_component (σ := σ) i)
  have hsel := isHolomorphicIn_mono (isHolomorphicIn_proj (entryIndexOf ν i)) hO (subset_univ _)
  have hmaps : MapsTo (fun z (t : Fin 4) => z (entryIndexOf ν i t))
      (matrixPiEquiv ν '' {p : σ → ComplexMatrix2 | IsUnit (p i)})
      (matrixEquiv '' {X : ComplexMatrix2 | IsUnit X}) := by
    rintro _ ⟨p, hp, rfl⟩
    refine ⟨p i, hp, ?_⟩
    funext t
    exact (matrixPiEquiv_entryIndexOf ν p i t).symm
  have hc := ((hm.1 4 _ hinv.1).1 4 _ hinv).2.2.2.1 _ _ _ hsel hmaps
  refine isHolomorphicIn_congr hc fun z _ => ?_
  have e : (fun t : Fin 4 => z (entryIndexOf ν i t)) =
      matrixEquiv ((matrixPiEquiv ν).symm z i) := by
    funext t
    exact (matrixEquiv_matrixPiEquiv_symm ν z i t).symm
  simp only [Function.comp_apply, e, Equiv.symm_apply_apply]
end Coordinates
section Rules
open YangMills.Construction.Coordinates.ComplexCoordinates
variable {ι ι' : Type} [Fintype ι] [Fintype ι']
omit [Fintype ι] [Fintype ι'] in
theorem mem_groupLieProduct_empty {p : ι ⊕ Empty → ComplexMatrix2} :
    p ∈ GroupLieProduct ι Empty ↔ ∀ i, p (.inl i) ∈ ComplexMatrix2.unitDeterminant :=
  ⟨fun h i => h (.inl i), fun h i => by
    rcases i with i | e
    · exact h i
    · exact e.elim⟩
theorem inv_mem_unitDeterminant {X : ComplexMatrix2} (h : X ∈ ComplexMatrix2.unitDeterminant) :
    X⁻¹ ∈ ComplexMatrix2.unitDeterminant := by apply _root_.YangMills.SharedProofs.p413 <;> assumption
theorem isUnit_of_mem_unitDeterminant {X : ComplexMatrix2}
    (h : X ∈ ComplexMatrix2.unitDeterminant) : IsUnit X := by apply _root_.YangMills.Construction.Averaging.ComplexLogMean.isUnit_of_mem_complexGaugeGroup <;> assumption
theorem inv_inv_of_mem_unitDeterminant {X : ComplexMatrix2}
    (h : X ∈ ComplexMatrix2.unitDeterminant) : X⁻¹⁻¹ = X := by apply _root_.YangMills.DeltaSharedProofs.p3551 <;> assumption
variable (H : ExpChartHolomorphy.ExpChartTheory)
  (hm : ComplexCoordinates.PowerSeriesHolomorphy.Properties)
  (β : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless)
include H
theorem isHolomorphicToUnimodular_of_via {k : ℕ} (ν : ι ⊕ Empty ≃ Fin k)
    {O : Set (ι ⊕ Empty → ComplexMatrix2)} {F : (ι ⊕ Empty → ComplexMatrix2) → ComplexMatrix2}
    (hF : IsHolomorphicVia (matrixPiEquiv ν) matrixEquiv O F)
    (hv : MapsTo F (O ∩ GroupLieProduct ι Empty) ComplexMatrix2.unitDeterminant) :
    IsHolomorphicToUnimodular β (O ∩ GroupLieProduct ι Empty) F := by
  obtain ⟨_, hG, hR⟩ := H.2.2.2.1 ι Empty
  obtain ⟨ho, hh⟩ := hR ComplexMatrix2 4 k matrixEquiv ν O F hF
  exact (hG β _ F ho hv).2 (hh β)
theorem isHolomorphicToUnimodular_component {W : Set (ι ⊕ Empty → ComplexMatrix2)}
    (hW : ComplexMatrix2.IsRelativelyOpen (GroupLieProduct ι Empty) W) (i : ι) :
    IsHolomorphicToUnimodular β W fun p => p (.inl i) := by
  obtain ⟨O, hO, rfl⟩ := hW
  exact isHolomorphicToUnimodular_of_via H β (Fintype.equivFin _)
    (isHolomorphicVia_component _ _ hO) fun p hp => mem_groupLieProduct_empty.1 hp.2 i
theorem isHolomorphicToUnimodular_comp {W : Set (ι ⊕ Empty → ComplexMatrix2)}
    {Ψ : (ι ⊕ Empty → ComplexMatrix2) → ι' ⊕ Empty → ComplexMatrix2}
    (hΨ : IsHolomorphicToProduct β W Ψ)
    {W' : Set (ι' ⊕ Empty → ComplexMatrix2)} {Φ : (ι' ⊕ Empty → ComplexMatrix2) → ComplexMatrix2}
    (hΦ : IsHolomorphicToUnimodular β W' Φ) :
    IsHolomorphicToUnimodular β (W ∩ Ψ ⁻¹' W') (Φ ∘ Ψ) := by
  have hG' := (H.2.2.2.1 ι' Empty).2.1
  have hG := (H.2.2.2.1 ι Empty).2.1
  have hΦ' := (hG' β W' Φ hΦ.1 hΦ.2.1).1 hΦ
  obtain ⟨_, ho, hh⟩ :=
    H.2.2.2.2.1 ι Empty ι' Empty β W Ψ hΨ.1 hΨ ComplexMatrix2 4 matrixEquiv W' Φ hΦ'
  exact (hG β _ _ ho fun p hp => hΦ.2.1 hp.2).2 hh
theorem isHolomorphicToUnimodular_mono {W W' : Set (ι ⊕ Empty → ComplexMatrix2)}
    {Φ : (ι ⊕ Empty → ComplexMatrix2) → ComplexMatrix2}
    (hΦ : IsHolomorphicToUnimodular β W' Φ)
    (hW : ComplexMatrix2.IsRelativelyOpen (GroupLieProduct ι Empty) W)
    (hs : W ⊆ W') : IsHolomorphicToUnimodular β W Φ := by
  have hΨ : IsHolomorphicToProduct β W (fun p : ι ⊕ Empty → ComplexMatrix2 => p) :=
    ⟨hW, fun i => isHolomorphicToUnimodular_component H β hW i, fun k => k.elim⟩
  have h := isHolomorphicToUnimodular_comp H β hΨ hΦ
  have e : W ∩ (fun p : ι ⊕ Empty → ComplexMatrix2 => p) ⁻¹' W' = W := inter_eq_left.2 hs
  rw [e] at h
  exact h
omit H in
theorem isHolomorphicToUnimodular_congr {W : Set (ι ⊕ Empty → ComplexMatrix2)}
    {Φ Φ' : (ι ⊕ Empty → ComplexMatrix2) → ComplexMatrix2}
    (hΦ : IsHolomorphicToUnimodular β W Φ) (he : ∀ p ∈ W, Φ p = Φ' p) :
    IsHolomorphicToUnimodular β W Φ' := by
  obtain ⟨ho, hmaps, hc, hl⟩ := hΦ
  refine ⟨ho, fun p hp => he p hp ▸ hmaps hp, hc.congr fun p hp => (he p hp).symm,
    fun p hp => ?_⟩
  obtain ⟨O, h0, hO, ht, hh⟩ := hl p hp
  refine ⟨O, h0, fun A hA => ?_, ht, fun ν => ?_⟩
  · rw [← he _ (hO A hA).1, ← he p hp]
    exact hO A hA
  · refine isHolomorphicIn_congr (hh ν) fun z hz => ?_
    simp only [Function.comp_apply]
    rw [← he _ (hO _ hz).1, ← he p hp]
include hm
theorem isHolomorphicToUnimodular_inv {W : Set (ι ⊕ Empty → ComplexMatrix2)}
    {Φ : (ι ⊕ Empty → ComplexMatrix2) → ComplexMatrix2}
    (hΦ : IsHolomorphicToUnimodular β W Φ) :
    IsHolomorphicToUnimodular β W fun p => (Φ p)⁻¹ := by
  have hinv : IsHolomorphicToUnimodular β (GroupLieProduct Unit Empty)
      fun r => (r (.inl ()))⁻¹ := by
    have h := isHolomorphicToUnimodular_of_via (ι := Unit) H β (Fintype.equivFin _)
      (isHolomorphicVia_inv_component hm (Fintype.equivFin (Unit ⊕ Empty)) (.inl ()))
      fun p hp => inv_mem_unitDeterminant (mem_groupLieProduct_empty.1 hp.2 ())
    have e : {p : Unit ⊕ Empty → ComplexMatrix2 | IsUnit (p (.inl ()))} ∩
        GroupLieProduct Unit Empty = GroupLieProduct Unit Empty :=
      inter_eq_right.2 fun p hp =>
        isUnit_of_mem_unitDeterminant (mem_groupLieProduct_empty.1 hp ())
    rwa [e] at h
  have hΨ : IsHolomorphicToProduct (ι' := Unit) (κ' := Empty) β W
      (fun p => Sum.elim (fun _ => Φ p) Empty.elim) :=
    ⟨hΦ.1, fun _ => hΦ, fun k => k.elim⟩
  have h := isHolomorphicToUnimodular_comp H β hΨ hinv
  have e : W ∩ (fun p => Sum.elim (fun _ : Unit => Φ p) Empty.elim) ⁻¹'
      GroupLieProduct Unit Empty = W :=
    inter_eq_left.2 fun p hp => mem_groupLieProduct_empty.2 fun _ => hΦ.2.1 hp
  rw [e] at h
  exact h
omit hm H [Fintype ι] [Fintype ι'] in
theorem isRelativelyOpen_setOf_forall {E τ : Type} [TopologicalSpace E] [Finite τ] {P : Set E}
    {D : τ → Set E} (hD : ∀ t, ComplexMatrix2.IsRelativelyOpen P (D t)) :
    ComplexMatrix2.IsRelativelyOpen P {x | x ∈ P ∧ ∀ t, x ∈ D t} := by
  choose O hO he using hD
  refine ⟨⋂ t, O t, isOpen_iInter_of_finite hO, ?_⟩
  ext x
  rw [mem_inter_iff, mem_iInter]
  constructor
  · rintro ⟨hx, h⟩
    exact ⟨fun t => by
      have := h t
      rw [he t] at this
      exact this.1, hx⟩
  · rintro ⟨h, hx⟩
    exact ⟨hx, fun t => by
      rw [he t]
      exact ⟨h t, hx⟩⟩
end Rules
section Points
open YangMills.Construction.Tower.DoubleBlockPolydisc
variable {σ : Type}
theorem image_asGroupFactors (O : Set (σ → ComplexMatrix2)) :
    asGroupFactors '' O = leftComponents ⁻¹' O := by
  ext p
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact hw
  · intro hp
    refine ⟨leftComponents p, hp, ?_⟩
    funext i
    rcases i with i | e
    · rfl
    · exact e.elim
theorem asGroupFactors_leftComponents (p : σ ⊕ Empty → ComplexMatrix2) :
    asGroupFactors (leftComponents p) = p := by apply _root_.YangMills.DeltaSharedProofs.p4358 <;> assumption
theorem continuous_asGroupFactors :
    Continuous (asGroupFactors : (σ → ComplexMatrix2) → σ ⊕ Empty → ComplexMatrix2) := by apply _root_.YangMills.SharedProofs.p11373 <;> assumption
theorem continuous_leftComponents :
    Continuous (leftComponents : (σ ⊕ Empty → ComplexMatrix2) → σ → ComplexMatrix2) :=
  continuous_pi fun _ => continuous_apply _
theorem asGroupFactors_mem_iff {w : σ → ComplexMatrix2} :
    asGroupFactors w ∈ GroupLieProduct σ Empty ↔ w ∈ unimodularPi σ :=
  ⟨fun h i => h (.inl i), fun h i => by
    rcases i with i | e
    · exact h i
    · exact e.elim⟩
theorem isRelativelyOpen_preimage_asGroupFactors {Wp : Set (σ ⊕ Empty → ComplexMatrix2)}
    (h : ComplexMatrix2.IsRelativelyOpen (GroupLieProduct σ Empty) Wp) :
    ComplexMatrix2.IsRelativelyOpen (unimodularPi σ) (asGroupFactors ⁻¹' Wp) := by
  obtain ⟨O, hO, rfl⟩ := h
  refine ⟨asGroupFactors ⁻¹' O, hO.preimage continuous_asGroupFactors, ?_⟩
  ext w
  simp only [mem_preimage, mem_inter_iff, asGroupFactors_mem_iff]
theorem isRelativelyOpen_preimage_leftComponents {O : Set (σ → ComplexMatrix2)}
    (h : ComplexMatrix2.IsRelativelyOpen (unimodularPi σ) O) :
    ComplexMatrix2.IsRelativelyOpen (GroupLieProduct σ Empty) (leftComponents ⁻¹' O) := by
  obtain ⟨O', hO, rfl⟩ := h
  refine ⟨leftComponents ⁻¹' O', hO.preimage continuous_leftComponents, ?_⟩
  ext p
  have : p ∈ GroupLieProduct σ Empty ↔ leftComponents p ∈ unimodularPi σ := by
    conv_lhs => rw [← asGroupFactors_leftComponents p]
    exact asGroupFactors_mem_iff
  simp only [mem_preimage, mem_inter_iff, this]
end Points
open YangMills.Construction.Tower.BondSetFields YangMills.Construction.Tower.DoubleBlockPolydisc
structure MeanData where
  Link : ℕ → Type
  opp : ∀ {i : ℕ}, Link i → Link i
  pos : ∀ {i : ℕ}, Link i → Prop
  block : ∀ {i : ℕ}, Link (i + 1) → Set (Link i)
  mean : ∀ {i : ℕ}, (Link i → ComplexMatrix2) → Link (i + 1) → ComplexMatrix2
  extend : ∀ {i : ℕ} (c : Link (i + 1)),
    (positivePart (@pos i) (block c) → ComplexMatrix2) → Link i → ComplexMatrix2
  radius : ℝ
namespace MeanData
variable (D : MeanData)
def polydisc {i : ℕ} (c : D.Link (i + 1)) : Set (D.Link i → ComplexMatrix2) :=
  {V | ((∀ b ∈ D.block c, V b ∈ PeriodicLattice.complexGaugeGroup) ∧
      ∀ b ∈ D.block c, V (D.opp b) = (V b)⁻¹) ∧
    ∀ b ∈ D.block c, ComplexMatrix2.operatorNorm (V b - 1) < D.radius}
def meanAt {i : ℕ} (w : D.Link i → Option ComplexMatrix2) (c : D.Link (i + 1)) :
    Option ComplexMatrix2 :=
  open Classical in
  if (∀ b ∈ D.block c, (w b).isSome) ∧ valuesOrOne w ∈ D.polydisc c then
    some (D.mean (valuesOrOne w) c)
  else none
def levelwise (W : D.Link 0 → ComplexMatrix2) : (i : ℕ) → D.Link i → Option ComplexMatrix2
  | 0 => fun c => some (W c)
  | i + 1 => fun c =>
    open Classical in
    if D.pos c then D.meanAt (levelwise W i) c
    else (D.meanAt (levelwise W i) (D.opp c)).map (·⁻¹)
def IsField {i : ℕ} (V : D.Link i → ComplexMatrix2) : Prop :=
  (∀ b, V b ∈ PeriodicLattice.complexGaugeGroup) ∧ ∀ b, V (D.opp b) = (V b)⁻¹
structure Admissible (k : ℕ) : Prop where
  opp_opp : ∀ {i : ℕ} (b : D.Link i), D.opp (D.opp b) = b
  xor_pos : ∀ i ≤ k, ∀ b : D.Link i, Xor (D.pos b) (D.pos (D.opp b))
  block_finite : ∀ i < k, ∀ c : D.Link (i + 1), D.pos c → (D.block c).Finite
  opp_mem : ∀ i < k, ∀ c : D.Link (i + 1), D.pos c → ∀ b ∈ D.block c, D.opp b ∈ D.block c
  exists_pos : ∀ i < k, ∀ c : D.Link (i + 1), D.pos c → ∃ b ∈ D.block c, D.pos b
  mean_mem : ∀ i < k, ∀ c : D.Link (i + 1), D.pos c → ∀ V ∈ D.polydisc c,
    D.mean V c ∈ PeriodicLattice.complexGaugeGroup
  holomorphic : ∀ i < k, ∀ c : D.Link (i + 1), D.pos c →
    ∃ _ : Fintype (positivePart (@D.pos i) (D.block c)),
      IsHolomorphicWithEntries (positiveImage (@D.pos i) (D.block c) (D.polydisc c)) fun v =>
        D.mean (D.extend c v) c
  mean_extend : ∀ i < k, ∀ c : D.Link (i + 1), D.pos c → ∀ V ∈ D.polydisc c,
    D.mean V c = D.mean (D.extend c fun b => V b.1) c
  eq_extend : ∀ i < k, ∀ c : D.Link (i + 1), D.pos c → ∀ V ∈ D.polydisc c, ∀ b ∈ D.block c,
    V b = D.extend c (fun b => V b.1) b
variable {D} {k : ℕ} (G : D.Admissible k)
theorem Admissible.pos_opp_of_not_pos (G : D.Admissible k) {i : ℕ} (hi : i ≤ k) {b : D.Link i}
    (h : ¬ D.pos b) : D.pos (D.opp b) := by
  rcases G.xor_pos i hi b with h' | h'
  · exact absurd h'.1 h
  · exact h'.1
theorem Admissible.not_pos_opp (G : D.Admissible k) {i : ℕ} (hi : i ≤ k) {b : D.Link i}
    (h : D.pos b) : ¬ D.pos (D.opp b) := by
  rcases G.xor_pos i hi b with h' | h'
  · exact h'.2
  · exact absurd h h'.2
theorem levelwise_succ_of_pos (W : D.Link 0 → ComplexMatrix2) {i : ℕ} {c : D.Link (i + 1)}
    (h : D.pos c) : D.levelwise W (i + 1) c = D.meanAt (D.levelwise W i) c := by
  simp only [levelwise, if_pos h]
theorem levelwise_succ_of_not_pos (W : D.Link 0 → ComplexMatrix2) {i : ℕ} {c : D.Link (i + 1)}
    (h : ¬ D.pos c) :
    D.levelwise W (i + 1) c = (D.meanAt (D.levelwise W i) (D.opp c)).map (·⁻¹) := by
  simp only [levelwise, if_neg h]
theorem meanAt_eq_some {i : ℕ} {w : D.Link i → Option ComplexMatrix2} {c : D.Link (i + 1)}
    {x : ComplexMatrix2} (h : D.meanAt w c = some x) :
    (∀ b ∈ D.block c, (w b).isSome) ∧ valuesOrOne w ∈ D.polydisc c ∧
      D.mean (valuesOrOne w) c = x := by
  unfold meanAt at h
  split_ifs at h with hc
  exact ⟨hc.1, hc.2, Option.some.inj h⟩
theorem meanAt_of {i : ℕ} {w : D.Link i → Option ComplexMatrix2} {c : D.Link (i + 1)}
    (h : ∀ b ∈ D.block c, (w b).isSome) (h' : valuesOrOne w ∈ D.polydisc c) :
    D.meanAt w c = some (D.mean (valuesOrOne w) c) := by
  unfold meanAt
  rw [if_pos ⟨h, h'⟩]
include G
theorem levelwise_mem {W : D.Link 0 → ComplexMatrix2} (hW : D.IsField W) :
    ∀ i ≤ k, ∀ (b : D.Link i) (x : ComplexMatrix2),
      D.levelwise W i b = some x → x ∈ PeriodicLattice.complexGaugeGroup := by
  intro i
  induction i with
  | zero =>
    intro _ b x h
    have : W b = x := Option.some.inj h
    exact this ▸ hW.1 b
  | succ i _ =>
    intro hi b x h
    have hik : i < k := hi
    by_cases hb : D.pos b
    · rw [levelwise_succ_of_pos W hb] at h
      obtain ⟨_, hp, he⟩ := meanAt_eq_some h
      exact he ▸ G.mean_mem i hik b hb _ hp
    · have hr := G.pos_opp_of_not_pos hi hb
      rw [levelwise_succ_of_not_pos W hb] at h
      obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.1 h
      obtain ⟨_, hp, he⟩ := meanAt_eq_some hy
      exact inv_mem_unitDeterminant (he ▸ G.mean_mem i hik _ hr _ hp)
theorem levelwise_opp {W : D.Link 0 → ComplexMatrix2} (hW : D.IsField W) :
    ∀ i ≤ k, ∀ (b : D.Link i) (x : ComplexMatrix2),
      D.levelwise W i b = some x → D.levelwise W i (D.opp b) = some x⁻¹ := by
  intro i
  cases i with
  | zero =>
    intro _ b x h
    have : W b = x := Option.some.inj h
    show some (W (D.opp b)) = _
    rw [hW.2 b, this]
  | succ i =>
    intro hi b x h
    by_cases hb : D.pos b
    · rw [levelwise_succ_of_not_pos W (G.not_pos_opp hi hb), G.opp_opp]
      rw [levelwise_succ_of_pos W hb] at h
      rw [h]
      rfl
    · have hr := G.pos_opp_of_not_pos hi hb
      rw [levelwise_succ_of_pos W hr]
      rw [levelwise_succ_of_not_pos W hb] at h
      obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.1 h
      have hmem : y ∈ PeriodicLattice.complexGaugeGroup := by
        obtain ⟨_, hp, he⟩ := meanAt_eq_some hy
        exact he ▸ G.mean_mem i hi _ hr _ hp
      rw [hy, inv_inv_of_mem_unitDeterminant hmem]
theorem levelwise_eq_of_sequence {j : ℕ} (hj : j ≤ k) {V : ∀ i : ℕ, D.Link i → ComplexMatrix2}
    (hconf : ∀ i ≤ j, D.IsField (V i))
    (hwithin : ∀ i < j, ∀ b, ComplexMatrix2.operatorNorm (V i b - 1) < D.radius)
    (hvalue : ∀ i < j, ∀ c : D.Link (i + 1), D.pos c → V (i + 1) c = D.mean (V i) c) :
    ∀ i ≤ j, ∀ c : D.Link i, D.levelwise (V 0) i c = some (V i c) := by
  intro i
  induction i with
  | zero => intro _ c; rfl
  | succ i ih =>
    intro hi c
    have hij : i < j := hi
    have hl : D.levelwise (V 0) i = fun b => some (V i b) := funext (ih hij.le)
    have hfv : valuesOrOne (D.levelwise (V 0) i) = V i := by
      rw [hl]
      rfl
    have hform : ∀ c' : D.Link (i + 1), D.pos c' →
        D.meanAt (D.levelwise (V 0) i) c' = some (V (i + 1) c') := by
      intro c' hc'
      have hp : valuesOrOne (D.levelwise (V 0) i) ∈ D.polydisc c' := by
        rw [hfv]
        exact ⟨⟨fun b _ => (hconf i hij.le).1 b, fun b _ => (hconf i hij.le).2 b⟩,
          fun b _ => hwithin i hij b⟩
      rw [meanAt_of (fun b _ => by rw [hl]; rfl) hp, hfv, hvalue i hij c' hc']
    by_cases hc : D.pos c
    · rw [levelwise_succ_of_pos _ hc, hform c hc]
    · have hik : i + 1 ≤ k := hi.trans hj
      rw [levelwise_succ_of_not_pos _ hc, hform _ (G.pos_opp_of_not_pos hik hc),
        (hconf (i + 1) hi).2 c]
      show some ((V (i + 1) c)⁻¹)⁻¹ = _
      rw [inv_inv_of_mem_unitDeterminant ((hconf (i + 1) hi).1 c)]
end MeanData
theorem finrank_traceless : Module.finrank ℂ ComplexMatrix2.traceless = 3 := by apply _root_.YangMills.SharedProofs.p8292 <;> assumption
def tracelessBasis : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless :=
  Module.finBasisOfFinrankEq ℂ _ finrank_traceless
theorem isOpen_operatorNorm_sub_one_lt {r : ℝ} :
    IsOpen {X : ComplexMatrix2 | ComplexMatrix2.operatorNorm (X - 1) < r} :=
  isOpen_lt (continuous_norm.comp (continuous_id.sub continuous_const)) continuous_const
namespace MeanData
variable {D : MeanData} {k : ℕ}
structure Representation (D : MeanData) (j : ℕ) (c : D.Link j) (U : D.Link 0 → ComplexMatrix2)
    (F : Finset (D.Link 0)) (O : Set (F → ComplexMatrix2))
    (f : (F → ComplexMatrix2) → ComplexMatrix2) : Prop where
  nonempty : F.Nonempty
  positive : ∀ b ∈ F, D.pos b
  isOpen : ComplexMatrix2.IsRelativelyOpen (unimodularPi F) O
  mem : (fun b : F => U b) ∈ O
  holomorphic : ∀ β : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless,
    IsHolomorphicToUnimodular β (asGroupFactors '' O) fun p => f fun b => p (.inl b)
  eq_some : ∀ W, D.IsField W → (fun b : F => W b) ∈ O →
    D.levelwise W j c = some (f fun b : F => W b)
def extendByOne (D : MeanData) (F : Finset (D.Link 0)) (w : F → ComplexMatrix2) (b : D.Link 0) :
    ComplexMatrix2 :=
  open Classical in
  if h : b ∈ F then w ⟨b, h⟩
  else if h' : D.opp b ∈ F then (w ⟨D.opp b, h'⟩)⁻¹
  else 1
theorem extendByOne_spec (G : D.Admissible k) {F : Finset (D.Link 0)} (hF : ∀ b ∈ F, D.pos b)
    {w : F → ComplexMatrix2} (hw : w ∈ unimodularPi F) :
    D.IsField (D.extendByOne F w) ∧ (fun b : F => D.extendByOne F w b) = w := by
  have h0 : (0 : ℕ) ≤ k := Nat.zero_le _
  have one_mem : (1 : ComplexMatrix2) ∈ PeriodicLattice.complexGaugeGroup := by
    show (1 : ComplexMatrix2).det = 1
    simp
  refine ⟨⟨fun b => ?_, fun b => ?_⟩, ?_⟩
  · unfold extendByOne
    split_ifs with h h'
    · exact hw _
    · exact inv_mem_unitDeterminant (hw _)
    · exact one_mem
  · by_cases h : b ∈ F
    · have hn : D.opp b ∉ F := fun h' => G.not_pos_opp h0 (hF b h) (hF _ h')
      have hr : D.opp (D.opp b) = b := G.opp_opp b
      simp only [extendByOne, dif_neg hn, dif_pos h]
      rw [dif_pos (by rw [hr]; exact h)]
      congr 2
      exact Subtype.ext hr
    · by_cases h' : D.opp b ∈ F
      · have hr : D.opp (D.opp b) = b := G.opp_opp b
        simp only [extendByOne, dif_pos h', dif_neg h]
        exact (inv_inv_of_mem_unitDeterminant (hw _)).symm
      · have hr : D.opp (D.opp b) = b := G.opp_opp b
        simp only [extendByOne, dif_neg h, dif_neg h']
        rw [dif_neg (by rw [hr]; exact h)]
        simp
  · funext b
    simp [extendByOne]
theorem Representation.opp (G : D.Admissible k)
    (hm : ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    {i : ℕ} (hi : i + 1 ≤ k) {c : D.Link (i + 1)} (hc : D.pos c) {U : D.Link 0 → ComplexMatrix2}
    {F : Finset (D.Link 0)} {O : Set (F → ComplexMatrix2)}
    {f : (F → ComplexMatrix2) → ComplexMatrix2}
    (H : ExpChartHolomorphy.ExpChartTheory)
    (w : D.Representation (i + 1) c U F O f) :
    D.Representation (i + 1) (D.opp c) U F O fun x => (f x)⁻¹ := by
  refine ⟨w.nonempty, w.positive, w.isOpen, w.mem, fun β => ?_, fun W hW hWO => ?_⟩
  · exact isHolomorphicToUnimodular_inv H hm β (w.holomorphic β)
  · rw [levelwise_succ_of_not_pos W (G.not_pos_opp hi hc), G.opp_opp,
      ← levelwise_succ_of_pos W hc, w.eq_some W hW hWO]
    rfl
theorem exists_representation_zero (G : D.Admissible k) (H : ExpChartHolomorphy.ExpChartTheory)
    (hm : ComplexCoordinates.PowerSeriesHolomorphy.Properties) (c : D.Link 0)
    {U : D.Link 0 → ComplexMatrix2} (hU : D.IsField U) :
    ∃ (F : Finset (D.Link 0)) (O : Set (F → ComplexMatrix2))
      (f : (F → ComplexMatrix2) → ComplexMatrix2), D.Representation 0 c U F O f := by
  classical
  have h0 : (0 : ℕ) ≤ k := Nat.zero_le _
  have key : ∀ c' : D.Link 0, D.pos c' →
      ∃ (F : Finset (D.Link 0)) (hc : c' ∈ F), F = {c'} ∧
        D.Representation 0 c' U F (unimodularPi F) fun w => w ⟨c', hc⟩ := by
    intro c' hc'
    refine ⟨{c'}, Finset.mem_singleton_self _, rfl,
      ⟨⟨c', Finset.mem_singleton_self _⟩, ?_, ?_, ?_, ?_, ?_⟩⟩
    · intro b hb
      rw [Finset.mem_singleton.1 hb]
      exact hc'
    · exact ⟨univ, isOpen_univ, by simp⟩
    · exact fun b => hU.1 b
    · intro β
      have hp : ComplexMatrix2.IsRelativelyOpen
          (GroupLieProduct ({c'} : Finset (D.Link 0)) Empty)
          (asGroupFactors '' unimodularPi _) := by
        rw [image_asGroupFactors]
        exact isRelativelyOpen_preimage_leftComponents ⟨univ, isOpen_univ, by simp⟩
      exact isHolomorphicToUnimodular_component H β hp ⟨c', Finset.mem_singleton_self _⟩
    · intro W _ _
      rfl
  by_cases hc : D.pos c
  · obtain ⟨F, hcF, _, w⟩ := key c hc
    exact ⟨F, _, _, w⟩
  · have hr := G.pos_opp_of_not_pos h0 hc
    obtain ⟨F, hcF, _, w⟩ := key _ hr
    refine ⟨F, _, fun x => (x ⟨D.opp c, hcF⟩)⁻¹, ⟨w.nonempty, w.positive, w.isOpen, w.mem,
      fun β => isHolomorphicToUnimodular_inv H hm β (w.holomorphic β), fun W hW _ => ?_⟩⟩
    show some (W c) = some (W (D.opp c))⁻¹
    rw [hW.2 c, inv_inv_of_mem_unitDeterminant (hW.1 c)]
theorem exists_representation_succ (G : D.Admissible k) (H : ExpChartHolomorphy.ExpChartTheory)
    {i : ℕ} (hi : i < k) {c : D.Link (i + 1)} (hc : D.pos c) {U : D.Link 0 → ComplexMatrix2}
    (hU : D.IsField U) (hform : (D.meanAt (D.levelwise U i) c).isSome)
    (IH : ∀ b ∈ D.block c, ∃ (F : Finset (D.Link 0)) (O : Set (F → ComplexMatrix2))
      (f : (F → ComplexMatrix2) → ComplexMatrix2), D.Representation i b U F O f) :
    ∃ (F : Finset (D.Link 0)) (O : Set (F → ComplexMatrix2))
      (f : (F → ComplexMatrix2) → ComplexMatrix2), D.Representation (i + 1) c U F O f := by
  classical
  have IH' : ∀ b : D.Link i, ∃ (F : Finset (D.Link 0)) (O : Set (F → ComplexMatrix2))
      (f : (F → ComplexMatrix2) → ComplexMatrix2), b ∈ D.block c → D.Representation i b U F O f := by
    intro b
    by_cases hb : b ∈ D.block c
    · obtain ⟨F, O, f, w⟩ := IH b hb
      exact ⟨F, O, f, fun _ => w⟩
    · exact ⟨∅, ∅, fun _ => 1, fun h => absurd h hb⟩
  choose Fb Ob fb hw using IH'
  obtain ⟨x₀, hx₀⟩ := Option.isSome_iff_exists.1 hform
  obtain ⟨hsome, hpolyU, _⟩ := meanAt_eq_some hx₀
  have hfin : (D.block c).Finite := G.block_finite i hi c hc
  let Fall : Finset (D.Link 0) := hfin.toFinset.biUnion Fb
  have hsub : ∀ b ∈ D.block c, ∀ x ∈ Fb b, x ∈ Fall := fun b hb x hx =>
    Finset.mem_biUnion.2 ⟨b, hfin.mem_toFinset.2 hb, hx⟩
  have hFallPos : ∀ x ∈ Fall, D.pos x := by
    intro x hx
    obtain ⟨b, hb, hxb⟩ := Finset.mem_biUnion.1 hx
    exact (hw b (hfin.mem_toFinset.1 hb)).positive x hxb
  let res : ∀ b, (Fall → ComplexMatrix2) → Fb b → ComplexMatrix2 :=
    fun b w x => D.extendByOne Fall w x.1
  have res_eq : ∀ b ∈ D.block c, ∀ (w : Fall → ComplexMatrix2) (x : Fb b) (hx : x.1 ∈ Fall),
      res b w x = w ⟨x.1, hx⟩ := by
    intro b _ w x hx
    simp only [res, extendByOne, dif_pos hx]
  have res_of : ∀ b ∈ D.block c, ∀ W : D.Link 0 → ComplexMatrix2,
      res b (fun x : Fall => W x) = fun x : Fb b => W x := by
    intro b hb W
    funext x
    rw [res_eq b hb _ x (hsub b hb x.1 x.2)]
  have hprodopen : ComplexMatrix2.IsRelativelyOpen (GroupLieProduct Fall Empty)
      (GroupLieProduct Fall Empty) :=
    ⟨univ, isOpen_univ, by simp⟩
  let R : ∀ b, (Fall ⊕ Empty → ComplexMatrix2) → (Fb b ⊕ Empty → ComplexMatrix2) :=
    fun b p => asGroupFactors (res b (leftComponents p))
  let g : ∀ b, (Fall ⊕ Empty → ComplexMatrix2) → ComplexMatrix2 :=
    fun b p => fb b (res b (leftComponents p))
  let A : ∀ b, Set (Fall ⊕ Empty → ComplexMatrix2) :=
    fun b => GroupLieProduct Fall Empty ∩ R b ⁻¹' (leftComponents ⁻¹' Ob b)
  have hR : ∀ β, ∀ b ∈ D.block c,
      IsHolomorphicToProduct β (GroupLieProduct Fall Empty) (R b) := by
    intro β b hb
    refine ⟨hprodopen, fun x => ?_, fun e => e.elim⟩
    refine isHolomorphicToUnimodular_congr β
      (isHolomorphicToUnimodular_component H β hprodopen ⟨x.1, hsub b hb x.1 x.2⟩) fun p _ => ?_
    exact (res_eq b hb (leftComponents p) x (hsub b hb x.1 x.2)).symm
  have hg : ∀ β, ∀ b ∈ D.block c, IsHolomorphicToUnimodular β (A b) (g b) := by
    intro β b hb
    have h := isHolomorphicToUnimodular_comp H β (hR β b hb) ((hw b hb).holomorphic β)
    rw [image_asGroupFactors] at h
    exact h
  have hgcont : ∀ b ∈ D.block c, ContinuousOn (g b) (A b) := fun b hb =>
    (hg tracelessBasis b hb).2.2.1
  have hAopen : ∀ b ∈ D.block c, ComplexMatrix2.IsRelativelyOpen (GroupLieProduct Fall Empty) (A b) :=
    fun b hb => (hg tracelessBasis b hb).1
  let Wb : (D.block c) → Set (Fall ⊕ Empty → ComplexMatrix2) :=
    fun b => {p | p ∈ A b.1 ∧ ComplexMatrix2.operatorNorm (g b.1 p - 1) < D.radius}
  have hWb : ∀ b, ComplexMatrix2.IsRelativelyOpen (GroupLieProduct Fall Empty) (Wb b) := by
    intro b
    obtain ⟨Oa, hOa, hAe⟩ := hAopen b.1 b.2
    obtain ⟨u, hu, hue⟩ := continuousOn_iff'.1 (hgcont b.1 b.2)
      {X | ComplexMatrix2.operatorNorm (X - 1) < D.radius} isOpen_operatorNorm_sub_one_lt
    refine ⟨u ∩ Oa, hu.inter hOa, ?_⟩
    ext p
    constructor
    · rintro ⟨hpA, hpn⟩
      have h1 : p ∈ u ∩ A b.1 := by
        rw [← hue]
        exact ⟨hpn, hpA⟩
      have h2 : p ∈ Oa ∩ GroupLieProduct Fall Empty := by
        rw [← hAe]
        exact hpA
      exact ⟨⟨h1.1, h2.1⟩, h2.2⟩
    · rintro ⟨⟨hpu, hpO⟩, hpP⟩
      have hpA : p ∈ A b.1 := by
        rw [hAe]
        exact ⟨hpO, hpP⟩
      have h1 : p ∈ g b.1 ⁻¹' {X | ComplexMatrix2.operatorNorm (X - 1) < D.radius} ∩ A b.1 := by
        rw [hue]
        exact ⟨hpu, hpA⟩
      exact ⟨hpA, h1.1⟩
  let Wall : Set (Fall ⊕ Empty → ComplexMatrix2) :=
    {p | p ∈ GroupLieProduct Fall Empty ∧ ∀ b, p ∈ Wb b}
  have : Finite (D.block c) := hfin.to_subtype
  have hWall : ComplexMatrix2.IsRelativelyOpen (GroupLieProduct Fall Empty) Wall :=
    isRelativelyOpen_setOf_forall hWb
  let O : Set (Fall → ComplexMatrix2) := asGroupFactors ⁻¹' Wall
  have himg : asGroupFactors '' O = Wall := by
    rw [image_asGroupFactors]
    ext p
    show asGroupFactors (leftComponents p) ∈ Wall ↔ _
    rw [asGroupFactors_leftComponents]
  have key : ∀ W, D.IsField W → (fun x : Fall => W x) ∈ O →
      (∀ b ∈ D.block c, D.levelwise W i b = some (fb b (res b fun x : Fall => W x))) ∧
        valuesOrOne (D.levelwise W i) ∈ D.polydisc c := by
    intro W hW hO
    have h1 : ∀ b ∈ D.block c, D.levelwise W i b = some (fb b (res b fun x : Fall => W x)) := by
      intro b hb
      have hm' : res b (fun x : Fall => W x) ∈ Ob b := (hO.2 ⟨b, hb⟩).1.2
      rw [res_of b hb W] at hm' ⊢
      exact (hw b hb).eq_some W hW hm'
    have hfv : ∀ b ∈ D.block c,
        valuesOrOne (D.levelwise W i) b = fb b (res b fun x : Fall => W x) := by
      intro b hb
      simp only [valuesOrOne, h1 b hb, Option.getD_some]
    refine ⟨h1, ⟨fun b hb => ?_, fun b hb => ?_⟩, fun b hb => ?_⟩
    · rw [hfv b hb]
      exact levelwise_mem G hW i hi.le b _ (h1 b hb)
    · have hr := levelwise_opp G hW i hi.le b _ (h1 b hb)
      rw [hfv b hb]
      simp only [valuesOrOne, hr, Option.getD_some]
    · rw [hfv b hb]
      exact (hO.2 ⟨b, hb⟩).2
  refine ⟨Fall, O, fun w => D.mean (D.extend c fun b => fb b.1 (res b.1 w)) c, ?_, hFallPos,
    isRelativelyOpen_preimage_asGroupFactors hWall, ?_, fun β => ?_, fun W hW hO => ?_⟩
  · obtain ⟨b, hb, _⟩ := G.exists_pos i hi c hc
    obtain ⟨x, hx⟩ := (hw b hb).nonempty
    exact ⟨x, hsub b hb x hx⟩
  · have hp : asGroupFactors (fun x : Fall => U x) ∈ GroupLieProduct Fall Empty :=
      asGroupFactors_mem_iff.2 fun x => hU.1 x
    refine ⟨hp, fun b => ⟨⟨hp, ?_⟩, ?_⟩⟩
    · show res b.1 (fun x : Fall => U x) ∈ Ob b.1
      rw [res_of b.1 b.2 U]
      exact (hw b.1 b.2).mem
    · show ComplexMatrix2.operatorNorm (fb b.1 (res b.1 fun x : Fall => U x) - 1) < D.radius
      rw [res_of b.1 b.2 U]
      have hv := (hw b.1 b.2).eq_some U hU (hw b.1 b.2).mem
      have hn := hpolyU.2 b.1 b.2
      simpa only [valuesOrOne, hv, Option.getD_some] using hn
  · obtain ⟨inst, hΦ⟩ := G.holomorphic i hi c hc
    let _ := inst
    let Ψ : (Fall ⊕ Empty → ComplexMatrix2) →
        (positivePart (@D.pos i) (D.block c)) ⊕ Empty → ComplexMatrix2 :=
      fun p => asGroupFactors fun b => g b.1 p
    have hΨ : IsHolomorphicToProduct β Wall Ψ :=
      ⟨hWall, fun b => isHolomorphicToUnimodular_mono H β (hg β b.1 b.2.1) hWall
        fun p hp => (hp.2 ⟨b.1, b.2.1⟩).1, fun e => e.elim⟩
    have h := isHolomorphicToUnimodular_comp H β hΨ (hΦ.toUnimodular β)
    have hs : Wall ⊆ Ψ ⁻¹' (leftComponents ⁻¹'
        positiveImage (@D.pos i) (D.block c) (D.polydisc c)) := by
      intro p hp
      have hwp : leftComponents p ∈ unimodularPi Fall := by
        intro x
        exact hp.1 (.inl x)
      obtain ⟨hWc, hWe⟩ := extendByOne_spec G hFallPos hwp
      have hO : (fun x : Fall => D.extendByOne Fall (leftComponents p) x) ∈ O := by
        rw [hWe]
        show asGroupFactors (leftComponents p) ∈ Wall
        rw [asGroupFactors_leftComponents]
        exact hp
      obtain ⟨h1, h2⟩ := key _ hWc hO
      refine ⟨_, ⟨_, h2, rfl⟩, ?_⟩
      funext b
      show valuesOrOne (D.levelwise (D.extendByOne Fall (leftComponents p)) i) b.1 = g b.1 p
      simp only [valuesOrOne, h1 b.1 b.2.1, Option.getD_some, hWe]
      rfl
    rw [inter_eq_left.2 hs] at h
    rw [himg]
    exact isHolomorphicToUnimodular_congr β h fun p _ => rfl
  · obtain ⟨h1, h2⟩ := key W hW hO
    rw [levelwise_succ_of_pos W hc, meanAt_of (fun b hb => by rw [h1 b hb]; rfl) h2,
      G.mean_extend i hi c hc _ h2]
    congr 3
    funext b
    simp only [valuesOrOne, h1 b.1 b.2.1, Option.getD_some]
theorem exists_representation (G : D.Admissible k) (H : ExpChartHolomorphy.ExpChartTheory)
    (hm : ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    {U : D.Link 0 → ComplexMatrix2} (hU : D.IsField U) :
    ∀ j ≤ k, ∀ c : D.Link j, (D.levelwise U j c).isSome →
      ∃ (F : Finset (D.Link 0)) (O : Set (F → ComplexMatrix2))
        (f : (F → ComplexMatrix2) → ComplexMatrix2), D.Representation j c U F O f := by
  intro j
  induction j with
  | zero => exact fun _ c _ => exists_representation_zero G H hm c hU
  | succ i ih =>
    intro hi c hs
    have hik : i < k := hi
    have step : ∀ c' : D.Link (i + 1), D.pos c' → (D.meanAt (D.levelwise U i) c').isSome →
        ∃ (F : Finset (D.Link 0)) (O : Set (F → ComplexMatrix2))
          (f : (F → ComplexMatrix2) → ComplexMatrix2), D.Representation (i + 1) c' U F O f := by
      intro c' hc' hs'
      obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 hs'
      exact exists_representation_succ G H hik hc' hU hs' fun b hb =>
        ih hik.le b ((meanAt_eq_some hx).1 b hb)
    by_cases hc : D.pos c
    · rw [levelwise_succ_of_pos U hc] at hs
      exact step c hc hs
    · have hr := G.pos_opp_of_not_pos hi hc
      rw [levelwise_succ_of_not_pos U hc, Option.isSome_map] at hs
      obtain ⟨F, O, f, w⟩ := step _ hr hs
      have := w.opp G hm hi hr H
      rw [G.opp_opp] at this
      exact ⟨F, O, _, this⟩
end MeanData
theorem MeanData.polydisc_congr {D : MeanData} {i : ℕ} {c : D.Link (i + 1)}
    (hr : ∀ b ∈ D.block c, D.opp b ∈ D.block c)
    {V V' : D.Link i → ComplexMatrix2} (hV : V ∈ D.polydisc c) (he : ∀ b ∈ D.block c, V b = V' b) :
    V' ∈ D.polydisc c := by
  refine ⟨⟨fun b hb => he b hb ▸ hV.1.1 b hb, fun b hb => ?_⟩, fun b hb => he b hb ▸ hV.2 b hb⟩
  rw [← he _ (hr b hb), ← he b hb]
  exact hV.1.2 b hb
section FiniteSide
def periodicData (L n k : ℕ) : MeanData where
  Link := fun i => Edge L n k i
  opp := fun b => b.opposite
  pos := fun b => b.IsPositivelyOriented
  block := fun {i} c => (PeriodicLattice.bondsInDoubleBlock c : Set (Edge L n k i))
  mean := fun V c => PeriodicLattice.complexBlockAverage V c
  extend := fun {_} c v => DoubleBlockPolydisc.fieldOfValues c v
  radius := polydiscRadius L
variable {L n k : ℕ}
theorem periodicData_levelwise (W : Edge L n k 0 → ComplexMatrix2) :
    ∀ i, (periodicData L n k).levelwise W i = levelwiseMean W i
  | 0 => rfl
  | i + 1 => by
    have ih := periodicData_levelwise W i
    funext c
    simp only [MeanData.levelwise, levelwiseMean, ih]
    rfl
theorem periodicData_admissible (hE : PeriodicLattice.BondEndpointsOrientation.Statement)
    (hP : DoubleBlockPolydisc.PolydiscsHold)
    (hS : SmoothingNearIdentity)
    (hV : ComplexMeanLiesInComplexGaugeGroup)
    (hR : PeriodicLattice.ComplexAverageIsLocal)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hk : 1 ≤ k) :
    (periodicData L n k).Admissible k := by
  have hxor : ∀ i ≤ k, ∀ b : Edge L n k i, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented :=
    fun i hi b => ((hE ⟨L, hL, ⟨k, hk⟩, ⟨n, hn⟩⟩ i hi).2.2.2 b).2.2.2.2.2
  have hpoly : ∀ i < k, ∀ c : Edge L n k (i + 1), c.IsPositivelyOriented →
      FiniteOpenPolydisc PeriodicLattice.Bond.opposite PeriodicLattice.Bond.IsPositivelyOriented
        PeriodicLattice.IsGaugeField (doubleBlockBonds c)
        (nearIdentityPolydisc (polydiscRadius L) c) :=
    fun i hi c hc => ((hP L hL k i hi).1 n hn c hc).finite_open
  have hagree : ∀ i < k, ∀ c : Edge L n k (i + 1), c.IsPositivelyOriented →
      ∀ V : Edge L n k i → ComplexMatrix2, V ∈ (periodicData L n k).polydisc (i := i) c →
      ∀ b ∈ (PeriodicLattice.bondsInDoubleBlock c : Set (Edge L n k i)),
        V b = DoubleBlockPolydisc.fieldOfValues c (fun b => V b.1) b := by
    intro i hi c hc V hVp b hb
    unfold DoubleBlockPolydisc.fieldOfValues PeriodicLattice.extendFromPositive
    by_cases hp : b.IsPositivelyOriented
    · rw [dif_pos (⟨hb, hp⟩ : b ∈ doubleBlockBonds c ∧ b.IsPositivelyOriented)]
    · have hrp : b.opposite.IsPositivelyOriented := by
        rcases hxor i hi.le b with h | h
        · exact absurd h.1 hp
        · exact h.1
      have hrb : b.opposite ∈ doubleBlockBonds c :=
        (hpoly i hi c hc).opposite_mem b hb
      rw [dif_neg (fun h : b ∈ doubleBlockBonds c ∧ b.IsPositivelyOriented => hp h.2),
        dif_pos (⟨hrb, hrp⟩ : b.opposite ∈ doubleBlockBonds c ∧ b.opposite.IsPositivelyOriented)]
      have e : (V b.opposite)⁻¹ = ((V b)⁻¹)⁻¹ := congrArg (·⁻¹) (hVp.1.2 b hb)
      exact (e.trans (inv_inv_of_mem_unitDeterminant (hVp.1.1 b hb))).symm
  refine ⟨fun b => rfl, hxor, fun i hi c hc => (hpoly i hi c hc).finite,
    fun i hi c hc => (hpoly i hi c hc).opposite_mem, ?_, ?_,
    fun i hi c hc => ((hP L hL k i hi).1 n hn c hc).holomorphic_smoothing, ?_, hagree⟩
  · intro i hi c hc
    obtain ⟨b, hb⟩ := (hpoly i hi c hc).positive_nonempty
    exact ⟨b, hb.1, hb.2⟩
  · intro i hi c hc V hVp
    have hsub := ((hS.1 L hL).2.2.periodic n k i hn hi c hc).subset_complexDomain
    exact ((hV.2 L k (i + 1) hL (by omega) hi).1 n hn c V hc (hsub hVp)).2
  · intro i hi (c : Edge L n k (i + 1)) (hc : c.IsPositivelyOriented)
      (V : Edge L n k i → ComplexMatrix2) hVp
    show PeriodicLattice.complexBlockAverage V c = PeriodicLattice.complexBlockAverage _ c
    unfold PeriodicLattice.complexBlockAverage
    simp only [if_pos hc]
    exact (hR L n k i hL.1 hL.2 hn hi c hc).average_eq _ _ (hagree i hi c hc V hVp)
end FiniteSide
namespace Unbounded
open YangMills.Construction.Tower.FullSpace
def unboundedData (L k : ℕ) : MeanData where
  Link := fun i => FullSpace.Edge L k i
  opp := fun b => b.opposite
  pos := fun b => b.IsPositivelyOriented
  block := fun {i} c => doubleCubeLinks L (meshAt L k i) c
  mean := fun {_} V c => complexSmoothing L V c
  extend := fun {i} c v => DoubleBlockPolydisc.Infinite.fieldOfValues L k i c v
  radius := polydiscRadius L
variable {L k : ℕ}
theorem unboundedData_levelwise (W : FullSpace.Edge L k 0 → ComplexMatrix2) :
    ∀ i, (unboundedData L k).levelwise W i = levelwiseMean W i
  | 0 => rfl
  | i + 1 => by
    have ih := unboundedData_levelwise W i
    funext c
    simp only [MeanData.levelwise, levelwiseMean, ih]
    rfl
theorem xor_isPositivelyOriented_opposite {a : ℝ} (ha : 0 < a) (b : InfiniteLattice.Link a) :
    Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented := by
  have key : ∀ μ ν, InfiniteLattice.axisStep a μ ≠ -InfiniteLattice.axisStep a ν := by
    intro μ ν h
    have h1 := congrArg
      (fun x : InfiniteLattice.LatticePoint a => (x : InfiniteLattice.AmbientSpace) μ) h
    by_cases e : μ = ν
    · subst e
      simp [InfiniteLattice.axisStep] at h1
      linarith
    · simp [InfiniteLattice.axisStep, Pi.single_eq_of_ne e] at h1
      linarith
  obtain ⟨μ, h | h⟩ := b.isAdjacent
  · refine Or.inl ⟨⟨μ, h⟩, ?_⟩
    rintro ⟨ν, h'⟩
    have h'' : b.initial - b.terminal = InfiniteLattice.axisStep a ν := h'
    apply key μ ν
    rw [← h, ← h'']
    abel
  · refine Or.inr ⟨⟨μ, ?_⟩, ?_⟩
    · show b.initial - b.terminal = InfiniteLattice.axisStep a μ
      rw [← neg_sub, h, neg_neg]
    · rintro ⟨ν, h'⟩
      apply key ν μ
      rw [← h', h]
theorem meshAt_pos (hL : Conventions.IsAdmissibleBlockingFactor L) (i : ℕ) :
    0 < meshAt L k i := by
  have : (0 : ℝ) < L := by
    have := hL.2
    exact_mod_cast (by omega : 0 < L)
  exact zpow_pos this _
theorem unboundedData_admissible (hP : DoubleBlockPolydisc.PolydiscsHold)
    (hS : SmoothingNearIdentity)
    (hV : ComplexMeanLiesInComplexGaugeGroup)
    (hQ : SublatticesSymmetriesScalingsAndProjections.Statement)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hk : 1 ≤ k) :
    (unboundedData L k).Admissible k := by
  have hL0 : 0 < L := by
    have := hL.2
    omega
  have hxor : ∀ i ≤ k, ∀ b : FullSpace.Edge L k i,
      Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented :=
    fun i _ b => xor_isPositivelyOriented_opposite (meshAt_pos hL i) b
  have hpoly : ∀ i < k, ∀ c : FullSpace.Edge L k (i + 1), c.IsPositivelyOriented →
      FiniteOpenPolydisc InfiniteLattice.Link.opposite
        InfiniteLattice.Link.IsPositivelyOriented Tower.FullSpace.IsFieldOn
        (DoubleBlockPolydisc.Infinite.doubleBlockBonds L k i c)
        (Tower.FullSpace.nearIdentityPolydisc L k i (polydiscRadius L) c) :=
    fun i hi c hc => ((hP L hL k i hi).2 c hc).finite_open
  have hserve := fun i (hi : i < k) (c : FullSpace.Edge L k (i + 1))
      (hc : c.IsPositivelyOriented) =>
    (hS.1 L hL).2.2.fullSpace k i hi c hc
  have hagree : ∀ i < k, ∀ c : FullSpace.Edge L k (i + 1), c.IsPositivelyOriented →
      ∀ V ∈ (unboundedData L k).polydisc c, ∀ b ∈ doubleCubeLinks L (meshAt L k i) c,
        V b = DoubleBlockPolydisc.Infinite.fieldOfValues L k i c (fun b => V b.1) b := by
    intro i hi c hc (V : FullSpace.Edge L k i → ComplexMatrix2) hVp b hb
    unfold DoubleBlockPolydisc.Infinite.fieldOfValues Tower.FullSpace.extendFromPositive
    by_cases hp : b.IsPositivelyOriented
    · rw [dif_pos (⟨hb, hp⟩ : b ∈ DoubleBlockPolydisc.Infinite.doubleBlockBonds L k i c ∧
        b.IsPositivelyOriented)]
    · have hrp : b.opposite.IsPositivelyOriented := by
        rcases hxor i hi.le b with h | h
        · exact absurd h.1 hp
        · exact h.1
      have hrb : b.opposite ∈ DoubleBlockPolydisc.Infinite.doubleBlockBonds L k i c :=
        (hpoly i hi c hc).opposite_mem b hb
      rw [dif_neg (fun h : b ∈ DoubleBlockPolydisc.Infinite.doubleBlockBonds L k i c ∧
          b.IsPositivelyOriented => hp h.2),
        dif_pos (⟨hrb, hrp⟩ : b.opposite ∈ DoubleBlockPolydisc.Infinite.doubleBlockBonds L k i c ∧
          b.opposite.IsPositivelyOriented)]
      have e : (V b.opposite)⁻¹ = ((V b)⁻¹)⁻¹ := congrArg (·⁻¹) (hVp.1.2 b hb)
      exact (e.trans (inv_inv_of_mem_unitDeterminant (hVp.1.1 b hb))).symm
  refine ⟨fun b => rfl, hxor, fun i hi c hc => (hpoly i hi c hc).finite,
    fun i hi c hc => (hpoly i hi c hc).opposite_mem, ?_, ?_,
    fun i hi c hc => ((hP L hL k i hi).2 c hc).holomorphic_smoothing, ?_, hagree⟩
  · intro i hi c hc
    obtain ⟨b, hb⟩ := (hpoly i hi c hc).positive_nonempty
    exact ⟨b, hb.1, hb.2⟩
  · intro i hi c hc V hVp
    exact ((hV.2 L k (i + 1) hL (by omega) hi).2 c V hc
      ((hserve i hi c hc).subset_complexDomain hVp)).2
  · intro i hi c hc V hVp
    have hVp' := MeanData.polydisc_congr (D := unboundedData L k)
      ((hpoly i hi c hc).opposite_mem) hVp (hagree i hi c hc V hVp)
    have hQ' := ((hQ L hL0 hL k).2.2.2.2.2.2 hk 1 one_pos).2 i hi c hc
    have e1 := hQ'.complexSmoothing_eq V ((hserve i hi c hc).subset_complexDomain hVp)
    have e2 := hQ'.complexSmoothing_eq _ ((hserve i hi c hc).subset_complexDomain hVp')
    refine e1.trans (Eq.trans ?_ e2.symm)
    congr 1
    funext x
    unfold Tower.FullSpace.projField
    split_ifs with h
    · exact hagree i hi c hc V hVp _ h.choose_spec.1
    · rfl
end Unbounded
namespace MeanData
variable {D : MeanData} {k : ℕ}
def twist (D : MeanData) {i : ℕ} (A U : D.Link i → ComplexMatrix2) (b : D.Link i) :
    ComplexMatrix2 :=
  open Classical in
  if D.pos b then ComplexMatrix2.matExp (Complex.I • A b) * U b
  else (ComplexMatrix2.matExp (Complex.I • A (D.opp b)) * U (D.opp b))⁻¹
def HasLeftCurves (D : MeanData) {i : ℕ} (U B : D.Link i → ComplexMatrix2) : Prop :=
  ∀ b, D.pos b →
    (∀ t : ℂ, ComplexMatrix2.matExp (Complex.I • (t • B) b) * U b ∈
      PeriodicLattice.complexGaugeGroup) ∧
    ContinuousAt (fun t : ℂ => ComplexMatrix2.matExp (Complex.I • (t • B) b) * U b) 0
theorem isField_twist (G : D.Admissible k) {i : ℕ} (hi : i ≤ k) {U B : D.Link i → ComplexMatrix2}
    (hleft : D.HasLeftCurves U B) (t : ℂ) : D.IsField (D.twist (t • B) U) := by
  classical
  have hmem : ∀ b, D.twist (t • B) U b ∈ PeriodicLattice.complexGaugeGroup := by
    intro b
    by_cases hb : D.pos b
    · simp only [twist, if_pos hb]
      exact (hleft b hb).1 t
    · simp only [twist, if_neg hb]
      exact inv_mem_unitDeterminant ((hleft _ (G.pos_opp_of_not_pos hi hb)).1 t)
  refine ⟨hmem, fun b => ?_⟩
  by_cases hb : D.pos b
  · have hn := G.not_pos_opp hi hb
    simp only [twist, if_neg hn, if_pos hb, G.opp_opp]
  · have hr := G.pos_opp_of_not_pos hi hb
    simp only [twist, if_pos hr, if_neg hb]
    exact (inv_inv_of_mem_unitDeterminant ((hleft _ hr).1 t)).symm
theorem inv_eq_adjugate_of_mem {X : ComplexMatrix2} (h : X ∈ ComplexMatrix2.unitDeterminant) :
    X⁻¹ = X.adjugate := by
  have e : X.det = 1 := h
  rw [Matrix.inv_def, e]
  simp
theorem tendsto_twist (G : D.Admissible k) {i : ℕ} (hi : i ≤ k) {U B : D.Link i → ComplexMatrix2}
    (hU : D.IsField U) (hleft : D.HasLeftCurves U B) :
    Tendsto (fun t : ℂ => D.twist (t • B) U) (𝓝 0) (𝓝 U) := by
  classical
  have hzero : ∀ b, ComplexMatrix2.matExp (Complex.I • ((0 : ℂ) • B) b) * U b = U b := by
    intro b
    simp [NormedSpace.exp_zero]
  refine tendsto_pi_nhds.2 fun b => ?_
  by_cases hb : D.pos b
  · have h := (hleft b hb).2.tendsto
    rw [hzero] at h
    refine h.congr fun t => ?_
    simp only [twist, if_pos hb]
  · have hr := G.pos_opp_of_not_pos hi hb
    have h := (hleft _ hr).2.tendsto
    rw [hzero] at h
    have h2 : Tendsto (fun t : ℂ =>
        (ComplexMatrix2.matExp (Complex.I • (t • B) (D.opp b)) * U (D.opp b)).adjugate)
        (𝓝 0) (𝓝 (U (D.opp b)).adjugate) :=
      (Continuous.matrix_adjugate continuous_id).continuousAt.tendsto.comp h
    have e0 : (U (D.opp b)).adjugate = U b := by
      rw [← inv_eq_adjugate_of_mem (hU.1 _), hU.2 b]
      exact inv_inv_of_mem_unitDeterminant (hU.1 b)
    rw [e0] at h2
    refine h2.congr fun t => ?_
    simp only [twist, if_neg hb]
    exact (inv_eq_adjugate_of_mem ((hleft _ hr).1 t)).symm
theorem Representation.eventually_along (G : D.Admissible k) {j : ℕ} {c : D.Link j}
    {U : D.Link 0 → ComplexMatrix2} {F : Finset (D.Link 0)} {O : Set (F → ComplexMatrix2)}
    {f : (F → ComplexMatrix2) → ComplexMatrix2}
    (w : D.Representation j c U F O f) {B : D.Link 0 → ComplexMatrix2}
    (hleft : D.HasLeftCurves U B) :
    ∀ᶠ t : ℂ in 𝓝 0,
      (fun b : F => ComplexMatrix2.matExp (Complex.I • (t • B) b.1) * U b.1) ∈ O ∧
      D.levelwise (D.twist (t • B) U) j c =
        some (f fun b : F => ComplexMatrix2.matExp (Complex.I • (t • B) b.1) * U b.1) := by
  classical
  have h0 : (0 : ℕ) ≤ k := Nat.zero_le _
  have hvals : ∀ t : ℂ, (fun b : F => D.twist (t • B) U b.1) =
      fun b : F => ComplexMatrix2.matExp (Complex.I • (t • B) b.1) * U b.1 := by
    intro t
    funext b
    simp only [twist, if_pos (w.positive b.1 b.2)]
  have hconf : ∀ t : ℂ, D.IsField (D.twist (t • B) U) := fun t => isField_twist G h0 hleft t
  have hcont : ContinuousAt
      (fun t : ℂ => fun b : F => ComplexMatrix2.matExp (Complex.I • (t • B) b.1) * U b.1) 0 :=
    continuousAt_pi.2 fun b => (hleft b.1 (w.positive b.1 b.2)).2
  have hzero : (fun b : F => ComplexMatrix2.matExp (Complex.I • ((0 : ℂ) • B) b.1) * U b.1) =
      fun b : F => U b.1 := by
    funext b
    simp [NormedSpace.exp_zero]
  obtain ⟨O', hO', he⟩ := w.isOpen
  have hm : (fun b : F => U b.1) ∈ O' := by
    have := w.mem
    rw [he] at this
    exact this.1
  have hev : ∀ᶠ t : ℂ in 𝓝 0,
      (fun b : F => ComplexMatrix2.matExp (Complex.I • (t • B) b.1) * U b.1) ∈ O' :=
    hcont (by
      show O' ∈ 𝓝 (fun b : F => ComplexMatrix2.matExp (Complex.I • ((0 : ℂ) • B) b.1) * U b.1)
      rw [hzero]
      exact hO'.mem_nhds hm)
  filter_upwards [hev] with t ht
  have hin : (fun b : F => ComplexMatrix2.matExp (Complex.I • (t • B) b.1) * U b.1) ∈ O := by
    rw [he]
    exact ⟨ht, fun b => (hleft b.1 (w.positive b.1 b.2)).1 t⟩
  refine ⟨hin, ?_⟩
  have hv := w.eq_some _ (hconf t) (by rw [hvals t]; exact hin)
  rw [hv, hvals t]
end MeanData
section FiniteSide
variable {L n k : ℕ}
theorem isField_of_mem {i : ℕ} {U : Edge L n k i → ComplexMatrix2}
    (h : U ∈ fieldsIn L n k i PeriodicLattice.complexGaugeGroup) :
    (periodicData L n k).IsField (i := i) U :=
  ⟨fun b => h.1 b (mem_univ _), fun b => h.2 b (mem_univ _)⟩
theorem levelwise_eq_periodic (G : (periodicData L n k).Admissible k) :
    ∀ j ≤ k, ∀ V : ∀ i : ℕ, Edge L n k i → ComplexMatrix2, IsMeanSequence j V →
      ∀ i ≤ j, ∀ c : Edge L n k i, levelwiseMean (V 0) i c = some (V i c) := by
  intro j hj V hV i hi c
  rw [← periodicData_levelwise]
  exact MeanData.levelwise_eq_of_sequence (D := periodicData L n k) G hj (V := V)
    (fun i hi => isField_of_mem (hV.mem_fields i hi)) hV.norm_sub_one_lt hV.eq_mean i hi c
theorem representation_toPeriodic {j : ℕ} {c : Edge L n k j} {U : Edge L n k 0 → ComplexMatrix2}
    {F : Finset (Edge L n k 0)} {O : Set (F → ComplexMatrix2)}
    {f : (F → ComplexMatrix2) → ComplexMatrix2}
    (w : (periodicData L n k).Representation j c U F O f) : IsHolomorphicRepresentation j c U F O f :=
  ⟨w.nonempty, w.positive, w.isOpen, w.mem, w.holomorphic, fun W hW hO => by
    rw [← periodicData_levelwise]
    exact w.eq_some W (isField_of_mem hW) hO⟩
theorem representation_ofPeriodic {j : ℕ} {c : Edge L n k j} {U : Edge L n k 0 → ComplexMatrix2}
    {F : Finset (Edge L n k 0)} {O : Set (F → ComplexMatrix2)}
    {f : (F → ComplexMatrix2) → ComplexMatrix2}
    (w : IsHolomorphicRepresentation j c U F O f) : (periodicData L n k).Representation j c U F O f :=
  ⟨w.nonempty, w.positive, w.isOpen, w.mem, w.holomorphic, fun W hW hO =>
    (congrFun (periodicData_levelwise W j) c).trans
      (w.eq_some W ⟨fun b _ => hW.1 b, fun b _ => hW.2 b⟩ hO)⟩
theorem exists_representation_periodic (G : (periodicData L n k).Admissible k)
    (H : ExpChartHolomorphy.ExpChartTheory)
    (hm : ComplexCoordinates.PowerSeriesHolomorphy.Properties) :
    ∀ j ≤ k, ∀ (c : Edge L n k j),
      ∀ U ∈ fieldsIn L n k 0 PeriodicLattice.complexGaugeGroup, IsDefinedAt U j c →
        ∃ (F : Finset (Edge L n k 0)) (O : Set (F → ComplexMatrix2))
          (f : (F → ComplexMatrix2) → ComplexMatrix2), IsHolomorphicRepresentation j c U F O f := by
  intro j hj c U hU hf
  have hs : ((periodicData L n k).levelwise U j c).isSome := by
    rw [periodicData_levelwise]
    exact hf
  obtain ⟨F, O, f, w⟩ := MeanData.exists_representation G H hm (isField_of_mem hU) j hj c hs
  exact ⟨F, O, f, representation_toPeriodic w⟩
theorem hasLeftCurves_periodic (G : (periodicData L n k).Admissible k)
    (hA : LeftChartFields.Claim) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hn : 0 < n) {i : ℕ} (hi : i ≤ k) {U : Edge L n k i → ComplexMatrix2}
    (hU : U ∈ fieldsIn L n k i PeriodicLattice.complexGaugeGroup) {B : Edge L n k i → ComplexMatrix2}
    (hB : ∀ b : Edge L n k i, b.IsPositivelyOriented → B b ∈ PeriodicLattice.complexLieAlgebra) :
    (periodicData L n k).HasLeftCurves (i := i) U B := by
  classical
  intro (b : Edge L n k i) (hb : b.IsPositivelyOriented)
  have hform : extendOddly B ∈ complexEdgeForms L n k i := by
    refine ⟨fun b' hb' => ?_, fun b' => ?_⟩
    · simp only [extendOddly, if_pos hb']
      exact hB b' hb'
    · by_cases hb' : b'.IsPositivelyOriented
      · have hn' : ¬ b'.opposite.IsPositivelyOriented := G.not_pos_opp hi hb'
        simp only [extendOddly, if_pos hb', if_neg hn']
        rfl
      · have hr : b'.opposite.IsPositivelyOriented := G.pos_opp_of_not_pos hi hb'
        simp only [extendOddly, if_pos hr, if_neg hb', neg_neg]
  have hl := (((hA.2.2 L k i hL hi).1 n hn).1.1).2 U hU _ hform ⟨b, hb⟩
  have e : (extendOddly B) b = B b := by
    simp only [extendOddly, if_pos hb]
  have h1 : ∀ t : ℂ, ComplexMatrix2.matExp (Complex.I • (t • extendOddly B b)) * U b ∈
      PeriodicLattice.complexGaugeGroup :=
    hl.1
  have h2 : ContinuousAt
      (fun t : ℂ => ComplexMatrix2.matExp (Complex.I • (t • extendOddly B b)) * U b) 0 :=
    hl.2.continuousAt
  rw [e] at h2
  exact ⟨fun t => by
    have h := h1 t
    rw [e] at h
    exact h, h2⟩
theorem representsAlongCurves_periodic (G : (periodicData L n k).Admissible k)
    (hA : LeftChartFields.Claim) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hn : 0 < n) :
    ∀ j ≤ k, ∀ (c : Edge L n k j),
      ∀ U ∈ fieldsIn L n k 0 PeriodicLattice.complexGaugeGroup,
        ∀ (F : Finset (Edge L n k 0)) (O : Set (F → ComplexMatrix2))
          (f : (F → ComplexMatrix2) → ComplexMatrix2),
          IsHolomorphicRepresentation j c U F O f → RepresentsAlongCurves j c U F O f := by
  intro j _ c U hU F O f w B hB
  have h := (representation_ofPeriodic w).eventually_along G (B := B)
    (hasLeftCurves_periodic G hA hL hn (Nat.zero_le _) hU hB)
  filter_upwards [h] with t ht
  exact ⟨ht.1, (congrFun (periodicData_levelwise _ j) c).symm.trans ht.2⟩
end FiniteSide
namespace Unbounded
open YangMills.Construction.Tower.FullSpace
variable {L k : ℕ}
theorem isField_of_mem {i : ℕ} {U : FullSpace.Edge L k i → ComplexMatrix2}
    (h : U ∈ Tower.FullSpace.fieldsValuedIn L k i PeriodicLattice.complexGaugeGroup) :
    (unboundedData L k).IsField (i := i) U := h
theorem levelwise_eq_unbounded (G : (unboundedData L k).Admissible k) :
    ∀ j ≤ k, ∀ V : ∀ i : ℕ, FullSpace.Edge L k i → ComplexMatrix2, IsMeanSequence j V →
      ∀ i ≤ j, ∀ c : FullSpace.Edge L k i, levelwiseMean (V 0) i c = some (V i c) := by
  intro j hj V hV i hi c
  rw [← unboundedData_levelwise]
  exact MeanData.levelwise_eq_of_sequence (D := unboundedData L k) G hj (V := V)
    (fun i hi => isField_of_mem (hV.mem_fields i hi)) hV.norm_sub_one_lt hV.eq_mean i hi c
theorem representation_toUnbounded {j : ℕ} {c : FullSpace.Edge L k j}
    {U : FullSpace.Edge L k 0 → ComplexMatrix2}
    {F : Finset (FullSpace.Edge L k 0)} {O : Set (F → ComplexMatrix2)}
    {f : (F → ComplexMatrix2) → ComplexMatrix2}
    (w : (unboundedData L k).Representation j c U F O f) :
    IsHolomorphicRepresentation j c U F O f :=
  ⟨⟨w.nonempty, w.positive⟩, w.isOpen, w.mem, w.holomorphic, fun W hW hO => by
    rw [← unboundedData_levelwise]
    exact w.eq_some W (isField_of_mem hW) hO⟩
theorem representation_ofUnbounded {j : ℕ} {c : FullSpace.Edge L k j}
    {U : FullSpace.Edge L k 0 → ComplexMatrix2}
    {F : Finset (FullSpace.Edge L k 0)} {O : Set (F → ComplexMatrix2)}
    {f : (F → ComplexMatrix2) → ComplexMatrix2}
    (w : IsHolomorphicRepresentation j c U F O f) :
    (unboundedData L k).Representation j c U F O f :=
  ⟨w.finite_edges.1, w.finite_edges.2, w.isOpen, w.mem, w.holomorphic, fun W hW hO =>
    (congrFun (unboundedData_levelwise W j) c).trans (w.eq_some W hW hO)⟩
theorem exists_representation_unbounded (G : (unboundedData L k).Admissible k)
    (H : ExpChartHolomorphy.ExpChartTheory)
    (hm : ComplexCoordinates.PowerSeriesHolomorphy.Properties) :
    ∀ j ≤ k, ∀ (c : FullSpace.Edge L k j),
      ∀ U ∈ Tower.FullSpace.fieldsValuedIn L k 0 PeriodicLattice.complexGaugeGroup,
        IsDefinedAt U j c →
        ∃ (F : Finset (FullSpace.Edge L k 0)) (O : Set (F → ComplexMatrix2))
          (f : (F → ComplexMatrix2) → ComplexMatrix2), IsHolomorphicRepresentation j c U F O f := by
  intro j hj c U hU hf
  have hs : ((unboundedData L k).levelwise U j c).isSome := by
    rw [unboundedData_levelwise]
    exact hf
  obtain ⟨F, O, f, w⟩ := MeanData.exists_representation G H hm (isField_of_mem hU) j hj c hs
  exact ⟨F, O, f, representation_toUnbounded w⟩
theorem hasLeftCurves_unbounded (G : (unboundedData L k).Admissible k)
    (hA : LeftChartFields.Claim) (hL : Conventions.IsAdmissibleBlockingFactor L)
    {i : ℕ} (hi : i ≤ k) {U : FullSpace.Edge L k i → ComplexMatrix2}
    (hU : U ∈ Tower.FullSpace.fieldsValuedIn L k i PeriodicLattice.complexGaugeGroup)
    {B : FullSpace.Edge L k i → ComplexMatrix2}
    (hB : ∀ b : FullSpace.Edge L k i, b.IsPositivelyOriented →
      B b ∈ PeriodicLattice.complexLieAlgebra) :
    (unboundedData L k).HasLeftCurves (i := i) U B := by
  classical
  intro (b : FullSpace.Edge L k i) (hb : b.IsPositivelyOriented)
  have hform : Tower.FullSpace.extendOddly B ∈
      Tower.FullSpace.complexEdgeForms (meshAt L k i) := by
    refine ⟨fun b' hb' => ?_, fun b' => ?_⟩
    · simp only [Tower.FullSpace.extendOddly, if_pos hb']
      exact hB b' hb'
    · by_cases hb' : b'.IsPositivelyOriented
      · have hn' : ¬ b'.opposite.IsPositivelyOriented := G.not_pos_opp hi hb'
        simp only [Tower.FullSpace.extendOddly, if_pos hb', if_neg hn']
        rfl
      · have hr : b'.opposite.IsPositivelyOriented := G.pos_opp_of_not_pos hi hb'
        simp only [Tower.FullSpace.extendOddly, if_pos hr, if_neg hb', neg_neg]
  have hl := (((hA.2.2 L k i hL hi).2.1).1).2 U hU _ hform ⟨b, hb⟩
  have e : (Tower.FullSpace.extendOddly B) b = B b := by
    simp only [Tower.FullSpace.extendOddly, if_pos hb]
  have h1 : ∀ t : ℂ,
      ComplexMatrix2.matExp (Complex.I • (t • Tower.FullSpace.extendOddly B b)) * U b ∈
        PeriodicLattice.complexGaugeGroup :=
    hl.1
  have h2 : ContinuousAt (fun t : ℂ =>
      ComplexMatrix2.matExp (Complex.I • (t • Tower.FullSpace.extendOddly B b)) * U b) 0 :=
    hl.2.continuousAt
  rw [e] at h2
  exact ⟨fun t => by
    have h := h1 t
    rw [e] at h
    exact h, h2⟩
theorem representsAlongCurves_unbounded (G : (unboundedData L k).Admissible k)
    (hA : LeftChartFields.Claim) (hL : Conventions.IsAdmissibleBlockingFactor L) :
    ∀ j ≤ k, ∀ (c : FullSpace.Edge L k j),
      ∀ U ∈ Tower.FullSpace.fieldsValuedIn L k 0 PeriodicLattice.complexGaugeGroup,
        ∀ (F : Finset (FullSpace.Edge L k 0)) (O : Set (F → ComplexMatrix2))
          (f : (F → ComplexMatrix2) → ComplexMatrix2),
          IsHolomorphicRepresentation j c U F O f → RepresentsAlongCurves j c U F O f := by
  intro j _ c U hU F O f w B hB
  have h := (representation_ofUnbounded w).eventually_along G (B := B)
    (hasLeftCurves_unbounded G hA hL (Nat.zero_le _) hU hB)
  filter_upwards [h] with t ht
  exact ⟨ht.1, (congrFun (unboundedData_levelwise _ j) c).symm.trans ht.2⟩
end Unbounded
open YangMills.Construction.Tower.LeftChartFields
abbrev scalarChart : ℂ ≃ ComplexCoordinates 1 := (Equiv.funUnique (Fin 1) ℂ).symm
theorem continuous_scalarChart : Continuous scalarChart :=
  (Homeomorph.funUnique (Fin 1) ℂ).symm.continuous
theorem isHolomorphicToCoords_entry (H : ExpChartHolomorphy.ExpChartTheory)
    {ι : Type} [Fintype ι] {β : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless}
    {W : Set (ι ⊕ Empty → ComplexMatrix2)}
    {Φ : (ι ⊕ Empty → ComplexMatrix2) → ComplexMatrix2}
    (h : IsHolomorphicToUnimodular β W Φ) (r s : Fin 2) :
    IsHolomorphicToCoords β scalarChart W fun p => Φ p r s := by
  have hm := ((H.2.2.2.1 ι Empty).2.1 β W Φ h.1 h.2.1).1 h
  have hk : ∀ X : ComplexMatrix2,
      ComplexCoordinates.matrixEquiv X (ComplexCoordinates.entryIndex (r, s)) = X r s :=
    fun X => by simp [ComplexCoordinates.matrixEquiv]
  refine ⟨hm.1, ?_, fun p hp => ?_⟩
  · have h1 := (continuous_apply (ComplexCoordinates.entryIndex (r, s))).comp_continuousOn hm.2.1
    have h2 : ContinuousOn (fun p => Φ p r s) W := h1.congr fun p _ => (hk (Φ p)).symm
    exact continuous_scalarChart.comp_continuousOn h2
  · obtain ⟨O, h0, hO, hhol⟩ := hm.2.2 p hp
    refine ⟨O, h0, hO, hhol.1, fun ν => ?_⟩
    have hh := hhol.2 ν
    refine ⟨hh.1, ?_, fun a ha j => ?_⟩
    · have h1 :=
        (continuous_apply (ComplexCoordinates.entryIndex (r, s))).comp_continuousOn hh.2.1
      refine continuous_scalarChart.comp_continuousOn (h1.congr fun z _ => ?_)
      exact (hk _).symm
    · filter_upwards [hh.2.2 a ha j] with ζ hd
      have h1 := (differentiableAt_pi.1 hd) (ComplexCoordinates.entryIndex (r, s))
      refine differentiableAt_pi.2 fun _ => ?_
      refine h1.congr_of_eventuallyEq (Eventually.of_forall fun z => ?_)
      exact (hk _).symm
theorem differentiableAt_along_leftChart (H : ExpChartHolomorphy.ExpChartTheory) {Λ : LatticeData}
    (hΛ : Λ.HolomorphicGradientExists) {σ : Type} [Fintype σ] [Nonempty σ]
    (ι : σ → Λ.PosLink) {O : Set (σ → ComplexMatrix2)}
    (hO : ComplexMatrix2.IsRelativelyOpen (unimodularPi σ) O)
    {Φ : (σ → ComplexMatrix2) → ComplexMatrix2}
    (hent : ∀ (β : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless) (r s : Fin 2),
      IsHolomorphicToCoords β scalarChart (leftComponents ⁻¹' O)
        fun p => Φ (leftComponents p) r s)
    {U : Λ.Link → ComplexMatrix2} (hU : U ∈ Λ.fields PeriodicLattice.complexGaugeGroup)
    (hUO : (fun s => U (Λ.incl (ι s))) ∈ O) {B : Λ.Link → ComplexMatrix2} (hB : B ∈ Λ.cforms) :
    DifferentiableAt ℂ (fun t : ℂ => Φ fun s =>
      leftExpMul (t • B (Λ.incl (ι s))) (U (Λ.incl (ι s)))) 0 := by
  classical
  let e := Fintype.equivFin σ
  have hr : 1 ≤ Fintype.card σ := Fintype.card_pos
  let bs : Fin (Fintype.card σ) → Λ.PosLink := fun i => ι (e.symm i)
  let O' : Set (Fin (Fintype.card σ) → ComplexMatrix2) := (fun w s => w (e s)) ⁻¹' O
  let Ψ : (Fin (Fintype.card σ) ⊕ Empty → ComplexMatrix2) → σ ⊕ Empty → ComplexMatrix2 :=
    fun q => asGroupFactors fun s => q (.inl (e s))
  obtain ⟨O₀, hO₀, rfl⟩ := hO
  have hreindex : Continuous fun (w : Fin (Fintype.card σ) → ComplexMatrix2) (s : σ) => w (e s) :=
    continuous_pi fun _ => continuous_apply _
  have hpow : ∀ w ∈ O', w ∈ unimodularPi (Fin (Fintype.card σ)) := by
    intro w hw i
    have := hw.2 (e.symm i)
    simpa using this
  have hO' : ComplexMatrix2.IsRelativelyOpen (unimodularPi (Fin (Fintype.card σ))) O' := by
    refine ⟨_, hO₀.preimage hreindex, ?_⟩
    ext w
    exact ⟨fun hw => ⟨hw.1, hpow w hw⟩, fun hw => ⟨hw.1, fun s => hw.2 (e s)⟩⟩
  have hprod : ComplexMatrix2.IsRelativelyOpen (GroupLieProduct (Fin (Fintype.card σ)) Empty)
      (GroupLieProduct (Fin (Fintype.card σ)) Empty) := ⟨univ, isOpen_univ, by simp⟩
  have hentry : ∀ a b : Fin 2, DifferentiableAt ℂ (fun t : ℂ => (Φ fun s =>
      leftExpMul (t • B (Λ.incl (ι s))) (U (Λ.incl (ι s)))) a b) 0 := by
    intro a b
    let β := tracelessBasis
    have hΨ : IsHolomorphicToProduct β (GroupLieProduct (Fin (Fintype.card σ)) Empty) Ψ :=
      ⟨hprod, fun s => isHolomorphicToUnimodular_component H β hprod (e s), fun x => x.elim⟩
    obtain ⟨_, _, hh⟩ := H.2.2.2.2.1 (Fin (Fintype.card σ)) Empty σ Empty β _ Ψ hprod hΨ ℂ 1
      scalarChart _ _ (hent β a b)
    have hset : GroupLieProduct (Fin (Fintype.card σ)) Empty ∩
        Ψ ⁻¹' (leftComponents ⁻¹' (O₀ ∩ unimodularPi σ)) = asGroupFactors '' O' := by
      rw [image_asGroupFactors]
      ext p
      constructor
      · rintro ⟨_, hp⟩
        exact hp
      · intro hp
        refine ⟨?_, hp⟩
        have : leftComponents p ∈ unimodularPi (Fin (Fintype.card σ)) := hpow _ hp
        rw [← asGroupFactors_leftComponents p]
        exact asGroupFactors_mem_iff.2 this
    rw [hset] at hh
    have hmain := hΛ β (Fintype.card σ) hr bs O' (fun w => Φ (fun s => w (e s)) a b) U hO' hh hU
      (by
        have e1 : (fun s => (fun i => LatticeData.onPositive U (bs i)) (e s)) =
            fun s => U (Λ.incl (ι s)) := by
          funext s
          simp [bs, LatticeData.onPositive]
        show (fun s => (fun i => LatticeData.onPositive U (bs i)) (e s)) ∈ O₀ ∩ unimodularPi σ
        rw [e1]
        exact hUO)
    have hd := hmain.2.1 B hB
    refine hd.congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)
    show _ = (Φ fun s => LatticeData.leftPoint bs U (algebraMap ℂ ℂ t • B) (e s)) a b
    simp [LatticeData.leftPoint, bs, LatticeData.onPositive]
  have hs : (fun t : ℂ => Φ fun s => leftExpMul (t • B (Λ.incl (ι s))) (U (Λ.incl (ι s)))) =
      fun t => ∑ a, ∑ b,
        ((Φ fun s => leftExpMul (t • B (Λ.incl (ι s))) (U (Λ.incl (ι s)))) a b) •
          (Matrix.single a b (1 : ℂ) : ComplexMatrix2) := by
    funext t
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.sum_apply, Matrix.single_apply]
  rw [hs]
  exact DifferentiableAt.fun_sum fun a _ => DifferentiableAt.fun_sum fun b _ =>
    (hentry a b).smul_const _
namespace MeanData
variable {D : MeanData} {k : ℕ}
theorem eventually_twist_mem_polydisc (G : D.Admissible k) {i : ℕ} (hi : i < k)
    {c : D.Link (i + 1)} (hc : D.pos c)
    {V B : D.Link i → ComplexMatrix2} (hV : D.IsField V) (hVp : V ∈ D.polydisc c)
    (hleft : D.HasLeftCurves V B) :
    ∀ᶠ t : ℂ in 𝓝 0, D.twist (t • B) V ∈ D.polydisc c := by
  have hT := tendsto_twist G hi.le hV hleft
  have hn : ∀ᶠ t : ℂ in 𝓝 0, ∀ b ∈ D.block c,
      ComplexMatrix2.operatorNorm (D.twist (t • B) V b - 1) < D.radius := by
    refine (eventually_all_finite (G.block_finite i hi c hc)).2 fun b hb => ?_
    have hb' : Tendsto (fun t : ℂ => D.twist (t • B) V b) (𝓝 0) (𝓝 (V b)) :=
      (tendsto_pi_nhds.1 hT) b
    exact hb'.eventually (isOpen_operatorNorm_sub_one_lt.mem_nhds (hVp.2 b hb))
  filter_upwards [hn] with t ht
  have hconf := isField_twist G hi.le hleft t
  exact ⟨⟨fun b _ => hconf.1 b, fun b _ => hconf.2 b⟩, ht⟩
theorem differentiableAt_of_extend (G : D.Admissible k) {i : ℕ} (hi : i < k)
    {c : D.Link (i + 1)} (hc : D.pos c)
    {V B : D.Link i → ComplexMatrix2} (hV : D.IsField V) (hVp : V ∈ D.polydisc c)
    (hleft : D.HasLeftCurves V B)
    {a : (D.Link i → ComplexMatrix2) → ComplexMatrix2}
    (hread : ∀ V' ∈ D.polydisc c, a V' = a (D.extend c fun b => V' b.1))
    (hd : DifferentiableAt ℂ (fun t : ℂ => a (D.extend c fun s =>
      ComplexMatrix2.matExp (Complex.I • (t • B) s.1) * V s.1)) 0) :
    DifferentiableAt ℂ (fun t : ℂ => a (D.twist (t • B) V)) 0 := by
  classical
  refine hd.congr_of_eventuallyEq ?_
  filter_upwards [eventually_twist_mem_polydisc G hi hc hV hVp hleft] with t ht
  rw [hread _ ht]
  congr 2
  funext s
  simp only [twist, if_pos s.2.2]
end MeanData
theorem hasDerivAt_ofReal_of_complex {g : ℂ → ComplexMatrix2} {d : ComplexMatrix2}
    (h : HasDerivAt g d 0) : HasDerivAt (fun t : ℝ => g (t : ℂ)) d 0 := by
  refine hasDerivAt_pi.2 fun a => hasDerivAt_pi.2 fun b => ?_
  have h1 : HasDerivAt (fun t => g t a b) (d a b) 0 := hasDerivAt_pi.1 (hasDerivAt_pi.1 h a) b
  have h2 : HasDerivAt (fun t : ℂ => g t a b) (d a b) ((0 : ℝ) : ℂ) := by simpa using h1
  exact h2.comp_ofReal
section FiniteSide
variable {L n k : ℕ}
theorem complexMeanContour_congr (hBP : PeriodicLattice.DoubleBlockStructure.Statement)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) {j : ℕ} (hj : j < k)
    {c : Edge L n k (j + 1)} {y : Vertex L n k (j + 1)}
    (hy : y ∈ ({c.source, c.target} : Set (Vertex L n k (j + 1))))
    {x : Vertex L n k j} (hx : x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y)
    {V V' : Edge L n k j → ComplexMatrix2}
    (he : ∀ b ∈ (PeriodicLattice.bondsInDoubleBlock c : Set (Edge L n k j)), V b = V' b) :
    PeriodicLattice.complexMeanContourHolonomy V y x =
      PeriodicLattice.complexMeanContourHolonomy V' y x := by
  have h := (hBP L n k j hL hn hj c).2.1 y hy x hx
  unfold PeriodicLattice.complexMeanContourHolonomy
  congr 1
  funext σ
  have hb := (h _ ⟨σ, rfl⟩).2
  simp only [PeriodicLattice.contourHolonomies, PeriodicLattice.pathHolonomy]
  congr 1
  exact List.map_congr_left fun b hbm => he b (hb b hbm)
theorem differentiableAt_twist (H : ExpChartHolomorphy.ExpChartTheory)
    (G : (periodicData L n k).Admissible k) (hA : LeftChartFields.Claim)
    (hP : DoubleBlockPolydisc.PolydiscsHold)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) {j : ℕ} (hj : j < k)
    {c : Edge L n k (j + 1)} (hc : c.IsPositivelyOriented) {V : Edge L n k j → ComplexMatrix2}
    (hV : V ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup)
    (hVp : V ∈ (periodicData L n k).polydisc (i := j) c) {B : Edge L n k j → ComplexMatrix2}
    (hB : B ∈ complexEdgeForms L n k j) {a : (Edge L n k j → ComplexMatrix2) → ComplexMatrix2}
    (hread : ∀ V' ∈ (periodicData L n k).polydisc (i := j) c,
      a V' = a (DoubleBlockPolydisc.fieldOfValues c fun b => V' b.1))
    (hent : ∃ _ : Fintype (positiveDoubleBlockBonds c),
      ∀ (β : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless) (r s : Fin 2),
      IsHolomorphicToCoords β scalarChart
        (leftComponents ⁻¹' polydiscPositive (polydiscRadius L) c) fun p =>
          a (DoubleBlockPolydisc.fieldOfValues c (leftComponents p)) r s) :
    DifferentiableAt ℂ (fun t : ℂ => a (PeriodicLattice.expTwist (t • B) V)) 0 := by
  obtain ⟨inst, hent⟩ := hent
  have hfo := ((hP L hL k j hj).1 n hn c hc).finite_open
  have hne : Nonempty (positiveDoubleBlockBonds c) := hfo.positive_nonempty.to_subtype
  have hleft := hasLeftCurves_periodic G hA hL hn hj.le hV hB.1
  have hd := differentiableAt_along_leftChart H (((hA.2.2 L k j hL hj.le).1 n hn).1.2.2.2)
    (Λ := finiteData L n k j) (σ := positiveDoubleBlockBonds c)
    (fun s => (⟨s.1, s.2.2⟩ : PositiveEdge L n k j)) hfo.isRelativelyOpen
    (Φ := fun v => a (DoubleBlockPolydisc.fieldOfValues c v)) hent hV
    ⟨_, ⟨V, hVp, rfl⟩, rfl⟩ hB
  exact MeanData.differentiableAt_of_extend (D := periodicData L n k) G hj hc (isField_of_mem hV)
    hVp hleft hread hd
theorem exists_open_nhd_one (hE6 : BondSetFields.ProductStructureHolds)
    (hB1 : SmoothingNearTrivialField)
    (hS : SmoothingNearIdentity)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hk : 1 ≤ k) {j : ℕ}
    (hj : j < k) :
    ∃ O₁ : Set (Edge L n k j → ComplexMatrix2), IsOpen O₁ ∧ (fun _ => (1 : ComplexMatrix2)) ∈ O₁ ∧
      ∀ V ∈ O₁, V ∈ fieldSpace L n k j →
        V ∈ commonSmoothingDomain L n k j ∧
          ∀ b, ComplexMatrix2.operatorNorm (V b - 1) < polydiscRadius L := by
  obtain ⟨⟨hSsub, hSopen⟩, h1⟩ := ((hB1 L n k hL hn hk).1 j hj).1
  have hAll := ((hE6 L hL k j hj.le).1 n hn).2
  have hSopen' : ComplexMatrix2.IsRelativelyOpen (fieldSpace L n k j)
      (commonSmoothingDomain L n k j) :=
    (hAll.2.2.2.2.2.2.2.1 _ hSsub).2 hSopen
  obtain ⟨O₀, hO₀, hSe⟩ := hSopen'
  have hρ : 0 < polydiscRadius L := (hS.1 L hL).2.2.pos
  have : Finite (Edge L n k j) := Set.finite_univ_iff.1 hAll.1
  refine ⟨O₀ ∩ ⋂ b, {V | ComplexMatrix2.operatorNorm (V b - 1) < polydiscRadius L}, ?_, ?_, ?_⟩
  · refine hO₀.inter (isOpen_iInter_of_finite fun b => ?_)
    have hcb : Continuous fun V : Edge L n k j → ComplexMatrix2 => V b := continuous_apply b
    exact (isOpen_operatorNorm_sub_one_lt (r := polydiscRadius L)).preimage hcb
  · have h1' : (fun _ => (1 : ComplexMatrix2)) ∈ commonSmoothingDomain L n k j := h1
    rw [hSe] at h1'
    refine ⟨h1'.1, mem_iInter.2 fun b => ?_⟩
    simpa using hρ
  · intro V hV hVc
    refine ⟨?_, fun b => mem_iInter.1 hV.2 b⟩
    rw [hSe]
    exact ⟨hV.1, hVc⟩
theorem facts_near_one (hB1 : SmoothingNearTrivialField)
    (hSch : PeriodicLattice.AveragingSchemeProperties)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hk : 1 ≤ k) {j : ℕ}
    (hj : j < k) {c : Edge L n k (j + 1)} (hc : c.IsPositivelyOriented)
    {V : Edge L n k j → ComplexMatrix2}
    (hV : V ∈ commonSmoothingDomain L n k j)
    (hball : ∀ b, ComplexMatrix2.operatorNorm (V b - 1) < polydiscRadius L) :
    V ∈ nearIdentityPolydisc (polydiscRadius L) c ∧
      PeriodicLattice.complexBlockAverage V c = smoothingStep L n k j V c ∧
      ∀ y ∈ ({c.source, c.target} : Set (Vertex L n k (j + 1))),
        ∀ x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y,
          PeriodicLattice.HasContourMean V y x ∧
            PeriodicLattice.complexMeanContourHolonomy V y x =
              PeriodicLattice.meanContourHolonomy V y x := by
  have hb := ((hB1 L n k hL hn hk).1 j hj).2 V hV c hc
  have hms := (hSch L hL n k j hn hj .centred).2.1 c hc
  have hmm := hms.2.2.2.2.1 V hb.isGaugeField hb.curvature_lt
  refine ⟨⟨⟨fun b hbm => ?_, hb.isGaugeField.2⟩, fun b _ => hball b⟩, ?_, fun y hy x hx =>
    ⟨hmm.unique_mean y hy x hx, hmm.contour_eq y hy x hx⟩⟩
  · exact (Matrix.mem_specialUnitaryGroup_iff.1 (hb.isGaugeField.1 b hbm)).2
  · exact (hms.2.2.1.average_eq V hmm.mem_domain).symm.trans hmm.average_eq
theorem mem_complexEdgeForms_of_mem {j : ℕ} {B : Edge L n k j → ComplexMatrix2}
    (hB : B ∈ edgeFormSpace L n k j) : B ∈ complexEdgeForms L n k j :=
  ⟨fun b hb => (hB.1 b hb).2, hB.2⟩
theorem ofReal_smul_mem_edgeFormSpace {j : ℕ} {B : Edge L n k j → ComplexMatrix2}
    (hB : B ∈ edgeFormSpace L n k j) (t : ℝ) : (t : ℂ) • B ∈ edgeFormSpace L n k j := by
  have e : (t : ℂ) • B = t • B := by
    funext b
    ext r s
    simp
  rw [e]
  exact (edgeFormSpace L n k j).smul_mem t hB
theorem mem_fieldsIn_of_mem {j : ℕ} {V : Edge L n k j → ComplexMatrix2}
    (hV : V ∈ fieldSpace L n k j) : V ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup :=
  ⟨fun b hb => (Matrix.mem_specialUnitaryGroup_iff.1 (hV.1 b hb)).2, hV.2⟩
theorem tendsto_ofReal_nhds_zero : Tendsto (fun t : ℝ => (t : ℂ)) (𝓝 0) (𝓝 0) := by
  simpa using Complex.continuous_ofReal.tendsto 0
theorem agreesNearIdentity_periodic (H : ExpChartHolomorphy.ExpChartTheory)
    (G : (periodicData L n k).Admissible k) (hA : LeftChartFields.Claim)
    (hP : DoubleBlockPolydisc.PolydiscsHold)
    (hE6 : BondSetFields.ProductStructureHolds)
    (hB1 : SmoothingNearTrivialField)
    (hS : SmoothingNearIdentity)
    (hSch : PeriodicLattice.AveragingSchemeProperties)
    (hBP : PeriodicLattice.DoubleBlockStructure.Statement)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hk : 1 ≤ k) :
    ∀ j < k, ∀ c : Edge L n k (j + 1), c.IsPositivelyOriented →
      ∀ y ∈ ({c.source, c.target} : Set (Vertex L n k (j + 1))),
        ∀ x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y,
          RealAndComplexAgreeNearIdentity j c y x := by
  intro j hj c hc y hy x hx
  obtain ⟨O₁, hO₁, h1, hgood⟩ := exists_open_nhd_one hE6 hB1 hS hL hn hk hj
  have facts : ∀ V ∈ O₁, V ∈ fieldSpace L n k j → _ := fun V hV hVc =>
    facts_near_one hB1 hSch hL hn hk hj hc (hgood V hV hVc).1 (hgood V hV hVc).2
  refine mem_nhdsWithin.2 ⟨O₁, hO₁, h1, ?_⟩
  rintro V ⟨hVO, hVc⟩
  obtain ⟨hp, e1, e2⟩ := facts V hVO hVc
  refine ⟨hp, e1, (e2 y hy x hx).1, (e2 y hy x hx).2, fun B hB => ?_⟩
  have hVC := mem_fieldsIn_of_mem hVc
  have hBC := mem_complexEdgeForms_of_mem hB
  have hleft := hasLeftCurves_periodic G hA hL hn hj.le hVC hBC.1
  have hT : Tendsto (fun t : ℝ => PeriodicLattice.expTwist ((t : ℂ) • B) V) (𝓝 0) (𝓝 V) :=
    (MeanData.tendsto_twist (D := periodicData L n k) G hj.le (isField_of_mem hVC) hleft).comp
      tendsto_ofReal_nhds_zero
  have hnear : ∀ᶠ t : ℝ in 𝓝 0, PeriodicLattice.expTwist ((t : ℂ) • B) V ∈ O₁ :=
    hT.eventually (hO₁.mem_nhds hVO)
  have hconf : ∀ t : ℝ, PeriodicLattice.expTwist ((t : ℂ) • B) V ∈ fieldSpace L n k j :=
    fun t => (hB1 L n k hL hn hk).2 j hj.le _ (ofReal_smul_mem_edgeFormSpace hB t) V hVc
  have hholo := (hP L hL k j hj).1 n hn c hc
  have hdA : DifferentiableAt ℂ (fun t : ℂ =>
      PeriodicLattice.complexBlockAverage (PeriodicLattice.expTwist (t • B) V) c) 0 :=
    differentiableAt_twist H G hA hP hL hn hj hc hVC hp hBC
      (a := fun W => PeriodicLattice.complexBlockAverage W c) (G.mean_extend j hj c hc)
      (by
        obtain ⟨inst, h⟩ := hholo.holomorphic_smoothing
        exact ⟨inst, h.entries⟩)
  have hdC : DifferentiableAt ℂ (fun t : ℂ =>
      PeriodicLattice.complexMeanContourHolonomy (PeriodicLattice.expTwist (t • B) V) y x) 0 :=
    differentiableAt_twist H G hA hP hL hn hj hc hVC hp hBC
      (a := fun W => PeriodicLattice.complexMeanContourHolonomy W y x)
      (fun V' hV' => complexMeanContour_congr hBP hL hn hj hy hx (G.eq_extend j hj c hc V' hV'))
      (by
        obtain ⟨inst, h⟩ := hholo.holomorphic_contourMean y hy x hx
        exact ⟨inst, h.entries⟩)
  refine ⟨hnear.mono fun t ht => (facts _ ht (hconf t)).1, ⟨_,
    (hasDerivAt_ofReal_of_complex hdA.hasDerivAt).congr_of_eventuallyEq
      (hnear.mono fun t ht => (facts _ ht (hconf t)).2.1.symm),
    hasDerivAt_ofReal_of_complex hdA.hasDerivAt⟩, ⟨_,
    (hasDerivAt_ofReal_of_complex hdC.hasDerivAt).congr_of_eventuallyEq
      (hnear.mono fun t ht => ((facts _ ht (hconf t)).2.2 y hy x hx).2.symm),
    hasDerivAt_ofReal_of_complex hdC.hasDerivAt⟩⟩
end FiniteSide
namespace Unbounded
open YangMills.Construction.Tower.FullSpace
variable {L k : ℕ}
theorem differentiableAt_twist (H : ExpChartHolomorphy.ExpChartTheory)
    (G : (unboundedData L k).Admissible k) (hA : LeftChartFields.Claim)
    (hP : DoubleBlockPolydisc.PolydiscsHold)
    (hL : Conventions.IsAdmissibleBlockingFactor L) {j : ℕ} (hj : j < k)
    {c : FullSpace.Edge L k (j + 1)} (hc : c.IsPositivelyOriented)
    {V : FullSpace.Edge L k j → ComplexMatrix2}
    (hV : V ∈ Tower.FullSpace.fieldsValuedIn L k j PeriodicLattice.complexGaugeGroup)
    (hVp : V ∈ (unboundedData L k).polydisc (i := j) c) {B : FullSpace.Edge L k j → ComplexMatrix2}
    (hB : B ∈ Tower.FullSpace.complexEdgeForms (meshAt L k j))
    {a : (FullSpace.Edge L k j → ComplexMatrix2) → ComplexMatrix2}
    (hread : ∀ V' ∈ (unboundedData L k).polydisc (i := j) c,
      a V' = a (DoubleBlockPolydisc.Infinite.fieldOfValues L k j c fun b => V' b.1))
    (hent : ∃ _ : Fintype (DoubleBlockPolydisc.Infinite.positiveDoubleBlockBonds L k j c),
      ∀ (β : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless) (r s : Fin 2),
      IsHolomorphicToCoords β scalarChart
        (leftComponents ⁻¹' DoubleBlockPolydisc.Infinite.polydiscPositive L k j
          (polydiscRadius L) c) fun p =>
          a (DoubleBlockPolydisc.Infinite.fieldOfValues L k j c (leftComponents p)) r s) :
    DifferentiableAt ℂ (fun t : ℂ => a (Tower.FullSpace.expTwist (t • B) V)) 0 := by
  obtain ⟨inst, hent⟩ := hent
  have hfo := ((hP L hL k j hj).2 c hc).finite_open
  have hne : Nonempty (DoubleBlockPolydisc.Infinite.positiveDoubleBlockBonds L k j c) :=
    hfo.positive_nonempty.to_subtype
  have hleft := hasLeftCurves_unbounded G hA hL hj.le hV hB.1
  have hd := differentiableAt_along_leftChart H (((hA.2.2 L k j hL hj.le).2.1).2.2.2)
    (Λ := fullData L k j) (σ := DoubleBlockPolydisc.Infinite.positiveDoubleBlockBonds L k j c)
    (fun s => (⟨s.1, s.2.2⟩ : Tower.FullSpace.PositiveEdge (meshAt L k j)))
    hfo.isRelativelyOpen
    (Φ := fun v => a (DoubleBlockPolydisc.Infinite.fieldOfValues L k j c v)) hent hV
    ⟨_, ⟨V, hVp, rfl⟩, rfl⟩ hB
  exact MeanData.differentiableAt_of_extend (D := unboundedData L k) G hj hc (isField_of_mem hV)
    hVp hleft hread hd
theorem complexContourMean_congr (hS : SmoothingNearIdentity)
    (hQ : SublatticesSymmetriesScalingsAndProjections.Statement)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hk : 1 ≤ k) {j : ℕ} (hj : j < k)
    {c : FullSpace.Edge L k (j + 1)} (hc : c.IsPositivelyOriented)
    {y : FullSpace.Vertex L k (j + 1)}
    (hy : y ∈ ({c.initial, c.terminal} : Set (FullSpace.Vertex L k (j + 1))))
    {x : FullSpace.Vertex L k j} (hx : x ∈ Tower.FullSpace.cubeVertices L (meshAt L k j) y)
    {V V' : FullSpace.Edge L k j → ComplexMatrix2} (hV : V ∈ (unboundedData L k).polydisc (i := j) c)
    (hV' : V' ∈ (unboundedData L k).polydisc (i := j) c)
    (he : ∀ b ∈ doubleCubeLinks L (meshAt L k j) c, V b = V' b) :
    Tower.FullSpace.complexContourMean L V y x = Tower.FullSpace.complexContourMean L V' y x := by
  have hL0 : 0 < L := by
    have := hL.2
    omega
  have hserve := (hS.1 L hL).2.2.fullSpace k j hj c hc
  have hQ' := ((hQ L hL0 hL k).2.2.2.2.2.2 hk 1 one_pos).2 j hj c hc
  have hy' : y = c.initial ∨ y = c.terminal := by simpa using hy
  have e1 := hQ'.complexContourMean_eq V (hserve.subset_complexDomain hV) y hy' x hx
  have e2 := hQ'.complexContourMean_eq V' (hserve.subset_complexDomain hV') y hy' x hx
  refine e1.trans (Eq.trans ?_ e2.symm)
  congr 1
  funext z
  unfold Tower.FullSpace.projField
  split_ifs with h
  · exact he _ h.choose_spec.1
  · rfl
theorem mem_complexEdgeForms_of_mem {j : ℕ} {B : FullSpace.Edge L k j → ComplexMatrix2}
    (hB : B ∈ Tower.FullSpace.edgeFormSpace (meshAt L k j)) :
    B ∈ Tower.FullSpace.complexEdgeForms (meshAt L k j) :=
  ⟨fun b hb => (hB.1 b hb).2, hB.2⟩
theorem realAndComplexAgree_unbounded (H : ExpChartHolomorphy.ExpChartTheory)
    (G : (unboundedData L k).Admissible k) (hA : LeftChartFields.Claim)
    (hP : DoubleBlockPolydisc.PolydiscsHold)
    (hS : SmoothingNearIdentity)
    (hQ : SublatticesSymmetriesScalingsAndProjections.Statement)
    (hM : Tower.FullSpace.SmoothingNearIdentity)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hk : 1 ≤ k) :
    ∀ j < k, Tower.FullSpace.EventuallyNearIdentity (Tower.FullSpace.fieldSpace L k j) fun V =>
      ∀ c : FullSpace.Edge L k (j + 1), c.IsPositivelyOriented →
        ∀ y ∈ ({c.initial, c.terminal} : Set (FullSpace.Vertex L k (j + 1))),
          ∀ x ∈ Tower.FullSpace.cubeVertices L (meshAt L k j) y,
            RealAndComplexAgreeAt j V c y x := by
  intro j hj
  have hρ : 0 < polydiscRadius L := (hS.1 L hL).2.2.pos
  have hω : 0 < Averaging.smoothingRadius L :=
    (Averaging.isSmoothingRadius_smoothingRadius hL.1 hL.2).1
  have hε : 0 < min (polydiscRadius L) (Averaging.smoothingRadius L / 4) :=
    lt_min hρ (by linarith)
  refine ⟨_, hε, fun V hVc hd c hc y hy x hx => ?_⟩
  have hball : ∀ b, ComplexMatrix2.operatorNorm (V b - 1) <
      min (polydiscRadius L) (Averaging.smoothingRadius L / 4) := by
    intro b
    have h1 : ENNReal.ofReal (ComplexMatrix2.operatorNorm (V b - 1)) ≤ supDistOne V :=
      le_iSup (fun b => ENNReal.ofReal (ComplexMatrix2.operatorNorm (V b - 1))) b
    exact (ENNReal.ofReal_lt_ofReal_iff hε).1 (h1.trans_lt hd)
  have hVC : V ∈ Tower.FullSpace.fieldsValuedIn L k j PeriodicLattice.complexGaugeGroup :=
    ⟨fun b => (Matrix.mem_specialUnitaryGroup_iff.1 (hVc.1 b)).2, hVc.2⟩
  have hp : V ∈ Tower.FullSpace.nearIdentityPolydisc L k j (polydiscRadius L) c :=
    ⟨⟨fun b _ => hVC.1 b, fun b _ => hVC.2 b⟩,
      fun b _ => (hball b).trans_le (min_le_left _ _)⟩
  have hd4 : supDistOne V < ENNReal.ofReal (Averaging.smoothingRadius L / 4) :=
    hd.trans_le (ENNReal.ofReal_le_ofReal (min_le_right _ _))
  have hdom : V ∈ smoothingDomain L k j := by
    refine ⟨hVc, fun c' hc' => ?_⟩
    have h := hM L k (j + 1) hL hk (by omega) hj V hVc hd4 c' hc'
    refine ⟨h.1, ?_⟩
    have e : complexSmoothing L V c' = complexSmoothingPositive L V c' := if_pos hc'
    rw [← e]
    exact h.2.1
  refine ⟨hp, hdom, fun B hB => ?_⟩
  have hBC := mem_complexEdgeForms_of_mem hB
  have hleft := hasLeftCurves_unbounded G hA hL hj.le hVC hBC.1
  have hholo := (hP L hL k j hj).2 c hc
  have hev := MeanData.eventually_twist_mem_polydisc (D := unboundedData L k) G hj hc
    (isField_of_mem hVC) hp hleft
  have hdA : DifferentiableAt ℂ (fun t : ℂ =>
      complexSmoothing L (Tower.FullSpace.expTwist (t • B) V) c) 0 :=
    differentiableAt_twist H G hA hP hL hj hc hVC hp hBC
      (a := fun W => complexSmoothing L W c) (G.mean_extend j hj c hc)
      (by
        obtain ⟨inst, h⟩ := hholo.holomorphic_smoothing
        exact ⟨inst, h.entries⟩)
  have hdC : DifferentiableAt ℂ (fun t : ℂ =>
      Tower.FullSpace.complexContourMean L (Tower.FullSpace.expTwist (t • B) V) y x) 0 :=
    differentiableAt_twist H G hA hP hL hj hc hVC hp hBC
      (a := fun W => Tower.FullSpace.complexContourMean L W y x)
      (fun V' hV' => complexContourMean_congr hS hQ hL hk hj hc hy hx hV'
        (MeanData.polydisc_congr (D := unboundedData L k) (G.opp_mem j hj c hc) hV'
          (G.eq_extend j hj c hc V' hV')) (G.eq_extend j hj c hc V' hV'))
      (by
        obtain ⟨inst, h⟩ := hholo.holomorphic_contourMean y hy x hx
        exact ⟨inst, h.entries⟩)
  exact ⟨tendsto_ofReal_nhds_zero.eventually hev,
    ⟨_, hasDerivAt_ofReal_of_complex hdA.hasDerivAt⟩,
    ⟨_, hasDerivAt_ofReal_of_complex hdC.hasDerivAt⟩⟩
end Unbounded
section FiniteSide
variable {L n k : ℕ}
theorem mem_nhdsWithin_of_isOpenNhdOfOne (hE6 : BondSetFields.ProductStructureHolds)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) {j : ℕ} (hj : j ≤ k)
    {𝒰 : Set (Edge L n k j → ComplexMatrix2)} (h : IsOpenNhdOfOne 𝒰) :
    𝒰 ∈ 𝓝[fieldSpace L n k j] (fun _ => (1 : ComplexMatrix2)) := by
  obtain ⟨⟨hsub, hopen⟩, h1⟩ := h
  have hAll := ((hE6 L hL k j hj).1 n hn).2
  obtain ⟨O₀, hO₀, he⟩ := (hAll.2.2.2.2.2.2.2.1 _ hsub).2 hopen
  have h1' : (fun _ => (1 : ComplexMatrix2)) ∈ 𝒰 := h1
  rw [he] at h1'
  refine mem_nhdsWithin.2 ⟨O₀, hO₀, h1'.1, fun V hV => ?_⟩
  rw [he]
  exact hV
theorem setOf_norm_lt_mem_nhds (hE6 : BondSetFields.ProductStructureHolds)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) {j : ℕ} (hj : j ≤ k) {r : ℝ}
    (hr : 0 < r) :
    {V : Edge L n k j → ComplexMatrix2 | ∀ b, ComplexMatrix2.operatorNorm (V b - 1) < r} ∈
      𝓝 (fun _ => (1 : ComplexMatrix2)) := by
  have hAll := ((hE6 L hL k j hj).1 n hn).2
  have : Finite (Edge L n k j) := Set.finite_univ_iff.1 hAll.1
  have hopen : IsOpen (⋂ b : Edge L n k j,
      {V : Edge L n k j → ComplexMatrix2 | ComplexMatrix2.operatorNorm (V b - 1) < r}) := by
    refine isOpen_iInter_of_finite fun b => ?_
    have hcb : Continuous fun V : Edge L n k j → ComplexMatrix2 => V b := continuous_apply b
    exact (isOpen_operatorNorm_sub_one_lt (r := r)).preimage hcb
  have hm : (fun _ => (1 : ComplexMatrix2)) ∈ ⋂ b : Edge L n k j,
      {V : Edge L n k j → ComplexMatrix2 | ComplexMatrix2.operatorNorm (V b - 1) < r} := by
    refine mem_iInter.2 fun b => ?_
    simpa using hr
  refine mem_of_superset (hopen.mem_nhds hm) fun V hV b => ?_
  exact mem_iInter.1 hV b
theorem tendsto_smoothingStep (hE6 : BondSetFields.ProductStructureHolds)
    (hB1 : SmoothingNearTrivialField)
    (hS : SmoothingNearIdentity)
    (hSch : PeriodicLattice.AveragingSchemeProperties)
    (hP : DoubleBlockPolydisc.PolydiscsHold)
    (hGF : AxialFunctionFacts.statement)
    (G : (periodicData L n k).Admissible k)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hk : 1 ≤ k) {j : ℕ}
    (hj : j < k) :
    Tendsto (smoothingStep L n k j) (𝓝[fieldSpace L n k j] fun _ => 1)
      (𝓝[fieldSpace L n k (j + 1)] fun _ => 1) := by
  have hmaps : ∀ᶠ V in 𝓝[fieldSpace L n k j] (fun _ => (1 : ComplexMatrix2)),
      smoothingStep L n k j V ∈ fieldSpace L n k (j + 1) := by
    obtain ⟨𝒰, hU, han, _⟩ := ((hS.1 L hL).1 n k j hn hj).1.analytic
    filter_upwards [mem_nhdsWithin_of_isOpenNhdOfOne hE6 hL hn hj.le hU] with V hV
    exact han.2.1 hV
  have hpos : ∀ c : Edge L n k (j + 1), c.IsPositivelyOriented →
      Tendsto (fun V => smoothingStep L n k j V c) (𝓝[fieldSpace L n k j] fun _ => 1)
        (𝓝 1) := by
    intro c hc
    obtain ⟨O₁, hO₁, h1, hgood⟩ := exists_open_nhd_one hE6 hB1 hS hL hn hk hj
    obtain ⟨inst, hΦ⟩ := ((hP L hL k j hj).1 n hn c hc).holomorphic_smoothing
    have hcont := (hΦ.toUnimodular tracelessBasis).2.2.1
    have h1c : (fun _ => (1 : ComplexMatrix2)) ∈ fieldSpace L n k j := by
      have h := ((hB1 L n k hL hn hk).1 j hj).1
      exact h.1.1 h.2
    have hfacts : ∀ V ∈ O₁, V ∈ fieldSpace L n k j → _ := fun V hV hVc =>
      facts_near_one hB1 hSch hL hn hk hj hc (hgood V hV hVc).1 (hgood V hV hVc).2
    let φ : (Edge L n k j → ComplexMatrix2) → positiveDoubleBlockBonds c ⊕ Empty → ComplexMatrix2 :=
      fun V => asGroupFactors fun b => V b.1
    have hφ : Continuous φ :=
      continuous_asGroupFactors.comp (continuous_pi fun b => continuous_apply _)
    have hin : ∀ V ∈ O₁, V ∈ fieldSpace L n k j →
        φ V ∈ leftComponents ⁻¹' polydiscPositive (polydiscRadius L) c :=
      fun V hV hVc => ⟨_, ⟨V, (hfacts V hV hVc).1, rfl⟩, rfl⟩
    have hw := hcont _ (hin _ h1 h1c)
    have hT : Tendsto φ (𝓝[fieldSpace L n k j] fun _ => 1)
        (𝓝[leftComponents ⁻¹' polydiscPositive (polydiscRadius L) c]
          (φ fun _ => 1)) := by
      refine tendsto_nhdsWithin_iff.2 ⟨(hφ.tendsto _).mono_left nhdsWithin_le_nhds, ?_⟩
      filter_upwards [mem_nhdsWithin.2 ⟨O₁, hO₁, h1, fun V hV => hV⟩] with V hV
      exact hin V hV.1 hV.2
    have hval : ((fun v => PeriodicLattice.complexBlockAverage
        (DoubleBlockPolydisc.fieldOfValues c v) c) ∘ leftComponents) (φ fun _ => 1) = 1 := by
      have e1 := G.mean_extend j hj c hc _ (hfacts _ h1 h1c).1
      have e2 := (hfacts _ h1 h1c).2.1
      have e3 := congrFun (hGF L n k j hL hn hj).smoothingStep_trivial c
      exact e1.symm.trans (e2.trans e3)
    have hlim := hw.tendsto.comp hT
    rw [hval] at hlim
    refine hlim.congr' ?_
    filter_upwards [mem_nhdsWithin.2 ⟨O₁, hO₁, h1, fun V hV => hV⟩] with V hV
    have e1 := G.mean_extend j hj c hc _ (hfacts V hV.1 hV.2).1
    have e2 := (hfacts V hV.1 hV.2).2.1
    exact e1.symm.trans e2
  refine tendsto_nhdsWithin_iff.2 ⟨tendsto_pi_nhds.2 fun c => ?_, hmaps⟩
  by_cases hc : c.IsPositivelyOriented
  · exact hpos c hc
  · have hr : c.opposite.IsPositivelyOriented := G.pos_opp_of_not_pos hj hc
    have h2 : Tendsto (fun V => (smoothingStep L n k j V c.opposite).adjugate)
        (𝓝[fieldSpace L n k j] fun _ => 1) (𝓝 ((1 : ComplexMatrix2).adjugate)) :=
      (Continuous.matrix_adjugate continuous_id).continuousAt.tendsto.comp (hpos _ hr)
    rw [Matrix.adjugate_one] at h2
    refine h2.congr' ?_
    filter_upwards [hmaps] with V hV
    have h3 : smoothingStep L n k j V c = (smoothingStep L n k j V c.opposite)⁻¹ :=
      hV.2 c.opposite (mem_univ _)
    rw [h3, MeanData.inv_eq_adjugate_of_mem
      (Matrix.mem_specialUnitaryGroup_iff.1 (hV.1 _ (mem_univ _))).2]
theorem tendsto_smoothingIter (hE6 : BondSetFields.ProductStructureHolds)
    (hB1 : SmoothingNearTrivialField)
    (hS : SmoothingNearIdentity)
    (hSch : PeriodicLattice.AveragingSchemeProperties)
    (hP : DoubleBlockPolydisc.PolydiscsHold)
    (hGF : AxialFunctionFacts.statement)
    (G : (periodicData L n k).Admissible k)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hk : 1 ≤ k) :
    ∀ i ≤ k, Tendsto (smoothingIter L n k i) (𝓝[fieldSpace L n k 0] fun _ => 1)
      (𝓝[fieldSpace L n k i] fun _ => 1) := by
  intro i
  induction i with
  | zero => exact fun _ => tendsto_id
  | succ i ih =>
    intro hi
    exact (tendsto_smoothingStep hE6 hB1 hS hSch hP hGF G hL hn hk hi).comp
      (ih (Nat.le_of_succ_le hi))
end FiniteSide
section FiniteSide
variable {L n k : ℕ}
def IteratesStayNear (L n k : ℕ) (U : Edge L n k 0 → ComplexMatrix2) : Prop :=
  ∀ i ∈ Iic k, smoothingIter L n k i U ∈ fieldSpace L n k i ∧
    (∀ b, ComplexMatrix2.operatorNorm (smoothingIter L n k i U b - 1) < polydiscRadius L) ∧
    (i < k → smoothingIter L n k i U ∈ commonSmoothingDomain L n k i)
theorem eventually_iteratesStayNear (hE6 : BondSetFields.ProductStructureHolds)
    (hB1 : SmoothingNearTrivialField)
    (hS : SmoothingNearIdentity)
    (hI : ∀ i ≤ k, Tendsto (smoothingIter L n k i) (𝓝[fieldSpace L n k 0] fun _ => 1)
      (𝓝[fieldSpace L n k i] fun _ => 1))
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hk : 1 ≤ k) :
    ∀ᶠ U in 𝓝[fieldSpace L n k 0] (fun _ => (1 : ComplexMatrix2)), IteratesStayNear L n k U := by
  refine (eventually_all_finite (finite_Iic k)).2 fun i hi => ?_
  have hρ : 0 < polydiscRadius L := (hS.1 L hL).2.2.pos
  have hT := hI i hi
  have h1 := (tendsto_nhdsWithin_iff.1 hT).2
  have h2 := (tendsto_nhdsWithin_iff.1 hT).1.eventually
    (setOf_norm_lt_mem_nhds hE6 hL hn hi hρ)
  by_cases hik : i < k
  · have h3 := hT (mem_nhdsWithin_of_isOpenNhdOfOne hE6 hL hn hi
      ((hB1 L n k hL hn hk).1 i hik).1)
    filter_upwards [h1, h2, h3] with U a b c
    exact ⟨a, b, fun _ => c⟩
  · filter_upwards [h1, h2] with U a b
    exact ⟨a, b, fun h => absurd h hik⟩
theorem levelwise_eq_smoothingIter (hB1 : SmoothingNearTrivialField)
    (hSch : PeriodicLattice.AveragingSchemeProperties)
    (G : (periodicData L n k).Admissible k)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hk : 1 ≤ k)
    {U : Edge L n k 0 → ComplexMatrix2} (hU : IteratesStayNear L n k U) :
    ∀ i ≤ k, ∀ c : Edge L n k i, levelwiseMean U i c = some (smoothingIter L n k i U c) := by
  have hfam : IsMeanSequence k fun i => smoothingIter L n k i U := by
    refine ⟨fun i hi => mem_fieldsIn_of_mem (hU i hi).1, fun i hi b => (hU i hi.le).2.1 b,
      fun i hi c hc => ?_⟩
    exact (facts_near_one hB1 hSch hL hn hk hi hc ((hU i hi.le).2.2 hi)
      (hU i hi.le).2.1).2.1.symm
  exact levelwise_eq_periodic G k le_rfl _ hfam
theorem I_smul_logDirectionalDeriv_eq {φ : (Edge L n k 0 → ComplexMatrix2) → ComplexMatrix2}
    {W : ComplexMatrix2} {B : Edge L n k 0 → ComplexMatrix2} {g : ℂ → ComplexMatrix2}
    {d : ComplexMatrix2} (h : HasDerivAt g d 0)
    (he : (fun t : ℝ => ComplexMatrix2.logSeries (φ ((t : ℂ) • B) * W⁻¹)) =ᶠ[𝓝 0]
      fun t : ℝ => g t) :
    Complex.I • logDirectionalDeriv ℝ φ W B = d := by
  have h' : HasDerivAt g d (((0 : ℝ) : ℂ)) := by simpa using h
  have h3 := HasDerivAt.scomp (𝕜 := ℝ) (𝕜' := ℂ) (0 : ℝ) h' Complex.ofRealCLM.hasDerivAt
  have h4 := h3.congr_of_eventuallyEq he
  unfold logDirectionalDeriv
  simp only [Complex.coe_algebraMap]
  rw [h4.deriv]
  simp [smul_smul]
theorem differentiableAt_representation (H : ExpChartHolomorphy.ExpChartTheory)
    (hA : LeftChartFields.Claim)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) {i : ℕ}
    {c : Edge L n k i} {U : Edge L n k 0 → ComplexMatrix2}
    (hUC : U ∈ fieldsIn L n k 0 PeriodicLattice.complexGaugeGroup)
    {B : Edge L n k 0 → ComplexMatrix2} (hBC : B ∈ complexEdgeForms L n k 0)
    {F : Finset (Edge L n k 0)} {O : Set (F → ComplexMatrix2)}
    {f : (F → ComplexMatrix2) → ComplexMatrix2}
    (w : IsHolomorphicRepresentation i c U F O f) :
    DifferentiableAt ℂ (fun t : ℂ => f (expChartPoint F (t • B) U)) 0 := by
  have hne : Nonempty F := w.nonempty.to_subtype
  have hlev : (finiteData L n k 0).HolomorphicGradientExists :=
    ((hA.2.2 L k 0 hL (Nat.zero_le k)).1 n hn).1.2.2.2
  have hent : ∀ (β : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless) (r s : Fin 2),
      IsHolomorphicToCoords β scalarChart (leftComponents ⁻¹' O)
        fun p => f (leftComponents p) r s := by
    intro β r s
    have h := isHolomorphicToCoords_entry H (w.holomorphic β) r s
    rw [image_asGroupFactors] at h
    exact h
  exact differentiableAt_along_leftChart H hlev (Λ := finiteData L n k 0) (σ := F)
    (fun s => (⟨s.1, w.positive s.1 s.2⟩ : PositiveEdge L n k 0)) w.isOpen (Φ := f) hent hUC
    w.mem hBC
theorem mem_unitDeterminant_of_representation {σ : Type} [Fintype σ]
    {O : Set (σ → ComplexMatrix2)} {f : (σ → ComplexMatrix2) → ComplexMatrix2}
    {β : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless}
    (h : IsHolomorphicToUnimodular β (asGroupFactors '' O) fun p => f fun b => p (.inl b))
    {w : σ → ComplexMatrix2} (hw : w ∈ O) : f w ∈ ComplexMatrix2.unitDeterminant := by
  have hp : asGroupFactors w ∈ asGroupFactors '' O := mem_image_of_mem _ hw
  have h3 := h.2.1 hp
  have e : (fun b => asGroupFactors w (Sum.inl b)) = w := rfl
  simp only [e] at h3
  exact h3
theorem differentiableAt_log_of_curve {ρ₀ : ℝ} (hlog : CurveLogDerivative ℂ (Metric.ball 0 ρ₀)
      PeriodicLattice.complexGaugeGroup PeriodicLattice.complexLieAlgebra)
    {W : ℂ → ComplexMatrix2} {d : ComplexMatrix2}
    (hmem : MapsTo W (Metric.ball 0 ρ₀) PeriodicLattice.complexGaugeGroup)
    (hd : HasDerivAt W d 0) :
    DifferentiableAt ℂ (fun t => ComplexMatrix2.logSeries (W t * (W 0)⁻¹)) 0 :=
  (hlog W hmem hd.differentiableAt).2.1
theorem differentiableAt_log_representation (hA : LeftChartFields.Claim)
    {i : ℕ} {c : Edge L n k i} {U : Edge L n k 0 → ComplexMatrix2}
    {B : Edge L n k 0 → ComplexMatrix2}
    {F : Finset (Edge L n k 0)} {O : Set (F → ComplexMatrix2)}
    {f : (F → ComplexMatrix2) → ComplexMatrix2}
    (w : IsHolomorphicRepresentation i c U F O f)
    (hg : DifferentiableAt ℂ (fun t : ℂ => f (expChartPoint F (t • B) U)) 0)
    (hal : ∀ᶠ t : ℂ in 𝓝 0, expChartPoint F (t • B) U ∈ O) :
    DifferentiableAt ℂ (fun t : ℂ =>
      ComplexMatrix2.logSeries (f (expChartPoint F (t • B) U) * (f (edgeEntries F U))⁻¹)) 0 := by
  obtain ⟨ρ₀, hρ₀, hball⟩ := Metric.eventually_nhds_iff_ball.1 hal
  have hmaps : MapsTo (fun t : ℂ => f (expChartPoint F (t • B) U)) (Metric.ball 0 ρ₀)
      PeriodicLattice.complexGaugeGroup := by
    intro t ht
    exact mem_unitDeterminant_of_representation (w.holomorphic tracelessBasis) (hball t ht)
  have hchart0 : expChartPoint F ((0 : ℂ) • B) U = edgeEntries F U := by
    funext b
    simp [expChartPoint, edgeEntries, NormedSpace.exp_zero]
  have hdl := differentiableAt_log_of_curve (hA.2.1 ρ₀ hρ₀) hmaps hg.hasDerivAt
  simp only [hchart0] at hdl
  exact hdl
theorem exists_deriv_representation (H : ExpChartHolomorphy.ExpChartTheory)
    (hA : LeftChartFields.Claim)
    (hB1 : SmoothingNearTrivialField)
    (hSch : PeriodicLattice.AveragingSchemeProperties)
    (G : (periodicData L n k).Admissible k)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hk : 1 ≤ k) {i : ℕ}
    (hi : i ≤ k) {c : Edge L n k i} (hc : c.IsPositivelyOriented)
    {U : Edge L n k 0 → ComplexMatrix2}
    (hU0 : U ∈ fieldSpace L n k 0)
    (hform : levelwiseMean U i c = some (smoothingIter L n k i U c))
    (hnear : ∀ᶠ x in 𝓝[fieldSpace L n k 0] U, IteratesStayNear L n k x)
    {B : Edge L n k 0 → ComplexMatrix2} (hB : B ∈ edgeFormSpace L n k 0)
    {F : Finset (Edge L n k 0)} {O : Set (F → ComplexMatrix2)}
    {f : (F → ComplexMatrix2) → ComplexMatrix2}
    (w : IsHolomorphicRepresentation i c U F O f) :
    ∃ D : ComplexMatrix2,
      HasDerivAt (fun t : ℂ => ComplexMatrix2.logSeries
        (f (expChartPoint F (t • B) U) * (f (edgeEntries F U))⁻¹)) D 0 ∧
      HasDerivAt (fun t : ℝ => ComplexMatrix2.logSeries (smoothingIter L n k i
        (PeriodicLattice.expTwist ((t : ℂ) • B) U) c * (smoothingIter L n k i U c)⁻¹)) D 0 ∧
      Complex.I • leftDifferential (smoothingIter L n k i) U B c = D := by
  have hUC := mem_fieldsIn_of_mem hU0
  have hBC := mem_complexEdgeForms_of_mem hB
  have hleft := hasLeftCurves_periodic G hA hL hn (Nat.zero_le k) hUC hBC.1
  have hal : ∀ᶠ t : ℂ in 𝓝 0, expChartPoint F (t • B) U ∈ O ∧
      (periodicData L n k).levelwise (PeriodicLattice.expTwist (t • B) U) i c =
        some (f (expChartPoint F (t • B) U)) :=
    (representation_ofPeriodic w).eventually_along G hleft
  have hg := differentiableAt_representation H hA hL hn hUC hBC w
  have hdl' := differentiableAt_log_representation hA w hg (hal.mono fun _ h => h.1)
  have hD := hdl'.hasDerivAt
  have hiter : smoothingIter L n k i U c = f (edgeEntries F U) :=
    Option.some.inj (hform.symm.trans (w.eq_some U hUC w.mem))
  have hconf : ∀ t : ℝ, PeriodicLattice.expTwist ((t : ℂ) • B) U ∈ fieldSpace L n k 0 :=
    fun t => (hB1 L n k hL hn hk).2 0 (Nat.zero_le k) _ (ofReal_smul_mem_edgeFormSpace hB t) U hU0
  have hT : Tendsto (fun t : ℝ => PeriodicLattice.expTwist ((t : ℂ) • B) U) (𝓝 0)
      (𝓝[fieldSpace L n k 0] U) :=
    tendsto_nhdsWithin_iff.2 ⟨(MeanData.tendsto_twist (D := periodicData L n k) G
      (Nat.zero_le k) (isField_of_mem hUC) hleft).comp tendsto_ofReal_nhds_zero,
      Eventually.of_forall hconf⟩
  have he : (fun t : ℝ => ComplexMatrix2.logSeries (smoothingIter L n k i
      (PeriodicLattice.expTwist ((t : ℂ) • B) U) c * (smoothingIter L n k i U c)⁻¹)) =ᶠ[𝓝 0]
      fun t : ℝ => (fun t : ℂ =>
        ComplexMatrix2.logSeries (f (expChartPoint F (t • B) U) * (f (edgeEntries F U))⁻¹)) t := by
    filter_upwards [hT.eventually hnear, tendsto_ofReal_nhds_zero.eventually hal] with t h1 h2
    have e1 := levelwise_eq_smoothingIter hB1 hSch G hL hn hk h1 i hi c
    have e2 : levelwiseMean (PeriodicLattice.expTwist ((t : ℂ) • B) U) i c =
        some (f (expChartPoint F ((t : ℂ) • B) U)) :=
      (congrFun (periodicData_levelwise _ i) c).symm.trans h2.2
    have e3 := Option.some.inj (e1.symm.trans e2)
    simp only [e3, hiter]
  refine ⟨_, hD, (hasDerivAt_ofReal_of_complex hD).congr_of_eventuallyEq he, ?_⟩
  have hmd : leftDifferential (smoothingIter L n k i) U B c =
      logDirectionalDeriv ℝ
        (fun X => smoothingIter L n k i (PeriodicLattice.expTwist X U) c)
        (smoothingIter L n k i U c) B := by
    simp only [leftDifferential, extendOddly, if_pos hc]
  rw [hmd]
  exact I_smul_logDirectionalDeriv_eq hD he
theorem iteratesDefinedNearIdentity_periodic (H : ExpChartHolomorphy.ExpChartTheory)
    (hm : ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (hA : LeftChartFields.Claim)
    (hE6 : BondSetFields.ProductStructureHolds)
    (hB1 : SmoothingNearTrivialField)
    (hS : SmoothingNearIdentity)
    (hSch : PeriodicLattice.AveragingSchemeProperties)
    (hI : ∀ i ≤ k, Tendsto (smoothingIter L n k i) (𝓝[fieldSpace L n k 0] fun _ => 1)
      (𝓝[fieldSpace L n k i] fun _ => 1))
    (G : (periodicData L n k).Admissible k)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hk : 1 ≤ k) :
    IteratesDefinedNearIdentity L n k := by
  have hE := eventually_iteratesStayNear hE6 hB1 hS hI hL hn hk
  have hall := (eventually_eventually_nhdsWithin.2 hE).and
    (hE.and (eventually_mem_nhdsWithin (a := fun _ => (1 : ComplexMatrix2))
      (s := fieldSpace L n k 0)))
  refine hall.mono ?_
  rintro U ⟨hnear, hU, hU0⟩ i hi
  have hform := levelwise_eq_smoothingIter hB1 hSch G hL hn hk hU
  refine ⟨(hU i hi).1, (hU i hi).2.1, hform i hi, fun B hB c hc => ?_⟩
  obtain ⟨F, O, f, w⟩ := exists_representation_periodic G H hm i hi c U (mem_fieldsIn_of_mem hU0)
    (by
      show (levelwiseMean U i c).isSome
      rw [hform i hi c]
      rfl)
  obtain ⟨D, _, h2, h3⟩ := exists_deriv_representation H hA hB1 hSch G hL hn hk hi hc hU0
    (hform i hi c) hnear hB w
  refine ⟨h3 ▸ h2, fun F' O' f' w' => ?_⟩
  obtain ⟨D', h1', _, h3'⟩ := exists_deriv_representation H hA hB1 hSch G hL hn hk hi hc hU0
    (hform i hi c) hnear hB w'
  exact h3' ▸ h1'
end FiniteSide
theorem levelwiseMeansHold (H : ExpChartHolomorphy.ExpChartTheory)
    (hm : ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (hE : PeriodicLattice.BondEndpointsOrientation.Statement)
    (hP : DoubleBlockPolydisc.PolydiscsHold)
    (hS : SmoothingNearIdentity)
    (hV : ComplexMeanLiesInComplexGaugeGroup)
    (hR : PeriodicLattice.ComplexAverageIsLocal)
    (hA : LeftChartFields.Claim)
    (hE6 : BondSetFields.ProductStructureHolds)
    (hB1 : SmoothingNearTrivialField)
    (hSch : PeriodicLattice.AveragingSchemeProperties)
    (hBP : PeriodicLattice.DoubleBlockStructure.Statement)
    (hGF : AxialFunctionFacts.statement)
    (hQ : SublatticesSymmetriesScalingsAndProjections.Statement)
    (hM : Tower.FullSpace.SmoothingNearIdentity) :
    LevelwiseMeansHold := by
  intro L hL k hk
  refine ⟨fun n hn => ?_, ?_⟩
  · have G := periodicData_admissible hE hP hS hV hR hL hn hk
    have hI := tendsto_smoothingIter hE6 hB1 hS hSch hP hGF G hL hn hk
    exact ⟨agreesNearIdentity_periodic H G hA hP hE6 hB1 hS hSch hBP hL hn hk,
      levelwise_eq_periodic G, exists_representation_periodic G H hm,
      representsAlongCurves_periodic G hA hL hn, hI,
      iteratesDefinedNearIdentity_periodic H hm hA hE6 hB1 hS hSch hI G hL hn hk⟩
  · have G := Unbounded.unboundedData_admissible hP hS hV hQ hL hk
    exact ⟨Unbounded.realAndComplexAgree_unbounded H G hA hP hS hQ hM hL hk,
      Unbounded.levelwise_eq_unbounded G, Unbounded.exists_representation_unbounded G H hm,
      Unbounded.representsAlongCurves_unbounded G hA hL⟩
end YangMills.Construction.Tower.LevelwiseMeans
end
