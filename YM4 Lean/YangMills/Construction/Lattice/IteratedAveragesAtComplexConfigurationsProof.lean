import YangMills.Construction.Lattice.BondsWithTheirReverses
import YangMills.Construction.Lattice.AveragesAndIteratesAreConfigurations
import YangMills.Construction.Lattice.ComplexBondwiseIteratesAreFormedByTheBondwiseMaps
import YangMills.Construction.Lattice.IteratedAveragesAtComplexConfigurations
import YangMills.Construction.Lattice.PositiveOneOfABondAndItsReverse
import YangMills.Construction.Towers.ComplexAveragesFormedLevelByLevelProof
import Mathlib
set_option autoImplicit false
open Set Filter
open scoped Topology
noncomputable section
namespace YangMills.Construction
open Matrices Matrices.GroupLieProduct Coordinates
namespace PeriodicLattice.ComplexIteratedAverages
section Coordinates
open Coordinates.ComplexCoordinates
theorem isHolomorphicIn_coordSelection {N N' : ℕ} (τ : Fin N' → Fin N) :
    IsHolomorphicIn univ (fun (z : ComplexCoordinates N) (t : Fin N') => z (τ t)) := by apply _root_.YangMills.Construction.Tower.LevelwiseMeans.isHolomorphicIn_proj <;> assumption
theorem isHolomorphicIn_congr {N N' : ℕ} {O : Set (ComplexCoordinates N)}
    {f g : ComplexCoordinates N → ComplexCoordinates N'} (h : IsHolomorphicIn O f)
    (hfg : ∀ z ∈ O, f z = g z) : IsHolomorphicIn O g := by apply _root_.YangMills.Construction.Averaging.ComplexLogMean.isHolomorphicIn_congr <;> assumption
variable {σ : Type}
def entryPosition {k : ℕ} (ν : σ ≃ Fin k) (i : σ) (t : Fin 4) :
    Fin (productDim fun _ : Fin k => Component.matrix) :=
  finSigmaFinEquiv (n := fun i => ((fun _ : Fin k => Component.matrix) i).dim) ⟨ν i, t⟩
theorem matrixEquiv_matrixPiEquiv_symm {k : ℕ} (ν : σ ≃ Fin k) (z) (i : σ) (t : Fin 4) :
    matrixEquiv ((matrixPiEquiv ν).symm z i) t = z (entryPosition ν i t) := by apply _root_.YangMills.Construction.Tower.LevelwiseMeans.matrixEquiv_matrixPiEquiv_symm <;> assumption
theorem isHolomorphicVia_mul_components (hm : ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    {k : ℕ} (ν : σ ≃ Fin k) (i i' : σ) :
    IsHolomorphicVia (matrixPiEquiv ν) matrixEquiv univ
      fun p => p i * p i' := by
  have hmul := hm.2.2.1
  unfold IsHolomorphicVia at hmul ⊢
  rw [image_univ_of_surjective (matrixPiEquiv ν).surjective]
  rw [image_univ_of_surjective matrixPairEquiv.surjective] at hmul
  let pos : Fin (productDim matrixPairComponents) → (a : Fin 2) × Fin 4 := fun u =>
    (finSigmaFinEquiv (n := fun a => (matrixPairComponents a).dim)).symm u
  let τ : Fin (productDim matrixPairComponents) → _ := fun u =>
    entryPosition ν (![i, i'] (pos u).1) (pos u).2
  have hsel := isHolomorphicIn_coordSelection τ
  have hc := ((hm.1 _ _ isOpen_univ).1 4 _ hmul).2.2.2.1 _ _ _ hsel (mapsTo_univ _ _)
  refine isHolomorphicIn_congr hc fun z _ => ?_
  have e : (fun u => z (τ u)) = matrixPairEquiv
      ((matrixPiEquiv ν).symm z i, (matrixPiEquiv ν).symm z i') := by
    funext u
    have hk : ∀ X Y : ComplexMatrix2, matrixPairEquiv (X, Y) u =
        matrixEquiv (![X, Y] (pos u).1) (pos u).2 := fun _ _ => rfl
    rw [hk]
    change z (entryPosition ν (![i, i'] (pos u).1) (pos u).2) = _
    refine (matrixEquiv_matrixPiEquiv_symm ν z _ _).symm.trans ?_
    generalize pos u = x
    obtain ⟨a, t⟩ := x
    fin_cases a <;> rfl
  simp only [Function.comp_apply, e, Equiv.symm_apply_apply]
end Coordinates
section Rules
open Coordinates.ComplexCoordinates
variable {ι ι' : Type} [Fintype ι] [Fintype ι']
omit [Fintype ι] [Fintype ι'] in
theorem mem_groupLieProduct_iff {p : ι ⊕ Empty → ComplexMatrix2} :
    p ∈ GroupLieProduct ι Empty ↔ ∀ i, p (.inl i) ∈ ComplexMatrix2.unitDeterminant := by apply _root_.YangMills.Construction.Tower.LevelwiseMeans.mem_groupLieProduct_empty <;> assumption
theorem inv_mem_unitDeterminant {X : ComplexMatrix2} (h : X ∈ ComplexMatrix2.unitDeterminant) :
    X⁻¹ ∈ ComplexMatrix2.unitDeterminant := by apply _root_.YangMills.SharedProofs.p413 <;> assumption
theorem mul_mem_unitDeterminant {X Y : ComplexMatrix2} (h : X ∈ ComplexMatrix2.unitDeterminant)
    (h' : Y ∈ ComplexMatrix2.unitDeterminant) : X * Y ∈ ComplexMatrix2.unitDeterminant := by apply _root_.YangMills.SharedProofs.p36859 <;> assumption
theorem inv_inv_of_mem_unitDeterminant {X : ComplexMatrix2}
    (h : X ∈ ComplexMatrix2.unitDeterminant) : X⁻¹⁻¹ = X := by apply _root_.YangMills.Construction.Tower.LevelwiseMeans.inv_inv_of_mem_unitDeterminant <;> assumption
variable (H : ExpChartHolomorphy.ExpChartTheory)
  (hm : ComplexCoordinates.PowerSeriesHolomorphy.Properties)
  (β : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless)
include H
theorem isHolomorphicToUnimodular_of_via {k : ℕ} (ν : ι ⊕ Empty ≃ Fin k)
    {O : Set (ι ⊕ Empty → ComplexMatrix2)} {F : (ι ⊕ Empty → ComplexMatrix2) → ComplexMatrix2}
    (hF : IsHolomorphicVia (matrixPiEquiv ν) matrixEquiv O F)
    (hv : MapsTo F (O ∩ GroupLieProduct ι Empty) ComplexMatrix2.unitDeterminant) :
    IsHolomorphicToUnimodular β (O ∩ GroupLieProduct ι Empty) F := by apply _root_.YangMills.Construction.Tower.LevelwiseMeans.isHolomorphicToUnimodular_of_via <;> assumption
theorem isHolomorphicToUnimodular_component {W : Set (ι ⊕ Empty → ComplexMatrix2)}
    (hW : ComplexMatrix2.IsRelativelyOpen (GroupLieProduct ι Empty) W) (i : ι) :
    IsHolomorphicToUnimodular β W fun p => p (.inl i) := by apply _root_.YangMills.Construction.Tower.LevelwiseMeans.isHolomorphicToUnimodular_component <;> assumption
theorem isHolomorphicToUnimodular_comp {W : Set (ι ⊕ Empty → ComplexMatrix2)}
    {Ψ : (ι ⊕ Empty → ComplexMatrix2) → ι' ⊕ Empty → ComplexMatrix2}
    (hΨ : IsHolomorphicToProduct β W Ψ)
    {W' : Set (ι' ⊕ Empty → ComplexMatrix2)} {Φ : (ι' ⊕ Empty → ComplexMatrix2) → ComplexMatrix2}
    (hΦ : IsHolomorphicToUnimodular β W' Φ) :
    IsHolomorphicToUnimodular β (W ∩ Ψ ⁻¹' W') (Φ ∘ Ψ) := by apply _root_.YangMills.Construction.Tower.LevelwiseMeans.isHolomorphicToUnimodular_comp <;> assumption
theorem isHolomorphicToUnimodular_mono {W W' : Set (ι ⊕ Empty → ComplexMatrix2)}
    {Φ : (ι ⊕ Empty → ComplexMatrix2) → ComplexMatrix2}
    (hΦ : IsHolomorphicToUnimodular β W' Φ)
    (hW : ComplexMatrix2.IsRelativelyOpen (GroupLieProduct ι Empty) W)
    (hs : W ⊆ W') : IsHolomorphicToUnimodular β W Φ := by apply _root_.YangMills.Construction.Tower.LevelwiseMeans.isHolomorphicToUnimodular_mono <;> assumption
omit H in
theorem isHolomorphicToUnimodular_congr {W : Set (ι ⊕ Empty → ComplexMatrix2)}
    {Φ Φ' : (ι ⊕ Empty → ComplexMatrix2) → ComplexMatrix2}
    (hΦ : IsHolomorphicToUnimodular β W Φ) (he : ∀ p ∈ W, Φ p = Φ' p) :
    IsHolomorphicToUnimodular β W Φ' := by apply _root_.YangMills.Construction.Tower.LevelwiseMeans.isHolomorphicToUnimodular_congr <;> assumption
omit H in
theorem isHolomorphicToUnimodular_empty (Φ : (ι ⊕ Empty → ComplexMatrix2) → ComplexMatrix2) :
    IsHolomorphicToUnimodular β ∅ Φ := by
  refine ⟨⟨∅, isOpen_empty, by simp⟩, mapsTo_empty _ _, continuousOn_empty _,
    fun p hp => hp.elim⟩
include hm
theorem isHolomorphicToUnimodular_inv {W : Set (ι ⊕ Empty → ComplexMatrix2)}
    {Φ : (ι ⊕ Empty → ComplexMatrix2) → ComplexMatrix2}
    (hΦ : IsHolomorphicToUnimodular β W Φ) :
    IsHolomorphicToUnimodular β W fun p => (Φ p)⁻¹ := by apply _root_.YangMills.Construction.Tower.LevelwiseMeans.isHolomorphicToUnimodular_inv <;> assumption
theorem isHolomorphicToUnimodular_mul {W : Set (ι ⊕ Empty → ComplexMatrix2)}
    {Φ Φ' : (ι ⊕ Empty → ComplexMatrix2) → ComplexMatrix2}
    (hΦ : IsHolomorphicToUnimodular β W Φ) (hΦ' : IsHolomorphicToUnimodular β W Φ') :
    IsHolomorphicToUnimodular β W fun p => Φ p * Φ' p := by
  have hmul : IsHolomorphicToUnimodular β (GroupLieProduct (Fin 2) Empty)
      fun r => r (.inl 0) * r (.inl 1) := by
    have h := isHolomorphicToUnimodular_of_via (ι := Fin 2) H β (Fintype.equivFin _)
      (isHolomorphicVia_mul_components hm (Fintype.equivFin (Fin 2 ⊕ Empty)) (.inl 0) (.inl 1))
      fun p hp => mul_mem_unitDeterminant (mem_groupLieProduct_iff.1 hp.2 0)
        (mem_groupLieProduct_iff.1 hp.2 1)
    rwa [univ_inter] at h
  have hΨ : IsHolomorphicToProduct (ι' := Fin 2) (κ' := Empty) β W
      (fun p => Sum.elim ![Φ p, Φ' p] Empty.elim) :=
    ⟨hΦ.1, Fin.forall_fin_two.2 ⟨hΦ, hΦ'⟩, fun k => k.elim⟩
  have h := isHolomorphicToUnimodular_comp H β hΨ hmul
  have e : W ∩ (fun p => Sum.elim ![Φ p, Φ' p] Empty.elim) ⁻¹'
      GroupLieProduct (Fin 2) Empty = W :=
    inter_eq_left.2 fun p hp =>
      mem_groupLieProduct_iff.2 (Fin.forall_fin_two.2 ⟨hΦ.2.1 hp, hΦ'.2.1 hp⟩)
  rw [e] at h
  exact h
omit hm
theorem isHolomorphicInAllNumberings_of_forall_basis [Nonempty ι]
    {W : Set (ι ⊕ Empty → ComplexMatrix2)}
    {Φ : (ι ⊕ Empty → ComplexMatrix2) → ComplexMatrix2}
    (hΦ : ∀ β : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless,
      IsHolomorphicToUnimodular β W Φ) : IsHolomorphicInAllNumberings W Φ := by
  intro n ν β'
  have hn : 1 ≤ n := by
    obtain ⟨i⟩ := ‹Nonempty ι›
    have := (ν i).pos
    omega
  let R : (Fin n ⊕ Empty → ComplexMatrix2) → ι ⊕ Empty → ComplexMatrix2 :=
    fun r => pointOfIndexedFamily ν fun k => r (.inl k)
  have hopen : ComplexMatrix2.IsRelativelyOpen (GroupLieProduct (Fin n) Empty)
      (GroupLieProduct (Fin n) Empty) := ⟨univ, isOpen_univ, by simp⟩
  have hΨ : IsHolomorphicToProduct β' (GroupLieProduct (Fin n) Empty) R :=
    ⟨hopen, fun i => isHolomorphicToUnimodular_component H β' hopen (ν i), fun k => k.elim⟩
  have h := isHolomorphicToUnimodular_comp H β' hΨ (hΦ β')
  have hp := (H.2.2.2.2.2.1 Empty n hn β' β' _ _ h.1 h.2.1).1 h
  have hWP : W ⊆ GroupLieProduct ι Empty := by
    obtain ⟨O, _, rfl⟩ := (hΦ β').1
    exact inter_subset_right
  have e : ExpChartHolomorphy.pointOfUnimodularPower ⁻¹'
      (GroupLieProduct (Fin n) Empty ∩ R ⁻¹' W) = pointOfIndexedFamily ν ⁻¹' W := by
    ext X
    refine ⟨fun hX => hX.2, fun hX => ⟨mem_groupLieProduct_iff.2 fun k => ?_, hX⟩⟩
    have := mem_groupLieProduct_iff.1 (hWP hX) (ν.symm k)
    change X k ∈ _
    simpa [pointOfIndexedFamily] using this
  rw [e] at hp
  exact hp
omit H [Fintype ι] [Fintype ι'] in
theorem isRelativelyOpen_setOf_forall {E τ : Type} [TopologicalSpace E] [Finite τ] {P : Set E}
    {D : τ → Set E} (hD : ∀ t, ComplexMatrix2.IsRelativelyOpen P (D t)) :
    ComplexMatrix2.IsRelativelyOpen P {x | x ∈ P ∧ ∀ t, x ∈ D t} := by apply _root_.YangMills.Construction.Tower.LevelwiseMeans.isRelativelyOpen_setOf_forall <;> assumption
end Rules
section Orientation
variable {L m : ℕ} {j : ℤ}
theorem extendFromPositive_of_positive {P : Set (Bond L m j)} (v : PositiveBondOf P → ComplexMatrix2)
    {b : Bond L m j} (hb : b ∈ P) (hp : b.IsPositivelyOriented) :
    extendFromPositive P v b = v ⟨b, hb, hp⟩ := by
  unfold extendFromPositive
  rw [dif_pos (⟨hb, hp⟩ : b ∈ P ∧ b.IsPositivelyOriented)]
theorem extendFromPositive_of_not_positive {P : Set (Bond L m j)}
    (v : PositiveBondOf P → ComplexMatrix2) {b : Bond L m j} (hn : ¬ b.IsPositivelyOriented)
    (hb : b.opposite ∈ P) (hp : b.opposite.IsPositivelyOriented) :
    extendFromPositive P v b = (v ⟨b.opposite, hb, hp⟩)⁻¹ := by
  unfold extendFromPositive
  rw [dif_neg (fun h : b ∈ P ∧ b.IsPositivelyOriented => hn h.2),
    dif_pos (⟨hb, hp⟩ : b.opposite ∈ P ∧ b.opposite.IsPositivelyOriented)]
def ExactlyOneOrientedPositively (L m : ℕ) (j : ℤ) : Prop :=
  ∀ b : Bond L m j, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented
theorem opposite_positive_of_not_positive (ho : ExactlyOneOrientedPositively L m j)
    {b : Bond L m j} (hn : ¬ b.IsPositivelyOriented) : b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.PeriodicLattice.isPositivelyOriented_opposite <;> assumption
theorem opposite_not_positive_of_positive (ho : ExactlyOneOrientedPositively L m j)
    {b : Bond L m j} (hp : b.IsPositivelyOriented) : ¬ b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.PeriodicLattice.not_isPositivelyOriented_opposite <;> assumption
theorem isGaugeField_extendFromPositive (ho : ExactlyOneOrientedPositively L m j)
    {P : Set (Bond L m j)} (hP : IsReversalClosed P) {v : PositiveBondOf P → ComplexMatrix2}
    (hv : ∀ i, v i ∈ ComplexMatrix2.unitDeterminant) :
    IsGaugeField complexGaugeGroup P (extendFromPositive P v) := by
  refine ⟨fun b hb => ?_, fun b hb => ?_⟩
  · by_cases hp : b.IsPositivelyOriented
    · rw [extendFromPositive_of_positive v hb hp]
      exact hv _
    · rw [extendFromPositive_of_not_positive v hp (hP b hb)
        (opposite_positive_of_not_positive ho hp)]
      exact inv_mem_unitDeterminant (hv _)
  · by_cases hp : b.IsPositivelyOriented
    · rw [extendFromPositive_of_positive v hb hp,
        extendFromPositive_of_not_positive v (opposite_not_positive_of_positive ho hp)
          (hP b.opposite (hP b hb)) hp]
      rfl
    · rw [extendFromPositive_of_positive v (hP b hb) (opposite_positive_of_not_positive ho hp),
        extendFromPositive_of_not_positive v hp (hP b hb) (opposite_positive_of_not_positive ho hp),
        inv_inv_of_mem_unitDeterminant (hv _)]
theorem extendFromPositive_restrictToPositive (ho : ExactlyOneOrientedPositively L m j)
    {P : Set (Bond L m j)} (hP : IsReversalClosed P) {V : Bond L m j → ComplexMatrix2}
    (hV : IsGaugeField complexGaugeGroup P V) {b : Bond L m j} (hb : b ∈ P) :
    extendFromPositive P (restrictToPositive P V) b = V b := by
  by_cases hp : b.IsPositivelyOriented
  · rw [extendFromPositive_of_positive _ hb hp]
    rfl
  · rw [extendFromPositive_of_not_positive _ hp (hP b hb)
      (opposite_positive_of_not_positive ho hp)]
    change (V b.opposite)⁻¹ = V b
    rw [hV.2 b hb, inv_inv_of_mem_unitDeterminant (hV.1 b hb)]
theorem eq_of_restrictToPositive_eq (ho : ExactlyOneOrientedPositively L m j)
    {P : Set (Bond L m j)} (hP : IsReversalClosed P) {V V' : Bond L m j → ComplexMatrix2}
    (hV : IsGaugeField complexGaugeGroup P V) (hV' : IsGaugeField complexGaugeGroup P V')
    (he : restrictToPositive P V = restrictToPositive P V') {b : Bond L m j} (hb : b ∈ P) :
    V b = V' b := by
  rw [← extendFromPositive_restrictToPositive ho hP hV hb, he,
    extendFromPositive_restrictToPositive ho hP hV' hb]
end Orientation
section Iterates
variable {L m K q : ℕ}
theorem complexBlockAverage_of_positive {j j' : ℤ} (U : Bond L m j' → ComplexMatrix2)
    {c : Bond L m j} (h : c.IsPositivelyOriented) :
    complexBlockAverage U c = complexBlockAverageOnPositive U c :=
  if_pos h
theorem complexBlockAverage_of_not_positive {j j' : ℤ} (U : Bond L m j' → ComplexMatrix2)
    {c : Bond L m j} (h : ¬ c.IsPositivelyOriented) :
    complexBlockAverage U c = (complexBlockAverageOnPositive U c.opposite)⁻¹ :=
  if_neg h
theorem exactlyOneOrientedPositively_of_le (hE : BondEndpointsOrientation.Statement)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hm0 : 0 < m) (hK : 0 < K) {k : ℕ}
    (hk : k ≤ K) : ExactlyOneOrientedPositively L m (levelDepth K k) := fun b =>
  ((hE ⟨L, hL, ⟨K, hK⟩, ⟨m, hm0⟩⟩ k hk).2.2.2 b).2.2.2.2.2
theorem isComplexGaugeField_fieldOfPoint
    (ho : ExactlyOneOrientedPositively L m (levelDepth K q))
    {ℬ : Set (BondAtLevel L m K q)} (hℬ : IsReversalClosed ℬ)
    {p : PositiveBondOf ℬ ⊕ Empty → ComplexMatrix2}
    (hp : p ∈ GroupLieProduct (PositiveBondOf ℬ) Empty) :
    IsComplexGaugeField ℬ (fieldOfPoint ℬ p) :=
  isGaugeField_extendFromPositive ho hℬ fun i => mem_groupLieProduct_iff.1 hp i
theorem iteratedAverage_isGaugeField (hAvg : AveragesAndIteratesAreGaugeFields)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hm0 : 0 < m) (hq : q < K)
    {ℬ : Set (BondAtLevel L m K q)} (hℬ : IsReversalClosed ℬ)
    {U : BondAtLevel L m K q → ComplexMatrix2} (hU : IsComplexGaugeField ℬ U) {j : ℕ}
    (hj : q + j ≤ K) :
    IsReversalClosed (iteratedAverage ℬ U j).support ∧
      IsGaugeField complexGaugeGroup (iteratedAverage ℬ U j).support
        (iteratedAverage ℬ U j).field :=
  ((hAvg L m K q hL hm0 hq ℬ hℬ).2.2.2 j hj).2 U hU
theorem iteratedValue_succ_holomorphic (H : ExpChartHolomorphy.ExpChartTheory)
    (hmx : ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (hE : BondEndpointsOrientation.Statement)
    (hD : PositiveOrientationOfBondAndOpposite)
    (hB : DoubleBlockStructure.Statement)
    (hSch : AveragingSchemeProperties)
    (hAvg : AveragesAndIteratesAreGaugeFields)
    (hR : ComplexAverageIsLocal)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hm0 : 0 < m) (hq : q < K)
    {ℬ : Set (BondAtLevel L m K q)} (hℬ : IsReversalClosed ℬ) [Fintype (PositiveBondOf ℬ)]
    (β : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless) (j : ℕ) (hj : q + j < K)
    (ih : ∀ b : BondAtLevel L m K (q + j),
      IsHolomorphicToUnimodular β (productDomain ℬ j b) (iteratedValue ℬ j b))
    (c : BondAtLevel L m K (q + j + 1)) :
    IsHolomorphicToUnimodular β (productDomain ℬ (j + 1) c) (iteratedValue ℬ (j + 1) c) := by
  have hK : 0 < K := by omega
  have hoq : ExactlyOneOrientedPositively L m (levelDepth K q) :=
    exactlyOneOrientedPositively_of_le hE hL hm0 hK hq.le
  have hoj : ExactlyOneOrientedPositively L m (levelDepth K (q + j)) :=
    exactlyOneOrientedPositively_of_le hE hL hm0 hK hj.le
  obtain ⟨-, -, hdpos, -, -, -, hPd⟩ := hD L m K hL hm0 hK (q + j) hj c
  obtain ⟨d, hd⟩ : ∃ d, d = c.positivelyOriented := ⟨_, rfl⟩
  rw [← hd] at hdpos hPd
  let Pd : Set (BondAtLevel L m K (q + j)) := bondsInDoubleBlock d
  have hPclosed : IsReversalClosed Pd := (hB L m K (q + j) hL hm0 hj d).1.2.2.1
  obtain ⟨-, hDom, hMean, -⟩ := (hSch L hL m K (q + j) hm0 hj .centred).2.1 d hdpos
  have hRd := hR L m K (q + j) hL.1 hL.2 hm0 hj d hdpos
  obtain ⟨⟨inst, -⟩, hdiff⟩ := hDom.average_holomorphic
  let _ := inst
  let N := Fintype.card (PositiveBondOf Pd)
  let ν : PositiveBondOf Pd ≃ Fin N := Fintype.equivFin _
  let S : Set (Fin N → ComplexMatrix2) :=
    (fun v => v ∘ ν.symm) '' (restrictToPositive Pd '' schemeHolomorphyDomain .centred d)
  let F : (Fin N → ComplexMatrix2) → ComplexMatrix2 :=
    fun X => schemeBlockAverage .centred (extendFromPositive Pd (X ∘ ν)) d
  have hF : ComplexCoordinates.IsHolomorphicOnSL2Power β S F := hdiff N ν β
  let Pr : (Fin N ⊕ Empty → ComplexMatrix2) → Fin N → ComplexMatrix2 := fun r i => r (.inl i)
  have hPr : Continuous Pr := continuous_pi fun i => continuous_apply _
  have hOpen : ComplexMatrix2.IsRelativelyOpen (GroupLieProduct (Fin N) Empty) (Pr ⁻¹' S) := by
    obtain ⟨O, hO, hSO⟩ := hF.2.1
    refine ⟨Pr ⁻¹' O, hO.preimage hPr, ?_⟩
    ext r
    change Pr r ∈ S ↔ Pr r ∈ O ∧ r ∈ GroupLieProduct (Fin N) Empty
    rw [hSO, mem_inter_iff, mem_groupLieProduct_iff]
    exact Iff.rfl
  have hGΦ : IsHolomorphicToUnimodular β (Pr ⁻¹' S) (F ∘ Pr) :=
    (H.2.2.2.2.2.1 Empty N hF.1 β β _ _ hOpen fun r hr => hF.2.2.1 hr).2 hF
  have hid : ∀ V : BondAtLevel L m K (q + j) → ComplexMatrix2, ∀ b ∈ Pd,
      onSetElseOne Pd V b = V b :=
    fun V b hb => if_pos hb
  have hdomEq : (schemeHolomorphyDomain .centred d :
      Set (BondAtLevel L m K (q + j) → ComplexMatrix2)) =
      complexAveragingDomainNearOne d := hMean.domain_eq
  have hdomain : ∀ V : BondAtLevel L m K (q + j) → ComplexMatrix2,
      IsGaugeField complexGaugeGroup Pd V →
      ((fun i : Fin N => V (ν.symm i).1) ∈ S ↔
        onSetElseOne Pd V ∈ complexAveragingDomainNearOne d) := by
    intro V hV
    constructor
    · rintro ⟨_, ⟨W, hW, rfl⟩, he⟩
      have hWd : W ∈ (complexAveragingDomainNearOne d :
          Set (BondAtLevel L m K (q + j) → ComplexMatrix2)) := by
        rw [← hdomEq]
        exact hW
      have hWc : IsGaugeField complexGaugeGroup Pd W := hWd.1.1
      have hpr : restrictToPositive Pd W = restrictToPositive Pd V := by
        funext i
        have := congrFun he (ν i)
        simpa [restrictToPositive] using this
      exact (hRd.mem_domain_iff W _ fun b hb => by
        rw [hid V b hb]
        exact eq_of_restrictToPositive_eq hoj hPclosed hWc hV hpr hb).1 hWd
    · intro h
      refine ⟨_, ⟨onSetElseOne Pd V, ?_, rfl⟩, ?_⟩
      · rw [hdomEq]
        exact h
      · funext i
        exact hid V _ (ν.symm i).2.1
  have hvalue : ∀ V : BondAtLevel L m K (q + j) → ComplexMatrix2,
      IsGaugeField complexGaugeGroup Pd V →
      onSetElseOne Pd V ∈ complexAveragingDomainNearOne d →
      F (fun i : Fin N => V (ν.symm i).1) =
        complexBlockAverageOnPositive (onSetElseOne Pd V) d := by
    intro V hV hI
    have e : (fun i : Fin N => V (ν.symm i).1) ∘ ν = restrictToPositive Pd V := by
      funext i
      simp [restrictToPositive]
    change schemeBlockAverage .centred (extendFromPositive Pd
      ((fun i : Fin N => V (ν.symm i).1) ∘ ν)) d = _
    rw [e]
    have hC : ∀ b ∈ Pd, onSetElseOne Pd V b =
        extendFromPositive Pd (restrictToPositive Pd V) b := fun b hb => by
      rw [hid V b hb, extendFromPositive_restrictToPositive hoj hPclosed hV hb]
    have hCd := (hRd.mem_domain_iff _ _ hC).1 hI
    rw [hMean.average_eq _ (by rw [hdomEq]; exact hCd), complexBlockAverage_of_positive _ hdpos,
      hRd.average_eq _ _ hC]
  let 𝒰 : Set (PositiveBondOf ℬ ⊕ Empty → ComplexMatrix2) :=
    {p | p ∈ GroupLieProduct (PositiveBondOf ℬ) Empty ∧
      ∀ i : PositiveBondOf Pd, p ∈ productDomain ℬ j i.1}
  have h𝒰 : ComplexMatrix2.IsRelativelyOpen (GroupLieProduct (PositiveBondOf ℬ) Empty) 𝒰 :=
    isRelativelyOpen_setOf_forall fun i => (ih i.1).1
  let Ψ : (PositiveBondOf ℬ ⊕ Empty → ComplexMatrix2) → Fin N ⊕ Empty → ComplexMatrix2 :=
    fun p => Sum.elim (fun i => iteratedValue ℬ j (ν.symm i).1 p) Empty.elim
  have hΨ : IsHolomorphicToProduct β 𝒰 Ψ :=
    ⟨h𝒰, fun i => isHolomorphicToUnimodular_mono H β (ih (ν.symm i).1) h𝒰 fun p hp => hp.2 _,
      fun k => k.elim⟩
  have hcomp := isHolomorphicToUnimodular_comp H β hΨ hGΦ
  have hmem : ∀ U : BondAtLevel L m K q → ComplexMatrix2,
      c ∈ (iteratedAverage ℬ U (j + 1)).support ↔
      (Pd ⊆ (iteratedAverage ℬ U j).support ∧
        onSetElseOne Pd (iteratedAverage ℬ U j).field ∈ complexAveragingDomainNearOne d) := by
    intro U
    have h : c ∈ (iteratedAverage ℬ U (j + 1)).support ↔
        ((bondsInDoubleBlock c : Set (BondAtLevel L m K (q + j))) ⊆
          (iteratedAverage ℬ U j).support ∧
        onSetElseOne (bondsInDoubleBlock c) (iteratedAverage ℬ U j).field ∈
          complexAveragingDomainNearOne c.positivelyOriented) := Iff.rfl
    rw [h, ← hPd, ← hd]
  have hval : ∀ U : BondAtLevel L m K q → ComplexMatrix2,
      (iteratedAverage ℬ U (j + 1)).field c =
      complexBlockAverage (onSetElseOne Pd (iteratedAverage ℬ U j).field) c := by
    intro U
    have h : (iteratedAverage ℬ U (j + 1)).field c = complexBlockAverage
        (onSetElseOne (bondsInDoubleBlock c) (iteratedAverage ℬ U j).field) c := rfl
    rw [h, ← hPd]
  have hset : productDomain ℬ (j + 1) c = 𝒰 ∩ Ψ ⁻¹' (Pr ⁻¹' S) := by
    ext p
    constructor
    · rintro ⟨hp, hU, hc⟩
      obtain ⟨hsub, hI⟩ := (hmem _).1 hc
      have hV := iteratedAverage_isGaugeField hAvg hL hm0 hq hℬ hU (j := j) hj.le
      have hVP : IsGaugeField complexGaugeGroup Pd
          (iteratedAverage ℬ (fieldOfPoint ℬ p) j).field :=
        ⟨fun b hb => hV.2.1 b (hsub hb), fun b hb => hV.2.2 b (hsub hb)⟩
      exact ⟨⟨hp, fun i => ⟨hp, hU, hsub i.2.1⟩⟩, (hdomain _ hVP).2 hI⟩
    · rintro ⟨⟨hp, hall⟩, hr⟩
      have hU := isComplexGaugeField_fieldOfPoint hoq hℬ hp
      have hV := iteratedAverage_isGaugeField hAvg hL hm0 hq hℬ hU (j := j) hj.le
      have hsub : Pd ⊆ (iteratedAverage ℬ (fieldOfPoint ℬ p) j).support := fun b hb => by
        by_cases hb' : b.IsPositivelyOriented
        · exact (hall ⟨b, hb, hb'⟩).2.2
        · exact hV.1 _
            (hall ⟨b.opposite, hPclosed b hb, opposite_positive_of_not_positive hoj hb'⟩).2.2
      have hVP : IsGaugeField complexGaugeGroup Pd
          (iteratedAverage ℬ (fieldOfPoint ℬ p) j).field :=
        ⟨fun b hb => hV.2.1 b (hsub hb), fun b hb => hV.2.2 b (hsub hb)⟩
      exact ⟨hp, hU, (hmem _).2 ⟨hsub, (hdomain _ hVP).1 hr⟩⟩
  have hpoint : ∀ p ∈ 𝒰 ∩ Ψ ⁻¹' (Pr ⁻¹' S), (F ∘ Pr) (Ψ p) = complexBlockAverageOnPositive
      (onSetElseOne Pd (iteratedAverage ℬ (fieldOfPoint ℬ p) j).field) d := by
    intro p hp
    have hp' : p ∈ productDomain ℬ (j + 1) c := by
      rw [hset]
      exact hp
    obtain ⟨-, hU, hc⟩ := hp'
    obtain ⟨hsub, hI⟩ := (hmem _).1 hc
    have hV := iteratedAverage_isGaugeField hAvg hL hm0 hq hℬ hU (j := j) hj.le
    exact hvalue _ ⟨fun b hb => hV.2.1 b (hsub hb), fun b hb => hV.2.2 b (hsub hb)⟩ hI
  rw [hset]
  by_cases hc : c.IsPositivelyOriented
  · have hdc : d = c := by
      rw [hd]
      exact if_pos hc
    refine isHolomorphicToUnimodular_congr β hcomp fun p hp => ?_
    change (F ∘ Pr) (Ψ p) = (iteratedAverage ℬ (fieldOfPoint ℬ p) (j + 1)).field c
    rw [hval, complexBlockAverage_of_positive _ hc, hpoint p hp, hdc]
  · have hdc : d = c.opposite := by
      rw [hd]
      exact if_neg hc
    refine isHolomorphicToUnimodular_congr β (isHolomorphicToUnimodular_inv H hmx β hcomp)
      fun p hp => ?_
    change ((F ∘ Pr) (Ψ p))⁻¹ = (iteratedAverage ℬ (fieldOfPoint ℬ p) (j + 1)).field c
    rw [hval, complexBlockAverage_of_not_positive _ hc, hpoint p hp, hdc]
end Iterates
section Assembly
variable {L m K q : ℕ}
theorem mem_iteratedAverage_zero_support {ℬ : Set (BondAtLevel L m K q)}
    {U : BondAtLevel L m K q → ComplexMatrix2} {c : BondAtLevel L m K q} :
    c ∈ (iteratedAverage ℬ U 0).support ↔ c ∈ ℬ := Iff.rfl
theorem iteratedValue_zero {ℬ : Set (BondAtLevel L m K q)} {c : BondAtLevel L m K q}
    {p : PositiveBondOf ℬ ⊕ Empty → ComplexMatrix2} :
    iteratedValue ℬ 0 c p = fieldOfPoint ℬ p c := rfl
theorem iteratedValue_zero_holomorphic (H : ExpChartHolomorphy.ExpChartTheory)
    (hmx : ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (hoq : ExactlyOneOrientedPositively L m (levelDepth K q))
    {ℬ : Set (BondAtLevel L m K q)} (hℬ : IsReversalClosed ℬ) [Fintype (PositiveBondOf ℬ)]
    (β : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless) (c : BondAtLevel L m K q) :
    IsHolomorphicToUnimodular β (productDomain ℬ 0 c) (iteratedValue ℬ 0 c) := by
  have hopen : ComplexMatrix2.IsRelativelyOpen (GroupLieProduct (PositiveBondOf ℬ) Empty)
      (GroupLieProduct (PositiveBondOf ℬ) Empty) := ⟨univ, isOpen_univ, by simp⟩
  by_cases hc : c ∈ ℬ
  · have hdom : productDomain ℬ 0 c = GroupLieProduct (PositiveBondOf ℬ) Empty := by
      ext p
      exact ⟨fun h => h.1, fun hp =>
        ⟨hp, isComplexGaugeField_fieldOfPoint hoq hℬ hp, mem_iteratedAverage_zero_support.2 hc⟩⟩
    rw [hdom]
    by_cases hp : c.IsPositivelyOriented
    · refine isHolomorphicToUnimodular_congr β
        (isHolomorphicToUnimodular_component H β hopen ⟨c, hc, hp⟩) fun p _ => ?_
      rw [iteratedValue_zero]
      exact (extendFromPositive_of_positive (fun b => p (.inl b)) hc hp).symm
    · have hr := opposite_positive_of_not_positive hoq hp
      refine isHolomorphicToUnimodular_congr β (isHolomorphicToUnimodular_inv H hmx β
        (isHolomorphicToUnimodular_component H β hopen ⟨c.opposite, hℬ c hc, hr⟩))
          fun p _ => ?_
      rw [iteratedValue_zero]
      exact (extendFromPositive_of_not_positive (fun b => p (.inl b)) hp (hℬ c hc) hr).symm
  · have hdom : productDomain ℬ 0 c = ∅ :=
      eq_empty_of_forall_notMem fun p h => hc (mem_iteratedAverage_zero_support.1 h.2.2)
    rw [hdom]
    exact isHolomorphicToUnimodular_empty β _
theorem iteratedValue_holomorphic (H : ExpChartHolomorphy.ExpChartTheory)
    (hmx : ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (hE : BondEndpointsOrientation.Statement)
    (hD : PositiveOrientationOfBondAndOpposite)
    (hB : DoubleBlockStructure.Statement)
    (hSch : AveragingSchemeProperties)
    (hAvg : AveragesAndIteratesAreGaugeFields)
    (hR : ComplexAverageIsLocal)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hm0 : 0 < m) (hq : q < K)
    {ℬ : Set (BondAtLevel L m K q)} (hℬ : IsReversalClosed ℬ) [Fintype (PositiveBondOf ℬ)]
    (β : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless) (j : ℕ) :
    q + j ≤ K → ∀ c : BondAtLevel L m K (q + j),
      IsHolomorphicToUnimodular β (productDomain ℬ j c) (iteratedValue ℬ j c) := by
  have hK : 0 < K := by omega
  have hoq : ExactlyOneOrientedPositively L m (levelDepth K q) :=
    exactlyOneOrientedPositively_of_le hE hL hm0 hK hq.le
  induction j with
  | zero =>
    intro _ c
    exact iteratedValue_zero_holomorphic H hmx hoq hℬ β c
  | succ j ih =>
    intro hj c
    exact iteratedValue_succ_holomorphic H hmx hE hD hB hSch hAvg hR hL hm0 hq hℬ β j
      (by omega) (ih (by omega)) c
theorem leftMultipliedValue_holomorphic (H : ExpChartHolomorphy.ExpChartTheory)
    (hmx : ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    {ℬ : Set (BondAtLevel L m K q)} [Fintype (PositiveBondOf ℬ)]
    (β : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless) {j : ℕ}
    {c : BondAtLevel L m K (q + j)}
    (hc : IsHolomorphicToUnimodular β (productDomain ℬ j c) (iteratedValue ℬ j c))
    {n : ℕ} (l : Fin n) (σ : ℤˣ) :
    IsHolomorphicToUnimodular β (productDomainTimesPower ℬ j c n)
      (leftMultipliedValue ℬ j c l σ) := by
  have htop : ComplexMatrix2.IsRelativelyOpen (GroupLieProduct (PositiveBondOf ℬ ⊕ Fin n) Empty)
      (GroupLieProduct (PositiveBondOf ℬ ⊕ Fin n) Empty) := ⟨univ, isOpen_univ, by simp⟩
  have hΨ : IsHolomorphicToProduct β (GroupLieProduct (PositiveBondOf ℬ ⊕ Fin n) Empty)
      (fieldComponent (B := ℬ) (n := n)) :=
    ⟨htop, fun i => isHolomorphicToUnimodular_component H β htop (.inl i), fun k => k.elim⟩
  have h := isHolomorphicToUnimodular_comp H β hΨ hc
  have e : GroupLieProduct (PositiveBondOf ℬ ⊕ Fin n) Empty ∩
      fieldComponent ⁻¹' productDomain ℬ j c = productDomainTimesPower ℬ j c n := by
    ext p
    constructor
    · rintro ⟨hp, hd⟩
      exact ⟨hd, fun l => mem_groupLieProduct_iff.1 hp (.inr l)⟩
    · rintro ⟨hd, hl⟩
      refine ⟨mem_groupLieProduct_iff.2 ?_, hd⟩
      rintro (i | l)
      · exact mem_groupLieProduct_iff.1 hd.1 i
      · exact hl l
  rw [e] at h
  have hY : IsHolomorphicToUnimodular β (productDomainTimesPower ℬ j c n)
      fun p => powerComponent p l :=
    isHolomorphicToUnimodular_component H β h.1 (.inr l)
  have hs : IsHolomorphicToUnimodular β (productDomainTimesPower ℬ j c n)
      fun p => signedPower σ (powerComponent p l) := by
    by_cases hσ : σ = 1
    · exact isHolomorphicToUnimodular_congr β hY fun p _ => (if_pos hσ).symm
    · exact isHolomorphicToUnimodular_congr β (isHolomorphicToUnimodular_inv H hmx β hY)
        fun p _ => (if_neg hσ).symm
  exact isHolomorphicToUnimodular_mul H hmx β hs h
theorem complexIteratedAveragesHolomorphic_holds (hE : BondEndpointsOrientation.Statement)
    (hD : PositiveOrientationOfBondAndOpposite)
    (hB : DoubleBlockStructure.Statement)
    (hR : ComplexAverageIsLocal)
    (hSch : AveragingSchemeProperties)
    (hAvg : AveragesAndIteratesAreGaugeFields)
    (hW : ComplexPartialItersFormedByPartialMaps)
    (H : ExpChartHolomorphy.ExpChartTheory)
    (hmx : ComplexCoordinates.PowerSeriesHolomorphy.Properties) :
    ComplexIteratedAveragesHolomorphic := by
  intro L m K hL hm0 q hq ℬ hℬ inst
  have hK : 0 < K := by omega
  have hoq : ExactlyOneOrientedPositively L m (levelDepth K q) :=
    exactlyOneOrientedPositively_of_le hE hL hm0 hK hq.le
  have hcore := fun β j => iteratedValue_holomorphic H hmx hE hD hB hSch hAvg hR hL hm0 hq hℬ
    (ℬ := ℬ) β j
  let β₀ := OneLoop.pauliBasis
  refine ⟨fun j hj c => ⟨?_, fun n hn l σ => ?_, ?_⟩, fun u hu js cs hjs => ?_⟩
  · refine ⟨(hcore β₀ j hj c).1, fun U hU => ?_, fun β => hcore β j hj c, fun hne => ?_⟩
    · exact (iteratedAverage_isGaugeField hAvg hL hm0 hq hℬ hU.1 hj).2.1 c hU.2
    · obtain ⟨b, hb⟩ := hne
      have : Nonempty (PositiveBondOf ℬ) := by
        by_cases hp : b.IsPositivelyOriented
        · exact ⟨⟨b, hb, hp⟩⟩
        · exact ⟨⟨b.opposite, hℬ b hb, opposite_positive_of_not_positive hoq hp⟩⟩
      exact isHolomorphicInAllNumberings_of_forall_basis H fun β => hcore β j hj c
  · have hall := fun β => leftMultipliedValue_holomorphic H hmx β (hcore β j hj c) l σ
    have : Nonempty (PositiveBondOf ℬ ⊕ Fin n) := ⟨.inr l⟩
    exact ⟨(hall β₀).1, hall, isHolomorphicInAllNumberings_of_forall_basis H hall⟩
  · have hw := fun U (hU : IsComplexGaugeField ℬ U) =>
      (hW L m K hL hm0 q hq).1 ⟨ℬ, U⟩ hℬ hU j hj c
    refine ⟨?_, fun U hU => (hw U hU.1).2 ((hw U hU.1).1.1 hU.2)⟩
    ext U
    exact ⟨fun h => ⟨h.1, (hw U h.1).1.1 h.2⟩, fun h => ⟨h.1, (hw U h.1).1.2 h.2⟩⟩
  · have hopen : ComplexMatrix2.IsRelativelyOpen (GroupLieProduct (PositiveBondOf ℬ) Empty)
        (⋂ s, productDomain ℬ (js s) (cs s)) := by
      have h := isRelativelyOpen_setOf_forall fun s => (hcore β₀ (js s) (hjs s) (cs s)).1
      have e : {x | x ∈ GroupLieProduct (PositiveBondOf ℬ) Empty ∧
          ∀ s, x ∈ productDomain ℬ (js s) (cs s)} =
          ⋂ s, productDomain ℬ (js s) (cs s) := by
        ext x
        rw [mem_iInter]
        exact ⟨fun hx => hx.2, fun hx => ⟨(hx ⟨0, hu⟩).1, hx⟩⟩
      rwa [e] at h
    exact ⟨hopen, fun s β => isHolomorphicToUnimodular_mono H β (hcore β (js s) (hjs s) (cs s))
      hopen (iInter_subset _ s)⟩
end Assembly
end PeriodicLattice.ComplexIteratedAverages
end YangMills.Construction
