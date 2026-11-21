import YangMills.Construction.Towers.ComplexAverageLiesInTheComplexGroupProof
import YangMills.Construction.Towers.BlocksStraightPathsContoursAndPivotBondsOfATower
import YangMills.Construction.Towers.BondsOnWhichTheAveragesDepend
import YangMills.Construction.Towers.ConfigurationsWhoseAveragesStayInThePolydiscsProof
import Mathlib
set_option autoImplicit false
open Set Filter
open scoped Topology
noncomputable section
namespace YangMills.Construction.Tower.SupportOfMeans
open YangMills.Construction.Matrices YangMills.Construction.Matrices.GroupLieProduct
open YangMills.Construction.Coordinates
open LevelwiseMeans (valuesOrOne)
section CoordinateMaps
open ComplexCoordinates
variable {σ : Type}
theorem isOpen_matrixPiEquiv_image {k : ℕ} (ν : σ ≃ Fin k) {O : Set (σ → ComplexMatrix2)}
    (hO : IsOpen O) : IsOpen (matrixPiEquiv ν '' O) := by apply _root_.YangMills.Construction.Tower.LevelwiseMeans.isOpen_matrixPiEquiv_image <;> assumption
end CoordinateMaps
section HolomorphyRules
open ComplexCoordinates
variable {ι ι' : Type} [Fintype ι] [Fintype ι']
theorem inv_mem_unitDeterminant {X : ComplexMatrix2} (h : X ∈ ComplexMatrix2.unitDeterminant) :
    X⁻¹ ∈ ComplexMatrix2.unitDeterminant := by apply _root_.YangMills.SharedProofs.p413 <;> assumption
theorem inv_inv_of_mem_unitDeterminant {X : ComplexMatrix2}
    (h : X ∈ ComplexMatrix2.unitDeterminant) : X⁻¹⁻¹ = X := by apply _root_.YangMills.Construction.Tower.LevelwiseMeans.inv_inv_of_mem_unitDeterminant <;> assumption
variable (H : GroupLieProduct.ExpChartHolomorphy.ExpChartTheory)
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
    (hΨ : IsHolomorphicToProduct β W Ψ) {W' : Set (ι' ⊕ Empty → ComplexMatrix2)}
    {Φ : (ι' ⊕ Empty → ComplexMatrix2) → ComplexMatrix2}
    (hΦ : IsHolomorphicToUnimodular β W' Φ) :
    IsHolomorphicToUnimodular β (W ∩ Ψ ⁻¹' W') (Φ ∘ Ψ) := by apply _root_.YangMills.Construction.Tower.LevelwiseMeans.isHolomorphicToUnimodular_comp <;> assumption
omit H in
theorem isHolomorphicToUnimodular_congr {W : Set (ι ⊕ Empty → ComplexMatrix2)}
    {Φ Φ' : (ι ⊕ Empty → ComplexMatrix2) → ComplexMatrix2}
    (hΦ : IsHolomorphicToUnimodular β W Φ) (he : ∀ p ∈ W, Φ p = Φ' p) :
    IsHolomorphicToUnimodular β W Φ' := by apply _root_.YangMills.Construction.Tower.LevelwiseMeans.isHolomorphicToUnimodular_congr <;> assumption
end HolomorphyRules
section FactorPoints
open DoubleBlockPolydisc
variable {σ : Type}
theorem asGroupFactors_image (O : Set (σ → ComplexMatrix2)) :
    asGroupFactors '' O = leftComponents ⁻¹' O := by apply _root_.YangMills.Construction.Tower.LevelwiseMeans.image_asGroupFactors <;> assumption
theorem isRelativelyOpen_preimage_leftComponents {O : Set (σ → ComplexMatrix2)}
    (h : ComplexMatrix2.IsRelativelyOpen (unimodularPi σ) O) :
    ComplexMatrix2.IsRelativelyOpen (GroupLieProduct σ Empty) (leftComponents ⁻¹' O) := by apply _root_.YangMills.Construction.Tower.LevelwiseMeans.isRelativelyOpen_preimage_leftComponents <;> assumption
end FactorPoints
theorem finrank_traceless : Module.finrank ℂ ComplexMatrix2.traceless = 3 := by apply _root_.YangMills.SharedProofs.p8292 <;> assumption
def tracelessBasis : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless :=
  Module.finBasisOfFinrankEq ℂ _ finrank_traceless
section ConstantMaps
open ComplexCoordinates
variable {σ : Type}
theorem isHolomorphicVia_const {k : ℕ} (ν : σ ≃ Fin k) (X : ComplexMatrix2)
    {O : Set (σ → ComplexMatrix2)} (hO : IsOpen O) :
    IsHolomorphicVia (matrixPiEquiv ν) matrixEquiv O fun _ => X := by
  unfold IsHolomorphicVia
  have e : (matrixEquiv ∘ (fun _ : σ → ComplexMatrix2 => X) ∘ (matrixPiEquiv ν).symm) =
      fun _ => matrixEquiv X := rfl
  rw [e]
  exact ⟨isOpen_matrixPiEquiv_image ν hO, continuousOn_const,
    fun _ _ _ => Eventually.of_forall fun _ => differentiableAt_const _⟩
end ConstantMaps
theorem isRelativelyOpen_of_local {E : Type} [TopologicalSpace E] {P O : Set E}
    (h : ∀ w ∈ O, ∃ N, ComplexMatrix2.IsRelativelyOpen P N ∧ w ∈ N ∧ N ⊆ O) (hs : O ⊆ P) :
    ComplexMatrix2.IsRelativelyOpen P O := by
  have h' : ∀ w ∈ O, ∃ A, IsOpen A ∧ w ∈ A ∧ A ∩ P ⊆ O := by
    intro w hw
    obtain ⟨N, ⟨A, hA, rfl⟩, hwN, hN⟩ := h w hw
    exact ⟨A, hA, hwN.1, hN⟩
  choose! A hA using h'
  refine ⟨⋃ w ∈ O, A w, isOpen_biUnion fun w hw => (hA w hw).1, ?_⟩
  ext x
  constructor
  · intro hx
    exact ⟨mem_biUnion hx (hA x hx).2.1, hs hx⟩
  · rintro ⟨hx, hP⟩
    obtain ⟨w, hw, hxw⟩ := mem_iUnion₂.1 hx
    exact (hA w hw).2.2 ⟨hxw, hP⟩
theorem isHolomorphicToUnimodular_of_local {ι : Type} [Fintype ι]
    (β : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless)
    {W : Set (ι ⊕ Empty → ComplexMatrix2)} {Φ : (ι ⊕ Empty → ComplexMatrix2) → ComplexMatrix2}
    (hW : ComplexMatrix2.IsRelativelyOpen (GroupLieProduct ι Empty) W)
    (h : ∀ p ∈ W, ∃ N, p ∈ N ∧ N ⊆ W ∧ IsHolomorphicToUnimodular β N Φ) :
    IsHolomorphicToUnimodular β W Φ := by apply _root_.YangMills.Construction.Tower.MeanStableFields.isHolomorphicToUnimodular_of_local <;> assumption
section ProductMaps
open DoubleBlockPolydisc
variable {σ τ : Type} [Fintype σ] [Fintype τ]
  (H : GroupLieProduct.ExpChartHolomorphy.ExpChartTheory)
include H
theorem isHolomorphicOnProduct_eval {O : Set (σ → ComplexMatrix2)}
    (hO : ComplexMatrix2.IsRelativelyOpen (unimodularPi σ) O) (s : σ) :
    IsHolomorphicOnProduct O fun w => w s := by
  intro β
  rw [asGroupFactors_image]
  exact isHolomorphicToUnimodular_component H β (isRelativelyOpen_preimage_leftComponents hO) s
theorem isHolomorphicOnProduct_const {O : Set (σ → ComplexMatrix2)}
    (hO : ComplexMatrix2.IsRelativelyOpen (unimodularPi σ) O) {X : ComplexMatrix2}
    (hX : X ∈ ComplexMatrix2.unitDeterminant) : IsHolomorphicOnProduct O fun _ => X := by
  intro β
  rw [asGroupFactors_image]
  obtain ⟨A, hA, e⟩ := isRelativelyOpen_preimage_leftComponents hO
  rw [e]
  exact isHolomorphicToUnimodular_of_via H β (Fintype.equivFin _)
    (isHolomorphicVia_const _ X hA) fun _ _ => hX
theorem isHolomorphicOnProduct_comp {O : Set (σ → ComplexMatrix2)}
    (hO : ComplexMatrix2.IsRelativelyOpen (unimodularPi σ) O)
    {Ψ : (σ → ComplexMatrix2) → τ → ComplexMatrix2}
    (hΨ : ∀ t, IsHolomorphicOnProduct O fun w => Ψ w t)
    {O' : Set (τ → ComplexMatrix2)} {f : (τ → ComplexMatrix2) → ComplexMatrix2}
    (hf : IsHolomorphicOnProduct O' f) (hm : MapsTo Ψ O O') :
    IsHolomorphicOnProduct O fun w => f (Ψ w) := by
  intro β
  have hW : ComplexMatrix2.IsRelativelyOpen (GroupLieProduct σ Empty) (asGroupFactors '' O) := by
    rw [asGroupFactors_image]
    exact isRelativelyOpen_preimage_leftComponents hO
  have hP : IsHolomorphicToProduct β (asGroupFactors '' O)
      (fun p : σ ⊕ Empty → ComplexMatrix2 =>
        (asGroupFactors (Ψ (leftComponents p)) : τ ⊕ Empty → ComplexMatrix2)) :=
    ⟨hW, fun t => hΨ t β, fun e => e.elim⟩
  have h := isHolomorphicToUnimodular_comp H β hP (hf β)
  have e : asGroupFactors '' O ∩ (fun p : σ ⊕ Empty → ComplexMatrix2 =>
      (asGroupFactors (Ψ (leftComponents p)) : τ ⊕ Empty → ComplexMatrix2)) ⁻¹'
        (asGroupFactors '' O') = asGroupFactors '' O := by
    refine inter_eq_left.2 ?_
    rintro _ ⟨w, hw, rfl⟩
    exact ⟨Ψ w, hm hw, rfl⟩
  rw [e] at h
  exact h
end ProductMaps
open BondSetFields DoubleBlockPolydisc
structure MeanScheme where
  E : ℕ → Type
  flip : ∀ {i : ℕ}, E i → E i
  IsPos : ∀ {i : ℕ}, E i → Prop
  supp : ∀ {i : ℕ}, E (i + 1) → Set (E i)
  mean : ∀ {i : ℕ}, (E i → ComplexMatrix2) → E (i + 1) → ComplexMatrix2
  extend : ∀ {i : ℕ} (c : E (i + 1)),
    (positivePart (@IsPos i) (supp c) → ComplexMatrix2) → E i → ComplexMatrix2
  r : ℝ
  Reaches : ∀ {u : ℕ}, E u → E 0 → Prop
namespace MeanScheme
variable (D : MeanScheme)
def polydisc {i : ℕ} (c : D.E (i + 1)) : Set (D.E i → ComplexMatrix2) :=
  {V | ((∀ b ∈ D.supp c, V b ∈ PeriodicLattice.complexGaugeGroup) ∧
      ∀ b ∈ D.supp c, V (D.flip b) = (V b)⁻¹) ∧
    ∀ b ∈ D.supp c, ComplexMatrix2.operatorNorm (V b - 1) < D.r}
def stepMean {i : ℕ} (w : D.E i → Option ComplexMatrix2) (c : D.E (i + 1)) :
    Option ComplexMatrix2 :=
  open Classical in
  if (∀ b ∈ D.supp c, (w b).isSome) ∧ valuesOrOne w ∈ D.polydisc c then
    some (D.mean (valuesOrOne w) c)
  else none
def levels (W : D.E 0 → ComplexMatrix2) : (i : ℕ) → D.E i → Option ComplexMatrix2
  | 0 => fun c => some (W c)
  | i + 1 => fun c =>
    open Classical in
    if D.IsPos c then D.stepMean (levels W i) c
    else (D.stepMean (levels W i) (D.flip c)).map (·⁻¹)
def IsField {i : ℕ} (V : D.E i → ComplexMatrix2) : Prop :=
  (∀ b, V b ∈ PeriodicLattice.complexGaugeGroup) ∧ ∀ b, V (D.flip b) = (V b)⁻¹
def support {u : ℕ} (c : D.E u) : Set (D.E 0) := {b | D.IsPos b ∧ D.Reaches c b}
def leftAct (A U : D.E 0 → ComplexMatrix2) (b : D.E 0) : ComplexMatrix2 :=
  open Classical in
  if D.IsPos b then ComplexMatrix2.matExp (Complex.I • A b) * U b
  else (ComplexMatrix2.matExp (Complex.I • A (D.flip b)) * U (D.flip b))⁻¹
structure Representation (j : ℕ) (c : D.E j) (U : D.E 0 → ComplexMatrix2)
    (F : Finset (D.E 0)) (O : Set (F → ComplexMatrix2))
    (f : (F → ComplexMatrix2) → ComplexMatrix2) : Prop where
  pos : ∀ b ∈ F, D.IsPos b
  isOpen : ComplexMatrix2.IsRelativelyOpen (unimodularPi F) O
  mem : (fun b : F => U b) ∈ O
  holo : IsHolomorphicOnProduct O f
  eq : ∀ W, D.IsField W → (fun b : F => W b) ∈ O → D.levels W j c = some (f fun b : F => W b)
structure Admissible (k : ℕ) : Prop where
  flip_flip : ∀ {i : ℕ} (b : D.E i), D.flip (D.flip b) = b
  xor_isPos : ∀ i ≤ k, ∀ b : D.E i, Xor (D.IsPos b) (D.IsPos (D.flip b))
  flip_mem : ∀ i < k, ∀ c : D.E (i + 1), D.IsPos c → ∀ b ∈ D.supp c, D.flip b ∈ D.supp c
  exists_isPos : ∀ i < k, ∀ c : D.E (i + 1), D.IsPos c → ∃ b ∈ D.supp c, D.IsPos b
  mean_eq : ∀ i < k, ∀ c : D.E (i + 1), D.IsPos c → ∀ V ∈ D.polydisc c,
    D.mean V c = D.mean (D.extend c fun b => V b.1) c
  eq_extend : ∀ i < k, ∀ c : D.E (i + 1), D.IsPos c → ∀ V ∈ D.polydisc c, ∀ b ∈ D.supp c,
    V b = D.extend c (fun b => V b.1) b
  reaches_flip : ∀ u ≤ k, ∀ (c : D.E u) (b : D.E 0), D.Reaches (D.flip c) b ↔ D.Reaches c b
  reaches_flip_right : ∀ c b : D.E 0, D.Reaches c (D.flip b) ↔ D.Reaches c b
  reaches_self : ∀ c : D.E 0, D.Reaches c c
  reaches_of_mem : ∀ i < k, ∀ c : D.E (i + 1), D.IsPos c → ∀ b' ∈ D.supp c, ∀ b : D.E 0,
    D.Reaches b' b → D.Reaches c b
  support_finite_of_isPos : ∀ u ≤ k, ∀ c : D.E u, D.IsPos c → (D.support c).Finite
  exists_representation : ∀ u ≤ k, ∀ (c : D.E u) (U : D.E 0 → ComplexMatrix2), D.IsField U →
    (D.levels U u c).isSome →
    ∃ (F : Finset (D.E 0)) (O : Set (F → ComplexMatrix2))
      (f : (F → ComplexMatrix2) → ComplexMatrix2), D.Representation u c U F O f
  leftAct_mem : ∀ U : D.E 0 → ComplexMatrix2, D.IsField U → ∀ C : D.E 0 → ComplexMatrix2,
    (∀ b, D.IsPos b → C b ∈ PeriodicLattice.complexLieAlgebra) →
    ∀ b, D.IsPos b →
      ComplexMatrix2.matExp (Complex.I • C b) * U b ∈ PeriodicLattice.complexGaugeGroup
variable {D} {k : ℕ}
theorem Admissible.isPos_flip_of_not (G : D.Admissible k) {i : ℕ} (hi : i ≤ k) {b : D.E i}
    (h : ¬ D.IsPos b) : D.IsPos (D.flip b) := by
  rcases G.xor_isPos i hi b with h' | h'
  · exact absurd h'.1 h
  · exact h'.1
theorem Admissible.not_isPos_flip (G : D.Admissible k) {i : ℕ} (hi : i ≤ k) {b : D.E i}
    (h : D.IsPos b) : ¬ D.IsPos (D.flip b) := by
  rcases G.xor_isPos i hi b with h' | h'
  · exact h'.2
  · exact absurd h h'.2
theorem levels_succ_of_isPos (W : D.E 0 → ComplexMatrix2) {i : ℕ} {c : D.E (i + 1)}
    (h : D.IsPos c) : D.levels W (i + 1) c = D.stepMean (D.levels W i) c := by
  simp only [levels, if_pos h]
theorem levels_succ_of_not_isPos (W : D.E 0 → ComplexMatrix2) {i : ℕ} {c : D.E (i + 1)}
    (h : ¬ D.IsPos c) :
    D.levels W (i + 1) c = (D.stepMean (D.levels W i) (D.flip c)).map (·⁻¹) := by
  simp only [levels, if_neg h]
def extendByOne (D : MeanScheme) (F : Finset (D.E 0)) (w : F → ComplexMatrix2) (b : D.E 0) :
    ComplexMatrix2 :=
  open Classical in
  if h : b ∈ F then w ⟨b, h⟩
  else if h' : D.flip b ∈ F then (w ⟨D.flip b, h'⟩)⁻¹
  else 1
theorem extendByOne_spec (G : D.Admissible k) {F : Finset (D.E 0)} (hF : ∀ b ∈ F, D.IsPos b)
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
    · have hn : D.flip b ∉ F := fun h' => G.not_isPos_flip h0 (hF b h) (hF _ h')
      have hr : D.flip (D.flip b) = b := G.flip_flip b
      simp only [extendByOne, dif_neg hn, dif_pos h]
      rw [dif_pos (by rw [hr]; exact h)]
      congr 2
      exact Subtype.ext hr
    · by_cases h' : D.flip b ∈ F
      · have hr : D.flip (D.flip b) = b := G.flip_flip b
        simp only [extendByOne, dif_pos h', dif_neg h]
        exact (inv_inv_of_mem_unitDeterminant (hw _)).symm
      · have hr : D.flip (D.flip b) = b := G.flip_flip b
        simp only [extendByOne, dif_neg h, dif_neg h']
        rw [dif_neg (by rw [hr]; exact h)]
        simp
  · funext b
    simp [extendByOne]
def extendByOneOn (D : MeanScheme) (F F' : Finset (D.E 0)) (w : F → ComplexMatrix2) :
    F' → ComplexMatrix2 :=
  fun b => D.extendByOne F w b
theorem Admissible.isField_leftAct (G : D.Admissible k) {U C : D.E 0 → ComplexMatrix2}
    (hU : D.IsField U) (hC : ∀ b, D.IsPos b → C b ∈ PeriodicLattice.complexLieAlgebra) :
    D.IsField (D.leftAct C U) := by
  classical
  have h0 : (0 : ℕ) ≤ k := Nat.zero_le _
  have hleft := G.leftAct_mem U hU C hC
  refine ⟨fun b => ?_, fun b => ?_⟩
  · by_cases hb : D.IsPos b
    · simp only [leftAct, if_pos hb]
      exact hleft b hb
    · simp only [leftAct, if_neg hb]
      exact inv_mem_unitDeterminant (hleft _ (G.isPos_flip_of_not h0 hb))
  · by_cases hb : D.IsPos b
    · have hn := G.not_isPos_flip h0 hb
      simp only [leftAct, if_neg hn, if_pos hb, G.flip_flip]
    · have hr := G.isPos_flip_of_not h0 hb
      simp only [leftAct, if_pos hr, if_neg hb]
      exact (inv_inv_of_mem_unitDeterminant (hleft _ hr)).symm
theorem polydisc_congr {i : ℕ} {c : D.E (i + 1)} (hr : ∀ b ∈ D.supp c, D.flip b ∈ D.supp c)
    {V V' : D.E i → ComplexMatrix2} (hV : V ∈ D.polydisc c) (he : ∀ b ∈ D.supp c, V b = V' b) :
    V' ∈ D.polydisc c := by
  refine ⟨⟨fun b hb => he b hb ▸ hV.1.1 b hb, fun b hb => ?_⟩, fun b hb => he b hb ▸ hV.2 b hb⟩
  rw [← he _ (hr b hb), ← he b hb]
  exact hV.1.2 b hb
theorem Admissible.support_flip (G : D.Admissible k) {u : ℕ} (hu : u ≤ k) (c : D.E u) :
    D.support (D.flip c) = D.support c := by
  ext b
  exact and_congr_right fun _ => G.reaches_flip u hu c b
theorem Admissible.support_finite (G : D.Admissible k) {u : ℕ} (hu : u ≤ k) (c : D.E u) :
    (D.support c).Finite := by
  by_cases hc : D.IsPos c
  · exact G.support_finite_of_isPos u hu c hc
  · rw [← G.support_flip hu c]
    exact G.support_finite_of_isPos u hu _ (G.isPos_flip_of_not hu hc)
theorem Admissible.support_nonempty (G : D.Admissible k) :
    ∀ u ≤ k, ∀ c : D.E u, (D.support c).Nonempty := by
  intro u
  induction u with
  | zero =>
    intro _ c
    by_cases hc : D.IsPos c
    · exact ⟨c, hc, G.reaches_self c⟩
    · exact ⟨D.flip c, G.isPos_flip_of_not (Nat.zero_le _) hc,
        (G.reaches_flip_right c c).2 (G.reaches_self c)⟩
  | succ i ih =>
    intro hi c
    have key : ∀ c' : D.E (i + 1), D.IsPos c' → (D.support c').Nonempty := by
      intro c' hc'
      obtain ⟨b', hb', _⟩ := G.exists_isPos i hi c' hc'
      obtain ⟨b, hb, he⟩ := ih (Nat.le_of_succ_le hi) b'
      exact ⟨b, hb, G.reaches_of_mem i hi c' hc' b' hb' b he⟩
    by_cases hc : D.IsPos c
    · exact key c hc
    · rw [← G.support_flip hi c]
      exact key _ (G.isPos_flip_of_not hi hc)
theorem Admissible.stepMean_congr (G : D.Admissible k) {i : ℕ} (hi : i < k) {c : D.E (i + 1)}
    (hc : D.IsPos c) {w w' : D.E i → Option ComplexMatrix2} (h : ∀ b ∈ D.supp c, w b = w' b) :
    D.stepMean w c = D.stepMean w' c := by
  have hf : ∀ b ∈ D.supp c, valuesOrOne w b = valuesOrOne w' b := fun b hb => by
    simp only [valuesOrOne, h b hb]
  have hr := G.flip_mem i hi c hc
  have hiff : ((∀ b ∈ D.supp c, (w b).isSome) ∧ valuesOrOne w ∈ D.polydisc c) ↔
      ((∀ b ∈ D.supp c, (w' b).isSome) ∧ valuesOrOne w' ∈ D.polydisc c) :=
    ⟨fun q => ⟨fun b hb => h b hb ▸ q.1 b hb, polydisc_congr hr q.2 hf⟩,
      fun q => ⟨fun b hb => (h b hb).symm ▸ q.1 b hb,
        polydisc_congr hr q.2 fun b hb => (hf b hb).symm⟩⟩
  unfold stepMean
  by_cases h1 : (∀ b ∈ D.supp c, (w b).isSome) ∧ valuesOrOne w ∈ D.polydisc c
  · rw [if_pos h1, if_pos (hiff.1 h1)]
    congr 1
    rw [G.mean_eq i hi c hc _ h1.2, G.mean_eq i hi c hc _ (hiff.1 h1).2]
    have e : (fun b : positivePart (@D.IsPos i) (D.supp c) => valuesOrOne w b.1) =
        fun b => valuesOrOne w' b.1 := funext fun b => hf b.1 b.2.1
    rw [e]
  · rw [if_neg h1, if_neg fun q => h1 (hiff.2 q)]
theorem Admissible.levels_congr (G : D.Admissible k) :
    ∀ u ≤ k, ∀ (c : D.E u) (W W' : D.E 0 → ComplexMatrix2),
      D.IsField W → D.IsField W' → (∀ b ∈ D.support c, W b = W' b) →
        D.levels W u c = D.levels W' u c := by
  intro u
  induction u with
  | zero =>
    intro _ c W W' hW hW' h
    show some (W c) = some (W' c)
    by_cases hc : D.IsPos c
    · rw [h c ⟨hc, G.reaches_self c⟩]
    · have hr := G.isPos_flip_of_not (Nat.zero_le _) hc
      have e := h _ ⟨hr, (G.reaches_flip_right c c).2 (G.reaches_self c)⟩
      have e1 := hW.2 (D.flip c)
      have e2 := hW'.2 (D.flip c)
      rw [G.flip_flip] at e1 e2
      rw [e1, e2, e]
  | succ i ih =>
    intro hi c W W' hW hW' h
    have key : ∀ c' : D.E (i + 1), D.IsPos c' → (∀ b ∈ D.support c', W b = W' b) →
        D.stepMean (D.levels W i) c' = D.stepMean (D.levels W' i) c' := by
      intro c' hc' h'
      refine G.stepMean_congr hi hc' fun b' hb' => ?_
      exact ih (Nat.le_of_succ_le hi) b' W W' hW hW' fun b hb =>
        h' b ⟨hb.1, G.reaches_of_mem i hi c' hc' b' hb' b hb.2⟩
    by_cases hc : D.IsPos c
    · rw [levels_succ_of_isPos W hc, levels_succ_of_isPos W' hc]
      exact key c hc h
    · have hr := G.isPos_flip_of_not hi hc
      rw [levels_succ_of_not_isPos W hc, levels_succ_of_not_isPos W' hc,
        key _ hr fun b hb => h b (by rw [← G.support_flip hi c]; exact hb)]
theorem definedAlike_of_eq {p q : Option ComplexMatrix2} (h : p = q) : DefinedAlike p q := by
  subst h
  exact ⟨Iff.rfl, fun X Y hX hY => Option.some.inj (hX.symm.trans hY)⟩
theorem mem_definedLocus_iff {β : Type} {𝒲 : Set (β → ComplexMatrix2)} {F : Finset β}
    {m : (β → ComplexMatrix2) → Option ComplexMatrix2} {w : F → ComplexMatrix2} :
    w ∈ definedLocus 𝒲 F m ↔
      w ∈ unimodularPi F ∧ ∀ W ∈ 𝒲, (fun b : F => W b) = w → (m W).isSome := Iff.rfl
theorem one_mem_unitDeterminant : (1 : ComplexMatrix2) ∈ ComplexMatrix2.unitDeterminant := by apply _root_.YangMills.Construction.Tower.ComplexMeanMembership.one_mem_gaugeGroup <;> assumption
theorem Admissible.exists_local_representation (G : D.Admissible k)
    (H : GroupLieProduct.ExpChartHolomorphy.ExpChartTheory)
    {u : ℕ} (hu : u ≤ k) (c : D.E u) {F : Finset (D.E 0)} (hpos : ∀ b ∈ F, D.IsPos b)
    {w₀ : F → ComplexMatrix2} (hw : w₀ ∈ unimodularPi F)
    (hs : (D.levels (D.extendByOne F w₀) u c).isSome) :
    ∃ (N : Set (F → ComplexMatrix2)) (g : (F → ComplexMatrix2) → ComplexMatrix2),
      ComplexMatrix2.IsRelativelyOpen (unimodularPi F) N ∧ w₀ ∈ N ∧
      N ⊆ unimodularPi F ∧ IsHolomorphicOnProduct N g ∧
      ∀ w ∈ N, D.levels (D.extendByOne F w) u c = some (g w) := by
  classical
  obtain ⟨F', O', f', wr⟩ :=
    G.exists_representation u hu c _ (extendByOne_spec G hpos hw).1 hs
  have hmember : ∀ b : F', (∃ s : F, ∀ w, D.extendByOneOn F F' w b = w s) ∨
      ∀ w, D.extendByOneOn F F' w b = 1 := by
    intro b
    by_cases h : b.1 ∈ F
    · refine Or.inl ⟨⟨b.1, h⟩, fun w => ?_⟩
      simp only [extendByOneOn, extendByOne, dif_pos h]
    · refine Or.inr fun w => ?_
      have h' : D.flip b.1 ∉ F := fun h' =>
        G.not_isPos_flip (Nat.zero_le _) (wr.pos _ b.2) (hpos _ h')
      simp only [extendByOneOn, extendByOne, dif_neg h, dif_neg h']
  have hcont : Continuous (D.extendByOneOn F F') := continuous_pi fun b => by
    rcases hmember b with ⟨s, hs'⟩ | h1
    · have e : (fun w => D.extendByOneOn F F' w b) = fun w => w s := funext hs'
      rw [e]
      exact continuous_apply s
    · have e : (fun w => D.extendByOneOn F F' w b) = fun _ => 1 := funext h1
      rw [e]
      exact continuous_const
  obtain ⟨A, hA, e⟩ := wr.isOpen
  have hN : ComplexMatrix2.IsRelativelyOpen (unimodularPi F)
      (D.extendByOneOn F F' ⁻¹' A ∩ unimodularPi F) :=
    ⟨_, hA.preimage hcont, rfl⟩
  have hmaps : MapsTo (D.extendByOneOn F F') (D.extendByOneOn F F' ⁻¹' A ∩ unimodularPi F) O' := by
    intro w hw'
    rw [e]
    exact ⟨hw'.1, fun b => (extendByOne_spec G hpos hw'.2).1.1 b⟩
  refine ⟨D.extendByOneOn F F' ⁻¹' A ∩ unimodularPi F, fun w => f' (D.extendByOneOn F F' w), hN,
    ?_, inter_subset_right, ?_, ?_⟩
  · have h1 := wr.mem
    rw [e] at h1
    exact ⟨h1.1, hw⟩
  · refine isHolomorphicOnProduct_comp H hN (fun b => ?_) wr.holo hmaps
    rcases hmember b with ⟨s, hs'⟩ | h1
    · have e' : (fun w => D.extendByOneOn F F' w b) = fun w => w s := funext hs'
      rw [e']
      exact isHolomorphicOnProduct_eval H hN s
    · have e' : (fun w => D.extendByOneOn F F' w b) = fun _ => 1 := funext h1
      rw [e']
      exact isHolomorphicOnProduct_const H hN one_mem_unitDeterminant
  · intro w hw'
    exact wr.eq _ (extendByOne_spec G hpos hw'.2).1 (hmaps hw')
theorem Admissible.dependsOnlyOn (G : D.Admissible k)
    (H : GroupLieProduct.ExpChartHolomorphy.ExpChartTheory)
    {u : ℕ} (hu : u ≤ k) (c : D.E u) {F : Finset (D.E 0)}
    (hF : (F : Set (D.E 0)) = D.support c) {𝒲 : Set (D.E 0 → ComplexMatrix2)}
    (h𝒲 : ∀ W, W ∈ 𝒲 ↔ D.IsField W) :
    DependsOnlyOn 𝒲 F (@D.IsPos 0) D.leftAct fun W => D.levels W u c := by
  classical
  have hmemF : ∀ {b}, b ∈ D.support c → b ∈ F := fun {b} hb => by
    rw [← Finset.mem_coe, hF]
    exact hb
  have hFmem : ∀ {b}, b ∈ F → b ∈ D.support c := fun {b} hb => by
    rw [← hF]
    exact hb
  have hpos : ∀ b ∈ F, D.IsPos b := fun b hb => (hFmem hb).1
  have hag : ∀ W W', D.IsField W → D.IsField W' → (∀ b ∈ F, W b = W' b) →
      D.levels W u c = D.levels W' u c :=
    fun W W' hW hW' h => G.levels_congr u hu c W W' hW hW' fun b hb => h b (hmemF hb)
  have hin : ∀ {W}, D.IsField W → (D.levels W u c).isSome →
      (fun b : F => W b) ∈ definedLocus 𝒲 F fun W => D.levels W u c := by
    intro W hW hs
    refine mem_definedLocus_iff.2 ⟨fun b => hW.1 b, fun W' hW' e => ?_⟩
    show (D.levels W' u c).isSome
    rw [hag W' W ((h𝒲 W').1 hW') hW fun b hb => congrFun e ⟨b, hb⟩]
    exact hs
  have hout : ∀ {w : F → ComplexMatrix2}, w ∈ unimodularPi F →
      (D.levels (D.extendByOne F w) u c).isSome →
      w ∈ definedLocus 𝒲 F fun W => D.levels W u c := by
    intro w hw hs
    have h := hin (extendByOne_spec G hpos hw).1 hs
    rwa [(extendByOne_spec G hpos hw).2] at h
  have hformed : ∀ {w : F → ComplexMatrix2}, w ∈ definedLocus 𝒲 F (fun W => D.levels W u c) →
      (D.levels (D.extendByOne F w) u c).isSome := by
    intro w hw
    have hw' := mem_definedLocus_iff.1 hw
    obtain ⟨hc, hv⟩ := extendByOne_spec G hpos hw'.1
    exact hw'.2 _ ((h𝒲 _).2 hc) hv
  have hopen : ComplexMatrix2.IsRelativelyOpen (unimodularPi F)
      (definedLocus 𝒲 F fun W => D.levels W u c) := by
    refine isRelativelyOpen_of_local (fun w hw => ?_) fun w hw => (mem_definedLocus_iff.1 hw).1
    obtain ⟨N, g, hN, hwN, hsub, _, hv⟩ :=
      G.exists_local_representation H hu c hpos (mem_definedLocus_iff.1 hw).1 (hformed hw)
    refine ⟨N, hN, hwN, fun w' hw' => hout (hsub hw') ?_⟩
    rw [hv w' hw']
    rfl
  have hvalue : ∀ {W : D.E 0 → ComplexMatrix2}, D.IsField W →
      (fun b : F => W b) ∈ definedLocus 𝒲 F (fun W => D.levels W u c) →
      D.levels W u c = some ((D.levels (D.extendByOne F fun b : F => W b) u c).getD 1) := by
    intro W hW hWO
    have hm := (mem_definedLocus_iff.1 hWO).1
    obtain ⟨hc, hv⟩ := extendByOne_spec G hpos hm
    have e := hag W _ hW hc fun b hb => (congrFun hv ⟨b, hb⟩).symm
    have hs := hformed hWO
    rw [← e] at hs ⊢
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 hs
    rw [hx]
    rfl
  refine ⟨?_, hopen, ?_, ?_, ?_, ?_, ?_⟩
  · intro W hW W' hW' h
    exact definedAlike_of_eq (hag W W' ((h𝒲 W).1 hW) ((h𝒲 W').1 hW') h)
  · intro W hW
    exact ⟨fun hs => hin ((h𝒲 W).1 hW) hs,
      fun hO => (mem_definedLocus_iff.1 hO).2 W hW rfl⟩
  · refine ⟨fun w => (D.levels (D.extendByOne F w) u c).getD 1, fun w hw => ?_,
      fun W hW hWO => ?_⟩
    · obtain ⟨N, g, _, hwN, _, hg, hv⟩ :=
        G.exists_local_representation H hu c hpos (mem_definedLocus_iff.1 hw).1 (hformed hw)
      show (D.levels (D.extendByOne F w) u c).getD 1 ∈ PeriodicLattice.complexGaugeGroup
      rw [hv w hwN]
      exact show g (fun s => asGroupFactors w (.inl s)) ∈ ComplexMatrix2.unitDeterminant from
        (hg tracelessBasis).2.1 (mem_image_of_mem asGroupFactors hwN)
    · exact hvalue ((h𝒲 W).1 hW) hWO
  · intro f g hf hg w hw
    have hm := (mem_definedLocus_iff.1 hw).1
    obtain ⟨hc, hv⟩ := extendByOne_spec G hpos hm
    have h1 : D.levels (D.extendByOne F w) u c = some (f fun b : F => D.extendByOne F w b) :=
      hf.eq_some _ ((h𝒲 _).2 hc) (by rw [hv]; exact hw)
    have h2 : D.levels (D.extendByOne F w) u c = some (g fun b : F => D.extendByOne F w b) :=
      hg.eq_some _ ((h𝒲 _).2 hc) (by rw [hv]; exact hw)
    rw [hv] at h1 h2
    exact Option.some.inj (h1.symm.trans h2)
  · intro f hf β
    have hW : ComplexMatrix2.IsRelativelyOpen (GroupLieProduct F Empty)
        (asGroupFactors '' definedLocus 𝒲 F fun W => D.levels W u c) := by
      rw [asGroupFactors_image]
      exact isRelativelyOpen_preimage_leftComponents hopen
    refine isHolomorphicToUnimodular_of_local β hW ?_
    rintro _ ⟨w, hw, rfl⟩
    obtain ⟨N, g, _, hwN, hsub, hg, hv⟩ :=
      G.exists_local_representation H hu c hpos (mem_definedLocus_iff.1 hw).1 (hformed hw)
    have hNO : N ⊆ definedLocus 𝒲 F fun W => D.levels W u c := fun w' hw' =>
      hout (hsub hw') (by rw [hv w' hw']; rfl)
    refine ⟨asGroupFactors '' N, ⟨w, hwN, rfl⟩, image_mono hNO, ?_⟩
    refine isHolomorphicToUnimodular_congr β (hg β) ?_
    rintro _ ⟨w', hw', rfl⟩
    obtain ⟨hc, hvv⟩ := extendByOne_spec G hpos (hsub hw')
    have h1 : D.levels (D.extendByOne F w') u c = some (f fun b : F => D.extendByOne F w' b) :=
      hf.eq_some _ ((h𝒲 _).2 hc) (by rw [hvv]; exact hNO hw')
    rw [hvv, hv w' hw'] at h1
    exact Option.some.inj h1
  · intro U hU U' hU' C C' hC hC' h
    have hconf : ∀ {U C}, U ∈ 𝒲 → (∀ b, D.IsPos b → C b ∈ PeriodicLattice.complexLieAlgebra) →
        D.IsField (D.leftAct C U) := fun hU hC => G.isField_leftAct ((h𝒲 _).1 hU) hC
    refine definedAlike_of_eq (hag _ _ (hconf hU hC) (hconf hU' hC') fun b hb => ?_)
    simp only [leftAct, if_pos (hpos b hb), (h b hb).1, (h b hb).2]
theorem isSome_step {i : ℕ} {c : D.E (i + 1)} (hc : D.IsPos c) {W : D.E 0 → ComplexMatrix2}
    (hs : (D.levels W (i + 1) c).isSome) :
    (∀ b' ∈ D.supp c, (D.levels W i b').isSome) ∧ valuesOrOne (D.levels W i) ∈ D.polydisc c := by
  rw [levels_succ_of_isPos W hc] at hs
  by_contra h
  unfold stepMean at hs
  rw [if_neg h] at hs
  simp at hs
theorem Admissible.holomorphicInRestriction_edge (G : D.Admissible k)
    (H : GroupLieProduct.ExpChartHolomorphy.ExpChartTheory)
    {i : ℕ} (hi : i < k) {c : D.E (i + 1)} (hc : D.IsPos c) {F : Finset (D.E 0)}
    (hF : (F : Set (D.E 0)) = D.support c) {𝒲 : Set (D.E 0 → ComplexMatrix2)}
    (h𝒲 : ∀ W, W ∈ 𝒲 ↔ D.IsField W) {b' : D.E i} (hb' : b' ∈ D.supp c) :
    HolomorphicInRestriction 𝒲 F (definedLocus 𝒲 F fun W => D.levels W (i + 1) c)
      fun W => valuesOrOne (D.levels W i) b' := by
  classical
  have hik : i ≤ k := hi.le
  have hpos : ∀ b ∈ F, D.IsPos b := fun b hb => by
    have h : b ∈ D.support c := by
      rw [← hF]
      exact hb
    exact h.1
  have hF' : (((G.support_finite hik b').toFinset : Finset (D.E 0)) : Set (D.E 0)) =
      D.support b' := Set.Finite.coe_toFinset _
  generalize (G.support_finite hik b').toFinset = F' at hF'
  have R := G.dependsOnlyOn H hik b' hF' h𝒲
  have R₀ := G.dependsOnlyOn H (u := i + 1) hi c hF h𝒲
  have hsub : ∀ b : F', b.1 ∈ F := fun b => by
    have hb : b.1 ∈ D.support b' := by
      rw [← hF']
      exact b.2
    rw [← Finset.mem_coe, hF]
    exact ⟨hb.1, G.reaches_of_mem i hi c hc b' hb' b.1 hb.2⟩
  obtain ⟨f', hf'⟩ := R.exists_representation
  have hh := R.representation_holomorphic f' hf'
  unfold HolomorphicInRestriction
  refine ⟨fun w => f' fun b : F' => w ⟨b.1, hsub b⟩, ?_, fun W hW hWO => ?_⟩
  · refine isHolomorphicOnProduct_comp H R₀.isOpen (Ψ := fun w (b : F') => w ⟨b.1, hsub b⟩)
      (fun b => isHolomorphicOnProduct_eval H R₀.isOpen ⟨b.1, hsub b⟩) hh ?_
    intro w hw
    obtain ⟨hcf, hv⟩ := extendByOne_spec G hpos (mem_definedLocus_iff.1 hw).1
    have hW𝒲 := (h𝒲 _).2 hcf
    have hs : (D.levels (D.extendByOne F w) (i + 1) c).isSome :=
      (mem_definedLocus_iff.1 hw).2 _ hW𝒲 hv
    have h1 : (D.levels (D.extendByOne F w) i b').isSome := (isSome_step hc hs).1 b' hb'
    have h2 := (R.isSome_iff _ hW𝒲).1 h1
    have e : (fun b : F' => D.extendByOne F w b) = fun b : F' => w ⟨b.1, hsub b⟩ :=
      funext fun b => congrFun hv ⟨b.1, hsub b⟩
    rw [e] at h2
    exact h2
  · have hs : (D.levels W (i + 1) c).isSome := (mem_definedLocus_iff.1 hWO).2 W hW rfl
    have h1 : (D.levels W i b').isSome := (isSome_step hc hs).1 b' hb'
    have h2 := (R.isSome_iff W hW).1 h1
    have h3 : D.levels W i b' = some (f' fun b : F' => W b) := hf'.eq_some W hW h2
    show f' _ = (D.levels W i b').getD 1
    rw [h3]
    rfl
theorem Admissible.holomorphicInRestriction_comp (G : D.Admissible k)
    (H : GroupLieProduct.ExpChartHolomorphy.ExpChartTheory)
    {i : ℕ} (hi : i < k) {c : D.E (i + 1)} (hc : D.IsPos c) {F : Finset (D.E 0)}
    (hF : (F : Set (D.E 0)) = D.support c) {𝒲 : Set (D.E 0 → ComplexMatrix2)}
    (h𝒲 : ∀ W, W ∈ 𝒲 ↔ D.IsField W) (Φ : (D.E i → ComplexMatrix2) → ComplexMatrix2)
    [Fintype (positivePart (@D.IsPos i) (D.supp c))]
    (hΦ : ∀ β : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless, IsHolomorphicToUnimodular β
      (leftComponents ⁻¹' positiveImage (@D.IsPos i) (D.supp c) (D.polydisc c))
      ((fun v => Φ (D.extend c v)) ∘ leftComponents))
    (hread : ∀ V ∈ D.polydisc c, Φ V = Φ (D.extend c fun b => V b.1)) :
    HolomorphicInRestriction 𝒲 F (definedLocus 𝒲 F fun W => D.levels W (i + 1) c)
      fun W => Φ (valuesOrOne (D.levels W i)) := by
  classical
  have hpos : ∀ b ∈ F, D.IsPos b := fun b hb => by
    have h : b ∈ D.support c := by
      rw [← hF]
      exact hb
    exact h.1
  have R₀ := G.dependsOnlyOn H (u := i + 1) hi c hF h𝒲
  have hb : ∀ t : positivePart (@D.IsPos i) (D.supp c),
      ∃ f : (F → ComplexMatrix2) → ComplexMatrix2,
      IsHolomorphicOnProduct (definedLocus 𝒲 F fun W => D.levels W (i + 1) c) f ∧
      ∀ W ∈ 𝒲, (fun b : F => W b) ∈ (definedLocus 𝒲 F fun W => D.levels W (i + 1) c) →
        f (fun b : F => W b) = valuesOrOne (D.levels W i) t.1 :=
    fun t => G.holomorphicInRestriction_edge H hi hc hF h𝒲 t.2.1
  choose f hf hv using hb
  unfold HolomorphicInRestriction
  refine ⟨fun w => Φ (D.extend c fun t => f t w), ?_, fun W hW hWO => ?_⟩
  · have hO' : IsHolomorphicOnProduct (positiveImage (@D.IsPos i) (D.supp c) (D.polydisc c))
        (fun v => Φ (D.extend c v)) := fun β => by
      rw [asGroupFactors_image]
      exact hΦ β
    refine isHolomorphicOnProduct_comp H R₀.isOpen (Ψ := fun w t => f t w) hf hO' ?_
    intro w hw
    obtain ⟨hcf, hval⟩ := extendByOne_spec G hpos (mem_definedLocus_iff.1 hw).1
    have hW𝒲 := (h𝒲 _).2 hcf
    have hs : (D.levels (D.extendByOne F w) (i + 1) c).isSome :=
      (mem_definedLocus_iff.1 hw).2 _ hW𝒲 hval
    have hWO : (fun b : F => D.extendByOne F w b) ∈
        (definedLocus 𝒲 F fun W => D.levels W (i + 1) c) := by
      rw [hval]
      exact hw
    refine ⟨_, ⟨valuesOrOne (D.levels (D.extendByOne F w) i), (isSome_step hc hs).2, rfl⟩, ?_⟩
    funext t
    have h := hv t _ hW𝒲 hWO
    rw [hval] at h
    exact h.symm
  · have hs : (D.levels W (i + 1) c).isSome := (mem_definedLocus_iff.1 hWO).2 W hW rfl
    have e : (fun t => f t fun b : F => W b) = fun t => valuesOrOne (D.levels W i) t.1 :=
      funext fun t => hv t W hW hWO
    show Φ (D.extend c fun t => f t fun b : F => W b) = _
    rw [e]
    exact (hread _ (isSome_step hc hs).2).symm
end MeanScheme
section PeriodicSide
def periodicScheme (L n k : ℕ) : MeanScheme where
  E := fun i => Edge L n k i
  flip := fun b => b.opposite
  IsPos := fun b => b.IsPositivelyOriented
  supp := fun {i} c => (PeriodicLattice.bondsInDoubleBlock c : Set (Edge L n k i))
  mean := fun V c => PeriodicLattice.complexBlockAverage V c
  extend := fun {_} c v => DoubleBlockPolydisc.fieldOfValues c v
  r := polydiscRadius L
  Reaches := fun {_} c b => HasEndpointsIn c b
variable {L n k : ℕ}
theorem periodicScheme_levels (W : Edge L n k 0 → ComplexMatrix2) :
    ∀ i, (periodicScheme L n k).levels W i = LevelwiseMeans.levelwiseMean W i
  | 0 => rfl
  | i + 1 => by
    have ih := periodicScheme_levels W i
    funext c
    simp only [MeanScheme.levels, LevelwiseMeans.levelwiseMean, ih]
    rfl
theorem refinedBlock_subset (hZ : BlockPathContourPivotStatement)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hk : 1 ≤ k) {i : ℕ}
    (hi : i < k) (y : Vertex L n k (i + 1)) (x : Vertex L n k i)
    (hx : (x : PeriodicLattice.FourTorus L n) ∈ PeriodicLattice.unitBlock y) :
    PeriodicLattice.refinedBlock i x ⊆ PeriodicLattice.refinedBlock (i + 1) y := by
  have h := ((hZ L hL k (i + 1) (i + 1) hk le_rfl hi).1 n hn).1.eq_biUnion_lower (by omega) y
  intro z hz
  rw [h]
  exact mem_biUnion (show x ∈ (PeriodicLattice.sitesIn (PeriodicLattice.unitBlock y) :
    Set (Vertex L n k i)) from hx) hz
theorem contourMean_congr (hBP : PeriodicLattice.DoubleBlockStructure.Statement)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) {j : ℕ} (hj : j < k)
    {c : Edge L n k (j + 1)} {y : Vertex L n k (j + 1)}
    (hy : y ∈ ({c.source, c.target} : Set (Vertex L n k (j + 1))))
    {x : Vertex L n k j}
    (hx : x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y)
    {V V' : Edge L n k j → ComplexMatrix2}
    (he : ∀ b ∈ (PeriodicLattice.bondsInDoubleBlock c : Set (Edge L n k j)), V b = V' b) :
    PeriodicLattice.complexMeanContourHolonomy V y x =
      PeriodicLattice.complexMeanContourHolonomy V' y x := by apply _root_.YangMills.Construction.Tower.LevelwiseMeans.complexMeanContour_congr <;> assumption
theorem leftAct_mem_periodic (hA : LeftChartFields.Claim)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n)
    (hnp : ∀ b : Edge L n k 0, b.IsPositivelyOriented → ¬ b.opposite.IsPositivelyOriented)
    (hpr : ∀ b : Edge L n k 0, ¬ b.IsPositivelyOriented → b.opposite.IsPositivelyOriented)
    {U : Edge L n k 0 → ComplexMatrix2}
    (hU : U ∈ fieldsIn L n k 0 PeriodicLattice.complexGaugeGroup)
    {C : Edge L n k 0 → ComplexMatrix2}
    (hC : ∀ b : Edge L n k 0, b.IsPositivelyOriented → C b ∈ PeriodicLattice.complexLieAlgebra)
    (b : Edge L n k 0) (hb : b.IsPositivelyOriented) :
    ComplexMatrix2.matExp (Complex.I • C b) * U b ∈ PeriodicLattice.complexGaugeGroup := by
  classical
  have hform : extendOddly C ∈ complexEdgeForms L n k 0 := by
    refine ⟨fun b' hb' => ?_, fun b' => ?_⟩
    · simp only [extendOddly, if_pos hb']
      exact hC b' hb'
    · by_cases hb' : b'.IsPositivelyOriented
      · have hn' : ¬ b'.opposite.IsPositivelyOriented := hnp b' hb'
        simp only [extendOddly, if_pos hb', if_neg hn']
        rfl
      · have hr : b'.opposite.IsPositivelyOriented := hpr b' hb'
        simp only [extendOddly, if_pos hr, if_neg hb', neg_neg]
  have hl := (((hA.2.2 L k 0 hL (Nat.zero_le _)).1 n hn).1.1).2 U hU _ hform ⟨b, hb⟩
  have e : (extendOddly C) b = C b := by
    simp only [extendOddly, if_pos hb]
  have h1 : ∀ t : ℂ, ComplexMatrix2.matExp (Complex.I • (t • extendOddly C b)) * U b ∈
      PeriodicLattice.complexGaugeGroup := hl.1
  have h := h1 1
  rwa [one_smul, e] at h
theorem periodicScheme_admissible (hE : PeriodicLattice.BondEndpointsOrientation.Statement)
    (hP : DoubleBlockPolydisc.PolydiscsHold)
    (hR : PeriodicLattice.ComplexAverageIsLocal)
    (hA : LeftChartFields.Claim)
    (hZ : BlockPathContourPivotStatement)
    (hW : LevelwiseMeans.LevelwiseMeansHold)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hk : 1 ≤ k) :
    (periodicScheme L n k).Admissible k := by
  have hxor : ∀ i ≤ k, ∀ b : Edge L n k i,
      Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented :=
    fun i hi b => ((hE ⟨L, hL, ⟨k, hk⟩, ⟨n, hn⟩⟩ i hi).2.2.2 b).2.2.2.2.2
  have hpoly : ∀ i < k, ∀ c : Edge L n k (i + 1), c.IsPositivelyOriented →
      FiniteOpenPolydisc PeriodicLattice.Bond.opposite PeriodicLattice.Bond.IsPositivelyOriented
        PeriodicLattice.IsGaugeField (doubleBlockBonds c)
        (nearIdentityPolydisc (polydiscRadius L) c) :=
    fun i hi c hc => ((hP L hL k i hi).1 n hn c hc).finite_open
  have hagree : ∀ i < k, ∀ c : Edge L n k (i + 1), c.IsPositivelyOriented →
      ∀ V : Edge L n k i → ComplexMatrix2, V ∈ (periodicScheme L n k).polydisc (i := i) c →
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
  have hself : ∀ y : Vertex L n k 0,
      (y : PeriodicLattice.FourTorus L n) ∈ PeriodicLattice.refinedBlock 0 y := by
    intro y
    have h := ((hZ L hL k 0 0 hk le_rfl (Nat.zero_le _)).1 n hn).1.eq_image y
    rw [h]
    exact ⟨0, mem_offsetBox_iff.2 fun μ => by simp,
      by simp [offsetPoint, PeriodicLattice.pointOnAxis]⟩
  refine ⟨fun b => rfl, hxor, fun i hi c hc => (hpoly i hi c hc).opposite_mem, ?_, ?_,
    hagree, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi c hc
    obtain ⟨b, hb⟩ := (hpoly i hi c hc).positive_nonempty
    exact ⟨b, hb.1, hb.2⟩
  · intro i hi (c : Edge L n k (i + 1)) (hc : c.IsPositivelyOriented)
      (V : Edge L n k i → ComplexMatrix2) hVp
    show PeriodicLattice.complexBlockAverage V c = PeriodicLattice.complexBlockAverage _ c
    unfold PeriodicLattice.complexBlockAverage
    simp only [if_pos hc]
    exact (hR L n k i hL.1 hL.2 hn hi c hc).average_eq _ _ (hagree i hi c hc V hVp)
  · intro u _ (c : Edge L n k u) b
    have e : endpointBlocks c.opposite = endpointBlocks c := union_comm _ _
    show HasEndpointsIn c.opposite b ↔ HasEndpointsIn c b
    simp only [HasEndpointsIn, e]
  · intro c b
    exact and_comm
  · intro (c : Edge L n k 0)
    exact ⟨Or.inl (hself _), Or.inr (hself _)⟩
  · intro i hi (c : Edge L n k (i + 1)) (hc : c.IsPositivelyOriented) (b' : Edge L n k i) hb' b he
    have hsub : ∀ x ∈ (PeriodicLattice.unitBlock c.source ∪ PeriodicLattice.unitBlock c.target :
        Set (PeriodicLattice.FourTorus L n)), ∀ x' : Vertex L n k i,
        (x' : PeriodicLattice.FourTorus L n) = x →
        PeriodicLattice.refinedBlock i x' ⊆ endpointBlocks c := by
      rintro x (hx | hx) x' rfl z hz
      · exact Or.inl (refinedBlock_subset hZ hL hn hk hi _ x' hx hz)
      · exact Or.inr (refinedBlock_subset hZ hL hn hk hi _ x' hx hz)
    have hsub' : endpointBlocks b' ⊆ endpointBlocks c := by
      rintro z (hz | hz)
      · exact hsub _ hb'.1 _ rfl hz
      · exact hsub _ hb'.2 _ rfl hz
    exact ⟨hsub' he.1, hsub' he.2⟩
  · intro u hu (c : Edge L n k u) (hc : c.IsPositivelyOriented)
    have h := (((hZ L hL k u u hk le_rfl hu).1 n hn).2.2.2.2.1).bonds_encard_le c hc
    generalize hv : u - u = v at h
    obtain rfl : v = 0 := by omega
    exact Set.finite_of_encard_le_coe h
  · intro u hu c U hU hs
    have hU' : U ∈ fieldsIn L n k 0 PeriodicLattice.complexGaugeGroup :=
      ⟨fun b _ => hU.1 b, fun b _ => hU.2 b⟩
    have e : (periodicScheme L n k).levels U u c = LevelwiseMeans.levelwiseMean U u c :=
      congrFun (periodicScheme_levels U u) c
    have hs' : LevelwiseMeans.IsDefinedAt U u c := by
      unfold LevelwiseMeans.IsDefinedAt
      rw [← e]
      exact hs
    obtain ⟨F, O, f, w⟩ := ((hW L hL k hk).1 n hn).exists_representation u hu c U hU' hs'
    exact ⟨F, O, f, ⟨w.positive, w.isOpen, w.mem, w.holomorphic, fun W hW' hO =>
      (congrFun (periodicScheme_levels W u) c).trans
        (w.eq_some W ⟨fun b _ => hW'.1 b, fun b _ => hW'.2 b⟩ hO)⟩⟩
  · intro U hU C hC b hb
    have hnp : ∀ b : Edge L n k 0, b.IsPositivelyOriented →
        ¬ b.opposite.IsPositivelyOriented := by
      intro b hb
      rcases hxor 0 (Nat.zero_le _) b with h | h
      · exact h.2
      · exact absurd hb h.2
    have hpr : ∀ b : Edge L n k 0, ¬ b.IsPositivelyOriented →
        b.opposite.IsPositivelyOriented := by
      intro b hb
      rcases hxor 0 (Nat.zero_le _) b with h | h
      · exact absurd h.1 hb
      · exact h.1
    exact leftAct_mem_periodic hA hL hn hnp hpr ⟨fun b _ => hU.1 b, fun b _ => hU.2 b⟩ hC b hb
theorem sideRelations_periodic (G : (periodicScheme L n k).Admissible k)
    (H : GroupLieProduct.ExpChartHolomorphy.ExpChartTheory)
    (hP : DoubleBlockPolydisc.PolydiscsHold)
    (hBP : PeriodicLattice.DoubleBlockStructure.Statement)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) : SideRequirements L n k := by
  have ee : (periodicScheme L n k).levels = LevelwiseMeans.levelwiseMean :=
    funext fun W => funext fun j => periodicScheme_levels W j
  have hc𝒲 : ∀ W, W ∈ baseFields L n k ↔ (periodicScheme L n k).IsField W :=
    fun W => ⟨fun h => ⟨fun b => h.1 b (mem_univ _), fun b => h.2 b (mem_univ _)⟩,
      fun h => ⟨fun b _ => h.1 b, fun b _ => h.2 b⟩⟩
  refine ⟨fun u hu c => ⟨G.support_finite hu c, G.support_nonempty u hu c⟩,
    fun i hi c hc b' hb' b hb => G.reaches_of_mem i hi c hc b' hb' b hb, ?_, ?_⟩
  · intro u hu c F hF
    have h := G.dependsOnlyOn H hu c hF hc𝒲
    rw [ee] at h
    exact h
  · intro i hi c hc F hF
    refine ⟨fun W hW hO => ?_, fun b' hb' => ?_, fun y hy x hx => ?_⟩
    · have R := G.dependsOnlyOn H (u := i + 1) hi c hF hc𝒲
      rw [ee] at R
      have hs : ((periodicScheme L n k).levels W (i + 1) c).isSome := by
        rw [ee]
        exact (R.isSome_iff W hW).2 hO
      have h := MeanScheme.isSome_step (D := periodicScheme L n k) hc hs
      rw [ee] at h
      exact h
    · have h := G.holomorphicInRestriction_edge H hi hc hF hc𝒲 hb'
      rw [ee] at h
      exact h
    · obtain ⟨inst, hΦ⟩ := ((hP L hL k i hi).1 n hn c hc).holomorphic_contourMean y hy x hx
      let _ : Fintype (positivePart (@MeanScheme.IsPos (periodicScheme L n k) i)
        ((periodicScheme L n k).supp c)) := inst
      have h := G.holomorphicInRestriction_comp H hi hc hF hc𝒲
        (fun V => PeriodicLattice.complexMeanContourHolonomy V y x) hΦ.toUnimodular
        (fun V hV => contourMean_congr hBP hL hn hi hy hx (G.eq_extend i hi c hc V hV))
      rw [ee] at h
      exact h
end PeriodicSide
namespace Unbounded
def unboundedScheme (L k : ℕ) : MeanScheme where
  E := fun i => FullSpace.Edge L k i
  flip := fun b => b.opposite
  IsPos := fun b => b.IsPositivelyOriented
  supp := fun {i} c => FullSpace.doubleCubeLinks L (meshAt L k i) c
  mean := fun {_} V c => FullSpace.complexSmoothing L V c
  extend := fun {i} c v => DoubleBlockPolydisc.Infinite.fieldOfValues L k i c v
  r := polydiscRadius L
  Reaches := fun {_} c b => HasEndpointsIn c b
variable {L k : ℕ}
theorem unboundedScheme_levels (W : FullSpace.Edge L k 0 → ComplexMatrix2) :
    ∀ i, (unboundedScheme L k).levels W i = LevelwiseMeans.Unbounded.levelwiseMean W i
  | 0 => rfl
  | i + 1 => by
    have ih := unboundedScheme_levels W i
    funext c
    simp only [MeanScheme.levels, LevelwiseMeans.Unbounded.levelwiseMean, ih]
    rfl
theorem xor_isPositivelyOriented_opposite {a : ℝ} (ha : 0 < a) (b : InfiniteLattice.Link a) :
    Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.Tower.LevelwiseMeans.Unbounded.xor_isPositivelyOriented_opposite <;> assumption
theorem meshAt_pos (hL : Conventions.IsAdmissibleBlockingFactor L) (i : ℕ) :
    0 < meshAt L k i := by apply _root_.YangMills.Construction.Tower.LevelwiseMeans.Unbounded.meshAt_pos <;> assumption
theorem cubeOfOrder_subset (hZ : BlockPathContourPivotStatement)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hk : 1 ≤ k) {i : ℕ} (hi : i < k)
    (y : FullSpace.Vertex L k (i + 1)) (x : FullSpace.Vertex L k i)
    (hx : (x : InfiniteLattice.AmbientSpace) ∈ FullSpace.cube L (meshAt L k i) y) :
    FullSpace.cubeOfOrder L (meshAt L k 0) i x ⊆
      FullSpace.cubeOfOrder L (meshAt L k 0) (i + 1) y := by
  have h := ((hZ L hL k (i + 1) (i + 1) hk le_rfl hi).2.1).eq_biUnion_lower (by omega) y
  rw [Nat.sub_self] at h
  intro z hz
  rw [h]
  exact mem_biUnion (show x ∈ FullSpace.cubeVertices L (meshAt L k i) y from hx) hz
theorem contourMean_congr (hS : SmoothingNearIdentity)
    (hQ : SublatticesSymmetriesScalingsAndProjections.Statement)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hk : 1 ≤ k) {j : ℕ} (hj : j < k)
    {c : FullSpace.Edge L k (j + 1)} (hc : c.IsPositivelyOriented)
    {y : FullSpace.Vertex L k (j + 1)}
    (hy : y ∈ ({c.initial, c.terminal} : Set (FullSpace.Vertex L k (j + 1))))
    {x : FullSpace.Vertex L k j} (hx : x ∈ FullSpace.cubeVertices L (meshAt L k j) y)
    {V V' : FullSpace.Edge L k j → ComplexMatrix2}
    (hV : V ∈ (unboundedScheme L k).polydisc (i := j) c)
    (hV' : V' ∈ (unboundedScheme L k).polydisc (i := j) c)
    (he : ∀ b ∈ FullSpace.doubleCubeLinks L (meshAt L k j) c, V b = V' b) :
    FullSpace.complexContourMean L V y x = FullSpace.complexContourMean L V' y x := by
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
  unfold FullSpace.projField
  split_ifs with h
  · exact he _ h.choose_spec.1
  · rfl
theorem leftAct_mem_unbounded (hA : LeftChartFields.Claim)
    (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hnp : ∀ b : FullSpace.Edge L k 0, b.IsPositivelyOriented →
      ¬ b.opposite.IsPositivelyOriented)
    (hpr : ∀ b : FullSpace.Edge L k 0, ¬ b.IsPositivelyOriented →
      b.opposite.IsPositivelyOriented)
    {U : FullSpace.Edge L k 0 → ComplexMatrix2}
    (hU : U ∈ FullSpace.fieldsValuedIn L k 0 PeriodicLattice.complexGaugeGroup)
    {C : FullSpace.Edge L k 0 → ComplexMatrix2}
    (hC : ∀ b : FullSpace.Edge L k 0, b.IsPositivelyOriented →
      C b ∈ PeriodicLattice.complexLieAlgebra)
    (b : FullSpace.Edge L k 0) (hb : b.IsPositivelyOriented) :
    ComplexMatrix2.matExp (Complex.I • C b) * U b ∈ PeriodicLattice.complexGaugeGroup := by
  classical
  have hform : FullSpace.extendOddly C ∈ FullSpace.complexEdgeForms (meshAt L k 0) := by
    refine ⟨fun b' hb' => ?_, fun b' => ?_⟩
    · simp only [FullSpace.extendOddly, if_pos hb']
      exact hC b' hb'
    · by_cases hb' : b'.IsPositivelyOriented
      · have hn' : ¬ b'.opposite.IsPositivelyOriented := hnp b' hb'
        simp only [FullSpace.extendOddly, if_pos hb', if_neg hn']
        rfl
      · have hr : b'.opposite.IsPositivelyOriented := hpr b' hb'
        simp only [FullSpace.extendOddly, if_pos hr, if_neg hb', neg_neg]
  have hl := (((hA.2.2 L k 0 hL (Nat.zero_le _)).2.1).1).2 U hU _ hform ⟨b, hb⟩
  have e : (FullSpace.extendOddly C) b = C b := by
    simp only [FullSpace.extendOddly, if_pos hb]
  have h1 : ∀ t : ℂ, ComplexMatrix2.matExp (Complex.I • (t • FullSpace.extendOddly C b)) * U b ∈
      PeriodicLattice.complexGaugeGroup := hl.1
  have h := h1 1
  rwa [one_smul, e] at h
theorem unboundedScheme_admissible (hP : DoubleBlockPolydisc.PolydiscsHold)
    (hS : SmoothingNearIdentity)
    (hQ : SublatticesSymmetriesScalingsAndProjections.Statement)
    (hA : LeftChartFields.Claim)
    (hZ : BlockPathContourPivotStatement)
    (hW : LevelwiseMeans.LevelwiseMeansHold)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hk : 1 ≤ k) :
    (unboundedScheme L k).Admissible k := by
  have hL0 : 0 < L := by
    have := hL.2
    omega
  have hxor : ∀ i ≤ k, ∀ b : FullSpace.Edge L k i,
      Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented :=
    fun i _ b => xor_isPositivelyOriented_opposite (meshAt_pos hL i) b
  have hpoly : ∀ i < k, ∀ c : FullSpace.Edge L k (i + 1), c.IsPositivelyOriented →
      FiniteOpenPolydisc InfiniteLattice.Link.opposite
        InfiniteLattice.Link.IsPositivelyOriented FullSpace.IsFieldOn
        (DoubleBlockPolydisc.Infinite.doubleBlockBonds L k i c)
        (FullSpace.nearIdentityPolydisc L k i (polydiscRadius L) c) :=
    fun i hi c hc => ((hP L hL k i hi).2 c hc).finite_open
  have hserve := fun i (hi : i < k) (c : FullSpace.Edge L k (i + 1))
      (hc : c.IsPositivelyOriented) => (hS.1 L hL).2.2.fullSpace k i hi c hc
  have hagree : ∀ i < k, ∀ c : FullSpace.Edge L k (i + 1), c.IsPositivelyOriented →
      ∀ V ∈ (unboundedScheme L k).polydisc c,
      ∀ b ∈ FullSpace.doubleCubeLinks L (meshAt L k i) c,
        V b = DoubleBlockPolydisc.Infinite.fieldOfValues L k i c (fun b => V b.1) b := by
    intro i hi c hc (V : FullSpace.Edge L k i → ComplexMatrix2) hVp b hb
    unfold DoubleBlockPolydisc.Infinite.fieldOfValues FullSpace.extendFromPositive
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
  have hself : ∀ (a : ℝ) {u : ℕ} (y : FullSpace.Vertex L k u),
      (y : InfiniteLattice.AmbientSpace) ∈ FullSpace.cubeOfOrder L a 0 y :=
    fun a u y => ⟨0, fun μ => by simp, by simp⟩
  refine ⟨fun b => rfl, hxor, fun i hi c hc => (hpoly i hi c hc).opposite_mem, ?_, ?_,
    hagree, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi c hc
    obtain ⟨b, hb⟩ := (hpoly i hi c hc).positive_nonempty
    exact ⟨b, hb.1, hb.2⟩
  · intro i hi c hc V hVp
    have hVp' := MeanScheme.polydisc_congr (D := unboundedScheme L k)
      ((hpoly i hi c hc).opposite_mem) hVp (hagree i hi c hc V hVp)
    have hQ' := ((hQ L hL0 hL k).2.2.2.2.2.2 hk 1 one_pos).2 i hi c hc
    have e1 := hQ'.complexSmoothing_eq V ((hserve i hi c hc).subset_complexDomain hVp)
    have e2 := hQ'.complexSmoothing_eq _ ((hserve i hi c hc).subset_complexDomain hVp')
    refine e1.trans (Eq.trans ?_ e2.symm)
    congr 1
    funext x
    unfold FullSpace.projField
    split_ifs with h
    · exact hagree i hi c hc V hVp _ h.choose_spec.1
    · rfl
  · intro u _ (c : FullSpace.Edge L k u) b
    have e : endpointBlocks c.opposite = endpointBlocks c := union_comm _ _
    show HasEndpointsIn c.opposite b ↔ HasEndpointsIn c b
    simp only [HasEndpointsIn, e]
  · intro c b
    exact and_comm
  · intro (c : FullSpace.Edge L k 0)
    exact ⟨Or.inl (hself _ _), Or.inr (hself _ _)⟩
  · intro i hi (c : FullSpace.Edge L k (i + 1)) (hc : c.IsPositivelyOriented)
      (b' : FullSpace.Edge L k i) hb' b he
    have hsub : ∀ x ∈ (FullSpace.cube L (meshAt L k i) c.initial ∪
        FullSpace.cube L (meshAt L k i) c.terminal : Set InfiniteLattice.AmbientSpace),
        ∀ x' : FullSpace.Vertex L k i, (x' : InfiniteLattice.AmbientSpace) = x →
        FullSpace.cubeOfOrder L (meshAt L k 0) i x' ⊆ endpointBlocks c := by
      rintro x (hx | hx) x' rfl z hz
      · exact Or.inl (cubeOfOrder_subset hZ hL hk hi _ x' hx hz)
      · exact Or.inr (cubeOfOrder_subset hZ hL hk hi _ x' hx hz)
    have hsub' : endpointBlocks b' ⊆ endpointBlocks c := by
      rintro z (hz | hz)
      · exact hsub _ hb'.1 _ rfl hz
      · exact hsub _ hb'.2 _ rfl hz
    exact ⟨hsub' he.1, hsub' he.2⟩
  · intro u hu (c : FullSpace.Edge L k u) (hc : c.IsPositivelyOriented)
    have h := ((hZ L hL k u u hk le_rfl hu).2.2.2.2.2.1).bonds_encard_le c hc
    generalize hv : u - u = v at h
    obtain rfl : v = 0 := by omega
    exact Set.finite_of_encard_le_coe h
  · intro u hu c U hU hs
    have e : (unboundedScheme L k).levels U u c =
        LevelwiseMeans.Unbounded.levelwiseMean U u c :=
      congrFun (unboundedScheme_levels U u) c
    have hs' : LevelwiseMeans.Unbounded.IsDefinedAt U u c := by
      unfold LevelwiseMeans.Unbounded.IsDefinedAt
      rw [← e]
      exact hs
    obtain ⟨F, O, f, w⟩ := (hW L hL k hk).2.exists_representation u hu c U hU hs'
    exact ⟨F, O, f, ⟨w.finite_edges.2, w.isOpen, w.mem, w.holomorphic, fun W hW' hO =>
      (congrFun (unboundedScheme_levels W u) c).trans (w.eq_some W hW' hO)⟩⟩
  · intro U hU C hC b hb
    have hnp : ∀ b : FullSpace.Edge L k 0, b.IsPositivelyOriented →
        ¬ b.opposite.IsPositivelyOriented := by
      intro b hb
      rcases hxor 0 (Nat.zero_le _) b with h | h
      · exact h.2
      · exact absurd hb h.2
    have hpr : ∀ b : FullSpace.Edge L k 0, ¬ b.IsPositivelyOriented →
        b.opposite.IsPositivelyOriented := by
      intro b hb
      rcases hxor 0 (Nat.zero_le _) b with h | h
      · exact absurd h.1 hb
      · exact h.1
    exact leftAct_mem_unbounded hA hL hnp hpr hU hC b hb
theorem sideRelations_unbounded (G : (unboundedScheme L k).Admissible k)
    (H : GroupLieProduct.ExpChartHolomorphy.ExpChartTheory)
    (hP : DoubleBlockPolydisc.PolydiscsHold)
    (hS : SmoothingNearIdentity)
    (hQ : SublatticesSymmetriesScalingsAndProjections.Statement)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hk : 1 ≤ k) : SideRequirements L k := by
  have ee : (unboundedScheme L k).levels = LevelwiseMeans.Unbounded.levelwiseMean :=
    funext fun W => funext fun j => unboundedScheme_levels W j
  have hc𝒲 : ∀ W, W ∈ baseFields L k ↔ (unboundedScheme L k).IsField W := fun W => Iff.rfl
  refine ⟨fun u hu c => ⟨G.support_finite hu c, G.support_nonempty u hu c⟩,
    fun i hi c hc b' hb' b hb => G.reaches_of_mem i hi c hc b' hb' b hb, ?_, ?_⟩
  · intro u hu c F hF
    have h := G.dependsOnlyOn H hu c hF hc𝒲
    rw [ee] at h
    exact h
  · intro i hi c hc F hF
    refine ⟨fun W hW hO => ?_, fun b' hb' => ?_, fun y hy x hx => ?_⟩
    · have R := G.dependsOnlyOn H (u := i + 1) hi c hF hc𝒲
      rw [ee] at R
      have hs : ((unboundedScheme L k).levels W (i + 1) c).isSome := by
        rw [ee]
        exact (R.isSome_iff W hW).2 hO
      have h := MeanScheme.isSome_step (D := unboundedScheme L k) hc hs
      rw [ee] at h
      exact h
    · have h := G.holomorphicInRestriction_edge H hi hc hF hc𝒲 hb'
      rw [ee] at h
      exact h
    · obtain ⟨inst, hΦ⟩ := ((hP L hL k i hi).2 c hc).holomorphic_contourMean y hy x hx
      let _ : Fintype (positivePart (@MeanScheme.IsPos (unboundedScheme L k) i)
        ((unboundedScheme L k).supp c)) := inst
      have h := G.holomorphicInRestriction_comp H hi hc hF hc𝒲
        (fun V => FullSpace.complexContourMean L V y x) hΦ.toUnimodular
        (fun V hV => contourMean_congr hS hQ hL hk hi hc hy hx hV
          (MeanScheme.polydisc_congr (G.flip_mem i hi c hc) hV (G.eq_extend i hi c hc V hV))
          (G.eq_extend i hi c hc V hV))
      rw [ee] at h
      exact h
end Unbounded
theorem supportOfMeans_holds (H : GroupLieProduct.ExpChartHolomorphy.ExpChartTheory)
    (hE : PeriodicLattice.BondEndpointsOrientation.Statement)
    (hP : DoubleBlockPolydisc.PolydiscsHold)
    (hS : SmoothingNearIdentity)
    (hR : PeriodicLattice.ComplexAverageIsLocal)
    (hA : LeftChartFields.Claim)
    (hBP : PeriodicLattice.DoubleBlockStructure.Statement)
    (hQ : SublatticesSymmetriesScalingsAndProjections.Statement)
    (hZ : BlockPathContourPivotStatement)
    (hW : LevelwiseMeans.LevelwiseMeansHold) : SupportOfMeansHolds :=
  fun L hL k hk =>
    ⟨fun n hn => sideRelations_periodic (periodicScheme_admissible hE hP hR hA hZ hW hL hn hk)
        H hP hBP hL hn,
      Unbounded.sideRelations_unbounded (Unbounded.unboundedScheme_admissible hP hS hQ hA hZ hW hL hk)
        H hP hS hQ hL hk⟩
end YangMills.Construction.Tower.SupportOfMeans
end
