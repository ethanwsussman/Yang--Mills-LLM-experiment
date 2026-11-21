import YangMills.Construction.Matrices.FiniteMatrixProducts
import YangMills.Construction.Towers.BlocksOfATower
import YangMills.Construction.Towers.ComplexAveragesFormedLevelByLevelProof
import YangMills.Construction.Towers.ConfigurationsWhoseAveragesStayInThePolydiscs
import YangMills.Construction.Towers.OneValueForEveryWriting
import Mathlib
set_option autoImplicit false
open Set Filter YangMills.Construction.Matrices YangMills.Construction.Matrices.GroupLieProduct
open scoped Topology Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.Tower.MeanStableFields
open YangMills.Construction.Tower.LevelwiseMeans
section Rules
open YangMills.Construction.Coordinates.ComplexCoordinates
variable {ι ι' : Type} [Fintype ι] [Fintype ι']
variable (H : ExpChartHolomorphy.ExpChartTheory)
  (β : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless)
include H
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
omit H [Fintype ι'] in
theorem isHolomorphicToUnimodular_of_local {W : Set (ι ⊕ Empty → ComplexMatrix2)}
    {Φ : (ι ⊕ Empty → ComplexMatrix2) → ComplexMatrix2}
    (hW : ComplexMatrix2.IsRelativelyOpen (GroupLieProduct ι Empty) W)
    (h : ∀ p ∈ W, ∃ W' : Set (ι ⊕ Empty → ComplexMatrix2),
      p ∈ W' ∧ W' ⊆ W ∧ IsHolomorphicToUnimodular β W' Φ) :
    IsHolomorphicToUnimodular β W Φ := by
  refine ⟨hW, fun p hp => ?_, fun p hp => ?_, fun p hp => ?_⟩
  · obtain ⟨W', hp', _, hΦ⟩ := h p hp
    exact hΦ.2.1 hp'
  · obtain ⟨W', hp', hs, hΦ⟩ := h p hp
    obtain ⟨O', hO', e⟩ := hΦ.1
    refine (hΦ.2.2.1 p hp').mono_of_mem_nhdsWithin ?_
    have hsub : O' ∩ W ⊆ W' := fun q hq => by
      obtain ⟨O, _, e'⟩ := hW
      rw [e]
      refine ⟨hq.1, ?_⟩
      rw [e'] at hq
      exact hq.2.2
    refine mem_of_superset ?_ hsub
    rw [inter_comm]
    refine inter_mem_nhdsWithin _ (hO'.mem_nhds ?_)
    rw [e] at hp'
    exact hp'.1
  · obtain ⟨W', hp', hs, hΦ⟩ := h p hp
    obtain ⟨O, h0, hO, ht⟩ := hΦ.2.2.2 p hp'
    exact ⟨O, h0, fun A hA => ⟨hs (hO A hA).1, (hO A hA).2⟩, ht⟩
end Rules
section Points
variable {σ : Type}
theorem asGroupFactors_image (O : Set (σ → ComplexMatrix2)) :
    asGroupFactors '' O = DoubleBlockPolydisc.leftComponents ⁻¹' O := by apply _root_.YangMills.Construction.Tower.LevelwiseMeans.image_asGroupFactors <;> assumption
theorem continuous_asGroupFactors :
    Continuous (asGroupFactors : (σ → ComplexMatrix2) → σ ⊕ Empty → ComplexMatrix2) := by apply _root_.YangMills.SharedProofs.p11373 <;> assumption
theorem isRelativelyOpen_leftComponents_preimage {O : Set (σ → ComplexMatrix2)}
    (h : ComplexMatrix2.IsRelativelyOpen (unimodularPi σ) O) :
    ComplexMatrix2.IsRelativelyOpen (GroupLieProduct σ Empty)
      (DoubleBlockPolydisc.leftComponents ⁻¹' O) := by apply _root_.YangMills.Construction.Tower.LevelwiseMeans.isRelativelyOpen_preimage_leftComponents <;> assumption
theorem exists_near_of_relativelyOpen (hE4 : FamilyProducts.FamilyProductsStatement) [Fintype σ]
    [Nonempty σ] (β : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless)
    {O : Set (σ → ComplexMatrix2)} {f : (σ → ComplexMatrix2) → ComplexMatrix2}
    {u : σ → ComplexMatrix2} (hO : ComplexMatrix2.IsRelativelyOpen (unimodularPi σ) O)
    (hu : u ∈ O)
    (hf : IsHolomorphicToUnimodular β (asGroupFactors '' O) fun p => f fun b => p (.inl b))
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ w ∈ unimodularPi σ,
      (∀ b, ComplexMatrix2.operatorNorm (w b - u b) < ε) →
        w ∈ O ∧ ComplexMatrix2.operatorNorm (f w - f u) < δ := by
  obtain ⟨O₁, hO₁, rfl⟩ := hO
  have hcont : ContinuousOn f (O₁ ∩ unimodularPi σ) :=
    hf.2.2.1.comp continuous_asGroupFactors.continuousOn (mapsTo_image _ _)
  have hN : {x : ComplexMatrix2 | ComplexMatrix2.operatorNorm (x - f u) < δ} ∈ 𝓝 (f u) :=
    (isOpen_lt (continuous_norm.comp (continuous_id.sub continuous_const))
      continuous_const).mem_nhds (by simpa using hδ)
  obtain ⟨N, hN', hs⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.1 (hcont u hu hN)
  obtain ⟨ε, hε, hb⟩ := ((hE4 σ).1 u).2 (N ∩ O₁) (inter_mem hN' (hO₁.mem_nhds hu.1))
  refine ⟨ε, hε, fun w hw hc => ?_⟩
  have hwb := hb (show w ∈ FamilyProducts.familyNbhd u ε from hc)
  exact ⟨⟨hwb.2, hw⟩, hs ⟨hwb.1, hwb.2, hw⟩⟩
end Points
theorem finrank_traceless : Module.finrank ℂ ComplexMatrix2.traceless = 3 := by apply _root_.YangMills.SharedProofs.p8292 <;> assumption
def tracelessBasis : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless :=
  Module.finBasisOfFinrankEq ℂ _ finrank_traceless
structure TowerSkeleton where
  Edges : ℕ → Type
  opp : ∀ {i : ℕ}, Edges i → Edges i
  IsPos : ∀ {i : ℕ}, Edges i → Prop
  support : ∀ {i : ℕ}, Edges (i + 1) → Set (Edges i)
  mean : ∀ {i : ℕ}, (Edges i → ComplexMatrix2) → Edges (i + 1) → ComplexMatrix2
  radius : ℝ
namespace TowerSkeleton
variable (D : TowerSkeleton)
def IsField {i : ℕ} (V : D.Edges i → ComplexMatrix2) : Prop :=
  (∀ b, V b ∈ PeriodicLattice.complexGaugeGroup) ∧ ∀ b, V (D.opp b) = (V b)⁻¹
structure IsMeanChain (j : ℕ) (V : ∀ i : ℕ, D.Edges i → ComplexMatrix2) : Prop where
  isField : ∀ i ≤ j, D.IsField (V i)
  near_one : ∀ i < j, ∀ b, ComplexMatrix2.operatorNorm (V i b - 1) < D.radius
  eq_mean : ∀ i < j, ∀ c : D.Edges (i + 1), D.IsPos c → V (i + 1) c = D.mean (V i) c
structure IsRegular (k : ℕ) : Prop where
  opp_opp : ∀ {i : ℕ} (b : D.Edges i), D.opp (D.opp b) = b
  xor_isPos : ∀ i ≤ k, ∀ b : D.Edges i, Xor (D.IsPos b) (D.IsPos (D.opp b))
  mean_mem : ∀ i < k, ∀ c : D.Edges (i + 1), D.IsPos c → ∀ V : D.Edges i → ComplexMatrix2,
    D.IsField V → (∀ b, ComplexMatrix2.operatorNorm (V b - 1) < D.radius) →
      D.mean V c ∈ PeriodicLattice.complexGaugeGroup
  mean_congr : ∀ i < k, ∀ c : D.Edges (i + 1), D.IsPos c →
    ∀ V V' : D.Edges i → ComplexMatrix2, D.IsField V → D.IsField V' →
    (∀ b, ComplexMatrix2.operatorNorm (V b - 1) < D.radius) →
    (∀ b, ComplexMatrix2.operatorNorm (V' b - 1) < D.radius) →
    (∀ b ∈ D.support c, V b = V' b) → D.mean V c = D.mean V' c
  incidence_finite : ∀ i < k, ∀ b : D.Edges i,
    {c : D.Edges (i + 1) | D.IsPos c ∧ b ∈ D.support c}.Finite
def EntriesContinuous (k : ℕ) : Prop :=
  ∀ j ≤ k, ∀ V : ∀ i : ℕ, D.Edges i → ComplexMatrix2, D.IsMeanChain j V →
    ∀ (c : D.Edges j) (δ : ℝ), 0 < δ →
    ∃ (F : Finset (D.Edges 0)) (ε : ℝ), 0 < ε ∧ (∀ b ∈ F, D.IsPos b) ∧
      ∀ W : D.Edges 0 → ComplexMatrix2, D.IsField W →
        (∀ b ∈ F, ComplexMatrix2.operatorNorm (W b - V 0 b) < ε) →
        ∀ V' : ∀ i : ℕ, D.Edges i → ComplexMatrix2, D.IsMeanChain j V' → V' 0 = W →
          ComplexMatrix2.operatorNorm (V' j c - V j c) < δ
variable {D}
theorem IsMeanChain.mono {j j' : ℕ} {V : ∀ i : ℕ, D.Edges i → ComplexMatrix2}
    (h : D.IsMeanChain j V) (hj : j' ≤ j) : D.IsMeanChain j' V :=
  ⟨fun i hi => h.isField i (hi.trans hj), fun i hi => h.near_one i (hi.trans_le hj),
    fun i hi => h.eq_mean i (hi.trans_le hj)⟩
end TowerSkeleton
theorem inv_mem_unitDeterminant {X : ComplexMatrix2} (h : X ∈ ComplexMatrix2.unitDeterminant) :
    X⁻¹ ∈ ComplexMatrix2.unitDeterminant := by apply _root_.YangMills.SharedProofs.p413 <;> assumption
theorem inv_inv_of_mem_unitDeterminant {X : ComplexMatrix2}
    (h : X ∈ ComplexMatrix2.unitDeterminant) : X⁻¹⁻¹ = X := by apply _root_.YangMills.Construction.Tower.LevelwiseMeans.inv_inv_of_mem_unitDeterminant <;> assumption
theorem exists_pos_forall_finset {τ : Type} (T : Finset τ) (Q : τ → ℝ → Prop)
    (hmono : ∀ t ε ε', ε' ≤ ε → Q t ε → Q t ε') (h : ∀ t ∈ T, ∃ ε : ℝ, 0 < ε ∧ Q t ε) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t ∈ T, Q t ε := by
  classical
  induction T using Finset.induction_on with
  | empty => exact ⟨1, one_pos, by simp⟩
  | insert a T _ ih =>
    obtain ⟨ε₁, h₁, q₁⟩ := ih fun t ht => h t (Finset.mem_insert_of_mem ht)
    obtain ⟨ε₂, h₂, q₂⟩ := h a (Finset.mem_insert_self _ _)
    refine ⟨min ε₁ ε₂, lt_min h₁ h₂, fun t ht => ?_⟩
    rcases Finset.mem_insert.1 ht with rfl | ht
    · exact hmono _ _ _ (min_le_right _ _) q₂
    · exact hmono _ _ _ (min_le_left _ _) (q₁ t ht)
theorem operatorNorm_sub_one_le (A B : ComplexMatrix2) :
    ComplexMatrix2.operatorNorm (A - 1) ≤
      ComplexMatrix2.operatorNorm (A - B) + ComplexMatrix2.operatorNorm (B - 1) := by
  have e : A - 1 = (A - B) + (B - 1) := by abel
  show ‖A - 1‖ ≤ ‖A - B‖ + ‖B - 1‖
  rw [e]
  exact norm_add_le _ _
namespace TowerSkeleton
variable {D : TowerSkeleton} {k : ℕ}
theorem IsRegular.isPos_opp_of_not (G : D.IsRegular k) {i : ℕ} (hi : i ≤ k) {b : D.Edges i}
    (h : ¬ D.IsPos b) : D.IsPos (D.opp b) := by
  rcases G.xor_isPos i hi b with h' | h'
  · exact absurd h'.1 h
  · exact h'.1
theorem IsRegular.not_isPos_opp (G : D.IsRegular k) {i : ℕ} (hi : i ≤ k) {b : D.Edges i}
    (h : D.IsPos b) : ¬ D.IsPos (D.opp b) := by
  rcases G.xor_isPos i hi b with h' | h'
  · exact h'.2
  · exact absurd h h'.2
theorem IsRegular.eq_of_eq_opp (G : D.IsRegular k) {i : ℕ} {V V' : D.Edges i → ComplexMatrix2}
    (hV : D.IsField V) (hV' : D.IsField V') {b : D.Edges i}
    (he : V (D.opp b) = V' (D.opp b)) : V b = V' b := by
  have h1 := hV.2 (D.opp b)
  have h2 := hV'.2 (D.opp b)
  rw [G.opp_opp] at h1 h2
  rw [h1, h2, he]
def meanField (D : TowerSkeleton) {i : ℕ} (V : D.Edges i → ComplexMatrix2) :
    D.Edges (i + 1) → ComplexMatrix2 :=
  open Classical in fun c => if D.IsPos c then D.mean V c else (D.mean V (D.opp c))⁻¹
theorem meanField_isField (G : D.IsRegular k) {i : ℕ} (hi : i < k)
    {V : D.Edges i → ComplexMatrix2} (hV : D.IsField V)
    (hw : ∀ b, ComplexMatrix2.operatorNorm (V b - 1) < D.radius) : D.IsField (D.meanField V) := by
  have hm : ∀ c : D.Edges (i + 1), D.IsPos c → D.mean V c ∈ PeriodicLattice.complexGaugeGroup :=
    fun c hc => G.mean_mem i hi c hc V hV hw
  constructor
  · intro c
    by_cases hc : D.IsPos c
    · simp only [meanField, if_pos hc]
      exact hm c hc
    · simp only [meanField, if_neg hc]
      exact inv_mem_unitDeterminant (hm _ (G.isPos_opp_of_not hi hc))
  · intro c
    by_cases hc : D.IsPos c
    · simp only [meanField, if_pos hc, if_neg (G.not_isPos_opp hi hc), G.opp_opp]
    · have hr := G.isPos_opp_of_not hi hc
      simp only [meanField, if_pos hr, if_neg hc]
      exact (inv_inv_of_mem_unitDeterminant (hm _ hr)).symm
theorem exists_chain_of_small_perturbation (G : D.IsRegular k) (hc : D.EntriesContinuous k)
    {V : ∀ i : ℕ, D.Edges i → ComplexMatrix2} (hV : D.IsMeanChain k V) (F : Finset (D.Edges 0)) :
    ∀ i ≤ k, ∃ (ε : ℝ) (S : Finset (D.Edges i)), 0 < ε ∧
      ∀ W : D.Edges 0 → ComplexMatrix2, D.IsField W →
        (∀ b, D.IsPos b → b ∉ F → W b = V 0 b) →
        (∀ b ∈ F, ComplexMatrix2.operatorNorm (W b - V 0 b) < ε) →
        ∃ V' : ∀ i : ℕ, D.Edges i → ComplexMatrix2, D.IsMeanChain i V' ∧ V' 0 = W ∧
          ∀ c : D.Edges i, D.IsPos c → c ∉ S → V' i c = V i c := by
  classical
  intro i
  induction i with
  | zero =>
    intro _
    refine ⟨1, F, one_pos, fun W hW hout _ => ?_⟩
    refine ⟨Function.update V 0 W, ⟨fun i hi => ?_, fun i hi => absurd hi (by omega),
      fun i hi => absurd hi (by omega)⟩, by simp, fun c hc hcF => ?_⟩
    · obtain rfl : i = 0 := by omega
      simpa using hW
    · simpa using hout c hc hcF
  | succ i ih =>
    intro hik
    have hi : i < k := hik
    obtain ⟨ε₀, S, hε₀, hS⟩ := ih hi.le
    set T : Finset (D.Edges i) := S ∪ S.image D.opp with hT
    have hVi := hV.mono hi.le
    let Q : D.Edges i → ℝ → Prop := fun c ε =>
      ∀ W : D.Edges 0 → ComplexMatrix2, D.IsField W → (∀ b, D.IsPos b → b ∉ F → W b = V 0 b) →
        (∀ b ∈ F, ComplexMatrix2.operatorNorm (W b - V 0 b) < ε) →
        ∀ V' : ∀ i : ℕ, D.Edges i → ComplexMatrix2, D.IsMeanChain i V' → V' 0 = W →
          ComplexMatrix2.operatorNorm (V' i c - 1) < D.radius
    obtain ⟨ε₁, hε₁, hQ⟩ := exists_pos_forall_finset T Q
      (fun c ε ε' hle q W hW hout hin => q W hW hout fun b hb => (hin b hb).trans_le hle)
      (fun c _ => by
        have hδ : 0 < D.radius - ComplexMatrix2.operatorNorm (V i c - 1) :=
          sub_pos.2 (hV.near_one i hi c)
        obtain ⟨F', ε, hε, hF', hnear⟩ := hc i hi.le V hVi c _ hδ
        refine ⟨ε, hε, fun W hW hout hin V' hfam h0 => ?_⟩
        have hd := hnear W hW (fun b hb => ?_) V' hfam h0
        · have := operatorNorm_sub_one_le (V' i c) (V i c)
          linarith
        · by_cases hbF : b ∈ F
          · exact hin b hbF
          · rw [hout b (hF' b hb) hbF, sub_self]
            simpa using hε)
    have hinc := fun b => G.incidence_finite i hi b
    refine ⟨min ε₀ ε₁, T.biUnion fun b => (hinc b).toFinset, lt_min hε₀ hε₁,
      fun W hW hout hin => ?_⟩
    obtain ⟨V'', hfam, h0, hagree⟩ :=
      hS W hW hout fun b hb => (hin b hb).trans_le (min_le_left _ _)
    have hinT : ∀ b ∈ T, ComplexMatrix2.operatorNorm (V'' i b - 1) < D.radius := fun b hb =>
      hQ b hb W hW hout (fun b hb => (hin b hb).trans_le (min_le_right _ _)) V'' hfam h0
    have hconf'' := hfam.isField i le_rfl
    have hconf := hV.isField i hi.le
    have hout' : ∀ b, b ∉ T → V'' i b = V i b := by
      intro b hb
      by_cases hp : D.IsPos b
      · exact hagree b hp fun h => hb (Finset.mem_union_left _ h)
      · have hr := G.isPos_opp_of_not hi.le hp
        refine G.eq_of_eq_opp hconf'' hconf (hagree _ hr fun h => hb ?_)
        refine Finset.mem_union_right _ (Finset.mem_image.2 ⟨_, h, G.opp_opp b⟩)
    have hwithin : ∀ b, ComplexMatrix2.operatorNorm (V'' i b - 1) < D.radius := by
      intro b
      by_cases hb : b ∈ T
      · exact hinT b hb
      · rw [hout' b hb]
        exact hV.near_one i hi b
    have hne : ∀ m, m ≤ i → m ≠ i + 1 := fun m hm => by omega
    refine ⟨Function.update V'' (i + 1) (D.meanField (V'' i)), ⟨fun m hm => ?_, fun m hm b => ?_,
      fun m hm c hc' => ?_⟩, ?_, fun c hc' hcS => ?_⟩
    · by_cases e : m = i + 1
      · subst e
        rw [Function.update_self]
        exact meanField_isField G hi hconf'' hwithin
      · rw [Function.update_of_ne e]
        exact hfam.isField m (by omega)
    · rw [Function.update_of_ne (hne m (by omega))]
      by_cases e : m = i
      · subst e
        exact hwithin b
      · exact hfam.near_one m (by omega) b
    · rw [Function.update_of_ne (hne m (by omega))]
      by_cases e : m = i
      · subst e
        rw [Function.update_self]
        simp only [meanField, if_pos hc']
      · rw [Function.update_of_ne (by omega)]
        exact hfam.eq_mean m (by omega) c hc'
    · rw [Function.update_of_ne (by omega)]
      exact h0
    · rw [Function.update_self]
      simp only [meanField, if_pos hc']
      rw [hV.eq_mean i hi c hc']
      refine G.mean_congr i hi c hc' _ _ hconf'' hconf hwithin (hV.near_one i hi) fun b hb => ?_
      refine hout' b fun hbT => hcS ?_
      exact Finset.mem_biUnion.2 ⟨b, hbT, (hinc b).mem_toFinset.2 ⟨hc', hb⟩⟩
end TowerSkeleton
section Periodic
variable {L n k : ℕ}
def periodicSkeleton (L n k : ℕ) : TowerSkeleton where
  Edges := fun i => Edge L n k i
  opp := fun b => b.opposite
  IsPos := fun b => b.IsPositivelyOriented
  support := fun {i} c => (PeriodicLattice.bondsInDoubleBlock c : Set (Edge L n k i))
  mean := fun V c => PeriodicLattice.complexBlockAverage V c
  radius := polydiscRadius L
theorem isField_of_mem {i : ℕ} {U : Edge L n k i → ComplexMatrix2}
    (h : U ∈ fieldsIn L n k i PeriodicLattice.complexGaugeGroup) :
    (periodicSkeleton L n k).IsField (i := i) U := by apply _root_.YangMills.Construction.Tower.LevelwiseMeans.isField_of_mem <;> assumption
theorem mem_of_isField {i : ℕ} {U : Edge L n k i → ComplexMatrix2}
    (h : (periodicSkeleton L n k).IsField (i := i) U) :
    U ∈ fieldsIn L n k i PeriodicLattice.complexGaugeGroup :=
  ⟨fun b _ => h.1 b, fun b _ => h.2 b⟩
theorem isMeanSequence_of_chain {j : ℕ} {V : ∀ i : ℕ, Edge L n k i → ComplexMatrix2}
    (h : (periodicSkeleton L n k).IsMeanChain j V) : IsMeanSequence j V :=
  ⟨fun i hi => mem_of_isField (h.isField i hi), h.near_one, h.eq_mean⟩
theorem chain_of_isMeanSequence {j : ℕ} {V : ∀ i : ℕ, Edge L n k i → ComplexMatrix2}
    (h : IsMeanSequence j V) : (periodicSkeleton L n k).IsMeanChain j V :=
  ⟨fun i hi => isField_of_mem (h.mem_fields i hi), h.norm_sub_one_lt, h.eq_mean⟩
theorem mem_nearIdentityPolydisc {i : ℕ} {V : Edge L n k i → ComplexMatrix2}
    (h : (periodicSkeleton L n k).IsField (i := i) V)
    (hw : ∀ b, ComplexMatrix2.operatorNorm (V b - 1) < polydiscRadius L)
    (c : Edge L n k (i + 1)) : V ∈ nearIdentityPolydisc (polydiscRadius L) c :=
  ⟨⟨fun b _ => h.1 b, fun b _ => h.2 b⟩, fun b _ => hw b⟩
theorem complexBlockAverage_congr (hR : PeriodicLattice.ComplexAverageIsLocal)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) {i : ℕ} (hi : i < k)
    {c : Edge L n k (i + 1)} (hc : c.IsPositivelyOriented) {V V' : Edge L n k i → ComplexMatrix2}
    (he : ∀ b ∈ (PeriodicLattice.bondsInDoubleBlock c : Set (Edge L n k i)), V b = V' b) :
    PeriodicLattice.complexBlockAverage V c = PeriodicLattice.complexBlockAverage V' c := by
  unfold PeriodicLattice.complexBlockAverage
  simp only [if_pos hc]
  exact (hR L n k i hL.1 hL.2 hn hi c hc).average_eq _ _ he
theorem periodicSkeleton_isRegular (hE : PeriodicLattice.BondEndpointsOrientation.Statement)
    (hS : SmoothingNearIdentity) (hV : ComplexMeanLiesInComplexGaugeGroup)
    (hR : PeriodicLattice.ComplexAverageIsLocal)
    (hE6 : BondSetFields.ProductStructureHolds)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hk : 1 ≤ k) :
    (periodicSkeleton L n k).IsRegular k := by
  refine ⟨fun b => rfl, fun i hi b => ((hE ⟨L, hL, ⟨k, hk⟩, ⟨n, hn⟩⟩ i hi).2.2.2 b).2.2.2.2.2,
    fun i hi c hc V hV' hw => ?_,
    fun i hi c hc V V' _ _ _ _ he => complexBlockAverage_congr hR hL hn hi hc he,
    fun i hi b => ?_⟩
  · have hsub := ((hS.1 L hL).2.2.periodic n k i hn hi c hc).subset_complexDomain
    exact ((hV.2 L k (i + 1) hL (by omega) hi).1 n hn c V hc
      (hsub (mem_nearIdentityPolydisc hV' hw c))).2
  · have hf : (univ : Set (Edge L n k (i + 1))).Finite := ((hE6 L hL k (i + 1) hi).1 n hn).2.1
    exact hf.subset (subset_univ _)
theorem periodicSkeleton_entriesContinuous (hE4 : FamilyProducts.FamilyProductsStatement)
    (hH : PeriodicConditions L n k) : (periodicSkeleton L n k).EntriesContinuous k := by
  intro j hj V hV c δ hδ
  have hform : levelwiseMean (V 0) j c = some (V j c) :=
    hH.sequence_is_levelwise j hj V (isMeanSequence_of_chain hV) j le_rfl c
  have hV0 := mem_of_isField (hV.isField 0 (Nat.zero_le _))
  obtain ⟨F, O, f, w⟩ := hH.exists_representation j hj c (V 0) hV0 (by
    show (levelwiseMean (V 0) j c).isSome
    rw [hform]
    rfl)
  have : Nonempty F := w.nonempty.to_subtype
  obtain ⟨ε, hε, hnear⟩ :=
    exists_near_of_relativelyOpen hE4 tracelessBasis w.isOpen w.mem (w.holomorphic _) hδ
  refine ⟨F, ε, hε, w.positive, fun W hW hin V' hV' h0 => ?_⟩
  have hwp : edgeEntries F W ∈ unimodularPi F := fun b => hW.1 b.1
  obtain ⟨ho, hd⟩ := hnear _ hwp fun b => hin b.1 b.2
  have e1 := w.eq_some W (mem_of_isField hW) ho
  have e2 := w.eq_some (V 0) hV0 w.mem
  have f1 : levelwiseMean (V' 0) j c = some (V' j c) :=
    hH.sequence_is_levelwise j hj V' (isMeanSequence_of_chain hV') j le_rfl c
  rw [h0] at f1
  have a1 : V' j c = f (edgeEntries F W) := Option.some.inj (f1.symm.trans e1)
  have a2 : V j c = f (edgeEntries F (V 0)) := Option.some.inj (hform.symm.trans e2)
  rw [a1, a2]
  exact hd
theorem fieldOfPositiveValues_of_pos {i : ℕ} (w : PositiveEdge L n k i → ComplexMatrix2)
    {b : Edge L n k i} (h : b.IsPositivelyOriented) : fieldOfPositiveValues w b = w ⟨b, h⟩ := by
  simp only [fieldOfPositiveValues, dif_pos h]
theorem fieldOfPositiveValues_of_not_pos {i : ℕ} (w : PositiveEdge L n k i → ComplexMatrix2)
    {b : Edge L n k i} (h : ¬ b.IsPositivelyOriented) (h' : b.opposite.IsPositivelyOriented) :
    fieldOfPositiveValues w b = (w ⟨b.opposite, h'⟩)⁻¹ := by
  simp only [fieldOfPositiveValues, dif_neg h, dif_pos h']
theorem restrict_fieldOfPositiveValues {i : ℕ} (w : PositiveEdge L n k i → ComplexMatrix2) :
    restrictToPositiveEdges (fieldOfPositiveValues w) = w := by apply _root_.YangMills.SharedProofs.p777 <;> assumption
theorem fieldOfPositiveValues_mem (G : (periodicSkeleton L n k).IsRegular k) {i : ℕ} (hi : i ≤ k)
    {w : PositiveEdge L n k i → ComplexMatrix2}
    (hw : w ∈ edgePower L n k i PeriodicLattice.complexGaugeGroup) :
    fieldOfPositiveValues w ∈ fieldsIn L n k i PeriodicLattice.complexGaugeGroup := by
  have hxor : ∀ b : Edge L n k i, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented :=
    G.xor_isPos i hi
  refine ⟨fun b _ => ?_, fun b _ => ?_⟩
  · rcases hxor b with h | h
    · rw [fieldOfPositiveValues_of_pos w h.1]
      exact hw _
    · rw [fieldOfPositiveValues_of_not_pos w h.2 h.1]
      exact inv_mem_unitDeterminant (hw _)
  · rcases hxor b with h | h
    · rw [fieldOfPositiveValues_of_not_pos w h.2
        (show b.opposite.opposite.IsPositivelyOriented from h.1),
        fieldOfPositiveValues_of_pos w h.1]
      rfl
    · rw [fieldOfPositiveValues_of_not_pos w h.2 h.1,
        fieldOfPositiveValues_of_pos w h.1]
      exact (inv_inv_of_mem_unitDeterminant (hw _)).symm
theorem fieldOfPositiveValues_restrict (G : (periodicSkeleton L n k).IsRegular k) {i : ℕ}
    (hi : i ≤ k) {U : Edge L n k i → ComplexMatrix2}
    (hU : U ∈ fieldsIn L n k i PeriodicLattice.complexGaugeGroup) :
    fieldOfPositiveValues (restrictToPositiveEdges U) = U := by
  have hxor : ∀ b : Edge L n k i, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented :=
    G.xor_isPos i hi
  funext b
  rcases hxor b with h | h
  · rw [fieldOfPositiveValues_of_pos _ h.1]
    rfl
  · rw [fieldOfPositiveValues_of_not_pos _ h.2 h.1]
    have e : U b.opposite = (U b)⁻¹ := hU.2 b (mem_univ _)
    show (U b.opposite)⁻¹ = U b
    rw [e]
    exact inv_inv_of_mem_unitDeterminant (hU.1 b (mem_univ _))
theorem isOpenFieldSet_of_perturbations (hE4 : FamilyProducts.FamilyProductsStatement)
    (G : (periodicSkeleton L n k).IsRegular k) {i : ℕ} (hi : i ≤ k) [Finite (PositiveEdge L n k i)]
    [Nonempty (PositiveEdge L n k i)] {𝔇 : Set (Edge L n k i → ComplexMatrix2)}
    (hs : 𝔇 ⊆ fieldsIn L n k i PeriodicLattice.complexGaugeGroup)
    (h : ∀ U ∈ 𝔇, ∃ ε : ℝ, 0 < ε ∧ ∀ W ∈ fieldsIn L n k i PeriodicLattice.complexGaugeGroup,
      (∀ b : Edge L n k i, b.IsPositivelyOriented →
        ComplexMatrix2.operatorNorm (W b - U b) < ε) → W ∈ 𝔇) :
    IsOpenFieldSet PeriodicLattice.complexGaugeGroup 𝔇 := by
  let _ : Fintype (PositiveEdge L n k i) := Fintype.ofFinite _
  have hsub : restrictToPositiveEdges '' 𝔇 ⊆ edgePower L n k i PeriodicLattice.complexGaugeGroup := by
    rintro _ ⟨U, hU, rfl⟩ b
    exact (hs hU).1 _ (mem_univ _)
  refine ⟨hs, ((hE4 (PositiveEdge L n k i)).2.1 _ _ hsub).2 ?_⟩
  rintro _ ⟨U, hU, rfl⟩
  obtain ⟨ε, hε, hm⟩ := h U hU
  refine ⟨ε, hε, fun w hw hb => ⟨fieldOfPositiveValues w, ?_,
    restrict_fieldOfPositiveValues w⟩⟩
  refine hm _ (fieldOfPositiveValues_mem G hi hw) fun b hp => ?_
  rw [fieldOfPositiveValues_of_pos w hp]
  exact hb ⟨b, hp⟩
theorem isHolomorphicOnFields_of_local (H : ExpChartHolomorphy.ExpChartTheory)
    (G : (periodicSkeleton L n k).IsRegular k) {i : ℕ} (hi : i ≤ k) [Finite (PositiveEdge L n k i)]
    (β : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless)
    {𝔇 : Set (Edge L n k i → ComplexMatrix2)}
    (ho : IsOpenFieldSet PeriodicLattice.complexGaugeGroup 𝔇)
    (h : (Edge L n k i → ComplexMatrix2) → ComplexMatrix2)
    (hloc : ∀ U ∈ 𝔇, ∃ (σ : Type) (_ : Fintype σ) (e : σ → PositiveEdge L n k i)
      (O : Set (σ → ComplexMatrix2)) (f : (σ → ComplexMatrix2) → ComplexMatrix2),
        (fun s => U (e s)) ∈ O ∧
        IsHolomorphicToUnimodular β (asGroupFactors '' O) (fun q => f fun s => q (.inl s)) ∧
        ∀ U' ∈ 𝔇, (fun s => U' (e s)) ∈ O → h U' = f fun s => U' (e s)) :
    IsHolomorphicOnFields β 𝔇 h := by
  let _ : Fintype (PositiveEdge L n k i) := Fintype.ofFinite _
  refine ⟨ho, inferInstance, ?_⟩
  have hW : ComplexMatrix2.IsRelativelyOpen (GroupLieProduct (PositiveEdge L n k i) Empty)
      (asGroupFactors '' (restrictToPositiveEdges '' 𝔇)) := by
    rw [asGroupFactors_image]
    exact isRelativelyOpen_leftComponents_preimage ho.2
  refine isHolomorphicToUnimodular_of_local β hW fun p hp => ?_
  obtain ⟨_, ⟨U, hU, rfl⟩, rfl⟩ := hp
  obtain ⟨σ, _, e, O, f, hmem, hf, hval⟩ := hloc U hU
  let Ψ : (PositiveEdge L n k i ⊕ Empty → ComplexMatrix2) → σ ⊕ Empty → ComplexMatrix2 :=
    fun p => asGroupFactors fun s => p (.inl (e s))
  have hΨ : IsHolomorphicToProduct β _ Ψ :=
    ⟨hW, fun s => isHolomorphicToUnimodular_component H β hW (e s), fun e => e.elim⟩
  have hc := isHolomorphicToUnimodular_comp H β hΨ hf
  refine ⟨asGroupFactors '' (restrictToPositiveEdges '' 𝔇) ∩ Ψ ⁻¹' (asGroupFactors '' O),
    ⟨⟨_, ⟨U, hU, rfl⟩, rfl⟩, ⟨_, hmem, rfl⟩⟩, inter_subset_left,
    isHolomorphicToUnimodular_congr β hc ?_⟩
  rintro _ ⟨⟨_, ⟨U', hU', rfl⟩, rfl⟩, w, hw, hwe⟩
  have hw' : w = fun s => U' (e s) := by
    funext s
    exact congrFun hwe (.inl s)
  subst hw'
  have e1 : fieldOfPositiveValues
      (fun b => asGroupFactors (restrictToPositiveEdges U') (.inl b)) = U' :=
    fieldOfPositiveValues_restrict G hi (ho.1 hU')
  show f (fun s => U' (e s)) = h (fieldOfPositiveValues _)
  rw [e1]
  exact (hval U' hU' hw).symm
theorem small_perturbation_periodic (G : (periodicSkeleton L n k).IsRegular k)
    (hc : (periodicSkeleton L n k).EntriesContinuous k) {U : Edge L n k 0 → ComplexMatrix2}
    (hU : U ∈ meanStableFields L n k k) (F : Finset (Edge L n k 0)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ W ∈ fieldsIn L n k 0 PeriodicLattice.complexGaugeGroup,
      (∀ b : Edge L n k 0, b.IsPositivelyOriented → b ∉ F → W b = U b) →
      (∀ b ∈ F, ComplexMatrix2.operatorNorm (W b - U b) < ε) →
        W ∈ meanStableFields L n k k := by
  obtain ⟨V, hV, rfl⟩ := hU
  obtain ⟨ε, S, hε, h⟩ :=
    TowerSkeleton.exists_chain_of_small_perturbation G hc (chain_of_isMeanSequence hV) F k le_rfl
  refine ⟨ε, hε, fun W hW hout hin => ?_⟩
  obtain ⟨V', hV', h0, _⟩ := h W (isField_of_mem hW) hout hin
  exact ⟨V', isMeanSequence_of_chain hV', h0⟩
theorem isOpenFieldSet_fieldsNearOne (G : (periodicSkeleton L n k).IsRegular k) {i : ℕ}
    (hi : i ≤ k) [Finite (PositiveEdge L n k i)] :
    IsOpenFieldSet PeriodicLattice.complexGaugeGroup (fieldsNearOne L n k i) := by
  have hcont : Continuous fun X : ComplexMatrix2 => ‖X.adjugate - 1‖ := by
    refine continuous_norm.comp (Continuous.sub ?_ continuous_const)
    exact Continuous.matrix_adjugate continuous_id
  have hcont' : Continuous fun X : ComplexMatrix2 => ‖X - 1‖ :=
    continuous_norm.comp (continuous_id.sub continuous_const)
  have inv_adj : ∀ {X : ComplexMatrix2}, X ∈ ComplexMatrix2.unitDeterminant →
      X⁻¹ = X.adjugate := by
    intro X h
    have e : X.det = 1 := h
    rw [Matrix.inv_def, e]
    simp
  refine ⟨fun V hV => hV.1, ⋂ b : PositiveEdge L n k i,
    {w | ‖w b - 1‖ < polydiscRadius L ∧
      ‖(w b).adjugate - 1‖ < polydiscRadius L}, ?_, ?_⟩
  · refine isOpen_iInter_of_finite fun b => IsOpen.inter ?_ ?_
    · exact isOpen_lt (hcont'.comp (continuous_apply b)) continuous_const
    · exact isOpen_lt (hcont.comp (continuous_apply b)) continuous_const
  · ext w
    constructor
    · rintro ⟨V, hV, rfl⟩
      refine ⟨mem_iInter.2 fun b => ⟨hV.2 b, ?_⟩, fun b => hV.1.1 _ (mem_univ _)⟩
      have e : V (b : Edge L n k i).opposite = (V b)⁻¹ := hV.1.2 _ (mem_univ _)
      show ‖(V b).adjugate - 1‖ < _
      rw [← inv_adj (hV.1.1 _ (mem_univ _)), ← e]
      exact hV.2 _
    · rintro ⟨hO, hw⟩
      refine ⟨fieldOfPositiveValues w, ⟨fieldOfPositiveValues_mem G hi hw, fun b => ?_⟩,
        restrict_fieldOfPositiveValues w⟩
      have hb := fun b => mem_iInter.1 hO b
      have hxor : ∀ b : Edge L n k i,
          Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented := G.xor_isPos i hi
      rcases hxor b with h | h
      · rw [fieldOfPositiveValues_of_pos w h.1]
        exact (hb ⟨b, h.1⟩).1
      · rw [fieldOfPositiveValues_of_not_pos w h.2 h.1, inv_adj (hw _)]
        exact (hb ⟨_, h.1⟩).2
theorem eq_fieldOfValues_of_mem (G : (periodicSkeleton L n k).IsRegular k)
    (hP : DoubleBlockPolydisc.PolydiscsHold) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hn : 0 < n) {i : ℕ} (hi : i < k) {c : Edge L n k (i + 1)} (hc : c.IsPositivelyOriented)
    {V : Edge L n k i → ComplexMatrix2} (hVp : V ∈ nearIdentityPolydisc (polydiscRadius L) c)
    {b : Edge L n k i} (hb : b ∈ (PeriodicLattice.bondsInDoubleBlock c : Set (Edge L n k i))) :
    V b = DoubleBlockPolydisc.fieldOfValues c (fun b => V b.1) b := by
  have hxor : ∀ b : Edge L n k i, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented :=
    G.xor_isPos i hi.le
  have hpoly := ((hP L hL k i hi).1 n hn c hc).finite_open
  unfold DoubleBlockPolydisc.fieldOfValues PeriodicLattice.extendFromPositive
  by_cases hp : b.IsPositivelyOriented
  · rw [dif_pos (⟨hb, hp⟩ : b ∈ DoubleBlockPolydisc.doubleBlockBonds c ∧ b.IsPositivelyOriented)]
  · have hrp : b.opposite.IsPositivelyOriented := by
      rcases hxor b with h | h
      · exact absurd h.1 hp
      · exact h.1
    have hrb : b.opposite ∈ DoubleBlockPolydisc.doubleBlockBonds c :=
      hpoly.opposite_mem b hb
    rw [dif_neg (fun h : b ∈ DoubleBlockPolydisc.doubleBlockBonds c ∧ b.IsPositivelyOriented =>
        hp h.2),
      dif_pos (⟨hrb, hrp⟩ : b.opposite ∈ DoubleBlockPolydisc.doubleBlockBonds c ∧
        b.opposite.IsPositivelyOriented)]
    have e : (V b.opposite)⁻¹ = ((V b)⁻¹)⁻¹ := congrArg (·⁻¹) (hVp.1.2 b hb)
    exact (e.trans (inv_inv_of_mem_unitDeterminant (hVp.1.1 b hb))).symm
theorem meanStable_periodic (H : ExpChartHolomorphy.ExpChartTheory)
    (hE : PeriodicLattice.BondEndpointsOrientation.Statement)
    (hP : DoubleBlockPolydisc.PolydiscsHold)
    (hS : SmoothingNearIdentity)
    (hV : ComplexMeanLiesInComplexGaugeGroup)
    (hR : PeriodicLattice.ComplexAverageIsLocal)
    (hE6 : BondSetFields.ProductStructureHolds)
    (hE4 : FamilyProducts.FamilyProductsStatement)
    (hH : PeriodicConditions L n k)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hk : 1 ≤ k) :
    MeanStableConditions L n k := by
  have G := periodicSkeleton_isRegular hE hS hV hR hE6 hL hn hk
  have hc := periodicSkeleton_entriesContinuous hE4 hH
  have hbonds : ∀ i ≤ k, Finite (Edge L n k i) := fun i hi =>
    Set.finite_univ_iff.1 ((hE6 L hL k i hi).1 n hn).2.1
  have hfin : ∀ i ≤ k, Finite (PositiveEdge L n k i) := fun i hi => by
    have := hbonds i hi
    exact Subtype.finite
  have hnon : Nonempty (PositiveEdge L n k 0) := by
    obtain ⟨b, _⟩ := ((hE6 L hL k 0 (Nat.zero_le _)).1 n hn).2.2.1
    have hxor : Xor (b : Edge L n k 0).IsPositivelyOriented b.opposite.IsPositivelyOriented :=
      G.xor_isPos 0 (Nat.zero_le _) b
    rcases hxor with h | h
    · exact ⟨⟨b, h.1⟩⟩
    · exact ⟨⟨_, h.1⟩⟩
  have hsub : meanStableFields L n k k ⊆ fieldsIn L n k 0 PeriodicLattice.complexGaugeGroup := by
    rintro _ ⟨V, hV', rfl⟩
    exact hV'.mem_fields 0 (Nat.zero_le _)
  have hopen : IsOpenFieldSet PeriodicLattice.complexGaugeGroup (meanStableFields L n k k) := by
    have := hfin 0 (Nat.zero_le _)
    have := hbonds 0 (Nat.zero_le _)
    refine isOpenFieldSet_of_perturbations hE4 G (Nat.zero_le _) hsub fun U hU => ?_
    obtain ⟨F, hF⟩ : ∃ F : Finset (Edge L n k 0), ∀ b, b ∈ F ↔ b.IsPositivelyOriented :=
      ⟨(Set.toFinite {b : Edge L n k 0 | b.IsPositivelyOriented}).toFinset,
        fun b => Set.Finite.mem_toFinset _⟩
    obtain ⟨ε, hε, h⟩ := small_perturbation_periodic G hc hU F
    exact ⟨ε, hε, fun W hW hb => h W hW (fun b hp hnF => absurd ((hF b).2 hp) hnF)
      fun b hbF => hb b ((hF b).1 hbF)⟩
  have hwithin : ∀ i < k,
      IsOpenFieldSet PeriodicLattice.complexGaugeGroup (fieldsNearOne L n k i) := fun i hi => by
    have := hfin i hi.le
    exact isOpenFieldSet_fieldsNearOne G hi.le
  refine ⟨?_, ?_, fun U hU F _ => small_perturbation_periodic G hc hU F, hopen, ?_, ?_,
    hwithin, ?_⟩
  · intro l hl W V V' h h' i hi
    funext c
    have a := hH.sequence_is_levelwise l hl V h.1 i hi c
    have a' := hH.sequence_is_levelwise l hl V' h'.1 i hi c
    rw [h.2] at a
    rw [h'.2] at a'
    exact Option.some.inj (a.symm.trans a')
  · intro l hl W V h i hi c
    have a := hH.sequence_is_levelwise l hl V h.1 i hi c
    rwa [h.2] at a
  · intro j hj c _ β
    have := hfin 0 (Nat.zero_le _)
    refine isHolomorphicOnFields_of_local H G (Nat.zero_le _) β hopen _ fun U hU => ?_
    obtain ⟨V, hV', rfl⟩ := id hU
    have hform : levelwiseMean (V 0) j c = some (V j c) :=
      hH.sequence_is_levelwise k le_rfl V hV' j hj c
    have hU0 := hsub hU
    obtain ⟨F, O, f, w⟩ := hH.exists_representation j hj c _ hU0 (by
      show (levelwiseMean _ j c).isSome
      rw [hform]
      rfl)
    refine ⟨F, inferInstance, fun s => ⟨s.1, w.positive s.1 s.2⟩, O, f, w.mem, w.holomorphic β,
      fun U' hU' hO => ?_⟩
    have e := w.eq_some U' (hsub hU') hO
    show (levelwiseMean U' j c).getD 1 = _
    rw [e]
    rfl
  · intro i hi c _ V hV'
    exact mem_nearIdentityPolydisc (isField_of_mem hV'.1) hV'.2 c
  · intro i hi c hcp β
    have := hfin i hi.le
    refine isHolomorphicOnFields_of_local H G hi.le β (hwithin i hi) _ fun U hU => ?_
    obtain ⟨inst, hh⟩ := ((hP L hL k i hi).1 n hn c hcp).holomorphic_smoothing
    have hmem : ∀ U' ∈ fieldsNearOne L n k i,
        U' ∈ nearIdentityPolydisc (polydiscRadius L) c := fun U' hU' =>
      mem_nearIdentityPolydisc (isField_of_mem hU'.1) hU'.2 c
    refine ⟨DoubleBlockPolydisc.positiveDoubleBlockBonds c, inst, fun s => ⟨s.1, s.2.2⟩,
      DoubleBlockPolydisc.polydiscPositive (polydiscRadius L) c,
      fun v => PeriodicLattice.complexBlockAverage (DoubleBlockPolydisc.fieldOfValues c v) c,
      ⟨_, ⟨U, hmem U hU, rfl⟩, rfl⟩, ?_, fun U' hU' _ => ?_⟩
    · rw [asGroupFactors_image]
      exact hh.toUnimodular β
    · exact complexBlockAverage_congr hR hL hn hi hcp fun b hb =>
        eq_fieldOfValues_of_mem G hP hL hn hi hcp (hmem U' hU') hb
end Periodic
namespace Infinite
variable {L k : ℕ}
def fullSpaceSkeleton (L k : ℕ) : TowerSkeleton where
  Edges := fun i => FullSpace.Edge L k i
  opp := fun b => b.opposite
  IsPos := fun b => b.IsPositivelyOriented
  support := fun {i} c => FullSpace.doubleCubeLinks L (meshAt L k i) c
  mean := fun {_} V c => FullSpace.complexSmoothing L V c
  radius := polydiscRadius L
theorem isField_of_mem {i : ℕ} {U : FullSpace.Edge L k i → ComplexMatrix2}
    (h : U ∈ FullSpace.fieldsValuedIn L k i PeriodicLattice.complexGaugeGroup) :
    (fullSpaceSkeleton L k).IsField (i := i) U := h
theorem mem_of_isField {i : ℕ} {U : FullSpace.Edge L k i → ComplexMatrix2}
    (h : (fullSpaceSkeleton L k).IsField (i := i) U) :
    U ∈ FullSpace.fieldsValuedIn L k i PeriodicLattice.complexGaugeGroup := h
theorem isMeanSequence_of_chain {j : ℕ} {V : ∀ i : ℕ, FullSpace.Edge L k i → ComplexMatrix2}
    (h : (fullSpaceSkeleton L k).IsMeanChain j V) :
    LevelwiseMeans.Unbounded.IsMeanSequence j V :=
  ⟨fun i hi => mem_of_isField (h.isField i hi), h.near_one, h.eq_mean⟩
theorem chain_of_isMeanSequence {j : ℕ} {V : ∀ i : ℕ, FullSpace.Edge L k i → ComplexMatrix2}
    (h : LevelwiseMeans.Unbounded.IsMeanSequence j V) :
    (fullSpaceSkeleton L k).IsMeanChain j V :=
  ⟨fun i hi => isField_of_mem (h.mem_fields i hi), h.norm_sub_one_lt, h.eq_mean⟩
theorem mem_nearIdentityPolydisc {i : ℕ} {V : FullSpace.Edge L k i → ComplexMatrix2}
    (h : (fullSpaceSkeleton L k).IsField (i := i) V)
    (hw : ∀ b, ComplexMatrix2.operatorNorm (V b - 1) < polydiscRadius L)
    (c : FullSpace.Edge L k (i + 1)) :
    V ∈ FullSpace.nearIdentityPolydisc L k i (polydiscRadius L) c :=
  ⟨⟨fun b _ => h.1 b, fun b _ => h.2 b⟩, fun b _ => hw b⟩
theorem xor_isPositivelyOriented_opposite {a : ℝ} (ha : 0 < a) (b : InfiniteLattice.Link a) :
    Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.Tower.LevelwiseMeans.Unbounded.xor_isPositivelyOriented_opposite <;> assumption
theorem meshAt_pos (hL : Conventions.IsAdmissibleBlockingFactor L) (i : ℕ) : 0 < meshAt L k i := by apply _root_.YangMills.Construction.Tower.LevelwiseMeans.Unbounded.meshAt_pos <;> assumption
theorem finite_links_with_endpoint {a : ℝ} (y : InfiniteLattice.LatticePoint a) :
    {c : InfiniteLattice.Link a | c.initial = y ∨ c.terminal = y}.Finite := by
  let g : InfiniteLattice.Link a → InfiniteLattice.LatticePoint a × InfiniteLattice.LatticePoint a :=
    fun c => (c.initial, c.terminal)
  have hinj : Function.Injective g := by
    rintro ⟨t, h, _⟩ ⟨t', h', _⟩ e
    simp only [g, Prod.mk.injEq] at e
    obtain ⟨rfl, rfl⟩ := e
    rfl
  let d : Fin 4 × Bool → InfiniteLattice.LatticePoint a :=
    fun p => if p.2 then InfiniteLattice.axisStep a p.1 else -InfiniteLattice.axisStep a p.1
  let r : (Fin 4 × Bool) × Bool →
      InfiniteLattice.LatticePoint a × InfiniteLattice.LatticePoint a :=
    fun p => if p.2 then (y, y + d p.1) else (y - d p.1, y)
  refine Set.Finite.of_finite_image ((Set.finite_range r).subset ?_) hinj.injOn
  rintro _ ⟨c, hc, rfl⟩
  have hd : ∃ p, c.terminal - c.initial = d p := by
    obtain ⟨μ, h | h⟩ := c.isAdjacent
    · exact ⟨(μ, true), by simpa [d] using h⟩
    · exact ⟨(μ, false), by simpa [d] using h⟩
  obtain ⟨p, hp⟩ := hd
  rcases hc with hc | hc
  · refine ⟨(p, true), ?_⟩
    have e : y + d p = c.terminal := by
      rw [← hp, ← hc]
      abel
    simp only [r, g, if_true, e, hc]
  · refine ⟨(p, false), ?_⟩
    have e : y - d p = c.initial := by
      rw [← hp, ← hc]
      abel
    simp only [r, g, Bool.false_eq_true, if_false, e, hc]
theorem finite_incident_links (hP : DoubleBlockPolydisc.PolydiscsHold) (hZ : BlockStructure)
    (hL : Conventions.IsAdmissibleBlockingFactor L) {i : ℕ} (hi : i < k)
    (b : FullSpace.Edge L k i) :
    {c : FullSpace.Edge L k (i + 1) | c.IsPositivelyOriented ∧
      b ∈ FullSpace.doubleCubeLinks L (meshAt L k i) c}.Finite := by
  obtain ⟨y, _, huniq⟩ :=
    (hZ L k (i + 1) hL (by omega) (by omega) (by omega)).2.2.1.2.1 b.initial
  refine (finite_links_with_endpoint y).subset ?_
  rintro c ⟨hcp, hb⟩
  have hb' : b ∈ DoubleBlockPolydisc.Infinite.doubleBlockBonds L k i c := hb
  rw [((hP L hL k i hi).2 c hcp).doubleBlockBonds_eq] at hb'
  rcases hb'.1 with h | h
  · exact Or.inl (huniq _ h)
  · exact Or.inr (huniq _ h)
theorem complexSmoothing_congr (hS : SmoothingNearIdentity)
    (hQ : SublatticesSymmetriesScalingsAndProjections.Statement)
    (hL : Conventions.IsAdmissibleBlockingFactor L) {i : ℕ} (hi : i < k)
    {c : FullSpace.Edge L k (i + 1)} (hc : c.IsPositivelyOriented)
    {V V' : FullSpace.Edge L k i → ComplexMatrix2}
    (hV : V ∈ FullSpace.nearIdentityPolydisc L k i (polydiscRadius L) c)
    (hV' : V' ∈ FullSpace.nearIdentityPolydisc L k i (polydiscRadius L) c)
    (he : ∀ b ∈ FullSpace.doubleCubeLinks L (meshAt L k i) c, V b = V' b) :
    FullSpace.complexSmoothing L V c = FullSpace.complexSmoothing L V' c := by
  have hL0 : 0 < L := by
    have := hL.2
    omega
  have hserve := (hS.1 L hL).2.2.fullSpace k i hi c hc
  have hQ' := ((hQ L hL0 hL k).2.2.2.2.2.2 (by omega) 1 one_pos).2 i hi c hc
  have e1 := hQ'.complexSmoothing_eq V (hserve.subset_complexDomain hV)
  have e2 := hQ'.complexSmoothing_eq V' (hserve.subset_complexDomain hV')
  refine e1.trans (Eq.trans ?_ e2.symm)
  congr 1
  funext x
  unfold FullSpace.projField
  split_ifs with h
  · exact he _ h.choose_spec.1
  · rfl
theorem fullSpaceSkeleton_isRegular (hP : DoubleBlockPolydisc.PolydiscsHold)
    (hS : SmoothingNearIdentity) (hV : ComplexMeanLiesInComplexGaugeGroup)
    (hQ : SublatticesSymmetriesScalingsAndProjections.Statement)
    (hZ : BlockStructure) (hL : Conventions.IsAdmissibleBlockingFactor L) :
    (fullSpaceSkeleton L k).IsRegular k := by
  refine ⟨fun b => rfl, fun i _ b => xor_isPositivelyOriented_opposite (meshAt_pos hL i) b,
    fun i hi c hc V hV' hw => ?_, fun i hi c hc V V' h1 h2 h3 h4 he => ?_,
    fun i hi b => finite_incident_links hP hZ hL hi b⟩
  · have hserve := (hS.1 L hL).2.2.fullSpace k i hi c hc
    exact ((hV.2 L k (i + 1) hL (by omega) hi).2 c V hc
      (hserve.subset_complexDomain (mem_nearIdentityPolydisc hV' hw c))).2
  · exact complexSmoothing_congr hS hQ hL hi hc (mem_nearIdentityPolydisc h1 h3 c)
      (mem_nearIdentityPolydisc h2 h4 c) he
theorem fullSpaceSkeleton_entriesContinuous (hE4 : FamilyProducts.FamilyProductsStatement)
    (hH : LevelwiseMeans.Unbounded.UnboundedConditions L k) :
    (fullSpaceSkeleton L k).EntriesContinuous k := by
  intro j hj V hV c δ hδ
  have hform : LevelwiseMeans.Unbounded.levelwiseMean (V 0) j c = some (V j c) :=
    hH.sequence_is_levelwise j hj V (isMeanSequence_of_chain hV) j le_rfl c
  have hV0 := mem_of_isField (hV.isField 0 (Nat.zero_le _))
  obtain ⟨F, O, f, w⟩ := hH.exists_representation j hj c (V 0) hV0 (by
    show (LevelwiseMeans.Unbounded.levelwiseMean (V 0) j c).isSome
    rw [hform]
    rfl)
  have : Nonempty F := w.finite_edges.1.to_subtype
  obtain ⟨ε, hε, hnear⟩ :=
    exists_near_of_relativelyOpen hE4 tracelessBasis w.isOpen w.mem (w.holomorphic _) hδ
  refine ⟨F, ε, hε, w.finite_edges.2, fun W hW hin V' hV' h0 => ?_⟩
  have hwp : FullSpace.restrictToEdges F W ∈ unimodularPi F := fun b => hW.1 b.1
  obtain ⟨ho, hd⟩ := hnear _ hwp fun b => hin b.1 b.2
  have e1 := w.eq_some W (mem_of_isField hW) ho
  have e2 := w.eq_some (V 0) hV0 w.mem
  have f1 : LevelwiseMeans.Unbounded.levelwiseMean (V' 0) j c = some (V' j c) :=
    hH.sequence_is_levelwise j hj V' (isMeanSequence_of_chain hV') j le_rfl c
  rw [h0] at f1
  have a1 : V' j c = f (FullSpace.restrictToEdges F W) := Option.some.inj (f1.symm.trans e1)
  have a2 : V j c = f (FullSpace.restrictToEdges F (V 0)) :=
    Option.some.inj (hform.symm.trans e2)
  rw [a1, a2]
  exact hd
theorem small_perturbation_fullSpace (G : (fullSpaceSkeleton L k).IsRegular k)
    (hc : (fullSpaceSkeleton L k).EntriesContinuous k)
    {U : FullSpace.Edge L k 0 → ComplexMatrix2}
    (hU : U ∈ meanStableFields L k k) (F : Finset (FullSpace.Edge L k 0)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ W ∈ FullSpace.fieldsValuedIn L k 0 PeriodicLattice.complexGaugeGroup,
      (∀ b : FullSpace.Edge L k 0, b.IsPositivelyOriented → b ∉ F → W b = U b) →
      (∀ b ∈ F, ComplexMatrix2.operatorNorm (W b - U b) < ε) → W ∈ meanStableFields L k k := by
  obtain ⟨V, hV, rfl⟩ := hU
  obtain ⟨ε, S, hε, h⟩ :=
    TowerSkeleton.exists_chain_of_small_perturbation G hc (chain_of_isMeanSequence hV) F k le_rfl
  refine ⟨ε, hε, fun W hW hout hin => ?_⟩
  obtain ⟨V', hV', h0, _⟩ := h W (isField_of_mem hW) hout hin
  exact ⟨V', isMeanSequence_of_chain hV', h0⟩
theorem eq_fieldOfValues_of_mem (G : (fullSpaceSkeleton L k).IsRegular k)
    (hP : DoubleBlockPolydisc.PolydiscsHold) (hL : Conventions.IsAdmissibleBlockingFactor L)
    {i : ℕ} (hi : i < k) {c : FullSpace.Edge L k (i + 1)} (hc : c.IsPositivelyOriented)
    {V : FullSpace.Edge L k i → ComplexMatrix2}
    (hVp : V ∈ FullSpace.nearIdentityPolydisc L k i (polydiscRadius L) c)
    {b : FullSpace.Edge L k i} (hb : b ∈ FullSpace.doubleCubeLinks L (meshAt L k i) c) :
    V b = DoubleBlockPolydisc.Infinite.fieldOfValues L k i c (fun b => V b.1) b := by
  have hxor : ∀ b : FullSpace.Edge L k i,
      Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented := G.xor_isPos i hi.le
  have hpoly := ((hP L hL k i hi).2 c hc).finite_open
  unfold DoubleBlockPolydisc.Infinite.fieldOfValues FullSpace.extendFromPositive
  by_cases hp : b.IsPositivelyOriented
  · rw [dif_pos (⟨hb, hp⟩ : b ∈ DoubleBlockPolydisc.Infinite.doubleBlockBonds L k i c ∧
      b.IsPositivelyOriented)]
  · have hrp : b.opposite.IsPositivelyOriented := by
      rcases hxor b with h | h
      · exact absurd h.1 hp
      · exact h.1
    have hrb : b.opposite ∈ DoubleBlockPolydisc.Infinite.doubleBlockBonds L k i c :=
      hpoly.opposite_mem b hb
    rw [dif_neg (fun h : b ∈ DoubleBlockPolydisc.Infinite.doubleBlockBonds L k i c ∧
        b.IsPositivelyOriented => hp h.2),
      dif_pos (⟨hrb, hrp⟩ : b.opposite ∈ DoubleBlockPolydisc.Infinite.doubleBlockBonds L k i c ∧
        b.opposite.IsPositivelyOriented)]
    have e : (V b.opposite)⁻¹ = ((V b)⁻¹)⁻¹ := congrArg (·⁻¹) (hVp.1.2 b hb)
    exact (e.trans (inv_inv_of_mem_unitDeterminant (hVp.1.1 b hb))).symm
theorem isRelativelyOpen_polydiscOnFinset {i : ℕ} {c : FullSpace.Edge L k (i + 1)}
    (F : Finset (FullSpace.Edge L k i))
    (hF : (F : Set (FullSpace.Edge L k i)) =
      DoubleBlockPolydisc.Infinite.positiveDoubleBlockBonds L k i c)
    (ho : ComplexMatrix2.IsRelativelyOpen
      (unimodularPi (DoubleBlockPolydisc.Infinite.positiveDoubleBlockBonds L k i c))
      (DoubleBlockPolydisc.Infinite.polydiscPositive L k i (polydiscRadius L) c)) :
    ComplexMatrix2.IsRelativelyOpen (unimodularPi F) (polydiscOnFinset c F hF) := by
  obtain ⟨O₁, hO₁, e⟩ := ho
  have hcont : Continuous (pointOfFinset c F hF) := continuous_pi fun _ => continuous_apply _
  refine ⟨pointOfFinset c F hF ⁻¹' O₁, hO₁.preimage hcont, ?_⟩
  ext w
  have hg : pointOfFinset c F hF w ∈
      unimodularPi (DoubleBlockPolydisc.Infinite.positiveDoubleBlockBonds L k i c) ↔
      w ∈ unimodularPi F := by
    constructor
    · intro h b
      have hb : b.1 ∈ DoubleBlockPolydisc.Infinite.positiveDoubleBlockBonds L k i c := by
        rw [← hF]
        exact b.2
      exact h ⟨b.1, hb⟩
    · intro h b
      exact h _
  show pointOfFinset c F hF w ∈
    DoubleBlockPolydisc.Infinite.polydiscPositive L k i (polydiscRadius L) c ↔ _
  rw [e]
  exact and_congr_right fun _ => hg
theorem meanStable_fullSpace (H : ExpChartHolomorphy.ExpChartTheory)
    (hP : DoubleBlockPolydisc.PolydiscsHold)
    (hS : SmoothingNearIdentity)
    (hV : ComplexMeanLiesInComplexGaugeGroup)
    (hQ : SublatticesSymmetriesScalingsAndProjections.Statement)
    (hZ : BlockStructure)
    (hE4 : FamilyProducts.FamilyProductsStatement)
    (hL2 : FullSpace.UniqueValue.PresentationsAgreeAndBallsOpen)
    (hH : LevelwiseMeans.Unbounded.UnboundedConditions L k)
    (hL : Conventions.IsAdmissibleBlockingFactor L) : MeanStableConditions L k := by
  have G : (fullSpaceSkeleton L k).IsRegular k := fullSpaceSkeleton_isRegular hP hS hV hQ hZ hL
  have hc := fullSpaceSkeleton_entriesContinuous hE4 hH
  have hsub : meanStableFields L k k ⊆
      FullSpace.fieldsValuedIn L k 0 PeriodicLattice.complexGaugeGroup := by
    rintro _ ⟨V, hV', rfl⟩
    exact hV'.mem_fields 0 (Nat.zero_le _)
  have hopen : FullSpace.IsFinitelyOpen PeriodicLattice.complexGaugeGroup
      (meanStableFields L k k) :=
    ⟨hsub, fun U hU F _ => small_perturbation_fullSpace G hc hU F⟩
  have hwsub : ∀ i, fieldsNearOne L k i ⊆
      FullSpace.fieldsValuedIn L k i PeriodicLattice.complexGaugeGroup := fun i V hV' => hV'.1
  have hmem : ∀ {i : ℕ} (c : FullSpace.Edge L k (i + 1)), ∀ U' ∈ fieldsNearOne L k i,
      U' ∈ FullSpace.nearIdentityPolydisc L k i (polydiscRadius L) c :=
    fun c U' hU' => mem_nearIdentityPolydisc (isField_of_mem hU'.1) hU'.2 c
  have hwriting : ∀ j ≤ k, ∀ c : FullSpace.Edge L k j,
      ∀ U ∈ meanStableFields L k k,
        ∀ (F : Finset (FullSpace.Edge L k 0)) (O : Set (F → ComplexMatrix2))
          (f : (F → ComplexMatrix2) → ComplexMatrix2),
          LevelwiseMeans.Unbounded.IsHolomorphicRepresentation j c U F O f →
          FullSpace.IsLocalPresentation PeriodicLattice.complexGaugeGroup
            (meanStableFields L k k) (levelwiseMeanAt j c) U F O f := by
    intro j hj c U hU F O f w
    refine ⟨w.finite_edges, w.isOpen, w.mem, fun U' hU' hO => ?_⟩
    have e := w.eq_some U' (hsub hU') hO
    show (LevelwiseMeans.Unbounded.levelwiseMean U' j c).getD 1 = _
    rw [e]
    rfl
  have hinto : ∀ {F : Finset (FullSpace.Edge L k 0)} {O : Set (F → ComplexMatrix2)}
      {f : (F → ComplexMatrix2) → ComplexMatrix2}
      (β : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless),
      IsHolomorphicToUnimodular β (asGroupFactors '' O) (fun p => f fun b => p (.inl b)) →
      IsHolomorphicToCoords β Coordinates.ComplexCoordinates.matrixEquiv (asGroupFactors '' O)
        fun p => f fun b => p (.inl b) := fun {F} {O} {f} β hΦ =>
    ((H.2.2.2.1 F Empty).2.1 β _ _ hΦ.1 hΦ.2.1).1 hΦ
  have htriple : ∀ j ≤ k, ∀ c : FullSpace.Edge L k j, ∀ U ∈ meanStableFields L k k,
      ∃ (F : Finset (FullSpace.Edge L k 0)) (O : Set (F → ComplexMatrix2))
        (f : (F → ComplexMatrix2) → ComplexMatrix2),
        LevelwiseMeans.Unbounded.IsHolomorphicRepresentation j c U F O f := by
    intro j hj c U hU
    obtain ⟨V, hV', rfl⟩ := id hU
    have hform : LevelwiseMeans.Unbounded.levelwiseMean (V 0) j c = some (V j c) :=
      hH.sequence_is_levelwise k le_rfl V hV' j hj c
    have hU0 := hsub hU
    exact hH.exists_representation j hj c _ hU0 (by
      show (LevelwiseMeans.Unbounded.levelwiseMean _ j c).isSome
      rw [hform]
      rfl)
  have hpolyw : ∀ i < k, ∀ c : FullSpace.Edge L k (i + 1), c.IsPositivelyOriented →
      ∀ (F : Finset (FullSpace.Edge L k i))
        (hF : (F : Set (FullSpace.Edge L k i)) =
          DoubleBlockPolydisc.Infinite.positiveDoubleBlockBonds L k i c),
        ∀ U ∈ fieldsNearOne L k i,
          FullSpace.IsLocalPresentation PeriodicLattice.complexGaugeGroup (fieldsNearOne L k i)
            (fun V => FullSpace.complexSmoothing L V c) U F (polydiscOnFinset c F hF)
            (smoothingOnFinset c F hF) := by
    intro i hi c hcp F hF U hU
    have hpoly := ((hP L hL k i hi).2 c hcp).finite_open
    refine ⟨⟨?_, ?_⟩, isRelativelyOpen_polydiscOnFinset F hF hpoly.isRelativelyOpen, ?_,
      fun U' hU' _ => ?_⟩
    · obtain ⟨b, hb⟩ := hpoly.positive_nonempty
      have hb' : b ∈ (F : Set (FullSpace.Edge L k i)) := by
        rw [hF]
        exact hb
      exact ⟨b, hb'⟩
    · intro b hb
      have hb' : b ∈ (F : Set (FullSpace.Edge L k i)) := hb
      rw [hF] at hb'
      exact hb'.2
    · exact ⟨_, ⟨U, hmem c U hU, rfl⟩, rfl⟩
    · have hag : ∀ b ∈ FullSpace.doubleCubeLinks L (meshAt L k i) c, U' b =
          DoubleBlockPolydisc.Infinite.fieldOfValues L k i c (fun b => U' b.1) b :=
        fun b hb => eq_fieldOfValues_of_mem G hP hL hi hcp (hmem c U' hU') hb
      show FullSpace.complexSmoothing L U' c = FullSpace.complexSmoothing L
        (DoubleBlockPolydisc.Infinite.fieldOfValues L k i c (fun b => U' b.1)) c
      refine complexSmoothing_congr hS hQ hL hi hcp (hmem c U' hU') ?_ hag
      refine ⟨⟨fun b hb => ?_, fun b hb => ?_⟩, fun b hb => ?_⟩
      · rw [← hag b hb]
        exact (hmem c U' hU').1.1 b hb
      · rw [← hag b hb, ← hag _ (hpoly.opposite_mem b hb)]
        exact (hmem c U' hU').1.2 b hb
      · rw [← hag b hb]
        exact (hmem c U' hU').2 b hb
  have hρ : 0 < polydiscRadius L := (hS.1 L hL).2.2.pos
  refine ⟨?_, ?_, fun U hU F _ => small_perturbation_fullSpace G hc hU F, hopen, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_⟩
  · intro l hl W V V' h h' i hi
    funext c
    have a := hH.sequence_is_levelwise l hl V h.1 i hi c
    have a' := hH.sequence_is_levelwise l hl V' h'.1 i hi c
    rw [h.2] at a
    rw [h'.2] at a'
    exact Option.some.inj (a.symm.trans a')
  · intro l hl W V h i hi c
    have a := hH.sequence_is_levelwise l hl V h.1 i hi c
    rwa [h.2] at a
  · intro j hj c _ β
    refine ⟨hsub, fun U hU => ?_⟩
    obtain ⟨F, O, f, w⟩ := htriple j hj c U hU
    exact ⟨F, O, f, hwriting j hj c U hU F O f w, hinto β (w.holomorphic β)⟩
  · exact fun j hj c _ U hU => htriple j hj c U hU
  · exact fun j hj c _ U hU F O f w => ⟨hwriting j hj c U hU F O f w,
      fun β => hinto β (w.holomorphic β)⟩
  · exact fun i _ c _ V hV' => hmem c V hV'
  · intro i hi
    exact ((hL2 L k i hL.1 hL.2 hi.le).2.2 _ hρ).2.2
  · intro i hi c hcp β
    refine ⟨hwsub i, fun U hU => ?_⟩
    have hpoly := ((hP L hL k i hi).2 c hcp).finite_open
    have hcoe : ((hpoly.positive_finite.toFinset : Finset (FullSpace.Edge L k i)) :
        Set (FullSpace.Edge L k i)) =
          DoubleBlockPolydisc.Infinite.positiveDoubleBlockBonds L k i c :=
      hpoly.positive_finite.coe_toFinset
    generalize hpoly.positive_finite.toFinset = F at hcoe
    refine ⟨F, polydiscOnFinset c F hcoe, smoothingOnFinset c F hcoe,
      hpolyw i hi c hcp F hcoe U hU, ?_⟩
    obtain ⟨inst, hh⟩ := ((hP L hL k i hi).2 c hcp).holomorphic_smoothing
    have hm := hh.toMatrices β
    have hW : ComplexMatrix2.IsRelativelyOpen (GroupLieProduct F Empty)
        (asGroupFactors '' polydiscOnFinset c F hcoe) := by
      rw [asGroupFactors_image]
      exact isRelativelyOpen_leftComponents_preimage
        (isRelativelyOpen_polydiscOnFinset F hcoe hpoly.isRelativelyOpen)
    have hmemF : ∀ s : DoubleBlockPolydisc.Infinite.positiveDoubleBlockBonds L k i c, s.1 ∈ F :=
      fun s => by
        have : s.1 ∈ (F : Set (FullSpace.Edge L k i)) := by
          rw [hcoe]
          exact s.2
        exact this
    let Ψ : (F ⊕ Empty → ComplexMatrix2) →
        DoubleBlockPolydisc.Infinite.positiveDoubleBlockBonds L k i c ⊕ Empty → ComplexMatrix2 :=
      fun p => asGroupFactors (pointOfFinset c F hcoe (DoubleBlockPolydisc.leftComponents p))
    have hΨ : IsHolomorphicToProduct β (asGroupFactors '' polydiscOnFinset c F hcoe) Ψ :=
      ⟨hW, fun s => isHolomorphicToUnimodular_component H β hW ⟨s.1, hmemF s⟩, fun e => e.elim⟩
    obtain ⟨_, _, hcomp⟩ := H.2.2.2.2.1 F Empty _ Empty β _ Ψ hΨ.1 hΨ ComplexMatrix2 4
      Coordinates.ComplexCoordinates.matrixEquiv _ _ hm
    have e : asGroupFactors '' polydiscOnFinset c F hcoe ∩
        Ψ ⁻¹' (DoubleBlockPolydisc.leftComponents ⁻¹'
          DoubleBlockPolydisc.Infinite.polydiscPositive L k i (polydiscRadius L) c) =
        asGroupFactors '' polydiscOnFinset c F hcoe := by
      refine inter_eq_left.2 ?_
      rintro _ ⟨w, hw, rfl⟩
      exact hw
    rw [e] at hcomp
    exact hcomp
  · intro i hi c hcp
    have hpoly := ((hP L hL k i hi).2 c hcp).finite_open
    exact ⟨hpoly.positive_finite.toFinset, hpoly.positive_finite.coe_toFinset,
      hpolyw i hi c hcp _ _⟩
end Infinite
theorem meanStableFieldsHold_proof (H : ExpChartHolomorphy.ExpChartTheory)
    (hE : PeriodicLattice.BondEndpointsOrientation.Statement)
    (hP : DoubleBlockPolydisc.PolydiscsHold)
    (hS : SmoothingNearIdentity)
    (hV : ComplexMeanLiesInComplexGaugeGroup)
    (hR : PeriodicLattice.ComplexAverageIsLocal)
    (hE6 : BondSetFields.ProductStructureHolds)
    (hE4 : FamilyProducts.FamilyProductsStatement)
    (hQ : SublatticesSymmetriesScalingsAndProjections.Statement)
    (hZ : BlockStructure)
    (hL2 : FullSpace.UniqueValue.PresentationsAgreeAndBallsOpen)
    (hH : LevelwiseMeans.LevelwiseMeansHold) :
    MeanStableFieldsHold := by
  intro L hL k hk
  obtain ⟨h₁, h₂⟩ := hH L hL k hk
  exact ⟨fun n hn => meanStable_periodic H hE hP hS hV hR hE6 hE4 (h₁ n hn) hL hn hk,
    Infinite.meanStable_fullSpace H hP hS hV hQ hZ hE4 hL2 h₂ hL⟩
end YangMills.Construction.Tower.MeanStableFields
end
