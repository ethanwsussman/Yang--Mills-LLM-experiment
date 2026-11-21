import YangMills.Construction.Matrices.FiniteMatrixProducts
import YangMills.Construction.Towers.CovariantAveragesAtTheTrivialConfigurationProof
import YangMills.Construction.Towers.MapOfAWritingNearThePoint
import Mathlib
set_option autoImplicit false
open Set
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction
namespace LocalPresentations
open InfiniteLattice
variable {L k j : ℕ}
theorem inv_mem_compactGaugeGroup (M : Matrices.ComplexMatrix2)
    (hM : M ∈ PeriodicLattice.compactGaugeGroup) :
    M⁻¹ ∈ PeriodicLattice.compactGaugeGroup ∧ M⁻¹⁻¹ = M := by
  have hdet : IsUnit M.det := by
    rw [(Matrix.mem_specialUnitaryGroup_iff.1 hM).2]
    exact isUnit_one
  refine ⟨?_, Matrix.nonsing_inv_nonsing_inv M hdet⟩
  have hA : M⁻¹ = (((⟨M, hM⟩ : Matrices.ComplexMatrix2.specialUnitary)⁻¹ :
      Matrices.ComplexMatrix2.specialUnitary) : Matrices.ComplexMatrix2) :=
    Matrix.inv_eq_right_inv
      (congrArg Subtype.val (mul_inv_cancel (⟨M, hM⟩ : Matrices.ComplexMatrix2.specialUnitary)))
  rw [hA]
  exact Subtype.prop _
theorem inv_mem_complexGaugeGroup (M : Matrices.ComplexMatrix2)
    (hM : M ∈ PeriodicLattice.complexGaugeGroup) :
    M⁻¹ ∈ PeriodicLattice.complexGaugeGroup ∧ M⁻¹⁻¹ = M := by
  have hd : M.det = 1 := hM
  have hdet : IsUnit M.det := by
    rw [hd]
    exact isUnit_one
  refine ⟨?_, Matrix.nonsing_inv_nonsing_inv M hdet⟩
  change (M⁻¹).det = 1
  rw [Matrix.det_nonsing_inv, hd]
  simp
theorem meshAt_pos (hL : Conventions.IsAdmissibleBlockingFactor L) : 0 < Tower.meshAt L k j := by apply _root_.YangMills.Construction.Tower.TrivialFieldAverages.meshAt_pos <;> assumption
theorem opposite_isPositivelyOriented_iff {a : ℝ} (ha : 0 < a) (e : Link a) :
    e.opposite.IsPositivelyOriented ↔ ¬ e.IsPositivelyOriented := by apply _root_.YangMills.Construction.Tower.TrivialFieldAverages.link_opposite_positive_iff <;> assumption
theorem replaceOn_of_isPositivelyOriented {F : Finset (Tower.FullSpace.Edge L k j)}
    {U : Tower.FullSpace.Edge L k j → Matrices.ComplexMatrix2} {w : F → Matrices.ComplexMatrix2}
    {e : Tower.FullSpace.Edge L k j} (he : e.IsPositivelyOriented) :
    replaceOn F U w e = positiveEdgeValue F U w e := by
  simp [replaceOn, he]
theorem replaceOn_of_mem {F : Finset (Tower.FullSpace.Edge L k j)}
    (hF : Tower.FullSpace.IsFinitePositiveEdgeSet F)
    {U : Tower.FullSpace.Edge L k j → Matrices.ComplexMatrix2} {w : F → Matrices.ComplexMatrix2}
    {e : Tower.FullSpace.Edge L k j} (he : e ∈ F) :
    replaceOn F U w e = w ⟨e, he⟩ := by
  rw [replaceOn_of_isPositivelyOriented (hF.2 e he)]
  simp [positiveEdgeValue, he]
theorem replaceOn_of_not_mem {F : Finset (Tower.FullSpace.Edge L k j)}
    {U : Tower.FullSpace.Edge L k j → Matrices.ComplexMatrix2} {w : F → Matrices.ComplexMatrix2}
    {e : Tower.FullSpace.Edge L k j} (he : e.IsPositivelyOriented) (heF : e ∉ F) :
    replaceOn F U w e = U e := by
  rw [replaceOn_of_isPositivelyOriented he]
  simp [positiveEdgeValue, heF]
section Values
variable {𝒢 : Set Matrices.ComplexMatrix2}
theorem replaceOn_mem_fieldsValuedIn (ha : 0 < Tower.meshAt L k j)
    (hinv : ∀ M ∈ 𝒢, M⁻¹ ∈ 𝒢 ∧ M⁻¹⁻¹ = M) {F : Finset (Tower.FullSpace.Edge L k j)}
    {U : Tower.FullSpace.Edge L k j → Matrices.ComplexMatrix2} {w : F → Matrices.ComplexMatrix2}
    (hU : U ∈ Tower.FullSpace.fieldsValuedIn L k j 𝒢)
    (hw : w ∈ Tower.FullSpace.edgeProduct 𝒢 F) :
    replaceOn F U w ∈ Tower.FullSpace.fieldsValuedIn L k j 𝒢 := by
  have hval : ∀ e, positiveEdgeValue F U w e ∈ 𝒢 := by
    intro e
    unfold positiveEdgeValue
    split_ifs with he
    · exact hw _
    · exact hU.1 e
  refine ⟨fun e => ?_, fun e => ?_⟩
  · by_cases he : e.IsPositivelyOriented
    · simpa [replaceOn, he] using hval e
    · simpa [replaceOn, he] using (hinv _ (hval e.opposite)).1
  · by_cases he : e.IsPositivelyOriented
    · have hr : ¬ e.opposite.IsPositivelyOriented := fun h =>
        (opposite_isPositivelyOriented_iff ha e).1 h he
      simp [replaceOn, he, hr, Link.opposite_opposite]
    · have hr : e.opposite.IsPositivelyOriented := (opposite_isPositivelyOriented_iff ha e).2 he
      simp only [replaceOn, he, hr, if_true, if_false]
      exact ((hinv _ (hval e.opposite)).2).symm
variable {E : Type} {𝔇 : Set (Tower.FullSpace.Edge L k j → Matrices.ComplexMatrix2)}
  {h : (Tower.FullSpace.Edge L k j → Matrices.ComplexMatrix2) → E}
  {U : Tower.FullSpace.Edge L k j → Matrices.ComplexMatrix2}
theorem exists_nbhd_subset_of_isLocalPresentation
    (hprod : Matrices.FamilyProducts.FamilyProductsStatement)
    {F : Finset (Tower.FullSpace.Edge L k j)} {O : Set (F → Matrices.ComplexMatrix2)}
    {f : (F → Matrices.ComplexMatrix2) → E}
    (hW : Tower.FullSpace.IsLocalPresentation 𝒢 𝔇 h U F O f) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ w ∈ Tower.FullSpace.edgeProduct 𝒢 F,
      (∀ e : F, Matrices.ComplexMatrix2.operatorNorm (w e - U e) < ε) → w ∈ O := by
  obtain ⟨hF, hopen, hmem, -⟩ := hW
  have : Nonempty F := hF.1.to_subtype
  have hsub : O ⊆ Tower.FullSpace.edgeProduct 𝒢 F := by
    obtain ⟨O₀, -, hO⟩ := hopen
    rw [hO]
    exact inter_subset_right
  obtain ⟨ε, hε, hball⟩ :=
    ((hprod F).2.1 (Tower.FullSpace.edgeProduct 𝒢 F) O hsub).1 hopen _ hmem
  exact ⟨ε, hε, fun w hw hn => hball w hw hn⟩
theorem presentationsAgree (hprod : Matrices.FamilyProducts.FamilyProductsStatement)
    (ha : 0 < Tower.meshAt L k j) (hinv : ∀ M ∈ 𝒢, M⁻¹ ∈ 𝒢 ∧ M⁻¹⁻¹ = M)
    (h𝔇 : Tower.FullSpace.IsFinitelyOpen 𝒢 𝔇) (hU : U ∈ 𝔇) : PresentationsAgree 𝒢 𝔇 h U := by
  intro F₁ F₂ F O₁ O₂ f₁ f₂ h₁ h₂ hF hW₁ hW₂
  obtain ⟨ε₀, hε₀, hopen⟩ := h𝔇.2 U hU F hF
  obtain ⟨ε₁, hε₁, hball₁⟩ := exists_nbhd_subset_of_isLocalPresentation hprod hW₁
  obtain ⟨ε₂, hε₂, hball₂⟩ := exists_nbhd_subset_of_isLocalPresentation hprod hW₂
  refine ⟨min ε₀ (min ε₁ ε₂), lt_min hε₀ (lt_min hε₁ hε₂), fun w hw hnear => ?_⟩
  have hnear₀ : ∀ e : F, Matrices.ComplexMatrix2.operatorNorm (w e - U e) < ε₀ := fun e =>
    lt_of_lt_of_le (hnear e) (min_le_left _ _)
  have hnear₁ : ∀ e : F, Matrices.ComplexMatrix2.operatorNorm (w e - U e) < ε₁ := fun e =>
    lt_of_lt_of_le (hnear e) ((min_le_right _ _).trans (min_le_left _ _))
  have hnear₂ : ∀ e : F, Matrices.ComplexMatrix2.operatorNorm (w e - U e) < ε₂ := fun e =>
    lt_of_lt_of_le (hnear e) ((min_le_right _ _).trans (min_le_right _ _))
  have hin : replaceOn F U w ∈ 𝔇 := by
    refine hopen _ (replaceOn_mem_fieldsValuedIn ha hinv (h𝔇.1 hU) hw)
      (fun e he heF => replaceOn_of_not_mem he heF) (fun e heF => ?_)
    rw [replaceOn_of_mem hF heF]
    exact hnear₀ ⟨e, heF⟩
  have hr₁ : restrictTuple h₁ w ∈ O₁ :=
    hball₁ _ (fun e => hw ⟨e, h₁ e.2⟩) (fun e => hnear₁ ⟨e, h₁ e.2⟩)
  have hr₂ : restrictTuple h₂ w ∈ O₂ :=
    hball₂ _ (fun e => hw ⟨e, h₂ e.2⟩) (fun e => hnear₂ ⟨e, h₂ e.2⟩)
  have he₁ : Tower.FullSpace.restrictToEdges F₁ (replaceOn F U w) = restrictTuple h₁ w := by
    funext e
    exact replaceOn_of_mem hF (h₁ e.2)
  have he₂ : Tower.FullSpace.restrictToEdges F₂ (replaceOn F U w) = restrictTuple h₂ w := by
    funext e
    exact replaceOn_of_mem hF (h₂ e.2)
  refine ⟨hin, hr₁, hr₂, ?_, ?_⟩
  · rw [hW₁.2.2.2 _ hin (by rw [he₁]; exact hr₁), he₁]
  · rw [hW₂.2.2.2 _ hin (by rw [he₂]; exact hr₂), he₂]
theorem presentationShrinks (hprod : Matrices.FamilyProducts.FamilyProductsStatement)
    (ha : 0 < Tower.meshAt L k j) (hinv : ∀ M ∈ 𝒢, M⁻¹ ∈ 𝒢 ∧ M⁻¹⁻¹ = M)
    (h𝔇 : Tower.FullSpace.IsFinitelyOpen 𝒢 𝔇) (hU : U ∈ 𝔇) (kept : Set (Set E)) :
    PresentationShrinks 𝒢 kept 𝔇 h U := by
  intro F O f hW
  have hF : Tower.FullSpace.IsFinitePositiveEdgeSet F := hW.1
  refine ⟨?_, fun O'' hopen hsub hmem f'' heq => ⟨hF, hopen, hmem, fun U' hU' hin => ?_⟩⟩
  · obtain ⟨ε, hε, hall⟩ := presentationsAgree hprod ha hinv h𝔇 hU F F F O O f f subset_rfl
      subset_rfl hF hW hW
    have : Nonempty F := hF.1.to_subtype
    have hO' : ∀ w ∈ Matrices.FamilyProducts.familyNbhd (Tower.FullSpace.restrictToEdges F U) ε ∩
        Tower.FullSpace.edgeProduct 𝒢 F, replaceOn F U w ∈ 𝔇 ∧ w ∈ O ∧
          f w = h (replaceOn F U w) := fun w hw => by
      obtain ⟨h₁, h₂, -, h₃, -⟩ := hall w hw.2 hw.1
      exact ⟨h₁, h₂, h₃⟩
    refine ⟨_, ⟨_, ((hprod F).1 (Tower.FullSpace.restrictToEdges F U)).1 ε hε, rfl⟩,
      fun w hw => (hO' w hw).2.1,
      ⟨fun e => ?_, fun e => (h𝔇.1 hU).1 e⟩, fun w hw => ⟨_, (hO' w hw).1, (hO' w hw).2.2⟩,
      fun S _ hS w hw => ?_⟩
    · simpa [Matrices.ComplexMatrix2.operatorNorm] using hε
    · rw [(hO' w hw).2.2]
      exact hS _ (hO' w hw).1
  · rw [heq hin]
    exact hW.2.2.2 U' hU' (hsub hin)
theorem nearPointProperties_of_inv_mem (hprod : Matrices.FamilyProducts.FamilyProductsStatement)
    (ha : 0 < Tower.meshAt L k j) (hinv : ∀ M ∈ 𝒢, M⁻¹ ∈ 𝒢 ∧ M⁻¹⁻¹ = M)
    (kept : Set (Set E)) : NearPointProperties L k j 𝒢 kept := by
  intro 𝔇 h U h𝔇 hU
  exact ⟨fun F w _ hw => replaceOn_mem_fieldsValuedIn ha hinv (h𝔇.1 hU) hw,
    presentationsAgree hprod ha hinv h𝔇 hU, presentationShrinks hprod ha hinv h𝔇 hU kept⟩
end Values
theorem localPresentationNearPoint_holds
    (hprod : Matrices.FamilyProducts.FamilyProductsStatement) : LocalPresentationNearPoint := by
  intro L hL k j _
  have ha : 0 < Tower.meshAt L k j := meshAt_pos hL
  exact ⟨nearPointProperties_of_inv_mem hprod ha inv_mem_compactGaugeGroup _,
    nearPointProperties_of_inv_mem hprod ha inv_mem_compactGaugeGroup _,
    nearPointProperties_of_inv_mem hprod ha inv_mem_complexGaugeGroup _,
    nearPointProperties_of_inv_mem hprod ha inv_mem_complexGaugeGroup _⟩
end LocalPresentations
end YangMills.Construction
end
