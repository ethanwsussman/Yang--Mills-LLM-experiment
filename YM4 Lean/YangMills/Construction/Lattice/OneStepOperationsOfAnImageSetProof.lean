import YangMills.Construction.Lattice.ConstraintMapFormedNearZero
import YangMills.Construction.Lattice.EliminationMapOfAFormedSetProof
import YangMills.Construction.Lattice.HolomorphyOfTheContinuationsUnderIsometriesProof
import YangMills.Construction.Lattice.LinearisingCorrectionOfAFormedSetProof
import YangMills.Construction.Lattice.OneStepIdentitiesAtAnImageBond
import YangMills.Construction.Lattice.OneStepOperationsOfAnImageSet
import YangMills.Construction.Lattice.TwistedMapsAndHessiansUnderIsometriesProof
import YangMills.Construction.Matrices.ConjugationDeterminantProof
import Mathlib
set_option autoImplicit false
open Set Filter
open scoped Topology
noncomputable section
namespace YangMills.Construction.PeriodicLattice
open YangMills.Construction.Matrices
namespace ImageSetIntertwining
variable {L m : ℕ} {j j' : ℤ}
theorem conjugateBy_add (X A B : ComplexMatrix2) :
    ComplexMatrix2.conjugateBy X (A + B) =
      ComplexMatrix2.conjugateBy X A + ComplexMatrix2.conjugateBy X B := by
  simp only [ComplexMatrix2.conjugateBy, mul_add, add_mul]
theorem conjugateBy_smul (X : ComplexMatrix2) (z : ℂ) (A : ComplexMatrix2) :
    ComplexMatrix2.conjugateBy X (z • A) = z • ComplexMatrix2.conjugateBy X A := by apply _root_.YangMills.Construction.LieInnerProductProof.conjugateBy_smul <;> assumption
theorem conjugateBy_zero (X : ComplexMatrix2) : ComplexMatrix2.conjugateBy X 0 = 0 := by
  simp [ComplexMatrix2.conjugateBy]
theorem conjugateBy_mem (X A : ComplexMatrix2) (hA : A ∈ complexLieAlgebra) :
    ComplexMatrix2.conjugateBy X A ∈ complexLieAlgebra :=
  (conjugationLinearMap X ⟨A, hA⟩).2
theorem conjugateBy_inv_conjugateBy {X : ComplexMatrix2} (hX : IsUnit X.det) (A : ComplexMatrix2) :
    ComplexMatrix2.conjugateBy X⁻¹ (ComplexMatrix2.conjugateBy X A) = A := by apply _root_.YangMills.SharedProofs.p32697 <;> assumption
theorem conjugateBy_conjugateBy_inv {X : ComplexMatrix2} (hX : IsUnit X.det) (A : ComplexMatrix2) :
    ComplexMatrix2.conjugateBy X (ComplexMatrix2.conjugateBy X⁻¹ A) = A := by apply _root_.YangMills.SharedProofs.p1183 <;> assumption
theorem twistedFormValue_add (σ : FourTorus L m ≃ FourTorus L m) (V₀ A B : Bond L m j → ComplexMatrix2)
    (b : Bond L m j) :
    twistedFormValue σ V₀ (A + B) b = twistedFormValue σ V₀ A b + twistedFormValue σ V₀ B b := by apply _root_.YangMills.Construction.PeriodicLattice.ContinuationHolomorphy.twistedFormValue_add <;> assumption
theorem twistedFormValue_smul (σ : FourTorus L m ≃ FourTorus L m) (V₀ A : Bond L m j → ComplexMatrix2)
    (z : ℂ) (b : Bond L m j) :
    twistedFormValue σ V₀ (z • A) b = z • twistedFormValue σ V₀ A b := by
  unfold twistedFormValue
  split_ifs
  · rfl
  · simp only [Pi.smul_apply, conjugateBy_smul, smul_neg]
theorem twistedFormValue_congr (σ : FourTorus L m ≃ FourTorus L m)
    (V₀ A B : Bond L m j → ComplexMatrix2) (b : Bond L m j)
    (h₁ : A (bondPreimage σ b) = B (bondPreimage σ b))
    (h₂ : A (bondPreimage σ b).opposite = B (bondPreimage σ b).opposite) :
    twistedFormValue σ V₀ A b = twistedFormValue σ V₀ B b := by
  unfold twistedFormValue
  split_ifs
  · exact h₁
  · rw [h₂]
theorem twistedTransportForm_of_pos (σ : FourTorus L m ≃ FourTorus L m)
    (V₀ A : Bond L m j → ComplexMatrix2) {b : Bond L m j}
    (hb : b.IsPositivelyOriented) : twistedTransportForm σ V₀ A b = twistedFormValue σ V₀ A b := by
  simp only [twistedTransportForm, if_pos hb]
theorem twistedTransportForm_add (σ : FourTorus L m ≃ FourTorus L m)
    (V₀ A B : Bond L m j → ComplexMatrix2) :
    twistedTransportForm σ V₀ (A + B) =
      twistedTransportForm σ V₀ A + twistedTransportForm σ V₀ B := by apply _root_.YangMills.Construction.PeriodicLattice.TwistedTransport.twisted_add <;> assumption
theorem twistedTransportForm_smul (σ : FourTorus L m ≃ FourTorus L m)
    (V₀ A : Bond L m j → ComplexMatrix2) (z : ℂ) :
    twistedTransportForm σ V₀ (z • A) = z • twistedTransportForm σ V₀ A := by
  funext b
  simp only [twistedTransportForm, Pi.smul_apply]
  split_ifs
  · exact twistedFormValue_smul σ V₀ A z b
  · rw [twistedFormValue_smul, smul_neg]
structure LevelTransport (σ : FourTorus L m ≃ FourTorus L m) (j : ℤ) : Prop where
  preimage_image : ∀ b : Bond L m j, bondPreimage σ (bondImage σ b) = b
  image_preimage : ∀ b : Bond L m j, bondImage σ (bondPreimage σ b) = b
  image_opposite : ∀ b : Bond L m j, bondImage σ b.opposite = (bondImage σ b).opposite
  preimage_opposite : ∀ b : Bond L m j, bondPreimage σ b.opposite = (bondPreimage σ b).opposite
  xor : ∀ b : Bond L m j, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented
theorem opposite_opposite (b : Bond L m j) : b.opposite.opposite = b := rfl
namespace LevelTransport
variable {σ : FourTorus L m ≃ FourTorus L m}
theorem not_pos_opposite (l : LevelTransport σ j) {b : Bond L m j} (hb : b.IsPositivelyOriented) :
    ¬ b.opposite.IsPositivelyOriented := by
  rcases l.xor b with h | h
  · exact h.2
  · exact absurd hb h.2
theorem pos_opposite (l : LevelTransport σ j) {b : Bond L m j} (hb : ¬ b.IsPositivelyOriented) :
    b.opposite.IsPositivelyOriented := by
  rcases l.xor b with h | h
  · exact absurd h.1 hb
  · exact h.1
theorem twistedFormValue_image (l : LevelTransport σ j) (V₀ A : Bond L m j → ComplexMatrix2)
    {b : Bond L m j} (hb : b.IsPositivelyOriented) :
    twistedFormValue σ V₀ A (bondImage σ b) = A b := by
  unfold twistedFormValue
  rw [l.preimage_image, if_pos hb]
theorem twistedFormValue_image_opposite (l : LevelTransport σ j) (V₀ A : Bond L m j → ComplexMatrix2)
    {b : Bond L m j} (hb : b.IsPositivelyOriented) :
    twistedFormValue σ V₀ A (bondImage σ b).opposite = -ComplexMatrix2.conjugateBy (V₀ b)⁻¹ (A b) := by
  unfold twistedFormValue
  rw [l.preimage_opposite, l.preimage_image, if_neg (l.not_pos_opposite hb)]
  rfl
theorem twistedFormValue_congr_at (l : LevelTransport σ j) (V₀ A B : Bond L m j → ComplexMatrix2)
    {c c' : Bond L m j} (hc : c.IsPositivelyOriented)
    (hr : c' = bondImage σ c ∨ c' = (bondImage σ c).opposite)
    (h : A c = B c) : twistedFormValue σ V₀ A c' = twistedFormValue σ V₀ B c' := by
  rcases hr with rfl | rfl
  · rw [l.twistedFormValue_image _ _ hc, l.twistedFormValue_image _ _ hc, h]
  · rw [l.twistedFormValue_image_opposite _ _ hc, l.twistedFormValue_image_opposite _ _ hc, h]
theorem twistedTransportForm_congr (l : LevelTransport σ j) (V₀ A B : Bond L m j → ComplexMatrix2)
    (b : Bond L m j)
    (h₁ : A (bondPreimage σ b) = B (bondPreimage σ b))
    (h₂ : A (bondPreimage σ b).opposite = B (bondPreimage σ b).opposite) :
    twistedTransportForm σ V₀ A b = twistedTransportForm σ V₀ B b := by
  simp only [twistedTransportForm]
  split_ifs
  · exact twistedFormValue_congr σ V₀ A B b h₁ h₂
  · rw [twistedFormValue_congr σ V₀ A B b.opposite (by rw [l.preimage_opposite]; exact h₂)
      (by rw [l.preimage_opposite]; exact h₁)]
theorem twistedTransportForm_isBondForm (l : LevelTransport σ j) (V₀ : Bond L m j → ComplexMatrix2)
    {A : Bond L m j → ComplexMatrix2} (hA : IsBondForm complexLieAlgebra A) :
    IsBondForm complexLieAlgebra (twistedTransportForm σ V₀ A) := by
  refine ⟨fun b hb => ?_, fun b => ?_⟩
  · rw [twistedTransportForm_of_pos σ V₀ A hb]
    unfold twistedFormValue
    split_ifs with h
    · exact hA.1 _ h
    · exact (Submodule.neg_mem _ (conjugateBy_mem _ _ (hA.1 _ (l.pos_opposite h))) :)
  · by_cases hb : b.IsPositivelyOriented
    · simp only [twistedTransportForm, if_pos hb, if_neg (l.not_pos_opposite hb)]
      rfl
    · simp only [twistedTransportForm, if_pos (l.pos_opposite hb), if_neg hb, neg_neg]
end LevelTransport
theorem extendForm_add {Γ : Set (Bond L m j)} (B B' : SupportBond j' Γ → ComplexMatrix2) :
    extendForm (B + B') = extendForm B + extendForm B' := by
  funext b
  simp only [extendForm, Pi.add_apply]
  split_ifs
  · rfl
  · rw [neg_add]
  · rw [add_zero]
theorem extendForm_smul {Γ : Set (Bond L m j)} (z : ℂ) (B : SupportBond j' Γ → ComplexMatrix2) :
    extendForm (z • B) = z • extendForm B := by apply _root_.YangMills.Construction.PeriodicLattice.LinearizingCorrection.extendForm_smul <;> assumption
theorem extendForm_of_mem {Γ : Set (Bond L m j)} (B : SupportBond j' Γ → ComplexMatrix2)
    {b : Bond L m j'} (hb : b ∈ doubleBlockSupport j' Γ ∧ b.IsPositivelyOriented) :
    extendForm B b = B ⟨b, hb⟩ := by
  simp only [extendForm, dif_pos hb]
theorem extendForm_of_not_mem {σ : FourTorus L m ≃ FourTorus L m} (l : LevelTransport σ j')
    {Γ : Set (Bond L m j)} (B : SupportBond j' Γ → ComplexMatrix2) {b : Bond L m j'}
    (hp : b.IsPositivelyOriented) (hb : b ∉ doubleBlockSupport j' Γ) : extendForm B b = 0 := by
  simp only [extendForm]
  rw [dif_neg (fun h => hb h.1), dif_neg (fun h => l.not_pos_opposite hp h.2)]
theorem extendForm_opposite {σ : FourTorus L m ≃ FourTorus L m} (l : LevelTransport σ j')
    {Γ : Set (Bond L m j)} (B : SupportBond j' Γ → ComplexMatrix2) (b : Bond L m j') :
    extendForm B b.opposite = -extendForm B b := by
  have key : ∀ b : Bond L m j', b.IsPositivelyOriented →
      extendForm B b.opposite = -extendForm B b := by
    intro b hp
    by_cases hb : b ∈ doubleBlockSupport j' Γ
    · rw [extendForm_of_mem B ⟨hb, hp⟩]
      simp only [extendForm]
      rw [dif_neg (fun h => l.not_pos_opposite hp h.2), dif_pos (show b.opposite.opposite ∈
        doubleBlockSupport j' Γ ∧ b.opposite.opposite.IsPositivelyOriented from ⟨hb, hp⟩)]
      try rfl
    · rw [extendForm_of_not_mem l B hp hb]
      simp only [extendForm]
      rw [dif_neg (fun h => l.not_pos_opposite hp h.2), dif_neg (fun h => hb h.1), neg_zero]
  by_cases hp : b.IsPositivelyOriented
  · exact key b hp
  · have := key b.opposite (l.pos_opposite hp)
    rw [opposite_opposite] at this
    rw [this, neg_neg]
theorem supportForms_eq_tracelessPi (Γ : Set (Bond L m j)) :
    (supportForms j' Γ : Set (SupportBond j' Γ → ComplexMatrix2)) =
      GroupLieProduct.tracelessPi (SupportBond j' Γ) := by
  ext B
  simp only [supportForms, SetLike.mem_coe, Submodule.mem_pi, mem_univ, forall_true_left]
  rfl
theorem extendForm_isBondForm {σ : FourTorus L m ≃ FourTorus L m} (l : LevelTransport σ j')
    {Γ : Set (Bond L m j)} {B : SupportBond j' Γ → ComplexMatrix2}
    (hB : B ∈ GroupLieProduct.tracelessPi (SupportBond j' Γ)) :
    IsBondForm complexLieAlgebra (extendForm B) := by
  refine ⟨fun b hp => ?_, fun b => extendForm_opposite l B b⟩
  by_cases hb : b ∈ doubleBlockSupport j' Γ
  · rw [extendForm_of_mem B ⟨hb, hp⟩]
    exact hB _
  · rw [extendForm_of_not_mem l B hp hb]
    exact Submodule.zero_mem _
theorem pivotCoeffInv_spec {V : Bond L m j' → ComplexMatrix2} {c : Bond L m j}
    (hinv : PivotCoeffInvertible V c) {Y : ComplexMatrix2} (hY : Y ∈ ComplexMatrix2.traceless) :
    pivotCoeffInv V c Y ∈ ComplexMatrix2.traceless ∧
      pivotCoeff V c (pivotCoeffInv V c Y) = Y := by
  obtain ⟨T, hT⟩ := hinv
  have hex : ∃ a ∈ (ComplexMatrix2.traceless : Set ComplexMatrix2), pivotCoeff V c a = Y :=
    ⟨(T.symm ⟨Y, hY⟩ : ComplexMatrix2.traceless), (T.symm ⟨Y, hY⟩).2, by
      rw [← hT, LinearEquiv.apply_symm_apply]⟩
  exact ⟨Function.invFunOn_mem hex, Function.invFunOn_eq hex⟩
theorem pivotCoeffInv_eq {V : Bond L m j' → ComplexMatrix2} {c : Bond L m j}
    (hinv : PivotCoeffInvertible V c) {X Y : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.traceless)
    (h : pivotCoeff V c X = Y) : pivotCoeffInv V c Y = X := by
  have hY : Y ∈ ComplexMatrix2.traceless := by
    obtain ⟨T, hT⟩ := hinv
    rw [← h]
    have := hT ⟨X, hX⟩
    rw [show pivotCoeff V c X = _ from this.symm]
    exact (T ⟨X, hX⟩).2
  obtain ⟨h₁, h₂⟩ := pivotCoeffInv_spec hinv hY
  obtain ⟨T, hT⟩ := hinv
  have e₁ := hT ⟨_, h₁⟩
  have e₂ := hT ⟨X, hX⟩
  have : T ⟨_, h₁⟩ = T ⟨X, hX⟩ := Subtype.ext (by rw [e₁, e₂]; exact h₂.trans h.symm)
  exact congrArg Subtype.val (T.injective this)
theorem pivotCorrectionLift_at_pivot {V : Bond L m j' → ComplexMatrix2} {Γ : Set (Bond L m j)}
    (hinj : ∀ c ∈ Γ, ∀ c'' ∈ Γ, (pivot c : Bond L m j') = pivot c'' → c = c'')
    {c : Bond L m j} (hc : c ∈ Γ)
    (hb : (pivot c : Bond L m j') ∈ doubleBlockSupport j' Γ ∧
      (pivot c : Bond L m j').IsPositivelyOriented) (ν : ↥Γ → ComplexMatrix2) :
    pivotCorrectionLift V Γ ν ⟨pivot c, hb⟩ =
      ((L : ℂ)⁻¹) • pivotCoeffInv V c (ν ⟨c, hc⟩) := by
  have h : ∃ c₀ : ↥Γ, ((⟨pivot c, hb⟩ : SupportBond j' Γ) : Bond L m j') =
      pivot (c₀ : Bond L m j) := ⟨⟨c, hc⟩, rfl⟩
  have e : h.choose = ⟨c, hc⟩ := Subtype.ext (hinj _ h.choose.2 _ hc h.choose_spec.symm)
  simp only [pivotCorrectionLift]
  rw [dif_pos h, e]
theorem pivotCorrectionLift_off_pivot {V : Bond L m j' → ComplexMatrix2} {Γ : Set (Bond L m j)}
    (b : SupportBond j' Γ)
    (h : ¬ ∃ c₀ : ↥Γ, (b : Bond L m j') = pivot (c₀ : Bond L m j)) (ν : ↥Γ → ComplexMatrix2) :
    pivotCorrectionLift V Γ ν b = 0 := by
  simp only [pivotCorrectionLift]
  rw [dif_neg h]
theorem pivotCorrectionLift_mem {V : Bond L m j' → ComplexMatrix2} {Γ : Set (Bond L m j)}
    (hinv : ∀ c ∈ Γ, PivotCoeffInvertible V c) {ν : ↥Γ → ComplexMatrix2}
    (hν : ∀ c, ν c ∈ ComplexMatrix2.traceless) (b : SupportBond j' Γ) :
    pivotCorrectionLift V Γ ν b ∈ ComplexMatrix2.traceless := by
  simp only [pivotCorrectionLift]
  split_ifs with h
  · exact Submodule.smul_mem _ _ (pivotCoeffInv_spec (hinv _ h.choose.2) (hν _)).1
  · exact Submodule.zero_mem _
theorem pivotCoeffInv_tendsto {V : Bond L m j' → ComplexMatrix2} {c : Bond L m j}
    (hinv : PivotCoeffInvertible V c) :
    Tendsto (pivotCoeffInv V c) (𝓝[(ComplexMatrix2.traceless : Set ComplexMatrix2)] 0) (𝓝 0) := by
  have h0 : (0 : ComplexMatrix2) ∈ (ComplexMatrix2.traceless : Set ComplexMatrix2) :=
    Submodule.zero_mem _
  rw [nhdsWithin_eq_map_subtype_coe h0, tendsto_map'_iff]
  obtain ⟨T, hT⟩ := id hinv
  have hcont : Continuous (T.symm : ↥ComplexMatrix2.traceless →ₗ[ℂ] ↥ComplexMatrix2.traceless) :=
    LinearMap.continuous_of_finiteDimensional _
  have e : pivotCoeffInv V c ∘
      (Subtype.val : ↥(ComplexMatrix2.traceless : Set ComplexMatrix2) → ComplexMatrix2) =
      fun X => ((T.symm X : ↥ComplexMatrix2.traceless) : ComplexMatrix2) := by
    funext X
    refine pivotCoeffInv_eq hinv (T.symm X).2 ?_
    rw [← hT, LinearEquiv.apply_symm_apply]
  rw [e]
  have h1 : Tendsto (fun X : ↥ComplexMatrix2.traceless => T.symm X) (𝓝 0) (𝓝 0) := by
    have := hcont.tendsto 0
    simpa using this
  exact (continuous_subtype_val.tendsto _).comp h1
theorem pivotCorrectionLift_tendsto {V : Bond L m j' → ComplexMatrix2} {Γ : Set (Bond L m j)}
    (hinv : ∀ c ∈ Γ, PivotCoeffInvertible V c) :
    Tendsto (pivotCorrectionLift V Γ) (𝓝[GroupLieProduct.tracelessPi ↥Γ] 0) (𝓝 0) := by
  rw [tendsto_pi_nhds]
  intro b
  simp only [pivotCorrectionLift]
  split_ifs with h
  · have h1 : Tendsto (fun ν : ↥Γ → ComplexMatrix2 => ν h.choose)
        (𝓝[GroupLieProduct.tracelessPi ↥Γ] 0)
        (𝓝[(ComplexMatrix2.traceless : Set ComplexMatrix2)] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · exact ((continuous_apply h.choose).tendsto' 0 0 rfl).mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with ν hν using hν h.choose
    have h2 := ((pivotCoeffInv_tendsto (hinv _ h.choose.2)).comp h1).const_smul ((L : ℂ)⁻¹)
    simpa using h2
  · exact tendsto_const_nhds
theorem isPivotBondOf_opposite {Γ : Set (Bond L m j)} {p : Bond L m j'} (h : IsPivotBondOf Γ p) :
    IsPivotBondOf Γ p.opposite := by apply _root_.YangMills.Construction.PeriodicLattice.EliminationConstruction.isPivotBondOf_opposite <;> assumption
theorem isBondForm_of_isEliminatedForm {σ : FourTorus L m ≃ FourTorus L m}
    (_l : LevelTransport σ j')
    {V : Bond L m j' → ComplexMatrix2} {Γ : Set (Bond L m j)} {A B : Bond L m j' → ComplexMatrix2}
    (hA : IsBondForm complexLieAlgebra A) (h : IsEliminatedForm V Γ A B) :
    IsBondForm complexLieAlgebra B := by
  obtain ⟨h₁, h₂, -⟩ := h
  refine ⟨fun b hb => ?_, fun b => ?_⟩
  · by_cases hp : IsPivotBondOf Γ b
    · obtain ⟨c, hc, rfl | rfl⟩ := hp
      · exact (h₂ c hc).1
      · rw [(h₂ c hc).2]
        exact Submodule.neg_mem _ (h₂ c hc).1
    · rw [h₁ b hp]
      exact hA.1 b hb
  · by_cases hp : IsPivotBondOf Γ b
    · obtain ⟨c, hc, rfl | rfl⟩ := hp
      · exact (h₂ c hc).2
      · rw [opposite_opposite, (h₂ c hc).2, neg_neg]
    · have hr : ¬ IsPivotBondOf Γ b.opposite := fun h => hp (isPivotBondOf_opposite h)
      rw [h₁ _ hr, h₁ _ hp, hA.2]
def PositiveImage (σ : FourTorus L m ≃ FourTorus L m) (c c' : Bond L m j) : Prop :=
  c'.IsPositivelyOriented ∧ (c' = bondImage σ c ∨ c' = (bondImage σ c).opposite)
structure TransportData (σ : FourTorus L m ≃ FourTorus L m) (V : Bond L m j' → ComplexMatrix2)
    (W : Bond L m j → ComplexMatrix2) (Γ Γ' : Set (Bond L m j)) : Prop where
  fine : LevelTransport σ j'
  coarse : LevelTransport σ j
  pivot_image : ∀ c : Bond L m j,
    bondImage σ (pivot c : Bond L m j') = pivot (bondImage σ c)
  pivot_opposite : ∀ c : Bond L m j,
    (pivot c.opposite : Bond L m j') = (pivot c : Bond L m j').opposite
  pivot_positive : ∀ c : Bond L m j,
    (pivot c : Bond L m j').IsPositivelyOriented ↔ c.IsPositivelyOriented
  double_image : ∀ c c' : Bond L m j, c.IsPositivelyOriented → PositiveImage σ c c' →
    bondImage σ '' (bondsInDoubleBlock c : Set (Bond L m j')) = bondsInDoubleBlock c'
  positive : ∀ c ∈ Γ, c.IsPositivelyOriented
  mem_image : ∀ c', c' ∈ Γ' ↔ ∃ c ∈ Γ, PositiveImage σ c c'
  formed : ComplexConstraintDefined V Γ
  invertible : ∀ c ∈ Γ, PivotCoeffInvertible V c
  invertible' : ∀ c' ∈ Γ', PivotCoeffInvertible (transportGaugeField σ V) c'
  pivot_injective : ∀ c ∈ Γ, ∀ c'' ∈ Γ, (pivot c : Bond L m j') = pivot c'' → c = c''
  pivot_injective' : ∀ c ∈ Γ', ∀ c'' ∈ Γ', (pivot c : Bond L m j') = pivot c'' → c = c''
  constraint : ∀ c ∈ Γ, ∀ c', PositiveImage σ c c' → ∀ A : Bond L m j' → ComplexMatrix2,
    IsBondForm complexLieAlgebra A →
    linearizedConstraint (transportGaugeField σ V) (twistedTransportForm σ V A) c' =
      twistedFormValue σ W (linearizedConstraint V A) c'
  constraint_map : ∀ c ∈ Γ, ∀ c', PositiveImage σ c c' → ∀ B : Bond L m j' → ComplexMatrix2,
    IsBondForm complexLieAlgebra B → ConstraintMapDefined V B c →
    ConstraintMapDefined (transportGaugeField σ V) (twistedTransportForm σ V B) c' →
    constraintMap (transportGaugeField σ V) (twistedTransportForm σ V B) c' =
      twistedFormValue σ W (constraintMap V B) c'
  pivot_coeff : ∀ c ∈ Γ, ∀ c', PositiveImage σ c c' → ∀ X : ↥ComplexMatrix2.traceless,
    ∃ Y : ↥ComplexMatrix2.traceless, (Y : ComplexMatrix2) = pivotCoeff V c X ∧
      pivotCoeff (transportGaugeField σ V) c'
          (twistedLinkMap σ V (pivot c) X : ↥ComplexMatrix2.traceless) =
        (twistedLinkMap σ W c Y : ↥ComplexMatrix2.traceless)
theorem mem_doubleBlockSupport_iff {Γ : Set (Bond L m j)} {b : Bond L m j'} :
    b ∈ doubleBlockSupport j' Γ ↔ ∃ c ∈ Γ, b ∈ (bondsInDoubleBlock c : Set (Bond L m j')) := by
  simp only [doubleBlockSupport, mem_iUnion, exists_prop]
theorem opposite_mem_doubleBlockSupport {Γ : Set (Bond L m j)} {b : Bond L m j'}
    (h : b ∈ doubleBlockSupport j' Γ) : b.opposite ∈ doubleBlockSupport j' Γ := by
  obtain ⟨c, hc, h₁, h₂⟩ := mem_doubleBlockSupport_iff.1 h
  exact mem_doubleBlockSupport_iff.2 ⟨c, hc, h₂, h₁⟩
namespace TransportData
variable {σ : FourTorus L m ≃ FourTorus L m} {V : Bond L m j' → ComplexMatrix2}
  {W : Bond L m j → ComplexMatrix2} {Γ Γ' : Set (Bond L m j)}
theorem exists_positiveImage (d : TransportData σ V W Γ Γ') {c : Bond L m j} (hc : c ∈ Γ) :
    ∃ c' ∈ Γ', PositiveImage σ c c' := by
  by_cases h : (bondImage σ c).IsPositivelyOriented
  · exact ⟨_, (d.mem_image _).2 ⟨c, hc, h, Or.inl rfl⟩, h, Or.inl rfl⟩
  · exact ⟨_, (d.mem_image _).2 ⟨c, hc, d.coarse.pos_opposite h, Or.inr rfl⟩,
      d.coarse.pos_opposite h, Or.inr rfl⟩
theorem bondImage_mem (d : TransportData σ V W Γ Γ') {b : Bond L m j'}
    (h : b ∈ doubleBlockSupport j' Γ) : bondImage σ b ∈ doubleBlockSupport j' Γ' := by
  obtain ⟨c, hc, hb⟩ := mem_doubleBlockSupport_iff.1 h
  obtain ⟨c', hc', hr⟩ := d.exists_positiveImage hc
  refine mem_doubleBlockSupport_iff.2 ⟨c', hc', ?_⟩
  rw [← d.double_image c c' (d.positive c hc) hr]
  exact mem_image_of_mem _ hb
theorem bondPreimage_mem (d : TransportData σ V W Γ Γ') {b : Bond L m j'}
    (h : b ∈ doubleBlockSupport j' Γ') : bondPreimage σ b ∈ doubleBlockSupport j' Γ := by
  obtain ⟨c', hc', hb⟩ := mem_doubleBlockSupport_iff.1 h
  obtain ⟨c, hc, hr⟩ := (d.mem_image c').1 hc'
  rw [← d.double_image c c' (d.positive c hc) hr] at hb
  obtain ⟨b₀, hb₀, rfl⟩ := hb
  rw [d.fine.preimage_image]
  exact mem_doubleBlockSupport_iff.2 ⟨c, hc, hb₀⟩
theorem isUnit_det (d : TransportData σ V W Γ Γ') {b : Bond L m j'}
    (h : b ∈ doubleBlockSupport j' Γ) : IsUnit (V b).det := by
  obtain ⟨c, hc, hb⟩ := mem_doubleBlockSupport_iff.1 h
  obtain ⟨⟨⟨h₁, -⟩, -⟩, -⟩ := d.formed c hc
  have : (V b).det = 1 := h₁ b hb
  rw [this]
  exact isUnit_one
theorem isPivotBondOf_bondImage (d : TransportData σ V W Γ Γ') {p : Bond L m j'}
    (h : IsPivotBondOf Γ p) : IsPivotBondOf Γ' (bondImage σ p) := by
  obtain ⟨c, hc, hp⟩ := h
  obtain ⟨c', hc', hr⟩ := d.exists_positiveImage hc
  refine ⟨c', hc', ?_⟩
  rcases hr.2 with e | e
  · rcases hp with rfl | rfl
    · exact Or.inl (by rw [e, d.pivot_image])
    · exact Or.inr (by rw [e, d.fine.image_opposite, d.pivot_image])
  · rcases hp with rfl | rfl
    · exact Or.inr (by rw [e, d.pivot_opposite, d.pivot_image]; rfl)
    · exact Or.inl (by rw [e, d.pivot_opposite, d.fine.image_opposite, d.pivot_image])
theorem isEliminatedForm_transport (d : TransportData σ V W Γ Γ')
    {A B : Bond L m j' → ComplexMatrix2}
    (hA : IsBondForm complexLieAlgebra A) (h : IsEliminatedForm V Γ A B) :
    IsEliminatedForm (transportGaugeField σ V) Γ' (twistedTransportForm σ V A)
      (twistedTransportForm σ V B) := by
  have hB := isBondForm_of_isEliminatedForm d.fine hA h
  have l := d.fine
  have hT := l.twistedTransportForm_isBondForm V hB
  refine ⟨fun b' hb' => ?_, fun c' hc' => ?_, fun c' hc' => ?_⟩
  · apply l.twistedTransportForm_congr
    · exact h.1 _ fun hp => hb' (by
        simpa only [l.image_preimage] using d.isPivotBondOf_bondImage hp)
    · exact h.1 _ fun hp => hb' (by
        simpa only [opposite_opposite, l.image_preimage] using
          d.isPivotBondOf_bondImage (isPivotBondOf_opposite hp))
  · obtain ⟨c, hc, hr⟩ := (d.mem_image c').1 hc'
    exact ⟨hT.1 _ ((d.pivot_positive c').2 hr.1), hT.2 _⟩
  · obtain ⟨c, hc, hr⟩ := (d.mem_image c').1 hc'
    rw [d.constraint c hc c' hr B hB,
      d.coarse.twistedFormValue_congr_at W _ (0 : Bond L m j → ComplexMatrix2) (d.positive c hc)
        hr.2 (h.2.2 c hc)]
    unfold twistedFormValue
    split_ifs
    · rfl
    · simp only [Pi.zero_apply, conjugateBy_zero, neg_zero]
theorem eliminate_transport (d : TransportData σ V W Γ Γ')
    (hE : ∀ A : Bond L m j' → ComplexMatrix2, IsBondForm complexLieAlgebra A →
      ∃! B, IsEliminatedForm V Γ A B)
    (hE' : ∀ A : Bond L m j' → ComplexMatrix2, IsBondForm complexLieAlgebra A →
      ∃! B, IsEliminatedForm (transportGaugeField σ V) Γ' A B)
    {A : Bond L m j' → ComplexMatrix2} (hA : IsBondForm complexLieAlgebra A) :
    eliminate (transportGaugeField σ V) Γ' (twistedTransportForm σ V A) =
      twistedTransportForm σ V (eliminate V Γ A) := by
  have hT := d.fine.twistedTransportForm_isBondForm V hA
  have h₁ : IsEliminatedForm V Γ A (eliminate V Γ A) :=
    Classical.epsilon_spec (hE A hA).exists
  have h₂ : IsEliminatedForm (transportGaugeField σ V) Γ' (twistedTransportForm σ V A)
      (eliminate (transportGaugeField σ V) Γ' (twistedTransportForm σ V A)) :=
    Classical.epsilon_spec (hE' _ hT).exists
  exact (hE' _ hT).unique h₂ (d.isEliminatedForm_transport hA h₁)
end TransportData
def coarseTransport (σ : FourTorus L m ≃ FourTorus L m) (W : Bond L m j → ComplexMatrix2)
    (Γ Γ' : Set (Bond L m j)) : (↥Γ → ComplexMatrix2) →ₗ[ℂ] (↥Γ' → ComplexMatrix2) where
  toFun ν c' := twistedFormValue σ W (Function.extend Subtype.val ν 0) c'
  map_add' ν ν' := by
    funext c'
    have e : Function.extend Subtype.val (ν + ν') (0 : Bond L m j → ComplexMatrix2) =
        Function.extend Subtype.val ν 0 + Function.extend Subtype.val ν' 0 := by
      simpa using Function.extend_add Subtype.val ν ν' (0 : Bond L m j → ComplexMatrix2) 0
    simp only [e, twistedFormValue_add, Pi.add_apply]
  map_smul' z ν := by
    funext c'
    have e : Function.extend Subtype.val (z • ν) (0 : Bond L m j → ComplexMatrix2) =
        z • Function.extend Subtype.val ν 0 := by
      simpa using Function.extend_smul z Subtype.val ν (0 : Bond L m j → ComplexMatrix2)
    simp only [e, twistedFormValue_smul, Pi.smul_apply, RingHom.id_apply]
theorem neg_conjugationLinearMap_apply (X : ComplexMatrix2) (A : ↥ComplexMatrix2.traceless) :
    (((-conjugationLinearMap X) A : ↥ComplexMatrix2.traceless) : ComplexMatrix2) =
      -ComplexMatrix2.conjugateBy X A := rfl
theorem extend_val_apply_of_mem {Γ : Set (Bond L m j)} {c : Bond L m j} (hc : c ∈ Γ)
    (ν : ↥Γ → ComplexMatrix2) :
    Function.extend Subtype.val ν (0 : Bond L m j → ComplexMatrix2) c = ν ⟨c, hc⟩ :=
  Subtype.val_injective.extend_apply ν 0 ⟨c, hc⟩
namespace TransportData
variable {σ : FourTorus L m ≃ FourTorus L m} {V : Bond L m j' → ComplexMatrix2}
  {W : Bond L m j → ComplexMatrix2} {Γ Γ' : Set (Bond L m j)}
theorem coarseTransport_mem (d : TransportData σ V W Γ Γ') {ν : ↥Γ → ComplexMatrix2}
    (hν : ν ∈ GroupLieProduct.tracelessPi ↥Γ) :
    coarseTransport σ W Γ Γ' ν ∈ GroupLieProduct.tracelessPi ↥Γ' := by
  rintro ⟨c', hc'⟩
  obtain ⟨c, hc, hr⟩ := (d.mem_image c').1 hc'
  show twistedFormValue σ W (Function.extend Subtype.val ν 0) c' ∈
    (ComplexMatrix2.traceless : Set ComplexMatrix2)
  have hcp := d.positive c hc
  have hνc : ν ⟨c, hc⟩ ∈ (ComplexMatrix2.traceless : Set ComplexMatrix2) := hν ⟨c, hc⟩
  rcases hr.2 with rfl | rfl
  · rw [d.coarse.twistedFormValue_image _ _ hcp, extend_val_apply_of_mem hc]
    exact hνc
  · rw [d.coarse.twistedFormValue_image_opposite _ _ hcp, extend_val_apply_of_mem hc]
    exact Submodule.neg_mem _ (conjugateBy_mem _ _ hνc)
set_option maxHeartbeats 1000000 in
theorem pivotCorrectionLift_transport (d : TransportData σ V W Γ Γ') {ν : ↥Γ → ComplexMatrix2}
    (hν : ∀ c, ν c ∈ ComplexMatrix2.traceless) :
    pivotCorrectionLift (transportGaugeField σ V) Γ' (coarseTransport σ W Γ Γ' ν) =
      fun b' : SupportBond j' Γ' =>
        twistedTransportForm σ V (extendForm (pivotCorrectionLift V Γ ν)) b' := by
  funext ⟨b', hb'⟩
  have l := d.fine
  show pivotCorrectionLift _ Γ' _ ⟨b', hb'⟩ =
    twistedTransportForm σ V (extendForm (pivotCorrectionLift V Γ ν)) b'
  rw [twistedTransportForm_of_pos σ V _ hb'.2]
  by_cases h : ∃ c₀ : ↥Γ', b' = pivot (c₀ : Bond L m j)
  · obtain ⟨⟨c', hc'⟩, rfl⟩ := h
    rw [pivotCorrectionLift_at_pivot d.pivot_injective' hc' hb']
    obtain ⟨c, hc, hrel⟩ := (d.mem_image c').1 hc'
    have hcp := d.positive c hc
    obtain ⟨hX, hmX⟩ := pivotCoeffInv_spec (d.invertible c hc) (hν ⟨c, hc⟩)
    obtain ⟨Y, hY, hm⟩ := d.pivot_coeff c hc c' hrel ⟨_, hX⟩
    have hYν : (Y : ComplexMatrix2) = ν ⟨c, hc⟩ := hY.trans hmX
    have hpc : (pivot c : Bond L m j').IsPositivelyOriented := (d.pivot_positive c).2 hcp
    rcases hrel.2 with e | e
    · subst e
      have hic : (bondImage σ c).IsPositivelyOriented := hrel.1
      have hbp := d.pivot_image c
      have hip : (bondImage σ (pivot c : Bond L m j')).IsPositivelyOriented := by
        rw [hbp]
        exact (d.pivot_positive _).2 hic
      have hO : twistedLinkMap σ V (pivot c : Bond L m j') = LinearMap.id := by
        simp only [twistedLinkMap, if_pos hip]
      have hOW : twistedLinkMap σ W c = LinearMap.id := by
        simp only [twistedLinkMap, if_pos hic]
      rw [hO, hOW] at hm
      simp only [LinearMap.id_apply] at hm
      have hrho : coarseTransport σ W Γ Γ' ν ⟨bondImage σ c, hc'⟩ = ν ⟨c, hc⟩ := by
        show twistedFormValue σ W (Function.extend Subtype.val ν 0) (bondImage σ c) = _
        rw [d.coarse.twistedFormValue_image _ _ hcp, extend_val_apply_of_mem hc]
      have hmem : (pivot c : Bond L m j') ∈ doubleBlockSupport j' Γ := by
        have := d.bondPreimage_mem hb'.1
        rwa [← hbp, l.preimage_image] at this
      rw [hrho, pivotCoeffInv_eq (d.invertible' _ hc') hX (hm.trans hYν), ← hbp,
        l.twistedFormValue_image _ _ hpc, extendForm_of_mem _ ⟨hmem, hpc⟩,
        pivotCorrectionLift_at_pivot d.pivot_injective hc]
    · subst e
      have hic : ¬ (bondImage σ c).IsPositivelyOriented := d.coarse.not_pos_opposite hrel.1
      have hbp : (pivot (bondImage σ c).opposite : Bond L m j') =
          (bondImage σ (pivot c : Bond L m j')).opposite := by
        rw [d.pivot_opposite, d.pivot_image]
      have hip : ¬ (bondImage σ (pivot c : Bond L m j')).IsPositivelyOriented := by
        rw [d.pivot_image]
        exact fun h => hic ((d.pivot_positive _).1 h)
      have hO : twistedLinkMap σ V (pivot c : Bond L m j') =
          -conjugationLinearMap (V (pivot c))⁻¹ := by
        simp only [twistedLinkMap, if_neg hip]
      have hOW : twistedLinkMap σ W c = -conjugationLinearMap (W c)⁻¹ := by
        simp only [twistedLinkMap, if_neg hic]
      rw [hO, hOW] at hm
      have hrho : coarseTransport σ W Γ Γ' ν ⟨(bondImage σ c).opposite, hc'⟩ =
          -ComplexMatrix2.conjugateBy (W c)⁻¹ (ν ⟨c, hc⟩) := by
        show twistedFormValue σ W (Function.extend Subtype.val ν 0) (bondImage σ c).opposite = _
        rw [d.coarse.twistedFormValue_image_opposite _ _ hcp, extend_val_apply_of_mem hc]
      have hmem : (pivot c : Bond L m j') ∈ doubleBlockSupport j' Γ := by
        have := d.bondPreimage_mem hb'.1
        rw [hbp, l.preimage_opposite, l.preimage_image] at this
        exact opposite_mem_doubleBlockSupport this
      have hm' : pivotCoeff (transportGaugeField σ V) (bondImage σ c).opposite
          (-ComplexMatrix2.conjugateBy (V (pivot c))⁻¹ (pivotCoeffInv V c (ν ⟨c, hc⟩))) =
          -ComplexMatrix2.conjugateBy (W c)⁻¹ (ν ⟨c, hc⟩) := by
        rw [neg_conjugationLinearMap_apply, neg_conjugationLinearMap_apply, hYν] at hm
        exact hm
      have hXm : -ComplexMatrix2.conjugateBy (V (pivot c))⁻¹ (pivotCoeffInv V c (ν ⟨c, hc⟩)) ∈
          ComplexMatrix2.traceless := Submodule.neg_mem _ (conjugateBy_mem _ _ hX)
      rw [hrho, pivotCoeffInv_eq (d.invertible' _ hc') hXm hm', hbp,
        l.twistedFormValue_image_opposite _ _ hpc, extendForm_of_mem _ ⟨hmem, hpc⟩,
        pivotCorrectionLift_at_pivot d.pivot_injective hc, conjugateBy_smul, smul_neg]
  · rw [pivotCorrectionLift_off_pivot ⟨b', hb'⟩ h]
    have hib : bondImage σ (bondPreimage σ b') = b' := l.image_preimage b'
    have key : ∀ q : Bond L m j', q.IsPositivelyOriented →
        (bondImage σ q = b' ∨ bondImage σ q = b'.opposite) →
        extendForm (pivotCorrectionLift V Γ ν) q = 0 := by
      intro q hq hi
      by_cases hXq : q ∈ doubleBlockSupport j' Γ
      · rw [extendForm_of_mem _ ⟨hXq, hq⟩]
        refine pivotCorrectionLift_off_pivot _ ?_ ν
        rintro ⟨⟨c, hc⟩, hqc⟩
        replace hqc : q = pivot c := hqc
        subst hqc
        apply h
        obtain ⟨c', hc', hr⟩ := d.exists_positiveImage hc
        refine ⟨⟨c', hc'⟩, ?_⟩
        show b' = pivot c'
        rcases hi with hi | hi
        · rw [d.pivot_image] at hi
          rcases hr.2 with e | e
          · rw [e, hi]
          · exfalso
            have h₁ : ¬ (bondImage σ c).IsPositivelyOriented := by
              rw [e] at hr
              exact d.coarse.not_pos_opposite hr.1
            exact h₁ ((d.pivot_positive _).1 (hi ▸ hb'.2))
        · rw [d.pivot_image] at hi
          rcases hr.2 with e | e
          · exfalso
            have h₁ : (bondImage σ c).IsPositivelyOriented := e ▸ hr.1
            exact l.not_pos_opposite hb'.2 (hi ▸ (d.pivot_positive _).2 h₁)
          · rw [e, d.pivot_opposite, hi]
            rfl
      · exact extendForm_of_not_mem l _ hq hXq
    show (0 : ComplexMatrix2) = twistedFormValue σ V (extendForm (pivotCorrectionLift V Γ ν)) b'
    unfold twistedFormValue
    split_ifs with hp
    · rw [key _ hp (Or.inl hib)]
    · rw [key _ (l.pos_opposite hp) (Or.inr (by rw [l.image_opposite, hib])), conjugateBy_zero,
        neg_zero]
end TransportData
theorem conjugateBy_neg (X A : ComplexMatrix2) :
    ComplexMatrix2.conjugateBy X (-A) = -ComplexMatrix2.conjugateBy X A := by
  simp only [ComplexMatrix2.conjugateBy, mul_neg, neg_mul]
def fineTransport (σ : FourTorus L m ≃ FourTorus L m) (V : Bond L m j' → ComplexMatrix2)
    (Γ Γ' : Set (Bond L m j)) :
    (SupportBond j' Γ → ComplexMatrix2) →ₗ[ℂ] (SupportBond j' Γ' → ComplexMatrix2) where
  toFun B b' := twistedTransportForm σ V (extendForm B) b'
  map_add' B B' := by
    funext b'
    simp only [extendForm_add, twistedTransportForm_add, Pi.add_apply]
  map_smul' z B := by
    funext b'
    simp only [extendForm_smul, twistedTransportForm_smul, Pi.smul_apply, RingHom.id_apply]
def fineTransportInv (σ : FourTorus L m ≃ FourTorus L m) (V : Bond L m j' → ComplexMatrix2)
    (Γ Γ' : Set (Bond L m j)) :
    (SupportBond j' Γ' → ComplexMatrix2) →ₗ[ℂ] (SupportBond j' Γ → ComplexMatrix2) where
  toFun B' b :=
    open Classical in
    if (bondImage σ (b : Bond L m j')).IsPositivelyOriented then extendForm B' (bondImage σ b)
    else -ComplexMatrix2.conjugateBy (V b) (extendForm B' (bondImage σ b).opposite)
  map_add' B B' := by
    funext b
    simp only [extendForm_add, Pi.add_apply]
    split_ifs
    · rfl
    · rw [conjugateBy_add, neg_add]
  map_smul' z B := by
    funext b
    simp only [extendForm_smul, Pi.smul_apply, RingHom.id_apply]
    split_ifs
    · rfl
    · rw [conjugateBy_smul, smul_neg]
theorem fineTransportInv_of_pos (σ : FourTorus L m ≃ FourTorus L m)
    (V : Bond L m j' → ComplexMatrix2) (Γ Γ' : Set (Bond L m j))
    (B' : SupportBond j' Γ' → ComplexMatrix2) (b : SupportBond j' Γ)
    (h : (bondImage σ (b : Bond L m j')).IsPositivelyOriented) :
    fineTransportInv σ V Γ Γ' B' b = extendForm B' (bondImage σ b) :=
  if_pos h
theorem fineTransportInv_of_not_pos (σ : FourTorus L m ≃ FourTorus L m)
    (V : Bond L m j' → ComplexMatrix2) (Γ Γ' : Set (Bond L m j))
    (B' : SupportBond j' Γ' → ComplexMatrix2) (b : SupportBond j' Γ)
    (h : ¬ (bondImage σ (b : Bond L m j')).IsPositivelyOriented) :
    fineTransportInv σ V Γ Γ' B' b =
      -ComplexMatrix2.conjugateBy (V b) (extendForm B' (bondImage σ b).opposite) :=
  if_neg h
namespace TransportData
variable {σ : FourTorus L m ≃ FourTorus L m} {V : Bond L m j' → ComplexMatrix2}
  {W : Bond L m j → ComplexMatrix2} {Γ Γ' : Set (Bond L m j)}
theorem fineTransport_fineTransportInv (d : TransportData σ V W Γ Γ')
    (B' : SupportBond j' Γ' → ComplexMatrix2) :
    fineTransport σ V Γ Γ' (fineTransportInv σ V Γ Γ' B') = B' := by
  have l := d.fine
  funext ⟨b', hb'⟩
  show twistedTransportForm σ V (extendForm (fineTransportInv σ V Γ Γ' B')) b' = B' ⟨b', hb'⟩
  rw [twistedTransportForm_of_pos σ V _ hb'.2]
  have hp' := d.bondPreimage_mem hb'.1
  have hib := l.image_preimage b'
  by_cases hp : (bondPreimage σ b').IsPositivelyOriented
  · have e : twistedFormValue σ V (extendForm (fineTransportInv σ V Γ Γ' B')) b' =
        extendForm (fineTransportInv σ V Γ Γ' B') (bondPreimage σ b') := if_pos hp
    rw [e, extendForm_of_mem _ ⟨hp', hp⟩,
      fineTransportInv_of_pos σ V Γ Γ' B' ⟨_, hp', hp⟩ (by
        show (bondImage σ _).IsPositivelyOriented
        rw [hib]
        exact hb'.2)]
    show extendForm B' (bondImage σ (bondPreimage σ b')) = _
    rw [hib, extendForm_of_mem _ hb']
  · have e : twistedFormValue σ V (extendForm (fineTransportInv σ V Γ Γ' B')) b' =
        -ComplexMatrix2.conjugateBy (V (bondPreimage σ b').opposite)⁻¹
          (extendForm (fineTransportInv σ V Γ Γ' B') (bondPreimage σ b').opposite) := if_neg hp
    have hq := l.pos_opposite hp
    have hqm := opposite_mem_doubleBlockSupport hp'
    have hiq : bondImage σ (bondPreimage σ b').opposite = b'.opposite := by
      rw [l.image_opposite, hib]
    rw [e, extendForm_of_mem _ ⟨hqm, hq⟩,
      fineTransportInv_of_not_pos σ V Γ Γ' B' ⟨_, hqm, hq⟩ (by
        show ¬ (bondImage σ _).IsPositivelyOriented
        rw [hiq]
        exact l.not_pos_opposite hb'.2)]
    show -ComplexMatrix2.conjugateBy (V (bondPreimage σ b').opposite)⁻¹
      (-ComplexMatrix2.conjugateBy (V (bondPreimage σ b').opposite)
        (extendForm B' (bondImage σ (bondPreimage σ b').opposite).opposite)) = _
    rw [hiq, opposite_opposite, extendForm_of_mem _ hb', conjugateBy_neg, neg_neg,
      conjugateBy_inv_conjugateBy (d.isUnit_det hqm)]
theorem fineTransportInv_fineTransport (d : TransportData σ V W Γ Γ')
    (B : SupportBond j' Γ → ComplexMatrix2) :
    fineTransportInv σ V Γ Γ' (fineTransport σ V Γ Γ' B) = B := by
  have l := d.fine
  funext ⟨b, hb⟩
  by_cases hi : (bondImage σ b).IsPositivelyOriented
  · rw [fineTransportInv_of_pos σ V Γ Γ' _ ⟨b, hb⟩ hi]
    show extendForm _ (bondImage σ b) = _
    rw [extendForm_of_mem _ ⟨d.bondImage_mem hb.1, hi⟩]
    show twistedTransportForm σ V (extendForm B) (bondImage σ b) = _
    rw [twistedTransportForm_of_pos σ V _ hi, l.twistedFormValue_image _ _ hb.2,
      extendForm_of_mem _ hb]
  · rw [fineTransportInv_of_not_pos σ V Γ Γ' _ ⟨b, hb⟩ hi]
    show -ComplexMatrix2.conjugateBy (V b) (extendForm _ (bondImage σ b).opposite) = _
    have hr := l.pos_opposite hi
    rw [extendForm_of_mem _ ⟨opposite_mem_doubleBlockSupport (d.bondImage_mem hb.1), hr⟩]
    show -ComplexMatrix2.conjugateBy (V b)
      (twistedTransportForm σ V (extendForm B) (bondImage σ b).opposite) = _
    rw [twistedTransportForm_of_pos σ V _ hr, l.twistedFormValue_image_opposite _ _ hb.2,
      extendForm_of_mem _ hb, conjugateBy_neg, neg_neg,
      conjugateBy_conjugateBy_inv (d.isUnit_det hb.1)]
theorem extendForm_fineTransport (d : TransportData σ V W Γ Γ')
    (B : SupportBond j' Γ → ComplexMatrix2) :
    extendForm (fineTransport σ V Γ Γ' B) = twistedTransportForm σ V (extendForm B) := by
  have l := d.fine
  have key : ∀ b' : Bond L m j', b'.IsPositivelyOriented →
      extendForm (fineTransport σ V Γ Γ' B) b' =
        twistedTransportForm σ V (extendForm B) b' := by
    intro b' hp
    by_cases hb : b' ∈ doubleBlockSupport j' Γ'
    · rw [extendForm_of_mem _ ⟨hb, hp⟩]
      rfl
    · rw [extendForm_of_not_mem l _ hp hb, twistedTransportForm_of_pos σ V _ hp]
      have hq : bondPreimage σ b' ∉ doubleBlockSupport j' Γ := fun h =>
        hb (by simpa only [l.image_preimage] using d.bondImage_mem h)
      symm
      unfold twistedFormValue
      split_ifs with h
      · exact extendForm_of_not_mem l _ h hq
      · rw [extendForm_of_not_mem l _ (l.pos_opposite h)
          (fun h' => hq (opposite_mem_doubleBlockSupport h')), conjugateBy_zero, neg_zero]
  funext b'
  by_cases hp : b'.IsPositivelyOriented
  · exact key b' hp
  · have e₁ := key b'.opposite (l.pos_opposite hp)
    have e₂ := extendForm_opposite l (fineTransport σ V Γ Γ' B) b'
    have e₃ : twistedTransportForm σ V (extendForm B) b' =
        -twistedFormValue σ V (extendForm B) b'.opposite := if_neg hp
    rw [twistedTransportForm_of_pos σ V _ (l.pos_opposite hp)] at e₁
    rw [e₃, ← e₁, e₂, neg_neg]
theorem fineTransport_mem (d : TransportData σ V W Γ Γ') {B : SupportBond j' Γ → ComplexMatrix2}
    (hB : B ∈ GroupLieProduct.tracelessPi (SupportBond j' Γ)) :
    fineTransport σ V Γ Γ' B ∈ GroupLieProduct.tracelessPi (SupportBond j' Γ') :=
  fun b' => (d.fine.twistedTransportForm_isBondForm V (extendForm_isBondForm d.fine hB)).1 _ b'.2.2
theorem fineTransportInv_mem (d : TransportData σ V W Γ Γ')
    {B' : SupportBond j' Γ' → ComplexMatrix2}
    (hB : B' ∈ GroupLieProduct.tracelessPi (SupportBond j' Γ')) :
    fineTransportInv σ V Γ Γ' B' ∈ GroupLieProduct.tracelessPi (SupportBond j' Γ) := by
  intro b
  have h₁ := extendForm_isBondForm d.fine hB
  show fineTransportInv σ V Γ Γ' B' b ∈ (ComplexMatrix2.traceless : Set ComplexMatrix2)
  by_cases hi : (bondImage σ (b : Bond L m j')).IsPositivelyOriented
  · rw [fineTransportInv_of_pos σ V Γ Γ' B' b hi]
    exact h₁.1 _ hi
  · rw [fineTransportInv_of_not_pos σ V Γ Γ' B' b hi]
    exact Submodule.neg_mem _ (conjugateBy_mem _ _ (h₁.1 _ (d.fine.pos_opposite hi)))
end TransportData
theorem mem_nhdsWithin_of_isSupOpen (hX : GroupLieProduct.ExpChartHolomorphy.ExpChartTheory)
    {α : Type} [Fintype α] {N : Set (α → ComplexMatrix2)} (hN : GroupLieProduct.IsSupOpen N)
    (h0 : (0 : α → ComplexMatrix2) ∈ N) :
    N ∈ 𝓝[GroupLieProduct.tracelessPi α] (0 : α → ComplexMatrix2) := by
  obtain ⟨O, hO, rfl⟩ := (((hX.2.1 α).1 N hN.1).1).1 hN
  exact mem_nhdsWithin.2 ⟨O, hO, h0.1, subset_rfl⟩
theorem isSupOpen_inter (hX : GroupLieProduct.ExpChartHolomorphy.ExpChartTheory)
    {α : Type} [Fintype α] {O : Set (α → ComplexMatrix2)} (hO : IsOpen O) :
    GroupLieProduct.IsSupOpen (O ∩ GroupLieProduct.tracelessPi α) :=
  (((hX.2.1 α).1 _ inter_subset_right).1).2 ⟨O, hO, rfl⟩
theorem linearMap_tendsto_nhdsWithin_zero {α β : Type} [Finite α] [Finite β]
    (T : (α → ComplexMatrix2) →ₗ[ℂ] (β → ComplexMatrix2)) {s : Set (α → ComplexMatrix2)}
    {t : Set (β → ComplexMatrix2)} (h : MapsTo T s t) : Tendsto T (𝓝[s] 0) (𝓝[t] 0) := by
  have hc : Continuous T := LinearMap.continuous_of_finiteDimensional T
  refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
  · exact (hc.tendsto' 0 0 (map_zero T)).mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with x hx using h hx
namespace TransportData
variable {σ : FourTorus L m ≃ FourTorus L m} {V : Bond L m j' → ComplexMatrix2}
  {W : Bond L m j → ComplexMatrix2} {Γ Γ' : Set (Bond L m j)}
theorem linearizingCorrection_transport (d : TransportData σ V W Γ Γ')
    (hH : GroupLieProduct.HolomorphicLinearComp)
    (hX : GroupLieProduct.ExpChartHolomorphy.ExpChartTheory)
    (fF' : Fintype (SupportBond j' Γ')) (fΓ' : Fintype ↥Γ')
    (hF : ∀ c' : ↥Γ', ∀ᶠ B in
      𝓝[GroupLieProduct.tracelessPi (SupportBond j' Γ')] (0 : SupportBond j' Γ' → ComplexMatrix2),
      ConstraintMapDefined (transportGaugeField σ V) (extendForm B) (c' : Bond L m j))
    {N : Set (SupportBond j' Γ → ComplexMatrix2)}
    {D : (SupportBond j' Γ → ComplexMatrix2) → ↥Γ → ComplexMatrix2}
    (hND : IsLinearizingCorrection V Γ N D) :
    ∃ N', IsLinearizingCorrection (transportGaugeField σ V) Γ' N'
      fun B' => coarseTransport σ W Γ Γ' (D (fineTransportInv σ V Γ Γ' B')) := by
  obtain ⟨h0, ⟨fF, fΓ, hD⟩, hval, hD0, hmain⟩ := hND
  have l := d.fine
  have hNopen : GroupLieProduct.IsSupOpen N :=
    (hD OneLoop.pauliBasis (Fintype.equivFin ↥Γ)).1
  have hNmem := mem_nhdsWithin_of_isSupOpen hX hNopen h0
  have hDc : ContinuousOn D N :=
    (hH _ _ OneLoop.pauliBasis N D (hD OneLoop.pauliBasis)).1
  have tS := linearMap_tendsto_nhdsWithin_zero (fineTransportInv σ V Γ Γ')
    (fun _ h => d.fineTransportInv_mem h)
  have tT := linearMap_tendsto_nhdsWithin_zero (fineTransport σ V Γ Γ')
    (fun _ h => d.fineTransport_mem h)
  have tD : Tendsto D (𝓝[GroupLieProduct.tracelessPi (SupportBond j' Γ)] 0)
      (𝓝[GroupLieProduct.tracelessPi ↥Γ] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have := (hDc 0 h0).tendsto
      rw [hD0] at this
      exact this.mono_left (nhdsWithin_le_of_mem hNmem)
    · filter_upwards [hNmem] with B hB using hval B hB
  have tG : Tendsto (fun B => B - pivotCorrectionLift V Γ (D B))
      (𝓝[GroupLieProduct.tracelessPi (SupportBond j' Γ)] 0)
      (𝓝[GroupLieProduct.tracelessPi (SupportBond j' Γ)] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have h₁ : Tendsto (fun B : SupportBond j' Γ → ComplexMatrix2 => B)
          (𝓝[GroupLieProduct.tracelessPi (SupportBond j' Γ)] 0) (𝓝 0) := nhdsWithin_le_nhds
      have h₂ := h₁.sub ((pivotCorrectionLift_tendsto d.invertible).comp tD)
      simpa only [sub_zero, Function.comp_def] using h₂
    · filter_upwards [hNmem, self_mem_nhdsWithin] with B hB hB' b
      exact Submodule.sub_mem _ (hB' b) (pivotCorrectionLift_mem d.invertible (hval B hB) b)
  have hform := (tT.comp (tG.comp tS)).eventually (eventually_all.2 hF)
  obtain ⟨O, hO, h0O, hsub⟩ :=
    mem_nhdsWithin.1 (hform.and (tS.eventually (eventually_mem_set.2 hNmem)))
  have h0a : (0 : SupportBond j' Γ' → ComplexMatrix2) ∈
      GroupLieProduct.tracelessPi (SupportBond j' Γ') :=
    fun _ => Submodule.zero_mem _
  refine ⟨O ∩ GroupLieProduct.tracelessPi (SupportBond j' Γ'), ⟨h0O, h0a⟩,
    ⟨fF', fΓ', fun b ν => ?_⟩, fun B' hB' => d.coarseTransport_mem (hval _ (hsub hB').2), ?_,
    fun B' hB' c' => ?_⟩
  · exact (hH _ _ b N D (hD b)).2 _ _ (fineTransportInv σ V Γ Γ') (coarseTransport σ W Γ Γ') _
      (isSupOpen_inter hX hO) (fun _ h => d.fineTransportInv_mem h) (fun _ h => (hsub h).2) ν
  · show coarseTransport σ W Γ Γ' (D (fineTransportInv σ V Γ Γ' 0)) = 0
    rw [map_zero, hD0, map_zero]
  · obtain ⟨hform', hBN⟩ := hsub hB'
    have e₁ := d.fineTransport_fineTransportInv B'
    set B := fineTransportInv σ V Γ Γ' B' with hBdef
    have hBa : B ∈ GroupLieProduct.tracelessPi (SupportBond j' Γ) := hNopen.1 hBN
    have hG : B - pivotCorrectionLift V Γ (D B) ∈ GroupLieProduct.tracelessPi (SupportBond j' Γ) :=
      fun b => Submodule.sub_mem _ (hBa b) (pivotCorrectionLift_mem d.invertible (hval B hBN) b)
    have e₂ : B' - pivotCorrectionLift (transportGaugeField σ V) Γ' (coarseTransport σ W Γ Γ' (D B)) =
        fineTransport σ V Γ Γ' (B - pivotCorrectionLift V Γ (D B)) := by
      rw [d.pivotCorrectionLift_transport (hval B hBN), map_sub, e₁]
      rfl
    have hfc := hform' c'
    simp only [Function.comp_def] at hfc
    rw [e₂]
    refine ⟨hfc, ?_⟩
    obtain ⟨c, hc, hr⟩ := (d.mem_image c').1 c'.2
    obtain ⟨m₁, m₂⟩ := hmain B hBN ⟨c, hc⟩
    rw [d.extendForm_fineTransport] at hfc ⊢
    rw [d.constraint_map c hc c' hr _ (extendForm_isBondForm l hG) m₁ hfc, ← e₁,
      d.extendForm_fineTransport, d.constraint c hc c' hr _ (extendForm_isBondForm l hBa),
      ← twistedFormValue_smul]
    exact d.coarse.twistedFormValue_congr_at W _ _ (d.positive c hc) hr.2 m₂
end TransportData
theorem bond_ext_of {b b' : Bond L m j} (ht : (b.source : FourTorus L m) = b'.source)
    (hh : (b.target : FourTorus L m) = b'.target) : b = b' :=
  Bond.ext (Subtype.ext ht) (Subtype.ext hh)
theorem LevelTransport.of_mapsCellsAndCubes {σ : FourTorus L m ≃ FourTorus L m}
    (h : MapsCellsAndCubes σ j) (h' : MapsCellsAndCubes σ.symm j)
    (hx : ∀ b : Bond L m j, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented) :
    LevelTransport σ j := by
  have it : ∀ b : Bond L m j, ((bondImage σ b).source : FourTorus L m) = σ b.source :=
    fun b => (h.2.2.2.1 b).1
  have ih : ∀ b : Bond L m j, ((bondImage σ b).target : FourTorus L m) = σ b.target :=
    fun b => (h.2.2.2.1 b).2
  have pt : ∀ b : Bond L m j, ((bondPreimage σ b).source : FourTorus L m) = σ.symm b.source :=
    fun b => (h'.2.2.2.1 b).1
  have ph : ∀ b : Bond L m j, ((bondPreimage σ b).target : FourTorus L m) = σ.symm b.target :=
    fun b => (h'.2.2.2.1 b).2
  refine ⟨fun b => ?_, fun b => ?_, fun b => ?_, fun b => ?_, hx⟩
  · exact bond_ext_of (by rw [pt, it, Equiv.symm_apply_apply])
      (by rw [ph, ih, Equiv.symm_apply_apply])
  · exact bond_ext_of (by rw [it, pt, Equiv.apply_symm_apply])
      (by rw [ih, ph, Equiv.apply_symm_apply])
  · exact bond_ext_of (by rw [it]; exact (ih b).symm) (by rw [ih]; exact (it b).symm)
  · exact bond_ext_of (by rw [pt]; exact (ph b).symm) (by rw [ph]; exact (pt b).symm)
theorem pivot_injOn_of {V : Bond L m j' → ComplexMatrix2} {Γ : Set (Bond L m j)}
    (hinv : ∀ c ∈ Γ, PivotCoeffInvertible V c)
    (h : ∀ c ∈ Γ, ∀ c'' ∈ Γ, c'' ≠ c → ∀ X ∈ complexLieAlgebra,
      linearizedConstraint V (singleBondForm (pivot c'') X) c = 0) :
    ∀ c ∈ Γ, ∀ c'' ∈ Γ, (pivot c : Bond L m j') = pivot c'' → c = c'' := by
  intro c hc c'' hc'' e
  by_contra hne
  obtain ⟨T, hT⟩ := hinv c hc
  have h0 := h c hc c'' hc'' (Ne.symm hne) _ (OneLoop.pauliBasis 0).2
  rw [← e] at h0
  have hTX : (T (OneLoop.pauliBasis 0) : ComplexMatrix2) = 0 := (hT _).trans h0
  have hz : T (OneLoop.pauliBasis 0) = 0 := Subtype.ext hTX
  exact OneLoop.pauliBasis.ne_zero 0 (T.map_eq_zero_iff.1 hz)
end ImageSetIntertwining
open ImageSetIntertwining in
theorem ImageSetIntertwining.holds
    (hO : BondOrientationDichotomy)
    (hP : PivotOfEveryBond)
    (hB : IsometryInvariance.InvariantUnderIsometries)
    (hG : LatticeIsometryGroupActionStatement)
    (hI : TransportIdentitiesAtImageBond)
    (hE : UniqueEliminationClaim)
    (hC : LinearizingCorrectionExistsAndIsLocallyUnique)
    (hF : ConstraintMapDefinedNearZero.Statement)
    (hH : GroupLieProduct.HolomorphicLinearComp)
    (hX : GroupLieProduct.ExpChartHolomorphy.ExpChartTheory) :
    ImageSetIntertwining.Statement := by
  intro L m K k i σ hL hm hi hσ hk hik V W Γ Γ' hpos hmem hf hinv hf' hinv' hW
  have hd0 : levelDepth K k = levelDepth K (k + 1) + 1 := by
    simp only [levelDepth]
    push_cast
    ring
  have hd1 : (0 : ℤ) ≤ levelDepth K (k + 1) := by
    simp only [levelDepth]
    omega
  have hG0 := hG L m i hL hm hi
  have hsymm : σ.symm ∈ latticeIsometries L m i := by
    obtain ⟨⟨H, hH'⟩, -⟩ := hG0.1
    have h1 : (σ : Equiv.Perm (FourTorus L m)) ∈ H := by
      rw [← SetLike.mem_coe, hH']
      exact hσ
    have h2 := H.inv_mem h1
    rw [← SetLike.mem_coe, hH'] at h2
    exact h2
  have car : ∀ τ ∈ latticeIsometries L m i, ∀ j : ℤ, i ≤ j → MapsCellsAndCubes τ j :=
    fun τ hτ j hj => (hG0.2.2.2.2 τ hτ j hj).1
  have lf : LevelTransport σ (levelDepth K k) :=
    LevelTransport.of_mapsCellsAndCubes (car σ hσ _ (by omega)) (car _ hsymm _ (by omega))
      (hO L m hL hm _ (by omega))
  have lc : LevelTransport σ (levelDepth K (k + 1)) :=
    LevelTransport.of_mapsCellsAndCubes (car σ hσ _ hik) (car _ hsymm _ hik)
      (hO L m hL hm _ (by omega))
  have hP' : ∀ c : BondAtLevel L m K (k + 1), PivotProperties c :=
    fun c => hP ⟨L, hL, ⟨K, by omega⟩, ⟨m, hm⟩⟩ k hk c
  have hcarry := (hB L m hL hm i hi σ hσ).2.1 K k hk hik
  have hId : ∀ c ∈ Γ, ∀ c', PositiveImage σ c c' → TransportIdentitiesAt σ V W c c' :=
    fun c hc c' hr => hI L m K k i σ hL hm hi hσ hk hik V W c c' (hpos c hc) hr.1 hr.2 (hf c hc)
      (hf' c' ((hmem c').2 ⟨c, hc, hr⟩)) (hW c hc)
  have hpos' : ∀ c' ∈ Γ', c'.IsPositivelyOriented := fun c' hc' => by
    obtain ⟨_, _, h, _⟩ := (hmem c').1 hc'
    exact h
  have hE1 := hE L m K k hL hm hk V Γ hpos hf hinv
  have hE2 := hE L m K k hL hm hk _ Γ' hpos' hf' hinv'
  have d : TransportData σ V W Γ Γ' :=
    { fine := lf
      coarse := lc
      pivot_image := fun c => (hcarry c).2.2.1
      pivot_opposite := fun c => (hP' c).pivot_opposite
      pivot_positive := fun c => (hP' c).isPositivelyOriented_iff
      double_image := fun c c' hc hr => by
        have h := (hcarry c).2.2.2
        have e1 : c.positivelyOriented = c := if_pos hc
        have e2 : (bondImage σ c).positivelyOriented = c' := by
          rcases hr.2 with e | e
          · subst e
            exact if_pos hr.1
          · subst e
            exact if_neg (lc.not_pos_opposite hr.1)
        rwa [e1, e2] at h
      positive := hpos
      mem_image := hmem
      formed := hf
      invertible := hinv
      invertible' := hinv'
      pivot_injective := pivot_injOn_of hinv hE1.1
      pivot_injective' := pivot_injOn_of hinv' hE2.1
      constraint := fun c hc c' hr A hA => (hId c hc c' hr).linearized A hA
      constraint_map := fun c hc c' hr B hB h₁ h₂ =>
        (hId c hc c' hr).constraint_map B hB h₁ h₂
      pivot_coeff := fun c hc c' hr X => (hId c hc c' hr).pivotCoeff_conj X }
  obtain ⟨⟨N₁, D₁, hND₁⟩, -⟩ := hC L m K k hL hm hk V Γ hpos hf hinv
  obtain ⟨⟨N₂, D₂, hND₂⟩, huniq⟩ := hC L m K k hL hm hk _ Γ' hpos' hf' hinv'
  obtain ⟨N, hN⟩ : ∃ N, IsLinearizingCorrection V Γ N (linearizingCorrection V Γ) :=
    Classical.epsilon_spec (p := fun D => ∃ N, IsLinearizingCorrection V Γ N D) ⟨D₁, N₁, hND₁⟩
  obtain ⟨N'', hN''⟩ : ∃ N, IsLinearizingCorrection (transportGaugeField σ V) Γ' N
      (linearizingCorrection (transportGaugeField σ V) Γ') :=
    Classical.epsilon_spec
      (p := fun D => ∃ N, IsLinearizingCorrection (transportGaugeField σ V) Γ' N D)
      ⟨D₂, N₂, hND₂⟩
  obtain ⟨fF', fΓ', -⟩ := hN''.2.1
  obtain ⟨fF, fΓ, hhol⟩ := hN.2.1
  have hFall : ∀ c' : ↥Γ', ∀ᶠ B in
      𝓝[GroupLieProduct.tracelessPi (SupportBond (levelDepth K k) Γ')]
        (0 : SupportBond (levelDepth K k) Γ' → ComplexMatrix2),
      ConstraintMapDefined (transportGaugeField σ V) (extendForm B)
        (c' : BondAtLevel L m K (k + 1)) := fun c' => by
    have h := hF L m K k hL hm hk _ Γ' c' c'.2 (hpos' _ c'.2) (hf' _ c'.2)
    rwa [supportForms_eq_tracelessPi] at h
  obtain ⟨N', hN'⟩ := d.linearizingCorrection_transport hH hX fF' fΓ' hFall hN
  have hU := huniq _ _ _ _ hN' hN''
  rw [supportForms_eq_tracelessPi] at hU
  have tT := linearMap_tendsto_nhdsWithin_zero (fineTransport σ V Γ Γ')
    (fun _ h => d.fineTransport_mem h)
  have hU' := tT.eventually hU
  have hNmem := mem_nhdsWithin_of_isSupOpen hX
    (hhol OneLoop.pauliBasis (Fintype.equivFin ↥Γ)).1 hN.1
  have hcorr : ∀ᶠ B in 𝓝[GroupLieProduct.tracelessPi (SupportBond (levelDepth K k) Γ)]
      (0 : SupportBond (levelDepth K k) Γ → ComplexMatrix2),
      linearizingCorrection (transportGaugeField σ V) Γ' (fineTransport σ V Γ Γ' B) =
        coarseTransport σ W Γ Γ' (linearizingCorrection V Γ B) ∧ B ∈ N := by
    filter_upwards [hU', hNmem] with B h₁ h₂
    refine ⟨?_, h₂⟩
    rw [← h₁]
    show coarseTransport σ W Γ Γ' (linearizingCorrection V Γ
      (fineTransportInv σ V Γ Γ' (fineTransport σ V Γ Γ' B))) = _
    rw [d.fineTransportInv_fineTransport]
  refine
    { eliminate_comm := fun A hA => d.eliminate_transport hE1.2 hE2.2 hA
      pivotLift_comm := fun ν hν => d.pivotCorrectionLift_transport hν
      correction_comm := ?_
      change_comm := ?_ }
  · rw [supportForms_eq_tracelessPi]
    exact hcorr.mono fun B h => h.1
  · rw [supportForms_eq_tracelessPi]
    refine hcorr.mono fun B h => ?_
    show fineTransport σ V Γ Γ' B - pivotCorrectionLift (transportGaugeField σ V) Γ'
      (linearizingCorrection (transportGaugeField σ V) Γ' (fineTransport σ V Γ Γ' B)) = _
    rw [h.1, d.pivotCorrectionLift_transport (hN.2.2.1 B h.2)]
    exact (map_sub (fineTransport σ V Γ Γ') B _).symm
end YangMills.Construction.PeriodicLattice
