import YangMills.Construction.Lattice.BlockPartition
import YangMills.Construction.Lattice.CovariantAdjointsBySummationByParts
import YangMills.Construction.Lattice.EliminationMapOfAFormedSet
import YangMills.Construction.Lattice.LevelBondOrientationDichotomy
import YangMills.Construction.Lattice.LinearisedConstraintAtAFormedBond
import YangMills.Construction.Lattice.PivotOfBond
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
open Matrices
namespace PeriodicLattice.EliminationConstruction
variable {L m K k : ℕ}
theorem opposite_opposite {j : ℤ} (b : Bond L m j) : b.opposite.opposite = b := by apply _root_.YangMills.SharedProofs.p1012 <;> assumption
theorem opposite_injective {j : ℤ} {b b' : Bond L m j} (h : b.opposite = b'.opposite) :
    b = b' := by
  rw [← opposite_opposite b, h, opposite_opposite]
theorem singleBondForm_self {j : ℤ} (b : Bond L m j) (X : ComplexMatrix2) :
    singleBondForm b X b = X := by
  simp [singleBondForm]
theorem singleBondForm_opposite {j : ℤ} {b : Bond L m j} (h : b ≠ b.opposite)
    (X : ComplexMatrix2) : singleBondForm b X b.opposite = -X := by
  simp [singleBondForm, h.symm]
theorem singleBondForm_of_ne {j : ℤ} {b b' : Bond L m j} (h₁ : b' ≠ b) (h₂ : b' ≠ b.opposite)
    (X : ComplexMatrix2) : singleBondForm b X b' = 0 := by
  simp [singleBondForm, h₁, h₂]
theorem isBondForm_singleBondForm {j : ℤ} {b : Bond L m j} (h : b ≠ b.opposite)
    {X : ComplexMatrix2} (hX : X ∈ complexLieAlgebra) :
    IsBondForm complexLieAlgebra (singleBondForm b X) := by
  refine ⟨fun b' _ => ?_, fun b' => ?_⟩
  · by_cases h₁ : b' = b
    · rw [h₁, singleBondForm_self]; exact hX
    · by_cases h₂ : b' = b.opposite
      · rw [h₂, singleBondForm_opposite h]; exact ComplexMatrix2.traceless.neg_mem hX
      · rw [singleBondForm_of_ne h₁ h₂]; exact ComplexMatrix2.traceless.zero_mem
  · by_cases h₁ : b' = b
    · rw [h₁, singleBondForm_opposite h, singleBondForm_self]
    · by_cases h₂ : b' = b.opposite
      · rw [h₂, opposite_opposite, singleBondForm_self, singleBondForm_opposite h, neg_neg]
      · have h₃ : b'.opposite ≠ b := fun e => h₂ (by rw [← e, opposite_opposite])
        have h₄ : b'.opposite ≠ b.opposite := fun e => h₁ (opposite_injective e)
        rw [singleBondForm_of_ne h₃ h₄, singleBondForm_of_ne h₁ h₂, neg_zero]
theorem isBondForm_zero {j : ℤ} :
    IsBondForm complexLieAlgebra (0 : Bond L m j → ComplexMatrix2) :=
  ⟨fun _ _ => ComplexMatrix2.traceless.zero_mem, fun _ => by simp⟩
theorem isPivotBondOf_opposite {j j' : ℤ} {Γ : Set (Bond L m j)} {b : Bond L m j'}
    (h : IsPivotBondOf Γ b) : IsPivotBondOf Γ b.opposite := by
  obtain ⟨c, hc, e | e⟩ := h
  · exact ⟨c, hc, Or.inr (by rw [e])⟩
  · exact ⟨c, hc, Or.inl (by rw [e, opposite_opposite])⟩
theorem not_isPivotBondOf_opposite {j j' : ℤ} {Γ : Set (Bond L m j)} {b : Bond L m j'}
    (h : ¬ IsPivotBondOf Γ b) : ¬ IsPivotBondOf Γ b.opposite := fun h' =>
  h (by simpa only [opposite_opposite] using isPivotBondOf_opposite h')
theorem site_eq_of_mem_unitBlock {j : ℤ}
    (hd : Pairwise (Function.onFun Disjoint fun y : Site L m j => refinedBlock 1 y))
    {y y' : Site L m j} {z : FourTorus L m} (h : z ∈ unitBlock y) (h' : z ∈ unitBlock y') :
    y = y' := by
  by_contra hne
  exact Set.disjoint_left.1 (hd hne) h h'
theorem source_ne_target {j : ℤ} {b : Bond L m j}
    (hx : Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented) :
    b.source ≠ b.target := by
  intro e
  have hr : b.opposite = b := Bond.ext e.symm e
  rw [hr] at hx
  rcases hx with h | h <;> exact h.2 h.1
theorem ne_opposite {j : ℤ} {b : Bond L m j}
    (hx : Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented) :
    b ≠ b.opposite := fun e => source_ne_target hx (congrArg Bond.source e)
theorem pivot_not_mem_bondsInDoubleBlock
    (hd : Pairwise (Function.onFun Disjoint
      fun y : SiteAtLevel L m K (k + 1) => refinedBlock 1 y))
    (hx : ∀ b : BondAtLevel L m K (k + 1),
      Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    (hp : ∀ c : BondAtLevel L m K (k + 1), PivotProperties (i := k) c)
    {c c'' : BondAtLevel L m K (k + 1)} (hc : c.IsPositivelyOriented)
    (hc'' : c''.IsPositivelyOriented) (hne : c'' ≠ c) :
    (pivot c'' : BondAtLevel L m K k) ∉
      (bondsInDoubleBlock c : Set (BondAtLevel L m K k)) := by
  rintro ⟨ht, hh⟩
  obtain ⟨hct, hch⟩ := (hp c'').isPivot.1
  have hT : c''.source = c.source ∨ c''.source = c.target := by
    rcases ht with h | h
    · exact Or.inl (site_eq_of_mem_unitBlock hd hct h)
    · exact Or.inr (site_eq_of_mem_unitBlock hd hct h)
  have hH : c''.target = c.source ∨ c''.target = c.target := by
    rcases hh with h | h
    · exact Or.inl (site_eq_of_mem_unitBlock hd hch h)
    · exact Or.inr (site_eq_of_mem_unitBlock hd hch h)
  have hth := source_ne_target (hx c'')
  rcases hT with hT | hT <;> rcases hH with hH | hH
  · exact hth (hT.trans hH.symm)
  · exact hne (Bond.ext hT hH)
  · have e : c'' = c.opposite := Bond.ext hT hH
    rw [e] at hc''
    rcases hx c with h | h
    · exact h.2 hc''
    · exact h.2 hc
  · exact hth (hT.trans hH.symm)
theorem isBondForm_of_pivotValues {Γ : Set (BondAtLevel L m K (k + 1))}
    {A B : BondAtLevel L m K k → ComplexMatrix2} (hA : IsBondForm complexLieAlgebra A)
    (h₁ : ∀ b, ¬ IsPivotBondOf Γ b → B b = A b)
    (h₂ : ∀ c ∈ Γ, B (pivot c) ∈ ComplexMatrix2.traceless ∧
      B (pivot c).opposite = -B (pivot c)) :
    IsBondForm complexLieAlgebra B := by
  refine ⟨fun b hb => ?_, fun b => ?_⟩
  · by_cases h : IsPivotBondOf Γ b
    · obtain ⟨c, hc, e | e⟩ := h
      · rw [e]; exact (h₂ c hc).1
      · rw [e, (h₂ c hc).2]; exact ComplexMatrix2.traceless.neg_mem (h₂ c hc).1
    · rw [h₁ b h]; exact hA.1 b hb
  · by_cases h : IsPivotBondOf Γ b
    · obtain ⟨c, hc, e | e⟩ := h
      · rw [e]; exact (h₂ c hc).2
      · rw [e, opposite_opposite, (h₂ c hc).2, neg_neg]
    · rw [h₁ b h, h₁ _ (not_isPivotBondOf_opposite h), hA.2 b]
theorem linearizedConstraint_eq_add {V : BondAtLevel L m K k → ComplexMatrix2}
    {Γ : Set (BondAtLevel L m K (k + 1))} {c : BondAtLevel L m K (k + 1)}
    (hx : ∀ b : BondAtLevel L m K k, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    (hnot : ∀ c'' ∈ Γ, c'' ≠ c →
      (pivot c'' : BondAtLevel L m K k) ∉ (bondsInDoubleBlock c : Set (BondAtLevel L m K k)))
    (H : LinearizedConstraintProperties V c)
    {E F : BondAtLevel L m K k → ComplexMatrix2} (hE : IsBondForm complexLieAlgebra E)
    (hF : IsBondForm complexLieAlgebra F) (hoff : ∀ b, ¬ IsPivotBondOf Γ b → E b = F b)
    {y : ComplexMatrix2} (hy : y ∈ complexLieAlgebra)
    (h₁ : E (pivot c) = F (pivot c) + y)
    (h₂ : E (pivot c).opposite = F (pivot c).opposite - y) :
    linearizedConstraint V E c = linearizedConstraint V F c + pivotCoeff V c y := by
  have hne : (pivot c : BondAtLevel L m K k) ≠ (pivot c : BondAtLevel L m K k).opposite :=
    ne_opposite (hx _)
  have hf := isBondForm_singleBondForm hne hy
  have hsum : IsBondForm complexLieAlgebra (F + singleBondForm (pivot c) y) := by
    refine ⟨fun b hb => ComplexMatrix2.traceless.add_mem (hF.1 b hb) (hf.1 b hb), fun b => ?_⟩
    rw [Pi.add_apply, Pi.add_apply, hF.2 b, hf.2 b, neg_add]
  refine (H.eq_of_eqOn_doubleBlock E _ hE hsum fun b hb => ?_).trans (H.map_add F _ hF hf)
  by_cases e₁ : b = pivot c
  · rw [e₁, Pi.add_apply, singleBondForm_self, h₁]
  · by_cases e₂ : b = (pivot c : BondAtLevel L m K k).opposite
    · rw [e₂, Pi.add_apply, singleBondForm_opposite hne, h₂, sub_eq_add_neg]
    · rw [Pi.add_apply, singleBondForm_of_ne e₁ e₂, add_zero]
      by_cases hpv : IsPivotBondOf Γ b
      · exfalso
        obtain ⟨c'', hc'', e | e⟩ := hpv
        · have hcc : c'' ≠ c := fun e' => e₁ (by rw [e, e'])
          exact hnot c'' hc'' hcc (e ▸ hb)
        · have hcc : c'' ≠ c := fun e' => e₂ (by rw [e, e'])
          rw [e] at hb
          exact hnot c'' hc'' hcc ⟨hb.2, hb.1⟩
      · exact hoff b hpv
def withPivotValues (Γ : Set (BondAtLevel L m K (k + 1)))
    (x : BondAtLevel L m K (k + 1) → ComplexMatrix2)
    (A : BondAtLevel L m K k → ComplexMatrix2) : BondAtLevel L m K k → ComplexMatrix2 :=
  open Classical in
  fun b => if h : ∃ c ∈ Γ, b = pivot c then x h.choose
    else if h' : ∃ c ∈ Γ, b = (pivot c : BondAtLevel L m K k).opposite then -x h'.choose
    else A b
def offPivots (Γ : Set (BondAtLevel L m K (k + 1))) (A : BondAtLevel L m K k → ComplexMatrix2) :
    BondAtLevel L m K k → ComplexMatrix2 :=
  open Classical in
  fun b => if IsPivotBondOf Γ b then 0 else A b
theorem isBondForm_offPivots {Γ : Set (BondAtLevel L m K (k + 1))}
    {A : BondAtLevel L m K k → ComplexMatrix2}
    (hA : IsBondForm complexLieAlgebra A) : IsBondForm complexLieAlgebra (offPivots Γ A) := by
  refine ⟨fun b hb => ?_, fun b => ?_⟩
  · by_cases h : IsPivotBondOf Γ b
    · simp only [offPivots, if_pos h]; exact ComplexMatrix2.traceless.zero_mem
    · simp only [offPivots, if_neg h]; exact hA.1 b hb
  · by_cases h : IsPivotBondOf Γ b
    · simp only [offPivots, if_pos h, if_pos (isPivotBondOf_opposite h), neg_zero]
    · simp only [offPivots, if_neg h, if_neg (not_isPivotBondOf_opposite h)]; exact hA.2 b
theorem offPivots_of_isPivotBondOf {Γ : Set (BondAtLevel L m K (k + 1))}
    {A : BondAtLevel L m K k → ComplexMatrix2}
    {b : BondAtLevel L m K k} (h : IsPivotBondOf Γ b) : offPivots Γ A b = 0 := by
  simp only [offPivots, if_pos h]
theorem offPivots_of_not_isPivotBondOf {Γ : Set (BondAtLevel L m K (k + 1))}
    {A : BondAtLevel L m K k → ComplexMatrix2}
    {b : BondAtLevel L m K k} (h : ¬ IsPivotBondOf Γ b) : offPivots Γ A b = A b := by
  simp only [offPivots, if_neg h]
theorem uniqueEliminationClaim (h₁ : LinearizedConstraintAtBond.Statement)
    (h₂ : BlockPartition.Properties)
    (h₃ : PivotOfEveryBond)
    (h₄ : LevelBondOrientationDichotomy) :
    UniqueEliminationClaim := by
  intro L m K k hL hm hk V Γ hpos hform hinv
  have hdepth : -(m : ℤ) ≤ levelDepth K (k + 1) := by
    simp only [levelDepth]; omega
  obtain ⟨-, ⟨-, -, hd, -⟩, -⟩ := h₂ L m hL hm (levelDepth K (k + 1)) 1 0 hdepth
  have hx1 : ∀ b : BondAtLevel L m K (k + 1),
      Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented :=
    h₄ L m K hL hm (by omega) (k + 1) (by omega)
  have hx0 : ∀ b : BondAtLevel L m K k,
      Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented :=
    h₄ L m K hL hm (by omega) k (by omega)
  have hp : ∀ c : BondAtLevel L m K (k + 1), PivotProperties (i := k) c := fun c =>
    h₃ ⟨L, hL, ⟨K, by omega⟩, ⟨m, hm⟩⟩ k hk c
  have hH : ∀ c ∈ Γ, LinearizedConstraintProperties V c := fun c hc =>
    h₁ L m K k hL hm hk V c (hpos c hc) (hform c hc)
  have hnot : ∀ c ∈ Γ, ∀ c'' ∈ Γ, c'' ≠ c →
      (pivot c'' : BondAtLevel L m K k) ∉ (bondsInDoubleBlock c : Set (BondAtLevel L m K k)) :=
    fun c hc c'' hc'' hne =>
      pivot_not_mem_bondsInDoubleBlock hd hx1 hp (hpos c hc) (hpos c'' hc'') hne
  have hin : ∀ c : BondAtLevel L m K (k + 1),
      (pivot c : BondAtLevel L m K k) ∈ (bondsInDoubleBlock c : Set (BondAtLevel L m K k)) :=
    fun c => ⟨Or.inl (hp c).isPivot.1.1, Or.inr (hp c).isPivot.1.2⟩
  have hinj : ∀ c ∈ Γ, ∀ c' ∈ Γ,
      (pivot c : BondAtLevel L m K k) = pivot c' → c = c' := by
    intro c hc c' hc' e
    by_contra hne
    exact hnot c' hc' c hc hne (e ▸ hin c')
  refine ⟨?_, fun A hA => ?_⟩
  · intro c hc c'' hc'' hne X hX
    have hf := isBondForm_singleBondForm (ne_opposite (hx0 (pivot c''))) hX
    have h0 : linearizedConstraint V (0 : BondAtLevel L m K k → ComplexMatrix2) c = 0 := by
      have h := (hH c hc).map_smul 0 0 isBondForm_zero
      simpa using h
    rw [← h0]
    refine (hH c hc).eq_of_eqOn_doubleBlock _ _ hf isBondForm_zero fun b hb => ?_
    rw [Pi.zero_apply]
    refine singleBondForm_of_ne ?_ ?_ X
    · rintro rfl
      exact hnot c hc c'' hc'' hne hb
    · rintro rfl
      exact hnot c hc c'' hc'' hne ⟨hb.2, hb.1⟩
  · have hA₀ := isBondForm_offPivots (Γ := Γ) hA
    have hsolve : ∀ c ∈ Γ, ∃ x, x ∈ complexLieAlgebra ∧
        pivotCoeff V c x = -linearizedConstraint V (offPivots Γ A) c := by
      intro c hc
      obtain ⟨T, hT⟩ := hinv c hc
      have hq : -linearizedConstraint V (offPivots Γ A) c ∈ ComplexMatrix2.traceless :=
        ComplexMatrix2.traceless.neg_mem ((hH c hc).mem_complexLieAlgebra _ hA₀)
      refine ⟨(T.symm ⟨_, hq⟩ : ComplexMatrix2.traceless), (T.symm ⟨_, hq⟩).2, ?_⟩
      rw [← hT]
      simp
    choose! x hxm hxe using hsolve
    have hBp : ∀ c ∈ Γ, withPivotValues Γ x A (pivot c) = x c := by
      intro c hc
      have h : ∃ c' ∈ Γ, (pivot c : BondAtLevel L m K k) = pivot c' := ⟨c, hc, rfl⟩
      have e := hinj c hc _ h.choose_spec.1 h.choose_spec.2
      have h' : withPivotValues Γ x A (pivot c) = x h.choose := dif_pos h
      rw [h', ← e]
    have hBr : ∀ c ∈ Γ, withPivotValues Γ x A (pivot c).opposite = -x c := by
      intro c hc
      have hn : ¬ ∃ c' ∈ Γ, (pivot c : BondAtLevel L m K k).opposite = pivot c' := by
        rintro ⟨c', hc', e⟩
        have p₁ : (pivot c : BondAtLevel L m K k).IsPositivelyOriented :=
          (hp c).isPositivelyOriented_iff.2 (hpos c hc)
        have p₂ : (pivot c : BondAtLevel L m K k).opposite.IsPositivelyOriented :=
          e ▸ (hp c').isPositivelyOriented_iff.2 (hpos c' hc')
        rcases hx0 (pivot c) with h | h
        · exact h.2 p₂
        · exact h.2 p₁
      have h : ∃ c' ∈ Γ, (pivot c : BondAtLevel L m K k).opposite =
          (pivot c' : BondAtLevel L m K k).opposite := ⟨c, hc, rfl⟩
      have e := hinj c hc _ h.choose_spec.1 (opposite_injective h.choose_spec.2)
      have h' : withPivotValues Γ x A (pivot c).opposite = -x h.choose :=
        (dif_neg hn).trans (dif_pos h)
      rw [h', ← e]
    have hBo : ∀ b, ¬ IsPivotBondOf Γ b → withPivotValues Γ x A b = A b := by
      intro b hb
      have n₁ : ¬ ∃ c ∈ Γ, b = pivot c := fun ⟨c, hc, e⟩ => hb ⟨c, hc, Or.inl e⟩
      have n₂ : ¬ ∃ c ∈ Γ, b = (pivot c : BondAtLevel L m K k).opposite :=
        fun ⟨c, hc, e⟩ => hb ⟨c, hc, Or.inr e⟩
      exact (dif_neg n₁).trans (dif_neg n₂)
    have hBs : ∀ c ∈ Γ, withPivotValues Γ x A (pivot c) ∈ ComplexMatrix2.traceless ∧
        withPivotValues Γ x A (pivot c).opposite = -withPivotValues Γ x A (pivot c) :=
      fun c hc => ⟨by rw [hBp c hc]; exact hxm c hc, by rw [hBp c hc, hBr c hc]⟩
    have hBone := isBondForm_of_pivotValues hA hBo hBs
    have hpiv : ∀ c ∈ Γ, IsPivotBondOf Γ (pivot c : BondAtLevel L m K k) :=
      fun c hc => ⟨c, hc, Or.inl rfl⟩
    have e : IsEliminatedForm V Γ A (withPivotValues Γ x A) := by
      refine ⟨hBo, hBs, fun c hc => ?_⟩
      have hsum := linearizedConstraint_eq_add hx0 (hnot c hc) (hH c hc) hBone hA₀
        (fun b hb => (hBo b hb).trans (offPivots_of_not_isPivotBondOf hb).symm) (hxm c hc)
        (by rw [hBp c hc, offPivots_of_isPivotBondOf (hpiv c hc), zero_add])
        (by rw [hBr c hc, offPivots_of_isPivotBondOf (isPivotBondOf_opposite (hpiv c hc)),
          zero_sub])
      rw [hsum, hxe c hc, add_neg_cancel]
    refine ⟨withPivotValues Γ x A, e, fun B' e' => ?_⟩
    have o₁ := isBondForm_of_pivotValues hA e'.1 e'.2.1
    have hy : ∀ c ∈ Γ, B' (pivot c) = withPivotValues Γ x A (pivot c) := by
      intro c hc
      have m₁ := (e'.2.1 c hc).1
      have m₂ := (e.2.1 c hc).1
      have hym : B' (pivot c) - withPivotValues Γ x A (pivot c) ∈ complexLieAlgebra :=
        ComplexMatrix2.traceless.sub_mem m₁ m₂
      have hsum := linearizedConstraint_eq_add hx0 (hnot c hc) (hH c hc) o₁ hBone
        (fun b hb => (e'.1 b hb).trans (e.1 b hb).symm) hym (by abel)
        (by rw [(e'.2.1 c hc).2, (e.2.1 c hc).2]; abel)
      rw [e'.2.2 c hc, e.2.2 c hc, zero_add] at hsum
      obtain ⟨T, hT⟩ := hinv c hc
      have hz : T ⟨_, hym⟩ = 0 := Subtype.ext (by rw [hT]; exact hsum.symm)
      have hz' : (⟨_, hym⟩ : ComplexMatrix2.traceless) = 0 := by simpa using hz
      exact sub_eq_zero.1 (congrArg Subtype.val hz')
    funext b
    by_cases hb : IsPivotBondOf Γ b
    · obtain ⟨c, hc, e₁ | e₁⟩ := hb
      · rw [e₁, hy c hc]
      · rw [e₁, (e'.2.1 c hc).2, (e.2.1 c hc).2, hy c hc]
    · exact (e'.1 b hb).trans (hBo b hb).symm
end PeriodicLattice.EliminationConstruction
end YangMills.Construction
