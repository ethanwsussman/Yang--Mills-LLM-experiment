import YangMills.Construction.Lattice.EliminationMapOfAFormedSetProof
import YangMills.Construction.Lattice.EliminationMapOnHolomorphicFamilies
import YangMills.Construction.Lattice.LinearisedConstraintOnHolomorphicFamilies
import YangMills.Construction.Lattice.PivotInverseOnHolomorphicFamilies
import YangMills.Construction.Lattice.SitesTopsAndIndicesAreFinitelyMany
import YangMills.Construction.Matrices.MatrixOperationsKeepHolomorphy
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.PeriodicLattice.EliminationHolomorphy
open Matrices Matrices.GroupLieProduct
variable {L m K k : ℕ}
private theorem opposite_opposite {j : ℤ} (b : Bond L m j) : b.opposite.opposite = b := by apply _root_.YangMills.SharedProofs.p1012 <;> assumption
private theorem singleBondForm_self {j : ℤ} (b : Bond L m j) (X : ComplexMatrix2) :
    singleBondForm b X b = X := by
  simp [singleBondForm]
private theorem singleBondForm_opposite {j : ℤ} {b : Bond L m j} (h : b ≠ b.opposite)
    (X : ComplexMatrix2) : singleBondForm b X b.opposite = -X := by
  simp [singleBondForm, h.symm]
private theorem singleBondForm_of_ne {j : ℤ} {b b' : Bond L m j} (h₁ : b' ≠ b)
    (h₂ : b' ≠ b.opposite) (X : ComplexMatrix2) : singleBondForm b X b' = 0 := by
  simp [singleBondForm, h₁, h₂]
private theorem isBondForm_singleBondForm {j : ℤ} {b : Bond L m j} (h : b ≠ b.opposite)
    {X : ComplexMatrix2} (hX : X ∈ complexLieAlgebra) :
    IsBondForm complexLieAlgebra (singleBondForm b X) := by apply _root_.YangMills.Construction.PeriodicLattice.EliminationConstruction.isBondForm_singleBondForm <;> assumption
private theorem isBondForm_add {j : ℤ} {E F : Bond L m j → ComplexMatrix2}
    (hE : IsBondForm complexLieAlgebra E) (hF : IsBondForm complexLieAlgebra F) :
    IsBondForm complexLieAlgebra (E + F) := by
  refine ⟨fun b hb => ComplexMatrix2.traceless.add_mem (hE.1 b hb) (hF.1 b hb), fun b => ?_⟩
  rw [Pi.add_apply, Pi.add_apply, hE.2 b, hF.2 b, neg_add]
private theorem ne_opposite {j : ℤ} {b : Bond L m j}
    (hx : Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented) : b ≠ b.opposite := by apply _root_.YangMills.Construction.PeriodicLattice.EliminationConstruction.ne_opposite <;> assumption
private theorem mem_traceless_of_isBondForm {j : ℤ}
    (hx : ∀ b : Bond L m j, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    {E : Bond L m j → ComplexMatrix2} (hE : IsBondForm complexLieAlgebra E) (b : Bond L m j) :
    E b ∈ ComplexMatrix2.traceless := by
  rcases hx b with h | h
  · exact hE.1 b h.1
  · have h' := ComplexMatrix2.traceless.neg_mem (hE.1 _ h.1)
    rwa [hE.2 b, neg_neg] at h'
private theorem isPivotBondOf_opposite {j j' : ℤ} {Γ : Set (Bond L m j)} {b : Bond L m j'}
    (h : IsPivotBondOf Γ b) : IsPivotBondOf Γ b.opposite := by apply _root_.YangMills.Construction.PeriodicLattice.EliminationConstruction.isPivotBondOf_opposite <;> assumption
private theorem not_isPivotBondOf_opposite {j j' : ℤ} {Γ : Set (Bond L m j)} {b : Bond L m j'}
    (h : ¬ IsPivotBondOf Γ b) : ¬ IsPivotBondOf Γ b.opposite := fun h' =>
  h (by simpa only [opposite_opposite] using isPivotBondOf_opposite h')
private def zeroOnPivots {j j' : ℤ} (Γ : Set (Bond L m j)) (A : Bond L m j' → ComplexMatrix2) :
    Bond L m j' → ComplexMatrix2 :=
  open Classical in
  fun b => if IsPivotBondOf Γ b then 0 else A b
private theorem zeroOnPivots_of_isPivotBondOf {j j' : ℤ} {Γ : Set (Bond L m j)}
    {A : Bond L m j' → ComplexMatrix2} {b : Bond L m j'} (h : IsPivotBondOf Γ b) :
    zeroOnPivots Γ A b = 0 := by
  simp only [zeroOnPivots, if_pos h]
private theorem zeroOnPivots_of_not {j j' : ℤ} {Γ : Set (Bond L m j)}
    {A : Bond L m j' → ComplexMatrix2} {b : Bond L m j'} (h : ¬ IsPivotBondOf Γ b) :
    zeroOnPivots Γ A b = A b := by
  simp only [zeroOnPivots, if_neg h]
private theorem isBondForm_zeroOnPivots {j j' : ℤ} {Γ : Set (Bond L m j)}
    {A : Bond L m j' → ComplexMatrix2} (hA : IsBondForm complexLieAlgebra A) :
    IsBondForm complexLieAlgebra (zeroOnPivots Γ A) := by
  refine ⟨fun b hb => ?_, fun b => ?_⟩
  · by_cases h : IsPivotBondOf Γ b
    · rw [zeroOnPivots_of_isPivotBondOf h]; exact ComplexMatrix2.traceless.zero_mem
    · rw [zeroOnPivots_of_not h]; exact hA.1 b hb
  · by_cases h : IsPivotBondOf Γ b
    · rw [zeroOnPivots_of_isPivotBondOf h,
        zeroOnPivots_of_isPivotBondOf (isPivotBondOf_opposite h), neg_zero]
    · rw [zeroOnPivots_of_not h, zeroOnPivots_of_not (not_isPivotBondOf_opposite h)]
      exact hA.2 b
private theorem isBondForm_of_isEliminatedForm {Γ : Set (BondAtLevel L m K (k + 1))}
    {A B : BondAtLevel L m K k → ComplexMatrix2} (hA : IsBondForm complexLieAlgebra A)
    (h₁ : ∀ b, ¬ IsPivotBondOf Γ b → B b = A b)
    (h₂ : ∀ c ∈ Γ, B (pivot c) ∈ ComplexMatrix2.traceless ∧ B (pivot c).opposite = -B (pivot c)) :
    IsBondForm complexLieAlgebra B := by apply _root_.YangMills.Construction.PeriodicLattice.EliminationConstruction.isBondForm_of_pivotValues <;> assumption
private theorem linearizedConstraint_eq_of_eqOn_nonpivots {V : BondAtLevel L m K k → ComplexMatrix2}
    {c : BondAtLevel L m K (k + 1)}
    (hx : ∀ b : BondAtLevel L m K k, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    (H : LinearizedConstraintProperties V c) (S : Finset (BondAtLevel L m K (k + 1)))
    (hS : ∀ c'' ∈ S, ∀ X ∈ complexLieAlgebra,
      linearizedConstraint V (singleBondForm (pivot c'') X) c = 0) :
    ∀ E F : BondAtLevel L m K k → ComplexMatrix2,
      IsBondForm complexLieAlgebra E → IsBondForm complexLieAlgebra F →
      (∀ b, ¬ IsPivotBondOf (S : Set (BondAtLevel L m K (k + 1))) b → E b = F b) →
      linearizedConstraint V E c = linearizedConstraint V F c := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    intro E F _ _ h
    have e : E = F := funext fun b => h b (by
      rintro ⟨c'', hc'', -⟩
      simp at hc'')
    rw [e]
  | insert a S _ ih =>
    intro E F hE hF hEF
    have hseen := hS a (Finset.mem_insert_self a S)
    obtain ⟨p, hp⟩ : ∃ p : BondAtLevel L m K k, p = pivot a := ⟨_, rfl⟩
    rw [← hp] at hseen
    have hne : p ≠ p.opposite := ne_opposite (hx p)
    have hy : E p - F p ∈ complexLieAlgebra :=
      ComplexMatrix2.traceless.sub_mem (mem_traceless_of_isBondForm hx hE p)
        (mem_traceless_of_isBondForm hx hF p)
    have hf := isBondForm_singleBondForm hne hy
    have hagree : ∀ b, ¬ IsPivotBondOf (S : Set (BondAtLevel L m K (k + 1))) b →
        E b = (F + singleBondForm p (E p - F p)) b := by
      intro b hb
      by_cases e₁ : b = p
      · rw [e₁, Pi.add_apply, singleBondForm_self]
        abel
      · by_cases e₂ : b = p.opposite
        · rw [e₂, Pi.add_apply, singleBondForm_opposite hne, hE.2 p, hF.2 p]
          abel
        · rw [Pi.add_apply, singleBondForm_of_ne e₁ e₂, add_zero]
          refine hEF b ?_
          rintro ⟨c'', hc'', e | e⟩
          · rcases Finset.mem_insert.1 (Finset.mem_coe.1 hc'') with rfl | h
            · exact e₁ (e.trans hp.symm)
            · exact hb ⟨c'', Finset.mem_coe.2 h, Or.inl e⟩
          · rcases Finset.mem_insert.1 (Finset.mem_coe.1 hc'') with rfl | h
            · exact e₂ (by rw [e, hp])
            · exact hb ⟨c'', Finset.mem_coe.2 h, Or.inr e⟩
    rw [ih (fun c'' h => hS c'' (Finset.mem_insert_of_mem h)) E _ hE (isBondForm_add hF hf) hagree,
      H.map_add F _ hF hf, hseen _ hy, add_zero]
private theorem eliminate_pivot_eq [Finite (BondAtLevel L m K (k + 1))]
    {V : BondAtLevel L m K k → ComplexMatrix2} {Γ : Set (BondAtLevel L m K (k + 1))}
    (hx : ∀ b : BondAtLevel L m K k, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    (H : ∀ c ∈ Γ, LinearizedConstraintProperties V c)
    (hinv : ∀ c ∈ Γ, PivotCoeffInvertible V c)
    (hseen : ∀ c ∈ Γ, ∀ c'' ∈ Γ, c'' ≠ c → ∀ X ∈ complexLieAlgebra,
      linearizedConstraint V (singleBondForm (pivot c'') X) c = 0)
    {A B : BondAtLevel L m K k → ComplexMatrix2} (hA : IsBondForm complexLieAlgebra A)
    (hB : IsEliminatedForm V Γ A B) {c : BondAtLevel L m K (k + 1)} (hc : c ∈ Γ) :
    B (pivot c) = pivotCoeffInv V c (-linearizedConstraint V (zeroOnPivots Γ A) c) := by
  classical
  have hone := isBondForm_of_isEliminatedForm hA hB.1 hB.2.1
  have hA₀ : IsBondForm complexLieAlgebra (zeroOnPivots Γ A) := isBondForm_zeroOnPivots hA
  have hxm := (hB.2.1 c hc).1
  obtain ⟨p, hp⟩ : ∃ p : BondAtLevel L m K k, p = pivot c := ⟨_, rfl⟩
  have hne : p ≠ p.opposite := ne_opposite (hx p)
  have hxm' : B p ∈ complexLieAlgebra := by rw [hp]; exact hxm
  have hf := isBondForm_singleBondForm hne hxm'
  have hfin : (Γ \ {c}).Finite := Set.toFinite _
  have hagree : ∀ b,
      ¬ IsPivotBondOf ((hfin.toFinset : Finset _) : Set (BondAtLevel L m K (k + 1))) b →
      B b = (zeroOnPivots Γ A + singleBondForm p (B p)) b := by
    intro b hb
    rw [Set.Finite.coe_toFinset] at hb
    by_cases e₁ : b = p
    · rw [e₁, Pi.add_apply, singleBondForm_self,
        zeroOnPivots_of_isPivotBondOf ⟨c, hc, Or.inl hp⟩, zero_add]
    · by_cases e₂ : b = p.opposite
      · rw [e₂, Pi.add_apply, singleBondForm_opposite hne,
          zeroOnPivots_of_isPivotBondOf ⟨c, hc, Or.inr (by rw [hp])⟩, zero_add, hp]
        exact (hB.2.1 c hc).2
      · rw [Pi.add_apply, singleBondForm_of_ne e₁ e₂, add_zero]
        have hnp : ¬ IsPivotBondOf Γ b := by
          rintro ⟨c'', hc'', e | e⟩
          · by_cases h : c'' = c
            · exact e₁ (by rw [e, h, hp])
            · exact hb ⟨c'', ⟨hc'', h⟩, Or.inl e⟩
          · by_cases h : c'' = c
            · exact e₂ (by rw [e, h, hp])
            · exact hb ⟨c'', ⟨hc'', h⟩, Or.inr e⟩
        rw [zeroOnPivots_of_not hnp]
        exact hB.1 b hnp
  have hsum := linearizedConstraint_eq_of_eqOn_nonpivots hx (H c hc) hfin.toFinset
    (fun c'' h X hX => by
      have h' := hfin.mem_toFinset.1 h
      exact hseen c hc c'' h'.1 h'.2 X hX)
    B _ hone (isBondForm_add hA₀ hf) hagree
  rw [hB.2.2 c hc, (H c hc).map_add _ _ hA₀ hf] at hsum
  have hm : pivotCoeff V c (B (pivot c)) = -linearizedConstraint V (zeroOnPivots Γ A) c := by
    rw [← hp]
    have e : pivotCoeff V c (B p) = linearizedConstraint V (singleBondForm p (B p)) c := by
      rw [hp]; rfl
    rw [e]
    exact eq_neg_of_add_eq_zero_right hsum.symm
  obtain ⟨T, hT⟩ := hinv c hc
  have hinj : InjOn (pivotCoeff V c) (ComplexMatrix2.traceless : Set ComplexMatrix2) := by
    intro u hu v hv e
    have h : T ⟨u, hu⟩ = T ⟨v, hv⟩ := Subtype.ext (by rw [hT, hT]; exact e)
    exact congrArg Subtype.val (T.injective h)
  rw [← hm]
  exact (hinj.leftInvOn_invFunOn hxm).symm
theorem eliminate_preservesHolomorphicForms (hE : UniqueEliminationClaim)
    (hF : LinearizedConstraintAtBond.Statement)
    (hQ : HolomorphicConstraint.claim)
    (hP : PivotInverseHolomorphic)
    (hM : HolomorphyClosureStatement)
    (hX : LevelBondOrientationDichotomy)
    (hS : SeparatedRegions.FinitenessOfSitesTopsAndIndices) :
    EliminationPreservesHolomorphicForms := by
  intro L m K k hL hm hk ι κ _ _ b W U hU Γ hpos hform hinv A hA
  have hW := hA.isOpen
  obtain ⟨hconst, -, -, -, hlin, -, -, -, -, -, hcongr⟩ := hM ι κ b W hW
  have hx : ∀ b : BondAtLevel L m K k,
      Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented :=
    hX L m K hL hm (by omega) k (by omega)
  have : Finite (BondAtLevel L m K (k + 1)) :=
    ((hS L m hL hm).1 K (k + 1) (by omega) (by omega)).2.1
  have hH : ∀ p ∈ W, ∀ c ∈ Γ, LinearizedConstraintProperties (U p) c := fun p hp c hc =>
    hF L m K k hL hm hk (U p) c (hpos c hc) (hform p hp c hc)
  have hEl := fun p (hp : p ∈ W) => hE L m K k hL hm hk (U p) Γ hpos (hform p hp) (hinv p hp)
  have hB : ∀ p ∈ W, IsEliminatedForm (U p) Γ (A p) (eliminate (U p) Γ (A p)) :=
    fun p hp => Classical.epsilon_spec ((hEl p hp).2 (A p) (hA.isBondForm p hp)).exists
  have hA₀ : IsHolomorphicBondFormFamily b W fun p => zeroOnPivots Γ (A p) := by
    refine ⟨hW, fun p hp => isBondForm_zeroOnPivots (hA.isBondForm p hp), fun e => ?_⟩
    by_cases he : IsPivotBondOf Γ e
    · exact hcongr _ _ (hconst 0) fun p _ => zeroOnPivots_of_isPivotBondOf he
    · exact hcongr _ _ (hA.holomorphic e) fun p _ => zeroOnPivots_of_not he
  have hneg : ∀ Φ : (ι ⊕ κ → ComplexMatrix2) → ComplexMatrix2,
      IsHolomorphicToMatrixEntries b W Φ →
      IsHolomorphicToMatrixEntries b W fun p => -Φ p := fun Φ hΦ =>
    hcongr _ _ (hlin (-LinearMap.id) Φ hΦ) fun p _ => by simp
  have hpv : ∀ c ∈ Γ, IsHolomorphicToMatrixEntries b W
      fun p => eliminate (U p) Γ (A p) (pivot c) := by
    intro c hc
    have hin : ∀ p ∈ W,
        U p ∈ (complexAveragingDomainNearOne c : Set (BondAtLevel L m K k → ComplexMatrix2)) :=
      fun p hp => hform p hp c hc
    have hset : {p | p ∈ W ∧ PivotCoeffInvertible (U p) c} = W :=
      Set.ext fun p => ⟨And.left, fun h => ⟨h, hinv p h c hc⟩⟩
    have hq := (hQ L m K k hL hm hk ι κ b W U hU c (hpos c hc) hin).1 _ hA₀
    have hν : IsHolomorphicToTraceless b W
        fun p => -linearizedConstraint (U p) (zeroOnPivots Γ (A p)) c :=
      ⟨fun p hp => ComplexMatrix2.traceless.neg_mem (hq.1 hp), hneg _ hq.2⟩
    have hr := (hP L m K k hL hm hk ι κ b W U hU c (hpos c hc) hin).2
    rw [hset] at hr
    exact hcongr _ _ (hr _ hν).2 fun p hp =>
      eliminate_pivot_eq hx (hH p hp) (hinv p hp) (hEl p hp).1 (hA.isBondForm p hp) (hB p hp) hc
  refine ⟨hW, fun p hp =>
    isBondForm_of_isEliminatedForm (hA.isBondForm p hp) (hB p hp).1 (hB p hp).2.1, fun e => ?_⟩
  by_cases he : IsPivotBondOf Γ e
  · obtain ⟨c, hc, rfl | rfl⟩ := he
    · exact hpv c hc
    · exact hcongr _ _ (hneg _ (hpv c hc)) fun p hp => ((hB p hp).2.1 c hc).2
  · exact hcongr _ _ (hA.holomorphic e) fun p hp => (hB p hp).1 e he
end YangMills.Construction.PeriodicLattice.EliminationHolomorphy
