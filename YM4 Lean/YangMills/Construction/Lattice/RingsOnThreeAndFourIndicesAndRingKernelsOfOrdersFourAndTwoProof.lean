import YangMills.Construction.Lattice.RingKernelOfOrderFourProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Tuples Function
namespace PeriodicLattice
namespace RingsOfOrderThreeFourAndKernelsProof
section TupleFacts
variable {J : Type*} {n : ℕ}
private theorem rotateBy_mem_ringClass {σ w : Fin n → J} (t : ℤ) (hw : w ∈ ringClass σ) :
    rotateBy t w ∈ ringClass σ := by
  rw [← ringClass_eq_of_mem hw]
  exact Or.inl ⟨t, rfl⟩
private theorem reversed_mem_ringClass {σ w : Fin n → J} (hw : w ∈ ringClass σ) :
    reversed w ∈ ringClass σ := by
  rw [← ringClass_eq_of_mem hw]
  exact Or.inr ⟨w, mem_rotationClass_self w, rfl⟩
private theorem mem_ringClass_self (σ : Fin n → J) : σ ∈ ringClass σ :=
  Or.inl (mem_rotationClass_self σ)
private theorem finRotate_three_apply : ∀ i : Fin 3, finRotate 3 i = ![1, 2, 0] i := by
  decide +kernel
private theorem finRotate_four_apply : ∀ i : Fin 4, finRotate 4 i = ![1, 2, 3, 0] i := by
  decide +kernel
private theorem rotateBy_one_three (σ : Fin 3 → J) : rotateBy 1 σ = ![σ 1, σ 2, σ 0] := by
  funext i
  rw [rotateBy_one_apply, finRotate_three_apply]
  fin_cases i <;> rfl
private theorem reversed_three (σ : Fin 3 → J) : reversed σ = ![σ 2, σ 1, σ 0] := by
  funext i
  fin_cases i <;> rfl
private theorem rotateBy_one_four (σ : Fin 4 → J) : rotateBy 1 σ = ![σ 1, σ 2, σ 3, σ 0] := by
  funext i
  rw [rotateBy_one_apply, finRotate_four_apply]
  fin_cases i <;> rfl
private theorem reversed_four (σ : Fin 4 → J) : reversed σ = ![σ 3, σ 2, σ 1, σ 0] := by
  funext i
  fin_cases i <;> rfl
private theorem finRotate_four_zpow (t : ℤ) :
    ∃ k : Fin 4, finRotate 4 ^ t = finRotate 4 ^ (k : ℕ) := by
  have hord : (finRotate 4) ^ (4 : ℤ) = 1 := by
    have hnat : (finRotate 4) ^ (4 : ℕ) = 1 := by decide +kernel
    exact_mod_cast hnat
  refine ⟨⟨(t % 4).toNat, by omega⟩, ?_⟩
  have ht : t = 4 * (t / 4) + ((t % 4).toNat : ℤ) := by omega
  conv_lhs => rw [ht]
  rw [zpow_add, zpow_mul, hord, one_zpow, one_mul, zpow_natCast]
private theorem rotateBy_four_cases (t : ℤ) (σ : Fin 4 → J) :
    rotateBy t σ = σ ∨ rotateBy t σ = ![σ 1, σ 2, σ 3, σ 0] ∨
      rotateBy t σ = ![σ 2, σ 3, σ 0, σ 1] ∨ rotateBy t σ = ![σ 3, σ 0, σ 1, σ 2] := by
  obtain ⟨k, hk⟩ := finRotate_four_zpow t
  have hform : rotateBy t σ = fun i => σ ((finRotate 4 ^ (k : ℕ)) i) := by
    funext i
    simp only [rotateBy, hk]
  have q0 : ∀ i : Fin 4, (finRotate 4 ^ 0) i = i := by decide +kernel
  have q1 : ∀ i : Fin 4, (finRotate 4 ^ 1) i = ![1, 2, 3, 0] i := by decide +kernel
  have q2 : ∀ i : Fin 4, (finRotate 4 ^ 2) i = ![2, 3, 0, 1] i := by decide +kernel
  have q3 : ∀ i : Fin 4, (finRotate 4 ^ 3) i = ![3, 0, 1, 2] i := by decide +kernel
  rw [hform]
  fin_cases k
  · left
    funext i
    exact congrArg σ (q0 i)
  · right; left
    funext i
    refine (congrArg σ (q1 i)).trans ?_
    fin_cases i <;> rfl
  · right; right; left
    funext i
    refine (congrArg σ (q2 i)).trans ?_
    fin_cases i <;> rfl
  · right; right; right
    funext i
    refine (congrArg σ (q3 i)).trans ?_
    fin_cases i <;> rfl
private theorem backwardFromFirst_eq_rotateBy (σ : Fin 4 → J) :
    ![σ 0, σ 3, σ 2, σ 1] = rotateBy 3 (reversed σ) := by
  have hthree : rotateBy 3 (reversed σ) = rotateBy 1 (rotateBy 1 (rotateBy 1 (reversed σ))) := by
    simp only [rotateBy_rotateBy]
    norm_num
  rw [hthree, rotateBy_one_four, rotateBy_one_four, rotateBy_one_four, reversed_four]
  rfl
private theorem ringClass_backwardFromFirst (σ : Fin 4 → J) :
    ringClass ![σ 0, σ 3, σ 2, σ 1] = ringClass σ := by
  rw [backwardFromFirst_eq_rotateBy, ringClass_rotateBy, ringClass_reversed]
private theorem eq_or_eq_backward_of_mem {σ w : Fin 4 → J} (hσ : Injective σ)
    (hw : w ∈ ringClass σ) (hfirst : w 0 = σ 0) : w = σ ∨ w = ![σ 0, σ 3, σ 2, σ 1] := by
  have d10 : σ 1 ≠ σ 0 := fun e => absurd (hσ e) (by decide)
  have d20 : σ 2 ≠ σ 0 := fun e => absurd (hσ e) (by decide)
  have d30 : σ 3 ≠ σ 0 := fun e => absurd (hσ e) (by decide)
  rw [ringClass_eq_union] at hw
  rcases hw with ⟨t, rfl⟩ | ⟨t, rfl⟩
  · rcases rotateBy_four_cases t σ with e | e | e | e <;> simp only [] at hfirst ⊢ <;>
      rw [e] at hfirst ⊢
    · exact Or.inl rfl
    · exact absurd hfirst d10
    · exact absurd hfirst d20
    · exact absurd hfirst d30
  · rcases rotateBy_four_cases t (reversed σ) with e | e | e | e <;> simp only [] at hfirst ⊢ <;>
      rw [e] at hfirst ⊢
    · exact absurd hfirst d30
    · exact absurd hfirst d20
    · exact absurd hfirst d10
    · exact Or.inr rfl
end TupleFacts
private theorem fixFirst_apply_zero (τ : Equiv.Perm (TailPosition 4)) : fixFirst τ 0 = 0 := by
  simp [fixFirst]
private theorem fixFirst_injective :
    Injective (fixFirst : Equiv.Perm (TailPosition 4) → Fin 4 → Fin 4) := by
  intro σ τ h
  refine Equiv.ext fun x => Subtype.ext ?_
  have hx := congrFun h x.1
  simpa only [fixFirst, dif_pos x.2] using hx
abbrev _root_.YangMills.SharedProofs.p29512 := @fixFirst_injective
private theorem exists_fixFirst_eq {v : Fin 4 → Fin 4} (hv : IsBijectiveTuple v) (hzero : v 0 = 0) :
    ∃ τ : Equiv.Perm (TailPosition 4), fixFirst τ = v := by apply _root_.YangMills.SharedProofs.p51877 <;> assumption
private theorem exists_eq_ringClass_fixFirst {R : Set (Fin 4 → Fin 4)} (hR : IsRingOfTuples R) :
    ∃ τ : Equiv.Perm (TailPosition 4), R = ringClass (fixFirst τ) := by
  obtain ⟨O, ⟨σ, hσ, rfl⟩, rfl⟩ := hR
  obtain ⟨i, hi⟩ := hσ.2 0
  have hrot : ∀ i : Fin 4, (finRotate 4 ^ (i : ℕ)) 0 = i := by decide +kernel
  have hzero : rotateBy ((i : ℕ) : ℤ) σ 0 = 0 := by
    simp only [rotateBy, zpow_natCast, hrot, hi]
  obtain ⟨τ, hτ⟩ := exists_fixFirst_eq (hσ.rotateBy ((i : ℕ) : ℤ)) hzero
  exact ⟨τ, by rw [hτ]; exact (ringClass_rotateBy _ σ).symm⟩
private theorem two_orderings_of_ring {R : Set (Fin 4 → Fin 4)} (hR : IsRingOfTuples R) :
    ∃ τ τ' : Equiv.Perm (TailPosition 4), τ ≠ τ' ∧
      {σ : Equiv.Perm (TailPosition 4) | ringClass (fixFirst σ) = R} = {τ, τ'} ∧
      rotationClass (fixFirst τ') = reversedSet (rotationClass (fixFirst τ)) := by
  obtain ⟨τ, rfl⟩ := exists_eq_ringClass_fixFirst hR
  have hv := isBijectiveTuple_fixFirst τ
  have hb : IsBijectiveTuple ![fixFirst τ 0, fixFirst τ 3, fixFirst τ 2, fixFirst τ 1] := by
    rw [backwardFromFirst_eq_rotateBy]
    exact hv.reversed.rotateBy 3
  obtain ⟨τ', hτ'⟩ := exists_fixFirst_eq hb (fixFirst_apply_zero τ)
  refine ⟨τ, τ', ?_, ?_, ?_⟩
  · rintro rfl
    have h13 : fixFirst τ 1 = fixFirst τ 3 := congrFun hτ' 1
    exact absurd (hv.1 h13) (by decide)
  · ext σ
    simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · intro h
      have hm : fixFirst σ ∈ ringClass (fixFirst τ) := h ▸ mem_ringClass_self _
      rcases eq_or_eq_backward_of_mem hv.1 hm
        ((fixFirst_apply_zero σ).trans (fixFirst_apply_zero τ).symm) with e | e
      · exact Or.inl (fixFirst_injective e)
      · exact Or.inr (fixFirst_injective (e.trans hτ'.symm))
    · rintro (rfl | rfl)
      · rfl
      · rw [hτ', ringClass_backwardFromFirst]
  · rw [hτ', backwardFromFirst_eq_rotateBy, rotationClass_rotateBy, reversedSet_rotationClass]
private theorem exists_standardFourRing_eq {R : Set (Fin 4 → Fin 4)} (hR : IsRingOfTuples R) :
    ∃ r, standardFourRing r = R := by
  obtain ⟨τ, rfl⟩ := exists_eq_ringClass_fixFirst hR
  have hv := isBijectiveTuple_fixFirst τ
  have hcases : ∀ b c d : Fin 4, b ≠ 0 → c ≠ 0 → d ≠ 0 → b ≠ c → b ≠ d → c ≠ d →
      ∃ r : Fin 3, ![0, b, c, d] = standardFourTuple r ∨ ![0, d, c, b] = standardFourTuple r := by
    decide +kernel
  have hne : ∀ {a b : Fin 4}, a ≠ b → fixFirst τ a ≠ fixFirst τ b :=
    fun h e => h (hv.1 e)
  have hz := fixFirst_apply_zero τ
  obtain ⟨r, hr⟩ := hcases _ _ _ (hz ▸ hne (a := 1) (b := 0) (by decide))
    (hz ▸ hne (a := 2) (b := 0) (by decide)) (hz ▸ hne (a := 3) (b := 0) (by decide))
    (hne (a := 1) (b := 2) (by decide)) (hne (a := 1) (b := 3) (by decide))
    (hne (a := 2) (b := 3) (by decide))
  have hfull : ![0, fixFirst τ 1, fixFirst τ 2, fixFirst τ 3] = fixFirst τ := by
    funext i
    fin_cases i
    · exact hz.symm
    · rfl
    · rfl
    · rfl
  refine ⟨r, ?_⟩
  rcases hr with e | e
  · rw [standardFourRing, ← e, hfull]
  · rw [standardFourRing, ← e, ← hz]
    exact ringClass_backwardFromFirst _
private theorem standardFourRing_injective : Injective standardFourRing := by
  intro a b h
  by_contra hab
  have hedge : ∀ a b : Fin 3, a ≠ b → ∃ x y : Fin 4,
      (∃ i, s(standardFourTuple a i, standardFourTuple a (finRotate 4 i)) = s(x, y)) ∧
      ¬ ∃ i, s(standardFourTuple b i, standardFourTuple b (finRotate 4 i)) = s(x, y) := by
    decide +kernel
  obtain ⟨x, y, h₁, h₂⟩ := hedge a b hab
  have hE : cyclicEdges (standardFourTuple a) = cyclicEdges (standardFourTuple b) := by
    rw [← edgesOfRing_ringClass, ← edgesOfRing_ringClass]
    exact congrArg edgesOfRing h
  have hm : s(x, y) ∈ cyclicEdges (standardFourTuple a) := h₁
  rw [hE] at hm
  exact h₂ hm
private theorem setOf_isRingOfTuples_four :
    {R : Set (Fin 4 → Fin 4) | IsRingOfTuples R} = Set.range standardFourRing := by
  ext R
  constructor
  · exact fun h => exists_standardFourRing_eq h
  · rintro ⟨r, rfl⟩
    exact isRingOfTuples_ringClass (isBijectiveTuple_standardFourTuple r)
private theorem existsUnique_ring_three : ∃! R : Set (Fin 3 → Fin 3), IsRingOfTuples R := by
  have he : IsBijectiveTuple (![0, 1, 2] : Fin 3 → Fin 3) := by
    unfold IsBijectiveTuple
    decide
  refine ⟨ringClass ![0, 1, 2], isRingOfTuples_ringClass he, ?_⟩
  rintro R ⟨O, ⟨σ, hσ, rfl⟩, rfl⟩
  have m0 := mem_ringClass_self (![0, 1, 2] : Fin 3 → Fin 3)
  have m1 : (![1, 2, 0] : Fin 3 → Fin 3) ∈ ringClass ![0, 1, 2] := by
    have hm := rotateBy_mem_ringClass 1 m0
    rwa [rotateBy_one_three] at hm
  have m2 : (![2, 0, 1] : Fin 3 → Fin 3) ∈ ringClass ![0, 1, 2] := by
    have hm := rotateBy_mem_ringClass 1 m1
    rwa [rotateBy_one_three] at hm
  have m3 : (![2, 1, 0] : Fin 3 → Fin 3) ∈ ringClass ![0, 1, 2] := by
    have hm := reversed_mem_ringClass m0
    rwa [reversed_three] at hm
  have m4 : (![0, 2, 1] : Fin 3 → Fin 3) ∈ ringClass ![0, 1, 2] := by
    have hm := reversed_mem_ringClass m1
    rwa [reversed_three] at hm
  have m5 : (![1, 0, 2] : Fin 3 → Fin 3) ∈ ringClass ![0, 1, 2] := by
    have hm := reversed_mem_ringClass m2
    rwa [reversed_three] at hm
  have hsix : ∀ a b c : Fin 3, a ≠ b → a ≠ c → b ≠ c →
      ![a, b, c] = ![0, 1, 2] ∨ ![a, b, c] = ![1, 2, 0] ∨ ![a, b, c] = ![2, 0, 1] ∨
        ![a, b, c] = ![2, 1, 0] ∨ ![a, b, c] = ![0, 2, 1] ∨ ![a, b, c] = ![1, 0, 2] := by
    decide +kernel
  have hne : ∀ {a b : Fin 3}, a ≠ b → σ a ≠ σ b := fun h e => h (hσ.1 e)
  have hfull : ![σ 0, σ 1, σ 2] = σ := by
    funext i
    fin_cases i <;> rfl
  have hm : σ ∈ ringClass ![0, 1, 2] := by
    rw [← hfull]
    rcases hsix _ _ _ (hne (a := 0) (b := 1) (by decide)) (hne (a := 0) (b := 2) (by decide))
      (hne (a := 1) (b := 2) (by decide)) with e | e | e | e | e | e <;> rw [e]
    exacts [m0, m1, m2, m3, m4, m5]
  exact ringClass_eq_of_mem hm
section KernelFacts
variable {L m : ℕ} {j : ℤ}
private theorem finprod_edgesOfRing_fixFirst (C : Plaquette L m j → Plaquette L m j → ℝ)
    (hC : IsSymmetricKernel C) (p : Fin 4 → Plaquette L m j)
    (τ : Equiv.Perm (TailPosition 4)) :
    ∏ᶠ e ∈ edgesOfRing (ringClass (fixFirst τ)), pairKernel C hC p e =
      ∏ i, C (p (fixFirst τ i)) (p (fixFirst τ (finRotate 4 i))) := by
  have h0 : Injective (fun i : Fin 4 => s(i, finRotate 4 i)) := by decide +kernel
  have hinj : Injective (fun i : Fin 4 => s(fixFirst τ i, fixFirst τ (finRotate 4 i))) := by
    intro a b hab
    exact h0 (Sym2.map.injective (isBijectiveTuple_fixFirst τ).1 hab)
  rw [edgesOfRing_ringClass, cyclicEdges, finprod_mem_range hinj, finprod_eq_prod_of_fintype]
  rfl
private theorem cyclicKernel_four (C : Plaquette L m j → Plaquette L m j → ℝ)
    (hC : IsSymmetricKernel C) (φ : Fin 4 → Plaquette L m j → ℝ) :
    cyclicKernel C φ =
      ∑ᶠ R : {R : Set (Fin 4 → Fin 4) // IsRingOfTuples R}, ∑ᶠ p : Fin 4 → Plaquette L m j,
        (∏ i, φ i (p i)) * ∏ᶠ e ∈ edgesOfRing R.1, pairKernel C hC p e := by
  classical
  have : Finite {R : Set (Fin 4 → Fin 4) // IsRingOfTuples R} := by
    have hfin : {R : Set (Fin 4 → Fin 4) | IsRingOfTuples R}.Finite := by
      rw [setOf_isRingOfTuples_four]
      exact Set.finite_range standardFourRing
    exact hfin.to_subtype
  let _ := Fintype.ofFinite {R : Set (Fin 4 → Fin 4) // IsRingOfTuples R}
  rw [finsum_eq_sum_of_fintype]
  set H : {R : Set (Fin 4 → Fin 4) // IsRingOfTuples R} → ℝ := fun R =>
    ∑ᶠ p : Fin 4 → Plaquette L m j,
      (∏ i, φ i (p i)) * ∏ᶠ e ∈ edgesOfRing R.1, pairKernel C hC p e with hH
  let ρ : Equiv.Perm (TailPosition 4) → {R : Set (Fin 4 → Fin 4) // IsRingOfTuples R} := fun τ =>
    ⟨ringClass (fixFirst τ), isRingOfTuples_ringClass (isBijectiveTuple_fixFirst τ)⟩
  have hS : ∀ τ : Equiv.Perm (TailPosition 4),
      (∑ᶠ p : Fin 4 → Plaquette L m j, (∏ i, φ i (p i)) *
        ∏ i, C (p (fixFirst τ i)) (p (fixFirst τ (finRotate 4 i)))) = H (ρ τ) := by
    intro τ
    refine finsum_congr fun p => ?_
    rw [finprod_edgesOfRing_fixFirst C hC p τ]
  have hfib : ∀ R : {R : Set (Fin 4 → Fin 4) // IsRingOfTuples R},
      ∑ τ ∈ Finset.univ.filter (fun τ => ρ τ = R), H (ρ τ) = 2 * H R := by
    intro R
    obtain ⟨τ, τ', hne, hset, -⟩ := two_orderings_of_ring R.2
    have hf : Finset.univ.filter (fun τ => ρ τ = R) = {τ, τ'} := by
      ext σ
      have hσ : ρ σ = R ↔ σ ∈ ({τ, τ'} : Set (Equiv.Perm (TailPosition 4))) := by
        rw [← hset]
        exact Subtype.ext_iff
      simpa using hσ
    have hτ : ρ τ = R := by
      apply Subtype.ext
      have hmem : τ ∈ ({τ, τ'} : Set (Equiv.Perm (TailPosition 4))) := by simp
      rw [← hset] at hmem
      exact hmem
    have hτ' : ρ τ' = R := by
      apply Subtype.ext
      have hmem : τ' ∈ ({τ, τ'} : Set (Equiv.Perm (TailPosition 4))) := by simp
      rw [← hset] at hmem
      exact hmem
    rw [hf, Finset.sum_pair hne, hτ, hτ']
    ring
  unfold cyclicKernel
  simp only [hS]
  rw [← Finset.sum_fiberwise Finset.univ ρ, Finset.sum_congr rfl fun R _ => hfib R,
    ← Finset.mul_sum]
  ring
private theorem two_mul_cyclicKernel_two (C : Plaquette L m j → Plaquette L m j → ℝ)
    (hC : IsSymmetricKernel C) (φ : Fin 2 → Plaquette L m j → ℝ) :
    2 * cyclicKernel C φ =
      ∑ᶠ x : Plaquette L m j × Plaquette L m j, φ 0 x.1 * φ 1 x.2 * C x.1 x.2 ^ 2 := by
  have : Subsingleton (TailPosition 2) := ⟨fun a b => Subtype.ext (by
    have ha := a.2
    have hb := b.2
    omega)⟩
  have : Subsingleton (Equiv.Perm (TailPosition 2)) :=
    ⟨fun a b => Equiv.ext fun x => Subsingleton.elim _ _⟩
  have hid : fixFirst (1 : Equiv.Perm (TailPosition 2)) = id := by
    funext i
    by_cases hi : 0 < (i : ℕ)
    · simp [fixFirst, hi]
    · simp [fixFirst, hi]
  have q0 : finRotate 2 0 = 1 := by decide +kernel
  have q1 : finRotate 2 1 = 0 := by decide +kernel
  rw [← finsum_comp_equiv (finTwoArrowEquiv (Plaquette L m j))]
  unfold cyclicKernel
  rw [Fintype.sum_subsingleton _ (1 : Equiv.Perm (TailPosition 2)), hid]
  rw [← mul_assoc, show (2 : ℝ) * (1 / 2) = 1 by norm_num, one_mul]
  refine finsum_congr fun p => ?_
  simp only [Fin.prod_univ_two, id, q0, q1, hC (p 1) (p 0)]
  show _ = φ 0 (p 0) * φ 1 (p 1) * C (p 0) (p 1) ^ 2
  ring
end KernelFacts
end RingsOfOrderThreeFourAndKernelsProof
open RingsOfOrderThreeFourAndKernelsProof in
theorem ringsOfOrderThreeFourAndKernels_holds : RingsOfOrderThreeFourAndKernels :=
  ⟨⟨existsUnique_ring_three, by
      rw [setOf_isRingOfTuples_four, ← Set.image_univ,
        Set.ncard_image_of_injective _ standardFourRing_injective,
        Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin], setOf_isRingOfTuples_four⟩,
    fun _ hR => two_orderings_of_ring hR,
    fun _ _ _ C hC φ _ => cyclicKernel_four C hC φ,
    fun _ _ _ C hC φ _ => two_mul_cyclicKernel_two C hC φ⟩
end PeriodicLattice
end YangMills.Construction
