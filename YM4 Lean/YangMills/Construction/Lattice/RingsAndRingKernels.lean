import YangMills.Construction.Lattice.PeriodicLattices
import Mathlib
noncomputable section
namespace YangMills.Construction
namespace Tuples
variable {J : Type*} {n : ℕ}
def IsBijectiveTuple (ς : Fin n → J) : Prop := Function.Bijective ς
def rotateBy (t : ℤ) (ς : Fin n → J) : Fin n → J := fun i => ς ((finRotate n ^ t) i)
def reversed (ς : Fin n → J) : Fin n → J := fun i => ς (Fin.rev i)
def rotationClass (ς : Fin n → J) : Set (Fin n → J) := Set.range fun t : ℤ => rotateBy t ς
def IsCyclicOrdering (O : Set (Fin n → J)) : Prop :=
  ∃ ς : Fin n → J, IsBijectiveTuple ς ∧ O = rotationClass ς
def reversedSet (O : Set (Fin n → J)) : Set (Fin n → J) := reversed '' O
def IsRingOfTuples (R : Set (Fin n → J)) : Prop :=
  ∃ O : Set (Fin n → J), IsCyclicOrdering O ∧ R = O ∪ reversedSet O
def ringClass (ς : Fin n → J) : Set (Fin n → J) :=
  rotationClass ς ∪ reversedSet (rotationClass ς)
def cyclicEdges (ς : Fin n → J) : Set (Sym2 J) :=
  Set.range fun i : Fin n => s(ς i, ς (finRotate n i))
def standardFourTuple : Fin 3 → Fin 4 → Fin 4 := ![![0, 1, 2, 3], ![0, 1, 3, 2], ![0, 2, 1, 3]]
def standardFourRing (r : Fin 3) : Set (Fin 4 → Fin 4) := ringClass (standardFourTuple r)
theorem isBijectiveTuple_standardFourTuple (r : Fin 3) :
    IsBijectiveTuple (standardFourTuple r) := by
  unfold IsBijectiveTuple
  fin_cases r <;> decide
theorem rotateBy_one_apply (ς : Fin n → J) (i : Fin n) : rotateBy 1 ς i = ς (finRotate n i) := by
  simp [rotateBy]
theorem rotateBy_zero (ς : Fin n → J) : rotateBy 0 ς = ς := by
  funext i
  simp [rotateBy]
theorem rotateBy_rotateBy (t t' : ℤ) (ς : Fin n → J) :
    rotateBy t' (rotateBy t ς) = rotateBy (t + t') ς := by
  funext i
  simp [rotateBy, zpow_add, Equiv.Perm.mul_apply]
theorem reversed_reversed (ς : Fin n → J) : reversed (reversed ς) = ς := by
  funext i
  simp [reversed]
private theorem finRotate_rev_finRotate (i : Fin n) :
    finRotate n (Fin.rev (finRotate n i)) = Fin.rev i := by
  cases n with
  | zero => exact i.elim0
  | succ k =>
    ext
    rw [coe_finRotate]
    by_cases hlast : i = Fin.last k
    · subst hlast
      simp
    · have hlt : (i : ℕ) < k := by
        have := i.isLt
        have : (i : ℕ) ≠ k := fun e => hlast (Fin.ext e)
        omega
      rw [finRotate_of_lt hlt]
      by_cases hrev : (⟨(i : ℕ) + 1, by omega⟩ : Fin (k + 1)).rev = Fin.last k
      · simp only [hrev, if_true]
        have := congrArg Fin.val hrev
        simp only [Fin.val_rev, Fin.val_last] at this
        simp only [Fin.val_rev]
        omega
      · rw [if_neg hrev]
        have : ((⟨(i : ℕ) + 1, by omega⟩ : Fin (k + 1)).rev : ℕ) = k - ((i : ℕ) + 1) := by
          simp only [Fin.val_rev]
          omega
        rw [this]
        simp only [Fin.val_rev]
        omega
abbrev _root_.YangMills.SharedProofs.p38097 := @finRotate_rev_finRotate
private theorem revPerm_semiconj_finRotate :
    SemiconjBy (Fin.revPerm (n := n)) (finRotate n)⁻¹ (finRotate n) := by
  ext i
  have := finRotate_rev_finRotate ((finRotate n)⁻¹ i)
  rw [show finRotate n ((finRotate n)⁻¹ i) = i from (finRotate n).apply_symm_apply i] at this
  simp only [Equiv.Perm.mul_apply, Fin.revPerm_apply]
  rw [this]
theorem reversed_rotateBy (t : ℤ) (ς : Fin n → J) :
    reversed (rotateBy t ς) = rotateBy (-t) (reversed ς) := by
  funext i
  have h := congrArg (fun g : Equiv.Perm (Fin n) => g i)
    (revPerm_semiconj_finRotate (n := n).zpow_right t).eq
  simp only [Equiv.Perm.mul_apply, Fin.revPerm_apply, inv_zpow] at h
  simp only [reversed, rotateBy, zpow_neg]
  rw [h]
theorem IsBijectiveTuple.rotateBy {ς : Fin n → J} (h : IsBijectiveTuple ς) (t : ℤ) :
    IsBijectiveTuple (rotateBy t ς) :=
  h.comp (finRotate n ^ t).bijective
theorem IsBijectiveTuple.reversed {ς : Fin n → J} (h : IsBijectiveTuple ς) :
    IsBijectiveTuple (reversed ς) :=
  h.comp Fin.revPerm.bijective
theorem mem_rotationClass_self (ς : Fin n → J) : ς ∈ rotationClass ς :=
  ⟨0, rotateBy_zero ς⟩
theorem rotationClass_rotateBy (t : ℤ) (ς : Fin n → J) :
    rotationClass (rotateBy t ς) = rotationClass ς := by
  ext w
  constructor
  · rintro ⟨t', rfl⟩
    exact ⟨t + t', (rotateBy_rotateBy t t' ς).symm⟩
  · rintro ⟨t', rfl⟩
    refine ⟨t' - t, ?_⟩
    simp only [rotateBy_rotateBy, add_sub_cancel]
theorem reversedSet_rotationClass (ς : Fin n → J) :
    reversedSet (rotationClass ς) = rotationClass (reversed ς) := by
  ext w
  constructor
  · rintro ⟨_, ⟨t, rfl⟩, rfl⟩
    exact ⟨-t, (reversed_rotateBy t ς).symm⟩
  · rintro ⟨t, rfl⟩
    refine ⟨rotateBy (-t) ς, ⟨-t, rfl⟩, ?_⟩
    rw [reversed_rotateBy, neg_neg]
theorem isRingOfTuples_ringClass {ς : Fin n → J} (h : IsBijectiveTuple ς) :
    IsRingOfTuples (ringClass ς) :=
  ⟨rotationClass ς, ⟨ς, h, rfl⟩, rfl⟩
theorem ringClass_eq_union (ς : Fin n → J) :
    ringClass ς = rotationClass ς ∪ rotationClass (reversed ς) := by
  rw [ringClass, reversedSet_rotationClass]
theorem ringClass_reversed (ς : Fin n → J) : ringClass (reversed ς) = ringClass ς := by
  rw [ringClass_eq_union, ringClass_eq_union, reversed_reversed, Set.union_comm]
theorem ringClass_rotateBy (t : ℤ) (ς : Fin n → J) : ringClass (rotateBy t ς) = ringClass ς := by
  rw [ringClass_eq_union, ringClass_eq_union, rotationClass_rotateBy, reversed_rotateBy,
    rotationClass_rotateBy]
theorem ringClass_eq_of_mem {ς ς' : Fin n → J} (h : ς' ∈ ringClass ς) :
    ringClass ς' = ringClass ς := by
  rw [ringClass_eq_union] at h
  rcases h with ⟨t, rfl⟩ | ⟨t, rfl⟩
  · exact ringClass_rotateBy t ς
  · rw [ringClass_rotateBy, ringClass_reversed]
theorem cyclicEdges_rotateBy (t : ℤ) (ς : Fin n → J) :
    cyclicEdges (rotateBy t ς) = cyclicEdges ς := by
  have hcomm : ∀ i, (finRotate n ^ t) (finRotate n i) = finRotate n ((finRotate n ^ t) i) :=
    fun i => by
      have := congrArg (fun g : Equiv.Perm (Fin n) => g i)
        ((Commute.refl (finRotate n)).zpow_left t).eq
      simpa only [Equiv.Perm.mul_apply] using this
  ext e
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨(finRotate n ^ t) i, by simp only [rotateBy, hcomm]⟩
  · rintro ⟨i, rfl⟩
    refine ⟨(finRotate n ^ t)⁻¹ i, ?_⟩
    simp only [rotateBy, hcomm]
    rw [show (finRotate n ^ t) ((finRotate n ^ t)⁻¹ i) = i from
      (finRotate n ^ t).apply_symm_apply i]
theorem cyclicEdges_reversed (ς : Fin n → J) : cyclicEdges (reversed ς) = cyclicEdges ς := by
  ext e
  constructor
  · rintro ⟨i, rfl⟩
    refine ⟨Fin.rev (finRotate n i), ?_⟩
    simp only [reversed, finRotate_rev_finRotate]
    exact Sym2.eq_swap
  · rintro ⟨i, rfl⟩
    refine ⟨Fin.rev (finRotate n i), ?_⟩
    simp only [reversed, finRotate_rev_finRotate, Fin.rev_rev]
    exact Sym2.eq_swap
theorem cyclicEdges_eq_of_mem_ringClass {ς ς' : Fin n → J} (h : ς' ∈ ringClass ς) :
    cyclicEdges ς' = cyclicEdges ς := by
  rw [ringClass_eq_union] at h
  rcases h with ⟨t, rfl⟩ | ⟨t, rfl⟩
  · exact cyclicEdges_rotateBy t ς
  · rw [cyclicEdges_rotateBy, cyclicEdges_reversed]
abbrev TailPosition (n : ℕ) : Type := {i : Fin n // 0 < (i : ℕ)}
def fixFirst (τ : Equiv.Perm (TailPosition n)) : Fin n → Fin n :=
  fun i => if h : 0 < (i : ℕ) then (τ ⟨i, h⟩ : Fin n) else i
theorem isBijectiveTuple_fixFirst (τ : Equiv.Perm (TailPosition n)) :
    IsBijectiveTuple (fixFirst τ) := by
  have hinj : Function.Injective (fixFirst τ) := by
    intro i i' h
    simp only [fixFirst] at h
    split_ifs at h with h₁ h₂ h₂
    · have := τ.injective (Subtype.ext h)
      exact congrArg Subtype.val (this)
    · have := (τ ⟨i, h₁⟩).2
      rw [h] at this
      exact absurd this h₂
    · have := (τ ⟨i', h₂⟩).2
      rw [← h] at this
      exact absurd this h₁
    · exact h
  exact ⟨hinj, Finite.injective_iff_surjective.mp hinj⟩
end Tuples
namespace PeriodicLattice
open Tuples
variable {L m : ℕ} {j : ℤ}
def IsSymmetricKernel (C : Plaquette L m j → Plaquette L m j → ℝ) : Prop :=
  ∀ p q, C p q = C q p
def cyclicKernel {n : ℕ} (C : Plaquette L m j → Plaquette L m j → ℝ)
    (φ : Fin n → Plaquette L m j → ℝ) : ℝ :=
  1 / 2 * ∑ τ : Equiv.Perm (TailPosition n), ∑ᶠ p : Fin n → Plaquette L m j,
    (∏ i, φ i (p i)) *
      ∏ i, C (p (fixFirst τ i)) (p (fixFirst τ (finRotate n i)))
end PeriodicLattice
end YangMills.Construction
