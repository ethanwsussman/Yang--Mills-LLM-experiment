import YangMills.Construction.Sequences.PNatIndexSetConvergence
import YangMills.Construction.TorusOrFourSpace.SeparatedTuplesAdmissibleRadiiAndTheSeparation
import Mathlib
set_option autoImplicit false
open scoped ENNReal Topology
noncomputable section
namespace YangMills.Construction.PeriodicSpace.DiagonalLimits
section OnTheSpace
variable (D : Params) (E : Kind)
def PairwiseSetDistGe {n : ℕ} (A : Fin n → Set (Kind.Pt D E)) (d : ℝ) : Prop :=
  ∀ l l', l ≠ l' → ENNReal.ofReal d ≤ Kind.setInfDist D E (A l) (A l')
abbrev IsSepTuple {n : ℕ} (f : Kind.FnTuple D E n) : Prop :=
  f ∈ Kind.sepC1Tuples D E n
end OnTheSpace
def EventuallyAlong (J : Sequences.PNatIndexSet) (P : ℕ+ → Prop) : Prop :=
  ∃ j' : ℤ, ∀ j ∈ J.carrier, j' ≤ (((j : ℕ+) : ℕ) : ℤ) → P j
def TendsToAlong (J : Sequences.PNatIndexSet) (j₀ : ℤ) (w : (J.filterGe j₀).carrier → ℂ) (z : ℂ) :
    Prop :=
  ∀ ε : ℝ, 0 < ε →
    EventuallyAlong J fun j => ∀ hj : j ∈ (J.filterGe j₀).carrier, ‖w ⟨j, hj⟩ - z‖ < ε
def HasLimitAlong (J : Sequences.PNatIndexSet) (j₀ : ℤ) (w : (J.filterGe j₀).carrier → ℂ) : Prop :=
  ∃ z : ℂ, TendsToAlong J j₀ w z
def IsValueOfMember (A : Sequences.PNatIndexSet) (k : ℕ) : Prop :=
  ∃ h : 0 < k, (⟨k, h⟩ : ℕ+) ∈ A.carrier
theorem setOf_isValueOfMember_infinite (A : Sequences.PNatIndexSet) :
    {k | IsValueOfMember A k}.Infinite := by
  refine (A.infinite.image PNat.coe_injective.injOn).mono ?_
  rintro _ ⟨j, hj, rfl⟩
  exact ⟨j.pos, hj⟩
def enumerate (A : Sequences.PNatIndexSet) (n : ℕ) : A.carrier :=
  have hmem : IsValueOfMember A (Nat.nth (IsValueOfMember A) n) :=
    Nat.nth_mem_of_infinite (setOf_isValueOfMember_infinite A) n
  ⟨⟨Nat.nth (IsValueOfMember A) n, hmem.1⟩, hmem.2⟩
theorem enumerate_strictMono (A : Sequences.PNatIndexSet) :
    StrictMono fun n => (((enumerate A n : A.carrier) : ℕ+) : ℕ) :=
  Nat.nth_strictMono (setOf_isValueOfMember_infinite A)
theorem exists_enumerate_eq (A : Sequences.PNatIndexSet) (j : A.carrier) :
    ∃ n, enumerate A n = j := by
  have hj : IsValueOfMember A ((j : ℕ+) : ℕ) := ⟨j.1.pos, j.2⟩
  have hr : ((j : ℕ+) : ℕ) ∈ Set.range (Nat.nth (IsValueOfMember A)) := by
    rw [Nat.range_nth_of_infinite (setOf_isValueOfMember_infinite A)]
    exact hj
  obtain ⟨n, hn⟩ := hr
  exact ⟨n, Subtype.ext (PNat.coe_injective hn)⟩
theorem tendsToAlong_iff_tendsTo (J : Sequences.PNatIndexSet) (j₀ : ℤ)
    (w : (J.filterGe j₀).carrier → ℂ) (z : ℂ) :
    TendsToAlong J j₀ w z ↔ (J.filterGe j₀).TendsTo w z := by
  constructor
  · intro h ε hε
    obtain ⟨j', hj'⟩ := h ε hε
    refine ⟨Nat.succPNat j'.toNat, fun j hj => ?_⟩
    refine hj' j.1 j.2.1 ?_ j.2
    have : j'.toNat + 1 ≤ ((j : ℕ+) : ℕ) := (PNat.coe_le_coe _ _).mpr hj
    omega
  · intro h ε hε
    obtain ⟨jε, hjε⟩ := h ε hε
    refine ⟨((jε : ℕ) : ℤ), fun j _ hle hj => hjε ⟨j, hj⟩ ?_⟩
    exact (PNat.coe_le_coe _ _).mp (by exact_mod_cast hle)
end YangMills.Construction.PeriodicSpace.DiagonalLimits
