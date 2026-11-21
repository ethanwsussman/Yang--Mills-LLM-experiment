import YangMills.Construction.TorusOrFourSpace.CountableFamilyOfACountableChoice
import YangMills.Construction.TorusOrFourSpace.DisjointMembersOfTheStock
import YangMills.Construction.TorusOrFourSpace.DistinctPointsAndProductsOfAdmissibleFamiliesProof
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.PeriodicSpace.DisjointStockMembers
open Kind
private theorem exists_pos_two_mul_le {ι : Type*} [Fintype ι] [Nonempty ι] (d : ι → ℝ≥0∞)
    (h : ∀ p, 0 < d p) : ∃ η : ℝ, 0 < η ∧ ∀ p, ENNReal.ofReal (2 * η) ≤ d p := by
  have hr : ∀ p, ∃ r : ℝ, 0 < r ∧ ENNReal.ofReal r ≤ d p := by
    intro p
    obtain ⟨r, hr0, hrd⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 (h p)
    refine ⟨r, by exact_mod_cast hr0, ?_⟩
    rw [ENNReal.ofReal_coe_nnreal]
    exact hrd.le
  choose r hr0 hrd using hr
  have hm : 0 < Finset.univ.inf' Finset.univ_nonempty r :=
    (Finset.lt_inf'_iff _).2 fun p _ => hr0 p
  refine ⟨Finset.univ.inf' Finset.univ_nonempty r / 2, by positivity, fun p => ?_⟩
  have hle : Finset.univ.inf' Finset.univ_nonempty r ≤ r p :=
    Finset.inf'_le _ (Finset.mem_univ p)
  refine le_trans (ENNReal.ofReal_le_ofReal ?_) (hrd p)
  linarith
private theorem isOpenQ_inter (D : Params) (E : Kind) {A B : Set (E.Pt D)}
    (hA : IsOpenQ D E A) (hB : IsOpenQ D E B) : IsOpenQ D E (A ∩ B) := by apply _root_.YangMills.Construction.PeriodicSpace.Kind.AdmissibleProducts.isOpenQ_inter <;> assumption
theorem holds (h₁ : Kind.QuotientCompactC1.Claim)
    (h₂ : CountableChoiceFamilyFacts) : DisjointStockMembers.Statement := by
  intro D E n hn S W hS hdisj hW hSW
  obtain ⟨-, -, -, ⟨hpos, hnbhd, -, hsep⟩, -⟩ := h₁ D E
  have hbetween := (h₂ D E).2.2.1
  have : Nonempty (Fin n × Fin n) := ⟨(⟨0, hn⟩, ⟨0, hn⟩)⟩
  obtain ⟨η, hη, hwidth⟩ := exists_pos_two_mul_le
    (fun p : Fin n × Fin n => if p.1 = p.2 then 1 else setInfDist D E (S p.1) (S p.2))
    (fun p => by
      by_cases hp : p.1 = p.2
      · simp [hp]
      · simpa [hp] using hpos _ _ (hS p.1) (hS p.2) (hdisj hp))
  have hQ : ∀ i, ∃ Q ∈ supportStock D E, S i ⊆ Q ∧
      Q ⊆ W i ∩ openThickening D E (S i) (hS i) η hη := fun i =>
    hbetween (S i) _ (hS i) (isOpenQ_inter D E (hW i) (hnbhd (S i) (hS i) η hη).1)
      (Set.subset_inter (hSW i) (hnbhd (S i) (hS i) η hη).2)
  choose Q hQstock hSQ hQW using hQ
  refine ⟨Q, hQstock, fun i k hik => ?_, fun i => ⟨hSQ i, (hQW i).trans Set.inter_subset_left⟩⟩
  have hd : ENNReal.ofReal (2 * η) ≤ setInfDist D E (S i) (S k) := by
    simpa [hik] using hwidth (i, k)
  have hempty := hsep (S i) (S k) (hS i) (hS k) η hη hd
  show Disjoint (Q i) (Q k)
  rw [Set.disjoint_iff_inter_eq_empty, Set.eq_empty_iff_forall_notMem]
  intro y hy
  have hy' : y ∈ openThickening D E (S i) (hS i) η hη ∩
      openThickening D E (S k) (hS k) η hη := ⟨(hQW i hy.1).2, (hQW k hy.2).2⟩
  rw [hempty] at hy'
  exact hy'
end YangMills.Construction.PeriodicSpace.DisjointStockMembers
