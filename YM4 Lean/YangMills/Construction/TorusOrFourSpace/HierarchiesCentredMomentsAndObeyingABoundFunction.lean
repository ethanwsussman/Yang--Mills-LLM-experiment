import YangMills.Construction.TorusOrFourSpace.BoundFunctionsAndEffectiveConstants
import YangMills.Construction.TorusOrFourSpace.MultilinearFunctionalsAndSetsAtPositiveDistance
import YangMills.Construction.TorusOrFourSpace.TuplesInABallAndLipschitzClasses
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.PeriodicSpace
def partitionsNoSingletons (p : ℕ) :
    Finset (Finpartition (Finset.univ : Finset (Fin p))) :=
  Finset.univ.filter fun π => ∀ J ∈ π.parts, J.card ≠ 1
theorem two_le_card_of_mem_partitionsNoSingletons {p : ℕ}
    {π : Finpartition (Finset.univ : Finset (Fin p))}
    (hπ : π ∈ partitionsNoSingletons p) {J : Finset (Fin p)} (hJ : J ∈ π.parts) :
    2 ≤ J.card := by
  have hne : J.card ≠ 1 := (Finset.mem_filter.mp hπ).2 J hJ
  have hpos : 0 < J.card := Finset.card_pos.mpr (π.nonempty_of_mem_parts hJ)
  omega
namespace Kind
variable (D : Params) (E : Kind)
theorem comp_mem_sepC1Tuples {n k : ℕ} {f : FnTuple D E n}
    (hf : f ∈ sepC1Tuples D E n) {e : Fin k → Fin n} (he : Function.Injective e) :
    (fun i => f (e i)) ∈ sepC1Tuples D E k :=
  ⟨fun i => hf.1 (e i), fun i => hf.2.1 (e i), fun _ _ hik => hf.2.2 _ _ (he.ne hik)⟩
theorem restrictTuple_mem_sepC1Tuples {n : ℕ} {f : FnTuple D E n}
    (hf : f ∈ sepC1Tuples D E n) (J : Finset (Fin n)) :
    restrictTuple D E f J ∈ sepC1Tuples D E J.card :=
  comp_mem_sepC1Tuples D E hf (J.orderEmbOfFin rfl).injective
@[ext]
structure Hierarchy where
  func : (n : ℕ) → 2 ≤ n → sepC1Tuples D E n → ℝ
  multilinear : ∀ n (hn : 2 ≤ n),
    IsMultilinearOn D E (sepC1Tuples D E n) (func n hn)
  symmetric : ∀ n (hn : 2 ≤ n),
    IsPermSymmetricOn D E (sepC1Tuples D E n) (func n hn)
namespace Hierarchy
variable {D E}
def partitionMoment (Φ : Hierarchy D E) {p : ℕ} (f : sepC1Tuples D E p) : ℝ :=
  ∑ π ∈ (partitionsNoSingletons p).attach, ∏ J ∈ π.1.parts.attach,
    Φ.func J.1.card (two_le_card_of_mem_partitionsNoSingletons π.2 J.2)
      ⟨restrictTuple D E f.1 J.1, restrictTuple_mem_sepC1Tuples D E f.2 J.1⟩
theorem partitionMoment_zero (Φ : Hierarchy D E) (f : sepC1Tuples D E 0) :
    Φ.partitionMoment f = 1 := by
  have hb : ∀ π : Finpartition (Finset.univ : Finset (Fin 0)), π.parts = ∅ := fun π =>
    Finset.eq_empty_of_forall_notMem fun J hJ => by
      obtain ⟨x, -⟩ := π.nonempty_of_mem_parts hJ
      exact x.elim0
  have hm : (⊥ : Finpartition (Finset.univ : Finset (Fin 0))) ∈
      partitionsNoSingletons 0 :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun J hJ => by simp [hb] at hJ⟩
  unfold partitionMoment
  refine (Finset.sum_eq_single_of_mem ⟨⊥, hm⟩ (Finset.mem_attach _ _) fun π _ hπ => ?_).trans
    (Finset.prod_eq_one fun J _ => ?_)
  · exact absurd (Subtype.ext (Finpartition.ext (by rw [hb π.1, hb ⊥]))) hπ
  · obtain ⟨J, hJ⟩ := J
    simp [hb] at hJ
def IsBoundedBy (Φ : Hierarchy D E) (C : BoundFamily) : Prop :=
  ∀ (n : ℕ) (hn : 2 ≤ n) (d R : ℝ), 0 < d → R ∈ allowedRadii D E →
    ∀ f : sepC1Tuples D E n, f.1 ∈ lipTuplesSpacedInBalls D E n d R →
      ENNReal.ofReal |Φ.func n hn f| ≤
        ENNReal.ofReal (C.val n d R) * ∏ i, sharpNormQ D E (f.1 i)
end Hierarchy
def boundedHierarchies (C : BoundFamily) : Set (Hierarchy D E) := {Φ | Φ.IsBoundedBy C}
end Kind
end YangMills.Construction.PeriodicSpace
