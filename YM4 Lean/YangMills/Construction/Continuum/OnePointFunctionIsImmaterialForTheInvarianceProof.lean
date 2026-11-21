import YangMills.Construction.Continuum.OnePointFunctionIsImmaterialForTheInvariance
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open MeasureTheory
open Orthogonal SeparatedTuples
open TupleLists (ofList toList)
open TestSpaces (cumulantRec sepRestrict)
open SetPartition (PartitionsFin)
namespace OrthogonalAction
open InfiniteLattice (AmbientSpace)
namespace OnePoint
def blockPlaces {n : ℕ} (J : Finset (Fin n)) : Finset ℕ := J.image fun i => i.1 + 1
theorem mem_blockPlaces {n : ℕ} (J : Finset (Fin n)) (i : Fin n) :
    i.1 + 1 ∈ blockPlaces J ↔ i ∈ J := by
  simp only [blockPlaces, Finset.mem_image, Nat.add_right_cancel_iff]
  exact ⟨fun ⟨j, hj, h⟩ => (Fin.ext h) ▸ hj, fun h => ⟨i, h, rfl⟩⟩
theorem blockPlaces_subset_Icc {n : ℕ} (J : Finset (Fin n)) : blockPlaces J ⊆ Finset.Icc 1 n := by
  intro k hk
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hk
  exact Finset.mem_Icc.2 ⟨by omega, by omega⟩
theorem zipIdx_one_eq_map_finRange (F : List RealValued) :
    F.zipIdx 1 = (List.finRange F.length).map fun i => (F.get i, i.1 + 1) := by
  refine List.ext_getElem (by simp) fun i h₁ h₂ => ?_
  simp [List.getElem_zipIdx, add_comm]
theorem filter_finRange_mem_eq_sort {n : ℕ} (J : Finset (Fin n)) :
    (List.finRange n).filter (fun i => decide (i ∈ J)) = J.sort (· ≤ ·) := by
  refine List.Perm.eq_of_pairwise (le := (· ≤ ·)) (fun _ _ _ _ h₁ h₂ => le_antisymm h₁ h₂)
    (((List.pairwise_le_finRange n)).filter _) (Finset.pairwise_sort J (· ≤ ·)) ?_
  refine (List.perm_ext_iff_of_nodup ((List.nodup_finRange n).filter _) (Finset.sort_nodup J _)).2
    fun i => ?_
  simp
theorem ofFn_restrictTuple {n : ℕ} {E : Type*} (g : Fin n → E) (J : Finset (Fin n)) :
    List.ofFn (SchwingerFunctions.restrictTuple g J) = (J.sort (· ≤ ·)).map g := by
  refine List.ext_getElem (by simp) fun i h₁ h₂ => ?_
  simp only [List.getElem_ofFn, List.getElem_map, SchwingerFunctions.restrictTuple]
  exact congrArg g (Finset.orderEmbOfFin_apply J rfl _)
theorem sublistOn_blockPlaces (F : List RealValued) (J : Finset (Fin F.length)) :
    SepTuple.sublistOn F (blockPlaces J) = List.ofFn (SchwingerFunctions.restrictTuple F.get J) := by
  rw [ofFn_restrictTuple, ← filter_finRange_mem_eq_sort, SepTuple.sublistOn,
    zipIdx_one_eq_map_finRange, List.filter_map, List.map_map]
  have hp : ((fun p : RealValued × ℕ => decide (p.2 ∈ blockPlaces J)) ∘
      fun i : Fin F.length => (F.get i, i.1 + 1)) = fun i => decide (i ∈ J) := by
    funext i
    simp only [Function.comp_apply, decide_eq_decide]
    exact mem_blockPlaces J i
  rw [hp]
  rfl
theorem toList_sepRestrict (T : SepTuple) (J : Finset (Fin T.1.length)) :
    toList ⟨J.card, sepRestrict (ofList T).2 J⟩ = T.subtuple (blockPlaces J) :=
  Subtype.ext (sublistOn_blockPlaces T.1 J).symm
theorem cumulantRec_sepRestrict (φ : TupleFunctional) (T : SepTuple) (J : Finset (Fin T.1.length)) :
    cumulantRec (fun S => φ (toList S)) J.card (sepRestrict (ofList T).2 J) =
      cumulantAt φ (T.subtuple (blockPlaces J)) := by
  rw [cumulantAt, ← toList_sepRestrict]
  exact congrArg (fun S : TestSpaces.SepTuple =>
    cumulantRec (fun S => φ (toList S)) S.1 S.2)
    (TupleLists.ofList_toList ⟨J.card, sepRestrict (ofList T).2 J⟩).symm
theorem length_subtuple_blockPlaces (T : SepTuple) {n : ℕ} (h : T.1.length = n) (J : Finset (Fin n)) :
    (T.subtuple (blockPlaces J)).1.length = J.card := by
  subst h
  show (SepTuple.sublistOn T.1 (blockPlaces J)).length = J.card
  rw [sublistOn_blockPlaces, List.length_ofFn]
theorem cumulantAt_eq_sub_sum (φ : TupleFunctional) (T : SepTuple) {n : ℕ} (h : T.1.length = n) :
    cumulantAt φ T = φ T - ∑ π ∈ TestSpaces.properPartitions n,
      ∏ J ∈ π.parts, cumulantAt φ (T.subtuple (blockPlaces J)) := by
  subst h
  have h₀ := TestSpaces.cumulantRec_eq (fun S => φ (toList S)) (ofList T).2
  refine Eq.trans h₀ ?_
  exact congrArg₂ (· - ·) (congrArg φ (TupleLists.toList_ofList T))
    (Finset.sum_congr rfl fun π _ => Finset.prod_congr rfl fun J _ =>
      cumulantRec_sepRestrict φ T J)
theorem apply_eq_sum_prod_cumulantAt (φ : TupleFunctional) (T : SepTuple) {n : ℕ}
    (h : T.1.length = n) (hn : 1 ≤ n) :
    φ T = ∑ π : PartitionsFin n, ∏ J ∈ π.parts, cumulantAt φ (T.subtuple (blockPlaces J)) := by
  subst h
  have h₀ := eq_sum_partitions_prod_cumulant (fun S => φ (toList S)) (n := (ofList T).1) hn (ofList T).2
  exact (congrArg φ (TupleLists.toList_ofList T)).symm.trans
    (h₀.trans (Finset.sum_congr rfl fun π _ => Finset.prod_congr rfl fun J _ =>
      cumulantRec_sepRestrict φ T J))
theorem invMap_matMap (R : orthogonalGroupFour) (x : AmbientSpace) :
    invMap (matMap R) x = (R⁻¹ : orthogonalGroupFour).1.mulVec x := by
  have hl : ∀ y : AmbientSpace, (R⁻¹ : orthogonalGroupFour).1.mulVec (matMap R y) = y := fun y => by
    show (R⁻¹ : orthogonalGroupFour).1.mulVec (R.1.mulVec y) = y
    rw [Matrix.mulVec_mulVec]
    have : (R⁻¹ : orthogonalGroupFour).1 * R.1 = 1 := congrArg Subtype.val (inv_mul_cancel R)
    rw [this, Matrix.one_mulVec]
  have hr : matMap R ((R⁻¹ : orthogonalGroupFour).1.mulVec x) = x := by
    show R.1.mulVec ((R⁻¹ : orthogonalGroupFour).1.mulVec x) = x
    rw [Matrix.mulVec_mulVec]
    have : R.1 * (R⁻¹ : orthogonalGroupFour).1 = 1 := congrArg Subtype.val (mul_inv_cancel R)
    rw [this, Matrix.one_mulVec]
  have hinj : Function.Injective (matMap R) := Function.LeftInverse.injective hl
  calc invMap (matMap R) x
        = invMap (matMap R) (matMap R ((R⁻¹ : orthogonalGroupFour).1.mulVec x)) := by
        rw [hr]
    _ = (R⁻¹ : orthogonalGroupFour).1.mulVec x := Function.leftInverse_invFun hinj _
theorem push_val_singleton (R : orthogonalGroupFour) (S : SepTuple) {f : RealValued} (hS : S.1 = [f])
    (hlen : (push (matMap R) S).size = S.size) :
    (push (matMap R) S).1 = [orthogonalAct R f] := by
  have hf : (f ∘ invMap (matMap R)) = orthogonalAct R f := by
    funext x
    simp only [Function.comp_apply, orthogonalAct, invMap_matMap]
  by_cases h : IsDisjointlySupported (pushList (matMap R) S.1)
  · have h₀ : push (matMap R) S = ⟨pushList (matMap R) S.1, h⟩ := dif_pos h
    rw [h₀]
    simp [pushList, hS, hf]
  · have h₀ : push (matMap R) S = SepTuple.nil := dif_neg h
    rw [h₀] at hlen
    simp [SepTuple.size, SepTuple.nil, hS] at hlen
theorem cumulantAt_push_of_isInvariant (hl : Laws.Statement) (φ : TupleFunctional)
    (R : orthogonalGroupFour) (hφ : φ.IsInvariant (matMap R)) (n : ℕ) :
    ∀ T : SepTuple, T.1.length = n → 1 ≤ n →
      cumulantAt φ (push (matMap R) T) = cumulantAt φ T := by
  obtain ⟨-, -, hlen, -, hsub, -⟩ := hl.1 R R
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro T hT _
    have hRT : (push (matMap R) T).1.length = n := (hlen T).trans hT
    rw [cumulantAt_eq_sub_sum φ T hT, cumulantAt_eq_sub_sum φ _ hRT, hφ T]
    congr 1
    refine Finset.sum_congr rfl fun π hπ => Finset.prod_congr rfl fun J hJ => ?_
    have hlt := TestSpaces.card_lt_of_mem_properPartitions hπ hJ
    have hne : 1 ≤ J.card := Finset.card_pos.2 (π.nonempty_of_mem_parts hJ)
    have hs : blockPlaces J ⊆ Finset.Icc 1 T.size := fun k hk => by
      have h := Finset.mem_Icc.1 (blockPlaces_subset_Icc J hk)
      exact Finset.mem_Icc.2 ⟨h.1, h.2.trans_eq hT.symm⟩
    rw [hsub T _ hs]
    exact ih J.card hlt _ (length_subtuple_blockPlaces T hT J) hne
theorem cumulantAt_push_singleton (hl : Laws.Statement) (φ : TupleFunctional)
    (R : orthogonalGroupFour)
    {c : ℝ} (hc : ∀ (f : RealValued) (hf : IsC1c f),
      cumulantAt φ (singletonTuple f hf) = φ (singletonTuple f hf) ∧
        φ (singletonTuple f hf) = c * ∫ x, f x)
    (S : SepTuple) (hS : S.1.length = 1) :
    cumulantAt φ (push (matMap R) S) = cumulantAt φ S := by
  obtain ⟨hfun, -, hlen, -⟩ := hl.1 R R
  obtain ⟨f, hf⟩ := List.length_eq_one_iff.1 hS
  have hcf : IsC1c f := S.2.1 f (by simp [hf])
  obtain ⟨hcg, -, -, -, hint, -⟩ := hfun f hcf
  have hS' : S = singletonTuple f hcf := Subtype.ext hf
  have hR : push (matMap R) S = singletonTuple (orthogonalAct R f) hcg :=
    Subtype.ext (push_val_singleton R S hf (hlen S))
  rw [hR, hS', (hc _ hcg).1, (hc _ hcg).2, (hc _ hcf).1, (hc _ hcf).2, hint]
theorem isInvariant_of_cumulantAt_push (hl : Laws.Statement) (φ : TupleFunctional)
    (R : orthogonalGroupFour)
    {c : ℝ} (hc : ∀ (f : RealValued) (hf : IsC1c f),
      cumulantAt φ (singletonTuple f hf) = φ (singletonTuple f hf) ∧
        φ (singletonTuple f hf) = c * ∫ x, f x)
    (h₂ : ∀ T : SepTuple, 2 ≤ T.size →
      cumulantAt φ (push (matMap R) T) = cumulantAt φ T) :
    φ.IsInvariant (matMap R) := by
  obtain ⟨-, -, hlen, -, hsub, -⟩ := hl.1 R R
  intro T
  rcases Nat.eq_zero_or_pos T.1.length with h0 | hpos
  · have hT : T = SepTuple.nil := Subtype.ext (List.length_eq_zero_iff.1 h0)
    rw [hT, push_nil]
  · have hT : T.1.length = T.1.length := rfl
    have hRT : (push (matMap R) T).1.length = T.1.length := hlen T
    rw [apply_eq_sum_prod_cumulantAt φ T hT hpos, apply_eq_sum_prod_cumulantAt φ _ hRT hpos]
    refine Finset.sum_congr rfl fun π _ => Finset.prod_congr rfl fun J hJ => ?_
    have hne : 1 ≤ J.card := Finset.card_pos.2 (π.nonempty_of_mem_parts hJ)
    rw [hsub T _ (blockPlaces_subset_Icc J)]
    have hk := length_subtuple_blockPlaces T hT J
    rcases Nat.lt_or_ge J.card 2 with h1 | h1
    · exact cumulantAt_push_singleton hl φ R hc _ (by omega)
    · exact h₂ _ (by show 2 ≤ (T.subtuple (blockPlaces J)).1.length; omega)
theorem onePoint_irrelevance (hl : Laws.Statement) : OnePointIrrelevance := by
  intro φ R
  refine ⟨fun hφ T hT => cumulantAt_push_of_isInvariant hl φ R hφ T.1.length T rfl hT, ?_⟩
  rintro ⟨c, hc⟩ h₂
  exact isInvariant_of_cumulantAt_push hl φ R hc h₂
end OnePoint
end OrthogonalAction
end YangMills.Construction
