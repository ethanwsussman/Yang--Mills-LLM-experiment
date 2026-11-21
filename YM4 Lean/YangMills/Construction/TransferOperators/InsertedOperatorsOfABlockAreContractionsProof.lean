import YangMills.Construction.Matrices.TensorOperatorsOfDisjointPartsCommute
import YangMills.Construction.TransferOperators.CopiesOfABlockAreDisjointOnATorus
import YangMills.Construction.TransferOperators.InsertedOperatorsOfABlockAreContractions
import YangMills.Construction.TransferOperators.KernelBetweenTwoSquareRootsFollowsABijection
import YangMills.Construction.TransferOperators.KernelBetweenTwoSquareRootsOfAProductIsAProduct
import Mathlib
set_option autoImplicit false
open YangMills.Construction.SpinHarmonics YangMills.Construction.InfiniteLattice
noncomputable section
namespace YangMills.Construction.TransferOperators.LevelProductOps
theorem finiteIndex_of_periods_le (Γ : CubicPeriodSublattice) {H : AddSubgroup (LatticePoint 1)}
    (h : Γ.lattice.periods ≤ H) : H.FiniteIndex := by
  have : NeZero Γ.side := ⟨by have := Γ.one_le_side; omega⟩
  have : Finite (LatticePoint 1 ⧸ H) := by
    refine Finite.of_injective (fun c : LatticePoint 1 ⧸ H => Γ.coordResidues (Quotient.out c)) fun c c' e => ?_
    have h₁ := h (Γ.sub_mem_periods (congrFun e))
    rw [← Quotient.out_eq c, ← Quotient.out_eq c']
    refine (QuotientAddGroup.eq).mpr ?_
    rw [neg_add_eq_sub]
    exact h₁
  exact AddSubgroup.finiteIndex_of_finite_quotient
theorem contraction_list_prod_norm_le_one {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (l : List (E →L[ℂ] E)) (h : ∀ T ∈ l, ‖T‖ ≤ 1) : ‖l.prod‖ ≤ 1 := by
  induction l with
  | nil => exact ContinuousLinearMap.norm_id_le
  | cons T l ih =>
    rw [List.prod_cons]
    refine (norm_mul_le _ _).trans ?_
    exact mul_le_one₀ (h T List.mem_cons_self) (norm_nonneg _)
      (ih fun T' hT' => h T' (List.mem_cons_of_mem _ hT'))
theorem norm_tensorOne_le (hProd : SandwichKernelProductStatement)
    {J : Type} [Finite J] [Nonempty J] (S : Set J) (hS : S.Nonempty)
    (X : HaarL2 ↥S →L[ℂ] HaarL2 ↥S) : ‖tensorOne S X‖ ≤ ‖X‖ := by
  have hu : IsPartitionWithRest (fun _ : Fin 1 => S) Sᶜ := by
    refine ⟨fun _ => hS, fun i k hik => (hik (Subsingleton.elim i k)).elim,
      fun _ => disjoint_compl_right, ?_⟩
    rw [Set.iUnion_const]
    exact Set.union_compl_self S
  have h := (hProd 1 one_pos J 1 (fun _ => S) Sᶜ (fun _ => X) hu).1
  simpa [tensorOneProduct] using h
variable {μ : Fin 4}
theorem norm_operatorCopy (hRelabel : SandwichKernelRelabelStatement)
    (Γ : CubicPeriodSublattice) (B : Block μ) (A : B.L2Operator) (v : LatticePoint 1)
    (hv : Function.Injective (Γ.blockCopy B v)) : ‖Γ.operatorCopy B A v‖ = ‖A‖ := by
  have : Nonempty ↥(B.links : Set (SliceLink μ)) := B.links_nonempty.to_subtype
  have hb : Function.Bijective (Set.rangeFactorization (Γ.blockCopy B v)) :=
    ⟨fun a b e => hv (congrArg Subtype.val e), Set.rangeFactorization_surjective⟩
  exact (hRelabel 1 one_pos _ _ _ A hb).2.2.2.1
theorem blockCopyRange_nonempty (Γ : CubicPeriodSublattice) (B : Block μ) (v : LatticePoint 1) :
    (Γ.blockCopyRange B v).Nonempty := by
  obtain ⟨b, hb⟩ := B.links_nonempty
  exact ⟨_, ⟨b, hb⟩, rfl⟩
theorem cosetRep_sub_notMem_periods (Γ : CubicPeriodSublattice) {H : AddSubgroup (LatticePoint 1)}
    {c c' : Γ.CosetsMod H} (h : c ≠ c') :
    Γ.cosetRep c - Γ.cosetRep c' ∉ Γ.lattice.periods := by
  intro hm
  apply h
  rw [← Quotient.out_eq c, ← Quotient.out_eq c']
  refine (QuotientAddGroup.eq).mpr (AddSubgroup.mem_addSubgroupOf.mpr ?_)
  have e : (((-Quotient.out c + Quotient.out c' : H) : LatticePoint 1)) =
      -(Γ.cosetRep c - Γ.cosetRep c') := by
    simp [CubicPeriodSublattice.cosetRep, sub_eq_add_neg, add_comm]
  rw [e]
  exact neg_mem hm
theorem contractionStatement_holds (hCopies : BlockCopies.DisjointStatement)
    (hComm : TensorOneDisjointCommuteForAll)
    (hRelabel : SandwichKernelRelabelStatement)
    (hProd : SandwichKernelProductStatement) : ContractionStatement := by
  intro μ B A hA i H hH Γ hΓ j
  obtain ⟨-, hinj, hdisj⟩ :=
    hCopies μ B i H (finiteIndex_of_periods_le Γ hΓ) hH Γ hΓ
  have hrep : ∀ c : Γ.CosetsMod H, Γ.cosetRep c ∈ H := fun c => (Quotient.out c).2
  have : Nonempty (Γ.LinkOrbits μ) := (blockCopyRange_nonempty Γ B 0).to_subtype.map Subtype.val
  refine ⟨fun c hc c' hc' => ?_, ?_⟩
  · by_cases hcc : c = c'
    · rw [hcc]
    · have hlevel : ∀ {d}, d ∈ Γ.cosetsAtLevel μ i H j →
          Γ.copyLevel μ i (Γ.cosetRep d) = j := fun hd => by
        have h := (Set.Finite.mem_toFinset (Set.toFinite _)).1 hd
        exact h
      have hd := hdisj _ (hrep c) _ (hrep c') (cosetRep_sub_notMem_periods Γ hcc)
        ((hlevel hc).trans (hlevel hc').symm)
      have hne := blockCopyRange_nonempty Γ B (Γ.cosetRep c)
      have hne' := blockCopyRange_nonempty Γ B (Γ.cosetRep c')
      have hsub : Γ.blockCopyRange B (Γ.cosetRep c') ⊆
          (Γ.blockCopyRange B (Γ.cosetRep c))ᶜ :=
        fun b hb hb' => Set.disjoint_left.1 hd hb' hb
      have huniv : Γ.blockCopyRange B (Γ.cosetRep c) ≠ Set.univ := by
        intro h
        obtain ⟨b, hb⟩ := hne'
        exact hsub hb (h ▸ Set.mem_univ b)
      exact hComm _ _ hne huniv _ _ hne' hsub _
  · refine contraction_list_prod_norm_le_one _ fun T hT => ?_
    obtain ⟨c, -, rfl⟩ := List.mem_map.1 hT
    refine (norm_tensorOne_le hProd _ (blockCopyRange_nonempty Γ B _) _).trans ?_
    rw [norm_operatorCopy hRelabel Γ B A _ (hinj _ (hrep c))]
    exact hA
end YangMills.Construction.TransferOperators.LevelProductOps
end
