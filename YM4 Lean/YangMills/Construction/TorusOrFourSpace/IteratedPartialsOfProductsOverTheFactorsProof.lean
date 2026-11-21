import YangMills.Construction.TorusOrFourSpace.ContinuousPartialsAreContinuousDifferentiability
import YangMills.Construction.TorusOrFourSpace.IteratedPartialsOfProductsOverTheFactors
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicSpace.PartialDerivatives
open Coords (partialAlong iterPartial ContPartialsUpTo)
variable {p : ℕ+}
theorem pnat_one_coe : ((1 : ℕ+) : ℕ) = 1 := rfl
def blockPoint (i : Fin (p : ℕ)) (x : Coords p) : Coords 1 := x.block i
def blockCoord (i : Fin (p : ℕ)) (μ : Fin (4 * ((1 : ℕ+) : ℕ))) : Fin (4 * (p : ℕ)) :=
  ⟨4 * (i : ℕ) + (μ : ℕ), by
    have hi := i.2
    have hμ := μ.2
    have hone := pnat_one_coe
    omega⟩
def coordBlock (j : Fin (4 * (p : ℕ))) : Fin (p : ℕ) :=
  ⟨(j : ℕ) / 4, by have := j.2; omega⟩
def coordOffset (j : Fin (4 * (p : ℕ))) : Fin (4 * ((1 : ℕ+) : ℕ)) :=
  ⟨(j : ℕ) % 4, by have hone := pnat_one_coe; omega⟩
theorem blockCoord_coordBlock_coordOffset (j : Fin (4 * (p : ℕ))) :
    blockCoord (coordBlock j) (coordOffset j) = j := by
  apply Fin.ext
  simp only [blockCoord, coordBlock, coordOffset]
  omega
def blockProduct (g : Fin (p : ℕ) → Coords 1 → ℂ) : Coords p → ℂ :=
  fun x => ∏ i, g i (blockPoint i x)
theorem blockPoint_add_single_same (i : Fin (p : ℕ)) (μ : Fin (4 * ((1 : ℕ+) : ℕ))) (x : Coords p)
    (t : ℝ) :
    blockPoint i (x + t • (Pi.single (blockCoord i μ) 1 : Coords p)) =
      blockPoint i x + t • (Pi.single μ 1 : Coords 1) := by
  funext ν
  have hone := pnat_one_coe
  have hν := ν.2
  have hμ := μ.2
  have hiff : (⟨4 * (i : ℕ) + (ν : ℕ), by have := i.2; omega⟩ : Fin (4 * (p : ℕ))) = blockCoord i μ ↔
      ν = μ := by
    constructor
    · intro e
      have e' := congrArg Fin.val e
      simp only [blockCoord] at e'
      exact Fin.ext (by omega)
    · rintro rfl
      rfl
  have hsingle : (Pi.single (blockCoord i μ) (1 : ℝ) : Fin (4 * (p : ℕ)) → ℝ)
        ⟨4 * (i : ℕ) + (ν : ℕ), by have := i.2; omega⟩ =
      (Pi.single μ (1 : ℝ) : Fin (4 * ((1 : ℕ+) : ℕ)) → ℝ) ν := by
    simp only [Pi.single_apply, hiff]
  show x ⟨4 * (i : ℕ) + (ν : ℕ), _⟩ + t * (Pi.single (blockCoord i μ) (1 : ℝ) :
        Fin (4 * (p : ℕ)) → ℝ) ⟨4 * (i : ℕ) + (ν : ℕ), _⟩ =
      x ⟨4 * (i : ℕ) + (ν : ℕ), _⟩ + t * (Pi.single μ (1 : ℝ) :
        Fin (4 * ((1 : ℕ+) : ℕ)) → ℝ) ν
  rw [hsingle]
theorem blockPoint_add_single_of_ne {i k : Fin (p : ℕ)} (hk : k ≠ i)
    (μ : Fin (4 * ((1 : ℕ+) : ℕ))) (x : Coords p) (t : ℝ) :
    blockPoint k (x + t • (Pi.single (blockCoord i μ) 1 : Coords p)) = blockPoint k x := by
  funext ν
  have hone := pnat_one_coe
  have hν := ν.2
  have hμ := μ.2
  have hne : (⟨4 * (k : ℕ) + (ν : ℕ), by have := k.2; omega⟩ : Fin (4 * (p : ℕ))) ≠
      blockCoord i μ := by
    intro e
    have e' := congrArg Fin.val e
    simp only [blockCoord] at e'
    exact hk (Fin.ext (by omega))
  simp [blockPoint, Coords.block, hne]
theorem partialAlong_blockProduct (g : Fin (p : ℕ) → Coords 1 → ℂ)
    (i : Fin (p : ℕ)) (μ : Fin (4 * ((1 : ℕ+) : ℕ))) :
    partialAlong (blockCoord i μ) (blockProduct g) =
      blockProduct (Function.update g i (partialAlong μ (g i))) := by
  funext x
  have hline : ∀ t : ℝ, blockProduct g (x + t • (Pi.single (blockCoord i μ) 1 : Coords p)) =
      g i (blockPoint i x + t • (Pi.single μ 1 : Coords 1)) *
        ∏ k ∈ Finset.univ.erase i, g k (blockPoint k x) := by
    intro t
    simp only [blockProduct]
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i), blockPoint_add_single_same]
    congr 1
    refine Finset.prod_congr rfl fun k hk => ?_
    rw [blockPoint_add_single_of_ne (Finset.ne_of_mem_erase hk)]
  have hright : blockProduct (Function.update g i (partialAlong μ (g i))) x =
      partialAlong μ (g i) (blockPoint i x) *
        ∏ k ∈ Finset.univ.erase i, g k (blockPoint k x) := by
    simp only [blockProduct]
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i), Function.update_self]
    congr 1
    refine Finset.prod_congr rfl fun k hk => ?_
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)]
  rw [hright]
  simp only [partialAlong, lineDeriv]
  simp only [hline]
  exact deriv_mul_const_field _
theorem iterate_partialAlong_blockProduct (g : Fin (p : ℕ) → Coords 1 → ℂ)
    (i : Fin (p : ℕ)) (μ : Fin (4 * ((1 : ℕ+) : ℕ))) (n : ℕ) :
    (partialAlong (blockCoord i μ))^[n] (blockProduct g) =
      blockProduct (Function.update g i ((partialAlong μ)^[n] (g i))) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, partialAlong_blockProduct,
      Function.update_idem, Function.update_self, Function.iterate_succ_apply']
def restrictToBlock (L : List (Fin (4 * (p : ℕ)))) (i : Fin (p : ℕ)) :
    List (Fin (4 * ((1 : ℕ+) : ℕ))) :=
  L.filterMap fun j => if coordBlock j = i then some (coordOffset j) else none
theorem foldr_partialAlong_blockProduct (a : Fin (4 * (p : ℕ)) → ℕ) (g : Fin (p : ℕ) → Coords 1 → ℂ)
    (L : List (Fin (4 * (p : ℕ)))) :
    L.foldr (fun j H => (partialAlong j)^[a j] H) (blockProduct g) =
      blockProduct fun i => (restrictToBlock L i).foldr
        (fun μ H => (partialAlong μ)^[a (blockCoord i μ)] H) (g i) := by
  induction L with
  | nil => simp [restrictToBlock]
  | cons j L ih =>
    rw [List.foldr_cons, ih]
    conv_lhs => rw [← blockCoord_coordBlock_coordOffset j]
    rw [iterate_partialAlong_blockProduct]
    congr 1
    funext i
    by_cases h : coordBlock j = i
    · subst h
      simp only [restrictToBlock, List.filterMap_cons, if_true, Function.update_self,
        blockCoord_coordBlock_coordOffset, List.foldr_cons]
    · have h' : i ≠ coordBlock j := fun e => h e.symm
      simp [restrictToBlock, h, h']
theorem restrictToBlock_finRange (i : Fin (p : ℕ)) :
    restrictToBlock (List.finRange (4 * (p : ℕ))) i = List.finRange (4 * ((1 : ℕ+) : ℕ)) := by
  have hone := pnat_one_coe
  refine List.SortedLT.eq_of_mem_iff ?_ (List.sortedLT_finRange _) ?_
  · apply List.Pairwise.sortedLT
    refine List.Pairwise.filterMap _ ?_ (List.sortedLT_finRange _).pairwise
    intro a b hab c hc d hd
    simp only [Option.ite_none_right_eq_some, Option.some.injEq] at hc hd
    obtain ⟨ha, rfl⟩ := hc
    obtain ⟨hb, rfl⟩ := hd
    have ea := congrArg Fin.val ha
    have eb := congrArg Fin.val hb
    simp only [coordBlock] at ea eb
    show (a : ℕ) % 4 < (b : ℕ) % 4
    omega
  · intro μ
    simp only [restrictToBlock, List.mem_filterMap, List.mem_finRange, true_and, iff_true]
    refine ⟨blockCoord i μ, ?_⟩
    have hμ := μ.2
    have eblock : coordBlock (blockCoord i μ) = i := by
      apply Fin.ext
      simp only [coordBlock, blockCoord]
      omega
    have eoffset : coordOffset (blockCoord i μ) = μ := by
      apply Fin.ext
      simp only [coordOffset, blockCoord]
      omega
    simp [eblock, eoffset]
theorem contDiff_blockPoint (ν : ℕ) (i : Fin (p : ℕ)) :
    ContDiff ℝ ν (blockPoint i : Coords p → Coords 1) :=
  contDiff_pi.2 fun _ => contDiff_apply ℝ ℝ _
theorem iteratedPartialsOfBlockProduct_holds (hcd : ContPartialsIffContDiff) :
    IteratedPartialsOfBlockProduct := by
  intro p ν g hg
  refine ⟨?_, fun α _ => ?_⟩
  · refine (hcd p ν _).2 ?_
    exact contDiff_prod fun i _ => ((hcd 1 ν (g i)).1 (hg i)).comp (contDiff_blockPoint ν i)
  · have key := foldr_partialAlong_blockProduct α g (List.finRange (4 * (p : ℕ)))
    simp only [restrictToBlock_finRange] at key
    exact key
end YangMills.Construction.PeriodicSpace.PartialDerivatives
