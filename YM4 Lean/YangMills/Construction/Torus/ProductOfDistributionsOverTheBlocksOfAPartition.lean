import YangMills.Construction.Cumulants.NumberOfBlocksAndImagesOfPartitions
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open SetPartition
namespace AmbientPoints
section OrderedBlocks
variable {n : ℕ} (π : PartitionsFin n)
def blockMin (J : π.parts) : Fin n := J.1.min' (π.nonempty_of_mem_parts J.2)
theorem blockMin_mem (J : π.parts) : blockMin π J ∈ J.1 := Finset.min'_mem _ _
theorem blockMin_injective : Function.Injective (blockMin π) := fun J J' h =>
  Subtype.ext (π.eq_of_mem_parts J.2 J'.2 (blockMin_mem π J) (h ▸ blockMin_mem π J'))
def blockMins : Finset (Fin n) := Finset.univ.image (blockMin π)
theorem card_blockMins : (blockMins π).card = blockCount π := by
  rw [blockMins, Finset.card_image_of_injective _ (blockMin_injective π)]
  simp [blockCount]
def blockMinOrdered (i : Fin (blockCount π)) : Fin n :=
  (blockMins π).orderEmbOfFin (card_blockMins π) i
theorem blockMinOrdered_strictMono : StrictMono (blockMinOrdered π) :=
  ((blockMins π).orderEmbOfFin (card_blockMins π)).strictMono
def orderedBlock (i : Fin (blockCount π)) : Finset (Fin n) := π.part (blockMinOrdered π i)
theorem orderedBlock_mem (i : Fin (blockCount π)) : orderedBlock π i ∈ π.parts :=
  π.part_mem.2 (Finset.mem_univ _)
theorem blockMin_orderedBlock (i : Fin (blockCount π)) :
    blockMin π ⟨orderedBlock π i, orderedBlock_mem π i⟩ = blockMinOrdered π i := by
  have hm : blockMinOrdered π i ∈ blockMins π := Finset.orderEmbOfFin_mem _ _ i
  obtain ⟨J, -, hJ⟩ := Finset.mem_image.1 hm
  have h : orderedBlock π i = J.1 :=
    π.part_eq_of_mem J.2 (hJ ▸ blockMin_mem π J)
  have h' : (⟨orderedBlock π i, orderedBlock_mem π i⟩ : π.parts) = J := Subtype.ext h
  rw [h', hJ]
theorem orderedBlock_injective : Function.Injective (orderedBlock π) := fun i i' h =>
  (blockMinOrdered_strictMono π).injective (by
    rw [← blockMin_orderedBlock, ← blockMin_orderedBlock]
    exact congrArg _ (Subtype.ext h))
theorem exists_orderedBlock_eq {J : Finset (Fin n)} (hJ : J ∈ π.parts) :
    ∃ i, orderedBlock π i = J := by
  have hm : blockMin π ⟨J, hJ⟩ ∈ blockMins π :=
    Finset.mem_image_of_mem _ (Finset.mem_univ _)
  rw [← Finset.mem_coe, ← Finset.range_orderEmbOfFin _ (card_blockMins π)] at hm
  obtain ⟨i, hi⟩ := hm
  refine ⟨i, π.part_eq_of_mem hJ ?_⟩
  change (blockMins π).orderEmbOfFin (card_blockMins π) i ∈ J
  rw [hi]
  exact blockMin_mem π ⟨J, hJ⟩
abbrev orderedBlockCard (i : Fin (blockCount π)) : ℕ := (orderedBlock π i).card
def blockMemberIndex (z : (i : Fin (blockCount π)) × Fin (orderedBlockCard π i)) : Fin n :=
  (orderedBlock π z.1).orderEmbOfFin rfl z.2
theorem blockMemberIndex_bijective : Function.Bijective (blockMemberIndex π) := by
  constructor
  · rintro ⟨i, a⟩ ⟨i', a'⟩ h
    have hi : i = i' := by
      refine orderedBlock_injective π (π.eq_of_mem_parts (orderedBlock_mem π i)
        (orderedBlock_mem π i') (Finset.orderEmbOfFin_mem _ rfl a) ?_)
      rw [show (orderedBlock π i).orderEmbOfFin rfl a = _ from h]
      exact Finset.orderEmbOfFin_mem _ rfl a'
    subst hi
    have ha : a = a' := ((orderedBlock π i).orderEmbOfFin rfl).injective h
    rw [ha]
  · intro m
    obtain ⟨i, hi⟩ := exists_orderedBlock_eq π (π.part_mem.2 (Finset.mem_univ m))
    have hm : m ∈ orderedBlock π i := hi ▸ π.mem_part_self.2 (Finset.mem_univ m)
    rw [← Finset.mem_coe, ← Finset.range_orderEmbOfFin _ rfl] at hm
    obtain ⟨a, ha⟩ := hm
    exact ⟨⟨i, a⟩, ha⟩
end OrderedBlocks
end AmbientPoints
end YangMills.Construction
