import YangMills.Construction.ReflectionPositivity.IsometriesCentringTuplesAndTheTwoFunctionals
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction
namespace SetPartition
variable {α β : Type*} [DecidableEq α] [DecidableEq β]
def blockCount {S : Finset α} (π : Partitions S) : ℕ := π.parts.card
def blockImage {S : Finset α} {T : Finset β} (e : S ≃ T) (B : Finset α) : Finset β :=
  (S.attach.filter fun i : S => (i : α) ∈ B).image fun i => (e i : β)
def partitionImage {S : Finset α} {T : Finset β} (e : S ≃ T) (π : Partitions S) :
    Finset (Finset β) :=
  π.parts.image (blockImage e)
theorem mem_blockImage {S : Finset α} {T : Finset β} (e : S ≃ T) (B : Finset α) (y : β) :
    y ∈ blockImage e B ↔ ∃ i : S, (i : α) ∈ B ∧ (e i : β) = y := by
  simp [blockImage]
theorem mem_partitionImage {S : Finset α} {T : Finset β} (e : S ≃ T) (π : Partitions S)
    (C : Finset β) : C ∈ partitionImage e π ↔ ∃ B ∈ π.parts, blockImage e B = C := by
  simp [partitionImage]
end SetPartition
end YangMills.Construction
