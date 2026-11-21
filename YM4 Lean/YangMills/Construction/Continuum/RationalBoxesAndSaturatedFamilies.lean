import YangMills.Construction.TorusOrFourSpace.BoxesStockOfSupportsAndFamilyOfTuples
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Continuum.RationalBoxes
def IsRatBox (B : Set (Fin 4 → ℝ)) : Prop :=
  ∃ a b : Fin 4 → ℚ, (∀ μ, a μ < b μ) ∧ B = univ.pi fun μ => Icc (a μ : ℝ) (b μ : ℝ)
def boxUnions : Set (Set (Fin 4 → ℝ)) :=
  {Q | ∃ (r : ℕ) (c : Fin r → Set (Fin 4 → ℝ)), (∀ i, IsRatBox (c i)) ∧ Q = ⋃ i, c i}
def c1Off (Q : Set (Fin 4 → ℝ)) : Set ((Fin 4 → ℝ) → ℝ) :=
  {f | TestFunctions.IsC1R4 f ∧ ∀ x, x ∉ Q → f x = 0}
def IsSaturatedFamily (D : boxUnions → Set ((Fin 4 → ℝ) → ℝ)) : Prop :=
  ∀ Q : boxUnions, D Q = (⋃ Q' : boxUnions, D Q') ∩ c1Off Q
open YangMills.Construction.PeriodicSpace
theorem isRatBox_iff_exists_box {B : Set (Fin 4 → ℝ)} :
    IsRatBox B ↔ ∃ c : RationalBox, B = c.toSet := by
  constructor
  · rintro ⟨a, b, h, rfl⟩
    exact ⟨⟨a, b, h⟩, rfl⟩
  · rintro ⟨c, rfl⟩
    exact ⟨c.lo, c.hi, c.lo_lt_hi, rfl⟩
theorem quotMap_euclidean_image (p : Params) (S : Set (Fin 4 → ℝ)) :
    Kind.quotMap p .euclidean '' S = S :=
  image_id S
theorem supportStock_euclidean_eq (p : Params) : Kind.supportStock p .euclidean = boxUnions := by
  ext Q
  constructor
  · rintro ⟨r, c, -, rfl⟩
    exact ⟨r, fun i => (c i).toSet, fun i => isRatBox_iff_exists_box.2 ⟨c i, rfl⟩,
      iUnion_congr fun i => quotMap_euclidean_image p _⟩
  · rintro ⟨r, c, hc, rfl⟩
    choose e he using fun i => isRatBox_iff_exists_box.1 (hc i)
    exact ⟨r, e, fun _ => trivial,
      iUnion_congr fun i => (he i).trans (quotMap_euclidean_image p _).symm⟩
end YangMills.Construction.Continuum.RationalBoxes
