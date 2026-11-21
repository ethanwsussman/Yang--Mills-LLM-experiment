import YangMills.Construction.Torus.MultilinearFunctionalsOnSeparatedTuplesOfTorusOrFourSpace
import YangMills.Construction.TorusOrFourSpace.ConvergenceOnSeparatedTuplesAndPartialHierarchies
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.PeriodicSpace
theorem two_le_card_of_mem_singletonFree {q : ℕ} {π : SetPartition.PartitionsFin q}
    (hπ : π ∈ SetPartition.singletonFree q) {I : Finset (Fin q)} (hI : I ∈ π.parts) :
    2 ≤ I.card := by apply _root_.YangMills.Construction.AmbientPoints.two_le_card_of_mem_singletonFree <;> assumption
namespace BoundFamily
def momentBound (C : BoundFamily) (q : ℕ) (d R : ℝ) : ℝ :=
  ∑ π ∈ SetPartition.singletonFree q, ∏ I ∈ π.parts, C.val I.card d R
end BoundFamily
namespace Kind
variable (D : Params) (E : Kind)
theorem restrictTuple_mem_sepLipTuplesWithin {n : ℕ} {O : Set (E.Pt D)} {f : FnTuple D E n}
    (hf : f ∈ sepLipTuplesWithin D E n O) (J : Finset (Fin n)) :
    restrictTuple D E f J ∈ sepLipTuplesWithin D E J.card O :=
  ⟨⟨fun _ => hf.1.1 _, fun _ => hf.1.2.1 _,
    fun _ _ hik => hf.1.2.2 _ _ ((J.orderEmbOfFin rfl).injective.ne hik)⟩, fun _ => hf.2 _⟩
structure FunctionalSystem where
  domain : (n : ℕ) → 2 ≤ n → Set (FnTuple D E n)
  eval : (n : ℕ) → (hn : 2 ≤ n) → domain n hn → ℝ
namespace FunctionalSystem
variable {D E}
def Defined (Φ : FunctionalSystem D E) {q : ℕ} (f : FnTuple D E q) : Prop :=
  ∀ (I : Finset (Fin q)) (hI : 2 ≤ I.card), restrictTuple D E f I ∈ Φ.domain I.card hI
def momentSum (Φ : FunctionalSystem D E) {q : ℕ} (f : FnTuple D E q) (hf : Φ.Defined f) : ℝ :=
  ∑ π ∈ (SetPartition.singletonFree q).attach, ∏ I ∈ π.1.parts.attach,
    Φ.eval I.1.card (two_le_card_of_mem_singletonFree π.2 I.2)
      ⟨restrictTuple D E f I.1, hf I.1 (two_le_card_of_mem_singletonFree π.2 I.2)⟩
theorem defined_of_mem_sepC1Tuples (Φ : FunctionalSystem D E)
    (hΦ : ∀ (n : ℕ) (hn : 2 ≤ n), sepC1Tuples D E n ⊆ Φ.domain n hn) {q : ℕ}
    {f : FnTuple D E q} (hf : f ∈ sepC1Tuples D E q) : Φ.Defined f :=
  fun I hI => hΦ I.card hI (restrictTuple_mem_sepC1Tuples D E hf I)
end FunctionalSystem
namespace Hierarchy
variable {D E}
def toFunctionalSystem (Φ : Hierarchy D E) : FunctionalSystem D E where
  domain n _ := sepC1Tuples D E n
  eval := Φ.func
theorem defined_of_mem_sepC1Tuples (Φ : Hierarchy D E) {q : ℕ} {f : FnTuple D E q}
    (hf : f ∈ sepC1Tuples D E q) : Φ.toFunctionalSystem.Defined f :=
  Φ.toFunctionalSystem.defined_of_mem_sepC1Tuples (fun _ _ _ h => h) hf
end Hierarchy
namespace PartialHierarchySeq
variable {D E} {J₀ : Sequences.PNatIndexSet} {ρ : J₀.carrier → ℝ≥0∞}
def toFunctionalSystem (Φ : PartialHierarchySeq D E J₀ ρ) (j : J₀.carrier) :
    FunctionalSystem D E where
  domain n _ := sepLipTuplesWithin D E n (centredBall D E (ρ j))
  eval := Φ.func j
theorem defined_of_mem_sepLipTuplesWithin (Φ : PartialHierarchySeq D E J₀ ρ)
    (j : J₀.carrier) {q : ℕ} {f : FnTuple D E q}
    (hf : f ∈ sepLipTuplesWithin D E q (centredBall D E (ρ j))) :
    (Φ.toFunctionalSystem j).Defined f :=
  fun I _ => restrictTuple_mem_sepLipTuplesWithin D E hf I
end PartialHierarchySeq
end Kind
end YangMills.Construction.PeriodicSpace
