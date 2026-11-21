import YangMills.Construction.TorusOrFourSpace.CutOffsOnAProductOfOpenSets
import YangMills.Construction.TorusOrFourSpace.FunctionsOfClassC1SupportsAndNorms
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicSpace.TensorOfSingles
open Kind
def Claim : Prop :=
  ∀ (P : Params) (Q : Kind) (p : ℕ+),
    (∀ (k : ℕ) (f : Fin (p : ℕ) → Q.Pt P → ℂ),
      (∀ i, Tuple.IsClassC P Q k (Tuple.ofSingle P Q (f i))) →
      Tuple.IsClassC P Q k (Tuple.tensorProd P Q f) ∧
      (∀ β : CoordIndex p, β.degree ≤ k →
        Tuple.partialDeriv P Q β (Tuple.tensorProd P Q f) =
          Tuple.tensorProd P Q fun i x =>
            Tuple.partialDeriv P Q
              (fun j => β ⟨4 * (i : ℕ) + (j : ℕ), by
              have hi := i.2
              have hj := j.2
              simp only [PNat.one_coe] at hj
              omega⟩)
              (Tuple.ofSingle P Q (f i)) fun _ => x) ∧
      Tuple.supportT P Q (Tuple.tensorProd P Q f) ⊆
        Tuple.boxSet P Q fun i => Kind.supportQ P Q (f i)) ∧
    (∀ (U : Fin (p : ℕ) → Set (Q.Pt P)) (f : Fin (p : ℕ) → Q.Pt P → ℂ),
      (∀ i, Kind.IsOpenQ P Q (U i)) →
        (∀ i, f i ∈ Tuple.singleTestFns P Q (U i)) →
          Tuple.tensorProd P Q f ∈
            Tuple.testFns P Q (Tuple.boxSet P Q U)) ∧
    ∀ (f : Fin (p : ℕ) → Q.Pt P → ℂ) (i : Fin (p : ℕ)) (g h : Q.Pt P → ℂ) (c : ℂ),
      Tuple.tensorProd P Q (Function.update f i (g + h)) =
          Tuple.tensorProd P Q (Function.update f i g) +
            Tuple.tensorProd P Q (Function.update f i h) ∧
        Tuple.tensorProd P Q (Function.update f i (c • g)) =
          c • Tuple.tensorProd P Q (Function.update f i g)
end YangMills.Construction.PeriodicSpace.TensorOfSingles
