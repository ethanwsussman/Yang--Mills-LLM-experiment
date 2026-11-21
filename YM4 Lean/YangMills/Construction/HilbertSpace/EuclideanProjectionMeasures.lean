import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace EuclideanSpectral
open Set
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
structure IsOrthProj [CompleteSpace H] (p : H →ₗ[ℂ] H) : Prop where
  idem : p ∘ₗ p = p
  symm : ∀ x y : H, inner ℂ (p x) y = inner ℂ x (p y)
structure IsUnitaryMap [CompleteSpace H] (U : H →ₗ[ℂ] H) : Prop where
  bijective : Function.Bijective U
  norm_map : ∀ x : H, ‖U x‖ = ‖x‖
def IsUnitaryMap.inv [CompleteSpace H] {U : H →ₗ[ℂ] H} (hU : IsUnitaryMap U) :
    H →ₗ[ℂ] H :=
  ((LinearEquiv.ofBijective U hU.bijective).symm : H →ₗ[ℂ] H)
abbrev BorelSubset (n : ℕ) : Type := {S : Set (EuclideanSpace ℝ (Fin n)) // MeasurableSet S}
def BorelSubset.univ (n : ℕ) : BorelSubset n := ⟨Set.univ, MeasurableSet.univ⟩
def BorelSubset.unionSeq {n : ℕ} (S : ℕ → BorelSubset n) : BorelSubset n :=
  ⟨⋃ k, (S k).1, MeasurableSet.iUnion fun k => (S k).2⟩
def BorelSubset.compl {n : ℕ} (S : BorelSubset n) : BorelSubset n :=
  ⟨Set.univ \ S.1, MeasurableSet.univ.diff S.2⟩
def diagValue [CompleteSpace H] {n : ℕ} (E : BorelSubset n → H →ₗ[ℂ] H) (x : H)
    (S : BorelSubset n) : ℂ :=
  inner ℂ x (E S x)
variable (H) in
structure ProjMeasure [CompleteSpace H] (n : ℕ) [NeZero n] where
  toFun : BorelSubset n → H →ₗ[ℂ] H
  isOrthProj : ∀ S, IsOrthProj (toFun S)
  univ_eq_id : toFun (BorelSubset.univ n) = LinearMap.id
  hasSum_diag : ∀ (x : H) (S : ℕ → BorelSubset n),
    Pairwise (fun k l => Disjoint (S k).1 (S l).1) →
      HasSum (fun k => diagValue toFun x (S k)) (diagValue toFun x (BorelSubset.unionSeq S))
namespace ProjMeasure
variable [CompleteSpace H] {n : ℕ} [NeZero n]
instance : CoeFun (ProjMeasure H n) fun _ => BorelSubset n → H →ₗ[ℂ] H := ⟨toFun⟩
def diag (E : ProjMeasure H n) (x : H) (S : BorelSubset n) : ℂ :=
  diagValue E.toFun x S
def IsNull (E : ProjMeasure H n) (S : BorelSubset n) : Prop :=
  E S = 0
def Supports (S : BorelSubset n) (E : ProjMeasure H n) : Prop :=
  E.IsNull S.compl
end ProjMeasure
end EuclideanSpectral
end YangMills.Construction
