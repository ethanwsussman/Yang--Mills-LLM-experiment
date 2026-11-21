import YangMills.Construction.Cumulants.CumulantsMomentsAndCentredMomentsProof
import YangMills.Construction.Cumulants.NonSingletonPartitions
import YangMills.Construction.LimitsOfLatticeFamilies.BoundFunctionsHierarchiesAndLimitData
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.LatticeLimits
namespace ModelSpace
variable (s : Conventions.StandingParameters) (Y : ModelSpace)
def tensorProd {q : ℕ} {E : Type*} [CommMonoid E] (f : Fin q → Y.Carrier s → E) :
    (Fin q → Y.Carrier s) → E :=
  fun y => ∏ l, f l (y l)
abbrev CFun (q : ℕ) : Type := (Fin q → Y.Carrier s) → ℂ
def cTensor {q : ℕ} (f : FunTuple s Y q) : CFun s Y q :=
  fun y => ((tensorProd s Y f y : ℝ) : ℂ)
def sepTensors (q : ℕ) (ρ : ℝ≥0∞) : Submodule ℂ (CFun s Y q) :=
  Submodule.span ℂ (cTensor s Y '' sepTuplesIn s Y q ρ)
abbrev sepTensorsTop (q : ℕ) : Submodule ℂ (CFun s Y q) :=
  sepTensors s Y q ⊤
def cfunZeroEquiv : CFun s Y 0 ≃ₗ[ℂ] ℂ :=
  LinearEquiv.funUnique (Fin 0 → Y.Carrier s) ℂ ℂ
theorem sepTensors_zero (ρ : ℝ≥0∞) : sepTensors s Y 0 ρ = ⊤ := by
  rw [eq_top_iff]
  intro g _
  have hone : cTensor s Y (fun i => i.elim0) ∈ sepTensors s Y 0 ρ :=
    Submodule.subset_span ⟨_, by simp [sepTuplesIn_zero], rfl⟩
  have hg : g = g (fun i => i.elim0) • cTensor s Y (fun i => i.elim0) := by
    funext y
    have hy : y = fun i => i.elim0 := Subsingleton.elim _ _
    simp [cTensor, tensorProd, hy]
  rw [hg]
  exact Submodule.smul_mem _ _ hone
abbrev FunctionalSeq (ρ : ℝ≥0∞) : Type :=
  (n : ℕ) → TupleFunctional (sepTuplesIn s Y n ρ)
variable {s Y}
def IsMultilinearSeq {ρ : ℝ≥0∞} (Ψ : FunctionalSeq s Y ρ) : Prop :=
  ∀ n, 2 ≤ n → IsMultilinearSep (Ψ n)
def restrictTuple {q : ℕ} (h : FunTuple s Y q) (B : Finset (Fin q)) : FunTuple s Y B.card :=
  fun i => h (B.orderEmbOfFin rfl i)
theorem restrictTuple_mem {q : ℕ} {ρ : ℝ≥0∞} {h : FunTuple s Y q} (hh : h ∈ sepTuplesIn s Y q ρ)
    (B : Finset (Fin q)) : restrictTuple h B ∈ sepTuplesIn s Y B.card ρ :=
  ⟨⟨fun _ => hh.1.1 _, fun _ => hh.1.2.1 _,
    fun _ _ hik => hh.1.2.2 _ _ fun e => hik ((B.orderEmbOfFin rfl).injective e)⟩,
    fun _ => hh.2 _⟩
theorem mem_nonSingletonPartitions_iff {q : ℕ}
    (π : Finpartition (Finset.univ : Finset (Fin q))) :
    π ∈ SetPartition.nonSingletonPartitions q ↔ ∀ B ∈ π.parts, B.card ≠ 1 := by
  simp only [SetPartition.nonSingletonPartitions, Finset.mem_filter, Finset.mem_univ, true_and]
  refine forall₂_congr fun B hB => ?_
  have := (π.nonempty_of_mem_parts hB).card_pos
  omega
theorem finpartition_fin_zero_parts (π : Finpartition (Finset.univ : Finset (Fin 0))) :
    π.parts = ∅ := by apply _root_.YangMills.Construction.Cumulants.MomentCumulantFormulas.parts_eq_of_fin_zero <;> assumption
theorem nonSingletonPartitions_zero :
    ∃ π, SetPartition.nonSingletonPartitions 0 = {π} ∧ π.parts = ∅ := by
  refine ⟨⊥, ?_, finpartition_fin_zero_parts _⟩
  ext π
  have hπ : π = ⊥ := Finpartition.ext (by
    rw [finpartition_fin_zero_parts, finpartition_fin_zero_parts])
  simp [mem_nonSingletonPartitions_iff, hπ]
def centredSum {ρ : ℝ≥0∞} (Ψ : FunctionalSeq s Y ρ) (q : ℕ) :
    TupleFunctional (sepTuplesIn s Y q ρ) :=
  fun h => ∑ π ∈ SetPartition.nonSingletonPartitions q,
    ∏ B ∈ π.parts, Ψ B.card ⟨restrictTuple h.1 B, restrictTuple_mem h.2 B⟩
theorem cTensor_mem {q : ℕ} {ρ : ℝ≥0∞} {h : FunTuple s Y q}
    (hh : h ∈ sepTuplesIn s Y q ρ) : cTensor s Y h ∈ sepTensors s Y q ρ :=
  Submodule.subset_span ⟨h, hh, rfl⟩
def IsCentredLinearForm {ρ : ℝ≥0∞} (Ψ : FunctionalSeq s Y ρ) (q : ℕ)
    (Λ : sepTensors s Y q ρ →ₗ[ℂ] ℂ) : Prop :=
  ∀ (h : FunTuple s Y q) (hh : h ∈ sepTuplesIn s Y q ρ),
    Λ ⟨cTensor s Y h, cTensor_mem hh⟩ = (centredSum Ψ q ⟨h, hh⟩ : ℂ)
def centredLinearForm {ρ : ℝ≥0∞} (Ψ : FunctionalSeq s Y ρ) :
    (q : ℕ) → sepTensors s Y q ρ →ₗ[ℂ] ℂ
  | 0 => (cfunZeroEquiv s Y).toLinearMap ∘ₗ (sepTensors s Y 0 ρ).subtype
  | q + 1 => Classical.epsilon (IsCentredLinearForm Ψ (q + 1))
variable (s Y)
variable {s Y}
end ModelSpace
open ModelSpace
variable {s : Conventions.StandingParameters} {Y : ModelSpace}
def HierarchySequence.restrictSeq (P : HierarchySequence s Y) (j : ℕ) :
    FunctionalSeq s Y (P.rad j) :=
  fun n h => (P.phi j n).extend h.1
end YangMills.Construction.LatticeLimits
end
