import YangMills.Construction.ToriAtArbitraryCouplings.ClassesOfFunctionsSeparatedTuplesAndTheSeparation
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.ToriAtArbitraryCouplings
open YangMills.Construction.ReflectionPositivity.AxisMirror (Ambient)
namespace TorusSide
variable (s : TorusSide)
def PairwisePosSeparated (E : Ambient) {n : ℕ} (A : Fin n → Set (s.Point E)) : Prop :=
  Pairwise fun i j => s.PositivelySeparated E (A i) (A j)
variable {s} in
theorem PairwisePosSeparated.disjoint {E : Ambient} {n : ℕ} {A : Fin n → Set (s.Point E)}
    (hA : s.PairwisePosSeparated E A) {i k : Fin n} (hik : i ≠ k) :
    Disjoint (A i) (A k) := by
  refine Ambient.disjoint_of_setDist_pos s.asMirrorData E ?_
  have hpos := hA hik
  cases E
  · exact hpos
  · exact hpos
def IsMultilinearOnProd (E : Ambient) {n : ℕ} {S : Set (s.FnTuple E)} (Ψ : S → ℝ)
    (C : Fin n → Set (s.Point E → ℝ)) : Prop :=
  ∀ u : Fin n → s.Point E → ℝ, (∀ i, u i ∈ C i) →
    ∀ (i : Fin n) (v : s.Point E → ℝ), v ∈ C i → ∀ a b : ℝ,
      Ambient.evalOrZero Ψ (List.ofFn (Function.update u i (a • u i + b • v))) =
        a * Ambient.evalOrZero Ψ (List.ofFn u) +
          b * Ambient.evalOrZero Ψ (List.ofFn (Function.update u i v))
theorem isSeparatedMultilinear_iff (E : Ambient) {n : ℕ} (Ψ : s.sepOfLength E n → ℝ) :
    Ambient.IsSeparatedMultilinear s.asMirrorData E Ψ ↔
      ∀ A : Fin n → Set (s.Point E), s.PairwisePosSeparated E A →
        s.IsMultilinearOnProd E Ψ fun i => s.c1SuppIn E (A i) := by
  have hsep : ∀ A : Fin n → Set (s.Point E), s.PairwisePosSeparated E A ↔
      Pairwise fun i j => 0 < Ambient.setDist s.asMirrorData E (A i) (A j) := by
    intro A
    cases E
    · exact Iff.rfl
    · exact Iff.rfl
  simp only [hsep, IsMultilinearOnProd, c1SuppIn_eq_compactC1SuppIn]
  exact Iff.rfl
theorem ofFn_mem_lipDisjointOfLength {E : Ambient} {n : ℕ} {A : Fin n → Set (s.Point E)}
    (hA : s.PairwisePosSeparated E A) {u : Fin n → s.Point E → ℝ}
    (hu : ∀ i, u i ∈ s.lipSuppIn E (A i)) : List.ofFn u ∈ s.lipDisjointOfLength E n :=
  (s.ofFn_mem_lipDisjointOfLength_iff E u).2 ⟨fun i => (hu i).1, fun i => (hu i).2.1,
    fun _ _ hik => (hA.disjoint hik).mono (hu _).2.2 (hu _).2.2⟩
def IsMultilinearOnLip (E : Ambient) {n : ℕ} (Ψ : s.lipDisjointOfLength E n → ℝ) : Prop :=
  ∀ A : Fin n → Set (s.Point E), s.PairwisePosSeparated E A →
    s.IsMultilinearOnProd E Ψ fun i => s.lipSuppIn E (A i)
def IsPermInvariant (E : Ambient) {n : ℕ} {S : Set (s.FnTuple E)} (Ψ : S → ℝ) : Prop :=
  ∀ (u : Fin n → s.Point E → ℝ) (σ : Equiv.Perm (Fin n)) (h : List.ofFn u ∈ S)
    (h' : List.ofFn (u ∘ σ) ∈ S), Ψ ⟨_, h'⟩ = Ψ ⟨_, h⟩
theorem comp_perm_mem_sepOfLength {E : Ambient} {n : ℕ} {u : Fin n → s.Point E → ℝ}
    (hu : List.ofFn u ∈ s.sepOfLength E n) (σ : Equiv.Perm (Fin n)) :
    List.ofFn (u ∘ σ) ∈ s.sepOfLength E n := by
  have hp := Equiv.Perm.ofFn_comp_perm σ u
  exact ⟨hp.length_eq.trans hu.1, fun v hv => hu.2.1 v (hp.mem_iff.1 hv),
    (hp.pairwise_iff fun h => Disjoint.symm h).2 hu.2.2⟩
end TorusSide
end YangMills.Construction.ToriAtArbitraryCouplings
end
