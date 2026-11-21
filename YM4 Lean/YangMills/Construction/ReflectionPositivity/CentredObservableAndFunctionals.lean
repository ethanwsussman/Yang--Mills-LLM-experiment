import YangMills.Construction.Cumulants.NonSingletonPartitions
import YangMills.Construction.ReflectionPositivity.SeparatedTuplesAndFunctionals
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.AxisMirror
namespace MirrorData
variable (D : MirrorData)
def centeredObservable (f : D.Torus → ℝ)
    (U : PeriodicLattice.Bond D.L D.m ((D.K : ℕ) : ℤ) → Matrices.ComplexMatrix2) : ℝ :=
  PeriodicLattice.smearedObservable f U -
    PeriodicLattice.gibbsExpectation D.L D.m D.K D.β (PeriodicLattice.smearedObservable f)
def latticeMoment (fs : List (D.Torus → ℝ)) : ℝ :=
  PeriodicLattice.gibbsExpectation D.L D.m D.K D.β fun U =>
    (fs.map fun f => D.centeredObservable f U).prod
end MirrorData
namespace Ambient
variable {D : MirrorData} {E : Ambient}
def subList {α : Type*} (xs : List α) (J : Finset (Fin xs.length)) : List α :=
  List.ofFn fun k : Fin J.card => xs.get (J.orderEmbOfFin rfl k)
theorem subList_mem_separatedN {xs : FnList D E} (hxs : IsSeparatedList D E xs)
    (J : Finset (Fin xs.length)) : subList xs J ∈ separatedN D E J.card := by
  refine ⟨List.length_ofFn, ?_, ?_⟩
  · intro g hg
    obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hg
    exact hxs.1 _ (List.get_mem _ _)
  · rw [subList, List.pairwise_ofFn]
    intro i j hij
    exact List.pairwise_iff_get.1 hxs.2 _ _ ((J.orderEmbOfFin rfl).strictMono hij)
namespace ConnectedFamily
variable (S : ConnectedFamily D E)
def evalAt (n : ℕ) (ys : FnList D E) : ℝ :=
  open Classical in if h : 2 ≤ n then evalOrZero (S.fn n h) ys else 0
theorem evalAt_of_mem {n : ℕ} (h : 2 ≤ n) {ys : FnList D E} (hys : ys ∈ separatedN D E n) :
    S.evalAt n ys = S.fn n h ⟨ys, hys⟩ := by
  simp [evalAt, h, evalOrZero, hys]
def centeredFunctional (xs : separatedAll D E) : ℝ :=
  ∑ π ∈ SetPartition.nonSingletonPartitions xs.1.length,
    ∏ J ∈ π.parts, S.evalAt J.card (subList xs.1 J)
end ConnectedFamily
end Ambient
end YangMills.Construction.ReflectionPositivity.AxisMirror
