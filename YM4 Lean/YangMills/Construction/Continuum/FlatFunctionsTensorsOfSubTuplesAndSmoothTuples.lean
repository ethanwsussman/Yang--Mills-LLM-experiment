import YangMills.Construction.Continuum.FlatSchwartzAndTuples
import YangMills.Construction.Continuum.FormsOfTheSeparatedTuplesOfFourSpaceTheirSpanAndFunctionals
import YangMills.Construction.Continuum.TestFunctionsOfConfigurationSpace
import YangMills.Construction.TestSpaces.PointsAndSeparatedTuples
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Set
open ReflectionPositivity.AxisMirror (Ambient)
open AmbientPoints
open scoped ContDiff
namespace FlatTensors
variable {n : ℕ}
abbrev flatSchwartz (n : ℕ) : Set (ConfigurationSpace.Config n → ℂ) :=
  ConfigurationSpace.flatSchwartzSet n
abbrev flatSchwartzDual (n : ℕ) : Set (flatSchwartz n → ℂ) :=
  ConfigurationSpace.flatSchwartzDualSet n
abbrev pointTensor {R : Type*} [CommMonoid R] (f : Fin n → (Fin 4 → ℝ) → R) :
    TestSpaces.PointTuple n → R :=
  TestSpaces.tensorProd f
def toComplexTuple {s : Conventions.StandingParameters} (f : Fin n → Pt s .euclidean → ℝ) :
    ConfigSpace.FnTuple n :=
  fun i x => ((f i x : ℝ) : ℂ)
def smoothSepTuples (s : Conventions.StandingParameters) :
    (n : ℕ) → Set (Fin n → Pt s .euclidean → ℝ)
  | 0 => {fun i => i.elim0}
  | 1 => {f | f ∈ separatedTuples s .euclidean 1 ∧
      ConfigSpace.SmoothEntries (toComplexTuple f)}
  | n + 2 => {f | toComplexTuple f ∈ ConfigSpace.smoothRealTupleSet (n + 2)}
variable {s : Conventions.StandingParameters}
theorem tsupport_ofReal_comp (g : (Fin 4 → ℝ) → ℝ) :
    tsupport (fun x => (g x : ℂ)) = tsupport g := by
  have h : Function.support (fun x => (g x : ℂ)) = Function.support g := by
    ext x
    simp
  simp only [tsupport, h]
theorem mem_separatedTuples_of_toComplexTuple {f : Fin n → Pt s .euclidean → ℝ}
    (h : toComplexTuple f ∈ ConfigSpace.realTupleSet n univ) :
    f ∈ separatedTuples s .euclidean n := by
  have hsupp : ∀ i, tsupport (toComplexTuple f i) = tsupport (fun x : Fin 4 → ℝ => f i x) :=
    fun i => tsupport_ofReal_comp _
  refine ⟨fun i => ⟨?_, ?_⟩, fun i j hij => ?_⟩
  · have hc := (h.1 i).2.1
    exact (isC1Fn_euclidean_iff (f i)).2 (Complex.reCLM.contDiff.comp hc)
  · have hc : HasCompactSupport (fun x : Fin 4 → ℝ => f i x) := by
      have := (h.1 i).2.2.1
      rw [HasCompactSupport, hsupp i] at this
      exact this
    exact (R4TupleForms.isCompact_tsupport_pt_iff_hasCompactSupport (s := s) _).2 hc
  · have hd := h.2 i j hij
    rw [hsupp i, hsupp j] at hd
    change Disjoint (tsupport (f i)) (tsupport (f j))
    rw [show tsupport (f i) = tsupport (fun x : Fin 4 → ℝ => f i x) from
        R4TupleForms.tsupport_pt_euclidean (s := s) _,
      show tsupport (f j) = tsupport (fun x : Fin 4 → ℝ => f j x) from
        R4TupleForms.tsupport_pt_euclidean (s := s) _]
    exact hd
theorem smoothSepTuples_subset_separatedTuples :
    ∀ n, smoothSepTuples s n ⊆ separatedTuples s .euclidean n
  | 0, f, hf => by
      rw [separatedTuples_zero]
      exact hf
  | 1, _, hf => hf.1
  | _ + 2, _, hf => mem_separatedTuples_of_toComplexTuple hf.1
end FlatTensors
end YangMills.Construction
