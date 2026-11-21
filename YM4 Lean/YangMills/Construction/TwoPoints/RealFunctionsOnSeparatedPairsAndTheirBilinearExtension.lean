import YangMills.Construction.Continuum.ComplexComponentsOfSeparatedTuples
import YangMills.Construction.EuclideanFunctionals.TuplesIsometriesFreeSpaceAndMirrorOfFourSpace
import YangMills.Construction.TwoPoints.FormsOnPairsWithDisjointSupports
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PairFunctions
open EuclideanFunctionals (R4 FnList defaultMirrorData)
open ComplexTestFunctions (ComplexValued ofRealFun)
open TwoPoints (compactC1Complex DisjointSupports)
abbrev sepPairs : Set FnList := EuclideanFunctionals.sepN 2
def evalPair (S : sepPairs → ℝ) (φ ψ : R4 → ℝ) : ℝ :=
  ReflectionPositivity.AxisMirror.Ambient.evalOrZero (D := defaultMirrorData)
    (E := ReflectionPositivity.AxisMirror.Ambient.euclidean) S [φ, ψ]
theorem evalPair_of_mem (S : sepPairs → ℝ) {φ ψ : R4 → ℝ} (hmem : [φ, ψ] ∈ sepPairs) :
    evalPair S φ ψ = S ⟨[φ, ψ], hmem⟩ := dif_pos hmem
theorem mem_sepPairs_iff (φ ψ : R4 → ℝ) :
    [φ, ψ] ∈ sepPairs ↔ SeparatedTuples.IsC1c φ ∧
      SeparatedTuples.IsC1c ψ ∧ Disjoint (tsupport φ) (tsupport ψ) := by
  have hkey := SeparatedTuplesR4.isDisjointTuple_iff_mem_separatedAll defaultMirrorData [φ, ψ]
  constructor
  · intro hmem
    have htup := hkey.2
      (ReflectionPositivity.AxisMirror.Ambient.separatedN_subset_separatedAll _ _ 2 hmem)
    exact ⟨htup.1 φ (by simp), htup.1 ψ (by simp), by simpa using htup.2⟩
  · rintro ⟨hφ, hψ, hdisj⟩
    have hsep : [φ, ψ] ∈ ReflectionPositivity.AxisMirror.Ambient.separatedAll defaultMirrorData
        ReflectionPositivity.AxisMirror.Ambient.euclidean :=
      hkey.1 ⟨fun g hg => by
        rcases List.mem_cons.1 hg with rfl | hg
        · exact hφ
        · rcases List.mem_cons.1 hg with rfl | hg
          · exact hψ
          · exact absurd hg List.not_mem_nil, by simpa using hdisj⟩
    obtain ⟨k, hk⟩ := Set.mem_iUnion.1 hsep
    exact ⟨rfl, hk.2⟩
theorem swap_mem_sepPairs {φ ψ : R4 → ℝ} (hmem : [φ, ψ] ∈ sepPairs) : [ψ, φ] ∈ sepPairs := by
  obtain ⟨hφ, hψ, hdisj⟩ := (mem_sepPairs_iff φ ψ).1 hmem
  exact (mem_sepPairs_iff ψ φ).2 ⟨hψ, hφ, hdisj.symm⟩
theorem linComb_mem_sepPairs (c c' : ℝ) {φ φ' ψ : R4 → ℝ} (hmem : [φ, ψ] ∈ sepPairs)
    (hmem' : [φ', ψ] ∈ sepPairs) : [c • φ + c' • φ', ψ] ∈ sepPairs := by
  obtain ⟨hφ, hψ, hdisj⟩ := (mem_sepPairs_iff φ ψ).1 hmem
  obtain ⟨hφ', -, hdisj'⟩ := (mem_sepPairs_iff φ' ψ).1 hmem'
  have hsub : tsupport (c • φ + c' • φ') ⊆ tsupport φ ∪ tsupport φ' := by
    refine closure_minimal (fun x hx => ?_) ((isClosed_tsupport φ).union (isClosed_tsupport φ'))
    by_contra hnot
    simp only [Set.mem_union, not_or] at hnot
    have hz : φ x = 0 := image_eq_zero_of_notMem_tsupport hnot.1
    have hz' : φ' x = 0 := image_eq_zero_of_notMem_tsupport hnot.2
    exact hx (by simp [hz, hz'])
  refine (mem_sepPairs_iff _ ψ).2 ⟨⟨?_, ?_⟩, hψ, ?_⟩
  · exact (contDiff_const.smul hφ.1).add (contDiff_const.smul hφ'.1)
  · exact (hφ.2.union hφ'.2).of_isClosed_subset (isClosed_tsupport _) hsub
  · exact Disjoint.mono_left hsub (Set.disjoint_union_left.2 ⟨hdisj, hdisj'⟩)
def IsBilinearOnPairs (S : sepPairs → ℝ) : Prop :=
  ∀ (c c' : ℝ) (φ φ' ψ : R4 → ℝ), [φ, ψ] ∈ sepPairs → [φ', ψ] ∈ sepPairs →
    evalPair S (c • φ + c' • φ') ψ = c * evalPair S φ ψ + c' * evalPair S φ' ψ ∧
      evalPair S ψ (c • φ + c' • φ') = c * evalPair S ψ φ + c' * evalPair S ψ φ'
def realPartForm (S : sepPairs → ℝ) (u v : ComplexValued) : ℝ :=
  evalPair S (ComplexTestFunctions.rePart u) (ComplexTestFunctions.rePart v)
theorem realPartForm_ofRealFun (S : sepPairs → ℝ) (φ ψ : R4 → ℝ) :
    realPartForm S (ofRealFun φ) (ofRealFun ψ) = evalPair S φ ψ := by
  simp [realPartForm]
def complexExtension (S : sepPairs → ℝ) (u v : ComplexValued) : ℂ :=
  TwoPoints.complexifyForm (realPartForm S) u v
theorem complexExtension_eq (S : sepPairs → ℝ) (u v : ComplexValued) :
    complexExtension S u v =
      ((evalPair S (ComplexTestFunctions.rePart u) (ComplexTestFunctions.rePart v) -
          evalPair S (ComplexTestFunctions.imPart u) (ComplexTestFunctions.imPart v) : ℝ) : ℂ) +
        Complex.I * ((evalPair S (ComplexTestFunctions.rePart u) (ComplexTestFunctions.imPart v) +
          evalPair S (ComplexTestFunctions.imPart u) (ComplexTestFunctions.rePart v) : ℝ) : ℂ) := by
  have hre : ∀ g : ComplexValued,
      ComplexTestFunctions.rePart (TwoPoints.realPartFun g) = ComplexTestFunctions.rePart g := by
    intro g
    funext x
    simp [ComplexTestFunctions.rePart, TwoPoints.realPartFun]
  have him : ∀ g : ComplexValued,
      ComplexTestFunctions.rePart (TwoPoints.imagPartFun g) = ComplexTestFunctions.imPart g := by
    intro g
    funext x
    simp [ComplexTestFunctions.rePart, ComplexTestFunctions.imPart, TwoPoints.imagPartFun]
  simp only [complexExtension, TwoPoints.complexifyForm, realPartForm, hre, him]
theorem rePart_mem_isC1c {u : ComplexValued} (hu : u ∈ compactC1Complex) :
    SeparatedTuples.IsC1c (ComplexTestFunctions.rePart u) :=
  ⟨Complex.reCLM.contDiff.comp hu.1, hu.2.1.of_isClosed_subset (isClosed_tsupport _)
    (ComplexTupleComponents.tsupport_rePart_subset u)⟩
theorem imPart_mem_isC1c {u : ComplexValued} (hu : u ∈ compactC1Complex) :
    SeparatedTuples.IsC1c (ComplexTestFunctions.imPart u) :=
  ⟨Complex.imCLM.contDiff.comp hu.1, hu.2.1.of_isClosed_subset (isClosed_tsupport _)
    (ComplexTupleComponents.tsupport_imPart_subset u)⟩
theorem parts_mem_sepPairs {u v : ComplexValued} (hu : u ∈ compactC1Complex)
    (hv : v ∈ compactC1Complex) (hdisj : DisjointSupports u v) :
    [ComplexTestFunctions.rePart u, ComplexTestFunctions.rePart v] ∈ sepPairs ∧
      [ComplexTestFunctions.imPart u, ComplexTestFunctions.imPart v] ∈ sepPairs ∧
      [ComplexTestFunctions.rePart u, ComplexTestFunctions.imPart v] ∈ sepPairs ∧
      [ComplexTestFunctions.imPart u, ComplexTestFunctions.rePart v] ∈ sepPairs := by
  have hr := ComplexTupleComponents.tsupport_rePart_subset
  have hi := ComplexTupleComponents.tsupport_imPart_subset
  exact ⟨(mem_sepPairs_iff _ _).2 ⟨rePart_mem_isC1c hu, rePart_mem_isC1c hv, hdisj.mono (hr u) (hr v)⟩,
    (mem_sepPairs_iff _ _).2 ⟨imPart_mem_isC1c hu, imPart_mem_isC1c hv, hdisj.mono (hi u) (hi v)⟩,
    (mem_sepPairs_iff _ _).2 ⟨rePart_mem_isC1c hu, imPart_mem_isC1c hv, hdisj.mono (hr u) (hi v)⟩,
    (mem_sepPairs_iff _ _).2 ⟨imPart_mem_isC1c hu, rePart_mem_isC1c hv, hdisj.mono (hi u) (hr v)⟩⟩
end YangMills.Construction.PairFunctions
end
