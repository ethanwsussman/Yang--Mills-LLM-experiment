import YangMills.Construction.InfiniteLattice.ObservablesHypercubicLatticeMapsAndHyperplanes
import YangMills.Construction.ReflectionPositivity.SeparatedTuples
import YangMills.Construction.Torus.SeparatedTuplesAndIsometriesOfTorusOrFourSpace
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open AmbientPoints
namespace FourSpaceSymbols
variable (s : Conventions.StandingParameters)
abbrev SymTuple : Type := FunctionTuple s .euclidean
def symbolSet : Set (SymTuple s) := allSeparatedTuples s .euclidean
abbrev Symbol : Type := ↥(symbolSet s)
variable {s}
def Symbol.length (X : Symbol s) : ℕ := X.1.1
def Symbol.entry (X : Symbol s) (i : Fin X.length) : Pt s .euclidean → ℝ := X.1.2 i
def transportSymTuple (g : Pt s .euclidean ≃ Pt s .euclidean) (T : SymTuple s) : SymTuple s :=
  ⟨T.1, transportTuple g T.2⟩
def toIsometryEquiv {g : Pt s .euclidean ≃ Pt s .euclidean} (hg : IsDistIsometry g) :
    Pt s .euclidean ≃ᵢ Pt s .euclidean :=
  ⟨g, Isometry.of_dist_eq hg⟩
theorem isDistIsometry_symm {g : Pt s .euclidean ≃ Pt s .euclidean} (hg : IsDistIsometry g) :
    IsDistIsometry g.symm := fun x y => by
  rw [← hg (g.symm x) (g.symm y), g.apply_symm_apply, g.apply_symm_apply]
def symmOnVectors (g : Pt s .euclidean ≃ Pt s .euclidean) : (Fin 4 → ℝ) → Fin 4 → ℝ :=
  g.symm
theorem contDiff_symmOnVectors {g : Pt s .euclidean ≃ Pt s .euclidean}
    (hg : IsDistIsometry g) : ContDiff ℝ 1 (symmOnVectors g) :=
  ReflectionPositivity.EuclidIsometry.contDiff_toFun
    ⟨symmOnVectors g, fun x y => isDistIsometry_symm hg x y⟩
theorem tsupport_transportFn {g : Pt s .euclidean ≃ Pt s .euclidean}
    (hg : IsDistIsometry g) (f : Pt s .euclidean → ℝ) :
    tsupport (transportFn g f) = g.symm ⁻¹' tsupport f :=
  tsupport_comp_eq_preimage f (toIsometryEquiv hg).toHomeomorph.symm
theorem transportSymTuple_mem {g : Pt s .euclidean ≃ Pt s .euclidean} (hg : IsDistIsometry g)
    (X : Symbol s) : transportSymTuple g X.1 ∈ symbolSet s := by
  have regX : ∀ i, IsC1Fn (X.entry i) ∧ IsCompact (tsupport (X.entry i)) := X.2.1
  have disjX : Pairwise fun i j => Disjoint (tsupport (X.entry i)) (tsupport (X.entry j)) := X.2.2
  refine ⟨fun i => ⟨?_, ?_⟩, fun i j hne => ?_⟩
  · have hsmooth : ContDiff ℝ 1 (fun x : Fin 4 → ℝ => X.entry i x) :=
      (isC1Fn_euclidean_iff _).1 (regX i).1
    exact (isC1Fn_euclidean_iff _).2 (hsmooth.comp (contDiff_symmOnVectors hg))
  · change IsCompact (tsupport (transportFn g (X.entry i)))
    rw [tsupport_transportFn hg]
    exact (toIsometryEquiv hg).toHomeomorph.symm.isCompact_preimage.2 (regX i).2
  · change Disjoint (tsupport (transportFn g (X.entry i)))
      (tsupport (transportFn g (X.entry j)))
    rw [tsupport_transportFn hg, tsupport_transportFn hg]
    exact (disjX hne).preimage _
def transportSymbol {g : Pt s .euclidean ≃ Pt s .euclidean} (hg : IsDistIsometry g)
    (X : Symbol s) : Symbol s :=
  ⟨transportSymTuple g X.1, transportSymTuple_mem hg X⟩
variable (s) in
def translationEquiv (v : Fin 4 → ℝ) : Pt s .euclidean ≃ Pt s .euclidean where
  toFun := InfiniteLattice.shiftMap v
  invFun := InfiniteLattice.shiftMap (-v)
  left_inv := fun x : Fin 4 → ℝ => add_neg_cancel_right x v
  right_inv := fun x : Fin 4 → ℝ => neg_add_cancel_right x v
theorem isDistIsometry_translationEquiv (v : Fin 4 → ℝ) :
    IsDistIsometry (translationEquiv s v) := fun (x y : Fin 4 → ℝ) => by
  change TorusMetric.euclidNormVec (x + v - (y + v)) = TorusMetric.euclidNormVec (x - y)
  rw [add_sub_add_right_eq_sub]
def translateFn {E : Type*} (v : Fin 4 → ℝ) (f : Pt s .euclidean → E) :
    Pt s .euclidean → E :=
  transportFn (translationEquiv s v) f
theorem translateFn_apply {E : Type*} (v : Fin 4 → ℝ) (f : Pt s .euclidean → E)
    (x : Fin 4 → ℝ) : translateFn v f x = f (x - v) := by
  change f (InfiniteLattice.shiftMap (-v) x) = f (x - v)
  simp [InfiniteLattice.shiftMap, sub_eq_add_neg]
def translateSymbol (v : Fin 4 → ℝ) (X : Symbol s) : Symbol s :=
  transportSymbol (isDistIsometry_translationEquiv v) X
def FamilyAdmissible {k : ℕ} (d R : ℝ) (A : Fin k → Set (Pt s .euclidean)) : Prop :=
  (∀ i, ∃ x, A i ⊆ closedBall s .euclidean x R) ∧
    ∀ i i', i ≠ i' → ENNReal.ofReal d ≤ setDist s .euclidean (A i) (A i')
def TupleAdmissible (d R : ℝ) (T : SymTuple s) : Prop :=
  FamilyAdmissible d R fun i => tsupport (T.2 i)
end FourSpaceSymbols
end YangMills.Construction
end
