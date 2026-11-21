import YangMills.Construction.Continuum.SymbolsOfFourSpaceWithATimeAxis
import Mathlib
set_option autoImplicit false
open Matrix
open scoped NNReal ComplexOrder
noncomputable section
namespace YangMills.Construction.TimeAxisSymbols.MirrorPicture
open YangMills.Construction.TorusTransport YangMills.Construction.TorusTransport.TupleVectors
variable {D : TransportData}
theorem actAny_mem_sepTuples {f : (Fin 4 → ℝ) → Fin 4 → ℝ}
    (hf : IsEuclideanMotion f) {U V : Set (Fin 4 → ℝ)} (hUV : Set.MapsTo f U V) {t : FnTuple}
    (ht : t ∈ sepTuples D U) : actAny hf t ∈ sepTuples D V := by
  obtain ⟨-, -, -, -, hsub⟩ := (mem_sepTuples_iff D U t).mp ht
  obtain ⟨h1, h2, h3, h4, -⟩ := (mem_sepTuples_iff D Set.univ _).mp
    (actAny_mem_spaceTimeSymbols hf (sepTuples_mono D (Set.subset_univ U) ht))
  refine (mem_sepTuples_iff D V _).mpr ⟨h1, h2, h3, h4, fun i => ?_⟩
  have hpre : entrySupp D ((actAny hf t).2 i) =
      hf.toPerm.symm ⁻¹' entrySupp D (t.2 i) :=
    tsupport_comp_eq_preimage (t.2 i) (motionHomeomorph hf).symm
  rw [hpre]
  intro x hx
  have hm := hUV (hsub i hx)
  have hinv : f (hf.toPerm.symm x) = x := hf.toPerm.apply_symm_apply x
  rwa [hinv] at hm
def motionOnSep {f : (Fin 4 → ℝ) → Fin 4 → ℝ} (hf : IsEuclideanMotion f)
    {U V : Set (Fin 4 → ℝ)} (hUV : Set.MapsTo f U V) (X : SepTuple D U) :
    SepTuple D V :=
  ⟨actAny hf X.1, actAny_mem_sepTuples hf hUV X.2⟩
def motionOnSpan {f : (Fin 4 → ℝ) → Fin 4 → ℝ} (hf : IsEuclideanMotion f)
    {U V : Set (Fin 4 → ℝ)} (hUV : Set.MapsTo f U V) : SepSpan D U →ₗ[ℂ] SepSpan D V :=
  linExtend fun X => TupleVectors.basisVec (motionOnSep hf hUV X)
end YangMills.Construction.TimeAxisSymbols.MirrorPicture
end
