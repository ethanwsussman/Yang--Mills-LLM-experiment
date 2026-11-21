import YangMills.Construction.InfiniteLattice.FunctionOfASetReadsOnlyItsBonds
import Mathlib
set_option autoImplicit false
open MeasureTheory
namespace YangMills.Construction.InfiniteLattice
theorem regionObservableReadsInteriorLinks_holds : RegionObservableReadsInteriorLinks := by
  intro a _ S F hF U U' hUU
  let 𝒜 : MeasurableSpace (GaugeField a) :=
    { MeasurableSet' := fun A => (U ∈ A ↔ U' ∈ A)
      measurableSet_empty := by simp
      measurableSet_compl := fun A h => not_congr h
      measurableSet_iUnion := fun f h => by
        simp only [Set.mem_iUnion]
        exact exists_congr h }
  have hle : regionSigma S ≤ 𝒜 := by
    refine iSup₂_le fun e he => ?_
    rintro _ ⟨A₀, -, rfl⟩
    have he' : U e = U' e := hUU e ((Link.mem_linksWithin_iff_liesIn e S).1 he)
    show U e ∈ A₀ ↔ U' e ∈ A₀
    rw [he']
  have hset : MeasurableSet[regionSigma S] (F ⁻¹' {F U}) :=
    (show Measurable[regionSigma S] F from hF.2) (measurableSet_singleton (F U))
  have hU' : U' ∈ F ⁻¹' {F U} := (hle _ hset).1 rfl
  exact (Set.mem_singleton_iff.1 hU').symm
end YangMills.Construction.InfiniteLattice
