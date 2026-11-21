import YangMills.Construction.InfiniteLattice.DenseSequenceOfContinuousLocalFunctions
import YangMills.Construction.InfiniteLattice.FactsFromTopologyMeasureAndFunctionTheory
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.InfiniteLattice
open YangMills.Construction.FixedSpacing YangMills.Construction.InfiniteLattice.AmbientFacts
theorem cylinderFunctionsHaveDenseSequence_holds
    (hFacts : AmbientFacts.AllFacts) :
    CylinderFunctionsHaveDenseSequence := by
  intro D
  have hAll := hFacts.1 D
  have hProducts : CompactMetrizableProducts D.mesh := hAll.1
  have hCylinderDense : CylinderFunctionsDense D.mesh := hAll.2.1
  have hDense : IsSupDense (continuousCylinderFunctions D.mesh) := hCylinderDense.2
  have : CompactSpace (GaugeField D.mesh) := hProducts.2.1
  have : TopologicalSpace.MetrizableSpace (GaugeField D.mesh) := hProducts.2.2
  let _ := TopologicalSpace.metrizableSpaceMetric (GaugeField D.mesh)
  have : SecondCountableTopology (GaugeField D.mesh) := inferInstance
  let S : Set C(GaugeField D.mesh, ℂ) := {f | (f : GaugeField D.mesh → ℂ) ∈ cylinderAlgebra D.mesh}
  have : Nonempty S := ⟨⟨0, (cylinderAlgebra D.mesh).zero_mem⟩⟩
  obtain ⟨u, hu⟩ := TopologicalSpace.exists_dense_seq S
  refine ⟨fun k => ((u k.natPred : C(GaugeField D.mesh, ℂ)) : GaugeField D.mesh → ℂ),
    fun k => (u k.natPred).2, fun H ε hε => ?_⟩
  have hε3 : 0 < ε / 3 := by positivity
  obtain ⟨G, hG, hHG⟩ := hDense H H.continuous (ε / 3) hε3
  let G' : C(GaugeField D.mesh, ℂ) := ⟨G, hG.1⟩
  have hG' : ‖H - G'‖ ≤ ε / 3 := by
    refine (ContinuousMap.norm_le _ hε3.le).2 fun U => ?_
    have h1 : ‖(⇑H - G) U‖ₑ ≤ normSup (⇑H - G) :=
      le_iSup (fun U => ‖(⇑H - G) U‖ₑ) U
    have h2 : ENNReal.ofReal ‖(⇑H - G) U‖ < ENNReal.ofReal (ε / 3) := by
      rw [ofReal_norm]
      exact lt_of_le_of_lt h1 hHG
    exact ((ENNReal.ofReal_lt_ofReal_iff hε3).1 h2).le
  obtain ⟨n, hn⟩ := hu.exists_dist_lt (⟨G', hG⟩ : S) hε3
  have hn' : ‖G' - (u n : C(GaugeField D.mesh, ℂ))‖ < ε / 3 := by
    rw [← dist_eq_norm]
    exact hn
  refine ⟨n.succPNat, ?_⟩
  have hnat : n.succPNat.natPred = n := Nat.natPred_succPNat n
  have htotal : ‖H - (u n : C(GaugeField D.mesh, ℂ))‖ ≤ 2 * (ε / 3) := by
    have := norm_sub_le_norm_sub_add_norm_sub H G' (u n : C(GaugeField D.mesh, ℂ))
    linarith
  have hbound : observableSupNorm
      (fun U => H U - ((u n.succPNat.natPred : C(GaugeField D.mesh, ℂ)) : GaugeField D.mesh → ℂ) U)
        ≤ 2 * (ε / 3) := by
    rw [hnat]
    refine Real.iSup_le (fun U => ?_) (by positivity)
    exact ((H - (u n : C(GaugeField D.mesh, ℂ))).norm_coe_le_norm U).trans htotal
  linarith
end YangMills.Construction.InfiniteLattice
