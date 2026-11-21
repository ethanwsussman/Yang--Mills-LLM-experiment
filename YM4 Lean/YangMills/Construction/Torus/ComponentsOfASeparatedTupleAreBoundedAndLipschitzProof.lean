import YangMills.Construction.Torus.ComponentsOfASeparatedTupleAreBoundedAndLipschitz
import YangMills.Construction.Torus.GradientNormLipschitzConstantAndSharpNorm
import Mathlib
set_option autoImplicit false
open YangMills.Construction.ReflectionPositivity.AxisMirror (Ambient)
namespace YangMills.Construction.AmbientPoints
theorem sepTupleComponentsBoundedLipschitz_holds
    (hGrad : GradientC1Bounds.Statement) :
    SepTupleEntriesBoundedLipschitz := by
  intro s E n f hf i
  have hC1 : IsCnAtPoint 1 (fun x => ((f i x : ℝ) : ℂ)) := hf.1 i
  have hCpt : IsCompact (closedSupport (ofSinglePoint fun x => ((f i x : ℝ) : ℂ))) := by
    have hSupp : closedSupport (ofSinglePoint fun x => ((f i x : ℝ) : ℂ)) =
        (Homeomorph.funUnique (Fin 1) (Pt s E)) ⁻¹' tsupport (f i) :=
      closedSupport_asFunctionOnOnePoint (f i)
    rw [hSupp]
    exact (Homeomorph.funUnique (Fin 1) (Pt s E)).isCompact_preimage.2 (hf.2.1 i)
  obtain ⟨hFin, hLipschitz, -, -⟩ := (hGrad s E).2 ⟨1, Set.mem_Ici.2 le_rfl⟩ (f i) hC1 hCpt
  refine ⟨?_, hLipschitz⟩
  have hTop : (⨆ x, ENNReal.ofReal ‖((f i x : ℝ) : ℂ)‖) ≠ ⊤ := by
    rw [← tupleSupNorm_ofSinglePoint]
    exact ne_top_of_le_ne_top hFin.ne (le_max_left _ _)
  refine ⟨(⨆ x, ENNReal.ofReal ‖((f i x : ℝ) : ℂ)‖).toReal, fun x => ?_⟩
  have hle : ENNReal.ofReal ‖((f i x : ℝ) : ℂ)‖ ≤ ⨆ x, ENNReal.ofReal ‖((f i x : ℝ) : ℂ)‖ :=
    le_iSup (fun x => ENNReal.ofReal ‖((f i x : ℝ) : ℂ)‖) x
  have hle' := (ENNReal.ofReal_le_iff_le_toReal hTop).1 hle
  simpa [Complex.norm_real] using hle'
end YangMills.Construction.AmbientPoints
