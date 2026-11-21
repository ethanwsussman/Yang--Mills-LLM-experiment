import YangMills.Construction.PeriodicOperators.ImaginaryShiftOfASymbol
import YangMills.Construction.PeriodicOperators.NormOfTheSymbol
import YangMills.Construction.PeriodicOperators.ProductOfPeriodicOperators
import YangMills.Construction.PeriodicOperators.QuotientsTransposesAndNorm
import YangMills.Construction.PeriodicOperators.SeriesOfTheSymbol
import YangMills.Construction.PeriodicOperators.SymbolOfAProduct
import YangMills.Construction.PeriodicOperators.SymbolOnClassesAndPlaneWaves
import YangMills.Construction.PeriodicOperators.SymbolsOfPeriodicOperators
import YangMills.Construction.PeriodicOperators.TorusKernelOfAPeriodicOperator
import YangMills.Construction.PeriodicOperators.TraceAndDeterminantOnATorus
import YangMills.Construction.PeriodicOperators.TraceOfAMomentumShift
import YangMills.Construction.PeriodicOperators.TranslationsOfTheSymbol
import YangMills.Construction.PeriodicOperators.TransposeOfAPeriodicOperator
import YangMills.Construction.PeriodicOperators.WaveSpacesOnATorus
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.PeriodicOperators.SymbolsAssembly
theorem symbols_claim (hNorm : Quotients.QuotientTransposeNorm)
    (hSeries : SymbolSeriesClaim)
    (hQuot : SymbolOnQuotients.Claim)
    (hTransl : SymbolTranslation.Claim)
    (hComp : CompClaim)
    (hSymbComp : SymbolCompClaim)
    (hTransp : Transpose.Claim)
    (hPer : Periodized.Claim)
    (hBloch : BlochDecomposition.Claim)
    (hShift : ShiftTrace.TraceVanishes)
    (hTrDet : TorusTraceDet.Claim)
    (hIm : SymbolImShift.Claim)
    (hNormSymb : SymbolNormBound) : Symbols.Claim := by
  refine ⟨?_, ?_⟩
  · intro I I' I'' hI hI' hI'' T S δ hT hδ hS hδS
    have ser := hSeries I I' hI hI' T δ hδ
    have quo := hQuot I I' hI hI' T hT
    have tra := hTransl.1 I I' hI hI' T hT
    have com := hComp I I' I'' hI hI' hI'' T S δ hT hδ hS hδS
    have tsp := hTransp I I' hI hI' T δ hT hδ
    have per := hPer I I' hI hI' T δ hT hδ
    have blo := hBloch I hI
    have nrm := (hNorm I I' hI hI' 1 one_pos).2.2.2 T hT
    exact
      { summable_on_strip := ser.summableOn_strip
        summable_locallyUniformly := ser.locallyUniform
        norm_summable_locallyUniformly := ser.locallyUniform_norm
        isHolomorphicIn := ser.holomorphic
        eq_of_mkQuot_eq := quo.fourierSymbol_congr_mkQuot
        applyKernel_blochWave := quo.applyKernel_blochWave
        compKernel_isPeriodicKernel := com.comp_periodic
        kernelTranspose_isPeriodicKernel := tsp.periodic
        quotSymbol_compKernel := hSymbComp I I' I'' hI hI' hI'' T S δ hT hδ hS hδS
        quotSymbol_kernelTranspose := tsp.symbol_eq
        wInner_quotTranspose := tsp.adjoint_of_real
        exp_phase_eq_of_mkQuot_eq := tra.exp_phase_eq_of_mkQuot_eq
        quotSymbol_addTwoPiInt := tra.quotSymbol_addTwoPiInt
        periodization_summable := per.summable
        periodization_eq_of_mkQuot_eq := per.depends_quot
        blochWaveSubspace_internal := blo.internal_sum
        blochWaveSubspace_orthogonal := blo.orthogonal
        periodicMatrix_blochWave := per.acts_by_symbol
        trace_eq_zero_of_shift := hShift I hI
        fourierSymbol_expConj := hIm I I' hI hI' T δ hT hδ
        kernelOpNorm_lt_top := ⟨fun f hf a => (nrm.1 f hf).1 a, nrm.2.1, nrm.2.2⟩
        quotOpNorm_le := hNormSymb I I' hI hI' T hT }
  · intro I hI T δ hT hδ
    have tra := hTransl.2 I hI T hT
    have tor := hTrDet I hI T δ hT hδ
    exact
      { trace_addTwoPiInt := tra.trace_addTwoPiInt
        det_addTwoPiInt := tra.det_addTwoPiInt
        trace_periodicMatrix := tor.trace_eq
        det_periodicMatrix := tor.det_eq }
end YangMills.Construction.PeriodicOperators.SymbolsAssembly
