import YangMills.Construction.Towers.AdjointOfAQuantization
import YangMills.Construction.Towers.ChargedFormInComponents
import YangMills.Construction.Towers.ChargedSectorOfTheConstantField
import YangMills.Construction.Towers.ChargedSymbolAtFluxZero
import YangMills.Construction.Towers.ChargedSymbolOfTheConstantField
import YangMills.Construction.Towers.CoefficientsReadOffAQuantization
import YangMills.Construction.Towers.ExpansionOfAPhaseSum
import YangMills.Construction.Towers.FormOfSymbolsIsTheFormOfAQuantization
import YangMills.Construction.Towers.QuadraticFormOfTheAbelianMassiveOperator
import Mathlib
set_option autoImplicit false
open scoped ComplexConjugate
noncomputable section
namespace YangMills.Construction.Tower.ConstantFieldSymbols
open UnitLatticeL2 MagneticWeyl AbelianFieldDensity AbelianFieldDensity.SectorDecomposition
theorem eq_zero_of_inner_self_of_finite_support {L : ℕ} (X : VectorL2 L 4 →L[ℂ] VectorL2 L 4)
    (hX : ∀ w : VectorL2 L 4, (Function.support fun x => w x).Finite →
      (inner ℂ w (X w) : ℂ) = 0) : X = 0 := by
  classical
  have hall : ∀ w : VectorL2 L 4, (inner ℂ w (X w) : ℂ) = 0 := by
    intro w
    have hsum := lp.hasSum_single (p := 2) (by norm_num) w
    have hc : Continuous fun u : VectorL2 L 4 => (inner ℂ u (X u) : ℂ) :=
      continuous_id.inner X.continuous
    have ht := (hc.tendsto w).comp hsum
    refine tendsto_nhds_unique ht ?_
    refine tendsto_const_nhds.congr fun s => ?_
    refine (hX _ ?_).symm
    refine s.finite_toSet.subset fun x hx => ?_
    by_contra hxs
    apply hx
    have : (∑ i ∈ s, lp.single 2 i (w i) : VectorL2 L 4) x = 0 := by
      rw [lp.coeFn_sum, Finset.sum_apply]
      refine Finset.sum_eq_zero fun i hi => ?_
      have hne : x ≠ i := fun e => hxs (e ▸ hi)
      simp [lp.single_apply, hne]
    exact this
  have hz : (X : VectorL2 L 4 →ₗ[ℂ] VectorL2 L 4) = 0 := by
    refine (inner_map_self_eq_zero _).mp fun w => ?_
    rw [← inner_conj_symm]
    simp [hall w]
  ext1 w
  exact congrArg (fun T : VectorL2 L 4 →ₗ[ℂ] VectorL2 L 4 => T w) hz
theorem sectorOp_eq_weylQuant
    (hPairs : PairsFormIsWeylForm)
    (hForm : ChargedPairsFormIdentity)
    (hQuad : MassiveOperatorQuadraticForm)
    {L : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L) (f : ℝ)
    (S : VectorL2 L 4 →L[ℂ] VectorL2 L 4) (hS : IsSelfAdjointOp S)
    (hB : ∀ w : VectorL2 L 4, (Function.support fun x => w x).Finite →
      ∃ B : FullSpace.Edge L 0 0 → Matrices.ComplexMatrix2, IsLieFormOf w B ∧
        FullSpace.HasFiniteEdgeSupport B ∧
        FullSpace.finiteEdgePairing B (FullSpace.abelianMassiveHessian (scaledLinearAngle L f) B) =
          (((inner ℂ w (S w) : ℂ).re : ℝ) : ℂ)) :
    S = weylQuant L (2 * f) (chargedSymbolExplicit (2 * f)) := by
  have hzero := eq_zero_of_inner_self_of_finite_support
    (S - weylQuant L (2 * f) (chargedSymbolExplicit (2 * f)))
    fun w hw => by
      obtain ⟨B, hBw, hfin, hpair⟩ := hB w hw
      have hq := (hQuad L hL (scaledLinearAngle L f) B hBw.1 hfin).2.2.2
      have hreal : (((inner ℂ w (S w) : ℂ).re : ℝ) : ℂ) = inner ℂ w (S w) := by
        have hconj : conj (inner ℂ w (S w) : ℂ) = inner ℂ w (S w) := by
          rw [inner_conj_symm]
          have h1 : (inner ℂ w (opAdjoint S w) : ℂ) = inner ℂ (S w) w :=
            ContinuousLinearMap.adjoint_inner_right S w w
          rw [← h1, hS]
        exact Complex.conj_eq_iff_re.mp hconj
      have hl := hPairs _ chargedTermPair L (2 * f) w
      have hf := hForm L hL f w B hw hBw
      rw [sub_apply, inner_sub_right, ← hreal, ← hpair, hq, hf, hl]
      exact sub_self _
  exact sub_eq_zero.mp hzero
theorem chargedSymbolExpansionExists_holds
    (hExp : TrigMatrixSumExpansion)
    (hZero : ChargedSymbolFluxZeroClaim)
    (hPairs : PairsFormIsWeylForm)
    (hForm : ChargedPairsFormIdentity)
    (hSector : ChargedSectorClaim)
    (hQuad : MassiveOperatorQuadraticForm)
    (hAdj : WeylQuantAdjoint)
    (hRead : FourierCoeffsFromQuantization) :
    ChargedSymbolExpansionExists := by
  obtain ⟨hTrig, hExpansion⟩ := hExp ChargedIdx (fun k => (chargedTermPair k).totalFreq)
    (fun k => (chargedTermPair k).offset) (fun k => (chargedTermPair k).coeffMatrix)
  have hStd : Conventions.IsAdmissibleBlockingFactor 13 := ⟨by decide, le_refl _⟩
  have hHerm : ∀ φ : ℝ, |φ| ≤ Real.pi → ∀ q,
      pointwiseAdjoint (chargedSymbolExplicit φ) q = chargedSymbolExplicit φ q := by
    intro φ hφ q
    have hf : |φ / 2| ≤ Real.pi / 2 := by
      rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      linarith
    obtain ⟨S, hS, -, hB⟩ := hSector 13 hStd (φ / 2) hf
    have hOp := sectorOp_eq_weylQuant hPairs hForm hQuad hStd (φ / 2) S hS hB
    rw [show 2 * (φ / 2) = φ by ring] at hOp
    have hsym : IsWeylSymbol (chargedSymbolExplicit φ) := (hTrig φ).1
    obtain ⟨hsa, hadj⟩ := hAdj 13 φ 4 4 (chargedSymbolExplicit φ) hsym
    have heq : weylQuant 13 φ (chargedSymbolExplicit φ) =
        weylQuant 13 φ (pointwiseAdjoint (chargedSymbolExplicit φ)) := by
      rw [← hadj, ← hOp]
      exact hS.symm
    have := ((hRead 13 φ).1 4 4 (chargedSymbolExplicit φ) hsym).2 _ hsa heq
    exact (congrFun this q).symm
  have hMassive : ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ f : ℝ,
      |f| ≤ Real.pi / 2 → ∀ v : VectorL2 L 4,
        AbelianFieldDensity.massiveOp (scaledLinearAngle L f)
            (edgeTensor v raisingPauli) =
          edgeTensor (weylQuant L (2 * f) (chargedSymbolExplicit (2 * f)) v) raisingPauli := by
    intro L hL f hf v
    obtain ⟨S, hS, hmul, hB⟩ := hSector L hL f hf
    rw [hmul v, sectorOp_eq_weylQuant hPairs hForm hQuad hL f S hS hB]
  obtain ⟨D, C, σ₁, σ₂, σr, h⟩ := hExpansion hZero hHerm hMassive
  exact ⟨D, C, σ₁, σ₂, chargedSymbolExplicit, σr, h⟩
end YangMills.Construction.Tower.ConstantFieldSymbols
end
