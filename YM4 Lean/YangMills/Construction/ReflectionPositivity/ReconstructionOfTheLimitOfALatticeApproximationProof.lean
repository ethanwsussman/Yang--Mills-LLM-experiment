import YangMills.Construction.ReflectionPositivity.ContractionOfTheLimitOfALatticeApproximation
import YangMills.Construction.ReflectionPositivity.ReconstructionOfTheLimitOfALatticeApproximation
import YangMills.Construction.ReflectionPositivity.SymmetriesAndMirrorsOfTheLimit
import Mathlib
set_option autoImplicit false
open Set
open scoped ComplexOrder NNReal
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.LimitReconstruction
open YangMills.Construction.SeparatedTuples YangMills.Construction.SpectralTheory
open YangMills.Construction.HilbertSpaceBasics (IsPosSemidef)
open YangMills.Construction.ReflectionPositivity.Reconstruction (ContractionHypotheses
  MatrixElementFormula SemigroupProperties SpatialProperties VacuumProperties temporalHyperplane
  timeBasisVec)
open YangMills.Construction.ReflectionPositivity.ShiftSpectralMeasure (EnergyOpProperties
  ExistsUniqueShiftMeasure MomentumOpProperties AgreesWithReconstruction VacuumAnnihilated)
open YangMills.Construction.ReflectionPositivity.ContractionFunctionals (IsAdmissible)
open YangMills.Construction.ReflectionPositivity.LimitSymmetries (HasSymmetriesAndMirrors)
theorem isTranslateInvariant_of_hasSymmetriesAndMirrors {σ : TupleFunctional}
    (hs : HasSymmetriesAndMirrors σ) : σ.IsTranslateInvariant := by
  intro v
  have hmem : Equiv.addRight v ∈ YangMills.Construction.LimitConventions.cubicMotionGroup :=
    ⟨1, one_mem _, v, fun x => by simp⟩
  exact hs.2.1.1 _ hmem
theorem exists_linearIsometryEquiv_of_isUnitaryOp {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] {A : E →L[ℂ] E}
    (hA : YangMills.Construction.HilbertSpaceBasics.IsUnitaryOp A) :
    ∃ V : E ≃ₗᵢ[ℂ] E, ∀ ψ, A ψ = V ψ :=
  ⟨Unitary.linearIsometryEquiv ⟨A, hA.1, hA.2⟩, fun _ => rfl⟩
theorem limitReconstructionTheorem_holds
    (hRec : YangMills.Construction.ReflectionPositivity.Reconstruction.ReconstructionTheorem)
    (hSym : YangMills.Construction.ReflectionPositivity.LimitSymmetries.LimitHasSymmetries)
    (hCon : YangMills.Construction.ReflectionPositivity.LimitContraction.ContractionBound)
    (hMeas : YangMills.Construction.ReflectionPositivity.ShiftSpectralMeasure.ShiftSpectralMeasureTheorem) :
    LimitReconstructionTheorem := by
  intro D T σ hb hrp hl
  obtain ⟨hσ, hs₀⟩ := hSym D T σ.toFun hb hrp hl
  have hs : HasSymmetriesAndMirrors σ := hs₀
  have hcon : ContractsAtAllTimes σ := by
    intro Z t ht
    obtain ⟨h₁, h₂, -, hc⟩ := hCon D T σ hb hrp hl Z t ht.le
    have heq : YangMills.Construction.ReflectionPositivity.LimitContraction.twiceTimeShift t =
        (2 * t) • timeBasisVec := rfl
    rw [heq] at h₁ hc
    exact Complex.le_def.mpr ⟨hc, h₁.trans h₂.symm⟩
  have hch : ContractionHypotheses σ (Ioi 0) :=
    { continuous := hs.1.2.2
      translateInvariant := isTranslateInvariant_of_hasSymmetriesAndMirrors hs
      reflectionPositive := (hs.2.2 temporalHyperplane).2
      subset_pos := subset_rfl
      dense := subset_closure
      contraction := fun F t ht => hcon F t ht }
  have hadm : IsAdmissible σ :=
    { contraction := ⟨_, hch⟩
      permInvariant := hs.1.1
      timeReflect_invariant := by
        rw [YangMills.Construction.Mirrors.timeReflection_eq_axialReflection]
        exact (hs.2.1.2 temporalHyperplane).2 }
  obtain ⟨h, hV, hS, hSp, hM, -, -⟩ := hRec σ (Ioi 0) hch
  obtain ⟨h', hP', -⟩ := hMeas σ hadm
  have hP : ∀ i : Fin 3, ExistsUniqueShiftMeasure σ h i ∧ EnergyOpProperties σ h i ∧
      MomentumOpProperties σ h i ∧ VacuumAnnihilated σ h i ∧ AgreesWithReconstruction σ h i := hP'
  refine ⟨hadm, hcon, h, hV, ?_, ?_, hM⟩
  · obtain ⟨hu, hT, hsc, hsg, hself, -⟩ := hS
    obtain ⟨-, ⟨⟨F, -, hF, hcar, hexp⟩, -, huniq⟩, -, ⟨hΩ, -⟩, -⟩ := hP 0
    refine ⟨hu, hT, hsc, ⟨hsg.1, fun a b => (hsg.2 a b).symm⟩, fun t => ⟨(hself t).1, (hself t).2.1,
      LinearMap.ker_eq_bot'.mpr (hself t).2.2⟩, ⟨F, hF, hcar, fun t => (hexp t).symm⟩, ?_, hΩ⟩
    rintro A ⟨G, hG, hGc, hGe⟩
    exact huniq A G hG hGc fun t => (hGe t).symm
  · obtain ⟨hu, hU, hsc, hur, hcomm, hfix, -⟩ := hSp
    refine ⟨hu, hU, hsc, ⟨hur.2.1, fun a b => (hur.2.2 a b).symm,
      fun a => exists_linearIsometryEquiv_of_isUnitaryOp (hur.1 a)⟩, hcomm, hfix, fun i => ?_⟩
    obtain ⟨-, -, ⟨⟨F, -, hF, hexp⟩, huniq⟩, ⟨-, hΩ⟩, -⟩ := hP i
    refine ⟨⟨F, hF, fun u => (hexp u).symm⟩, ?_, hΩ⟩
    rintro A ⟨G, hG, hGe⟩
    exact huniq A G hG fun u => (hGe u).symm
end YangMills.Construction.ReflectionPositivity.LimitReconstruction
