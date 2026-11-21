import YangMills.Construction.EuclideanFunctionals.FirstFactsOnAReconstructionProof
import YangMills.Construction.EuclideanFunctionals.MeasuresAndOperatorsOfTheReconstruction
import YangMills.Construction.RotationInvariance.AnalyticityAlongTangentialMovesProof
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
noncomputable section
namespace YangMills.Construction.EuclideanFunctionals
namespace EuclidFunctionalWithRecon
open BorelSpectral
open WholeSpaceSpectral (restrictToUniv diagSetFn)
open BorelCalculus (IsBoundedFn)
open SpectralTheorem
  (IsSpectralIntegralOf IsSpectralMeasureFor IntegralsAgree spectralIntegralOp pushforwardToLine
    spectralMeasure)
open HilbertSpaceBasics (UnboundedOp)
open ResolvedOps (StronglyCommute IsJointSpectralMeasure IsDiagonalized boxSet)
open SpectralPoint
theorem spectralIntegralOp_congr {n : ℕ} {Y : Set (Fin n → ℝ)} {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] {E : SpectralMeasure Y H} {g g' : Y → ℂ}
    (h : IntegralsAgree E g E g') : spectralIntegralOp E g = spectralIntegralOp E g' := by
  have hp : (fun A : UnboundedOp H => IsSpectralIntegralOf A E g) =
      fun A => IsSpectralIntegralOf A E g' := by
    funext A
    refine propext ⟨fun ⟨h₁, h₂⟩ => ⟨fun ψ => ?_, fun ψ => ?_⟩, fun ⟨h₁, h₂⟩ => ⟨fun ψ => ?_, fun ψ => ?_⟩⟩
    · rw [← h.1]
      exact h₁ ψ
    · exact (h₂ ψ).trans (h.2 ψ ((h₁ ψ).1 ψ.2))
    · rw [h.1]
      exact h₁ ψ
    · refine (h₂ ψ).trans (h.2 ψ ?_).symm
      rw [h.1]
      exact (h₁ ψ).1 ψ.2
  unfold spectralIntegralOp
  rw [hp]
theorem stronglyCommute_symm {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] {A B : UnboundedOp H} (h : StronglyCommute A B) : StronglyCommute B A :=
  fun Δ Δ' => (h Δ' Δ).symm
theorem spatialEmbed_mem_spatialVecs (u : Fin 3 → ℝ) : spatialEmbed u ∈ spatialVecs := by apply _root_.YangMills.Construction.EuclideanFunctionals.HamMomMatrixCalculusProof.spatialEmbed_mem_spatialVecs <;> assumption
theorem transl_mul (a b : R4) :
    EuclidMotion.transl a * EuclidMotion.transl b = EuclidMotion.transl (a + b) := by apply _root_.YangMills.Construction.EuclideanFunctionals.TangentialAnalyticity.transl_mul_transl <;> assumption
theorem finCombIn_mono {O O' : Set R4} (h : O ⊆ O') :
    finCombIn O ≤ finCombIn O' := by apply _root_.YangMills.Construction.EuclideanFunctionals.HeightTuples.finCombIn_mono <;> assumption
theorem isOpen_upperHalf : IsOpen upperHalf :=
  isOpen_lt continuous_const (continuous_apply 3)
theorem transl_actFree_mem (hT : TupleRules.TupleSpanActionRules) (y : R4) (hy : 0 ≤ y 3)
    {G : FreeSep} (hG : G ∈ finCombIn upperHalf) :
    (EuclidMotion.transl y).actFree G ∈ finCombIn upperHalf := by
  have hsub : (EuclidMotion.transl y) '' upperHalf ⊆ upperHalf := by
    rintro _ ⟨z, hz, rfl⟩
    have hz' : 0 < z 3 := hz
    change 0 < (EuclidMotion.transl y z) 3
    rw [EuclidMotion.transl_apply, Pi.add_apply]
    linarith
  exact finCombIn_mono hsub
    ((hT.2.1 (EuclidMotion.transl y) _ isOpen_upperHalf).2.2.mapsTo hG)
theorem timePart_add_spatialEmbed (x : R4) :
    x 3 • timeVec + spatialEmbed (spatialProj x) = x := by
  funext i
  fin_cases i <;>
    simp [spatialEmbed, spatialProj, Fin.snoc, PeriodicLattice.coordVec, LinearMap.funLeft]
theorem timeStabilizer_mem_spatialVecs (w : timeStabilizer) {v : R4}
    (hv : v ∈ spatialVecs) : (w : EuclidMotion) v ∈ spatialVecs := by apply _root_.YangMills.Construction.EuclideanFunctionals.ReconstructionFactsProof.stab_mem_spatialVecs <;> assumption
variable {c : SharpScale} {S : ConnFamily} (σ : EuclidFunctionalWithRecon c S)
theorem hamMomFamily_isDiagonalized (hC : SelfAdjointResolution.SelfAdjointDiagonalizationTheorem)
    (k : Fin 4) : IsDiagonalized (hamMomFamily σ.recon.ham σ.recon.mom k) := by
  have h := (hC.1 σ.space).2.2.2.1
  induction k using Fin.cases with
  | zero => exact h _ σ.recon.ham_selfAdjoint
  | succ j => exact h _ (σ.recon.mom_selfAdjoint j)
theorem hamMomFamily_stronglyCommute (j k : Fin 4) (hjk : j ≠ k) : StronglyCommute
    (hamMomFamily σ.recon.ham σ.recon.mom j)
    (hamMomFamily σ.recon.ham σ.recon.mom k) := by apply _root_.YangMills.Construction.EuclideanFunctionals.ReconstructionFactsProof.stronglyCommute_hmFamily <;> assumption
abbrev hamMomPair : Fin 2 → UnboundedOp σ.space :=
  ![σ.recon.ham, σ.recon.mom 0]
theorem hamMomPair_isDiagonalized (hC : SelfAdjointResolution.SelfAdjointDiagonalizationTheorem)
    (k : Fin 2) : IsDiagonalized (σ.hamMomPair k) := by
  have h := (hC.1 σ.space).2.2.2.1
  fin_cases k
  · exact h _ σ.recon.ham_selfAdjoint
  · exact h _ (σ.recon.mom_selfAdjoint 0)
theorem hamMomPair_stronglyCommute (j k : Fin 2) (hjk : j ≠ k) :
    StronglyCommute (σ.hamMomPair j) (σ.hamMomPair k) := by
  fin_cases j <;> fin_cases k
  · exact absurd rfl hjk
  · exact stronglyCommute_symm (σ.recon.mom_commute_ham 0)
  · exact σ.recon.mom_commute_ham 0
  · exact absurd rfl hjk
theorem jointMeasure_facts (hC : SelfAdjointResolution.SelfAdjointDiagonalizationTheorem) :
    IsJointSpectralMeasure (hamMomFamily σ.recon.ham σ.recon.mom) σ.jointMeasure ∧
      ∀ k, σ.jointMeasure.coordMarginal k = spectralMeasure
        (hamMomFamily σ.recon.ham σ.recon.mom k) := by
  have h := (hC.2.2 σ.space).1 4 (by norm_num) _ (σ.hamMomFamily_isDiagonalized hC)
    σ.hamMomFamily_stronglyCommute
  exact ⟨h.2.1, h.2.2.1⟩
theorem planeMeasure_facts (hC : SelfAdjointResolution.SelfAdjointDiagonalizationTheorem) :
    (∀ F, IsJointSpectralMeasure σ.hamMomPair F → F = σ.planeMeasure) ∧
      ∀ k, σ.planeMeasure.coordMarginal k = spectralMeasure (σ.hamMomPair k) := by
  obtain ⟨⟨E, -, huniq⟩, hJ, hm, -⟩ :=
    (hC.2.2 σ.space).1 2 (by norm_num) _ (σ.hamMomPair_isDiagonalized hC)
      σ.hamMomPair_stronglyCommute
  exact ⟨fun F hF => (huniq F hF).trans (huniq _ hJ).symm, hm⟩
theorem planePushforward_hasRectangleValues
    (hC : SelfAdjointResolution.SelfAdjointDiagonalizationTheorem) :
    σ.HasRectangleValues σ.planePushforward := by
  intro Δ₀ Δ₁
  have hm := (σ.jointMeasure_facts hC).2
  have h₀ : spectralMeasure σ.recon.ham (realLineSet Δ₀) =
      σ.jointMeasure ⟨{y | y.1 0 ∈ Δ₀.1},
        ((measurable_pi_apply 0).comp measurable_subtype_coe) Δ₀.2⟩ := by
    have := congrArg (fun E => E.toFun (realLineSet Δ₀)) (hm 0)
    exact this.symm
  have h₁ : spectralMeasure (σ.recon.mom 0) (realLineSet Δ₁) =
      σ.jointMeasure ⟨{y | y.1 1 ∈ Δ₁.1},
        ((measurable_pi_apply 1).comp measurable_subtype_coe) Δ₁.2⟩ := by
    have := congrArg (fun E => E.toFun (realLineSet Δ₁)) (hm 1)
    exact this.symm
  rw [h₀, h₁, ← SpectralMeasure.map_inter]
  change σ.jointMeasure _ = σ.jointMeasure _
  congr 1
  refine Subtype.ext ?_
  ext y
  simp [boxSet, energyMomentumPlane, SpectralPoint.energyOf, SpectralPoint.momentumOf,
    Fin.forall_fin_two]
theorem eq_planeMeasure (hC : SelfAdjointResolution.SelfAdjointDiagonalizationTheorem)
    (F : SpectralMeasure EPlanePoints σ.space) (hF : σ.HasRectangleValues F) :
    F = σ.planeMeasure := by
  refine (σ.planeMeasure_facts hC).1 F fun Δ => ?_
  have hΔ : ![Δ 0, Δ 1] = Δ := by
    funext i
    fin_cases i <;> rfl
  have h := hF (Δ 0) (Δ 1)
  rw [hΔ] at h
  rw [h]
  simp [List.ofFn_succ]
theorem measureFacts_holds (hC : SelfAdjointResolution.SelfAdjointDiagonalizationTheorem)
    (hD : SpectralMeasureCalculus.CalculusTheorem) :
    σ.MeasureFacts := by
  have himg : σ.planePushforward = σ.planeMeasure :=
    σ.eq_planeMeasure hC _ (σ.planePushforward_hasRectangleValues hC)
  have hI := (hD σ.space 4 univ σ.jointMeasure).2.2.2.2.1
  have hspec := fun (A : UnboundedOp σ.space)
    (hA : OperatorTransport.IsSelfAdjointUnbounded A) => ((hC.1 σ.space).2.2.2.2.2 A hA).2
  refine
    { isJoint := (σ.jointMeasure_facts hC).1
      spectralMeasureAt_eq := fun ψ Δ => ?_
      pushforward_hasValues := σ.planePushforward_hasRectangleValues hC
      pushforward_unique := fun F hF => (σ.eq_planeMeasure hC F hF).trans himg.symm
      pushforward_eq := himg
      planeMeasure_apply := fun Δ => ?_
      planeDiagMeasure_eq := fun ψ => ?_
      planeIntegralOp_eq := fun f hf hb => ?_
      pushforwardToLine_energy := (σ.jointMeasure_facts hC).2 0
      pushforwardToLine_planeEnergy := (σ.planeMeasure_facts hC).2 0
      pushforwardToLine_planeMomentum := (σ.planeMeasure_facts hC).2 1
      isSpectralMeasureFor_ham := hspec _ σ.recon.ham_selfAdjoint
      isSpectralMeasureFor_mom := hspec _ (σ.recon.mom_selfAdjoint 0) }
  · exact (σ.jointMeasure.inner_apply_self_eq_diagMeasure ψ (restrictToUniv Δ)).symm
  · rw [← himg]
    rfl
  · change σ.planeMeasure.diagMeasure ψ = _
    rw [← himg]
    exact hI.scalarMeasure_image (by norm_num) MeasurableSet.univ _ _ ψ
  · obtain ⟨b, hb⟩ := hb
    have hs := hI.integral_image (by norm_num) MeasurableSet.univ energyMomentumPlane
      measurable_energyMomentumPlane f hf
    change σ.planeMeasure.integralOp f = _
    rw [← himg]
    ext ψ
    have hb' : ∀ y, ‖(f ∘ energyMomentumPlane) y‖ ≤ b := fun y => hb _
    have hdom : ψ ∈ σ.jointMeasure.integralDom (f ∘ energyMomentumPlane) := by
      rw [SpectralMeasure.integralDom_eq_univ _ hb']
      exact mem_univ _
    rw [← SpectralMeasure.integralApply_eq_integralOp _ hb,
      ← SpectralMeasure.integralApply_eq_integralOp _ hb']
    exact hs.2 ψ (by rw [hs.1]; exact hdom)
theorem boundedOnCarrierIntegrals_holds
    (hC : SelfAdjointResolution.SelfAdjointDiagonalizationTheorem)
    (hD : SpectralMeasureCalculus.CalculusTheorem)
    (hcar : σ.jointMeasure.IsCarriedBy SpectralPoint.nonnegEnergy) :
    σ.BoundedOnCarrierIntegrals := by
  refine ⟨hcar, fun C hCar Φ hΦ hb => ?_⟩
  have hJ := (hC.2.2 σ.space).1 4 (by norm_num) _ (σ.hamMomFamily_isDiagonalized hC)
    σ.hamMomFamily_stronglyCommute
  have hΦ' : Measurable fun y : C.1 => Φ y.1 := hΦ.comp measurable_subtype_coe
  have hs := (hJ.2.2.2.2.2.2 C (fun y => Φ y.1) hCar hΦ' hb).1
  have hcong := (hD σ.space 4 univ σ.jointMeasure).2.2.1.congr Φ
    (zeroExtend C.1 fun y => Φ y.1) C hΦ (measurable_zeroExtend C.2 hΦ') hCar
    fun y hy => by simp [zeroExtend, hy]
  exact (spectralIntegralOp_congr hcong).trans hs
theorem translateClasses_holds (hT : TupleRules.TupleSpanActionRules) :
    σ.TranslateClasses := by
  intro x hx F
  have hv := spatialEmbed_mem_spatialVecs (spatialProj x)
  have hFv := transl_actFree_mem hT _ (le_of_eq (hv : _ = (0 : ℝ)).symm) F.2
  have h₁ := σ.recon.transl_cls _ hv F
  rw [readClass, dif_pos hFv] at h₁
  have h₂ := σ.recon.expHam_cls (x 3) hx ⟨_, hFv⟩
  have hcomp : (EuclidMotion.transl (x 3 • timeVec)).actFree
      ((EuclidMotion.transl (spatialEmbed (spatialProj x))).actFree F.1) =
      (EuclidMotion.transl x).actFree F.1 := by
    rw [(hT.2.2.1 _ _ F.1).1, transl_mul, timePart_add_spatialEmbed]
  have hx' := transl_actFree_mem hT x hx F.2
  refine ⟨hx', ?_⟩
  simp only [hcomp] at h₂
  rw [readClass, dif_pos hx'] at h₂
  refine Eq.trans ?_ h₂
  exact congrArg (σ.heatSemigroup (x 3)) h₁
end EuclidFunctionalWithRecon
theorem reconstructionMeasureOperatorFacts_holds
    (hA : ReconstructionBasicFacts)
    (hC : SelfAdjointResolution.SelfAdjointDiagonalizationTheorem)
    (hD : SpectralMeasureCalculus.CalculusTheorem)
    (hT : TupleRules.TupleSpanActionRules) :
    ReconstructionMeasureOperatorFacts := by
  intro c S σ
  have hf : σ.SpectralGeneratorsAndKernel ∧ σ.TranslUnitaryGroup ∧
      σ.SpectralMeasureUniqueness ∧ σ.VacuumInvariance ∧ σ.RotationCovariance :=
    hA c S σ σ.space σ.recon
  obtain ⟨⟨-, -, hcar, htr⟩, -, -, hvac, hgrp⟩ := hf
  refine ⟨σ.measureFacts_holds hC hD, σ.boundedOnCarrierIntegrals_holds hC hD hcar,
    ?_, ?_, σ.translateClasses_holds hT, ?_⟩
  · intro t ht x
    refine ⟨(htr t ht _ (EuclidFunctionalWithRecon.spatialEmbed_mem_spatialVecs x)).2, ?_⟩
    have hres := (hC.1 σ.space).2.2.2.1 _ σ.recon.ham_selfAdjoint
    exact ((hC.2.1 σ.space).2.2.2.1 _ hres σ.recon.ham_nonneg).1
      (t : ℂ) (by simpa [ResolvedFacts.rightClosedHalfPlane] using ht)
  · obtain ⟨h₁, h₂, -, -, h₅, -⟩ := hvac
    refine ⟨h₁, h₂, ?_⟩
    have hm : MeasurableSet {p : SpectralPoint.EMPoints | SpectralPoint.energyOf p ≠ 0} :=
      (SpectralPoint.measurable_energyOf (measurableSet_singleton 0)).compl
    rw [h₅, Measure.dirac_apply' _ hm]
    exact Set.indicator_of_notMem
      (show _ ∉ {p : SpectralPoint.EMPoints | SpectralPoint.energyOf p ≠ 0} from fun h => h rfl) _
  · obtain ⟨h₁, h₂, -⟩ := hgrp
    exact ⟨fun w t ht => h₁ t ht w, fun w v hv =>
      ⟨EuclidFunctionalWithRecon.timeStabilizer_mem_spatialVecs w hv, h₂ w v hv⟩⟩
end YangMills.Construction.EuclideanFunctionals
