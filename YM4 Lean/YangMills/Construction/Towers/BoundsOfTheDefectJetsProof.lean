import YangMills.Construction.PeriodicOperators.NormOfAnElementOfHomProof
import YangMills.Construction.Towers.BoundsOfTheDefectJets
import YangMills.Construction.Towers.CoefficientsOfTheHalfPlaquetteTraceNearAnIndex
import YangMills.Construction.Towers.CoefficientsOfTheHessianCurvatureNearAnIndex
import YangMills.Construction.Towers.CoefficientsOfTheScaledCovariantDifferenceNearAnIndex
import YangMills.Construction.Towers.CoefficientsOfTheTransportDefectNearAnIndex
import YangMills.Construction.Towers.ConstantComponentsOfTheBasicJets
import YangMills.Construction.Towers.TheBackgroundsAreBoundedNearAPoint
import YangMills.Construction.Towers.TheOperatorFunctionsOfTheScaledPictureAndTheirJets
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.DefectJetBoundLemmas
open YangMills.Construction.PeriodicOperators
open YangMills.Construction.Tower.FullSpace.BackgroundJets
open YangMills.Construction.Tower.FullSpace.FinestLatticeNeighbours
theorem finestMesh_mem_unit (L k : ℕ) (hk : 1 ≤ k) : 0 ≤ finestMesh L k ∧ finestMesh L k ≤ 1 := by
  have h : finestMesh L k = ((L : ℝ) ^ k)⁻¹ := by
    simp [finestMesh, meshAt, zpow_neg]
  rw [h]
  refine ⟨by positivity, ?_⟩
  rcases Nat.eq_zero_or_pos L with rfl | hL
  · simp [show k ≠ 0 by omega]
  · exact inv_le_one_of_one_le₀ (one_le_pow₀ (by exact_mod_cast hL))
theorem phaseField_smul (F : PeriodicData) (q : Fin 4 → ℂ) (a : F.UnitQuot → ℂ)
    (y : InfiniteLattice.AmbientSpace) (z : ℂ) :
    phaseField F q (z • a) y = z • phaseField F q a y := by
  funext κ
  simp only [phaseField, Pi.smul_apply, smul_eq_mul]
  ring
theorem exp_sum_im_le (δ η : ℝ) (κ : Fin 4 → ℂ) (hκ : ∀ μ, |(κ μ).im| ≤ 2 * δ) (h1 : η ≤ 1) : Real.exp (∑ μ, |(κ μ).im| * (2 * η)) ≤ Real.exp (16 * δ) := by
  apply Real.exp_le_exp.mpr
  have hterm : ∀ μ, |(κ μ).im| * (2 * η) ≤ 4 * δ := fun μ => by
    have := hκ μ
    have hn := abs_nonneg (κ μ).im
    nlinarith
  calc ∑ μ, |(κ μ).im| * (2 * η) ≤ ∑ _μ : Fin 4, 4 * δ := Finset.sum_le_sum fun μ _ => hterm μ
    _ = 16 * δ := by simp; ring
theorem quotHomNorm_id_le_one {I : PeriodicData} : quotHomNorm (LinearMap.id : QuotHom I I) ≤ 1 := by apply _root_.YangMills.Construction.PeriodicOperators.HomNorm.quotHomNorm_id_le <;> assumption
theorem quotHomNorm_zero_le_one {I I' : PeriodicData} : quotHomNorm (0 : QuotHom I I') ≤ 1 := by
  refine iSup₂_le fun f _ => ?_
  simp [wNorm]
theorem jetNorm_le_of_components {I I' : PeriodicData} {δ : ℝ} {p : Fin 4 → ℂ} {T : JetQuad I I'} {X : ℝ}
    (hX : 0 ≤ X) (h0 : ∀ κ ∈ imStrip (2 * δ), quotHomNorm (T.f00 κ) ≤ 1)
    (h1 : ∀ κ ∈ stripAddShift δ p, quotHomNorm (T.f10 κ) ≤ ENNReal.ofReal X)
    (h2 : ∀ κ ∈ stripSubShift δ p, quotHomNorm (T.f01 κ) ≤ ENNReal.ofReal X)
    (h3 : ∀ κ ∈ realDualPoints, quotHomNorm (T.f11 κ) ≤ ENNReal.ofReal X) :
    JetQuad.jetNorm δ p T ≤ ENNReal.ofReal (1 + 3 * X) := by
  have e : ENNReal.ofReal (1 + 3 * X) =
      1 + ENNReal.ofReal X + ENNReal.ofReal X + ENNReal.ofReal X := by
    rw [show 1 + 3 * X = 1 + X + X + X by ring,
      ENNReal.ofReal_add (by positivity) hX, ENNReal.ofReal_add (by positivity) hX,
      ENNReal.ofReal_add (by positivity) hX, ENNReal.ofReal_one]
  rw [e]
  exact add_le_add (add_le_add (add_le_add (iSup₂_le h0) (iSup₂_le h1)) (iSup₂_le h2)) (iSup₂_le h3)
def jetComponentBound (c M : ℝ) : ℝ :=
  11250 * ((Real.exp (16 * stripHalfWidth) + 1) * (c * M + c * M ^ 2))
theorem jetComponentBound_nonneg {c M : ℝ} (hc : 0 ≤ c) (hM : 0 ≤ M) : 0 ≤ jetComponentBound c M := by
  unfold jetComponentBound
  positivity
theorem jet_components_bounded {I I' : PeriodicData} (hG : JetComponentBound.Claim)
    (L k : ℕ) (hk : 1 ≤ k) (hF : IsPeriodic (remainderIndex L k))
    (hI : IsPeriodic I) (hI' : IsPeriodic I')
    (T : ((remainderIndex L k).Carrier → ℂ) → I'.Carrier → I.Carrier → ℂ)
    (hloc : IsLocalOpFun (remainderIndex L k) I I' T) (w : ℝ)
    (wI : ∀ i, I.weightOf i = w) (wI' : ∀ j, I'.weightOf j = w)
    (standingConstraints : ∀ y, {i : I.Carrier | WithinBox (2 * finestMesh L k) (I.pos i) y}.encard ≤ 11250)
    (cols : ∀ y, {j : I'.Carrier | WithinBox (2 * finestMesh L k) (I'.pos j) y}.encard ≤ 11250)
    {c M : ℝ} (hc : 0 ≤ c) (hM : 0 ≤ M) (hcT : CoeffsLocallyBounded (I := I) (J := I') L k T c)
    (hB : ∀ q ∈ momentumPolydisc stripHalfWidth, ∀ (μ : Fin 4) (y : InfiniteLattice.AmbientSpace),
      FieldBoundedNear L k y
        (phaseField (remainderIndex L k) q (responseAmplitude L k q μ) y) M)
    (p : Fin 4 → ℂ) (hp : p ∈ momentumPolydisc stripHalfWidth) (μPlus μMinus : Fin 4) :
    (∀ κ ∈ imStrip (2 * stripHalfWidth),
      quotHomNorm ((jetAlongResponse L k T p μPlus μMinus).f10 κ) ≤
          ENNReal.ofReal (jetComponentBound c M) ∧
        quotHomNorm ((jetAlongResponse L k T p μPlus μMinus).f01 κ) ≤
          ENNReal.ofReal (jetComponentBound c M)) ∧
      ∀ κ ∈ realDualPoints, quotHomNorm ((jetAlongResponse L k T p μPlus μMinus).f11 κ) ≤
        ENNReal.ofReal (jetComponentBound c M) := by
  obtain ⟨η0, η1⟩ := finestMesh_mem_unit L k hk
  have hneg : -p ∈ momentumPolydisc stripHalfWidth := fun μ => by simpa using hp μ
  set η := finestMesh L k with hη
  set β := c * M + c * M ^ 2 with hβ
  have hβ0 : 0 ≤ β := by positivity
  have hrow : ∀ j : I'.Carrier,
      {i : I.Carrier | WithinBox (2 * η) (I.pos i) (I'.pos j)}.encard ≤ (11250 : ℕ) :=
    fun j => by simpa using standingConstraints (I'.pos j)
  have hcol : ∀ i : I.Carrier,
      {j : I'.Carrier | WithinBox (2 * η) (I.pos i) (I'.pos j)}.encard ≤ (11250 : ℕ) := by
    intro i
    have e : {j : I'.Carrier | WithinBox (2 * η) (I.pos i) (I'.pos j)} =
        {j : I'.Carrier | WithinBox (2 * η) (I'.pos j) (I.pos i)} := by
      ext j
      simp only [Set.mem_ofPred_eq, WithinBox]
      exact forall_congr' fun μ => by rw [abs_sub_comm]
    rw [e]
    simpa using cols (I.pos i)
  have hsm : ∀ (q : Fin 4 → ℂ) (μ : Fin 4) (y : InfiniteLattice.AmbientSpace),
      phaseField (remainderIndex L k) q (scaledResponseField L k q μ) y =
        ((η : ℝ) : ℂ) • phaseField (remainderIndex L k) q (responseAmplitude L k q μ) y :=
    fun q μ y => phaseField_smul _ q _ y _
  have main := hG (remainderIndex L k) I I' hF hI hI' T hloc w wI wI' (2 * η) β 11250 hβ0 hrow
    hcol p (scaledResponseField L k p μPlus) (scaledResponseField L k (-p) μMinus)
    (fun j i hn => ⟨(hcT.1 _ 0 j i hn).1, (hcT.1 _ 0 j i hn).1, (hcT.1 _ _ j i hn).2⟩)
    (fun j i _ => by
      rw [hsm, hsm]
      have hA := hB p hp μPlus (I'.pos j)
      have hA' := hB (-p) hneg μMinus (I'.pos j)
      obtain ⟨f1, s1⟩ := hcT.2 _ _ M j i hM hA hA'
      obtain ⟨f2, -⟩ := hcT.2 _ _ M j i hM hA' hA
      have l1 : c * M ≤ β := by rw [hβ]; nlinarith [mul_nonneg hc (sq_nonneg M)]
      have l2 : c * M ^ 2 ≤ β := by rw [hβ]; nlinarith [mul_nonneg hc hM]
      exact ⟨f1.trans l1, f2.trans l1, s1.trans l2⟩)
  have hexp : ∀ κ : Fin 4 → ℂ, Real.exp (∑ μ, |(κ μ).im| * (2 * η)) ≤
      Real.exp (16 * stripHalfWidth) + 1 → ((11250 : ℕ) : ℝ) *
        (Real.exp (∑ μ, |(κ μ).im| * (2 * η)) * β) ≤ jetComponentBound c M := by
    intro κ h
    unfold jetComponentBound
    have := mul_le_mul_of_nonneg_right h hβ0
    push_cast
    linarith
  refine ⟨fun κ hκ => ?_, fun κ hκ => ?_⟩
  · have hb := hexp κ ((exp_sum_im_le stripHalfWidth η κ hκ η1).trans (by linarith))
    exact ⟨(main κ).1.trans (ENNReal.ofReal_le_ofReal hb),
      (main κ).2.1.trans (ENNReal.ofReal_le_ofReal hb)⟩
  · have him : ∀ μ, (κ μ).im = 0 := hκ
    have hb := hexp κ (by
      simp only [him, abs_zero, zero_mul, Finset.sum_const_zero, Real.exp_zero]
      linarith [Real.exp_pos (16 * stripHalfWidth)])
    exact (main κ).2.2.trans (ENNReal.ofReal_le_ofReal hb)
theorem defectJetBounds_holds (hConstant : ConstantJetComponents)
    (hG : JetComponentBound.Claim)
    (hOperators : ScaledOperatorFunctions.ScaledOperatorFunctionsClaim)
    (hIndices : NeighbourCountBound)
    (hD : CovariantDifferenceCoeffs.CovariantDifferenceCoeffsBounded)
    (hE : HolonomyDefectCoeffsBounded)
    (hZ : HalfFaceTraceNearIndex.HalfFaceTraceCoeffsBounded)
    (hH : CurvatureKernelCoeffs.CurvatureKernelCoeffsBounded)
    (hBackgrounds : BackgroundsBoundedNearPoint.Claim) : DefectJetBounds := by
  intro L hL
  obtain ⟨cD, hcD, bD⟩ := hD L hL
  obtain ⟨cE, hcE, bE⟩ := hE L hL
  obtain ⟨cZ, hcZ, bZ⟩ := hZ L hL
  obtain ⟨cH, hcH, bH⟩ := hH L hL
  obtain ⟨M, hM, bM⟩ := hBackgrounds L hL
  have xD := jetComponentBound_nonneg hcD hM
  have xE := jetComponentBound_nonneg hcE hM
  have xZ := jetComponentBound_nonneg hcZ hM
  have xH := jetComponentBound_nonneg hcH hM
  refine ⟨(1 + 3 * jetComponentBound cD M) + (1 + 3 * jetComponentBound cE M) +
    (1 + 3 * jetComponentBound cZ M) + (1 + 3 * jetComponentBound cH M), by positivity, ?_⟩
  intro k hk μPlus μMinus p hp
  obtain ⟨hperS, hperB, hperP, -, -⟩ := ((hOperators.1 L hL k hk).1).periodic
  have hops := (hOperators.1 L hL k hk).1
  have rS := fun y => (hIndices L hL k hk y).1
  have rB := fun y => (hIndices L hL k hk y).2.1
  have rP := fun y => (hIndices L hL k hk y).2.2
  have cD' := jet_components_bounded hG L k hk hperB hperS hperB _ hops.D_local.1
    (meshAt L k 0 ^ 4) (fun _ => rfl) (fun _ => rfl) rS rB hcD hM (bD k hk)
    (bM k hk) p hp μPlus μMinus
  have cE' := jet_components_bounded hG L k hk hperB hperB hperP _ hops.holonomyDefect_local.1
    (meshAt L k 0 ^ 4) (fun _ => rfl) (fun _ => rfl) rB rP hcE hM (bE k hk)
    (bM k hk) p hp μPlus μMinus
  have cZ' := jet_components_bounded hG L k hk hperB hperP hperP _ hops.halfFaceTrace_local.1
    (meshAt L k 0 ^ 4) (fun _ => rfl) (fun _ => rfl) rP rP hcZ hM (bZ k hk)
    (bM k hk) p hp μPlus μMinus
  have cH' := jet_components_bounded hG L k hk hperB hperB hperB _ hops.curvature_local.1
    (meshAt L k 0 ^ 4) (fun _ => rfl) (fun _ => rfl) rB rB hcH hM (bH k hk)
    (bM k hk) p hp μPlus μMinus
  have hzero := hConstant L hL k hk μPlus μMinus p hp
  have sub1 : stripAddShift stripHalfWidth p ⊆ imStrip (2 * stripHalfWidth) := fun κ h => h.1
  have sub2 : stripSubShift stripHalfWidth p ⊆ imStrip (2 * stripHalfWidth) := fun κ h => h.1
  have enD : JetQuad.jetNorm stripHalfWidth p (covDerivDefectJet L k p μPlus μMinus) ≤
      ENNReal.ofReal (1 + 3 * jetComponentBound cD M) := by
    refine jetNorm_le_of_components xD (fun κ hκ => ?_) (fun κ hκ => ?_) (fun κ hκ => ?_) (fun κ hκ => ?_)
    · rw [(hzero κ hκ).1]
      exact quotHomNorm_zero_le_one
    · have e : (covDerivDefectJet L k p μPlus μMinus).f10 κ =
          (covDerivJet L k p μPlus μMinus).f10 κ := by
        simp [covDerivDefectJet, JetQuad.add, JetQuad.smul, JetQuad.ofKernel]
      rw [e]
      exact (cD'.1 κ (sub1 hκ)).1
    · have e : (covDerivDefectJet L k p μPlus μMinus).f01 κ =
          (covDerivJet L k p μPlus μMinus).f01 κ := by
        simp [covDerivDefectJet, JetQuad.add, JetQuad.smul, JetQuad.ofKernel]
      rw [e]
      exact (cD'.1 κ (sub2 hκ)).2
    · have e : (covDerivDefectJet L k p μPlus μMinus).f11 κ =
          (covDerivJet L k p μPlus μMinus).f11 κ := by
        simp [covDerivDefectJet, JetQuad.add, JetQuad.smul, JetQuad.ofKernel]
      rw [e]
      exact cD'.2 κ hκ
  have enE : JetQuad.jetNorm stripHalfWidth p (holonomyDefectJet L k p μPlus μMinus) ≤
      ENNReal.ofReal (1 + 3 * jetComponentBound cE M) :=
    jetNorm_le_of_components xE (fun κ hκ => by rw [(hzero κ hκ).2.1]; exact quotHomNorm_zero_le_one)
      (fun κ hκ => (cE'.1 κ (sub1 hκ)).1) (fun κ hκ => (cE'.1 κ (sub2 hκ)).2)
      (fun κ hκ => cE'.2 κ hκ)
  have enZ : JetQuad.jetNorm stripHalfWidth p (halfFaceTraceJet L k p μPlus μMinus) ≤
      ENNReal.ofReal (1 + 3 * jetComponentBound cZ M) :=
    jetNorm_le_of_components xZ (fun κ hκ => by rw [(hzero κ hκ).2.2.1]; exact quotHomNorm_id_le_one)
      (fun κ hκ => (cZ'.1 κ (sub1 hκ)).1) (fun κ hκ => (cZ'.1 κ (sub2 hκ)).2)
      (fun κ hκ => cZ'.2 κ hκ)
  have enH : JetQuad.jetNorm stripHalfWidth p (curvatureJet L k p μPlus μMinus) ≤
      ENNReal.ofReal (1 + 3 * jetComponentBound cH M) :=
    jetNorm_le_of_components xH (fun κ hκ => by rw [(hzero κ hκ).2.2.2]; exact quotHomNorm_zero_le_one)
      (fun κ hκ => (cH'.1 κ (sub1 hκ)).1) (fun κ hκ => (cH'.1 κ (sub2 hκ)).2)
      (fun κ hκ => cH'.2 κ hκ)
  have mono : ∀ {a b : ℝ}, a ≤ b → ENNReal.ofReal a ≤ ENNReal.ofReal b :=
    fun h => ENNReal.ofReal_le_ofReal h
  exact ⟨enD.trans (mono (by linarith)), enE.trans (mono (by linarith)),
    enZ.trans (mono (by linarith)), enH.trans (mono (by linarith))⟩
end YangMills.Construction.Tower.FullSpace.DefectJetBoundLemmas
end
