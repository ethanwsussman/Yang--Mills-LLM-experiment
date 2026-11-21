import YangMills.Construction.Towers.TheBackgroundNumbersNearZeroProof
import YangMills.Construction.Towers.TheBackgroundNumbersOnTheRealPolydisc
import Mathlib
set_option autoImplicit false
open Set Filter Topology
noncomputable section
namespace YangMills.Construction.Tower.MassiveOpFunctions.BackgroundCoeffsOnRealPolydisc
open YangMills.Construction.PeriodicOperators
open YangMills.Construction.Tower.BackgroundFieldResponse (responseKernel)
open YangMills.Construction.Tower.FullSpace
open YangMills.Construction.Tower.FullSpace.BackgroundJets
open YangMills.Construction.Tower.FullSpace.BackgroundProperties (responseOnAxis axisAmplitude)
theorem pauliFamily_two_ne_zero : Matrices.ComplexMatrix2.pauliFamily 2 ≠ 0 := by apply _root_.YangMills.Construction.Tower.MassiveOpFunctions.BackgroundCoeffsNearZero.pauliFamily_two_ne_zero <;> assumption
theorem stripHalfWidth_properties (hN : FreeStrip.ConstantsAdmissible.ConstantsAreAdmissible) :
    stripHalfWidth ∈ FreeStrip.halfSupRate ∧ 0 < stripHalfWidth ∧ stripHalfWidth ≤ 1 / 64 := by apply _root_.YangMills.Construction.Tower.FullSpace.BackgroundProperties.stripHalfWidth_spec <;> assumption
theorem atLevel_stripHalfWidth (hN : FreeStrip.ConstantsAdmissible.ConstantsAreAdmissible)
    (hR : ResponseOperators.Claim) {L k : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hk : 1 ≤ k) :
    ResponseOperators.AtLevel stripHalfWidth L k := by apply _root_.YangMills.Construction.Tower.FullSpace.BackgroundProperties.responseAtLevel <;> assumption
theorem applyKernel_planeWaveOfConstant_axis {L k : ℕ}
    (hfin : Finite (colourEdges L k k).UnitQuot) {υ : ℝ}
    (hr : ResponseOperators.HasDecayRate (colourEdges L k k) (colourEdges L k 0)
      (responseKernel L k) υ)
    {q : Fin 4 → ℂ} (hq : q ∈ openImStrip υ) (μ : Fin 4) :
    applyKernel (responseKernel L k) (planeWaveOfConstant L k q (axisPauliElement μ 2)) =
        blochWave (colourEdges L k 0) q (responseAmplitude L k q μ) ∧
      responseAmplitude L k q μ = responseOnAxis L k q μ := by apply _root_.YangMills.Construction.Tower.MassiveOpFunctions.BackgroundCoeffsNearZero.applyKernel_axisWave <;> assumption
theorem responseAmplitude_of_ne (hT : TowerTranslations.Claim) {L k : ℕ}
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hk : 1 ≤ k) (hs : meshAt L k k ≠ 0)
    (htriv : IsColourTrivial (responseKernel L k)) {q : Fin 4 → ℂ} {μ : Fin 4}
    (hact : applyKernel (responseKernel L k) (planeWaveOfConstant L k q (axisPauliElement μ 2)) =
      blochWave (colourEdges L k 0) q (responseAmplitude L k q μ))
    {a : Fin 3} (ha : a ≠ 2) (b : PosEdge L k 0) :
    responseAmplitude L k q μ ((colourEdges L k 0).mkQuot 1 (a, b)) = 0 := by apply _root_.YangMills.Construction.Tower.MassiveOpFunctions.BackgroundCoeffsNearZero.responseAmplitude_off_z <;> assumption
def thirdFourierCoeff (L k : ℕ) (α : (colourEdges L k 0).UnitQuot → ℂ) (ν : Fin 4)
    (m : Fin 4 → ℤ) : ℂ :=
  ((finestMesh L k ^ 4 : ℝ) : ℂ) * ∑ᶠ c : PlaneWaves.VertexClass L k,
    PlaneWaves.fourierPhase m (Quot.out c : FullSpace.Vertex L k 0) *
      α ((colourEdges L k 0).mkQuot 1 (2, PlaneWaves.edgeAt L k (Quot.out c) ν))
theorem edgeFourierCoeff_eq_smul_pauliFamily_two {L k : ℕ}
    {α : (colourEdges L k 0).UnitQuot → ℂ}
    (hα : ∀ (a : Fin 3), a ≠ 2 → ∀ b, α ((colourEdges L k 0).mkQuot 1 (a, b)) = 0)
    (ν : Fin 4) (m : Fin 4 → ℤ) :
    PlaneWaves.edgeFourierCoeff L k α ν m =
      thirdFourierCoeff L k α ν m • Matrices.ComplexMatrix2.pauliFamily 2 := by
  have hform : ∀ b, PlaneWaves.edgeFieldOfClasses L k α b =
      α ((colourEdges L k 0).mkQuot 1 (2, b)) • Matrices.ComplexMatrix2.pauliFamily 2 := fun b => by
    show ∑ a, α ((colourEdges L k 0).mkQuot 1 (a, b)) • Matrices.ComplexMatrix2.pauliFamily a = _
    rw [Fin.sum_univ_three, hα 0 (by decide) b, hα 1 (by decide) b]
    simp
  simp only [PlaneWaves.edgeFourierCoeff, PlaneWaves.fourierCoeff, thirdFourierCoeff, hform]
  rw [mul_smul, finsum_smul]
  simp only [mul_smul]
theorem backgroundCoeff_eq_thirdFourierCoeff {L k : ℕ} {q : Fin 4 → ℂ} {μ : Fin 4}
    (hα : ∀ (a : Fin 3), a ≠ 2 → ∀ b,
      responseAmplitude L k q μ ((colourEdges L k 0).mkQuot 1 (a, b)) = 0)
    (ν : Fin 4) (m : Fin 4 → ℤ) :
    backgroundCoeff L k q μ ν m = thirdFourierCoeff L k (responseAmplitude L k q μ) ν m := by
  have h := edgeFourierCoeff_eq_smul_pauliFamily_two hα ν m
  have hs : PlaneWaves.edgeFourierCoeff L k (responseAmplitude L k q μ) ν m =
      backgroundCoeff L k q μ ν m • Matrices.ComplexMatrix2.pauliFamily 2 :=
    Classical.epsilon_spec (p := fun z => PlaneWaves.edgeFourierCoeff L k
      (responseAmplitude L k q μ) ν m = z • Matrices.ComplexMatrix2.pauliFamily 2) ⟨_, h⟩
  exact smul_left_injective ℂ pauliFamily_two_ne_zero (hs.symm.trans h)
theorem finite_vertexClass {L k : ℕ} (h : Finite (colourVertices L k 0).UnitQuot) :
    Finite (PlaneWaves.VertexClass L k) := by apply _root_.YangMills.Construction.Tower.ResponseBoundProof.finite_vertexClass <;> assumption
theorem thirdFourierCoeff_continuousOn {L k : ℕ} (hfin : Finite (PlaneWaves.VertexClass L k))
    {O : Set (Fin 4 → ℂ)} {A : (Fin 4 → ℂ) → (colourEdges L k 0).UnitQuot → ℂ}
    (hA : ∀ c, ContinuousOn (fun q => A q c) O) (ν : Fin 4) (m : Fin 4 → ℤ) :
    ContinuousOn (fun q => thirdFourierCoeff L k (A q) ν m) O := by
  let _ := Fintype.ofFinite (PlaneWaves.VertexClass L k)
  simp only [thirdFourierCoeff, finsum_eq_sum_of_fintype]
  exact continuousOn_const.mul (continuousOn_finsetSum _ fun c _ => continuousOn_const.mul (hA _))
theorem claim_holds (hN : FreeStrip.ConstantsAdmissible.ConstantsAreAdmissible)
    (hR : ResponseOperators.Claim) (hB : FullSpace.BackgroundProperties.BackgroundPropertiesHold)
    (hT : TowerTranslations.Claim) (hI : TowerIndexSets.Claim) :
    Claim := by
  intro L hL k hk
  obtain ⟨_, hpos, _⟩ := stripHalfWidth_properties hN
  have hs : meshAt L k k ≠ 0 := by simp [meshAt]
  have ht := atLevel_stripHalfWidth hN hR hL hk
  obtain ⟨pS, _, _⟩ := hI L hL k 0 (Nat.zero_le k)
  obtain ⟨_, pBk, _⟩ := hI L hL k k le_rfl
  have hfinB : Finite (colourEdges L k k).UnitQuot := pBk.finite_quot
  have hfinS : Finite (PlaneWaves.VertexClass L k) := finite_vertexClass pS.finite_quot
  obtain ⟨υ, hυ, _, hr, _⟩ := ht.exists_rate
  have hstrip : ∀ q ∈ momentumPolydisc stripHalfWidth, q ∈ openImStrip υ := fun q hq ν => by
    have := (Complex.abs_im_le_norm (q ν)).trans (hq ν)
    linarith
  have hcolour : ∀ q ∈ momentumPolydisc stripHalfWidth, ∀ μ : Fin 4, ∀ a : Fin 3, a ≠ 2 → ∀ b,
      responseAmplitude L k q μ ((colourEdges L k 0).mkQuot 1 (a, b)) = 0 :=
    fun q hq μ a ha b => responseAmplitude_of_ne hT hL hk hs ht.resp_real.2
      (applyKernel_planeWaveOfConstant_axis hfinB hr (hstrip q hq) μ).1 ha b
  refine ⟨fun p hp μ ν m _ => ?_, fun μ ν m _ => ?_⟩
  · rw [backgroundCoeff_eq_thirdFourierCoeff (hcolour _ hp μ)]
    exact edgeFourierCoeff_eq_smul_pauliFamily_two (hcolour _ hp μ) ν m
  · obtain ⟨O, _, hsub, hon⟩ := (hB L hL k hk).exists_nhds μ μ
    have hA : ∀ c, ContinuousOn (fun q => axisAmplitude L k q μ c) O := fun c =>
      continuousOn_pi.1 (hon.amplitude_pos.2.2 c).2.1 0
    have hcv : Continuous toComplexVec :=
      continuous_pi fun i => Complex.continuous_ofReal.comp (continuous_apply i)
    refine ((thirdFourierCoeff_continuousOn hfinS hA ν m).comp hcv.continuousOn
      fun p hp => hsub hp).congr fun p hp => ?_
    show backgroundCoeff L k (toComplexVec p) μ ν m =
      thirdFourierCoeff L k (axisAmplitude L k (toComplexVec p) μ) ν m
    have hp' : toComplexVec p ∈ momentumPolydisc stripHalfWidth := hp
    rw [axisAmplitude, if_pos hp']
    exact backgroundCoeff_eq_thirdFourierCoeff (hcolour _ hp' μ) ν m
end YangMills.Construction.Tower.MassiveOpFunctions.BackgroundCoeffsOnRealPolydisc
end
