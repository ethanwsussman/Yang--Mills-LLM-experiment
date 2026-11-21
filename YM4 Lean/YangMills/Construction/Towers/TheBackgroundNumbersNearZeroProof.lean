import YangMills.Construction.Towers.PropertiesOfTheBackgroundsProof
import YangMills.Construction.Towers.TheBackgroundNumbersNearZero
import Mathlib
set_option autoImplicit false
open Set Filter Topology
noncomputable section
namespace YangMills.Construction.Tower.MassiveOpFunctions.BackgroundCoeffsNearZero
open Coordinates Matrices
open PeriodicOperators
open BackgroundFieldResponse (responseKernel)
open FullSpace
open FullSpace.BackgroundJets
open FullSpace.BackgroundProperties (responseOnAxis axisAmplitude)
section Holomorphic
variable {N : ℕ}
theorem isHolomorphicIn_mono {O O' : Set (ComplexCoordinates N)} {u : ComplexCoordinates N → ℂ}
    (h : ComplexCoordinates.IsHolomorphicIn (N' := 1) O fun z _ => u z) (hs : O' ⊆ O)
    (ho : IsOpen O') : ComplexCoordinates.IsHolomorphicIn (N' := 1) O' fun z _ => u z := by apply _root_.YangMills.Construction.Tower.FullSpace.BackgroundProperties.isHolomorphicIn_one_mono <;> assumption
theorem isHolomorphicIn_congr {O : Set (ComplexCoordinates N)} {u v : ComplexCoordinates N → ℂ}
    (h : ComplexCoordinates.IsHolomorphicIn (N' := 1) O fun z _ => u z) (e : EqOn v u O) :
    ComplexCoordinates.IsHolomorphicIn (N' := 1) O fun z _ => v z := by apply _root_.YangMills.Construction.Tower.FullSpace.BackgroundProperties.isHolomorphicIn_one_congr <;> assumption
theorem isHolomorphicIn_const_mul {O : Set (ComplexCoordinates N)} {u : ComplexCoordinates N → ℂ} (c : ℂ)
    (h : ComplexCoordinates.IsHolomorphicIn (N' := 1) O fun z _ => u z) :
    ComplexCoordinates.IsHolomorphicIn (N' := 1) O fun z _ => c * u z := by apply _root_.YangMills.Construction.Tower.FullSpace.BackgroundProperties.isHolomorphicIn_one_const_mul <;> assumption
theorem isHolomorphicIn_finset_sum {J : Type} (s : Finset J) {O : Set (ComplexCoordinates N)} (ho : IsOpen O)
    {u : J → ComplexCoordinates N → ℂ}
    (h : ∀ i ∈ s, ComplexCoordinates.IsHolomorphicIn (N' := 1) O fun z _ => u i z) :
    ComplexCoordinates.IsHolomorphicIn (N' := 1) O fun z _ => ∑ i ∈ s, u i z := by apply _root_.YangMills.Construction.Tower.FullSpace.BackgroundProperties.isHolomorphicIn_one_sum <;> assumption
end Holomorphic
theorem pauliCoeff_combination (x : Fin 3 → ℂ) (a : Fin 3) :
    pauliCoeff a (∑ b, x b • ComplexMatrix2.pauliFamily b) = x a := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.pauliCoeff_sum_smul <;> assumption
theorem smul_pauliZ_eq_combination (b : ℂ) :
    b • ComplexMatrix2.pauliFamily 2 = ∑ a, (Pi.single 2 b : Fin 3 → ℂ) a • ComplexMatrix2.pauliFamily a := by
  simp [Pi.single_apply]
theorem pauliCoeff_smul_pauliZ (b : ℂ) (a : Fin 3) :
    pauliCoeff a (b • ComplexMatrix2.pauliFamily 2) = (Pi.single 2 b : Fin 3 → ℂ) a := by
  rw [smul_pauliZ_eq_combination, pauliCoeff_combination]
theorem pauliFamily_two_ne_zero : ComplexMatrix2.pauliFamily 2 ≠ 0 := by
  intro h
  have e := pauliCoeff_smul_pauliZ 1 2
  rw [one_smul, h] at e
  have e₀ := pauliCoeff_smul_pauliZ 0 2
  rw [zero_smul] at e₀
  rw [e₀] at e
  simp at e
theorem pauliNorm_smul_pauliZ (b : ℂ) : pauliNorm (b • ComplexMatrix2.pauliFamily 2) = ‖b‖ := by
  simp [pauliNorm, pauliCoeff_smul_pauliZ, Fin.sum_univ_three, Pi.single_apply,
    Real.sqrt_sq (norm_nonneg b)]
theorem norm_le_pauliFamilyNorm (b : Fin 4 → ℂ) (ρ : Fin 4) :
    ‖b ρ‖ ≤ pauliFamilyNorm fun σ => b σ • ComplexMatrix2.pauliFamily 2 := by
  refine Real.le_sqrt_of_sq_le ?_
  simp only [pauliNorm_smul_pauliZ]
  exact Finset.single_le_sum (f := fun σ => ‖b σ‖ ^ 2) (fun σ _ => sq_nonneg _) (Finset.mem_univ ρ)
theorem stripHalfWidth_spec (hN : FreeStrip.ConstantsAdmissible.ConstantsAreAdmissible) :
    stripHalfWidth ∈ FreeStrip.halfSupRate ∧ 0 < stripHalfWidth ∧ stripHalfWidth ≤ 1 / 64 := by apply _root_.YangMills.Construction.Tower.FullSpace.BackgroundProperties.stripHalfWidth_spec <;> assumption
theorem responseOperators_atLevel (hN : FreeStrip.ConstantsAdmissible.ConstantsAreAdmissible)
    (hR : ResponseOperators.Claim) {L k : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L) (hk : 1 ≤ k) :
    ResponseOperators.AtLevel stripHalfWidth L k := by apply _root_.YangMills.Construction.Tower.FullSpace.BackgroundProperties.responseAtLevel <;> assumption
theorem constantEdgeForm_eq {L k : ℕ} (hs : meshAt L k k ≠ 0) (ε : Fin 4 → ComplexMatrix2)
    (β : FullSpace.Edge L k k) (μ : Fin 4)
    (hβ : β.terminal - β.initial = InfiniteLattice.axisStep (meshAt L k k) μ) :
    constantEdgeForm L k ε β = ε μ := by apply _root_.YangMills.Construction.Tower.FullSpace.BackgroundProperties.constantEdgeForm_eq <;> assumption
theorem constantEdgeForm_isQuotInvariant (hT : TowerTranslations.Claim) {L k : ℕ}
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hk : 1 ≤ k) (hs : meshAt L k k ≠ 0)
    (ε : Fin 4 → ComplexMatrix2) :
    IsQuotInvariant (colourEdges L k k) ((FullSpace.edgePauliCoordinates L k k).coeffs (constantEdgeForm L k ε)) := by apply _root_.YangMills.Construction.Tower.FullSpace.BackgroundProperties.isQuotInvariant_coeffs_constantEdgeForm <;> assumption
theorem constantFormAmplitude_mkQuot (hT : TowerTranslations.Claim) {L k : ℕ}
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hk : 1 ≤ k) (hs : meshAt L k k ≠ 0)
    (ε : Fin 4 → ComplexMatrix2) (a : Fin 3) (b : PeriodicOperators.PosEdge L k k) (ρ : Fin 4)
    (hb : b.1.terminal - b.1.initial = InfiniteLattice.axisStep (meshAt L k k) ρ) :
    constantFormAmplitude L k ε ((colourEdges L k k).mkQuot 1 (a, b)) =
      pauliCoeff a (ε ρ) := by
  have e := descendFn_mkQuot (constantEdgeForm_isQuotInvariant hT hL hk hs ε) (a, b)
  refine e.trans ?_
  show pauliCoeff a (constantEdgeForm L k ε b.1) = _
  rw [constantEdgeForm_eq hs ε _ ρ hb]
theorem axisPauliElement_apply (ρ μ : Fin 4) :
    axisPauliElement μ 2 ρ = (if ρ = μ then (1 : ℂ) else 0) • ComplexMatrix2.pauliFamily 2 := by
  by_cases h : ρ = μ
  · subst h
    simp [axisPauliElement]
  · simp [axisPauliElement, h]
theorem topEdgeComponent_axis (hT : TowerTranslations.Claim) {L k : ℕ}
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hk : 1 ≤ k) (hs : meshAt L k k ≠ 0) (μ ρ : Fin 4) :
    PlaneWaveCalculus.topEdgeComponent L k (constantFormAmplitude L k (axisPauliElement μ 2)) ρ =
      (if ρ = μ then (1 : ℂ) else 0) • ComplexMatrix2.pauliFamily 2 := by
  rw [smul_pauliZ_eq_combination]
  show ∑ a, constantFormAmplitude L k (axisPauliElement μ 2) ((colourEdges L k k).mkQuot 1
    (a, PlaneWaveCalculus.posEdgeAt L k k 0 ρ)) • ComplexMatrix2.pauliFamily a = _
  refine Finset.sum_congr rfl fun a _ => ?_
  congr 1
  rw [constantFormAmplitude_mkQuot hT hL hk hs _ a _ ρ (by simp [PlaneWaveCalculus.posEdgeAt,
    InfiniteLattice.Link.forwardFrom]), axisPauliElement_apply, pauliCoeff_smul_pauliZ]
theorem pauliFamilyNorm_axis (hT : TowerTranslations.Claim) {L k : ℕ}
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hk : 1 ≤ k) (hs : meshAt L k k ≠ 0) (μ : Fin 4) :
    pauliFamilyNorm (PlaneWaveCalculus.topEdgeComponent L k
      (constantFormAmplitude L k (axisPauliElement μ 2))) = 1 := by apply _root_.YangMills.Construction.Tower.FullSpace.BackgroundProperties.pauliFamilyNorm_axisPauliElement <;> assumption
theorem constantFormAmplitude_off_z (hT : TowerTranslations.Claim) {L k : ℕ}
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hk : 1 ≤ k) (hs : meshAt L k k ≠ 0) (μ : Fin 4)
    {a : Fin 3} (ha : a ≠ 2) (b : PeriodicOperators.PosEdge L k k) :
    constantFormAmplitude L k (axisPauliElement μ 2) ((colourEdges L k k).mkQuot 1 (a, b)) = 0 := by
  obtain ⟨ρ, hρ⟩ := b.2
  rw [constantFormAmplitude_mkQuot hT hL hk hs _ a b ρ hρ, axisPauliElement_apply, pauliCoeff_smul_pauliZ,
    Pi.single_eq_of_ne ha]
theorem waveAmplitude_blochWave (I : PeriodicData) (κ : Fin 4 → ℂ) (φ : I.UnitQuot → ℂ) :
    waveAmplitude I κ (blochWave I κ φ) = φ := by apply _root_.YangMills.Construction.Tower.FullSpace.BackgroundProperties.waveAmplitude_blochWave <;> assumption
theorem symbolHom_apply (I I' : PeriodicData) [Finite I.UnitQuot] (T : I'.Carrier → I.Carrier → ℂ)
    (κ : Fin 4 → ℂ) (φ : I.UnitQuot → ℂ) :
    symbolHom I I' T κ φ = applyKernel (quotSymbol I I' T κ) φ :=
  linearMapOfEntries_eq_applyKernel _ _
theorem applyKernel_axisWave {L k : ℕ} (hfin : Finite (colourEdges L k k).UnitQuot) {υ : ℝ}
    (hr : ResponseOperators.HasDecayRate (colourEdges L k k) (colourEdges L k 0) (responseKernel L k) υ)
    {q : Fin 4 → ℂ} (hq : q ∈ openImStrip υ) (μ : Fin 4) :
    applyKernel (responseKernel L k) (planeWaveOfConstant L k q (axisPauliElement μ 2)) =
        blochWave (colourEdges L k 0) q (responseAmplitude L k q μ) ∧
      responseAmplitude L k q μ = responseOnAxis L k q μ := by
  have e : applyKernel (responseKernel L k) (planeWaveOfConstant L k q (axisPauliElement μ 2)) =
      blochWave (colourEdges L k 0) q (responseOnAxis L k q μ) := by
    funext ι'
    refine (hr.applyKernel_blochWave q hq _ ι').2.trans ?_
    rw [responseOnAxis, symbolHom_apply]
  have e' : responseAmplitude L k q μ = responseOnAxis L k q μ := by
    rw [responseAmplitude, e, waveAmplitude_blochWave]
  exact ⟨by rw [e', e], e'⟩
theorem responseAmplitude_off_z (hT : TowerTranslations.Claim) {L k : ℕ}
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hk : 1 ≤ k) (hs : meshAt L k k ≠ 0)
    (htriv : IsColourTrivial (responseKernel L k)) {q : Fin 4 → ℂ} {μ : Fin 4}
    (hact : applyKernel (responseKernel L k) (planeWaveOfConstant L k q (axisPauliElement μ 2)) =
      blochWave (colourEdges L k 0) q (responseAmplitude L k q μ))
    {a : Fin 3} (ha : a ≠ 2) (b : PeriodicOperators.PosEdge L k 0) :
    responseAmplitude L k q μ ((colourEdges L k 0).mkQuot 1 (a, b)) = 0 := by
  have hz : applyKernel (responseKernel L k) (planeWaveOfConstant L k q (axisPauliElement μ 2)) (a, b) = 0 := by
    have e : ∀ ι : (colourEdges L k k).Carrier, responseKernel L k (a, b) ι *
        planeWaveOfConstant L k q (axisPauliElement μ 2) ι = 0 := by
      rintro ⟨a', b'⟩
      by_cases h : a = a'
      · subst h
        have : planeWaveOfConstant L k q (axisPauliElement μ 2) (a, b') = 0 := by
          show _ * constantFormAmplitude L k (axisPauliElement μ 2)
            ((colourEdges L k k).mkQuot 1 (a, b')) = 0
          rw [constantFormAmplitude_off_z hT hL hk hs μ ha b', mul_zero]
        rw [this, mul_zero]
      · rw [htriv.1 a' a b b' h, zero_mul]
    simp only [applyKernel, e, tsum_zero]
  rw [hact] at hz
  exact (mul_eq_zero.1 hz).resolve_left (Complex.exp_ne_zero _)
def zCoeff (L k : ℕ) (α : (colourEdges L k 0).UnitQuot → ℂ) (ρ : Fin 4)
    (m : Fin 4 → ℤ) : ℂ :=
  ((finestMesh L k ^ 4 : ℝ) : ℂ) * ∑ᶠ c : PlaneWaves.VertexClass L k,
    PlaneWaves.fourierPhase m (Quot.out c : FullSpace.Vertex L k 0) *
      α ((colourEdges L k 0).mkQuot 1 (2, PlaneWaves.edgeAt L k (Quot.out c) ρ))
theorem edgeFourierCoeff_of_z {L k : ℕ} {α : (colourEdges L k 0).UnitQuot → ℂ}
    (hα : ∀ (a : Fin 3), a ≠ 2 → ∀ b, α ((colourEdges L k 0).mkQuot 1 (a, b)) = 0)
    (ρ : Fin 4) (m : Fin 4 → ℤ) :
    PlaneWaves.edgeFourierCoeff L k α ρ m = zCoeff L k α ρ m • ComplexMatrix2.pauliFamily 2 := by
  have hform : ∀ b, PlaneWaves.edgeFieldOfClasses L k α b =
      α ((colourEdges L k 0).mkQuot 1 (2, b)) • ComplexMatrix2.pauliFamily 2 := fun b => by
    show ∑ a, α ((colourEdges L k 0).mkQuot 1 (a, b)) • ComplexMatrix2.pauliFamily a = _
    rw [Fin.sum_univ_three, hα 0 (by decide) b, hα 1 (by decide) b]
    simp
  simp only [PlaneWaves.edgeFourierCoeff, PlaneWaves.fourierCoeff, zCoeff, hform]
  rw [mul_smul, finsum_smul]
  simp only [mul_smul]
theorem backgroundCoeff_eq_zCoeff {L k : ℕ} {q : Fin 4 → ℂ} {μ : Fin 4}
    (hα : ∀ (a : Fin 3), a ≠ 2 → ∀ b,
      responseAmplitude L k q μ ((colourEdges L k 0).mkQuot 1 (a, b)) = 0)
    (ρ : Fin 4) (m : Fin 4 → ℤ) :
    backgroundCoeff L k q μ ρ m = zCoeff L k (responseAmplitude L k q μ) ρ m := by
  have h := edgeFourierCoeff_of_z hα ρ m
  have hs : PlaneWaves.edgeFourierCoeff L k (responseAmplitude L k q μ) ρ m =
      backgroundCoeff L k q μ ρ m • ComplexMatrix2.pauliFamily 2 :=
    Classical.epsilon_spec (p := fun b => PlaneWaves.edgeFourierCoeff L k
      (responseAmplitude L k q μ) ρ m = b • ComplexMatrix2.pauliFamily 2) ⟨_, h⟩
  exact smul_left_injective ℂ pauliFamily_two_ne_zero (hs.symm.trans h)
theorem finite_vertexClass {L k : ℕ} (h : Finite (colourVertices L k 0).UnitQuot) :
    Finite (PlaneWaves.VertexClass L k) := by apply _root_.YangMills.Construction.Tower.ResponseBoundProof.finite_vertexClass <;> assumption
theorem zCoeff_isHolomorphicIn {L k : ℕ} (hfin : Finite (PlaneWaves.VertexClass L k))
    {O : Set (Fin 4 → ℂ)} (ho : IsOpen O) {A : (Fin 4 → ℂ) → (colourEdges L k 0).UnitQuot → ℂ}
    (hA : ∀ c, ComplexCoordinates.IsHolomorphicIn (N := 4) (N' := 1) O fun q _ => A q c)
    (ρ : Fin 4) (m : Fin 4 → ℤ) :
    ComplexCoordinates.IsHolomorphicIn (N := 4) (N' := 1) O fun q _ =>
      zCoeff L k (A q) ρ m := by
  let _ := Fintype.ofFinite (PlaneWaves.VertexClass L k)
  simp only [zCoeff, finsum_eq_sum_of_fintype]
  exact isHolomorphicIn_const_mul _ (isHolomorphicIn_finset_sum (N := 4) Finset.univ ho
    fun c _ => isHolomorphicIn_const_mul _ (hA _))
theorem claim_holds (hN : FreeStrip.ConstantsAdmissible.ConstantsAreAdmissible)
    (hR : ResponseOperators.Claim) (hP : ResponseProperties.AllProperties)
    (hB : FullSpace.BackgroundProperties.BackgroundPropertiesHold)
    (hT : TowerTranslations.Claim) (hI : TowerIndexSets.Claim) :
    Claim := by
  intro L hL k hk
  obtain ⟨hmem, hpos, hle⟩ := stripHalfWidth_spec hN
  have hs : meshAt L k k ≠ 0 := by simp [meshAt]
  have ht := responseOperators_atLevel hN hR hL hk
  obtain ⟨pS, pB, _⟩ := hI L hL k 0 (Nat.zero_le k)
  obtain ⟨_, pBk, _⟩ := hI L hL k k le_rfl
  have hfinB : Finite (colourEdges L k k).UnitQuot := pBk.finite_quot
  have hfinS : Finite (PlaneWaves.VertexClass L k) := finite_vertexClass pS.finite_quot
  obtain ⟨υ, hυ, _, hr, _⟩ := ht.exists_rate
  obtain ⟨C, N, hN₀, hbeh⟩ := hP.2.2.2 stripHalfWidth hmem L hL k hk
  have hnear := fun μ : Fin 4 => (hB L hL k hk).exists_nhds μ μ
  choose O₁ hO₁open hO₁sub hO₁on using hnear
  let O : Set (Fin 4 → ℂ) :=
    interior N ∩ ((⋂ μ, O₁ μ) ∩ ⋂ μ : Fin 4, {q : Fin 4 → ℂ | ‖q μ‖ < stripHalfWidth})
  have hOopen : IsOpen O := by
    refine isOpen_interior.inter ((isOpen_iInter_of_finite hO₁open).inter
      (isOpen_iInter_of_finite fun μ => ?_))
    exact isOpen_lt (continuous_norm.comp (continuous_apply μ)) continuous_const
  have hOmem : (0 : Fin 4 → ℂ) ∈ O := by
    refine ⟨mem_interior_iff_mem_nhds.2 hN₀, mem_iInter.2 fun μ => hO₁sub μ fun ρ => ?_,
      mem_iInter.2 fun μ => ?_⟩
    · simpa using hpos.le
    · simpa using hpos
  have hOpoly : O ⊆ momentumPolydisc stripHalfWidth := fun q hq μ =>
    (mem_iInter.1 hq.2.2 μ).le
  have hstrip : ∀ q ∈ O, q ∈ openImStrip υ := fun q hq ρ => by
    have := (Complex.abs_im_le_norm (q ρ)).trans (hOpoly hq ρ)
    linarith
  have hfacts := fun q (hq : q ∈ O) (μ : Fin 4) => applyKernel_axisWave hfinB hr (hstrip q hq) μ
  have hcolour : ∀ q ∈ O, ∀ μ : Fin 4, ∀ a : Fin 3, a ≠ 2 → ∀ b,
      responseAmplitude L k q μ ((colourEdges L k 0).mkQuot 1 (a, b)) = 0 :=
    fun q hq μ a ha b => responseAmplitude_off_z hT hL hk hs ht.resp_real.2 (hfacts q hq μ).1 ha b
  have hcoef : ∀ q ∈ O, ∀ (μ ρ : Fin 4) (m : Fin 4 → ℤ),
      PlaneWaves.edgeFourierCoeff L k (responseAmplitude L k q μ) ρ m =
        backgroundCoeff L k q μ ρ m • ComplexMatrix2.pauliFamily 2 := fun q hq μ ρ m => by
    rw [backgroundCoeff_eq_zCoeff (hcolour q hq μ)]
    exact edgeFourierCoeff_of_z (hcolour q hq μ) ρ m
  refine ⟨O, hOopen, hOmem, hOpoly, fun q hq μ ρ m _ => hcoef q hq μ ρ m,
    fun μ ρ m _ => ?_, C, fun q hq μ ρ => ?_⟩
  · have hA : ∀ c, ComplexCoordinates.IsHolomorphicIn (N := 4) (N' := 1) O
        fun q _ => responseAmplitude L k q μ c := fun c => by
      have h₁ := isHolomorphicIn_mono ((hO₁on μ).amplitude_pos.2.2 c)
        (fun q hq => mem_iInter.1 hq.2.1 μ) hOopen
      refine isHolomorphicIn_congr h₁ fun q hq => ?_
      show responseAmplitude L k q μ c = axisAmplitude L k q μ c
      rw [axisAmplitude, if_pos (hOpoly hq)]
    have h₂ := zCoeff_isHolomorphicIn hfinS hOopen hA ρ m
    exact isHolomorphicIn_congr h₂ fun q hq => backgroundCoeff_eq_zCoeff (hcolour q hq μ) ρ m
  · have hpoint : ResponseProperties.InFundamentalStrip stripHalfWidth q := by
      refine ⟨fun σ => ?_, fun σ => ?_⟩
      · have := (Complex.abs_im_le_norm (q σ)).trans (hOpoly hq σ)
        linarith
      · have h₁ := (Complex.abs_re_le_norm (q σ)).trans (hOpoly hq σ)
        have h₂ := Real.pi_gt_three
        linarith
    obtain ⟨b₁, b₂, _⟩ := hbeh q (interior_subset hq.1) hpoint
      (constantFormAmplitude L k (axisPauliElement μ 2))
    have e : ResponseProperties.responseSymbolForm L k q
        (constantFormAmplitude L k (axisPauliElement μ 2)) = responseAmplitude L k q μ :=
      (hfacts q hq μ).2.symm
    rw [e, pauliFamilyNorm_axis hT hL hk hs μ, mul_one] at b₁ b₂
    refine ⟨fun m hm hm0 => ?_, ?_⟩
    · refine (le_trans ?_ (b₁ m hm hm0))
      simp only [hcoef q hq μ _ m]
      exact norm_le_pauliFamilyNorm (fun σ => backgroundCoeff L k q μ σ m) ρ
    · refine le_trans ?_ b₂
      have e₂ : (fun σ => PlaneWaves.edgeFourierCoeff L k (responseAmplitude L k q μ) σ 0 -
            PlaneWaveCalculus.topEdgeComponent L k (constantFormAmplitude L k (axisPauliElement μ 2)) σ) =
          fun σ => (backgroundCoeff L k q μ σ 0 - if σ = μ then 1 else 0) • ComplexMatrix2.pauliFamily 2 := by
        funext σ
        rw [hcoef q hq μ σ 0, topEdgeComponent_axis hT hL hk hs μ σ, sub_smul]
      rw [e₂]
      exact norm_le_pauliFamilyNorm (fun σ => backgroundCoeff L k q μ σ 0 - if σ = μ then 1 else 0) ρ
end YangMills.Construction.Tower.MassiveOpFunctions.BackgroundCoeffsNearZero
end
