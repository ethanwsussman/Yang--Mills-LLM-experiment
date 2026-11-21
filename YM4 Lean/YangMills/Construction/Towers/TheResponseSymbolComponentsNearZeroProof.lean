import YangMills.Construction.Towers.FormsOfTheFreeOperatorsInCoefficientsProof
import YangMills.Construction.Towers.AveragesOfTheScaledPictureAreLocalProof
import YangMills.Construction.Towers.SymbolOfTheTotalNormaliserIsATemperingChoiceProof
import YangMills.Construction.Towers.TheMixedDerivativeOfTheMassiveFunctionProof
import YangMills.Construction.Towers.TheResponseSymbolComponentsNearZero
import YangMills.Construction.Towers.TheResponseSymbolNearTheStripProof
import YangMills.Construction.Towers.TheTrialFormOfTheResponseNearZeroProof
import Mathlib
set_option autoImplicit false
open Set Filter Topology
noncomputable section
namespace YangMills.Construction.Tower.ResponseSymbolNearZero
open YangMills.Construction.PeriodicOperators hiding addIVec
open YangMills.Construction.PeriodicOperators.LogDetSecondDerivs (descendField)
open YangMills.Construction.Matrices (ComplexMatrix2)
open BackgroundFieldResponse (responseKernel responseDefect)
open PlaneWaveCalculus (EdgeCoeffFacts posEdgeAt topEdgeComponent integerWave)
open PlaneWaves
open ResponseProperties (SmallMomentumBehaviour InFundamentalStrip responseSymbolForm defectSymbol)
open FreeStrip (admissibleRates halfSupRate)
open FullSpace
section Colour
theorem pauliCoeff_combination (x : Fin 3 → ℂ) (a : Fin 3) :
    pauliCoeff a (∑ b, x b • ComplexMatrix2.pauliFamily b) = x a := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.pauliCoeff_sum_smul <;> assumption
theorem pauliCoeff_smul (a : Fin 3) (c : ℂ) {X : ComplexMatrix2} (h : X ∈ ComplexMatrix2.traceless) :
    pauliCoeff a (c • X) = c * pauliCoeff a X := by apply _root_.YangMills.SharedProofs.p5172 <;> assumption
theorem pauliCoeff_sub (a : Fin 3) {X Y : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.traceless)
    (hY : Y ∈ ComplexMatrix2.traceless) :
    pauliCoeff a (X - Y) = pauliCoeff a X - pauliCoeff a Y := by apply _root_.YangMills.Construction.Tower.DiagonalSymbolBounds.pauliCoeff_sub <;> assumption
theorem pauliNorm_add_le {X Y : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.traceless)
    (hY : Y ∈ ComplexMatrix2.traceless) :
    pauliNorm (X + Y) ≤ pauliNorm X + pauliNorm Y := by apply _root_.YangMills.Construction.Tower.ResponseBoundProof.pauliNorm_add_le <;> assumption
theorem pauliNorm_smul (c : ℂ) {X : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.traceless) :
    pauliNorm (c • X) = ‖c‖ * pauliNorm X := by apply _root_.YangMills.Construction.Tower.ResponseBoundProof.pauliNorm_smul <;> assumption
theorem pauliNorm_sum_le {ι : Type} (s : Finset ι) (X : ι → ComplexMatrix2)
    (h : ∀ i, X i ∈ ComplexMatrix2.traceless) :
    pauliNorm (∑ i ∈ s, X i) ≤ ∑ i ∈ s, pauliNorm (X i) := by apply _root_.YangMills.Construction.Tower.TrialResponse.pauliNorm_sum_le <;> assumption
theorem pauliNorm_le_familyNorm (F : Fin 4 → ComplexMatrix2) (μ : Fin 4) :
    pauliNorm (F μ) ≤ pauliFamilyNorm F := by apply _root_.YangMills.Construction.Tower.ResponseBoundProof.pauliNorm_le_familyNorm <;> assumption
theorem pauliFamilyNorm_nonneg (F : Fin 4 → ComplexMatrix2) : 0 ≤ pauliFamilyNorm F :=
  Real.sqrt_nonneg _
theorem norm_pauliCoeff_le (a : Fin 3) (X : ComplexMatrix2) : ‖pauliCoeff a X‖ ≤ pauliNorm X := by
  refine (le_abs_self _).trans (Real.abs_le_sqrt ?_)
  exact Finset.single_le_sum (f := fun b => ‖pauliCoeff b X‖ ^ 2)
    (fun _ _ => sq_nonneg _) (Finset.mem_univ a)
theorem ofPauliCoeffs_mem {σ : Type} (c : Fin 3 × σ → ℂ) (x : σ) :
    ofPauliCoeffs c x ∈ ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.ofPauliCoeffs_mem <;> assumption
end Colour
theorem waveAmplitude_blochWave (I : PeriodicData) (κ : Fin 4 → ℂ) (φ : I.UnitQuot → ℂ) :
    waveAmplitude I κ (blochWave I κ φ) = φ := by apply _root_.YangMills.Construction.Tower.FullSpace.BackgroundProperties.waveAmplitude_blochWave <;> assumption
theorem smul_blochWave (I : PeriodicData) (κ : Fin 4 → ℂ) (z : ℂ) (φ : I.UnitQuot → ℂ) :
    z • blochWave I κ φ = blochWave I κ (z • φ) := by apply _root_.YangMills.Construction.Tower.ResponseSymbolNearStrip.smul_blochWave <;> assumption
theorem applyKernel_blochWave_eq {I I' : PeriodicData} [Finite I.UnitQuot]
    {T : I'.Carrier → I.Carrier → ℂ} {κ : Fin 4 → ℂ} {φ : I.UnitQuot → ℂ}
    (h : ∀ ι', applyKernel T (blochWave I κ φ) ι' =
      blochWave I' κ (applyKernel (quotSymbol I I' T κ) φ) ι') :
    applyKernel T (blochWave I κ φ) = blochWave I' κ (symbolHom I I' T κ φ) := by apply _root_.YangMills.Construction.Tower.ResponseSymbolNearStrip.applyKernel_blochWave_eq <;> assumption
theorem linearMap_apply_eq_sum {J J' : Type} [Fintype J] (M : (J → ℂ) →ₗ[ℂ] (J' → ℂ))
    (f : J → ℂ) (c' : J') :
    M f c' = ∑ c, linearMapEntry M c' c * f c := by apply _root_.YangMills.Construction.PeriodicOperators.HomNorm.apply_eq_sum_linearMapEntry <;> assumption
section Components
variable {L k : ℕ} [Finite (colourEdges L k k).UnitQuot] {υ : ℝ} {p : Fin 4 → ℂ}
theorem defectOfWave_eq
    (hn : ResponseOperators.HasDecayRate (colourEdges L k k) (colourEdges L k k)
      (responseDefect L k) υ)
    (hp : p ∈ openImStrip υ) (ε : Fin 4 → ComplexMatrix2) :
    defectOfWave L k p ε =
      blochWave (colourEdges L k k) p (defectSymbol L k p (constantFormAmplitude L k ε)) := by apply _root_.YangMills.Construction.Tower.ResponseSymbolNearStrip.defectOfWave_eq <;> assumption
theorem backgroundResponseSymbol_eq
    (hr : ResponseOperators.HasDecayRate (colourEdges L k k) (colourEdges L k 0)
      (responseKernel L k) υ)
    (hp : p ∈ openImStrip υ) (ε : Fin 4 → ComplexMatrix2) :
    backgroundResponseSymbol L k p ε =
      ((finestMesh L k : ℝ) : ℂ) • responseSymbolForm L k p (constantFormAmplitude L k ε) := by apply _root_.YangMills.Construction.Tower.ResponseSymbolNearStrip.backgroundResponseSymbol_eq <;> assumption
theorem coarseResponseSymbol_eq
    (hn : ResponseOperators.HasDecayRate (colourEdges L k k) (colourEdges L k k)
      (responseDefect L k) υ)
    (hp : p ∈ openImStrip υ) (ε : Fin 4 → ComplexMatrix2) :
    coarseResponseSymbol L k p ε = defectSymbol L k p (constantFormAmplitude L k ε) := by apply _root_.YangMills.Construction.Tower.ResponseSymbolNearStrip.coarseResponseSymbol_eq <;> assumption
theorem crossingSmoothingTranspose_blochWave (hQ : TransposeKernelProps L k) (p : Fin 4 → ℂ)
    (φ : (colourEdges L k k).UnitQuot → ℂ) :
    crossingSmoothingTranspose L k (blochWave (colourEdges L k k) p φ) =
      blochWave (colourEdges L k 0) p
        (symbolHom (colourEdges L k k) (colourEdges L k 0)
          (crossingSmoothingTransposeKernel L k) p φ) := by apply _root_.YangMills.Construction.Tower.ResponseSymbolNearStrip.crossingSmoothingTranspose_blochWave <;> assumption
theorem sourceResponseSymbol_eq (hQ : TransposeKernelProps L k)
    (hn : ResponseOperators.HasDecayRate (colourEdges L k k) (colourEdges L k k)
      (responseDefect L k) υ)
    (hp : p ∈ openImStrip υ) (ε : Fin 4 → ComplexMatrix2) :
    sourceResponseSymbol L k p ε =
      symbolHom (colourEdges L k k) (colourEdges L k 0) (crossingSmoothingTransposeKernel L k) p
        (defectSymbol L k p (constantFormAmplitude L k ε)) := by
  rw [sourceResponseSymbol, defectOfWave_eq hn hp, crossingSmoothingTranspose_blochWave hQ,
    waveAmplitude_blochWave]
end Components
section Constant
variable {L k j : ℕ}
theorem axisStep_injective {a : ℝ} (ha : a ≠ 0) {μ ρ : Fin 4}
    (h : InfiniteLattice.axisStep a μ = InfiniteLattice.axisStep a ρ) : μ = ρ := by apply _root_.YangMills.Construction.Tower.FacesContainingEdge.axisStep_injective <;> assumption
def constantEdgeForm (L k j : ℕ) (ε : Fin 4 → ComplexMatrix2) : FullSpace.Edge L k j → ComplexMatrix2 :=
  open Classical in
  FullSpace.extendOddly fun b : FullSpace.Edge L k j =>
    ∑ ρ, if b.terminal - b.initial = InfiniteLattice.axisStep (meshAt L k j) ρ then ε ρ else 0
theorem constantEdgeForm_apply (hs : meshAt L k j ≠ 0) (ε : Fin 4 → ComplexMatrix2)
    (β : FullSpace.Edge L k j) (μ : Fin 4)
    (hβ : β.terminal - β.initial = InfiniteLattice.axisStep (meshAt L k j) μ) :
    constantEdgeForm L k j ε β = ε μ := by
  have pos : β.IsPositivelyOriented := ⟨μ, hβ⟩
  simp only [constantEdgeForm, FullSpace.extendOddly, if_pos pos, hβ]
  rw [Finset.sum_eq_single μ]
  · simp
  · intro ρ _ hρ
    rw [if_neg fun e => hρ (axisStep_injective hs e).symm]
  · simp
theorem constantEdgeForm_quotInvariant (hT : PeriodicOperators.TowerTranslations.Claim)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hk : 1 ≤ k) (hj : j ≤ k)
    (hs : meshAt L k j ≠ 0) (ε : Fin 4 → ComplexMatrix2) :
    IsQuotInvariant (colourEdges L k j)
      ((FullSpace.edgePauliCoordinates L k j).coeffs (constantEdgeForm L k j ε)) := by
  have hstep : ∀ ι ι' : (colourEdges L k j).Carrier,
      (∃ n : Fin 4 → ℤ, ι' = (colourEdges L k j).translate (1 • n) ι) →
        (FullSpace.edgePauliCoordinates L k j).coeffs (constantEdgeForm L k j ε) ι =
          (FullSpace.edgePauliCoordinates L k j).coeffs (constantEdgeForm L k j ε) ι' := by
    rintro ⟨a, b⟩ _ ⟨n, rfl⟩
    obtain ⟨μ, hμ⟩ := b.2
    rw [(hT L hL k j hk hj (1 • n)).2.2.2.1 a b μ hμ]
    show pauliCoeff a (constantEdgeForm L k j ε b.1) =
      pauliCoeff a (constantEdgeForm L k j ε (InfiniteLattice.Link.forwardFrom _ μ))
    rw [constantEdgeForm_apply hs ε b.1 μ hμ,
      constantEdgeForm_apply hs ε _ μ (by simp [InfiniteLattice.Link.forwardFrom])]
  intro ι ι' e
  exact congrArg (Quot.lift _ hstep) e
theorem descendField_constantEdgeForm (hT : PeriodicOperators.TowerTranslations.Claim)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hk : 1 ≤ k) (hj : j ≤ k)
    (hs : meshAt L k j ≠ 0) (ε : Fin 4 → ComplexMatrix2) (a : Fin 3)
    (b : PeriodicOperators.PosEdge L k j) (ρ : Fin 4)
    (hb : b.1.terminal - b.1.initial = InfiniteLattice.axisStep (meshAt L k j) ρ) :
    descendField (colourEdges L k j) 1
        ((FullSpace.edgePauliCoordinates L k j).coeffs (constantEdgeForm L k j ε))
        ((colourEdges L k j).mkQuot 1 (a, b)) =
      pauliCoeff a (ε ρ) := by
  have e := descendFn_mkQuot (constantEdgeForm_quotInvariant hT hL hk hj hs ε) (a, b)
  refine e.trans ?_
  show pauliCoeff a (constantEdgeForm L k j ε b.1) = _
  rw [constantEdgeForm_apply hs ε _ ρ hb]
end Constant
section Classes
variable {L k : ℕ}
theorem meshAt_self (L k : ℕ) : meshAt L k k = 1 := by apply _root_.YangMills.Construction.Tower.FullSpace.IterTransposesOnFullSpace.meshAt_self <;> assumption
theorem vertex_integral (L k : ℕ) (x : FullSpace.Vertex L k k) :
    ∃ n : Fin 4 → ℤ, (x : InfiniteLattice.AmbientSpace) = castVec n := by apply _root_.YangMills.Construction.Tower.FreeSymbolCoefficients.vertex_integral <;> assumption
def edgeClass (L k : ℕ) (a : Fin 3) (μ : Fin 4) : (colourEdges L k k).UnitQuot :=
  (colourEdges L k k).mkQuot 1 (a, posEdgeAt L k k 0 μ)
theorem exists_eq_edgeClass (hT : PeriodicOperators.TowerTranslations.Claim)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hk : 1 ≤ k)
    (c : (colourEdges L k k).UnitQuot) :
    ∃ a μ, c = edgeClass L k a μ := by apply _root_.YangMills.Construction.Tower.FreeSymbolCoefficients.exists_unitEdgeClass <;> assumption
theorem pauliCoeff_topEdgeComponent (z : (colourEdges L k k).UnitQuot → ℂ) (a : Fin 3)
    (μ : Fin 4) :
    pauliCoeff a (topEdgeComponent L k z μ) = z (edgeClass L k a μ) := by apply _root_.YangMills.Construction.Tower.FreeSymbolCoefficients.pauliCoeff_topEdgeComponent <;> assumption
theorem norm_apply_le_pauliFamilyNorm (hT : PeriodicOperators.TowerTranslations.Claim)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hk : 1 ≤ k)
    (z : (colourEdges L k k).UnitQuot → ℂ) (c : (colourEdges L k k).UnitQuot) :
    ‖z c‖ ≤ pauliFamilyNorm (topEdgeComponent L k z) := by
  obtain ⟨a, μ, rfl⟩ := exists_eq_edgeClass hT hL hk c
  rw [← pauliCoeff_topEdgeComponent z]
  exact (norm_pauliCoeff_le _ _).trans (pauliNorm_le_familyNorm _ μ)
theorem pauliCoeff_topEdgeComponent_constant (hT : PeriodicOperators.TowerTranslations.Claim)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hk : 1 ≤ k) (ε : Fin 4 → ComplexMatrix2)
    (a : Fin 3) (μ : Fin 4) :
    pauliCoeff a (topEdgeComponent L k (constantFormAmplitude L k ε) μ) = pauliCoeff a (ε μ) := by
  rw [pauliCoeff_topEdgeComponent]
  have hs : meshAt L k k ≠ 0 := by rw [meshAt_self]; exact one_ne_zero
  exact descendField_constantEdgeForm hT hL hk le_rfl hs ε a (posEdgeAt L k k 0 μ) μ
    (by simp [posEdgeAt, InfiniteLattice.Link.forwardFrom])
end Classes
section Bonds
variable {L k : ℕ}
theorem norm_integerWave (m : Fin 4 → ℤ) (x : InfiniteLattice.AmbientSpace) :
    ‖integerWave m x‖ = 1 := by apply _root_.YangMills.Construction.Tower.ResponseBoundProof.norm_integerWave <;> assumption
theorem integerWave_zero (x : InfiniteLattice.AmbientSpace) : integerWave 0 x = 1 := by
  simp [integerWave, bilinDot, toComplexVec, castVec]
theorem edgeFourierCoeff_mem (b : (colourEdges L k 0).UnitQuot → ℂ) (μ : Fin 4) (m : Fin 4 → ℤ) :
    edgeFourierCoeff L k b μ m ∈ ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.Tower.DiagonalSymbolBounds.edgeFourierCoeff_mem_traceless <;> assumption
theorem finestMesh_pos (hL : 0 < L) : 0 < finestMesh L k := by apply _root_.YangMills.Construction.Tower.FullSpace.ScaledMeansLocality.finestMesh_pos <;> assumption
theorem zero_mem_freqBox (hL : 0 < L) : (0 : Fin 4 → ℤ) ∈ freqBox L k := by apply _root_.YangMills.Construction.Tower.MassiveOpFunctions.MixedPartialOfMassiveLogFn.zero_mem_freqBox <;> assumption
theorem eq_edgeAt (β : PeriodicOperators.PosEdge L k 0) (μ : Fin 4)
    (hμ : β.1.terminal - β.1.initial = InfiniteLattice.axisStep (meshAt L k 0) μ) :
    β = edgeAt L k β.1.initial μ := by
  obtain ⟨⟨t, h, ad⟩, pos⟩ := β
  have e : h = t + InfiniteLattice.axisStep (meshAt L k 0) μ := by
    have hμ' : h - t = InfiniteLattice.axisStep (meshAt L k 0) μ := hμ
    rw [← hμ']
    abel
  subst e
  rfl
theorem norm_sub_pauliCoeff_le (hB : EdgeCoeffFacts L k) (hL : 0 < L)
    (b : (colourEdges L k 0).UnitQuot → ℂ) {t : ComplexMatrix2} (ht : t ∈ ComplexMatrix2.traceless)
    (μ : Fin 4) {x y : ℝ} (hy : 0 ≤ y) (h0 : pauliNorm (edgeFourierCoeff L k b μ 0 - t) ≤ x)
    (hm : ∀ m ∈ freqBox L k, m ≠ 0 → pauliNorm (edgeFourierCoeff L k b μ m) ≤ y) (a : Fin 3)
    (β : PeriodicOperators.PosEdge L k 0)
    (hμ : β.1.terminal - β.1.initial = InfiniteLattice.axisStep (meshAt L k 0) μ) :
    ‖b ((colourEdges L k 0).mkQuot 1 (a, β)) - pauliCoeff a t‖ ≤
      x + ((freqBox L k).card : ℝ) * y := by
  classical
  obtain ⟨s, rfl⟩ : ∃ s, β = edgeAt L k s μ := ⟨_, eq_edgeAt β μ hμ⟩
  have hV : pauliCoeff a (edgeFieldOfClasses L k b (edgeAt L k s μ)) =
      b ((colourEdges L k 0).mkQuot 1 (a, edgeAt L k s μ)) :=
    pauliCoeff_combination
      (fun a => b ((colourEdges L k 0).mkQuot 1 (a, edgeAt L k s μ))) a
  have hVmem : edgeFieldOfClasses L k b (edgeAt L k s μ) ∈ ComplexMatrix2.traceless :=
    ofPauliCoeffs_mem _ _
  rw [← hV, ← pauliCoeff_sub a hVmem ht]
  refine (norm_pauliCoeff_le _ _).trans ?_
  have hterm : ∀ m, integerWave m s • edgeFourierCoeff L k b μ m ∈ ComplexMatrix2.traceless :=
    fun m => Submodule.smul_mem _ _ (edgeFourierCoeff_mem b μ m)
  have e : edgeFieldOfClasses L k b (edgeAt L k s μ) - t =
      (edgeFourierCoeff L k b μ 0 - t) +
        ∑ m ∈ (freqBox L k).erase 0, integerWave m s • edgeFourierCoeff L k b μ m := by
    rw [hB.expansion b μ s, ← Finset.add_sum_erase _ _ (zero_mem_freqBox hL), integerWave_zero,
      one_smul]
    abel
  rw [e]
  refine (pauliNorm_add_le (Submodule.sub_mem _ (edgeFourierCoeff_mem b μ 0) ht)
    (Submodule.sum_mem _ fun m _ => hterm m)).trans (add_le_add h0 ?_)
  refine (pauliNorm_sum_le _ _ fun m => hterm m).trans ?_
  calc ∑ m ∈ (freqBox L k).erase 0, pauliNorm (integerWave m s • edgeFourierCoeff L k b μ m)
      ≤ ∑ _m ∈ (freqBox L k).erase 0, y := Finset.sum_le_sum fun m hm' => by
        rw [pauliNorm_smul _ (edgeFourierCoeff_mem b μ m), norm_integerWave, one_mul]
        exact hm m (Finset.mem_of_mem_erase hm') (Finset.ne_of_mem_erase hm')
    _ = (((freqBox L k).erase 0).card : ℝ) * y := by simp
    _ ≤ ((freqBox L k).card : ℝ) * y :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.card_erase_le) hy
end Bonds
theorem pos_of_mem_halfSupRate {δ₀ : ℝ} (h : δ₀ ∈ halfSupRate) : 0 < δ₀ := by apply _root_.YangMills.Construction.Tower.NormaliserSymbol.pos_of_mem_halfSupRate <;> assumption
theorem euclidNorm_nonneg (p : Fin 4 → ℂ) : 0 ≤ ResponseProperties.euclidNorm p :=
  Real.sqrt_nonneg _
theorem euclidNorm_le_one {p : Fin 4 → ℂ} (h : ‖p‖ < 1 / 2) :
    ResponseProperties.euclidNorm p ≤ 1 := by
  unfold ResponseProperties.euclidNorm
  refine Real.sqrt_le_iff.2 ⟨by norm_num, ?_⟩
  have hterm : ∀ ρ : Fin 4, ‖p ρ‖ ^ 2 ≤ 1 / 4 := fun ρ => by
    have h1 : ‖p ρ‖ ≤ 1 / 2 := (norm_le_pi_norm p ρ).trans h.le
    have h0 := norm_nonneg (p ρ)
    nlinarith
  calc ∑ ρ, ‖p ρ‖ ^ 2 ≤ ∑ _ρ : Fin 4, (1 / 4 : ℝ) := Finset.sum_le_sum fun ρ _ => hterm ρ
    _ = 1 ^ 2 := by simp
theorem componentsNearZero_atLevel (hT : PeriodicOperators.TowerTranslations.Claim) {δ₀ : ℝ}
    (hδ : 0 < δ₀) {L k : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L) (hk : 1 ≤ k)
    (hB₀ : IsPeriodic (colourEdges L k 0)) (hBk : IsPeriodic (colourEdges L k k))
    (hQ : TransposeKernelProps L k) (hB : EdgeCoeffFacts L k) {υ : ℝ}
    (hυ : 2 * δ₀ < υ)
    (hr : ResponseOperators.HasDecayRate (colourEdges L k k) (colourEdges L k 0)
      (responseKernel L k) υ)
    (hn : ResponseOperators.HasDecayRate (colourEdges L k k) (colourEdges L k k)
      (responseDefect L k) υ)
    (hbeh : SmallMomentumBehaviour δ₀ L k) (ε : Fin 4 → ComplexMatrix2)
    (hε : ResponseSymbolNearStrip.IsTracelessTuple ε) :
    ∃ C : ℝ, ∃ N ∈ nhds (0 : Fin 4 → ℂ), ∀ p ∈ N,
      (∀ c, ‖sourceResponseSymbol L k p ε c‖ ≤ C * ResponseProperties.euclidNorm p ^ 2) ∧
      (∀ c, ‖coarseResponseSymbol L k p ε c‖ ≤ C * ResponseProperties.euclidNorm p ^ 2) ∧
      ∀ c, ‖backgroundResponseSymbol L k p ε c -
          constantFormOnQuot L k (((finestMesh L k : ℝ) : ℂ) • ε) c‖ ≤
        C * ResponseProperties.euclidNorm p := by
  have hLpos : 0 < L := by
    have := hL.2
    omega
  have finK : Finite (colourEdges L k k).UnitQuot := hBk.finite_quot
  have fin0 : Finite (colourEdges L k 0).UnitQuot := hB₀.finite_quot
  let _ : Fintype (colourEdges L k k).UnitQuot := Fintype.ofFinite _
  let _ : Fintype (colourEdges L k 0).UnitQuot := Fintype.ofFinite _
  obtain ⟨C₀, N₀, hN₀, hbound⟩ := hbeh
  choose Mc hMc using hQ.bounded 1 one_pos
  obtain ⟨M, hM0, hM⟩ : ∃ M : ℝ, 0 ≤ M ∧ ∀ c', ∀ p ∈ imStrip 1,
      ∑ c, ‖linearMapEntry (symbolHom (colourEdges L k k) (colourEdges L k 0)
        (crossingSmoothingTransposeKernel L k) p) c' c‖ ≤ M := by
    refine ⟨∑ c', ∑ c, |Mc (c', c)|, Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
      abs_nonneg _, fun c' p hp => ?_⟩
    calc ∑ c, ‖linearMapEntry (symbolHom (colourEdges L k k) (colourEdges L k 0)
          (crossingSmoothingTransposeKernel L k) p) c' c‖
        ≤ ∑ c, |Mc (c', c)| :=
          Finset.sum_le_sum fun c _ => (hMc (c', c) p hp).trans (le_abs_self _)
      _ ≤ ∑ c'', ∑ c, |Mc (c'', c)| :=
          Finset.single_le_sum (f := fun c'' => ∑ c, |Mc (c'', c)|)
            (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ c')
  set a := constantFormAmplitude L k ε with ha
  set E := pauliFamilyNorm (topEdgeComponent L k a) with hE
  have hE0 : 0 ≤ E := pauliFamilyNorm_nonneg _
  set A := |C₀| * E with hA
  have hA0 : 0 ≤ A := mul_nonneg (abs_nonneg _) hE0
  have hη : 0 < finestMesh L k := finestMesh_pos hLpos
  set η := finestMesh L k with hηdef
  set card : ℝ := ((freqBox L k).card : ℝ) with hcard
  have hcard0 : 0 ≤ card := Nat.cast_nonneg _
  set r₀ := min (2 * δ₀) (1 / 2) with hr₀
  have hr₀pos : 0 < r₀ := lt_min (by linarith) (by norm_num)
  refine ⟨A + M * A + η * (A * (1 + card)), N₀ ∩ Metric.ball 0 r₀,
    inter_mem hN₀ (Metric.ball_mem_nhds _ hr₀pos), ?_⟩
  rintro p ⟨hpN, hpb⟩
  have hnorm : ‖p‖ < r₀ := by simpa using hpb
  have hco : ∀ ρ, ‖p ρ‖ < r₀ := fun ρ => (norm_le_pi_norm p ρ).trans_lt hnorm
  have him : ∀ ρ, |(p ρ).im| < r₀ := fun ρ => (Complex.abs_im_le_norm _).trans_lt (hco ρ)
  have hr₀δ : r₀ ≤ 2 * δ₀ := min_le_left _ _
  have hr₀h : r₀ ≤ 1 / 2 := min_le_right _ _
  have hpS : InFundamentalStrip δ₀ p :=
    ⟨fun ρ => (him ρ).le.trans hr₀δ, fun ρ =>
      ((Complex.abs_re_le_norm _).trans (hco ρ).le).trans
        (hr₀h.trans (by linarith [Real.pi_gt_three]))⟩
  have hpυ : p ∈ openImStrip υ := fun ρ => (him ρ).trans_le (hr₀δ.trans hυ.le)
  have hp1 : p ∈ imStrip 1 := fun ρ => (him ρ).le.trans (hr₀h.trans (by norm_num))
  set r := ResponseProperties.euclidNorm p with hrdef
  have hr0 : 0 ≤ r := euclidNorm_nonneg p
  have hr1 : r ≤ 1 := euclidNorm_le_one (hnorm.trans_le hr₀h)
  obtain ⟨hm, h0, hres⟩ := hbound p hpN hpS a
  have habs : ∀ x : ℝ, 0 ≤ x → C₀ * (x * E) ≤ A * x := fun x hx => by
    have := mul_le_mul_of_nonneg_right (le_abs_self C₀) (mul_nonneg hx hE0)
    calc C₀ * (x * E) ≤ |C₀| * (x * E) := this
      _ = A * x := by rw [hA]; ring
  have hr2 : 0 ≤ r ^ 2 := sq_nonneg r
  have hnval : ∀ c, ‖defectSymbol L k p a c‖ ≤ A * r ^ 2 := fun c =>
    ((norm_apply_le_pauliFamilyNorm hT hL hk _ c).trans hres).trans (habs _ hr2)
  have hAr2 : 0 ≤ A * r ^ 2 := mul_nonneg hA0 hr2
  have hMA : 0 ≤ M * A := mul_nonneg hM0 hA0
  have hηA : 0 ≤ η * (A * (1 + card)) :=
    mul_nonneg hη.le (mul_nonneg hA0 (by linarith))
  refine ⟨fun c => ?_, fun c => ?_, fun c => ?_⟩
  · rw [sourceResponseSymbol_eq hQ hn hpυ ε, linearMap_apply_eq_sum]
    calc ‖∑ c₁, linearMapEntry (symbolHom (colourEdges L k k) (colourEdges L k 0)
            (crossingSmoothingTransposeKernel L k) p) c c₁ * defectSymbol L k p a c₁‖
        ≤ ∑ c₁, ‖linearMapEntry (symbolHom (colourEdges L k k) (colourEdges L k 0)
            (crossingSmoothingTransposeKernel L k) p) c c₁‖ * (A * r ^ 2) :=
          (norm_sum_le _ _).trans (Finset.sum_le_sum fun c₁ _ => by
            rw [norm_mul]
            exact mul_le_mul_of_nonneg_left (hnval c₁) (norm_nonneg _))
      _ = (∑ c₁, ‖linearMapEntry (symbolHom (colourEdges L k k) (colourEdges L k 0)
            (crossingSmoothingTransposeKernel L k) p) c c₁‖) * (A * r ^ 2) := by
          rw [Finset.sum_mul]
      _ ≤ M * (A * r ^ 2) := mul_le_mul_of_nonneg_right (hM c p hp1) hAr2
      _ ≤ (A + M * A + η * (A * (1 + card))) * r ^ 2 := by
          have : 0 ≤ (A + η * (A * (1 + card))) * r ^ 2 := mul_nonneg (by linarith) hr2
          nlinarith
  · rw [coarseResponseSymbol_eq hn hpυ ε]
    refine (hnval c).trans ?_
    exact mul_le_mul_of_nonneg_right (by linarith) hr2
  · rw [backgroundResponseSymbol_eq hr hpυ ε]
    induction c using Quot.ind with
    | mk ι =>
      obtain ⟨a', β⟩ := ι
      obtain ⟨μ, hμ⟩ := β.2
      have hs : meshAt L k 0 ≠ 0 := hη.ne'
      have hg : constantFormOnQuot L k (((η : ℝ) : ℂ) • ε)
            ((colourEdges L k 0).mkQuot 1 (a', β)) =
          ((η : ℝ) : ℂ) * pauliCoeff a' (topEdgeComponent L k a μ) := by
        have e := descendField_constantEdgeForm hT hL hk (Nat.zero_le k) hs
          (((η : ℝ) : ℂ) • ε) a' β μ hμ
        refine e.trans ?_
        rw [Pi.smul_apply, pauliCoeff_smul a' _ (hε μ), ha,
          pauliCoeff_topEdgeComponent_constant hT hL hk]
      have hx : pauliNorm (edgeFourierCoeff L k (responseSymbolForm L k p a) μ 0 -
          topEdgeComponent L k a μ) ≤ A * r :=
        ((pauliNorm_le_familyNorm
          (fun μ => edgeFourierCoeff L k (responseSymbolForm L k p a) μ 0 -
            topEdgeComponent L k a μ) μ).trans h0).trans (habs _ hr0)
      have hy : ∀ m ∈ freqBox L k, m ≠ 0 →
          pauliNorm (edgeFourierCoeff L k (responseSymbolForm L k p a) μ m) ≤ A * r ^ 2 :=
        fun m hmem hne =>
          ((pauliNorm_le_familyNorm
            (fun μ => edgeFourierCoeff L k (responseSymbolForm L k p a) μ m) μ).trans
            (hm m hmem hne)).trans (habs _ hr2)
      have hv := norm_sub_pauliCoeff_le hB hLpos (responseSymbolForm L k p a)
        (ofPauliCoeffs_mem _ _ : topEdgeComponent L k a μ ∈ ComplexMatrix2.traceless) μ hAr2 hx hy
        a' β hμ
      show ‖((η : ℝ) : ℂ) * responseSymbolForm L k p a ((colourEdges L k 0).mkQuot 1 (a', β)) -
          constantFormOnQuot L k (((η : ℝ) : ℂ) • ε)
            ((colourEdges L k 0).mkQuot 1 (a', β))‖ ≤ _
      rw [hg, ← mul_sub, norm_mul, Complex.norm_real, Real.norm_of_nonneg hη.le]
      have h3 : A * r + card * (A * r ^ 2) ≤ A * (1 + card) * r := by
        have h4 : r ^ 2 ≤ r := by nlinarith
        have : card * (A * r ^ 2) ≤ card * (A * r) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h4 hA0) hcard0
        nlinarith
      calc η * ‖responseSymbolForm L k p a ((colourEdges L k 0).mkQuot 1 (a', β)) -
              pauliCoeff a' (topEdgeComponent L k a μ)‖
          ≤ η * (A * (1 + card) * r) := mul_le_mul_of_nonneg_left (hv.trans h3) hη.le
        _ = η * (A * (1 + card)) * r := by ring
        _ ≤ (A + M * A + η * (A * (1 + card))) * r :=
            mul_le_mul_of_nonneg_right (by linarith) hr0
theorem componentsNearZero_holds (hResp : ResponseOperators.Claim)
    (hCom : FullSpace.JointWidthAndTransposeTheorem)
    (hProp : ResponseProperties.AllProperties) (hWav : PlaneWaveCalculus.PlaneWaveCalculusHolds)
    (hIdx : PeriodicOperators.TowerIndexSets.Claim)
    (hT : PeriodicOperators.TowerTranslations.Claim) :
    ComponentsNearZero := by
  intro δ₀ hδ L hL k hk ε hε
  obtain ⟨δ₁, hδ₁, hA⟩ := hResp
  have A : ResponseOperators.AtLevel δ₀ L k := (Part.mem_unique hδ₁ hδ) ▸ hA L hL k hk
  obtain ⟨υ, hυ, -, hr, hn⟩ := A.exists_rate
  have hLpos : 0 < L := by
    have := hL.2
    omega
  exact componentsNearZero_atLevel hT (pos_of_mem_halfSupRate hδ) hL hk
    (hIdx L hL k 0 (Nat.zero_le k)).2.1 (hIdx L hL k k le_rfl).2.1 (hCom L hLpos hL k hk).2.2.1
    (hWav L hL k hk).2.2.1 hυ hr hn (hProp.2.2.2 δ₀ hδ L hL k hk) ε hε
end YangMills.Construction.Tower.ResponseSymbolNearZero
end
