import YangMills.Construction.PeriodicOperators.EntriesDeterminantsAndHolomorphicFunctionsProof
import YangMills.Construction.Towers.ComponentsOfTheJetAlongHolomorphicAmplitudesProof
import YangMills.Construction.Towers.SumsProductsAndTransposesOfJetsWithHolomorphicComponentsProof
import YangMills.Construction.PeriodicOperators.JetOfAProductOfLocalOperatorFunctionsProof
import YangMills.Construction.PeriodicOperators.ProductOfLocalOperatorFunctionsProof
import YangMills.Construction.Towers.ExistenceOfTheBoundOfTheResponseProof
import YangMills.Construction.Towers.PropertiesOfTheBackgrounds
import YangMills.Construction.Towers.PropertiesOfTheResponse
import YangMills.Construction.Towers.TheResponseOperators
import Mathlib
set_option autoImplicit false
open Set Filter Topology
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.BackgroundProperties
open Coordinates Matrices
open PeriodicOperators
open BackgroundFieldResponse (responseKernel)
open BackgroundJets
open PeriodicOperators.JetDomains (fstMomentum sndMomentum)
section Holomorphic
variable {N : ℕ}
theorem isHolomorphicIn_one_iff (O : Set (ComplexCoordinates N)) (u : ComplexCoordinates N → ℂ) :
    ComplexCoordinates.IsHolomorphicIn (N' := 1) O (fun z _ => u z) ↔
      IsOpen O ∧ ContinuousOn u O ∧ ∀ a ∈ O, ∀ j : Fin N, ∀ᶠ ζ in 𝓝 (0 : ℂ),
        DifferentiableAt ℂ (fun ζ : ℂ => u (a + ζ • ComplexCoordinates.stdBasisVector j)) ζ := by apply _root_.YangMills.Construction.PeriodicOperators.OpFunComp.isHolomorphicIn_scalar_iff <;> assumption
theorem isHolomorphicIn_one_mono {O O' : Set (ComplexCoordinates N)} {u : ComplexCoordinates N → ℂ}
    (h : ComplexCoordinates.IsHolomorphicIn (N' := 1) O fun z _ => u z) (hs : O' ⊆ O)
    (ho : IsOpen O') : ComplexCoordinates.IsHolomorphicIn (N' := 1) O' fun z _ => u z := by
  obtain ⟨_, hc, hd⟩ := (isHolomorphicIn_one_iff O u).1 h
  exact (isHolomorphicIn_one_iff O' u).2 ⟨ho, hc.mono hs, fun a ha => hd a (hs ha)⟩
theorem isHolomorphicIn_one_congr {O : Set (ComplexCoordinates N)} {u v : ComplexCoordinates N → ℂ}
    (h : ComplexCoordinates.IsHolomorphicIn (N' := 1) O fun z _ => u z) (e : EqOn v u O) :
    ComplexCoordinates.IsHolomorphicIn (N' := 1) O fun z _ => v z := by
  obtain ⟨ho, hc, hd⟩ := (isHolomorphicIn_one_iff O u).1 h
  refine (isHolomorphicIn_one_iff O v).2 ⟨ho, hc.congr e, fun a ha j => ?_⟩
  have hline : Continuous fun ζ : ℂ => a + ζ • ComplexCoordinates.stdBasisVector j := by fun_prop
  have hnear : ∀ᶠ ζ in 𝓝 (0 : ℂ), a + ζ • ComplexCoordinates.stdBasisVector j ∈ O := by
    refine hline.continuousAt.eventually_mem (ho.mem_nhds ?_)
    simpa using ha
  filter_upwards [hd a ha j, hnear.eventually_nhds] with ζ h₁ h₂
  exact h₁.congr_of_eventuallyEq (h₂.mono fun ζ' hz => e hz)
theorem isHolomorphicIn_one_const_mul {O : Set (ComplexCoordinates N)} {u : ComplexCoordinates N → ℂ}
    (c : ℂ) (h : ComplexCoordinates.IsHolomorphicIn (N' := 1) O fun z _ => u z) :
    ComplexCoordinates.IsHolomorphicIn (N' := 1) O fun z _ => c * u z := by apply _root_.YangMills.Construction.Tower.FullSpace.JetClosure.ScalarHolomorphic.const_mul <;> assumption
theorem isHolomorphicIn_one_mul {O : Set (ComplexCoordinates N)} {u v : ComplexCoordinates N → ℂ}
    (h : ComplexCoordinates.IsHolomorphicIn (N' := 1) O fun z _ => u z)
    (h' : ComplexCoordinates.IsHolomorphicIn (N' := 1) O fun z _ => v z) :
    ComplexCoordinates.IsHolomorphicIn (N' := 1) O fun z _ => u z * v z := by apply _root_.YangMills.Construction.PeriodicOperators.EntriesDets.HolomorphicFnOn.mul <;> assumption
theorem isHolomorphicIn_one_sum {J : Type} (s : Finset J) {O : Set (ComplexCoordinates N)}
    (ho : IsOpen O) {u : J → ComplexCoordinates N → ℂ}
    (h : ∀ i ∈ s, ComplexCoordinates.IsHolomorphicIn (N' := 1) O fun z _ => u i z) :
    ComplexCoordinates.IsHolomorphicIn (N' := 1) O fun z _ => ∑ i ∈ s, u i z := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    refine (isHolomorphicIn_one_iff O _).2 ⟨ho, continuousOn_const, fun a _ j => ?_⟩
    exact Eventually.of_forall fun ζ => differentiableAt_const _
  | insert i s hi ih =>
    have h₁ := (isHolomorphicIn_one_iff O _).1 (h i (Finset.mem_insert_self i s))
    have h₂ := (isHolomorphicIn_one_iff O _).1 (ih fun i' hi' => h i' (Finset.mem_insert_of_mem hi'))
    simp only [Finset.sum_insert hi]
    refine (isHolomorphicIn_one_iff O _).2 ⟨ho, h₁.2.1.add h₂.2.1, fun a ha j => ?_⟩
    filter_upwards [h₁.2.2 a ha j, h₂.2.2 a ha j] with ζ d₁ d₂
    exact d₁.add d₂
theorem isHolomorphicIn_one_comp_neg {O : Set (ComplexCoordinates N)} {u : ComplexCoordinates N → ℂ}
    (h : ComplexCoordinates.IsHolomorphicIn (N' := 1) O fun z _ => u z)
    (hneg : ∀ z ∈ O, -z ∈ O) :
    ComplexCoordinates.IsHolomorphicIn (N' := 1) O fun z _ => u (-z) := by
  obtain ⟨ho, hc, hd⟩ := (isHolomorphicIn_one_iff O u).1 h
  refine (isHolomorphicIn_one_iff O _).2 ⟨ho, hc.comp continuous_neg.continuousOn hneg, fun a ha j => ?_⟩
  have hneg0 : Tendsto (fun ζ : ℂ => -ζ) (𝓝 0) (𝓝 0) := by
    simpa using (continuous_neg (G := ℂ)).tendsto 0
  filter_upwards [hneg0.eventually (hd (-a) (hneg a ha) j)] with ζ h₁
  have e : (fun ζ : ℂ => u (-(a + ζ • ComplexCoordinates.stdBasisVector j))) =
      (fun ζ : ℂ => u (-a + ζ • ComplexCoordinates.stdBasisVector j)) ∘ fun ζ => -ζ := by
    funext ζ'
    simp only [Function.comp, neg_smul, neg_add]
  rw [e]
  exact DifferentiableAt.comp ζ h₁ differentiableAt_id.neg
end Holomorphic
theorem blochWave_injective (I : PeriodicData) (κ : Fin 4 → ℂ) {φ φ' : I.UnitQuot → ℂ}
    (h : blochWave I κ φ = blochWave I κ φ') : φ = φ' := by apply _root_.YangMills.SharedProofs.p12280 <;> assumption
theorem waveAmplitude_blochWave (I : PeriodicData) (κ : Fin 4 → ℂ) (φ : I.UnitQuot → ℂ) :
    waveAmplitude I κ (blochWave I κ φ) = φ :=
  blochWave_injective I κ
    (Classical.epsilon_spec (p := fun φ' => blochWave I κ φ' = blochWave I κ φ) ⟨φ, rfl⟩)
theorem symbolHom_apply (I I' : PeriodicData) [Finite I.UnitQuot] (T : I'.Carrier → I.Carrier → ℂ)
    (κ : Fin 4 → ℂ) (φ : I.UnitQuot → ℂ) :
    symbolHom I I' T κ φ = applyKernel (quotSymbol I I' T κ) φ :=
  linearMapOfEntries_eq_applyKernel _ _
theorem linearMap_apply_eq_sum_entry {J J' : Type} [Fintype J] (M : (J → ℂ) →ₗ[ℂ] (J' → ℂ))
    (f : J → ℂ) (c' : J') :
    M f c' = ∑ c, linearMapEntry M c' c * f c := by apply _root_.YangMills.Construction.PeriodicOperators.HomNorm.apply_eq_sum_linearMapEntry <;> assumption
theorem pauliFamily_mem_traceless (a : Fin 3) : ComplexMatrix2.pauliFamily a ∈ ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.OneLoopLaw.PlaneWaveSymmetries.pauliFamily_mem_traceless <;> assumption
theorem pauliCoeff_sum_smul_pauliFamily (x : Fin 3 → ℂ) (a : Fin 3) :
    pauliCoeff a (∑ b, x b • ComplexMatrix2.pauliFamily b) = x a := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.pauliCoeff_sum_smul <;> assumption
theorem sum_pauliCoeff_smul_pauliFamily {X : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.traceless) :
    ∑ a, pauliCoeff a X • ComplexMatrix2.pauliFamily a = X := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.sum_pauliCoeff_smul <;> assumption
theorem stripHalfWidth_spec (hN : FreeStrip.ConstantsAdmissible.ConstantsAreAdmissible) :
    stripHalfWidth ∈ FreeStrip.halfSupRate ∧ 0 < stripHalfWidth ∧ stripHalfWidth ≤ 1 / 64 := by
  obtain ⟨_, _, δ₀, hδ, C₀, _, hI, _, _⟩ := hN
  have e : stripHalfWidth = δ₀ :=
    Part.mem_unique (stripHalfWidth_mem (Part.dom_iff_mem.2 ⟨_, hδ⟩)) hδ
  rw [e]
  exact ⟨hδ, hI.1, hI.2⟩
theorem responseAtLevel (hN : FreeStrip.ConstantsAdmissible.ConstantsAreAdmissible)
    (hR : ResponseOperators.Claim) {L k : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hk : 1 ≤ k) : ResponseOperators.AtLevel stripHalfWidth L k := by
  obtain ⟨δ₀, hδ, h⟩ := hR
  have e : stripHalfWidth = δ₀ := Part.mem_unique (stripHalfWidth_spec hN).1 hδ
  rw [e]
  exact h L hL k hk
theorem responseAmplitude_eq_responseOnAxis {L k : ℕ} (hfin : Finite (colourEdges L k k).UnitQuot)
    {υ : ℝ}
    (hr : ResponseOperators.HasDecayRate (colourEdges L k k) (colourEdges L k 0) (responseKernel L k) υ)
    {q : Fin 4 → ℂ} (hq : q ∈ openImStrip υ) (μ : Fin 4) :
    responseAmplitude L k q μ = responseOnAxis L k q μ := by
  have e : applyKernel (responseKernel L k) (planeWaveOfConstant L k q (axisPauliElement μ 2)) =
      blochWave (colourEdges L k 0) q (responseOnAxis L k q μ) := by
    funext ι'
    refine (hr.applyKernel_blochWave q hq _ ι').2.trans ?_
    rw [responseOnAxis, symbolHom_apply]
  rw [responseAmplitude, e, waveAmplitude_blochWave]
theorem scaledEdgeCoboundary_symbol_spec (hFO : FreeOperators.FreeOperatorsArePeriodic)
    (hS : SymbolCalculus.Claim) (hSym : Symbols.Claim) (hId : IdKernelFacts.Claim)
    {L k : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L) (hk : 1 ≤ k)
    (hB : IsPeriodic (colourEdges L k 0)) (hP : IsPeriodic (colourFaces L k 0)) :
    IsPeriodicKernel (colourEdges L k 0) (colourFaces L k 0) (scaledEdgeCoboundaryKernel L k 0) ∧
      FourierSymbolIsEntire (colourEdges L k 0) (colourFaces L k 0)
        (scaledEdgeCoboundaryKernel L k 0) ∧
      ∀ (q : Fin 4 → ℂ) (b : (colourEdges L k 0).UnitQuot → ℂ),
        (edgePauliCoordinates L k 0).mapOnCoeffs (vertexCoordinate (Face L k 0))
            scaledEdgeCoboundary (blochWave (colourEdges L k 0) q b) =
          blochWave (colourFaces L k 0) q (edgeCoboundarySymbol L k q b) := by
  have hk3 := (hFO.2 L hL k hk).1.edgeCoboundary 0 (Nat.zero_le k)
  obtain ⟨hper, hfin, hrate⟩ := hk3.finite_range
  have hent := (hS _ _ hB hP).1 _ hper hfin
  refine ⟨hper, hent, fun q b => ?_⟩
  have hI := hId _ hB
  have facts := hSym.1 _ _ _ hB hP hB _ (idKernel _) 1 hper (hrate 1 one_pos) hI.1
    (hI.2.1 1 one_pos)
  have : Finite (colourEdges L k 0).UnitQuot := hB.finite_quot
  rw [← hk3.applyKernel_eq]
  funext ι'
  rw [(facts.applyKernel_blochWave q (hent.1 q (mem_univ q)) b ι').2]
  exact congrArg (fun φ => blochWave (colourFaces L k 0) q φ ι')
    (symbolHom_apply (colourEdges L k 0) (colourFaces L k 0)
      (scaledEdgeCoboundaryKernel L k 0) q b).symm
theorem isHolomorphicIn_linearMapEntry_of_entire (hQ : StripSymbols.Claim) {I I' : PeriodicData}
    (hI : IsPeriodic I) (hI' : IsPeriodic I') {T : I'.Carrier → I.Carrier → ℂ}
    (hper : IsPeriodicKernel I I' T) (hent : FourierSymbolIsEntire I I' T) (c' : I'.UnitQuot)
    (c : I.UnitQuot) :
    ComplexCoordinates.IsHolomorphicIn (N := 4) (N' := 1) univ fun κ _ =>
      linearMapEntry (symbolHom I I' T κ) c' c := by
  induction c' using Quot.ind with
  | mk ι' =>
    induction c using Quot.ind with
    | mk ι =>
      refine isHolomorphicIn_one_congr (hent.2 ι' ι).2 fun κ _ => ?_
      exact ((hQ.2.1 I I' hI hI').2.1 T κ hper (hent.1 κ (mem_univ κ))).carrierEntry_symbolHom ι' ι
theorem modulatedForm_edgeFormOf (L k : ℕ) (q : Fin 4 → ℂ) (b : (colourEdges L k 0).UnitQuot → ℂ) :
    ResponseProperties.modulatedForm L k q (edgeFormOf L k b) =
      (edgePauliCoordinates L k 0).ofCoeffs (blochWave (colourEdges L k 0) q b) := by apply _root_.YangMills.Construction.Tower.ResponseBoundProof.modulatedForm_eq <;> assumption
open Classical in
theorem ofCoeffs_mem_traceless (L k : ℕ) (c : (edgePauliCoordinates L k 0).Index → ℂ)
    (β : Edge L k 0) : (edgePauliCoordinates L k 0).ofCoeffs c β ∈ ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.Tower.ResponseBoundProof.ofCoeffs_mem_traceless <;> assumption
theorem isCoboundaryFactor_of_mapOnCoeffs (L k : ℕ) (q : Fin 4 → ℂ)
    (b : (colourEdges L k 0).UnitQuot → ℂ) (F : (colourFaces L k 0).UnitQuot → ℂ)
    (hmap : (edgePauliCoordinates L k 0).mapOnCoeffs (vertexCoordinate (Face L k 0))
        scaledEdgeCoboundary (blochWave (colourEdges L k 0) q b) =
      blochWave (colourFaces L k 0) q F) :
    ResponseProperties.IsCoboundaryFactor L k q (edgeFormOf L k b) (faceFunctionOf L k F) := by
  intro P
  rw [modulatedForm_edgeFormOf]
  have hW := ofCoeffs_mem_traceless L k (blochWave (colourEdges L k 0) q b)
  set W := (edgePauliCoordinates L k 0).ofCoeffs (blochWave (colourEdges L k 0) q b) with hWdef
  have hmem : scaledEdgeCoboundary (L := L) (k := k) (j := 0) W P ∈ ComplexMatrix2.traceless := by
    have h₁ : edgeCoboundary W P ∈ ComplexMatrix2.traceless :=
      Submodule.sub_mem _ (Submodule.sub_mem _ (Submodule.add_mem _ (hW _) (hW _)) (hW _)) (hW _)
    have ht : Matrix.trace (edgeCoboundary W P) = 0 := h₁
    show Matrix.trace ((meshAt L k 0)⁻¹ • edgeCoboundary W P) = 0
    rw [Matrix.trace_smul, ht, smul_zero]
  have hc : ∀ a, pauliCoeff a (scaledEdgeCoboundary (L := L) (k := k) (j := 0) W P) =
      blochWave (colourFaces L k 0) q F (a, P) := fun a => congrFun hmap (a, P)
  calc scaledEdgeCoboundary (L := L) (k := k) (j := 0) W P
      = ∑ a, pauliCoeff a (scaledEdgeCoboundary (L := L) (k := k) (j := 0) W P) •
          ComplexMatrix2.pauliFamily a := (sum_pauliCoeff_smul_pauliFamily hmem).symm
    _ = ∑ a, blochWave (colourFaces L k 0) q F (a, P) • ComplexMatrix2.pauliFamily a := by
      simp only [hc]
    _ = PlaneWaveCalculus.expWave q P.corner • faceFunctionOf L k F P := by
      simp only [faceFunctionOf, ofPauliCoeffs, Finset.smul_sum, smul_smul]
      rfl
theorem axisStep_injective {a : ℝ} (ha : a ≠ 0) {μ ρ : Fin 4}
    (h : InfiniteLattice.axisStep a μ = InfiniteLattice.axisStep a ρ) : μ = ρ := by apply _root_.YangMills.Construction.Tower.FacesContainingEdge.axisStep_injective <;> assumption
theorem constantEdgeForm_eq {L k : ℕ} (hs : meshAt L k k ≠ 0) (ε : Fin 4 → ComplexMatrix2)
    (β : Edge L k k) (μ : Fin 4)
    (hβ : β.terminal - β.initial = InfiniteLattice.axisStep (meshAt L k k) μ) :
    constantEdgeForm L k ε β = ε μ := by
  have pos : β.IsPositivelyOriented := ⟨μ, hβ⟩
  simp only [constantEdgeForm, extendOddly, if_pos pos, hβ]
  rw [Finset.sum_eq_single μ]
  · simp
  · intro ρ _ hρ
    rw [if_neg fun e => hρ (axisStep_injective hs e).symm]
  · simp
theorem isQuotInvariant_coeffs_constantEdgeForm (hT : TowerTranslations.Claim) {L k : ℕ}
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hk : 1 ≤ k) (hs : meshAt L k k ≠ 0)
    (ε : Fin 4 → ComplexMatrix2) :
    IsQuotInvariant (colourEdges L k k) ((edgePauliCoordinates L k k).coeffs (constantEdgeForm L k ε)) := by
  have hstep : ∀ ι ι' : (colourEdges L k k).Carrier,
      (∃ n : Fin 4 → ℤ, ι' = (colourEdges L k k).translate (1 • n) ι) →
        (edgePauliCoordinates L k k).coeffs (constantEdgeForm L k ε) ι =
          (edgePauliCoordinates L k k).coeffs (constantEdgeForm L k ε) ι' := by
    rintro ⟨a, b⟩ _ ⟨n, rfl⟩
    obtain ⟨μ, hμ⟩ := b.2
    rw [(hT L hL k k hk le_rfl (1 • n)).2.2.2.1 a b μ hμ]
    show pauliCoeff a (constantEdgeForm L k ε b.1) =
      pauliCoeff a (constantEdgeForm L k ε (InfiniteLattice.Link.forwardFrom _ μ))
    rw [constantEdgeForm_eq hs ε b.1 μ hμ,
      constantEdgeForm_eq hs ε _ μ (by simp [InfiniteLattice.Link.forwardFrom])]
  intro ι ι' e
  exact congrArg (Quot.lift _ hstep) e
theorem topEdgeComponent_constantFormAmplitude (hT : TowerTranslations.Claim)
    {L k : ℕ} (hL : Conventions.IsAdmissibleBlockingFactor L) (hk : 1 ≤ k) (hs : meshAt L k k ≠ 0)
    (ε : Fin 4 → ComplexMatrix2) (hε : ∀ μ, ε μ ∈ ComplexMatrix2.traceless) (μ : Fin 4) :
    PlaneWaveCalculus.topEdgeComponent L k (constantFormAmplitude L k ε) μ = ε μ := by
  refine Eq.trans (?_ : _ = ∑ a, pauliCoeff a (ε μ) • ComplexMatrix2.pauliFamily a)
    (sum_pauliCoeff_smul_pauliFamily (hε μ))
  show ∑ a, constantFormAmplitude L k ε ((colourEdges L k k).mkQuot 1
    (a, PlaneWaveCalculus.posEdgeAt L k k 0 μ)) • ComplexMatrix2.pauliFamily a = _
  refine Finset.sum_congr rfl fun a _ => ?_
  congr 1
  have e := descendFn_mkQuot (isQuotInvariant_coeffs_constantEdgeForm hT hL hk hs ε)
    (a, PlaneWaveCalculus.posEdgeAt L k k 0 μ)
  refine e.trans ?_
  show pauliCoeff a (constantEdgeForm L k ε (InfiniteLattice.Link.forwardFrom 0 μ)) = _
  rw [constantEdgeForm_eq hs ε _ μ (by simp [InfiniteLattice.Link.forwardFrom])]
theorem pauliNorm_zero : pauliNorm (0 : ComplexMatrix2) = 0 := by
  have e : ∀ a, pauliCoeff a (0 : ComplexMatrix2) = 0 := fun a => by
    simpa using pauliCoeff_sum_smul_pauliFamily (fun _ => 0) a
  simp [pauliNorm, e]
theorem pauliNorm_pauliFamily_two : pauliNorm (ComplexMatrix2.pauliFamily 2) = 1 := by
  have e : ∀ a, pauliCoeff a (ComplexMatrix2.pauliFamily 2) = (Pi.single 2 1 : Fin 3 → ℂ) a :=
    fun a => by
      have h := pauliCoeff_sum_smul_pauliFamily (Pi.single 2 1) a
      simpa [Pi.single_apply] using h
  simp [pauliNorm, e, Fin.sum_univ_three]
theorem pauliFamilyNorm_axisPauliElement (hT : TowerTranslations.Claim) {L k : ℕ}
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hk : 1 ≤ k) (hs : meshAt L k k ≠ 0)
    (μ : Fin 4) :
    pauliFamilyNorm (PlaneWaveCalculus.topEdgeComponent L k
      (constantFormAmplitude L k (axisPauliElement μ 2))) = 1 := by
  have hε : ∀ ρ, axisPauliElement μ 2 ρ ∈ ComplexMatrix2.traceless := fun ρ => by
    by_cases h : ρ = μ
    · subst h
      simpa [axisPauliElement] using pauliFamily_mem_traceless 2
    · simp [axisPauliElement, Pi.single_eq_of_ne h]
  have e : PlaneWaveCalculus.topEdgeComponent L k
      (constantFormAmplitude L k (axisPauliElement μ 2)) = axisPauliElement μ 2 :=
    funext fun ρ => topEdgeComponent_constantFormAmplitude hT hL hk hs _ hε ρ
  rw [e, pauliFamilyNorm, Finset.sum_eq_single μ]
  · simp [axisPauliElement, pauliNorm_pauliFamily_two]
  · intro ρ _ hρ
    simp [axisPauliElement, Pi.single_eq_of_ne hρ, pauliNorm_zero]
  · simp
theorem pointProperties_of (hN : FreeStrip.ConstantsAdmissible.ConstantsAreAdmissible)
    (hP : ResponseProperties.AllProperties) (hW : PlaneWaveCalculus.PlaneWaveCalculusHolds)
    (hT : TowerTranslations.Claim) {L k : ℕ}
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hk : 1 ≤ k) {q : Fin 4 → ℂ}
    (hq : q ∈ momentumPolydisc stripHalfWidth) (μ : Fin 4)
    (hamp : responseAmplitude L k q μ = responseOnAxis L k q μ)
    (hcurv : (edgePauliCoordinates L k 0).mapOnCoeffs (vertexCoordinate (Face L k 0))
        scaledEdgeCoboundary (blochWave (colourEdges L k 0) q (responseAmplitude L k q μ)) =
      blochWave (colourFaces L k 0) q (responseCurvature L k q μ)) :
    PointProperties L k q μ := by
  obtain ⟨hmem, hpos, hle⟩ := stripHalfWidth_spec hN
  have hs : meshAt L k k ≠ 0 := by simp [meshAt]
  have hpoint : ResponseProperties.InFundamentalStrip stripHalfWidth q := by
    refine ⟨fun ρ => ?_, fun ρ => ?_⟩
    · have := (Complex.abs_im_le_norm (q ρ)).trans (hq ρ)
      linarith
    · have h₁ := (Complex.abs_re_le_norm (q ρ)).trans (hq ρ)
      have h₂ := Real.pi_gt_three
      linarith
  have hform : ResponseProperties.IsFourierSynthesis L k
      (ResponseProperties.responseSymbolForm L k q (constantFormAmplitude L k (axisPauliElement μ 2)))
      (edgeFormOf L k (responseAmplitude L k q μ)) := by
    intro x ρ
    have e : ResponseProperties.responseSymbolForm L k q
        (constantFormAmplitude L k (axisPauliElement μ 2)) = responseAmplitude L k q μ := hamp.symm
    rw [e]
    exact (hW L hL k hk).2.2.1.expansion _ ρ x
  have hfac := isCoboundaryFactor_of_mapOnCoeffs L k q _ _ hcurv
  have key := fun (C : ℝ) (hC : ResponseProperties.ResponseBound C) =>
    hC stripHalfWidth hmem L hL k hk q hpoint _ _ _ hform hfac
  have hfin := key _ hP.2.2.1
  refine ⟨hamp, hfin.1, hfin.2.1, fun C hC => ?_⟩
  have h := (key C hC).2.2
  rw [pauliFamilyNorm_axisPauliElement hT hL hk hs μ, mul_one] at h
  have n₁ : 0 ≤ wNorm ((colourEdges L k 0).quotWeight 1)
      (ResponseProperties.responseSymbolForm L k q
        (constantFormAmplitude L k (axisPauliElement μ 2))) :=
    Real.sqrt_nonneg _
  have n₂ : 0 ≤ pauliFamilyNorm (PlaneWaveCalculus.topEdgeComponent L k
      (ResponseProperties.defectSymbol L k q
        (constantFormAmplitude L k (axisPauliElement μ 2)))) := Real.sqrt_nonneg _
  have n₃ : 0 ≤ pauliNorm (PlaneWaveCalculus.topVertexElement L k
      (ResponseProperties.smoothedDivergence L k q
        (constantFormAmplitude L k (axisPauliElement μ 2)))) := Real.sqrt_nonneg _
  linarith
theorem jetWidth_spec (hpos : 0 < stripHalfWidth) (p : Fin 4 → ℂ) :
    0 < jetWidth p ∧ p ∈ imStrip (jetWidth p) := by
  refine ⟨lt_of_lt_of_le hpos (le_max_left _ _), fun μ => ?_⟩
  fin_cases μ <;> simp [jetWidth]
theorem symbolSummableOn_coeffZero (hFO : FreeOperators.FreeOperatorsArePeriodic)
    (hS : SymbolCalculus.Claim) {F I I' : PeriodicData} (hI : IsPeriodic I) (hI' : IsPeriodic I')
    {T : (F.Carrier → ℂ) → I'.Carrier → I.Carrier → ℂ} (hT : IsLocalOpFun F I I' T) :
    SymbolSummableOn I I' (coeffZero F I I' T) univ := by
  obtain ⟨ρ, R, hm⟩ := hT
  have below : IsSupBelow F 0 ρ := ⟨0, hm.radius_pos, fun _ => by simp⟩
  have hcov : IsShiftInvariant I I' (coeffZero F I I' T) := fun n ι' ι =>
    hm.shift_covariant 0 below n ι' ι
  have hvan : VanishesOutsideRadius I I' (max R 0) (coeffZero F I I' T) := fun ι' ι h => by
    refine hm.vanish_far 0 below ι' ι fun h' => h ?_
    have e : TorusMetric.euclidNormVec (I'.pos ι' - I.pos ι) =
        TorusMetric.euclidNormVec (I.pos ι - I'.pos ι') := by
      simp only [TorusMetric.euclidNormVec, Pi.sub_apply]
      congr 1
      exact Finset.sum_congr rfl fun x _ => by ring
    rw [e]
    exact h'.trans (le_max_left _ _)
  obtain ⟨hper, hfin, _⟩ := (hFO.1 I I' hI hI').1 _ _ (le_max_right _ _) hcov hvan
  exact ((hS I I' hI hI').1 _ hper hfin).1
theorem jetWellDefined_of_local (hFO : FreeOperators.FreeOperatorsArePeriodic)
    (hS : SymbolCalculus.Claim) (hJ : JetDomains.OpFunJetTheory) (hpos : 0 < stripHalfWidth)
    {L k : ℕ} (hF : IsPeriodic (remainderIndex L k)) (μPlus μMinus : Fin 4) {I I' : PeriodicData}
    (hI : IsPeriodic I) (hI' : IsPeriodic I')
    {T : ((remainderIndex L k).Carrier → ℂ) → I'.Carrier → I.Carrier → ℂ}
    (hT : IsLocalOpFun (remainderIndex L k) I I' T) :
    JetWellDefined L k μPlus μMinus I I' T := by
  have facts := hJ.2.1 _ I I' hF hI hI' T hT
  refine ⟨symbolSummableOn_coeffZero hFO hS hI hI' hT, fun p _ => facts.triple_unique p _ _,
    fun p _ => ?_⟩
  exact facts.isJet _ (jetWidth_spec hpos p).1 p (jetWidth_spec hpos p).2 _ _
theorem appendSet_univ_prod (O : Set (Fin 4 → ℂ)) :
    appendSet (n := 4) (n' := 4) (univ ×ˢ O) = productOver O := by apply _root_.YangMills.Construction.Tower.FullSpace.JetAlongAmplitudes.appendSet_univ_prod <;> assumption
theorem isHolomorphicIn_entry_of_momentumPair {I I' : PeriodicData} {O : Set (Fin 4 → ℂ)}
    {A : ComplexCoordinates 4 → ComplexCoordinates 4 → QuotHom I I'}
    (h : ScaledOperatorFunctions.IsHolomorphicInMomentumPair (univ ×ˢ O) A) (c' : I'.UnitQuot)
    (c : I.UnitQuot) :
    ComplexCoordinates.IsHolomorphicIn (N := 4 + 4) (N' := 1) (productOver O) fun z _ =>
      linearMapEntry (A (sndMomentum z) (fstMomentum z)) c' c := by
  have e := h.2.2 (c', c)
  rw [appendSet_univ_prod] at e
  exact e
theorem componentsHolomorphicOn_of_local {L k : ℕ} {μPlus μMinus : Fin 4} {O : Set (Fin 4 → ℂ)}
    {I I' : PeriodicData}
    (hc : ScaledOperatorFunctions.JetComponentsHolomorphic L k I I')
    (hplus : HolomorphicOnEntrywise (n := 4) quotFnEntries O fun p => axisField L k p μPlus)
    (hminus : HolomorphicOnEntrywise (n := 4) quotFnEntries O fun p => axisField L k (-p) μMinus)
    {T : ((remainderIndex L k).Carrier → ℂ) → I'.Carrier → I.Carrier → ℂ}
    (hT : IsLocalOpFun (remainderIndex L k) I I' T) :
    ComponentsHolomorphicOn L k μPlus μMinus O I I' T := by
  obtain ⟨h00, h10, h01, h11⟩ := hc T hT O _ _ hplus hminus
  exact ⟨isHolomorphicIn_entry_of_momentumPair h00, isHolomorphicIn_entry_of_momentumPair h10,
    isHolomorphicIn_entry_of_momentumPair h01, isHolomorphicIn_entry_of_momentumPair h11⟩
theorem forAllEight_of (hO : ScaledOperatorFunctions.ScaledOperatorFunctionsClaim)
    (hA : IteratedSmallFieldMeans.IteratedMeansClaim) {L k : ℕ}
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hk : 1 ≤ k)
    {P : ∀ I I' : PeriodicData, (((remainderIndex L k).Carrier → ℂ) → I'.Carrier → I.Carrier → ℂ) → Prop}
    (h : ∀ (I I' : PeriodicData), IsPeriodic I → IsPeriodic I' →
      ∀ T : ((remainderIndex L k).Carrier → ℂ) → I'.Carrier → I.Carrier → ℂ,
        IsLocalOpFun (remainderIndex L k) I I' T → P I I' T) :
    ForAllEight L k P := by
  have ho := (hO.1 L hL k hk).1
  obtain ⟨pS, pB, pP, pSk, pBk⟩ := ho.periodic
  have hn := hA.1 L hL
  obtain ⟨ρ₁, R₁, m₁, _⟩ := ho.Q_local _ _ hn
  obtain ⟨ρ₂, R₂, m₂, _⟩ := ho.R_local _ _ hn
  exact ⟨h _ _ pS pB _ ho.D_local.1, h _ _ pB pP _ ho.holonomyDefect_local.1,
    h _ _ pP pP _ ho.halfFaceTrace_local.1, h _ _ pB pB _ ho.curvature_local.1,
    h _ _ pB pB _ ho.K_local.1, h _ _ pS pS _ ho.Delta_local.1,
    h _ _ pB pBk _ ⟨ρ₁, R₁, m₁⟩, h _ _ pS pSk _ ⟨ρ₂, R₂, m₂⟩⟩
theorem isHolomorphicIn_one_const {N : ℕ} {O : Set (ComplexCoordinates N)} (ho : IsOpen O) (c : ℂ) :
    ComplexCoordinates.IsHolomorphicIn (N' := 1) O fun _ _ => c := by apply _root_.YangMills.Construction.PeriodicOperators.EntriesDets.holomorphicFnOn_const <;> assumption
theorem axisFields_holomorphic_on_strip (hpos : 0 < stripHalfWidth) (hQ : StripSymbols.Claim)
    {L k : ℕ} (ht : ResponseOperators.AtLevel stripHalfWidth L k)
    (hBk : IsPeriodic (colourEdges L k k)) (hB : IsPeriodic (colourEdges L k 0))
    (hPl : IsPeriodic (colourFaces L k 0))
    (hd : IsPeriodicKernel (colourEdges L k 0) (colourFaces L k 0)
      (scaledEdgeCoboundaryKernel L k 0))
    (hent : FourierSymbolIsEntire (colourEdges L k 0) (colourFaces L k 0)
      (scaledEdgeCoboundaryKernel L k 0))
    (hcurv : ∀ (q : Fin 4 → ℂ) (b : (colourEdges L k 0).UnitQuot → ℂ),
      (edgePauliCoordinates L k 0).mapOnCoeffs (vertexCoordinate (Face L k 0))
          scaledEdgeCoboundary (blochWave (colourEdges L k 0) q b) =
        blochWave (colourFaces L k 0) q (edgeCoboundarySymbol L k q b)) :
    IsOpen (openImStrip (2 * stripHalfWidth)) ∧
      (∀ p ∈ openImStrip (2 * stripHalfWidth), ResponseSymbolSummableAt L k p) ∧
      (∀ μ, HolomorphicOnEntrywise (n := 4) quotFnEntries
        (openImStrip (2 * stripHalfWidth)) fun p => axisAmplitude L k p μ) ∧
      (∀ μ, HolomorphicOnEntrywise (n := 4) quotFnEntries
        (openImStrip (2 * stripHalfWidth)) fun p => axisAmplitude L k (-p) μ) ∧
      (∀ μ, HolomorphicOnEntrywise (n := 4) quotFnEntries
        (openImStrip (2 * stripHalfWidth)) fun p => axisCurvature L k p μ) ∧
      (∀ μ, HolomorphicOnEntrywise (n := 4) quotFnEntries
        (openImStrip (2 * stripHalfWidth)) fun p => axisCurvature L k (-p) μ) ∧
      (∀ μ, HolomorphicOnEntrywise (n := 4) quotFnEntries
        (openImStrip (2 * stripHalfWidth)) fun p => axisField L k p μ) ∧
      ∀ μ, HolomorphicOnEntrywise (n := 4) quotFnEntries
        (openImStrip (2 * stripHalfWidth)) fun p => axisField L k (-p) μ := by
  have hOopen : IsOpen (openImStrip (2 * stripHalfWidth)) :=
    (hQ.1 _ (by linarith)).2.1
  have hneg : ∀ z ∈ openImStrip (2 * stripHalfWidth),
      -z ∈ openImStrip (2 * stripHalfWidth) := fun z hz μ => by simpa using hz μ
  obtain ⟨υ, hυ, _, hr, _⟩ := ht.exists_rate
  have hsub : openImStrip (2 * stripHalfWidth) ⊆ openImStrip υ :=
    fun z hz μ => (hz μ).trans hυ
  have hfin : Finite (colourEdges L k k).UnitQuot := hBk.finite_quot
  have hfin0 : Finite (colourEdges L k 0).UnitQuot := hB.finite_quot
  let _ := Fintype.ofFinite (colourEdges L k k).UnitQuot
  let _ := Fintype.ofFinite (colourEdges L k 0).UnitQuot
  obtain ⟨O₁, _, hO₁, hon⟩ := ht.near
  have hOs : openImStrip (2 * stripHalfWidth) ⊆ O₁ := fun z hz => hO₁ fun μ => (hz μ).le
  have hh : ∀ (c : (colourEdges L k 0).UnitQuot) (c' : (colourEdges L k k).UnitQuot),
      ComplexCoordinates.IsHolomorphicIn (N := 4) (N' := 1) (openImStrip (2 * stripHalfWidth))
        fun x _ => linearMapEntry (ResponseOperators.respSymbol L k x) c c' := fun c c' =>
    isHolomorphicIn_one_mono (hon.resp_holomorphic.2.2 (c, c')) hOs hOopen
  have hresp : ∀ (μ : Fin 4) (c : (colourEdges L k 0).UnitQuot),
      ComplexCoordinates.IsHolomorphicIn (N := 4) (N' := 1) (openImStrip (2 * stripHalfWidth))
        fun x _ => responseOnAxis L k x μ c := fun μ c => by
    have hsum := isHolomorphicIn_one_sum (N := 4) Finset.univ hOopen
      (u := fun c' x => linearMapEntry (ResponseOperators.respSymbol L k x) c c' *
        constantFormAmplitude L k (axisPauliElement μ 2) c')
      (fun c' _ => isHolomorphicIn_one_mul (hh c c') (isHolomorphicIn_one_const hOopen _))
    exact isHolomorphicIn_one_congr hsum fun x _ => linearMap_apply_eq_sum_entry _ _ _
  have hdd : ∀ (c : (colourFaces L k 0).UnitQuot) (c' : (colourEdges L k 0).UnitQuot),
      ComplexCoordinates.IsHolomorphicIn (N := 4) (N' := 1) (openImStrip (2 * stripHalfWidth))
        fun x _ => linearMapEntry (edgeCoboundarySymbol L k x) c c' := fun c c' =>
    isHolomorphicIn_one_mono (isHolomorphicIn_linearMapEntry_of_entire hQ hB hPl hd hent c c')
      (subset_univ _) hOopen
  have hcs : ∀ (μ : Fin 4) (c : (colourFaces L k 0).UnitQuot),
      ComplexCoordinates.IsHolomorphicIn (N := 4) (N' := 1) (openImStrip (2 * stripHalfWidth))
        fun x _ => edgeCoboundarySymbol L k x (responseOnAxis L k x μ) c := fun μ c => by
    have hsum := isHolomorphicIn_one_sum (N := 4) Finset.univ hOopen
      (u := fun c' x => linearMapEntry (edgeCoboundarySymbol L k x) c c' * responseOnAxis L k x μ c')
      (fun c' _ => isHolomorphicIn_one_mul (hdd c c') (hresp μ c'))
    exact isHolomorphicIn_one_congr hsum fun x _ => linearMap_apply_eq_sum_entry _ _ _
  have eA : ∀ (μ : Fin 4), ∀ x ∈ openImStrip (2 * stripHalfWidth),
      axisAmplitude L k x μ = responseOnAxis L k x μ := fun μ x hx => by
    unfold axisAmplitude
    split_ifs
    · exact responseAmplitude_eq_responseOnAxis hfin hr (hsub hx) μ
    · rfl
  have eC : ∀ (μ : Fin 4), ∀ x ∈ openImStrip (2 * stripHalfWidth),
      axisCurvature L k x μ = edgeCoboundarySymbol L k x (responseOnAxis L k x μ) :=
    fun μ x hx => by
      unfold axisCurvature
      split_ifs
      · rw [responseCurvature, hcurv, waveAmplitude_blochWave,
          responseAmplitude_eq_responseOnAxis hfin hr (hsub hx) μ]
      · rfl
  have hA : ∀ (μ : Fin 4) (c : (colourEdges L k 0).UnitQuot),
      ComplexCoordinates.IsHolomorphicIn (N := 4) (N' := 1) (openImStrip (2 * stripHalfWidth))
        fun x _ => axisAmplitude L k x μ c := fun μ c =>
    isHolomorphicIn_one_congr (hresp μ c) fun x hx => congrFun (eA μ x hx) c
  have hC : ∀ (μ : Fin 4) (c : (colourFaces L k 0).UnitQuot),
      ComplexCoordinates.IsHolomorphicIn (N := 4) (N' := 1) (openImStrip (2 * stripHalfWidth))
        fun x _ => axisCurvature L k x μ c := fun μ c =>
    isHolomorphicIn_one_congr (hcs μ c) fun x hx => congrFun (eC μ x hx) c
  refine ⟨hOopen, fun p hp => ⟨hr.summable p (hsub hp), hr.summable (-p) (hsub (hneg p hp))⟩,
    fun μ => ⟨by norm_num, hOopen, fun c => hA μ c⟩,
    fun μ => ⟨by norm_num, hOopen, fun c => isHolomorphicIn_one_comp_neg (hA μ c) hneg⟩,
    fun μ => ⟨by norm_num, hOopen, fun c => hC μ c⟩,
    fun μ => ⟨by norm_num, hOopen, fun c => isHolomorphicIn_one_comp_neg (hC μ c) hneg⟩,
    fun μ => ⟨by norm_num, hOopen, fun c => isHolomorphicIn_one_const_mul _ (hA μ c)⟩,
    fun μ => ⟨by norm_num, hOopen, fun c =>
      isHolomorphicIn_one_const_mul _ (isHolomorphicIn_one_comp_neg (hA μ c) hneg)⟩⟩
theorem backgroundPropertiesHold (hN : FreeStrip.ConstantsAdmissible.ConstantsAreAdmissible)
    (hR : ResponseOperators.Claim) (hP : ResponseProperties.AllProperties)
    (hW : PlaneWaveCalculus.PlaneWaveCalculusHolds) (hQ : StripSymbols.Claim)
    (hS : SymbolCalculus.Claim) (hFO : FreeOperators.FreeOperatorsArePeriodic)
    (hSym : Symbols.Claim) (hId : IdKernelFacts.Claim)
    (hJ : JetDomains.OpFunJetTheory)
    (hO : ScaledOperatorFunctions.ScaledOperatorFunctionsClaim)
    (hT : TowerTranslations.Claim)
    (hA : IteratedSmallFieldMeans.IteratedMeansClaim) : BackgroundPropertiesHold := by
  intro L hL k hk
  obtain ⟨_, hpos, _⟩ := stripHalfWidth_spec hN
  have ho := hO.1 L hL k hk
  obtain ⟨_, pB, pP, _, pBk⟩ := ho.1.periodic
  have ht := responseAtLevel hN hR hL hk
  obtain ⟨hd, hent, hcurv⟩ := scaledEdgeCoboundary_symbol_spec hFO hS hSym hId hL hk pB pP
  have hfin : Finite (colourEdges L k k).UnitQuot := pBk.finite_quot
  obtain ⟨υ, hυ, _, hr, _⟩ := ht.exists_rate
  have hat : ∀ q ∈ momentumPolydisc stripHalfWidth, ∀ μ, PointProperties L k q μ := fun q hq μ => by
    have hqs : q ∈ openImStrip υ := fun ρ => by
      have := (Complex.abs_im_le_norm (q ρ)).trans (hq ρ)
      linarith
    refine pointProperties_of hN hP hW hT hL hk hq μ
      (responseAmplitude_eq_responseOnAxis hfin hr hqs μ) ?_
    rw [responseCurvature, hcurv, waveAmplitude_blochWave]
  obtain ⟨hOopen, hformed, hAp, hAm, hCp, hCm, hFp, hFm⟩ :=
    axisFields_holomorphic_on_strip hpos hQ ht pBk pB pP hd hent hcurv
  refine ⟨fun p hp μPlus μMinus => ⟨hat p hp μPlus, hat (-p) (fun ρ => ?_) μMinus⟩, hent.1,
    fun μPlus μMinus => forAllEight_of hO hA hL hk fun I I' hI hI' T hT' =>
      jetWellDefined_of_local hFO hS hJ hpos pB μPlus μMinus hI hI' hT', fun μPlus μMinus => ?_⟩
  · simpa using hp ρ
  · refine ⟨openImStrip (2 * stripHalfWidth), hOopen, fun p hp ρ => ?_, hformed,
      hAp μPlus, hAm μMinus, hCp μPlus, hCm μMinus,
      forAllEight_of hO hA hL hk fun I I' hI hI' T hT' =>
        componentsHolomorphicOn_of_local (ho.2 I I' hI hI') (hFp μPlus) (hFm μMinus) hT'⟩
    have := (Complex.abs_im_le_norm (p ρ)).trans (hp ρ)
    linarith
end YangMills.Construction.Tower.FullSpace.BackgroundProperties
end
