import YangMills.Construction.PeriodicOperators.SymmetricKernelOfAQuadraticFormProof
import YangMills.Construction.Towers.ACommonWidthAndTheTransposedStraightAverage
import YangMills.Construction.Towers.MapsOfTheResponseAndTheirTransposes
import YangMills.Construction.Towers.MeansAtTheTrivialConfigurationOfTheScaledPictureOnTheWholeProof
import YangMills.Construction.Towers.PeriodicExtensionsAndPeriodisation
import YangMills.Construction.Towers.PolarisationAtTheResponseFieldProof
import YangMills.Construction.Towers.PropertiesOfTheBackgroundsProof
import YangMills.Construction.Towers.RelationsOfTheResponseOnTheTorus
import YangMills.Construction.Towers.ResponseFieldOfAPlaneWave
import YangMills.Construction.Towers.TheMassiveFamilyIsTemperedProof
import YangMills.Construction.Towers.TheResponseSymbolNearTheStrip
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Tower.ResponseOfFourierMode
open PeriodicOperators (IsPeriodic IsPeriodicKernel colourEdges toComplexVec bilinDot
  applyKernel dualLattice imStrip periodicMatrix)
open TorusResponseField
open CriticalBranchResponse
open BackgroundFieldResponse (responseKernel responseDefect)
open ResponseOperators (ClassFnEqForm)
open PeriodicOperators.Tempered (EventuallyForSides UnitEdge imagComponent realComponent)
open LocalKernels (projPositiveEdge)
open LocalKernels.Periodisation (ProjEdgesCompatible ProjCellsClassified periodSide)
open InfiniteLattice (AmbientSpace)
theorem pauliCoeff_linear_combination {X Y : Matrices.ComplexMatrix2}
    (hX : X ∈ Matrices.ComplexMatrix2.traceless) (hY : Y ∈ Matrices.ComplexMatrix2.traceless)
    (c d : ℂ) (a : Fin 3) :
    pauliCoeff a (c • X + d • Y) = c * pauliCoeff a X + d * pauliCoeff a Y := by apply _root_.YangMills.Construction.Tower.LeftChartAlgebra.FiniteFaceDerivatives.pauliCoeff_linearCombination <;> assumption
theorem pauliCoeff_smul {X : Matrices.ComplexMatrix2} (hX : X ∈ Matrices.ComplexMatrix2.traceless)
    (c : ℂ) (a : Fin 3) :
    pauliCoeff a (c • X) = c * pauliCoeff a X := by apply _root_.YangMills.Construction.Tower.MassiveOpFunctions.Tempered.pauliCoeff_smul <;> assumption
theorem pauliCoeff_add_smul {X Y : Matrices.ComplexMatrix2}
    (hX : X ∈ Matrices.ComplexMatrix2.traceless) (hY : Y ∈ Matrices.ComplexMatrix2.traceless)
    (z : ℂ) (a : Fin 3) :
    pauliCoeff a (X + z • Y) = pauliCoeff a X + z * pauliCoeff a Y := by
  have h := pauliCoeff_linear_combination hX hY 1 z a
  simpa using h
theorem pauliFamily_mem_traceless (a : Fin 3) :
    Matrices.ComplexMatrix2.pauliFamily a ∈ Matrices.ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.OneLoopLaw.PlaneWaveSymmetries.pauliFamily_mem_traceless <;> assumption
theorem sum_pauliCoeff_smul {X : Matrices.ComplexMatrix2}
    (hX : X ∈ Matrices.ComplexMatrix2.traceless) :
    ∑ a, pauliCoeff a X • Matrices.ComplexMatrix2.pauliFamily a = X := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.sum_pauliCoeff_smul <;> assumption
theorem hermitianPart_mem {X : Matrices.ComplexMatrix2} (hX : X ∈ Matrices.ComplexMatrix2.traceless) :
    (2⁻¹ : ℂ) • (X + X.conjTranspose) ∈ Matrices.ComplexMatrix2.hermitianTraceless := by apply _root_.YangMills.SharedProofs.p48895 <;> assumption
theorem skewPart_mem {X : Matrices.ComplexMatrix2} (hX : X ∈ Matrices.ComplexMatrix2.traceless) :
    (2 * Complex.I)⁻¹ • (X - X.conjTranspose) ∈ Matrices.ComplexMatrix2.hermitianTraceless := by apply _root_.YangMills.SharedProofs.p51273 <;> assumption
theorem eq_hermitianPart_add_I_smul (X : Matrices.ComplexMatrix2) :
    X = (2⁻¹ : ℂ) • (X + X.conjTranspose) +
      Complex.I • ((2 * Complex.I)⁻¹ • (X - X.conjTranspose)) := by
  have hI : Complex.I * (2 * Complex.I)⁻¹ = (2⁻¹ : ℂ) := by
    field_simp
  rw [smul_smul, hI, ← smul_add]
  ext i j
  simp
  ring
section Forms
variable {L n k : ℕ}
theorem realComponent_mem {B : UnitEdge L n → Matrices.ComplexMatrix2}
    (hB : B ∈ complexEdgeForms L n 0 0) :
    realComponent B ∈ edgeFormSpace L n 0 0 := by apply _root_.YangMills.SharedProofs.p16359 <;> assumption
theorem imagComponent_mem {B : UnitEdge L n → Matrices.ComplexMatrix2}
    (hB : B ∈ complexEdgeForms L n 0 0) :
    imagComponent B ∈ edgeFormSpace L n 0 0 := by apply _root_.YangMills.SharedProofs.p9724 <;> assumption
theorem topEdgeEquivUnit_isPositivelyOriented {b : Edge L n k k} (hb : b.IsPositivelyOriented) :
    (topEdgeEquivUnit L n k b).IsPositivelyOriented := by
  obtain ⟨μ, h⟩ := hb
  refine ⟨μ, ?_⟩
  show topVertexEquivUnit L n k b.target - topVertexEquivUnit L n k b.source = _
  rw [← map_sub, h, topVertexEquivUnit_unitStep]
theorem topEdgeEquivUnit_opposite (b : Edge L n k k) :
    topEdgeEquivUnit L n k b.opposite = (topEdgeEquivUnit L n k b).opposite :=
  PeriodicLattice.Bond.ext rfl rfl
theorem topForm_mem {R : UnitEdge L n → Matrices.ComplexMatrix2} (hR : R ∈ edgeFormSpace L n 0 0) :
    topForm L n k R ∈ edgeFormSpace L n k k := by
  refine ⟨fun b hb => hR.1 _ (topEdgeEquivUnit_isPositivelyOriented hb), fun b => ?_⟩
  show R (topEdgeEquivUnit L n k b.opposite) = -R (topEdgeEquivUnit L n k b)
  rw [topEdgeEquivUnit_opposite, hR.2]
theorem complexify_realizes (r : RealPeriodicField L n k) :
    (complexify r).RealizedBy r := by apply _root_.YangMills.SharedProofs.p20583 <;> assumption
theorem opposite_isPositivelyOriented_of_not {j : ℕ} {b : Edge L n k j}
    (hb : ¬ b.IsPositivelyOriented) :
    b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.Tower.IteratedMeans.opposite_isPositivelyOriented_of_not <;> assumption
theorem complexForm_ext_of_coeffs {j : ℕ} (hc : ProjCellsClassified L n k j)
    {A A' : complexEdgeForms L n k j}
    (h : ∀ ι : (colourEdges L k j).Carrier,
      (edgePauliCoordinates L n k j).coeffs A.1 (ι.1, projPositiveEdge L n k j ι.2) =
        (edgePauliCoordinates L n k j).coeffs A'.1 (ι.1, projPositiveEdge L n k j ι.2)) :
    A = A' := by
  have hpos : ∀ b : Edge L n k j, b.IsPositivelyOriented → A.1 b = A'.1 b := by
    intro b hb
    obtain ⟨b', hb'⟩ := (hc .edge).1 (⟨b, hb⟩ : Tower.PositiveEdge L n k j)
    have e : projPositiveEdge L n k j b' = ⟨b, hb⟩ := hb'
    have h' : ∀ a, pauliCoeff a (A.1 b) = pauliCoeff a (A'.1 b) := by
      intro a
      have := h (a, b')
      simpa [edgePauliCoordinates, toPauliCoeffs, restrictToPositiveEdges, e] using this
    rw [← sum_pauliCoeff_smul (A.2.1 b hb), ← sum_pauliCoeff_smul (A'.2.1 b hb)]
    exact Finset.sum_congr rfl fun a _ => by rw [h' a]
  apply Subtype.ext
  funext b
  by_cases hb : b.IsPositivelyOriented
  · exact hpos b hb
  · have e : b.opposite.opposite = b := PeriodicLattice.Bond.ext rfl rfl
    have r := opposite_isPositivelyOriented_of_not hb
    have h1 := A.2.2 b.opposite
    have h2 := A'.2.2 b.opposite
    rw [e] at h1 h2
    rw [h1, h2, hpos _ r]
end Forms
section Wave
variable {L n k : ℕ}
theorem meshAt_top : meshAt L k k = 1 := by apply _root_.YangMills.Construction.Tower.FullSpace.IterTransposesOnFullSpace.meshAt_self <;> assumption
theorem projPositiveEdge_sub (hb : ProjEdgesCompatible L n k k)
    (b : PeriodicOperators.PosEdge L k k) (ν : Fin 4)
    (hν : b.1.terminal - b.1.initial = InfiniteLattice.axisStep (meshAt L k k) ν) :
    (projPositiveEdge L n k k b).1.target - (projPositiveEdge L n k k b).1.source =
      PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth k k) ν := by
  obtain ⟨ht, hh⟩ := hb.1 b.1
  rw [hb.2.1 b, ht, hh]
  apply Subtype.ext
  have hv : (b.1.terminal : AmbientSpace) =
      (b.1.initial : AmbientSpace) + (InfiniteLattice.axisStep (meshAt L k k) ν : AmbientSpace) := by
    rw [← hν]
    simp
  funext μ
  show (((b.1.terminal : AmbientSpace) μ : ℝ) : AddCircle (PeriodicLattice.torusSide L n)) -
      (((b.1.initial : AmbientSpace) μ : ℝ) : AddCircle (PeriodicLattice.torusSide L n)) =
    PeriodicLattice.pointOnAxis L n ν
      (PeriodicLattice.meshSize L (PeriodicLattice.levelDepth k k)) μ
  rw [hv]
  by_cases h : μ = ν
  · subst h
    simp [PeriodicLattice.pointOnAxis, InfiniteLattice.axisStep, meshAt, PeriodicLattice.meshSize,
      PeriodicLattice.levelDepth]
  · simp [PeriodicLattice.pointOnAxis, InfiniteLattice.axisStep, meshAt, PeriodicLattice.meshSize,
      PeriodicLattice.levelDepth, Pi.single_eq_of_ne h]
theorem topEdgeEquivUnit_sub {c : Edge L n k k} {ν : Fin 4}
    (hd : c.target - c.source = PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth k k) ν) :
    (topEdgeEquivUnit L n k c).target - (topEdgeEquivUnit L n k c).source =
      PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth 0 0) ν := by
  show topVertexEquivUnit L n k c.target - topVertexEquivUnit L n k c.source = _
  rw [← map_sub, hd, topVertexEquivUnit_unitStep]
theorem unitStep_ne {ν μ : Fin 4} (h : ν ≠ μ) :
    PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth 0 0) ν ≠
      PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth 0 0) μ := by apply _root_.YangMills.Construction.Tower.MassiveOpFunctions.Tempered.unitStep_ne <;> assumption
theorem phase_coe (hL : 0 < L) {p : AmbientSpace} (hp : p ∈ dualLattice (2 * L ^ n))
    (y : AmbientSpace) :
    PeriodicOperators.Tempered.phase (L := L) (n := n) p
        (fun μ => ((y μ : ℝ) : AddCircle (PeriodicLattice.torusSide L n))) =
      Complex.exp (Complex.I * bilinDot (toComplexVec p) (toComplexVec y)) := by apply _root_.YangMills.Construction.Tower.MassiveOpFunctions.Tempered.phase_coe <;> assumption
theorem constantEdgeForm_apply (hs : meshAt L k k ≠ 0) (ε : Fin 4 → Matrices.ComplexMatrix2)
    (β : FullSpace.Edge L k k) (μ : Fin 4)
    (hβ : β.terminal - β.initial = InfiniteLattice.axisStep (meshAt L k k) μ) :
    FullSpace.constantEdgeForm L k ε β = ε μ := by apply _root_.YangMills.Construction.Tower.FullSpace.BackgroundProperties.constantEdgeForm_eq <;> assumption
theorem constantEdgeForm_isQuotInvariant (hT : PeriodicOperators.TowerTranslations.Claim)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hk : 1 ≤ k) (hs : meshAt L k k ≠ 0)
    (ε : Fin 4 → Matrices.ComplexMatrix2) :
    PeriodicOperators.IsQuotInvariant (colourEdges L k k)
      ((FullSpace.edgePauliCoordinates L k k).coeffs (FullSpace.constantEdgeForm L k ε)) := by
  have hstep : ∀ ι ι' : (colourEdges L k k).Carrier,
      (∃ n : Fin 4 → ℤ, ι' = (colourEdges L k k).translate (1 • n) ι) →
        (FullSpace.edgePauliCoordinates L k k).coeffs (FullSpace.constantEdgeForm L k ε) ι =
          (FullSpace.edgePauliCoordinates L k k).coeffs (FullSpace.constantEdgeForm L k ε) ι' := by
    rintro ⟨a, b⟩ _ ⟨n, rfl⟩
    obtain ⟨μ, hμ⟩ := b.2
    rw [(hT L hL k k hk le_rfl (1 • n)).2.2.2.1 a b μ hμ]
    show pauliCoeff a (FullSpace.constantEdgeForm L k ε b.1) =
      pauliCoeff a (FullSpace.constantEdgeForm L k ε (InfiniteLattice.Link.forwardFrom _ μ))
    rw [constantEdgeForm_apply hs ε b.1 μ hμ,
      constantEdgeForm_apply hs ε _ μ (by simp [InfiniteLattice.Link.forwardFrom])]
  intro ι ι' e
  exact congrArg (Quot.lift _ hstep) e
theorem constantFormAmplitude_mkQuot (hT : PeriodicOperators.TowerTranslations.Claim)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hk : 1 ≤ k) (hs : meshAt L k k ≠ 0)
    (ε : Fin 4 → Matrices.ComplexMatrix2) (a : Fin 3) (b : PeriodicOperators.PosEdge L k k)
    (ρ : Fin 4)
    (hb : b.1.terminal - b.1.initial = InfiniteLattice.axisStep (meshAt L k k) ρ) :
    FullSpace.constantFormAmplitude L k ε ((colourEdges L k k).mkQuot 1 (a, b)) =
      pauliCoeff a (ε ρ) := by
  have e := PeriodicOperators.descendFn_mkQuot
    (constantEdgeForm_isQuotInvariant hT hL hk hs ε) (a, b)
  refine e.trans ?_
  show pauliCoeff a (FullSpace.constantEdgeForm L k ε b.1) = _
  rw [constantEdgeForm_apply hs ε _ ρ hb]
theorem pauliCoeff_fourierModeForm (hT : PeriodicOperators.TowerTranslations.Claim)
    (hst : Conventions.IsAdmissibleBlockingFactor L) (hk : 1 ≤ k) (hL : 0 < L)
    (hb : ProjEdgesCompatible L n k k)
    {p : AmbientSpace} (hp : p ∈ dualLattice (2 * L ^ n)) (a : Fin 3) (μ : Fin 4)
    (ι : (colourEdges L k k).Carrier) :
    pauliCoeff ι.1 (PeriodicOperators.Tempered.fourierModeForm L n a p μ
        (topEdgeEquivUnit L n k (projPositiveEdge L n k k ι.2).1)) =
      FullSpace.planeWaveOfConstant L k (toComplexVec p) (FullSpace.axisPauliElement μ a) ι := by
  classical
  rcases ι with ⟨c, b⟩
  obtain ⟨ν, hν⟩ := b.2
  have hs : meshAt L k k ≠ 0 := by
    rw [meshAt_top]
    exact one_ne_zero
  have hd := topEdgeEquivUnit_sub (projPositiveEdge_sub hb b ν hν)
  have hpos := topEdgeEquivUnit_isPositivelyOriented (projPositiveEdge L n k k b).2
  have htail : ((topEdgeEquivUnit L n k (projPositiveEdge L n k k b).1).source :
      PeriodicLattice.FourTorus L n) =
      fun ρ => (((b.1.initial : AmbientSpace) ρ : ℝ) :
        AddCircle (PeriodicLattice.torusSide L n)) := by
    show (((projPositiveEdge L n k k b).1.source : Vertex L n k k) :
      PeriodicLattice.FourTorus L n) = _
    rw [hb.2.1 b, (hb.1 b.1).1]
    rfl
  have hphase : PeriodicOperators.Tempered.phase p
      ((topEdgeEquivUnit L n k (projPositiveEdge L n k k b).1).source :
        PeriodicLattice.FourTorus L n) =
        Complex.exp (Complex.I * bilinDot (toComplexVec p)
          (toComplexVec (b.1.initial : AmbientSpace))) := by
    rw [htail]
    exact phase_coe hL hp _
  have hval : PeriodicOperators.Tempered.fourierModeForm L n a p μ
      (topEdgeEquivUnit L n k (projPositiveEdge L n k k b).1) =
      if ν = μ then Complex.exp (Complex.I * bilinDot (toComplexVec p)
          (toComplexVec (b.1.initial : AmbientSpace))) •
        Matrices.ComplexMatrix2.pauliFamily a else 0 := by
    simp only [PeriodicOperators.Tempered.fourierModeForm, extendOddly, if_pos hpos]
    by_cases h : ν = μ
    · subst h
      rw [if_pos hd, if_pos rfl, hphase]
    · rw [if_neg h, if_neg]
      intro e
      exact unitStep_ne h (hd.symm.trans e)
  show _ = Complex.exp (Complex.I * bilinDot (toComplexVec p)
      (toComplexVec (b.1.initial : AmbientSpace))) *
    FullSpace.constantFormAmplitude L k (FullSpace.axisPauliElement μ a)
      ((colourEdges L k k).mkQuot 1 (c, b))
  rw [constantFormAmplitude_mkQuot hT hst hk hs _ c b ν hν, hval]
  by_cases h : ν = μ
  · subst h
    rw [if_pos rfl, pauliCoeff_smul (pauliFamily_mem_traceless a)]
    simp [FullSpace.axisPauliElement]
  · have h0 := pauliCoeff_smul (Matrices.ComplexMatrix2.traceless.zero_mem) 0 c
    have hz : pauliCoeff c (0 : Matrices.ComplexMatrix2) = 0 := by simpa using h0
    rw [if_neg h]
    simp [FullSpace.axisPauliElement, Pi.single_eq_of_ne h, hz]
theorem fourierModeForm_mem (hL : 2 ≤ L) (hn : 0 < n) (a : Fin 3) (p : AmbientSpace) (μ : Fin 4) :
    PeriodicOperators.Tempered.fourierModeForm L n a p μ ∈ complexEdgeForms L n 0 0 := by apply _root_.YangMills.Construction.Tower.MassiveOpFunctions.Tempered.fourierModeForm_mem <;> assumption
end Wave
section Images
variable {L n k : ℕ}
theorem projPositiveEdge_shiftEdge {j : ℕ} (hc : ProjCellsClassified L n k j)
    (b : PeriodicOperators.PosEdge L k j) (m : Fin 4 → ℤ) :
    projPositiveEdge L n k j (PeriodicOperators.shiftEdge (periodSide L n • m) b) =
      projPositiveEdge L n k j b :=
  (((hc .edge).2 b (PeriodicOperators.shiftEdge (periodSide L n • m) b)).2 ⟨m, rfl⟩).symm
theorem finite_quotMod {j : ℕ} (hc : ProjCellsClassified L n k j)
    [Finite (Tower.PositiveEdge L n k j)] :
    Finite ((colourEdges L k j).QuotMod (periodSide L n)) := by
  let f : (colourEdges L k j).QuotMod (periodSide L n) →
      Fin 3 × Tower.PositiveEdge L n k j :=
    Quot.lift (fun ι => (ι.1, projPositiveEdge L n k j ι.2)) (by
      rintro ι _ ⟨m, rfl⟩
      exact Prod.ext rfl (projPositiveEdge_shiftEdge hc ι.2 m).symm)
  refine Finite.of_injective f ?_
  intro c c' h
  obtain ⟨ι, rfl⟩ := Quot.exists_rep c
  obtain ⟨ι', rfl⟩ := Quot.exists_rep c'
  have h0 : (ι.1, projPositiveEdge L n k j ι.2) = (ι'.1, projPositiveEdge L n k j ι'.2) := h
  have h1 : ι.1 = ι'.1 := (Prod.mk.inj h0).1
  have h2 : projPositiveEdge L n k j ι.2 = projPositiveEdge L n k j ι'.2 :=
    (Prod.mk.inj h0).2
  obtain ⟨m, hm⟩ := ((hc .edge).2 ι.2 ι'.2).1 h2
  exact Quot.sound ⟨m, Prod.ext h1.symm hm⟩
theorem image_coeffs_blochWave {i j : ℕ} (hF : PeriodicOperators.Symbols.Claim)
    (hId : PeriodicOperators.IdKernelFacts.Claim)
    (hi : IsPeriodic (colourEdges L k i)) (hj : IsPeriodic (colourEdges L k j))
    (hfin : Finite ((colourEdges L k i).QuotMod (periodSide L n)))
    (hs : 0 < periodSide L n)
    {T : (colourEdges L k j).Carrier → (colourEdges L k i).Carrier → ℂ}
    (hT : IsPeriodicKernel (colourEdges L k i) (colourEdges L k j) T)
    {p : AmbientSpace} (hp : p ∈ dualLattice (periodSide L n))
    {B₁ B₂ : Edge L n k i → Matrices.ComplexMatrix2} {X₁ X₂ : edgeFormSpace L n k j}
    (h₁ : IsPeriodicImage L n k i j T B₁ X₁) (h₂ : IsPeriodicImage L n k i j T B₂ X₂)
    (φ : (colourEdges L k i).UnitQuot → ℂ)
    (hw : ∀ ι : (colourEdges L k i).Carrier,
      toPauliCoeffs (restrictToPositiveEdges B₁) (ι.1, projPositiveEdge L n k i ι.2) +
          Complex.I * toPauliCoeffs (restrictToPositiveEdges B₂)
            (ι.1, projPositiveEdge L n k i ι.2) =
        PeriodicOperators.blochWave (colourEdges L k i) (toComplexVec p) φ ι)
    (ι' : (colourEdges L k j).Carrier) :
    toPauliCoeffs (restrictToPositiveEdges (X₁ : Edge L n k j → Matrices.ComplexMatrix2))
        (ι'.1, projPositiveEdge L n k j ι'.2) +
      Complex.I * toPauliCoeffs (restrictToPositiveEdges (X₂ : Edge L n k j → Matrices.ComplexMatrix2))
        (ι'.1, projPositiveEdge L n k j ι'.2) =
      applyKernel T (PeriodicOperators.blochWave (colourEdges L k i) (toComplexVec p) φ) ι' := by
  obtain ⟨g₁, a₁, b₁⟩ := h₁
  obtain ⟨g₂, a₂, b₂⟩ := h₂
  have hstand := (hId _ hi).2.2.2.2.2.1 _ hj T hT
  obtain ⟨δ, hδ⟩ := hstand.exists_rate
  have w := hstand.withRate δ hδ
  have facts := hF.1 _ _ _ w.mid_periodic w.target_periodic w.source_periodic T _ δ w.left_kernel
    w.left_rate w.right_kernel w.right_rate
  have hκ : toComplexVec p ∈ PeriodicOperators.strictImStrip δ := by
    have e : PeriodicOperators.imVec (toComplexVec p) = 0 := by
      funext μ
      simp [PeriodicOperators.imVec, toComplexVec]
    show TorusMetric.euclidNormVec _ < δ
    rw [e]
    simpa [TorusMetric.euclidNormVec] using hδ.1
  have formed := facts.summable_on_strip _ hκ
  have act := facts.periodicMatrix_blochWave _ hs p hp φ (g₁ + Complex.I • g₂)
    (fun ι => by
      show g₁ _ + Complex.I * g₂ _ = _
      rw [a₁ ι, a₂ ι, hw ι]) ι'
  have lin : applyKernel (periodicMatrix (colourEdges L k i) (colourEdges L k j) T (periodSide L n))
        (g₁ + Complex.I • g₂) ((colourEdges L k j).mkQuot (periodSide L n) ι') =
      applyKernel (periodicMatrix (colourEdges L k i) (colourEdges L k j) T (periodSide L n)) g₁
          ((colourEdges L k j).mkQuot (periodSide L n) ι') +
        Complex.I * applyKernel
          (periodicMatrix (colourEdges L k i) (colourEdges L k j) T (periodSide L n)) g₂
          ((colourEdges L k j).mkQuot (periodSide L n) ι') := by
    let _ := Fintype.ofFinite ((colourEdges L k i).QuotMod (periodSide L n))
    simp only [applyKernel, tsum_fintype, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add,
      Finset.sum_add_distrib, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun c _ => ?_
    ring
  rw [← b₁ ι', ← b₂ ι', ← lin, act, (facts.applyKernel_blochWave _ formed φ ι').2]
theorem coeffs_add_smul {j : ℕ} (A₁ A₂ : edgeFormSpace L n k j) (z : ℂ)
    (b : Tower.PositiveEdge L n k j) (c : Fin 3) :
    (edgePauliCoordinates L n k j).coeffs ((A₁ : Edge L n k j → Matrices.ComplexMatrix2) +
        z • (A₂ : Edge L n k j → Matrices.ComplexMatrix2)) (c, b) =
      toPauliCoeffs (restrictToPositiveEdges (A₁ : Edge L n k j → Matrices.ComplexMatrix2)) (c, b) +
        z * toPauliCoeffs (restrictToPositiveEdges (A₂ : Edge L n k j → Matrices.ComplexMatrix2))
          (c, b) :=
  pauliCoeff_add_smul (A₁.2.1 _ b.2).2 (A₂.2.1 _ b.2).2 z c
theorem coeffs_meshScaledResponse (B : Edge L n k k → Matrices.ComplexMatrix2)
    (b : Tower.PositiveEdge L n k 0) (c : Fin 3) :
    toPauliCoeffs (restrictToPositiveEdges
        (meshScaledResponse L n k B : Edge L n k 0 → Matrices.ComplexMatrix2)) (c, b) =
      ((finestMesh L k : ℝ) : ℂ) *
        toPauliCoeffs (restrictToPositiveEdges
          (periodicResponse L n k B : Edge L n k 0 → Matrices.ComplexMatrix2)) (c, b) := by
  show pauliCoeff c ((finestMesh L k : ℝ) •
      (periodicResponse L n k B : Edge L n k 0 → Matrices.ComplexMatrix2) b.1) =
    ((finestMesh L k : ℝ) : ℂ) *
      pauliCoeff c ((periodicResponse L n k B : Edge L n k 0 → Matrices.ComplexMatrix2) b.1)
  rw [← Complex.coe_smul]
  exact pauliCoeff_smul ((periodicResponse L n k B).2.1 _ b.2).2 _ c
end Images
section Classes
variable {L k : ℕ} (hL : 0 < L)
include hL in
theorem tripleAmplitude_mkQuot (a j : (colourEdges L k 0).UnitQuot → ℂ)
    (m : (colourEdges L k k).UnitQuot → ℂ)
    (x : (FullSpace.fieldPeriodicData L k hL).Carrier) :
    FullSpace.tripleAmplitude L k hL a j m ((FullSpace.fieldPeriodicData L k hL).mkQuot 1 x) =
      FullSpace.tripleIndexFunction L k hL a j m x := by
  have hstep : ∀ ι ι' : (FullSpace.fieldPeriodicData L k hL).Carrier,
      (∃ n : Fin 4 → ℤ, ι' = (FullSpace.fieldPeriodicData L k hL).translate (1 • n) ι) →
        FullSpace.tripleIndexFunction L k hL a j m ι =
          FullSpace.tripleIndexFunction L k hL a j m ι' := by
    rintro ⟨pl, ι⟩ _ ⟨n, rfl⟩
    cases pl
    · exact congrArg a (Quot.sound ⟨n, rfl⟩)
    · exact congrArg j (Quot.sound ⟨n, rfl⟩)
    · exact congrArg m (Quot.sound ⟨n, rfl⟩)
  have hone : PeriodicOperators.IsQuotInvariant (FullSpace.fieldPeriodicData L k hL)
      (FullSpace.tripleIndexFunction L k hL a j m) := by
    intro ι ι' e
    exact congrArg (Quot.lift _ hstep) e
  exact PeriodicOperators.descendFn_mkQuot hone x
end Classes
section Coefficients
theorem pauliCoeff_sum_smul (c : Fin 3 → ℂ) (a : Fin 3) :
    pauliCoeff a (∑ b, c b • Matrices.ComplexMatrix2.pauliFamily b) = c a := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.pauliCoeff_sum_smul <;> assumption
theorem pauliFamily_mem_hermitianTraceless (a : Fin 3) :
    Matrices.ComplexMatrix2.pauliFamily a ∈ Matrices.ComplexMatrix2.hermitianTraceless := by apply _root_.YangMills.SharedProofs.p1437 <;> assumption
theorem halfTrace_mul_eq_sum (hP : OneLoop.PauliMatrixRelations) {X Y : Matrices.ComplexMatrix2}
    (hX : X ∈ Matrices.ComplexMatrix2.traceless) (hY : Y ∈ Matrices.ComplexMatrix2.traceless) :
    Matrices.ComplexMatrix2.halfTrace (X * Y) = ∑ a, pauliCoeff a X * pauliCoeff a Y := by apply _root_.YangMills.SharedProofs.p22145 <;> assumption
end Coefficients
section BlockEvaluations
open PeriodicOperators (swapKernel)
variable {L n k : ℕ}
theorem full_ofCoeffs_coeffs {j : ℕ} {G : FullSpace.Edge L k j → Matrices.ComplexMatrix2}
    (hG : G ∈ FullSpace.complexEdgeForms (meshAt L k j)) :
    (FullSpace.edgePauliCoordinates L k j).ofCoeffs ((FullSpace.edgePauliCoordinates L k j).coeffs G) = G := by apply _root_.YangMills.Construction.Tower.FullSpace.TrivialFieldMeans.ofCoeffs_coeffs <;> assumption
theorem ofCoeffs_coeffs {j : ℕ} {X : Edge L n k j → Matrices.ComplexMatrix2}
    (hX : X ∈ complexEdgeForms L n k j) :
    (edgePauliCoordinates L n k j).ofCoeffs ((edgePauliCoordinates L n k j).coeffs X) = X := by
  classical
  have hpos : ∀ (b : Edge L n k j) (h : b.IsPositivelyOriented),
      ofPauliCoeffs (toPauliCoeffs (restrictToPositiveEdges X)) ⟨b, h⟩ = X b :=
    fun b h => sum_pauliCoeff_smul (hX.1 b h)
  funext b
  show extendOddly (fun b => if h : b.IsPositivelyOriented then
    ofPauliCoeffs (toPauliCoeffs (restrictToPositiveEdges X)) ⟨b, h⟩ else 0) b = X b
  by_cases hb : b.IsPositivelyOriented
  · simp only [extendOddly, if_pos hb, dif_pos hb]
    exact hpos b hb
  · have r := opposite_isPositivelyOriented_of_not hb
    simp only [extendOddly, if_neg hb, dif_pos r]
    rw [hpos _ r, hX.2 b, neg_neg]
theorem not_opposite_isPositivelyOriented {j : ℕ} (hL : 2 ≤ L) (hnk : k < n) (hj : j ≤ k)
    {b : Edge L n k j} (hb : b.IsPositivelyOriented) : ¬ b.opposite.IsPositivelyOriented := by
  rcases PeriodicLattice.MatrixValued.xor_isPositivelyOriented_opposite (L := L) (m := n)
      (j := PeriodicLattice.levelDepth k j) hL (by simp [PeriodicLattice.levelDepth]; omega) b with
    ⟨-, h'⟩ | ⟨-, h'⟩
  · exact h'
  · exact absurd hb h'
def indicatorCoeffs {j : ℕ} (κ : Fin 3 × Tower.PositiveEdge L n k j) :
    Fin 3 × Tower.PositiveEdge L n k j → ℂ :=
  open Classical in fun ι => if ι = κ then 1 else 0
def indicatorForm {j : ℕ} (κ : Fin 3 × Tower.PositiveEdge L n k j) :
    Edge L n k j → Matrices.ComplexMatrix2 :=
  (edgePauliCoordinates L n k j).ofCoeffs (indicatorCoeffs κ)
theorem indicatorForm_of_pos {j : ℕ} (κ : Fin 3 × Tower.PositiveEdge L n k j)
    (b : Edge L n k j) (h : b.IsPositivelyOriented) :
    indicatorForm κ b = ofPauliCoeffs (indicatorCoeffs κ) ⟨b, h⟩ := by
  classical
  show extendOddly (fun b => if h : b.IsPositivelyOriented then
    ofPauliCoeffs (indicatorCoeffs κ) ⟨b, h⟩ else 0) b = _
  simp only [extendOddly, if_pos h, dif_pos h]
theorem indicatorForm_of_not_pos {j : ℕ} (κ : Fin 3 × Tower.PositiveEdge L n k j)
    (b : Edge L n k j) (h : ¬ b.IsPositivelyOriented) :
    indicatorForm κ b = -ofPauliCoeffs (indicatorCoeffs κ)
      ⟨b.opposite, opposite_isPositivelyOriented_of_not h⟩ := by
  classical
  show extendOddly (fun b => if h : b.IsPositivelyOriented then
    ofPauliCoeffs (indicatorCoeffs κ) ⟨b, h⟩ else 0) b = _
  simp only [extendOddly, if_neg h, dif_pos (opposite_isPositivelyOriented_of_not h)]
theorem indicatorForm_mem {j : ℕ} (hL : 2 ≤ L) (hnk : k < n) (hj : j ≤ k)
    (κ : Fin 3 × Tower.PositiveEdge L n k j) : indicatorForm κ ∈ edgeFormSpace L n k j := by
  classical
  have hrr : ∀ b : Edge L n k j, b.opposite.opposite = b :=
    fun b => PeriodicLattice.Bond.ext rfl rfl
  refine ⟨fun b hb => ?_, fun b => ?_⟩
  · rw [indicatorForm_of_pos κ b hb]
    show ∑ a, indicatorCoeffs κ (a, ⟨b, hb⟩) • Matrices.ComplexMatrix2.pauliFamily a ∈
      Matrices.ComplexMatrix2.hermitianTraceless
    refine Matrices.ComplexMatrix2.hermitianTraceless.sum_mem fun a _ => ?_
    by_cases e : (a, (⟨b, hb⟩ : Tower.PositiveEdge L n k j)) = κ
    · simp only [indicatorCoeffs, if_pos e, one_smul]
      exact pauliFamily_mem_hermitianTraceless a
    · simp only [indicatorCoeffs, if_neg e, zero_smul]
      exact Matrices.ComplexMatrix2.hermitianTraceless.zero_mem
  · by_cases hb : b.IsPositivelyOriented
    · have hr := not_opposite_isPositivelyOriented hL hnk hj hb
      rw [indicatorForm_of_not_pos κ _ hr, indicatorForm_of_pos κ b hb]
      simp only [hrr]
    · rw [indicatorForm_of_not_pos κ _ hb,
        indicatorForm_of_pos κ _ (opposite_isPositivelyOriented_of_not hb), neg_neg]
theorem coeffs_indicatorForm {j : ℕ} (κ : Fin 3 × Tower.PositiveEdge L n k j) :
    toPauliCoeffs (restrictToPositiveEdges (indicatorForm κ)) = indicatorCoeffs κ := by
  classical
  funext ι
  show pauliCoeff ι.1 (indicatorForm κ ι.2.1) = _
  rw [indicatorForm_of_pos κ _ ι.2.2]
  exact pauliCoeff_sum_smul (fun a => indicatorCoeffs κ (a, ι.2)) ι.1
theorem finite_positiveEdge (hL : 0 < L) {j : ℕ} : Finite (Tower.PositiveEdge L n k j) := by apply _root_.YangMills.SharedProofs.p11983 <;> assumption
theorem edgeFormPairing_eq_tsum (hL : 0 < L) (hP : OneLoop.PauliMatrixRelations) {j : ℕ}
    {A B : Edge L n k j → Matrices.ComplexMatrix2} (hA : A ∈ complexEdgeForms L n k j)
    (hB : B ∈ complexEdgeForms L n k j) :
    edgeFormPairing A B = ∑' κ : Fin 3 × Tower.PositiveEdge L n k j,
      toPauliCoeffs (restrictToPositiveEdges A) κ * toPauliCoeffs (restrictToPositiveEdges B) κ := by
  have := finite_positiveEdge (n := n) (k := k) (j := j) hL
  let _ := Fintype.ofFinite (Tower.PositiveEdge L n k j)
  have h₁ : ∀ b : Tower.PositiveEdge L n k j,
      Matrices.ComplexMatrix2.halfTrace (A b.1 * B b.1) =
      ∑ a, toPauliCoeffs (restrictToPositiveEdges A) (a, b) *
        toPauliCoeffs (restrictToPositiveEdges B) (a, b) :=
    fun b => halfTrace_mul_eq_sum hP (hA.1 _ b.2) (hB.1 _ b.2)
  show ∑ᶠ b : Tower.PositiveEdge L n k j, Matrices.ComplexMatrix2.halfTrace (A b.1 * B b.1) = _
  rw [finsum_eq_sum_of_fintype, tsum_fintype, Fintype.sum_prod_type_right]
  exact Finset.sum_congr rfl fun b _ => h₁ b
theorem coeffs_transposeMap (hL : 2 ≤ L) (hnk : k < n)
    (hP : OneLoop.PauliMatrixRelations)
    {mT : (Edge L n k 0 → Matrices.ComplexMatrix2) → Edge L n k k → Matrices.ComplexMatrix2}
    (H : PauliComponentsOfSymmetricKernel.HasLocalKernel (edgePauliCoordinates L n k 0) (edgePauliCoordinates L n k k) mT)
    (hQ : ∀ f ∈ edgeFormSpace L n k 0, mT f = crossingSmoothingIter L n k k f)
    (hMaps : ResponseMaps.OnTower L n k)
    (m : (edgePairedSpace L n k 0).complexSubmodule →ₗ[ℂ]
      (edgePairedSpace L n k k).complexSubmodule)
    (hm : ∀ f : (edgePairedSpace L n k 0).complexSubmodule, (m f).1 = mT f.1)
    (ν₁ ν₂ : edgeFormSpace L n k k) (X : (edgePairedSpace L n k k).complexSubmodule)
    (hX : X.1 = (ν₁ : Edge L n k k → Matrices.ComplexMatrix2) +
      Complex.I • (ν₂ : Edge L n k k → Matrices.ComplexMatrix2))
    (κ₀ : Fin 3 × Tower.PositiveEdge L n k 0) :
    toPauliCoeffs (restrictToPositiveEdges (PairedFunctionSpace.transposeMap m X).1) κ₀ =
      toPauliCoeffs (restrictToPositiveEdges
          (crossingSmoothingTranspose L n k ν₁ : Edge L n k 0 → Matrices.ComplexMatrix2)) κ₀ +
        Complex.I * toPauliCoeffs (restrictToPositiveEdges
          (crossingSmoothingTranspose L n k ν₂ : Edge L n k 0 → Matrices.ComplexMatrix2)) κ₀ := by
  classical
  have hL0 : 0 < L := by omega
  have e₀ : PairedFunctionSpace.linearOfValues (edgePairedSpace L n k 0)
      (edgePairedSpace L n k k) mT = m := by
    have hex : ∃ T : (edgePairedSpace L n k 0).complexSubmodule →ₗ[ℂ]
        (edgePairedSpace L n k k).complexSubmodule,
        ∀ f : (edgePairedSpace L n k 0).complexSubmodule, (T f).1 = mT f.1 := ⟨m, hm⟩
    have hs := Classical.epsilon_spec hex
    exact LinearMap.ext fun f => Subtype.ext ((hs f).trans (hm f).symm)
  obtain ⟨K, hg, ht⟩ : ∃ K : Fin 3 × Tower.PositiveEdge L n k k →
        Fin 3 × Tower.PositiveEdge L n k 0 → ℂ,
      (∀ f : Fin 3 × Tower.PositiveEdge L n k 0 → ℂ, applyKernel K f =
        toPauliCoeffs (restrictToPositiveEdges (mT ((edgePauliCoordinates L n k 0).ofCoeffs f)))) ∧
      (∀ f : Fin 3 × Tower.PositiveEdge L n k k → ℂ,
        applyKernel (swapKernel K) f = toPauliCoeffs (restrictToPositiveEdges
          (PairedFunctionSpace.transposeOfValues (edgePairedSpace L n k 0)
            (edgePairedSpace L n k k) mT ((edgePauliCoordinates L n k k).ofCoeffs f)))) :=
    ⟨PauliComponentsOfSymmetricKernel.kernel (edgePauliCoordinates L n k 0) (edgePauliCoordinates L n k k) mT,
      fun f => (H.represents f).2, fun f => (H.swap_represents f).2⟩
  have tv : applyKernel (swapKernel K) (toPauliCoeffs (restrictToPositiveEdges X.1)) =
      toPauliCoeffs (restrictToPositiveEdges (PairedFunctionSpace.transposeMap m X).1) := by
    have e₁ : PairedFunctionSpace.transposeOfValues (edgePairedSpace L n k 0)
        (edgePairedSpace L n k k) mT X.1 =
        (PairedFunctionSpace.transposeMap (PairedFunctionSpace.linearOfValues
          (edgePairedSpace L n k 0) (edgePairedSpace L n k k) mT) X).1 := dif_pos X.2
    have e₂ : (edgePauliCoordinates L n k k).ofCoeffs (toPauliCoeffs (restrictToPositiveEdges X.1)) = X.1 :=
      ofCoeffs_coeffs X.2
    have e₃ : PairedFunctionSpace.transposeOfValues (edgePairedSpace L n k 0)
        (edgePairedSpace L n k k) mT
        ((edgePauliCoordinates L n k k).ofCoeffs (toPauliCoeffs (restrictToPositiveEdges X.1))) =
        (PairedFunctionSpace.transposeMap m X).1 :=
      (congrArg (PairedFunctionSpace.transposeOfValues (edgePairedSpace L n k 0)
        (edgePairedSpace L n k k) mT) e₂).trans (e₁.trans (by rw [e₀]))
    exact (ht _).trans (congrArg (fun Z => toPauliCoeffs (restrictToPositiveEdges Z)) e₃)
  have hδ := indicatorForm_mem hL hnk (Nat.zero_le k) κ₀
  set D : edgeFormSpace L n k 0 := ⟨indicatorForm κ₀, hδ⟩ with hD
  have col : ∀ κ', K κ' κ₀ = toPauliCoeffs (restrictToPositiveEdges
      (crossingSmoothingToTop L n k D : Edge L n k k → Matrices.ComplexMatrix2)) κ' := by
    intro κ'
    have g := congrFun (hg (indicatorCoeffs κ₀)) κ'
    have g₁ : applyKernel K (indicatorCoeffs κ₀) κ' = K κ' κ₀ := by
      show ∑' κ, K κ' κ * indicatorCoeffs κ₀ κ = _
      rw [tsum_eq_single κ₀ fun κ h => by simp [indicatorCoeffs, h]]
      simp [indicatorCoeffs]
    rw [← g₁, g, hMaps.crossing_eq D]
    show toPauliCoeffs (restrictToPositiveEdges (mT (indicatorForm κ₀))) κ' = _
    rw [hQ _ hδ]
  have hc : ∀ ν : edgeFormSpace L n k k, ν.1 ∈ complexEdgeForms L n k k := fun ν =>
    ⟨fun b hb => (ν.2.1 b hb).2, ν.2.2⟩
  have hc₀ : ∀ ν : edgeFormSpace L n k 0, ν.1 ∈ complexEdgeForms L n k 0 := fun ν =>
    ⟨fun b hb => (ν.2.1 b hb).2, ν.2.2⟩
  have hpair : ∀ ν : edgeFormSpace L n k k,
      ∑' κ', toPauliCoeffs (restrictToPositiveEdges
          (ν : Edge L n k k → Matrices.ComplexMatrix2)) κ' * K κ' κ₀ =
        toPauliCoeffs (restrictToPositiveEdges
          (crossingSmoothingTranspose L n k ν : Edge L n k 0 → Matrices.ComplexMatrix2)) κ₀ := by
    intro ν
    have h₁ := hMaps.crossing_transpose ν D
    rw [edgeFormPairing_eq_tsum hL0 hP (hc₀ _) (hc₀ D),
      edgeFormPairing_eq_tsum hL0 hP (hc ν) (hc _)] at h₁
    have h₂ : toPauliCoeffs (restrictToPositiveEdges (D : Edge L n k 0 → Matrices.ComplexMatrix2)) =
        indicatorCoeffs κ₀ :=
      coeffs_indicatorForm κ₀
    rw [h₂, tsum_eq_single κ₀ fun κ h => by simp [indicatorCoeffs, h]] at h₁
    simp only [indicatorCoeffs, if_true, mul_one] at h₁
    rw [h₁]
    exact tsum_congr fun κ' => by rw [col κ']
  have := finite_positiveEdge (n := n) (k := k) (j := k) hL0
  let _ := Fintype.ofFinite (Tower.PositiveEdge L n k k)
  rw [← tv, ← hpair ν₁, ← hpair ν₂]
  show ∑' κ', K κ' κ₀ * toPauliCoeffs (restrictToPositiveEdges X.1) κ' = _
  simp only [tsum_fintype, Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun κ' _ => ?_
  have e : toPauliCoeffs (restrictToPositiveEdges X.1) κ' =
      toPauliCoeffs (restrictToPositiveEdges (ν₁ : Edge L n k k → Matrices.ComplexMatrix2)) κ' +
        Complex.I * toPauliCoeffs (restrictToPositiveEdges
          (ν₂ : Edge L n k k → Matrices.ComplexMatrix2)) κ' := by
    rw [hX]
    exact coeffs_add_smul ν₁ ν₂ Complex.I κ'.2 κ'.1
  rw [e]
  ring
end BlockEvaluations
section Current
open LocalKernels.Periodisation
open PeriodicOperators (KernelMatrix)
variable {L n k : ℕ}
theorem full_hermitianPart_mem {a : ℝ} {G : InfiniteLattice.Link a → Matrices.ComplexMatrix2}
    (hG : G ∈ FullSpace.complexEdgeForms a) :
    (fun b => (2⁻¹ : ℂ) • (G b + (G b).conjTranspose)) ∈ FullSpace.edgeFormSpace a := by
  refine ⟨fun b hb => hermitianPart_mem (hG.1 b hb), fun b => ?_⟩
  simp only [hG.2 b, Matrix.conjTranspose_neg, ← neg_add, smul_neg]
theorem full_skewPart_mem {a : ℝ} {G : InfiniteLattice.Link a → Matrices.ComplexMatrix2}
    (hG : G ∈ FullSpace.complexEdgeForms a) :
    (fun b => (2 * Complex.I)⁻¹ • (G b - (G b).conjTranspose)) ∈ FullSpace.edgeFormSpace a := by
  refine ⟨fun b hb => skewPart_mem (hG.1 b hb), fun b => ?_⟩
  simp only [hG.2 b, Matrix.conjTranspose_neg, sub_neg_eq_add, ← smul_neg, neg_sub, neg_add_eq_sub]
theorem full_crossingSmoothingTranspose_eq (hbr : PairBracketTranspose (k := k) L)
    (hS : FullSpace.CrossingSmoothingComplexProps L k)
    (hAt : FullSpace.TrivialFieldAverages.IterateIdentities L k k)
    {T : KernelMatrix (Idx L (edgesAtZero k).colourPairs)
      (Idx L (CellClass.edgeClass k k le_rfl).colourPairs)}
    (hloc : IsRLocal L (edgesAtZero k).colourPairs (CellClass.edgeClass k k le_rfl).colourPairs 6 T)
    (hgiven : IsRepresentedOnPairs L (edgesAtZero k) (CellClass.edgeClass k k le_rfl)
      (fun f => FullSpace.iterCovariantDeriv L k (fun _ => 1) k f.1) T)
    {G : FullSpace.Edge L k k → Matrices.ComplexMatrix2}
    (hG : G ∈ FullSpace.complexEdgeForms (meshAt L k k))
    (ι' : (colourEdges L k 0).Carrier) :
    FullSpace.crossingSmoothingTranspose L k (toPauliCoeffs (FullSpace.restrictToPositiveEdges G)) ι' =
      applyKernel (kernelT L (edgesAtZero k).colourPairs
          (CellClass.edgeClass k k le_rfl).colourPairs T)
        (CellClass.coeffsOn L (CellClass.edgeClass k k le_rfl) G) ⟨(), ι'⟩ := by
  classical
  obtain ⟨m₁, m₂, g₁, g₂, -, -, hm⟩ := (hbr (edgesAtZero k) (CellClass.edgeClass k k le_rfl)
    (by simp [CellClass.edgeClass]) (by simp [CellClass.edgeClass])).2 6 (by norm_num) T hloc
  have hread : ∀ {P Q : FullSpace.Edge L k k → Matrices.ComplexMatrix2},
      P ∈ FullSpace.complexEdgeForms (meshAt L k k) →
      Q ∈ FullSpace.complexEdgeForms (meshAt L k k) →
      CellClass.coeffsOn L (CellClass.edgeClass k k le_rfl) P =
        CellClass.coeffsOn L (CellClass.edgeClass k k le_rfl) Q → P = Q := by
    intro P Q hP hQ e
    have e' : toPauliCoeffs (FullSpace.restrictToPositiveEdges P) =
        toPauliCoeffs (FullSpace.restrictToPositiveEdges Q) :=
      funext fun ι => congrFun e ⟨(), ι⟩
    rw [← full_ofCoeffs_coeffs hP, ← full_ofCoeffs_coeffs hQ]
    exact congrArg (FullSpace.edgePauliCoordinates L k k).ofCoeffs e'
  let sA : (CellClass.fullSpace L (edgesAtZero k)).complexSubmodule →ₗ[ℂ]
      (CellClass.fullSpace L (CellClass.edgeClass k k le_rfl)).complexSubmodule :=
    FullSpace.crossingSmoothingComplex L k
  have hv : ∀ f : (CellClass.fullSpace L (edgesAtZero k)).complexSubmodule,
      (sA f).1 = FullSpace.crossingSmoothingIter L k k f.1 := hS.values
  have hreal : ∀ (B : (CellClass.fullSpace L (edgesAtZero k)).complexSubmodule),
      B.1 ∈ FullSpace.edgeFormSpace (meshAt L k 0) → (m₁ B).1 = (sA B).1 := by
    intro B hB
    have a₁ := g₁ B
    have a₂ := hgiven B
    have e := hread a₁.1 a₂.1 (a₁.2.trans a₂.2.symm)
    exact e.trans ((hAt.1 B.1 hB).2.1.trans (hv B).symm)
  have hall : ∀ f : (CellClass.fullSpace L (edgesAtZero k)).complexSubmodule,
      (m₁ f).1 = (sA f).1 := by
    intro f
    have hf₁ := full_hermitianPart_mem (a := meshAt L k 0) f.2
    have hf₂ := full_skewPart_mem (a := meshAt L k 0) f.2
    let F₁ : (CellClass.fullSpace L (edgesAtZero k)).complexSubmodule :=
      ⟨_, ⟨fun b hb => (hf₁.1 b hb).2, hf₁.2⟩⟩
    let F₂ : (CellClass.fullSpace L (edgesAtZero k)).complexSubmodule :=
      ⟨_, ⟨fun b hb => (hf₂.1 b hb).2, hf₂.2⟩⟩
    have hf : f = F₁ + Complex.I • F₂ :=
      Subtype.ext (funext fun b => eq_hermitianPart_add_I_smul (f.1 b))
    rw [hf, map_add, map_add, map_smul, map_smul]
    show (m₁ F₁).1 + Complex.I • (m₁ F₂).1 = (sA F₁).1 + Complex.I • (sA F₂).1
    rw [hreal F₁ hf₁, hreal F₂ hf₂]
  have hS1 : m₁ = sA := LinearMap.ext fun f => Subtype.ext (hall f)
  have e₁ : PairedFunctionSpace.transposeOfValues (FullSpace.fineFormSpace L k)
      (FullSpace.coarseFormSpace L k) (FullSpace.crossingSmoothingIter L k k) G =
      (PairedFunctionSpace.transposeMap sA ⟨G, hG⟩).1 := dif_pos hG
  have e₃ : PairedFunctionSpace.transposeOfValues (FullSpace.fineFormSpace L k)
      (FullSpace.coarseFormSpace L k) (FullSpace.crossingSmoothingIter L k k)
        ((FullSpace.edgePauliCoordinates L k k).ofCoeffs
          (toPauliCoeffs (FullSpace.restrictToPositiveEdges G))) =
      (m₂ ⟨G, hG⟩).1 :=
    (congrArg (PairedFunctionSpace.transposeOfValues (FullSpace.fineFormSpace L k)
      (FullSpace.coarseFormSpace L k) (FullSpace.crossingSmoothingIter L k k))
        (full_ofCoeffs_coeffs hG)).trans (e₁.trans (by rw [hm, hS1]))
  have e₄ := congrFun (g₂ ⟨G, hG⟩).2 ⟨(), ι'⟩
  refine Eq.trans ?_ e₄
  exact congrFun (congrArg (fun Z => toPauliCoeffs (FullSpace.restrictToPositiveEdges Z)) e₃) ι'
theorem coeffs_crossingSmoothingTranspose (hL : 2 ≤ L) (hnk : k < n)
    (hst : Conventions.IsAdmissibleBlockingFactor L) (hk : 1 ≤ k) (hn : 0 < n)
    (hY : LocalKernels.Periodisation.PeriodisationHolds)
    (hA : TrivialFieldAverages.AtTrivialField)
    (hO : RescaledTrivialSteps)
    (hC : FullSpace.JointWidthAndTransposeTheorem)
    (hM : ResponseMaps.ResponseMapsHold)
    (hKer : ThreeMapKernels.Claim)
    (hP : OneLoop.PauliMatrixRelations)
    (ν₁ ν₂ : edgeFormSpace L n k k) (W : (colourEdges L k k).Carrier → ℂ)
    (hW : ∀ ι : (colourEdges L k k).Carrier,
      toPauliCoeffs (restrictToPositiveEdges (ν₁ : Edge L n k k → Matrices.ComplexMatrix2))
          (ι.1, projPositiveEdge L n k k ι.2) +
        Complex.I * toPauliCoeffs (restrictToPositiveEdges
          (ν₂ : Edge L n k k → Matrices.ComplexMatrix2))
          (ι.1, projPositiveEdge L n k k ι.2) = W ι)
    (ι' : (colourEdges L k 0).Carrier) :
    toPauliCoeffs (restrictToPositiveEdges
          (crossingSmoothingTranspose L n k ν₁ : Edge L n k 0 → Matrices.ComplexMatrix2))
        (ι'.1, projPositiveEdge L n k 0 ι'.2) +
      Complex.I * toPauliCoeffs (restrictToPositiveEdges
          (crossingSmoothingTranspose L n k ν₂ : Edge L n k 0 → Matrices.ComplexMatrix2))
        (ι'.1, projPositiveEdge L n k 0 ι'.2) =
      FullSpace.crossingSmoothingTranspose L k W ι' := by
  classical
  have hL0 : 0 < L := by omega
  have hk0 : 0 < k := hk
  obtain ⟨hcb, -, -, -, -, hbr, -, -, hav⟩ := hY L hst k n hn
  have hb := (hcb k le_rfl).2
  have hsmall := (hO L hst k hk n hn).1
  have hUc := hsmall.1
  obtain ⟨-, -, hit, -, -⟩ := ((hav hk) _ hUc).2 hsmall 0 (complexEdgeForms L n k k).zero_mem
  obtain ⟨T, m, hloc, hgiven, hval, -, M, hM₁, hM₂⟩ := (hit k le_rfl hk).2.1
  have hc : ∀ ν : edgeFormSpace L n k k, ν.1 ∈ complexEdgeForms L n k k := fun ν =>
    ⟨fun b hb => (ν.2.1 b hb).2, ν.2.2⟩
  let X : (edgePairedSpace L n k k).complexSubmodule :=
    ⟨(ν₁ : Edge L n k k → Matrices.ComplexMatrix2) +
        Complex.I • (ν₂ : Edge L n k k → Matrices.ComplexMatrix2),
      (complexEdgeForms L n k k).add_mem (hc ν₁) ((complexEdgeForms L n k k).smul_mem _ (hc ν₂))⟩
  let G : FullSpace.Edge L k k → Matrices.ComplexMatrix2 :=
    fun b => X.1 (FullSpace.projEdge L n k k b)
  have hG : G ∈ FullSpace.complexEdgeForms (meshAt L k k) := by
    refine ⟨fun b h => ?_, fun b => ?_⟩
    · have e := hb.2.1 ⟨b, h⟩
      show X.1 (FullSpace.projEdge L n k k b) ∈ _
      have e' : (projPositiveEdge L n k k ⟨b, h⟩).1 = FullSpace.projEdge L n k k b := e
      rw [← e']
      exact X.2.1 _ (projPositiveEdge L n k k ⟨b, h⟩).2
    · have e : FullSpace.projEdge L n k k b.opposite = (FullSpace.projEdge L n k k b).opposite :=
        PeriodicLattice.Bond.ext (((hb.1 b.opposite).1).trans ((hb.1 b).2).symm)
          (((hb.1 b.opposite).2).trans ((hb.1 b).1).symm)
      show X.1 _ = -X.1 _
      rw [e, X.2.2]
  have hpoint : ∀ ι : (colourEdges L k k).Carrier,
      toPauliCoeffs (FullSpace.restrictToPositiveEdges G) ι =
        toPauliCoeffs (restrictToPositiveEdges X.1) (ι.1, projPositiveEdge L n k k ι.2) := by
    intro ι
    have e : (projPositiveEdge L n k k ι.2).1 = FullSpace.projEdge L n k k ι.2.1 := hb.2.1 ι.2
    show pauliCoeff ι.1 (X.1 (FullSpace.projEdge L n k k ι.2.1)) =
      pauliCoeff ι.1 (X.1 (projPositiveEdge L n k k ι.2).1)
    rw [e]
  have hWG : toPauliCoeffs (FullSpace.restrictToPositiveEdges G) = W := by
    funext ι
    rw [hpoint ι, ← hW ι]
    exact coeffs_add_smul ν₁ ν₂ Complex.I _ _
  have hext : (CellClass.edgeClass k k le_rfl).colourPairs.lift L n
      (CellClass.quotCoeffsOn L n (CellClass.edgeClass k k le_rfl) X.1) =
      CellClass.coeffsOn L (CellClass.edgeClass k k le_rfl) G := by
    funext x
    exact (hpoint x.2).symm
  have hAtS := ((hA L hst).1 n k hn hk0).2.1 k le_rfl
  have hAtW := ((hA L hst).2 k hk0).2.1 k le_rfl
  have H := (((hKer L hst k hk).1 n hn).2.2.2 _ hsmall).1
  have hS := (hC L hL0 hst k hk).2.1
  have h₁ := coeffs_transposeMap hL hnk hP H (fun f hf => (hAtS.1 f hf).2.1)
    (hM L hst k n hk hn) m hval ν₁ ν₂ X rfl (ι'.1, projPositiveEdge L n k 0 ι'.2)
  have h₂ := full_crossingSmoothingTranspose_eq hbr hS hAtW hloc hgiven hG ι'
  have h₃ := congrFun
    (hM₂.2 (CellClass.quotCoeffsOn L n (CellClass.edgeClass k k le_rfl) X.1)) ⟨(), ι'⟩
  rw [hext, ← hM₁ X] at h₃
  rw [← hWG, h₂, h₃]
  exact h₁.symm
end Current
section Field
variable {L n k : ℕ}
theorem periodicField_ext (hL : 0 < L) (hc₀ : ProjCellsClassified L n k 0)
    (hc : ProjCellsClassified L n k k)
    {ζ ζ' : PeriodicField L n k} (h : ζ.pauliCoeffs hL = ζ'.pauliCoeffs hL) : ζ = ζ' :=
  Prod.ext (complexForm_ext_of_coeffs hc₀ fun ι => congrFun h ⟨.background, ι⟩)
    (Prod.ext (complexForm_ext_of_coeffs hc₀ fun ι => congrFun h ⟨.source, ι⟩)
      (complexForm_ext_of_coeffs hc fun ι => congrFun h ⟨.coarse, ι⟩))
theorem complexResponse_fourierModeForm (hR : ResponseOperators.Claim)
    (hS : ResponseSymbolNearStrip.ResponseSymbolHolomorphicNearStrip)
    (hF : PeriodicOperators.Symbols.Claim)
    (hId : PeriodicOperators.IdKernelFacts.Claim)
    (hP : PeriodicOperators.TowerIndexSets.Claim)
    (hT : PeriodicOperators.TowerTranslations.Claim)
    (hRel : TorusResponseRelations.statement)
    (hM : ResponseMaps.ResponseMapsHold)
    (hY : LocalKernels.Periodisation.PeriodisationHolds)
    (hA : TrivialFieldAverages.AtTrivialField)
    (hC : FullSpace.JointWidthAndTransposeTheorem)
    (hO : RescaledTrivialSteps)
    (hN : FreeStrip.ConstantsAdmissible.ConstantsAreAdmissible)
    (hKer : ThreeMapKernels.Claim)
    (hPa : OneLoop.PauliMatrixRelations)
    (hL : 0 < L) (hst : Conventions.IsAdmissibleBlockingFactor L) (hk : 1 ≤ k) (hn : 0 < n)
    (hnk : k < n)
    {p : AmbientSpace} (hp : p ∈ dualLattice (2 * L ^ n)) (a : Fin 3) (μ : Fin 4) :
    complexResponse L n k (PeriodicOperators.Tempered.fourierModeForm L n a p μ) =
      blochWaveField L n k hL (toComplexVec p)
        (FullSpace.responseSymbol L k hL (toComplexVec p) (FullSpace.axisPauliElement μ a)) := by
  classical
  have hL2 : 2 ≤ L := by
    have := hst.2
    omega
  obtain ⟨hcb, -⟩ := hY L hst k n hn
  have hc₀ := (hcb 0 (Nat.zero_le k)).1
  have hc := (hcb k le_rfl).1
  have hb := (hcb k le_rfl).2
  have hs : 0 < periodSide L n := by
    simp only [periodSide]
    positivity
  obtain ⟨δ₀, hδ₀, hS'⟩ := hS
  obtain ⟨O, -, hO', hOn⟩ := hS' L hL hst k hk
  obtain ⟨-, -, δ₁, hδ₁, C₀, -, hI, -, -⟩ := hN
  have e₀ : δ₀ = δ₁ := Part.mem_unique hδ₀ hδ₁
  have hκ : toComplexVec p ∈ O := hO' fun μ => by
    have : 0 < δ₀ := by
      rw [e₀]
      exact hI.1
    simp only [toComplexVec, Complex.ofReal_im, abs_zero]
    positivity
  obtain ⟨δ₂, -, hAt'⟩ := hR
  have hAt := hAt' L hst k hk
  have hi₀ := (hP L hst k 0 (Nat.zero_le k)).2.1
  have hik := (hP L hst k k le_rfl).2.1
  have hfinB := finite_positiveEdge (n := n) (k := k) (j := k) hL
  have hfin := finite_quotMod hc
  have hE := fourierModeForm_mem hL2 hn a p μ
  set E := PeriodicOperators.Tempered.fourierModeForm L n a p μ with hEdef
  set ε := FullSpace.axisPauliElement μ a with hε
  set R' := topForm L n k (realComponent E) with hR'
  set S' := topForm L n k (imagComponent E) with hS'def
  have mR : R' ∈ edgeFormSpace L n k k := topForm_mem (realComponent_mem hE)
  have mS : S' ∈ edgeFormSpace L n k k := topForm_mem (imagComponent_mem hE)
  have hεm : ResponseSymbolNearStrip.IsTracelessTuple ε := by
    intro ρ
    by_cases h : ρ = μ
    · subst h
      simpa [hε, FullSpace.axisPauliElement] using pauliFamily_mem_traceless a
    · simp [hε, FullSpace.axisPauliElement, Pi.single_eq_of_ne h]
  have hw : ∀ ι : (colourEdges L k k).Carrier,
      toPauliCoeffs (restrictToPositiveEdges R') (ι.1, projPositiveEdge L n k k ι.2) +
          Complex.I * toPauliCoeffs (restrictToPositiveEdges S')
            (ι.1, projPositiveEdge L n k k ι.2) =
        PeriodicOperators.blochWave (colourEdges L k k) (toComplexVec p)
          (FullSpace.constantFormAmplitude L k ε) ι := by
    intro ι
    have h := pauliCoeff_fourierModeForm hT hst hk hL hb hp a μ ι
    have hX := hE.1 _ (topEdgeEquivUnit_isPositivelyOriented (projPositiveEdge L n k k ι.2).2)
    refine Eq.trans ?_ h
    conv_rhs => rw [eq_hermitianPart_add_I_smul
      (PeriodicOperators.Tempered.fourierModeForm L n a p μ _)]
    rw [pauliCoeff_add_smul (hermitianPart_mem hX).2 (skewPart_mem hX).2]
    rfl
  have fR := hRel L hst k hk n hn ⟨R', mR⟩
  have fS := hRel L hst k hk n hn ⟨S', mS⟩
  have wb := image_coeffs_blochWave hF hId hik hi₀ hfin hs hAt.resp_periodic hp fR.image_response
    fS.image_response _ hw
  have wm := image_coeffs_blochWave hF hId hik hik hfin hs hAt.defect_periodic hp fR.image_defect
    fS.image_defect _ hw
  have wj := coeffs_crossingSmoothingTranspose hL2 hnk hst hk hn hY hA hO hC hM hKer hPa _ _ _ wm
  have hfr := complexify_realizes (responseField L n k R')
  have hfs := complexify_realizes (responseField L n k S')
  have e₁ : ((complexResponse L n k E).1 : Edge L n k 0 → Matrices.ComplexMatrix2) =
      (meshScaledResponse L n k R' : Edge L n k 0 → Matrices.ComplexMatrix2) +
        Complex.I • (meshScaledResponse L n k S' : Edge L n k 0 → Matrices.ComplexMatrix2) := by
    show ((complexify (responseField L n k R')).1 : Edge L n k 0 → Matrices.ComplexMatrix2) +
      Complex.I • ((complexify (responseField L n k S')).1 :
        Edge L n k 0 → Matrices.ComplexMatrix2) = _
    rw [hfr.1, hfs.1]
    rfl
  have e₂ : ((complexResponse L n k E).2.1 : Edge L n k 0 → Matrices.ComplexMatrix2) =
      (crossingSmoothingTranspose L n k (periodicDefect L n k R') :
          Edge L n k 0 → Matrices.ComplexMatrix2) +
        Complex.I • (crossingSmoothingTranspose L n k (periodicDefect L n k S') :
          Edge L n k 0 → Matrices.ComplexMatrix2) := by
    show ((complexify (responseField L n k R')).2.1 : Edge L n k 0 → Matrices.ComplexMatrix2) +
      Complex.I • ((complexify (responseField L n k S')).2.1 :
        Edge L n k 0 → Matrices.ComplexMatrix2) = _
    rw [hfr.2.1, hfs.2.1]
    rfl
  have e₃ : ((complexResponse L n k E).2.2 : Edge L n k k → Matrices.ComplexMatrix2) =
      (periodicDefect L n k R' : Edge L n k k → Matrices.ComplexMatrix2) +
        Complex.I • (periodicDefect L n k S' : Edge L n k k → Matrices.ComplexMatrix2) := by
    show ((complexify (responseField L n k R')).2.2 : Edge L n k k → Matrices.ComplexMatrix2) +
      Complex.I • ((complexify (responseField L n k S')).2.2 :
        Edge L n k k → Matrices.ComplexMatrix2) = _
    rw [hfr.2.2, hfs.2.2]
    rfl
  have key : (complexResponse L n k E).pauliCoeffs hL =
      PeriodicOperators.blochWave (FullSpace.fieldPeriodicData L k hL) (toComplexVec p)
        (FullSpace.responseSymbol L k hL (toComplexVec p) ε) := by
    funext x
    have hv : PeriodicOperators.blochWave (FullSpace.fieldPeriodicData L k hL) (toComplexVec p)
        (FullSpace.responseSymbol L k hL (toComplexVec p) ε) x =
        Complex.exp (Complex.I * bilinDot (toComplexVec p)
            (toComplexVec ((FullSpace.fieldPeriodicData L k hL).pos x))) *
          FullSpace.tripleIndexFunction L k hL
            (FullSpace.backgroundResponseSymbol L k (toComplexVec p) ε)
            (FullSpace.sourceResponseSymbol L k (toComplexVec p) ε)
            (FullSpace.coarseResponseSymbol L k (toComplexVec p) ε) x :=
      congrArg (fun z => Complex.exp (Complex.I * bilinDot (toComplexVec p)
        (toComplexVec ((FullSpace.fieldPeriodicData L k hL).pos x))) * z)
        (tripleAmplitude_mkQuot hL _ _ _ x)
    rw [hv]
    rcases x with ⟨pl, ι⟩
    cases pl
    · show (edgePauliCoordinates L n k 0).coeffs
          ((complexResponse L n k E).1 : Edge L n k 0 → Matrices.ComplexMatrix2)
        (ι.1, projPositiveEdge L n k 0 ι.2) =
        PeriodicOperators.blochWave (colourEdges L k 0) (toComplexVec p)
          (FullSpace.backgroundResponseSymbol L k (toComplexVec p) ε) ι
      rw [e₁, coeffs_add_smul, coeffs_meshScaledResponse, coeffs_meshScaledResponse, mul_left_comm,
        ← mul_add, wb ι, (hOn.background_wave _ hκ ε hεm).2]
      rfl
    · show (edgePauliCoordinates L n k 0).coeffs
          ((complexResponse L n k E).2.1 : Edge L n k 0 → Matrices.ComplexMatrix2)
        (ι.1, projPositiveEdge L n k 0 ι.2) =
        PeriodicOperators.blochWave (colourEdges L k 0) (toComplexVec p)
          (FullSpace.sourceResponseSymbol L k (toComplexVec p) ε) ι
      rw [e₂, coeffs_add_smul, wj ι, hOn.source_wave _ hκ ε hεm]
      rfl
    · show (edgePauliCoordinates L n k k).coeffs
          ((complexResponse L n k E).2.2 : Edge L n k k → Matrices.ComplexMatrix2)
        (ι.1, projPositiveEdge L n k k ι.2) =
        PeriodicOperators.blochWave (colourEdges L k k) (toComplexVec p)
          (FullSpace.coarseResponseSymbol L k (toComplexVec p) ε) ι
      rw [e₃, coeffs_add_smul, wm ι, (hOn.coarse_wave _ hκ ε hεm).2]
      rfl
  have hex : ∃ ζ : PeriodicField L n k, ζ.pauliCoeffs hL =
      PeriodicOperators.blochWave (FullSpace.fieldPeriodicData L k hL) (toComplexVec p)
        (FullSpace.responseSymbol L k hL (toComplexVec p) ε) := ⟨_, key⟩
  exact periodicField_ext hL hc₀ hc (key.trans (Classical.epsilon_spec hex).symm)
end Field
theorem le_of_torusSide_le {L : ℕ} (hL : 2 ≤ L) {m n : ℕ}
    (h : PeriodicLattice.torusSide L m ≤ PeriodicLattice.torusSide L n) :
    m ≤ n := by
  have h1 : (1 : ℝ) < L := by exact_mod_cast (by omega : 1 < L)
  simp only [PeriodicLattice.torusSide] at h
  rw [mul_le_mul_iff_right₀ (by norm_num : (0 : ℝ) < 2)] at h
  exact (pow_le_pow_iff_right₀ h1).1 h
theorem claim_holds (hR : ResponseOperators.Claim)
    (hS : ResponseSymbolNearStrip.ResponseSymbolHolomorphicNearStrip)
    (hF : PeriodicOperators.Symbols.Claim)
    (hId : PeriodicOperators.IdKernelFacts.Claim)
    (hP : PeriodicOperators.TowerIndexSets.Claim)
    (hT : PeriodicOperators.TowerTranslations.Claim)
    (hRel : TorusResponseRelations.statement)
    (hM : ResponseMaps.ResponseMapsHold)
    (hY : LocalKernels.Periodisation.PeriodisationHolds)
    (hA : TrivialFieldAverages.AtTrivialField)
    (hC : FullSpace.JointWidthAndTransposeTheorem)
    (hO : RescaledTrivialSteps)
    (hN : FreeStrip.ConstantsAdmissible.ConstantsAreAdmissible)
    (hKer : ThreeMapKernels.Claim)
    (hPa : OneLoop.PauliMatrixRelations) :
    Claim := by
  intro L hL hst k hk
  have hL2 : 2 ≤ L := by
    have := hst.2
    omega
  refine ⟨PeriodicLattice.torusSide L (k + 1), ⟨k + 1, by omega, rfl⟩, ?_⟩
  rintro s - hs n hn rfl p hp a μ
  exact complexResponse_fourierModeForm hR hS hF hId hP hT hRel hM hY hA hC hO hN hKer hPa hL hst hk
    hn (le_of_torusSide_le hL2 hs) hp a μ
end YangMills.Construction.Tower.ResponseOfFourierMode
end
