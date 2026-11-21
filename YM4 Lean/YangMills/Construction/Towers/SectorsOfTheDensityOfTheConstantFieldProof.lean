import YangMills.Construction.Towers.CovariantShiftsOfAnAbelianFieldProof
import YangMills.Construction.Towers.GaugeRelationOfTheChargedSymbolProof
import YangMills.Construction.Towers.LogarithmsOfTheAbelianOperatorsProof
import YangMills.Construction.Towers.LogarithmsSectorsAndTheDensity
import YangMills.Construction.Towers.NeutralFormsInTheConstantField
import YangMills.Construction.Towers.ProductOfTheBlockAverageWithItsTransposeOnTheSidesProof
import YangMills.Construction.Towers.SectorsOfTheDensityOfTheConstantField
import YangMills.Construction.Towers.TheAbelianOperatorsAreShiftedPositiveProof
import Mathlib
set_option autoImplicit false
open YangMills.Construction.OperatorCalculus YangMills.Construction.Tower.UnitLatticeL2
open YangMills.Construction.Tower.UnitaryCombinations
open YangMills.Construction.InfiniteLattice (AmbientSpace)
open YangMills.Construction.PeriodicOperators (toComplexVec castVec bilinDot)
open YangMills.Construction.Matrices (ComplexMatrix2)
noncomputable section
namespace YangMills.Construction.Tower.ConstantFieldSymbols
open MagneticWeyl AbelianFieldDensity AbelianFieldDensity.SectorDecomposition Massive
open AbelianFieldFacts (CovariantShifts covShift covShiftSubOne covShiftAdjSubOne
  raisingVertexFn IsRaisingFormOf cartanPhase)
open UnitGaugeDirections (CovDiffAndAdjoint unitVertexSpace unitEdgeSpace)
namespace DensitySectors
section QuantizedOperators
variable {L : ℕ} {N' : ℕ} [NeZero N']
theorem sum_covShift_eq_weylQuant (hS : WeylQuantHasSum)
    (hC : FourierCoeffsOfSymbol)
    (hU : UnitaryOperatorSeriesClaim)
    (hR : MagneticWeylRelations) {φ : ℝ}
    (hF : CovariantShifts (halfFluxAngle L φ)) (w : ScalarL2 L) :
    ∑ μ, covShiftAdjSubOne (halfFluxAngle L φ) μ (covShiftSubOne (halfFluxAngle L φ) μ w) =
      weylQuant L φ scalarMultiplier w := by apply _root_.YangMills.Construction.Tower.ConstantFieldSymbols.GaugeRelation.sum_covShiftAdj_eq_weylQuant_scalarMultiplier <;> assumption
end QuantizedOperators
section PauliMatrices
theorem conjugateBy_cartanPhase (t : ℝ) (M : ComplexMatrix2) :
    ComplexMatrix2.conjugateBy (cartanPhase t) M =
    !![M 0 0, Complex.exp (2 * Complex.I * t) * M 0 1;
      Complex.exp (-(2 * Complex.I * t)) * M 1 0, M 1 1] := by apply _root_.YangMills.Construction.Tower.AbelianShiftsProof.conjugateBy_cartanPhase <;> assumption
theorem conjugateBy_cartanPhase_smul_third (t : ℝ) (c : ℂ) :
    ComplexMatrix2.conjugateBy (cartanPhase t) (c • ComplexMatrix2.pauliFamily 2) =
      c • ComplexMatrix2.pauliFamily 2 := by
  rw [conjugateBy_cartanPhase, ComplexMatrix2.pauliFamily_apply.2.2]
  ext i j
  fin_cases i <;> fin_cases j <;> simp
theorem halfTrace_smul_third_mul (c : ℂ) (A : ComplexMatrix2) :
    ComplexMatrix2.halfTrace ((c • ComplexMatrix2.pauliFamily 2) * A) =
      1 / 2 * (c * (A 0 0 - A 1 1)) := by
  rw [ComplexMatrix2.pauliFamily_apply.2.2]
  show (1 / 2 : ℂ) * Matrix.trace _ = _
  rw [Matrix.trace_fin_two]
  simp only [Matrix.mul_apply, Fin.sum_univ_two]
  simp
  ring
theorem pauliThird_mem : ComplexMatrix2.pauliFamily 2 ∈ ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.Tower.MassiveOpFunctions.ThirdColourScaling.pauliFamily_two_mem_traceless <;> assumption
theorem eq_of_halfTrace_mul (Y Y' : ComplexMatrix2) (hY : Y ∈ ComplexMatrix2.traceless)
    (hY' : Y' ∈ ComplexMatrix2.traceless)
    (h : ∀ X ∈ ComplexMatrix2.traceless,
      ComplexMatrix2.halfTrace (Y * X) = ComplexMatrix2.halfTrace (Y' * X)) :
    Y = Y' := by apply _root_.YangMills.Construction.Tower.CubeAverageTranspose.eq_of_halfTrace_mul_eq <;> assumption
end PauliMatrices
section OrientedLinks
variable {L : ℕ}
theorem extendOddly_of_not_positive {a : ℝ} (f : InfiniteLattice.Link a → ComplexMatrix2)
    {b : InfiniteLattice.Link a} (hb : ¬b.IsPositivelyOriented) :
    FullSpace.extendOddly f b = -FullSpace.extendOddly f b.opposite := by apply _root_.YangMills.Construction.Tower.FullSpace.CovarianceProof.extendOddly_opposite <;> assumption
theorem eq_of_forwardFrom {a : ℝ} {B₁ B₂ : InfiniteLattice.Link a → ComplexMatrix2}
    (h₁ : ∀ b : InfiniteLattice.Link a, ¬b.IsPositivelyOriented → B₁ b = -B₁ b.opposite)
    (h₂ : ∀ b : InfiniteLattice.Link a, ¬b.IsPositivelyOriented → B₂ b = -B₂ b.opposite)
    (h : ∀ (x : InfiniteLattice.LatticePoint a) (μ : Fin 4),
      B₁ (InfiniteLattice.Link.forwardFrom x μ) = B₂ (InfiniteLattice.Link.forwardFrom x μ)) :
    B₁ = B₂ := by apply _root_.YangMills.Construction.Tower.ConstantFieldSymbols.GaugeRelation.eq_of_forwardFrom <;> assumption
theorem extendOddly_of_positive {a : ℝ} (f : InfiniteLattice.Link a → ComplexMatrix2)
    {b : InfiniteLattice.Link a} (h : b.IsPositivelyOriented) : FullSpace.extendOddly f b = f b := by apply _root_.YangMills.Construction.Tower.FullSpace.Translations.extendOddly_of_pos <;> assumption
theorem extendOddly_congr {a : ℝ} {f g : InfiniteLattice.Link a → ComplexMatrix2}
    (h : ∀ b : InfiniteLattice.Link a, b.IsPositivelyOriented → f b = g b) :
    FullSpace.extendOddly f = FullSpace.extendOddly g := by apply _root_.YangMills.Construction.Tower.FullSpace.Translations.extendOddly_congr <;> assumption
variable (θ : FullSpace.PositiveEdge (meshAt L 0 0) → ℝ)
theorem abelianLinkField_positive (b : FullSpace.PositiveEdge (meshAt L 0 0)) :
    FullSpace.abelianLinkField θ b.1 = cartanPhase (θ b) :=
  dif_pos b.2
theorem abelianLinkField_mem_complex :
    FullSpace.abelianLinkField θ ∈
      FullSpace.fieldsValuedIn L 0 0 PeriodicLattice.complexGaugeGroup := by apply _root_.YangMills.Construction.Tower.AbelianShiftsProof.abelianLinkField_mem_fieldsValuedIn <;> assumption
end OrientedLinks
theorem ofCoords_injective {σ : Type} (hC : CoordsIsometry σ)
    {f g : L2Field σ}
    (h : ofCoords f = ofCoords g) : f = g := by apply _root_.YangMills.Construction.Tower.AbelianFieldDensity.SectorDecomposition.AbelianOperatorLogarithmsProof.ofCoords_injective <;> assumption
section RaisingSector
variable {L : ℕ}
theorem laplacianOp_raising (hC : CoordsIsometry (FullSpace.Vertex L 0 0))
    {θ : FullSpace.PositiveEdge (meshAt L 0 0) → ℝ}
    (hO : AbelianFieldFacts.AbelianOperators θ) (hF : CovariantShifts θ)
    (hsite : ∀ (v : VectorL2 L 1) (x : FullSpace.Vertex L 0 0),
      ofCoords (vertexTensor v raisingPauli) x = v x 0 • raisingPauli)
    (w : ScalarL2 L) :
    laplacianOp θ (vertexTensor w raisingPauli) =
      vertexTensor (∑ ν, covShiftAdjSubOne θ ν (covShiftSubOne θ ν w)) raisingPauli := by
  obtain ⟨B, hB⟩ := hF.exists_raisingForm fun ν => covShiftSubOne θ ν w
  have hanti : ∀ b : FullSpace.Edge L 0 0, ¬b.IsPositivelyOriented → B b = -B b.opposite :=
    fun b _ => by rw [hB.1.2 b, neg_neg]
  have hBB : FullSpace.covDiff (FullSpace.abelianLinkField θ) (raisingVertexFn w) = B :=
    eq_of_forwardFrom (fun b hb => extendOddly_of_not_positive _ hb) hanti fun x μ => by
      rw [hF.covDiff_raising w x μ, hB.2 x μ]
  have hT : FullSpace.covDiffAdjoint (FullSpace.abelianLinkField θ) B =
      raisingVertexFn (∑ ν, covShiftAdjSubOne θ ν (covShiftSubOne θ ν w)) := by
    funext y
    rw [hF.covDiffAdjoint_raising _ B hB y]
    simp only [raisingVertexFn]
    rw [lp.coeFn_sum, Finset.sum_apply, WithLp.ofLp_sum, Finset.sum_apply]
  have hc : ∀ v : ScalarL2 L,
      ofCoords (vertexTensor v raisingPauli) = raisingVertexFn v :=
    fun v => funext fun x => hsite v x
  apply ofCoords_injective hC
  rw [hO.laplacian_apply, hc, hc]
  change FullSpace.covDiffAdjoint (FullSpace.abelianLinkField θ)
    (FullSpace.covDiff (FullSpace.abelianLinkField θ) (raisingVertexFn w)) = _
  rw [hBB, hT]
end RaisingSector
section NeutralSector
variable {L : ℕ}
open Classical in
def vertexIndicator (x : FullSpace.Vertex L 0 0) (X : ComplexMatrix2) :
    FullSpace.Vertex L 0 0 → ComplexMatrix2 :=
  fun y => if y = x then X else 0
theorem halfTrace_covDiffAdjoint {U : FullSpace.Edge L 0 0 → ComplexMatrix2}
    (hD : CovDiffAndAdjoint U) (B : FullSpace.Edge L 0 0 → ComplexMatrix2)
    (hB : B ∈ (unitEdgeSpace L).complexSubmodule) (x : FullSpace.Vertex L 0 0)
    (X : ComplexMatrix2) (hX : X ∈ ComplexMatrix2.traceless) :
    ComplexMatrix2.halfTrace (FullSpace.covDiffAdjoint U B x * X) =
      FullSpace.finiteEdgePairing B (FullSpace.covDiff U (vertexIndicator x X)) := by
  classical
  obtain ⟨-, hM, -, hT, hV⟩ := hD
  have hl : vertexIndicator x X ∈ (unitVertexSpace L).complexSubmodule := by
    intro y _
    by_cases hy : y = x
    · simpa [vertexIndicator, hy] using hX
    · simp [vertexIndicator, hy]
  have hfin : (unitVertexSpace L).IsFinitelySupported (vertexIndicator x X) := by
    refine (Set.finite_singleton x).subset fun y hy => ?_
    by_contra hn
    have hne : y ≠ x := hn
    exact hy (by simp [vertexIndicator, hne])
  have hp := hT ⟨B, hB⟩ ⟨vertexIndicator x X, hl⟩ hfin
  have e : traceFinsumPairing (FullSpace.covDiffAdjoint U B) (vertexIndicator x X) =
      FullSpace.finiteEdgePairing B (FullSpace.covDiff U (vertexIndicator x X)) := by
    have e₁ := hV ⟨B, hB⟩
    have e₂ := hM ⟨vertexIndicator x X, hl⟩
    simp only at e₁ e₂
    rw [e₁, ← e₂]
    exact hp
  have eL : traceFinsumPairing (FullSpace.covDiffAdjoint U B) (vertexIndicator x X) =
      ComplexMatrix2.halfTrace (FullSpace.covDiffAdjoint U B x * X) := by
    unfold traceFinsumPairing
    rw [finsum_eq_single _ x]
    · simp [vertexIndicator]
    · intro y hy
      simp [vertexIndicator, hy]
  rw [← eL, e]
theorem covDiff_diag_sub (θ : FullSpace.PositiveEdge (meshAt L 0 0) → ℝ)
    (l : FullSpace.Vertex L 0 0 → ComplexMatrix2) (b : FullSpace.PositiveEdge (meshAt L 0 0)) :
    FullSpace.covDiff (FullSpace.abelianLinkField θ) l b.1 0 0 -
        FullSpace.covDiff (FullSpace.abelianLinkField θ) l b.1 1 1 =
      (l b.1.terminal 0 0 - l b.1.initial 0 0) - (l b.1.terminal 1 1 - l b.1.initial 1 1) := by
  unfold FullSpace.covDiff
  rw [extendOddly_of_positive _ b.2, abelianLinkField_positive θ b, conjugateBy_cartanPhase]
  simp
theorem edgeFormPairing_neutral (θ θ' : FullSpace.PositiveEdge (meshAt L 0 0) → ℝ)
    (B : FullSpace.Edge L 0 0 → ComplexMatrix2)
    (c : FullSpace.PositiveEdge (meshAt L 0 0) → ℂ)
    (hB : ∀ b, B b.1 = c b • ComplexMatrix2.pauliFamily 2)
    (l : FullSpace.Vertex L 0 0 → ComplexMatrix2) :
    FullSpace.finiteEdgePairing B (FullSpace.covDiff (FullSpace.abelianLinkField θ) l) =
      FullSpace.finiteEdgePairing B (FullSpace.covDiff (FullSpace.abelianLinkField θ') l) := by
  unfold FullSpace.finiteEdgePairing traceFinsumPairing
  refine finsum_congr fun b => ?_
  show ComplexMatrix2.halfTrace (B b.1 * FullSpace.covDiff _ l b.1) =
    ComplexMatrix2.halfTrace (B b.1 * FullSpace.covDiff _ l b.1)
  rw [hB b, halfTrace_smul_third_mul, halfTrace_smul_third_mul, covDiff_diag_sub θ l b,
    covDiff_diag_sub θ' l b]
theorem conjugate_sub_neutral (θ : FullSpace.PositiveEdge (meshAt L 0 0) → ℝ)
    {l : FullSpace.Vertex L 0 0 → ComplexMatrix2} {c : FullSpace.Vertex L 0 0 → ℂ}
    (hl : ∀ x, l x = c x • ComplexMatrix2.pauliFamily 2)
    (b : FullSpace.PositiveEdge (meshAt L 0 0)) :
    ComplexMatrix2.conjugateBy (FullSpace.abelianLinkField θ b.1) (l b.1.terminal) -
        l b.1.initial =
      (c b.1.terminal - c b.1.initial) • ComplexMatrix2.pauliFamily 2 := by
  rw [abelianLinkField_positive θ b, hl, hl, conjugateBy_cartanPhase_smul_third, sub_smul]
theorem laplacianOp_neutral (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hG : UnitGaugeDirections.Claim)
    (hC : CoordsIsometry (FullSpace.Vertex L 0 0))
    {θ θ' : FullSpace.PositiveEdge (meshAt L 0 0) → ℝ}
    (hO : AbelianFieldFacts.AbelianOperators θ)
    (hO' : AbelianFieldFacts.AbelianOperators θ')
    (hsite : ∀ (v : VectorL2 L 1) (x : FullSpace.Vertex L 0 0),
      ofCoords (vertexTensor v (ComplexMatrix2.pauliFamily 2)) x =
        v x 0 • ComplexMatrix2.pauliFamily 2)
    (v : VectorL2 L 1) :
    laplacianOp θ (vertexTensor v (ComplexMatrix2.pauliFamily 2)) =
      laplacianOp θ' (vertexTensor v (ComplexMatrix2.pauliFamily 2)) := by
  apply ofCoords_injective hC
  rw [hO.laplacian_apply, hO'.laplacian_apply]
  obtain ⟨hD, -, hP, -⟩ := (hG L hL).2 _ (abelianLinkField_mem_complex θ)
  obtain ⟨hD', -, hP', -⟩ := (hG L hL).2 _ (abelianLinkField_mem_complex θ')
  set l := ofCoords (vertexTensor v (ComplexMatrix2.pauliFamily 2)) with hldef
  have hl : ∀ x, l x = (fun y : FullSpace.Vertex L 0 0 => v y 0) x • ComplexMatrix2.pauliFamily 2 :=
    hsite v
  have hlmem : l ∈ (unitVertexSpace L).complexSubmodule := by
    intro y _
    rw [hl]
    exact ComplexMatrix2.traceless.smul_mem _ pauliThird_mem
  have hDD : FullSpace.covDiff (FullSpace.abelianLinkField θ) l =
      FullSpace.covDiff (FullSpace.abelianLinkField θ') l := by
    refine extendOddly_congr fun b hb => ?_
    rw [conjugate_sub_neutral θ hl ⟨b, hb⟩, conjugate_sub_neutral θ' hl ⟨b, hb⟩]
  have hB := (hP'.1 l hlmem).1
  set B := FullSpace.covDiff (FullSpace.abelianLinkField θ') l with hBdef
  have hneutral : ∀ b : FullSpace.PositiveEdge (meshAt L 0 0), B b.1 =
      (v b.1.terminal 0 - v b.1.initial 0) • ComplexMatrix2.pauliFamily 2 := by
    intro b
    rw [hBdef]
    unfold FullSpace.covDiff
    rw [extendOddly_of_positive _ b.2]
    exact conjugate_sub_neutral θ' hl b
  change FullSpace.covDiffAdjoint (FullSpace.abelianLinkField θ)
      (FullSpace.covDiff (FullSpace.abelianLinkField θ) l) =
    FullSpace.covDiffAdjoint (FullSpace.abelianLinkField θ') B
  rw [hDD]
  funext x
  refine eq_of_halfTrace_mul _ _ ((hP.2 B hB).1 x (Set.mem_univ x))
    ((hP'.2 B hB).1 x (Set.mem_univ x)) fun X hX => ?_
  rw [halfTrace_covDiffAdjoint hD B hB x X hX, halfTrace_covDiffAdjoint hD' B hB x X hX]
  exact edgeFormPairing_neutral θ θ' B _ hneutral _
end NeutralSector
section BoundedOperators
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
theorem toBddOp_coe (A : H →L[ℂ] H) : toBddOp (⇑A) = A := by apply _root_.YangMills.Construction.Tower.AbelianFieldDensity.SectorDecomposition.AbelianOperatorLogarithmsProof.toBddOp_coe <;> assumption
theorem isBoundedBelowBy_addScalar {T : H →L[ℂ] H} {c s c' : ℝ} (h : IsBoundedBelowBy T c)
    (hc : c' ≤ c + s) : IsBoundedBelowBy (addScalar T s) c' := by apply _root_.YangMills.Construction.Tower.AbelianFieldDensity.ShiftedPositiveProof.isBoundedBelowBy_addScalar <;> assumption
end BoundedOperators
end DensitySectors
open DensitySectors in
theorem densitySectorDecomposition_holds
    (hFacts : AbelianFieldFacts.AllFacts)
    (hSec : AbelianFieldDensity.LogSectorsAndDensity)
    (hNeu : NeutralSectorOperator)
    (hSq : UnitLatticeL2Statement)
    (hGauge : UnitGaugeDirections.Claim)
    (hS : WeylQuantHasSum) (hC : FourierCoeffsOfSymbol)
    (hU : UnitaryOperatorSeriesClaim)
    (hR : MagneticWeylRelations) :
    densitySectorDecomposition := by
  intro L hL z hz
  obtain ⟨-, hsl, hsite, -, -, -, -, -, -, -, -, -, -, -, -, hAb, -, -⟩ := hSec.2 L hL z hz
  have hCoord : CoordsIsometry (FullSpace.Vertex L 0 0) := (hSq.2 L).2.1.1
  obtain ⟨-, -, hAll⟩ := hFacts
  obtain ⟨-, -, hAngles, hθ⟩ := hAll L hL z hz
  have hsiteR := hsite raisingPauli (hsl _ (Or.inr (Or.inl rfl)))
  have hsiteN := hsite (ComplexMatrix2.pauliFamily 2) (hsl _ (Or.inl rfl))
  have hForm : ∀ f : ℝ, |f| ≤ Real.pi / 2 → 24 * |Real.sin f| ≤ z / 2 →
      DensityDefined z (scaledLinearAngle L f) := by
    intro f hf hs
    obtain ⟨-, -, -, -, -, hLow, -⟩ := hθ (scaledLinearAngle L f)
    have hang : ∀ p : FullSpace.Face L 0 0,
        FullSpace.faceAngle (scaledLinearAngle L f) p =
          if p.lowAxis = 0 ∧ p.highAxis = 1 then f else 0 := fun p => hAngles f p
    have hK := hLow.1 fun p => by
      rw [hang]
      split_ifs
      · exact hf
      · rw [abs_zero]
        positivity
    have hsup : (⨆ p : FullSpace.Face L 0 0,
        |Real.sin (FullSpace.faceAngle (scaledLinearAngle L f) p)|) ≤ |Real.sin f| :=
      Real.iSup_le (fun p => by
        rw [hang]
        split_ifs
        · exact le_rfl
        · simp) (abs_nonneg _)
    exact isBoundedBelowBy_addScalar hK (by linarith)
  have hForm₀ : DensityDefined z (scaledLinearAngle L 0) :=
    hForm 0 (by simpa using by positivity) (by simpa using by positivity)
  obtain ⟨-, -, -, -, -, ⟨S₀, hS₀, -⟩, -⟩ := (hAb _ hForm₀).1
  obtain ⟨hO₀, -⟩ := hθ (scaledLinearAngle L 0)
  refine ⟨vecTraceAt (opLog (addScalar (toBddOp S₀.1) z)) 0,
    fun f hf hs => ?_⟩
  have hFormf := hForm f hf hs
  have hNeuf := hNeu L hL f hf
  have hMag : scaledLinearAngle L f = halfFluxAngle L (2 * f) := by
    funext b
    simp only [scaledLinearAngle, halfFluxAngle]
    ring
  rw [hMag] at hFormf hNeuf ⊢
  obtain ⟨hO, -, hSh, -⟩ := hθ (halfFluxAngle L (2 * f))
  obtain ⟨hLogS, hLogB⟩ := hAb _ hFormf
  obtain ⟨-, -, -, -, -, ⟨S, hSs, -⟩, hAllS⟩ := hLogS
  obtain ⟨-, -, -, -, -, ⟨S', hSb, -⟩, hAllB⟩ := hLogB
  have hSectors : IsSectorTriple (vertexTensor (L := L))
      (laplacianOp (halfFluxAngle L (2 * f)))
      S₀.1 (⇑(weylQuant L (2 * f) scalarMultiplier)) S.2.2 := by
    refine ⟨fun v => ?_, fun v => ?_, hSs.2.2⟩
    · rw [laplacianOp_neutral hL hGauge hCoord hO hO₀ hsiteN v]
      exact hS₀.1 v
    · rw [laplacianOp_raising hCoord hO hSh hsiteR v,
        sum_covShift_eq_weylQuant hS hC hU hR hSh v]
  obtain ⟨-, ⟨-, hψ⟩, -, -, -, -, hτ⟩ := hAllS _ _ _ hSectors
  rw [toBddOp_coe] at hψ
  refine ⟨hFormf, hψ.2, fun a ha => ?_⟩
  have hBonds : IsSectorTriple (edgeTensor (L := L))
      (AbelianFieldDensity.massiveOp (halfFluxAngle L (2 * f)))
      (⇑(weylQuant L 0 (neutralSectorSymbol f))) (⇑(weylQuant L (2 * f) a)) S'.2.2 :=
    ⟨hNeuf, ha, hSb.2.2⟩
  obtain ⟨-, ⟨-, ha'⟩, -, -, -, -, hτ'⟩ := hAllB _ _ _ hBonds
  rw [toBddOp_coe] at ha'
  refine ⟨ha'.2, ?_⟩
  obtain ⟨e₁, e₂⟩ := hτ 0
  obtain ⟨e₃, e₄⟩ := hτ' 0
  simp only [toBddOp_coe] at e₁ e₂ e₃ e₄
  unfold densityAt FluxSecondOrder.logTrace
  rw [e₁, e₃, e₂, e₄]
  ring
end YangMills.Construction.Tower.ConstantFieldSymbols
end
