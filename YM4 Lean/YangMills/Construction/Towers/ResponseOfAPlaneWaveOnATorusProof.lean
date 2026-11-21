import YangMills.Construction.Towers.CalculusOfPlaneWaves
import YangMills.Construction.Towers.CoefficientsOfTheResponseAtAColour
import YangMills.Construction.Towers.PlaneWavesUnderTheMapOfOneStepProof
import YangMills.Construction.Towers.PolarisationOfACompositionWithAStepProof
import YangMills.Construction.Towers.QuotientOfATowerCarriesSetsProof
import YangMills.Construction.Towers.RelationsOfTheResponseOnTheTorus
import YangMills.Construction.Towers.TheMassiveFamilyIsTemperedProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.PeriodicResponseOfFourierMode
open Tower
open Tower.PlaneWaves (edgeAt edgeFieldOfClasses shiftedFreq)
open Tower.PlaneWaveCalculus (posEdgeAt topEdgeComponent expWave)
open Tower.ResponseProperties (responseSymbolForm)
open Tower.BackgroundFieldResponse (responseKernel)
open Tower.CriticalBranchResponse (IsPeriodicImage)
open Tower.ResponseOperators (ClassFnEqForm)
open PeriodicOperators
open InfiniteLattice (AmbientSpace)
open LocalKernels LocalKernels.Periodisation
open PeriodicOperators.Tempered (UnitEdge topEdgeEquiv phase realComponent imagComponent)
open PeriodicOperators.Tempered.OneStep
open Matrices
theorem pauliFamily_mem_traceless (a : Fin 3) :
    ComplexMatrix2.pauliFamily a ∈ ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.OneLoopLaw.PlaneWaveSymmetries.pauliFamily_mem_traceless <;> assumption
theorem sum_pauliCoeff_smul {X : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.traceless) :
    ∑ a, pauliCoeff a X • ComplexMatrix2.pauliFamily a = X := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.sum_pauliCoeff_smul <;> assumption
theorem pauliCoeff_linear {X Y : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.traceless)
    (hY : Y ∈ ComplexMatrix2.traceless) (c d : ℂ) (a : Fin 3) :
    pauliCoeff a (c • X + d • Y) = c * pauliCoeff a X + d * pauliCoeff a Y := by apply _root_.YangMills.Construction.Tower.LeftChartAlgebra.FiniteFaceDerivatives.pauliCoeff_linearCombination <;> assumption
theorem pauliCoeff_pauliFamily (a' a : Fin 3) :
    pauliCoeff a' (ComplexMatrix2.pauliFamily a) = if a' = a then 1 else 0 := by apply _root_.YangMills.Construction.Tower.CrossingSmoothingContraction.pauliCoeff_pauliFamily <;> assumption
theorem pauliCoeff_smul {X : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.traceless) (c : ℂ)
    (a : Fin 3) :
    pauliCoeff a (c • X) = c * pauliCoeff a X := by apply _root_.YangMills.Construction.Tower.MassiveOpFunctions.Tempered.pauliCoeff_smul <;> assumption
section Parts
variable {L n : ℕ}
theorem realComponent_mem {B : UnitEdge L n → ComplexMatrix2}
    (hB : B ∈ complexEdgeForms L n 0 0) :
    realComponent B ∈ edgeFormSpace L n 0 0 := by apply _root_.YangMills.SharedProofs.p16359 <;> assumption
theorem imagComponent_mem {B : UnitEdge L n → ComplexMatrix2}
    (hB : B ∈ complexEdgeForms L n 0 0) :
    imagComponent B ∈ edgeFormSpace L n 0 0 := by apply _root_.YangMills.SharedProofs.p9724 <;> assumption
theorem eq_realComponent_add_imagComponent (B : UnitEdge L n → ComplexMatrix2) (b : UnitEdge L n) :
    B b = (1 : ℂ) • realComponent B b + Complex.I • imagComponent B b := by
  have hI : Complex.I * (2 * Complex.I)⁻¹ = (2⁻¹ : ℂ) := by
    field_simp
  simp only [realComponent, imagComponent, smul_smul, hI]
  ext i j
  simp
  ring
theorem cast_isPositivelyOriented {m : ℕ} {d d' : ℤ} (h : d = d')
    (b : PeriodicLattice.Bond L m d) :
    (Equiv.cast (congrArg (PeriodicLattice.Bond L m) h) b).IsPositivelyOriented ↔
      b.IsPositivelyOriented := by apply _root_.YangMills.Construction.Tower.HessianOfStepComposite.cast_isPositivelyOriented <;> assumption
theorem cast_opposite {m : ℕ} {d d' : ℤ} (h : d = d') (b : PeriodicLattice.Bond L m d) :
    Equiv.cast (congrArg (PeriodicLattice.Bond L m) h) b.opposite =
      (Equiv.cast (congrArg (PeriodicLattice.Bond L m) h) b).opposite := by apply _root_.YangMills.Construction.Tower.HessianOfStepComposite.cast_opposite <;> assumption
theorem levelDepth_self (k : ℕ) :
    PeriodicLattice.levelDepth k k = PeriodicLattice.levelDepth 0 0 := by
  simp [PeriodicLattice.levelDepth]
theorem topLevelForm_mem (k : ℕ) {A : UnitEdge L n → ComplexMatrix2}
    (hA : A ∈ edgeFormSpace L n 0 0) :
    topLevelForm L n k A ∈ edgeFormSpace L n k k :=
  ⟨fun b hb => hA.1 _ ((cast_isPositivelyOriented (levelDepth_self k) b).2 hb), fun b => by
    show A (Equiv.cast _ b.opposite) = -A (Equiv.cast _ b)
    rw [cast_opposite (levelDepth_self k)]
    exact hA.2 _⟩
end Parts
section Top
variable {L k : ℕ}
theorem castVec_mem (v : Fin 4 → ℤ) :
    castVec v ∈ InfiniteLattice.latticeSubgroup (meshAt L k k) :=
  ⟨v, fun μ => by simp [castVec, meshAt]⟩
theorem vertexImage_intShift (v : Fin 4 → ℤ) (x : FullSpace.Vertex L k k) :
    FullSpace.vertexImage (intShift v) x = x + ⟨castVec v, castVec_mem v⟩ :=
  Subtype.ext (Classical.epsilon_spec
    (p := fun x' : InfiniteLattice.LatticePoint (meshAt L k k) =>
      (x' : AmbientSpace) = intShift v x)
    ⟨x + ⟨castVec v, castVec_mem v⟩, rfl⟩)
theorem edgeImage_forwardFrom (v : Fin 4 → ℤ) (x : FullSpace.Vertex L k k) (μ : Fin 4) :
    FullSpace.edgeImage (intShift v) (InfiniteLattice.Link.forwardFrom x μ) =
      InfiniteLattice.Link.forwardFrom (FullSpace.vertexImage (intShift v) x) μ := by
  have hstep : FullSpace.vertexImage (intShift v) (x + InfiniteLattice.axisStep (meshAt L k k) μ) =
      FullSpace.vertexImage (intShift v) x + InfiniteLattice.axisStep (meshAt L k k) μ := by
    rw [vertexImage_intShift, vertexImage_intShift]
    abel
  have spec := Classical.epsilon_spec
    (p := fun b' : InfiniteLattice.Link (meshAt L k k) =>
      b'.initial = FullSpace.vertexImage (intShift v) (InfiniteLattice.Link.forwardFrom x μ).initial ∧
        b'.terminal =
          FullSpace.vertexImage (intShift v) (InfiniteLattice.Link.forwardFrom x μ).terminal)
    ⟨InfiniteLattice.Link.forwardFrom (FullSpace.vertexImage (intShift v) x) μ, rfl, hstep.symm⟩
  have spec' : (FullSpace.edgeImage (intShift v) (InfiniteLattice.Link.forwardFrom x μ)).initial =
        FullSpace.vertexImage (intShift v) x ∧
      (FullSpace.edgeImage (intShift v) (InfiniteLattice.Link.forwardFrom x μ)).terminal =
        FullSpace.vertexImage (intShift v) (x + InfiniteLattice.axisStep (meshAt L k k) μ) := spec
  exact InfiniteLattice.Link.ext spec'.1 (spec'.2.trans hstep)
theorem shiftEdge_eq_posEdgeAt (v : Fin 4 → ℤ) (b : PeriodicOperators.PosEdge L k k) (μ : Fin 4)
    (hb : b.1.terminal - b.1.initial = InfiniteLattice.axisStep (meshAt L k k) μ) :
    shiftEdge v b = posEdgeAt L k k (FullSpace.vertexImage (intShift v) b.1.initial) μ := by
  have hf : b.1 = InfiniteLattice.Link.forwardFrom b.1.initial μ :=
    InfiniteLattice.Link.ext rfl (by
      show b.1.terminal = b.1.initial + InfiniteLattice.axisStep (meshAt L k k) μ
      rw [← hb]
      abel)
  have hm : FullSpace.edgeImage (intShift v) b.1 =
      InfiniteLattice.Link.forwardFrom (FullSpace.vertexImage (intShift v) b.1.initial) μ :=
    (congrArg (FullSpace.edgeImage (intShift v)) hf).trans (edgeImage_forwardFrom v _ μ)
  have spec := Classical.epsilon_spec
    (p := fun b' : PeriodicOperators.PosEdge L k k =>
      b'.1 = FullSpace.edgeImage (intShift v) b.1)
    ⟨posEdgeAt L k k (FullSpace.vertexImage (intShift v) b.1.initial) μ, hm.symm⟩
  exact Subtype.ext (spec.trans hm)
def HasColourAndAxis (a : Fin 3) (μ : Fin 4) (ι : (colourEdges L k k).Carrier) : Prop :=
  ι.1 = a ∧ ι.2.1.terminal - ι.2.1.initial = InfiniteLattice.axisStep (meshAt L k k) μ
theorem posEdgeAt_sub (x : FullSpace.Vertex L k k) (ν : Fin 4) :
    (posEdgeAt L k k x ν).1.terminal - (posEdgeAt L k k x ν).1.initial =
      InfiniteLattice.axisStep (meshAt L k k) ν := by
  show x + InfiniteLattice.axisStep (meshAt L k k) ν - x = _
  abel
theorem hasColourAndAxis_translate (a : Fin 3) (μ : Fin 4) (v : Fin 4 → ℤ)
    (ι : (colourEdges L k k).Carrier) :
    HasColourAndAxis a μ ((colourEdges L k k).translate v ι) ↔ HasColourAndAxis a μ ι := by
  obtain ⟨a', b⟩ := ι
  obtain ⟨ν, hν⟩ := b.2
  have e : (colourEdges L k k).translate v (a', b) =
      (a', posEdgeAt L k k (FullSpace.vertexImage (intShift v) b.1.initial) ν) :=
    Prod.ext rfl (shiftEdge_eq_posEdgeAt v b ν hν)
  rw [e]
  unfold HasColourAndAxis
  simp only
  rw [posEdgeAt_sub, hν]
open Classical in
def unitAmplitude (L k : ℕ) (a : Fin 3) (μ : Fin 4) : (colourEdges L k k).UnitQuot → ℂ :=
  Quot.lift (fun ι => if HasColourAndAxis a μ ι then 1 else 0) (by
    rintro ι _ ⟨v, rfl⟩
    simp only [hasColourAndAxis_translate])
open Classical in
theorem unitAmplitude_mkQuot (a : Fin 3) (μ : Fin 4) (ι : (colourEdges L k k).Carrier) :
    unitAmplitude L k a μ ((colourEdges L k k).mkQuot 1 ι) =
      if HasColourAndAxis a μ ι then 1 else 0 :=
  rfl
theorem axisStep_injective {ν μ : Fin 4} (h : InfiniteLattice.axisStep (meshAt L k k) ν =
    InfiniteLattice.axisStep (meshAt L k k) μ) : ν = μ := by
  by_contra hne
  have h2 := congrFun (congrArg Subtype.val h) ν
  simp [InfiniteLattice.axisStep, meshAt, Pi.single_eq_of_ne hne] at h2
theorem topEdgeComponent_unitAmplitude (a : Fin 3) (μ ν : Fin 4) :
    topEdgeComponent L k (unitAmplitude L k a μ) ν =
      if ν = μ then ComplexMatrix2.pauliFamily a else 0 := by
  classical
  have hc : ∀ c : Fin 3, unitAmplitude L k a μ
      ((colourEdges L k k).mkQuot 1
        ((c, posEdgeAt L k k 0 ν) : (colourEdges L k k).Carrier)) =
        if c = a ∧ ν = μ then 1 else 0 := by
    intro c
    refine (unitAmplitude_mkQuot a μ
      ((c, posEdgeAt L k k 0 ν) : (colourEdges L k k).Carrier)).trans ?_
    have hiff : HasColourAndAxis a μ ((c, posEdgeAt L k k 0 ν) : (colourEdges L k k).Carrier) ↔
        c = a ∧ ν = μ := by
      unfold HasColourAndAxis
      simp only
      rw [posEdgeAt_sub]
      exact and_congr_right fun _ => ⟨axisStep_injective, fun h => by rw [h]⟩
    by_cases h : c = a ∧ ν = μ
    · rw [if_pos (hiff.2 h), if_pos h]
    · rw [if_neg (fun e => h (hiff.1 e)), if_neg h]
  show ∑ c, unitAmplitude L k a μ ((colourEdges L k k).mkQuot 1
    ((c, posEdgeAt L k k 0 ν) : (colourEdges L k k).Carrier)) • ComplexMatrix2.pauliFamily c = _
  simp only [hc]
  by_cases h : ν = μ
  · simp [h]
  · simp [h]
end Top
section Torus
variable {L n k : ℕ}
theorem projVertex_sub {j : ℕ} (x y : FullSpace.Vertex L k j) :
    FullSpace.projVertex L n k j (x - y) =
      FullSpace.projVertex L n k j x - FullSpace.projVertex L n k j y := by apply _root_.YangMills.Construction.Tower.EdgeProjection.projVertex_sub <;> assumption
theorem projVertex_add {j : ℕ} (x y : FullSpace.Vertex L k j) :
    FullSpace.projVertex L n k j (x + y) =
      FullSpace.projVertex L n k j x + FullSpace.projVertex L n k j y := by apply _root_.YangMills.Construction.Tower.FullSpace.ProjectionSets.projVertex_add <;> assumption
theorem projVertex_axisStep {j : ℕ} (μ : Fin 4) :
    FullSpace.projVertex L n k j (InfiniteLattice.axisStep (meshAt L k j) μ) =
      PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth k j) μ := by apply _root_.YangMills.Construction.Tower.EdgeProjection.projVertex_axisStep <;> assumption
theorem projPositiveEdge_sub {j : ℕ} (hb : ProjEdgesCompatible L n k j)
    (b : PeriodicOperators.PosEdge L k j) (ν : Fin 4)
    (hν : b.1.terminal - b.1.initial = InfiniteLattice.axisStep (meshAt L k j) ν) :
    (projPositiveEdge L n k j b).1.target - (projPositiveEdge L n k j b).1.source =
      PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth k j) ν := by
  rw [hb.2.1 b, (hb.1 b.1).2, (hb.1 b.1).1, ← projVertex_sub, hν, projVertex_axisStep]
theorem unitStep_ne {ν μ : Fin 4} (h : ν ≠ μ) :
    PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth 0 0) ν ≠
      PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth 0 0) μ := by apply _root_.YangMills.Construction.Tower.MassiveOpFunctions.Tempered.unitStep_ne <;> assumption
theorem phase_torusProj (hL : 0 < L) {p : AmbientSpace} (hp : p ∈ dualLattice (2 * L ^ n))
    (y : AmbientSpace) :
    phase (L := L) (n := n) p
        (fun μ => ((y μ : ℝ) : AddCircle (PeriodicLattice.torusSide L n))) =
      Complex.exp (Complex.I * bilinDot (toComplexVec p) (toComplexVec y)) := by apply _root_.YangMills.Construction.Tower.MassiveOpFunctions.Tempered.phase_coe <;> assumption
theorem fourierModeForm_cast {d : ℤ} (h : d = PeriodicLattice.levelDepth 0 0) (a : Fin 3)
    (μ : Fin 4) (p : AmbientSpace) (b : PeriodicLattice.Bond L n d) (ν : Fin 4)
    (hν : b.target - b.source = PeriodicLattice.unitStep L n d ν) :
    Tempered.fourierModeForm L n a p μ (Equiv.cast (congrArg (PeriodicLattice.Bond L n) h) b) =
      if ν = μ then phase p (b.source : PeriodicLattice.FourTorus L n) •
        ComplexMatrix2.pauliFamily a else 0 := by
  classical
  subst h
  show Tempered.fourierModeForm L n a p μ b = _
  have hpos : b.IsPositivelyOriented := ⟨ν, hν⟩
  simp only [Tempered.fourierModeForm, extendOddly, if_pos hpos]
  by_cases hνμ : ν = μ
  · subst hνμ
    rw [if_pos hν, if_pos rfl]
  · rw [if_neg hνμ, if_neg]
    intro e
    exact unitStep_ne hνμ (hν.symm.trans e)
theorem pauliCoeff_fourierModeForm (hL : 0 < L) (hb : ProjEdgesCompatible L n k k)
    {p : AmbientSpace} (hp : p ∈ dualLattice (2 * L ^ n)) (a : Fin 3) (μ : Fin 4)
    (κ : (colourEdges L k k).Carrier) :
    pauliCoeff κ.1 (Tempered.fourierModeForm L n a p μ
        (topEdgeEquiv L n k (projPositiveEdge L n k k κ.2).1)) =
      PeriodicOperators.blochWave (colourEdges L k k) (toComplexVec p) (unitAmplitude L k a μ) κ := by
  classical
  obtain ⟨ν, hν⟩ := κ.2.2
  have hd := projPositiveEdge_sub hb κ.2 ν hν
  have htail : ((projPositiveEdge L n k k κ.2).1.source : PeriodicLattice.FourTorus L n) =
      fun ρ => (((κ.2.1.initial : AmbientSpace) ρ : ℝ) : AddCircle (PeriodicLattice.torusSide L n)) := by
    rw [hb.2.1 κ.2, (hb.1 κ.2.1).1]
    rfl
  have hphase : phase p
      ((projPositiveEdge L n k k κ.2).1.source : PeriodicLattice.FourTorus L n) =
        Complex.exp (Complex.I *
          bilinDot (toComplexVec p) (toComplexVec (κ.2.1.initial : AmbientSpace))) := by
    rw [htail]
    exact phase_torusProj hL hp _
  have hval : Tempered.fourierModeForm L n a p μ
      (topEdgeEquiv L n k (projPositiveEdge L n k k κ.2).1) =
      if ν = μ then phase p
        ((projPositiveEdge L n k k κ.2).1.source : PeriodicLattice.FourTorus L n) •
          ComplexMatrix2.pauliFamily a else 0 :=
    fourierModeForm_cast (levelDepth_self k) a μ p _ ν hd
  show pauliCoeff κ.1 (Tempered.fourierModeForm L n a p μ
      (topEdgeEquiv L n k (projPositiveEdge L n k k κ.2).1)) =
    Complex.exp (Complex.I *
        bilinDot (toComplexVec p) (toComplexVec (κ.2.1.initial : AmbientSpace))) *
      unitAmplitude L k a μ ((colourEdges L k k).mkQuot 1 κ)
  rw [unitAmplitude_mkQuot, hval]
  by_cases h : ν = μ
  · subst h
    rw [if_pos rfl, pauliCoeff_smul (pauliFamily_mem_traceless a), pauliCoeff_pauliFamily, hphase]
    by_cases ha : κ.1 = a
    · have hC : HasColourAndAxis a ν κ := ⟨ha, hν⟩
      rw [if_pos ha, if_pos hC]
    · rw [if_neg ha, if_neg (fun hc : HasColourAndAxis a ν κ => ha hc.1)]
  · have hn : ¬ HasColourAndAxis a μ κ := by
      intro hc
      exact h (axisStep_injective (hν.symm.trans hc.2))
    have h0 := pauliCoeff_smul (ComplexMatrix2.traceless.zero_mem) 0 κ.1
    rw [if_neg h, if_neg hn, mul_zero]
    simpa using h0
theorem fourierModeForm_mem (hL : 2 ≤ L) (hn : 0 < n) (a : Fin 3) (p : AmbientSpace) (μ : Fin 4) :
    Tempered.fourierModeForm L n a p μ ∈ complexEdgeForms L n 0 0 := by apply _root_.YangMills.Construction.Tower.MassiveOpFunctions.Tempered.fourierModeForm_mem <;> assumption
theorem projPositiveEdge_edgeAt (hb : ProjEdgesCompatible L n k 0) (y : FullSpace.Vertex L k 0)
    (ρ : Fin 4) :
    (projPositiveEdge L n k 0 (edgeAt L k y ρ)).1 =
      PeriodicLattice.Bond.forwardFrom (FullSpace.projVertex L n k 0 y) ρ := by
  obtain ⟨ht, hh⟩ := hb.1 (edgeAt L k y ρ).1
  rw [hb.2.1 (edgeAt L k y ρ)]
  refine PeriodicLattice.Bond.ext ht ?_
  rw [hh]
  show FullSpace.projVertex L n k 0 (y + InfiniteLattice.axisStep (meshAt L k 0) ρ) =
    FullSpace.projVertex L n k 0 y + PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth k 0) ρ
  rw [projVertex_add, projVertex_axisStep]
theorem toComplexVec_shift (p : AmbientSpace) (m : Fin 4 → ℤ) :
    toComplexVec (fun ν => p ν + 2 * Real.pi * (m ν : ℝ)) =
      Tower.PlaneWaves.shiftedFreq (toComplexVec p) m := by apply _root_.YangMills.Construction.Tower.StepImageOfFourierModes.toComplexVec_shifted <;> assumption
end Torus
section Main
variable {L n : ℕ}
theorem periodicResponse_forwardFrom (hRel : Tower.TorusResponseRelations.statement)
    (hOps : Tower.ResponseOperators.Claim) (hSym : PeriodicOperators.Symbols.Claim)
    (hIdx : PeriodicOperators.TowerIndexSets.Claim)
    (hQuot : PeriodicOperators.Quotients.QuotientTransposeNorm)
    (hCells : LocalKernels.PeriodicLiftCells.CellsAndClassesHold)
    (hCalc : Tower.PlaneWaveCalculus.PlaneWaveCalculusHolds)
    (hCoef : Tower.ResponseCoefficients.ColourCoefficientClaim)
    (hDil : Tower.StepScalingOfFourierModes.Claim)
    (hst : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (i : ℕ) {p : AmbientSpace}
    (hp : p ∈ dualLattice (2 * L ^ n)) (a : Fin 3) (μ ρ : Fin 4) (x : Vertex L n (i + 1) 0) :
    complexPeriodicResponse L n i (Tempered.fourierModeForm L n a p μ)
        (PeriodicLattice.Bond.forwardFrom x ρ) =
      ∑ m ∈ Tower.PlaneWaves.freqBox L (i + 1),
        (phase (L := L) (n := n) (fun ν => p ν + 2 * Real.pi * (m ν : ℝ))
            (x : PeriodicLattice.FourTorus L n) *
          responseCoeff L (i + 1) (toComplexVec p) ρ μ m) • ComplexMatrix2.pauliFamily a := by
  classical
  have hL2 : 2 ≤ L := by have := hst.2; omega
  have hL0 : 0 < L := by omega
  have hk : 1 ≤ i + 1 := by omega
  have hs : 0 < periodSide L n := by
    unfold periodSide
    positivity
  obtain ⟨-, hI, -⟩ := hIdx L hst (i + 1) (i + 1) le_rfl
  obtain ⟨-, hI', -⟩ := hIdx L hst (i + 1) 0 (Nat.zero_le _)
  obtain ⟨δ₀, -, hall⟩ := hOps
  have hper : IsPeriodicKernel (colourEdges L (i + 1) (i + 1)) (colourEdges L (i + 1) 0)
      (responseKernel L (i + 1)) := (hall L hst (i + 1) hk).resp_periodic
  obtain ⟨C, δ, hC, hδ, hobey⟩ := hper.2
  have hzb : ExpDecay (colourEdges L (i + 1) (i + 1)) (colourEdges L (i + 1) (i + 1))
      (fun _ _ => 0) 1 δ := fun _ _ => by
    simp only [norm_zero]
    positivity
  have hF := hSym.1 (colourEdges L (i + 1) (i + 1)) (colourEdges L (i + 1) 0)
    (colourEdges L (i + 1) (i + 1)) hI hI' hI (responseKernel L (i + 1)) (fun _ _ => 0) δ
    hper ⟨hδ, C, hC, hobey⟩ ⟨fun _ _ _ => rfl, 1, δ, one_pos, hδ, hzb⟩ ⟨hδ, 1, one_pos, hzb⟩
  have hformed : SymbolSummableAt (colourEdges L (i + 1) (i + 1)) (colourEdges L (i + 1) 0)
      (responseKernel L (i + 1)) (toComplexVec p) := by
    refine hF.summable_on_strip _ ?_
    show TorusMetric.euclidNormVec (PeriodicOperators.imVec (toComplexVec p)) < δ
    have h0 : PeriodicOperators.imVec (toComplexVec p) = 0 := by
      funext ν
      simp [PeriodicOperators.imVec, toComplexVec]
    rw [h0]
    simpa [TorusMetric.euclidNormVec] using hδ
  obtain ⟨-, hfin, -⟩ := (hQuot (colourEdges L (i + 1) (i + 1)) (colourEdges L (i + 1) 0) hI hI'
    (periodSide L n) hs).1
  have hfin1 : Finite (colourEdges L (i + 1) (i + 1)).UnitQuot := hI.finite_quot
  have hcb := (hCells L hst (i + 1) n hn).1
  obtain ⟨-, hbT⟩ := hcb (i + 1) le_rfl
  obtain ⟨hc0, hb0⟩ := hcb 0 (Nat.zero_le _)
  set E := Tempered.fourierModeForm L n a p μ with hE
  have hEm : E ∈ complexEdgeForms L n 0 0 := fourierModeForm_mem hL2 hn a p μ
  have hRf := realComponent_mem hEm
  have hSf := imagComponent_mem hEm
  have hTR := topLevelForm_mem (i + 1) hRf
  have hTS := topLevelForm_mem (i + 1) hSf
  obtain ⟨gR, hgR, hgR'⟩ := (hRel L hst (i + 1) hk n hn ⟨_, hTR⟩).image_response
  obtain ⟨gS, hgS, hgS'⟩ := (hRel L hst (i + 1) hk n hn ⟨_, hTS⟩).image_response
  set z := unitAmplitude L (i + 1) a μ with hz
  let g : (colourEdges L (i + 1) (i + 1)).QuotMod (periodSide L n) → ℂ :=
    fun c => gR c + Complex.I * gS c
  have hg : ∀ ι, g ((colourEdges L (i + 1) (i + 1)).mkQuot (periodSide L n) ι) =
      PeriodicOperators.blochWave (colourEdges L (i + 1) (i + 1)) (toComplexVec p) z ι := by
    intro ι
    rw [← pauliCoeff_fourierModeForm hL0 hbT hp a μ ι]
    have hpos : (topEdgeEquiv L n (i + 1)
        (projPositiveEdge L n (i + 1) (i + 1) ι.2).1).IsPositivelyOriented :=
      (cast_isPositivelyOriented (levelDepth_self (i + 1)) _).2
        (projPositiveEdge L n (i + 1) (i + 1) ι.2).2
    have e := pauliCoeff_linear (hRf.1 _ hpos).2 (hSf.1 _ hpos).2 1 Complex.I ι.1
    rw [← eq_realComponent_add_imagComponent E, one_mul] at e
    rw [e]
    show gR _ + Complex.I * gS _ = _
    rw [hgR ι, hgS ι]
    rfl
  have hact := hF.periodicMatrix_blochWave (periodSide L n) hs p hp z g hg
  have hsplit : ∀ c', applyKernel (periodicMatrix (colourEdges L (i + 1) (i + 1))
      (colourEdges L (i + 1) 0) (responseKernel L (i + 1)) (periodSide L n)) g c' =
      applyKernel (periodicMatrix (colourEdges L (i + 1) (i + 1))
        (colourEdges L (i + 1) 0) (responseKernel L (i + 1)) (periodSide L n)) gR c' +
      Complex.I * applyKernel (periodicMatrix (colourEdges L (i + 1) (i + 1))
        (colourEdges L (i + 1) 0) (responseKernel L (i + 1)) (periodSide L n)) gS c' := by
    intro c'
    have := Fintype.ofFinite ((colourEdges L (i + 1) (i + 1)).QuotMod (periodSide L n))
    simp only [applyKernel, tsum_fintype, g, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun c _ => ?_
    ring
  have hform : responseSymbolForm L (i + 1) (toComplexVec p) z =
      applyKernel (quotSymbol (colourEdges L (i + 1) (i + 1)) (colourEdges L (i + 1) 0)
        (responseKernel L (i + 1)) (toComplexVec p)) z :=
    linearMapOfEntries_eq_applyKernel _ _
  obtain ⟨y, hy⟩ : ∃ y : FullSpace.Vertex L (i + 1) 0, FullSpace.projVertex L n (i + 1) 0 y = x :=
    (hc0 .vertex).1 x
  subst hy
  have hβ := projPositiveEdge_edgeAt hb0 y ρ
  set U : Edge L n (i + 1) 0 → ComplexMatrix2 := (CriticalBranchResponse.periodicResponse L n (i + 1)
    (topLevelForm L n (i + 1) (realComponent E)) : Edge L n (i + 1) 0 → ComplexMatrix2) with hU
  set V : Edge L n (i + 1) 0 → ComplexMatrix2 := (CriticalBranchResponse.periodicResponse L n (i + 1)
    (topLevelForm L n (i + 1) (imagComponent E)) : Edge L n (i + 1) 0 → ComplexMatrix2) with hV
  have hcoef : ∀ c : Fin 3, pauliCoeff c (U (projPositiveEdge L n (i + 1) 0
        (edgeAt L (i + 1) y ρ)).1) +
      Complex.I * pauliCoeff c (V (projPositiveEdge L n (i + 1) 0
        (edgeAt L (i + 1) y ρ)).1) =
      expWave (toComplexVec p) (y : AmbientSpace) *
        responseSymbolForm L (i + 1) (toComplexVec p) z
          ((colourEdges L (i + 1) 0).mkQuot 1
            ((c, edgeAt L (i + 1) y ρ) : (colourEdges L (i + 1) 0).Carrier)) := by
    intro c
    have h1 := hgR' ((c, edgeAt L (i + 1) y ρ) : (colourEdges L (i + 1) 0).Carrier)
    have h2 := hgS' ((c, edgeAt L (i + 1) y ρ) : (colourEdges L (i + 1) 0).Carrier)
    have h3 := hact ((c, edgeAt L (i + 1) y ρ) : (colourEdges L (i + 1) 0).Carrier)
    rw [hsplit, h1, h2] at h3
    rw [hform]
    exact h3
  have hposb : (projPositiveEdge L n (i + 1) 0 (edgeAt L (i + 1) y ρ)).1.IsPositivelyOriented :=
    (projPositiveEdge L n (i + 1) 0 (edgeAt L (i + 1) y ρ)).2
  have hUm : U (projPositiveEdge L n (i + 1) 0 (edgeAt L (i + 1) y ρ)).1 ∈
      ComplexMatrix2.traceless :=
    ((CriticalBranchResponse.periodicResponse L n (i + 1)
      (topLevelForm L n (i + 1) (realComponent E))).2.1 _ hposb).2
  have hVm : V (projPositiveEdge L n (i + 1) 0 (edgeAt L (i + 1) y ρ)).1 ∈
      ComplexMatrix2.traceless :=
    ((CriticalBranchResponse.periodicResponse L n (i + 1)
      (topLevelForm L n (i + 1) (imagComponent E))).2.1 _ hposb).2
  obtain ⟨-, -, hbonds, -⟩ := hCalc L hst (i + 1) hk
  have hexp := hbonds.exp_expansion (toComplexVec p)
    (responseSymbolForm L (i + 1) (toComplexVec p) z) ρ y
  have hval : complexPeriodicResponse L n i E
      (PeriodicLattice.Bond.forwardFrom (FullSpace.projVertex L n (i + 1) 0 y) ρ) =
      expWave (toComplexVec p) (y : AmbientSpace) • Tower.PlaneWaves.edgeFieldOfClasses L (i + 1)
        (responseSymbolForm L (i + 1) (toComplexVec p) z) (edgeAt L (i + 1) y ρ) := by
    rw [← hβ]
    show U _ + Complex.I • V _ = _
    have hX := ComplexMatrix2.traceless.add_mem (ComplexMatrix2.traceless.smul_mem (1 : ℂ) hUm)
      (ComplexMatrix2.traceless.smul_mem Complex.I hVm)
    rw [← one_smul ℂ (U _), ← sum_pauliCoeff_smul hX]
    show _ = expWave (toComplexVec p) (y : AmbientSpace) •
      ∑ c, responseSymbolForm L (i + 1) (toComplexVec p) z
        ((colourEdges L (i + 1) 0).mkQuot 1
          ((c, edgeAt L (i + 1) y ρ) : (colourEdges L (i + 1) 0).Carrier)) •
            ComplexMatrix2.pauliFamily c
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [pauliCoeff_linear hUm hVm, one_mul, hcoef c, smul_smul]
  rw [hval, hexp]
  refine Finset.sum_congr rfl fun m _ => ?_
  have hmom := (hDil L hL0 hst n i hn).2.2.1 p hp m
  have hc := hCoef L hst (i + 1) hk (toComplexVec p) ρ μ m a z hformed
    (fun ν => topEdgeComponent_unitAmplitude a μ ν)
  rw [hc, smul_smul]
  congr 1
  congr 1
  have h2 := phase_torusProj hL0 hmom (y : AmbientSpace)
  rw [toComplexVec_shift] at h2
  exact h2.symm
end Main
theorem claim_holds (hRel : Tower.TorusResponseRelations.statement)
    (hOps : Tower.ResponseOperators.Claim) (hSym : PeriodicOperators.Symbols.Claim)
    (hIdx : PeriodicOperators.TowerIndexSets.Claim)
    (hQuot : PeriodicOperators.Quotients.QuotientTransposeNorm)
    (hCells : LocalKernels.PeriodicLiftCells.CellsAndClassesHold)
    (hCalc : Tower.PlaneWaveCalculus.PlaneWaveCalculusHolds)
    (hCoef : Tower.ResponseCoefficients.ColourCoefficientClaim)
    (hDil : Tower.StepScalingOfFourierModes.Claim) : Claim := by
  intro L hst i
  refine ⟨PeriodicLattice.torusSide L 1, ⟨1, one_pos, rfl⟩, ?_⟩
  rintro s - - n hn - p hp a μ ρ x
  exact periodicResponse_forwardFrom hRel hOps hSym hIdx hQuot hCells hCalc hCoef hDil hst hn i hp
    a μ ρ x
end YangMills.Construction.Tower.PeriodicResponseOfFourierMode
end
