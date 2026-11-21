import YangMills.Construction.Towers.MassiveOperatorOnGaugeDirectionsOfTheConstantField
import YangMills.Construction.Towers.PlaquetteAnglesOfTheLinearAbelianField
import YangMills.Construction.Towers.QuadraticFormsAndTransposesOnTheRealSpacesProof
import YangMills.Construction.Towers.RelationsOfOneCovariantStepAtTheSideInfinityProof
import YangMills.Construction.Towers.SecondDerivativeInAGaugeDirectionAtTheSideInfinity
import YangMills.Construction.Towers.SymmetriesOfTheAbelianOperatorsProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.ConstantFieldSymbols.GaugeDirectionHessian
open YangMills.Construction.Matrices
open AbelianFieldFacts (ActionDerivative LinearFieldAngles)
open HessianKernel (finiteSupportComplexForms)
open UnitGaugeDirections (unitVertexSpace covDiffLinear CovDiffAndAdjoint)
section TracelessMatrices
theorem mem_traceless_iff {X : ComplexMatrix2} :
    X ∈ ComplexMatrix2.traceless ↔ Matrix.trace X = 0 := Iff.rfl
theorem traceless_ext {Z W : ComplexMatrix2} (hZ : Z ∈ ComplexMatrix2.traceless)
    (hW : W ∈ ComplexMatrix2.traceless)
    (h : ∀ i, ComplexMatrix2.halfTrace (ComplexMatrix2.pauliFamily i * Z) =
      ComplexMatrix2.halfTrace (ComplexMatrix2.pauliFamily i * W)) : Z = W := by apply _root_.YangMills.Construction.Tower.AbelianSymmetryProof.traceless_ext_of_halfTrace <;> assumption
def hermPart (X : ComplexMatrix2) : ComplexMatrix2 := (1 / 2 : ℂ) • (X + X.conjTranspose)
def antiHermPart (X : ComplexMatrix2) : ComplexMatrix2 :=
  (-(Complex.I / 2)) • (X - X.conjTranspose)
theorem hermPart_add_I_smul (X : ComplexMatrix2) :
    hermPart X + Complex.I • antiHermPart X = X := by
  ext r s
  simp only [hermPart, antiHermPart, Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply,
    smul_eq_mul]
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  linear_combination (-(1 / 2 : ℂ) * (X r s - X.conjTranspose r s)) * hI
theorem trace_conjTranspose_eq_zero_of_traceless {X : ComplexMatrix2}
    (hX : X ∈ ComplexMatrix2.traceless) : Matrix.trace X.conjTranspose = 0 := by apply _root_.YangMills.Construction.Tower.FullSpace.StepRelations.trace_conjTranspose_eq_zero <;> assumption
theorem hermPart_mem {X : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.traceless) :
    hermPart X ∈ ComplexMatrix2.hermitianTraceless := by
  refine ⟨?_, ?_⟩
  · ext r s
    simp [hermPart, add_comm]
    ring
  · show Matrix.trace (hermPart X) = 0
    rw [hermPart, Matrix.trace_smul, Matrix.trace_add, mem_traceless_iff.mp hX,
      trace_conjTranspose_eq_zero_of_traceless hX]
    simp
theorem antiHermPart_mem {X : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.traceless) :
    antiHermPart X ∈ ComplexMatrix2.hermitianTraceless := by
  refine ⟨?_, ?_⟩
  · ext r s
    simp [antiHermPart]
    ring
  · show Matrix.trace (antiHermPart X) = 0
    rw [antiHermPart, Matrix.trace_smul, Matrix.trace_sub, mem_traceless_iff.mp hX,
      trace_conjTranspose_eq_zero_of_traceless hX]
    simp
theorem hermPart_zero : hermPart 0 = 0 := by simp [hermPart]
theorem antiHermPart_zero : antiHermPart 0 = 0 := by simp [antiHermPart]
theorem conjugateBy_add_smul (V A B : ComplexMatrix2) (c : ℂ) :
    ComplexMatrix2.conjugateBy V (A + c • B) =
      ComplexMatrix2.conjugateBy V A + c • ComplexMatrix2.conjugateBy V B := by
  simp [ComplexMatrix2.conjugateBy, mul_add, add_mul]
theorem conjugateBy_mem_of_unitary {V A : ComplexMatrix2}
    (hV : V ∈ Matrix.unitaryGroup (Fin 2) ℂ) (hA : A ∈ ComplexMatrix2.hermitianTraceless) :
    ComplexMatrix2.conjugateBy V A ∈ ComplexMatrix2.hermitianTraceless := by
  have hVV : V * star V = 1 := Matrix.mem_unitaryGroup_iff.mp hV
  have hVV' : star V * V = 1 := Matrix.mem_unitaryGroup_iff'.mp hV
  have hinv : V⁻¹ = star V := Matrix.inv_eq_right_inv hVV
  refine ⟨?_, ?_⟩
  · rw [ComplexMatrix2.conjugateBy, hinv, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, ← hA.1, mul_assoc]
  · show Matrix.trace (ComplexMatrix2.conjugateBy V A) = 0
    rw [ComplexMatrix2.conjugateBy, hinv, Matrix.trace_mul_comm, ← mul_assoc, hVV', one_mul]
    exact hA.2
theorem bracket_mem_hermitianTraceless {Z B : ComplexMatrix2}
    (hZ : Z ∈ ComplexMatrix2.hermitianTraceless) (hB : B ∈ ComplexMatrix2.hermitianTraceless) :
    (Complex.I / 2) • ⁅Z, B⁆ ∈ ComplexMatrix2.hermitianTraceless := by apply _root_.YangMills.Construction.Tower.RealQuadraticTransposes.halfI_smul_bracket_mem <;> assumption
end TracelessMatrices
section EdgeForms
variable {a : ℝ}
theorem extendOddly_of_pos (f : InfiniteLattice.Link a → ComplexMatrix2)
    {b : InfiniteLattice.Link a} (hb : b.IsPositivelyOriented) :
    FullSpace.extendOddly f b = f b := if_pos hb
theorem extendOddly_opposite (ha : 0 < a) (f : InfiniteLattice.Link a → ComplexMatrix2)
    (b : InfiniteLattice.Link a) :
    FullSpace.extendOddly f b.opposite = -FullSpace.extendOddly f b := by apply _root_.YangMills.Construction.Tower.FullSpace.CurveDerivatives.extendOddly_opposite <;> assumption
theorem odd_ext {B B' : InfiniteLattice.Link a → ComplexMatrix2}
    (hB : ∀ b : InfiniteLattice.Link a, B b.opposite = -B b)
    (hB' : ∀ b : InfiniteLattice.Link a, B' b.opposite = -B' b)
    (h : ∀ b : InfiniteLattice.Link a, b.IsPositivelyOriented → B b = B' b) : B = B' := by apply _root_.YangMills.Construction.Tower.FullSpace.Surjectivity.eq_of_eq_on_positive <;> assumption
theorem covDiff_add_smul (ha : 0 < a) (U : InfiniteLattice.Link a → ComplexMatrix2)
    (l₁ l₂ : InfiniteLattice.LatticePoint a → ComplexMatrix2) (c : ℂ) :
    FullSpace.covDiff U (l₁ + c • l₂) =
      FullSpace.covDiff U l₁ + c • FullSpace.covDiff U l₂ := by
  refine odd_ext (extendOddly_opposite ha _) (fun b => ?_) fun b hb => ?_
  · show FullSpace.covDiff U l₁ b.opposite + c • FullSpace.covDiff U l₂ b.opposite = _
    rw [show FullSpace.covDiff U l₁ b.opposite = -FullSpace.covDiff U l₁ b from
        extendOddly_opposite ha _ b,
      show FullSpace.covDiff U l₂ b.opposite = -FullSpace.covDiff U l₂ b from
        extendOddly_opposite ha _ b]
    simp only [Pi.add_apply, Pi.smul_apply, smul_neg]
    abel
  · show FullSpace.extendOddly _ b =
      FullSpace.extendOddly _ b + c • FullSpace.extendOddly _ b
    rw [extendOddly_of_pos _ hb, extendOddly_of_pos _ hb, extendOddly_of_pos _ hb]
    simp only [Pi.add_apply, Pi.smul_apply, conjugateBy_add_smul]
    module
theorem levelBracketTerm_of_pos (U : InfiniteLattice.Link a → ComplexMatrix2)
    (l : InfiniteLattice.LatticePoint a → ComplexMatrix2)
    (B : InfiniteLattice.Link a → ComplexMatrix2)
    {b : InfiniteLattice.Link a} (hb : b.IsPositivelyOriented) :
    FullSpace.levelBracketTerm U l B b =
      (Complex.I / 2) • ⁅l b.initial + ComplexMatrix2.conjugateBy (U b) (l b.terminal), B b⁆ :=
  extendOddly_of_pos _ hb
theorem levelBracketTerm_mem (ha : 0 < a) {U : InfiniteLattice.Link a → ComplexMatrix2}
    (hU : ∀ b, U b ∈ Matrix.unitaryGroup (Fin 2) ℂ)
    {l : InfiniteLattice.LatticePoint a → ComplexMatrix2}
    (hl : ∀ x, l x ∈ ComplexMatrix2.hermitianTraceless)
    {B : InfiniteLattice.Link a → ComplexMatrix2} (hB : B ∈ FullSpace.edgeFormSpace a) :
    FullSpace.levelBracketTerm U l B ∈ FullSpace.edgeFormSpace a := by
  refine ⟨fun b hb => ?_, extendOddly_opposite ha _⟩
  rw [levelBracketTerm_of_pos U l B hb]
  exact bracket_mem_hermitianTraceless
    (ComplexMatrix2.hermitianTraceless.add_mem (hl _) (conjugateBy_mem_of_unitary (hU b) (hl _)))
    (hB.1 b hb)
theorem levelBracketTerm_eq_zero (U : InfiniteLattice.Link a → ComplexMatrix2)
    (l : InfiniteLattice.LatticePoint a → ComplexMatrix2)
    {B : InfiniteLattice.Link a → ComplexMatrix2}
    {b : InfiniteLattice.Link a} (hb : b.IsPositivelyOriented) (h0 : B b = 0) :
    FullSpace.levelBracketTerm U l B b = 0 := by
  rw [levelBracketTerm_of_pos U l B hb, h0]
  simp [Ring.lie_def]
end EdgeForms
section FaceSum
variable {a : ℝ}
def xyFace (x : InfiniteLattice.LatticePoint a) : InfiniteLattice.ElementaryPlaquette a :=
  ⟨x, 0, 1, by decide⟩
theorem xyFace_injective :
    Function.Injective (xyFace : InfiniteLattice.LatticePoint a → _) := fun _ _ h =>
  congrArg InfiniteLattice.ElementaryPlaquette.corner h
theorem forwardEdge_injective (μ : Fin 4) :
    Function.Injective fun x : InfiniteLattice.LatticePoint a => FullSpace.forwardEdge x μ :=
  fun _ _ h => congrArg (fun b : FullSpace.PositiveEdge a => b.1.initial) h
theorem support_forwardEdge_finite {g : FullSpace.PositiveEdge a → ℝ}
    (hg : (Function.support g).Finite) (μ : Fin 4) :
    (Function.support fun x : InfiniteLattice.LatticePoint a =>
      g (FullSpace.forwardEdge x μ)).Finite :=
  (hg.preimage (forwardEdge_injective μ).injOn).subset fun _ hx => hx
theorem finsum_xyFace_edgeDifference {g : FullSpace.PositiveEdge a → ℝ}
    (hg : (Function.support g).Finite) :
    ∑ᶠ p : InfiniteLattice.ElementaryPlaquette a,
      (if p.lowAxis = 0 ∧ p.highAxis = 1 then FullSpace.edgeDifference g p else 0) = 0 := by
  have hsupp : Function.support (fun p : InfiniteLattice.ElementaryPlaquette a =>
      if p.lowAxis = 0 ∧ p.highAxis = 1 then FullSpace.edgeDifference g p else 0) ⊆
      Set.range xyFace := by
    intro p hp
    by_cases c : p.lowAxis = 0 ∧ p.highAxis = 1
    · exact ⟨p.corner, InfiniteLattice.ElementaryPlaquette.ext rfl c.1.symm c.2.symm⟩
    · exact absurd (if_neg c) hp
  have e₁ : ∑ᶠ p : InfiniteLattice.ElementaryPlaquette a,
      (if p.lowAxis = 0 ∧ p.highAxis = 1 then FullSpace.edgeDifference g p else 0) =
      ∑ᶠ x : InfiniteLattice.LatticePoint a, FullSpace.edgeDifference g (xyFace x) := by
    have e := finsum_mem_range (f := fun p : InfiniteLattice.ElementaryPlaquette a =>
      if p.lowAxis = 0 ∧ p.highAxis = 1 then FullSpace.edgeDifference g p else 0)
      (xyFace_injective (a := a))
    rw [finsum_mem_def, Set.indicator_eq_self.mpr hsupp] at e
    rw [e]
    exact finsum_congr fun x => if_pos ⟨rfl, rfl⟩
  rw [e₁]
  obtain ⟨A, hA⟩ : ∃ A : InfiniteLattice.LatticePoint a → ℝ,
      A = fun x => g (FullSpace.forwardEdge x 0) := ⟨_, rfl⟩
  obtain ⟨C, hC⟩ : ∃ C : InfiniteLattice.LatticePoint a → ℝ,
      C = fun x => g (FullSpace.forwardEdge x 1) := ⟨_, rfl⟩
  have fA : (Function.support A).Finite := hA ▸ support_forwardEdge_finite hg 0
  have fC : (Function.support C).Finite := hC ▸ support_forwardEdge_finite hg 1
  have shifted : ∀ (F : InfiniteLattice.LatticePoint a → ℝ) (s : InfiniteLattice.LatticePoint a),
      (Function.support F).Finite → (Function.support fun x => F (x + s)).Finite :=
    fun F s hF => (hF.preimage (add_left_injective s).injOn).subset fun _ hx => hx
  have moved : ∀ (F : InfiniteLattice.LatticePoint a → ℝ) (s : InfiniteLattice.LatticePoint a),
      ∑ᶠ x, F (x + s) = ∑ᶠ x, F x := fun F s => finsum_comp_equiv (Equiv.addRight s)
  have e₂ : ∀ x : InfiniteLattice.LatticePoint a, FullSpace.edgeDifference g (xyFace x) =
      A x + C (x + InfiniteLattice.axisStep a 0) - A (x + InfiniteLattice.axisStep a 1) - C x := by
    intro x
    rw [hA, hC]
    rfl
  rw [finsum_congr e₂,
    finsum_sub_distrib (((fA.union (shifted C _ fC)).subset (Function.support_add _ _)).union
      (shifted A _ fA) |>.subset (Function.support_sub _ _)) fC,
    finsum_sub_distrib ((fA.union (shifted C _ fC)).subset (Function.support_add _ _))
      (shifted A _ fA),
    finsum_add_distrib fA (shifted C _ fC), moved C, moved A]
  ring
end FaceSum
section HessianOperator
variable {L : ℕ}
theorem meshAt_pos (hL : 0 < L) : 0 < meshAt L 0 0 := by apply _root_.YangMills.Construction.Tower.AbelianFieldDensity.SectorDecomposition.AbelianOperatorLogarithmsProof.meshAt_zero_pos <;> assumption
theorem complexHessianOperator_mem {U : FullSpace.Edge L 0 0 → ComplexMatrix2} (hL : 0 < L)
    (B : FullSpace.Edge L 0 0 → ComplexMatrix2) :
    FullSpace.complexHessianOperator U B ∈ FullSpace.complexEdgeForms (meshAt L 0 0) := by apply _root_.YangMills.Construction.Tower.AbelianSymmetryProof.complexHessianOperator_mem <;> assumption
theorem basisForm_mem_edgeFormSpace (hL : 0 < L) (i : Fin 3)
    (b : FullSpace.PositiveEdge (meshAt L 0 0)) :
    FullSpace.basisForm i b ∈ FullSpace.edgeFormSpace (meshAt L 0 0) := by apply _root_.YangMills.Construction.Tower.AbelianSymmetryProof.basisForm_mem_edgeFormSpace <;> assumption
theorem basisForm_mem_complexEdgeForms (hL : 0 < L) (i : Fin 3)
    (b : FullSpace.PositiveEdge (meshAt L 0 0)) :
    FullSpace.basisForm i b ∈ FullSpace.complexEdgeForms (meshAt L 0 0) := by apply _root_.YangMills.Construction.Tower.AbelianSymmetryProof.basisForm_mem_complexEdgeForms <;> assumption
theorem basisForm_hasFiniteEdgeSupport (i : Fin 3) (b : FullSpace.PositiveEdge (meshAt L 0 0)) :
    FullSpace.HasFiniteEdgeSupport (FullSpace.basisForm i b) := by apply _root_.YangMills.SharedProofs.p37344 <;> assumption
theorem edgeFormPairing_basisForm (i : Fin 3) (b : FullSpace.PositiveEdge (meshAt L 0 0))
    (X : FullSpace.Edge L 0 0 → ComplexMatrix2) :
    FullSpace.finiteEdgePairing (FullSpace.basisForm i b) X =
      ComplexMatrix2.halfTrace (ComplexMatrix2.pauliFamily i * X b.1) := by apply _root_.YangMills.Construction.Tower.AbelianSymmetryProof.edgeFormPairing_basisForm <;> assumption
theorem covDiff_mem_finiteSupportComplexForms {U : FullSpace.Edge L 0 0 → ComplexMatrix2}
    (hD : CovDiffAndAdjoint U) {l : FullSpace.Vertex L 0 0 → ComplexMatrix2}
    (hl : l ∈ (unitVertexSpace L).complexSubmodule) (hf : HasFiniteSupp l) :
    FullSpace.covDiff U l ∈ finiteSupportComplexForms L 0 0 := by
  have e := hD.2.1 ⟨l, hl⟩
  have h₁ : FullSpace.covDiff U l ∈ FullSpace.complexEdgeForms (meshAt L 0 0) :=
    e ▸ (_root_.YangMills.Construction.Tower.UnitGaugeDirections.covDiffLinear U ⟨l, hl⟩).2
  have h₂ : HasFiniteSupp (FullSpace.restrictToPositiveEdges (FullSpace.covDiff U l)) :=
    e ▸ hD.2.2.1 ⟨l, hl⟩ hf
  exact ⟨h₁, (h₂.image Subtype.val).subset fun b hb => ⟨⟨b, hb.1⟩, hb.2, rfl⟩⟩
theorem complexActionDeriv_eq_zero {f : ℝ}
    (hD : ActionDerivative (AbelianFieldDensity.scaledLinearAngle L f))
    (hA : LinearFieldAngles L) {C : FullSpace.Edge L 0 0 → ComplexMatrix2}
    (hC : C ∈ FullSpace.edgeFormSpace (meshAt L 0 0)) (hf : FullSpace.HasFiniteEdgeSupport C) :
    FullSpace.complexActionDeriv
      (FullSpace.abelianLinkField (AbelianFieldDensity.scaledLinearAngle L f)) C = 0 := by
  rw [(hD C hC hf).2]
  have hg : (Function.support fun b : FullSpace.PositiveEdge (meshAt L 0 0) =>
      Real.sin f * FullSpace.diagonalComponent C b).Finite := by
    refine (hf.preimage Subtype.val_injective.injOn).subset fun b hb => ?_
    refine ⟨b.2, fun h0 => hb ?_⟩
    show Real.sin f * (ComplexMatrix2.halfTrace (C b.1 * ComplexMatrix2.pauliFamily 2)).re = 0
    rw [h0]
    simp [ComplexMatrix2.halfTrace]
  have e : ∑ᶠ p : FullSpace.Face L 0 0,
      Real.sin (FullSpace.faceAngle (AbelianFieldDensity.scaledLinearAngle L f) p) *
        FullSpace.edgeDifference (FullSpace.diagonalComponent C) p =
      ∑ᶠ p : FullSpace.Face L 0 0, (if p.lowAxis = 0 ∧ p.highAxis = 1 then
        FullSpace.edgeDifference
          (fun b => Real.sin f * FullSpace.diagonalComponent C b) p else 0) := by
    refine finsum_congr fun p => ?_
    have hp := hA f p
    show Real.sin (FullSpace.faceAngle (fun b => f * FullSpace.linearAbelianAngle b) p) * _ = _
    rw [hp]
    by_cases c : p.lowAxis = 0 ∧ p.highAxis = 1
    · rw [if_pos c, if_pos c]
      simp only [FullSpace.edgeDifference]
      ring
    · rw [if_neg c, if_neg c]
      simp
  rw [e, finsum_xyFace_edgeDifference hg]
  simp
end HessianOperator
theorem holds
    (hKernel : HessianKernel.KernelProperties)
    (hGauge : FullSpace.GaugeDirectionHessianClaim)
    (hDerivative : AbelianActionGradient.Statement)
    (hAngles : LinearFieldPlaquetteAngles.Claim)
    (hPlaquettes : AbelianFieldPlaquettes.Claim)
    (hDirections : UnitGaugeDirections.Claim) :
    GaugeDirectionHessianIdentity := by
  intro L hL f l hl hfin
  have hL0 : 0 < L := by
    have := hL.2
    omega
  have ha := meshAt_pos hL0
  have hDer := hDerivative L hL (AbelianFieldDensity.scaledLinearAngle L f)
  have hAng := hAngles L hL
  show FullSpace.massiveHessian
      (FullSpace.abelianLinkField (AbelianFieldDensity.scaledLinearAngle L f)) _ = _
  obtain ⟨U, hU⟩ : ∃ U,
      U = FullSpace.abelianLinkField (AbelianFieldDensity.scaledLinearAngle L f) := ⟨_, rfl⟩
  rw [← hU]
  have hUr : U ∈ FullSpace.fieldsValuedIn L 0 0 PeriodicLattice.compactGaugeGroup :=
    hU ▸ (hPlaquettes L hL (AbelianFieldDensity.scaledLinearAngle L f)).abelianLinkField_mem
  have hUc : U ∈ FullSpace.fieldsValuedIn L 0 0 PeriodicLattice.complexGaugeGroup :=
    ⟨fun b => (Matrix.mem_specialUnitaryGroup_iff.mp (hUr.1 b)).2, hUr.2⟩
  have hUu : ∀ b, U b ∈ Matrix.unitaryGroup (Fin 2) ℂ := fun b =>
    (Matrix.mem_specialUnitaryGroup_iff.mp (hUr.1 b)).1
  have hDir := ((hDirections L hL).2 U hUc).1
  have hK := (hKernel L hL 0 0 le_rfl).2 U hUc
  obtain ⟨l₁, hl₁⟩ : ∃ l₁ : FullSpace.Vertex L 0 0 → ComplexMatrix2,
      l₁ = fun x => hermPart (l x) := ⟨_, rfl⟩
  obtain ⟨l₂, hl₂⟩ : ∃ l₂ : FullSpace.Vertex L 0 0 → ComplexMatrix2,
      l₂ = fun x => antiHermPart (l x) := ⟨_, rfl⟩
  have hsum : l = l₁ + Complex.I • l₂ := by
    funext x
    rw [hl₁, hl₂]
    exact (hermPart_add_I_smul (l x)).symm
  have hr₁ : ∀ x, l₁ x ∈ ComplexMatrix2.hermitianTraceless := fun x => hl₁ ▸ hermPart_mem (hl x)
  have hr₂ : ∀ x, l₂ x ∈ ComplexMatrix2.hermitianTraceless := fun x =>
    hl₂ ▸ antiHermPart_mem (hl x)
  have hc₁ : ∀ x, l₁ x ∈ ComplexMatrix2.traceless := fun x => (hr₁ x).2
  have hc₂ : ∀ x, l₂ x ∈ ComplexMatrix2.traceless := fun x => (hr₂ x).2
  have hf₁ : HasFiniteSupp l₁ := hfin.subset fun x hx h0 => hx (by
    rw [hl₁]
    show hermPart (l x) = 0
    rw [h0, hermPart_zero])
  have hf₂ : HasFiniteSupp l₂ := hfin.subset fun x hx h0 => hx (by
    rw [hl₂]
    show antiHermPart (l x) = 0
    rw [h0, antiHermPart_zero])
  have hD₁ := covDiff_mem_finiteSupportComplexForms hDir (fun x _ => hc₁ x) hf₁
  have hD₂ := covDiff_mem_finiteSupportComplexForms hDir (fun x _ => hc₂ x) hf₂
  have hDl := covDiff_mem_finiteSupportComplexForms hDir (fun x _ => hl x) hfin
  have hdiff : FullSpace.covDiff U l =
      Complex.I • FullSpace.covDiff U l₂ + FullSpace.covDiff U l₁ := by
    conv_lhs => rw [hsum]
    rw [covDiff_add_smul ha, add_comm]
  have hreal : ∀ {lr : FullSpace.Vertex L 0 0 → ComplexMatrix2},
      (∀ x, lr x ∈ ComplexMatrix2.hermitianTraceless) →
      HasFiniteSupp lr → ∀ E ∈ finiteSupportComplexForms L 0 0,
      E ∈ FullSpace.edgeFormSpace (meshAt L 0 0) →
      FullSpace.complexActionHessian U E (FullSpace.covDiff U lr) = 0 := by
    intro lr hlr hfr E hE hEr
    rw [hGauge L 0 0 hL le_rfl U lr E hUc (fun x => (hlr x).2) hfr hE.1 hE.2, hU]
    refine complexActionDeriv_eq_zero hDer hAng
      (levelBracketTerm_mem ha (hU ▸ hUu) hlr hEr) (hE.2.subset fun b hb => ?_)
    exact ⟨hb.1, fun h0 => hb.2 (levelBracketTerm_eq_zero _ lr hb.1 h0)⟩
  have hzero : ∀ E ∈ finiteSupportComplexForms L 0 0,
      E ∈ FullSpace.edgeFormSpace (meshAt L 0 0) →
      FullSpace.complexActionHessian U E (FullSpace.covDiff U l) = 0 := by
    intro E hE hEr
    rw [hdiff, (hK.1 Complex.I _ hD₂ _ hD₁ E hE).2.1, hreal hr₁ hf₁ E hE hEr,
      hreal hr₂ hf₂ E hE hEr]
    simp
  have hH : FullSpace.complexHessianOperator U (FullSpace.covDiff U l) = 0 := by
    have hm := complexHessianOperator_mem (U := U) hL0 (FullSpace.covDiff U l)
    refine odd_ext hm.2 (fun b => by simp) fun b hb => ?_
    refine traceless_ext (hm.1 b hb) ComplexMatrix2.traceless.zero_mem fun i => ?_
    obtain ⟨E, hE⟩ : ∃ E, E = FullSpace.basisForm i
      (⟨b, hb⟩ : FullSpace.PositiveEdge (meshAt L 0 0)) := ⟨_, rfl⟩
    have hEf : E ∈ finiteSupportComplexForms L 0 0 :=
      hE ▸ ⟨basisForm_mem_complexEdgeForms hL0 i _, basisForm_hasFiniteEdgeSupport i _⟩
    have hEr : E ∈ FullSpace.edgeFormSpace (meshAt L 0 0) :=
      hE ▸ basisForm_mem_edgeFormSpace hL0 i _
    have t := edgeFormPairing_basisForm i (⟨b, hb⟩ : FullSpace.PositiveEdge (meshAt L 0 0))
      (FullSpace.complexHessianOperator U (FullSpace.covDiff U l))
    rw [← hE, hK.2.2.2.2.1 E hEf _ hDl, hzero E hEf hEr] at t
    rw [← t]
    simp [ComplexMatrix2.halfTrace]
  show FullSpace.complexHessianOperator U (FullSpace.covDiff U l) + _ = _
  rw [hH, zero_add]
end YangMills.Construction.Tower.ConstantFieldSymbols.GaugeDirectionHessian
end
