import YangMills.Construction.Towers.CoefficientsOfTheSymbolOfTheSecondDifferential
import YangMills.Construction.Towers.CrossingAverageOnASideProof
import YangMills.Construction.Towers.IteratedAveragesReadOnlyTheBlocksAtTheSideInfinityProof
import YangMills.Construction.Towers.LatticesOfSideInfinityOverAFiniteSide
import YangMills.Construction.Towers.PlaquettesOfABondProof
import YangMills.Construction.Towers.PolarisationAtTheResponseFieldProof
import YangMills.Construction.Towers.TheSecondDifferentialIsCloseToItsSymbolProof
import YangMills.Construction.Towers.TheSymbolAtZeroOnConstantForms
import Mathlib
set_option autoImplicit false
open Filter Topology
noncomputable section
namespace YangMills.Construction.Tower.SymbolAtZero
open Matrices (ComplexMatrix2)
open Matrices.ComplexMatrix2 (pauliFamily hermitianTraceless traceless)
open PeriodicOperators (PeriodicData PosEdge toComplexVec bilinDot dualLattice blochWave wNorm
  imStrip colourEdges castVec intShift shiftEdge)
open PeriodicOperators.LogDetSecondDerivs (descendField)
open TorusResponseField (constantFieldAmplitude constantFinestForm blochWaveField)
open LocalKernels (FieldIdx FieldComponent)
open FullSpace (fieldPeriodicData secondVariationSymbol)
open InfiniteLattice (AmbientSpace axisStep)
open PeriodicLattice (torusSide FourTorus levelDepth)
open FullLatticeOverTorus (ShiftSurjectiveOnEdges)
theorem pauliFamily_mem_hermitianTraceless (a : Fin 3) : pauliFamily a ∈ hermitianTraceless := by apply _root_.YangMills.SharedProofs.p1437 <;> assumption
theorem mem_traceless_of_mem_hermitianTraceless {X : ComplexMatrix2} (h : X ∈ hermitianTraceless) :
    X ∈ traceless := h.2
theorem pauliCoeff_eq_coordinate {X : ComplexMatrix2} (h : X ∈ traceless) (a : Fin 3) :
    pauliCoeff a X = OneLoop.pauliCoordinateEquiv ⟨X, h⟩ a := by
  simp only [pauliCoeff, dif_pos h]
theorem pauliCoeff_zero (a : Fin 3) : pauliCoeff a (0 : ComplexMatrix2) = 0 := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.pauliCoeff_zero <;> assumption
theorem pauliCoeff_pauliFamily (a a' : Fin 3) :
    pauliCoeff a (pauliFamily a') = if a = a' then 1 else 0 := by apply _root_.YangMills.Construction.Tower.CrossingSmoothingContraction.pauliCoeff_pauliFamily <;> assumption
theorem pauliCoeff_smul (z : ℂ) {X : ComplexMatrix2} (h : X ∈ traceless) (a : Fin 3) :
    pauliCoeff a (z • X) = z * pauliCoeff a X := by
  rw [pauliCoeff_eq_coordinate (traceless.smul_mem z h), pauliCoeff_eq_coordinate h]
  have : (⟨z • X, traceless.smul_mem z h⟩ : traceless) = z • ⟨X, h⟩ := rfl
  rw [this, map_smul]
  rfl
theorem eq_of_pauliCoeff_eq {X Y : ComplexMatrix2} (hX : X ∈ traceless) (hY : Y ∈ traceless)
    (h : ∀ a, pauliCoeff a X = pauliCoeff a Y) : X = Y := by apply _root_.YangMills.Construction.Tower.FullSpace.IterLocality.eq_of_pauliCoeff_eq <;> assumption
theorem descendField_mkQuot (F : PeriodicData) {f : F.Carrier → ℂ}
    (hf : ∀ (m : Fin 4 → ℤ) (ι : F.Carrier), f (F.translate ((1 : ℕ) • m) ι) = f ι)
    (ι : F.Carrier) :
    descendField F 1 f (F.mkQuot 1 ι) = f ι := by
  have hl : ∀ ι ι' : F.Carrier, (∃ m : Fin 4 → ℤ, ι' = F.translate ((1 : ℕ) • m) ι) →
      f ι = f ι' := by
    rintro ι ι' ⟨m, rfl⟩
    exact (hf m ι).symm
  have hk : ∀ κ, F.mkQuot 1 κ = F.mkQuot 1 ι → f κ = f ι := fun κ h =>
    congrArg (Quot.lift f hl) h
  have := Classical.epsilon_spec
    (p := fun z => ∀ κ, F.mkQuot 1 κ = F.mkQuot 1 ι → f κ = z) ⟨f ι, hk⟩
  exact ((this ι rfl).trans rfl).symm
section Amplitude
variable {L k : ℕ}
def edgeAxis (b : PosEdge L k 0) : Fin 4 := b.2.choose
theorem edgeAxis_spec (b : PosEdge L k 0) :
    b.1.terminal - b.1.initial = axisStep (meshAt L k 0) (edgeAxis b) :=
  b.2.choose_spec
theorem axisStep_injective {s : ℝ} (hs : s ≠ 0) {ρ ρ' : Fin 4}
    (h : axisStep s ρ = axisStep s ρ') : ρ = ρ' := by apply _root_.YangMills.Construction.Tower.FacesContainingEdge.axisStep_injective <;> assumption
theorem meshAt_ne_zero (hL : 0 < L) (i : ℕ) : meshAt L k i ≠ 0 := by apply _root_.YangMills.Construction.Tower.FullSpace.DoubleCubeImage.meshAt_ne_zero <;> assumption
theorem edgeAxis_eq (hL : 0 < L) (b : PosEdge L k 0) {ρ : Fin 4}
    (h : b.1.terminal - b.1.initial = axisStep (meshAt L k 0) ρ) :
    edgeAxis b = ρ :=
  axisStep_injective (meshAt_ne_zero hL 0) ((edgeAxis_spec b).symm.trans h)
theorem constantFinestForm_apply (hL : 0 < L) (ξ : Fin 4 → ComplexMatrix2) (b : PosEdge L k 0) :
    constantFinestForm L k ξ b.1 = ξ (edgeAxis b) := by
  classical
  have hspec := edgeAxis_spec b
  simp only [constantFinestForm, FullSpace.extendOddly, if_pos b.2]
  rw [Finset.sum_eq_single (edgeAxis b)]
  · rw [if_pos hspec]
  · intro ρ _ hρ
    rw [if_neg]
    intro h
    exact hρ (axisStep_injective (meshAt_ne_zero hL 0) (h.symm.trans hspec))
  · intro h
    exact absurd (Finset.mem_univ _) h
theorem edgeAxis_shiftEdge (hL : 0 < L) (N : Fin 4 → ℤ) (hT : ShiftSurjectiveOnEdges L k 0 N)
    (b : PosEdge L k 0) :
    edgeAxis (shiftEdge N b) = edgeAxis b := by
  refine edgeAxis_eq hL _ ?_
  rw [← edgeAxis_spec b]
  apply Subtype.ext
  have h₁ := (hT.2 b).1
  have h₂ := (hT.2 b).2
  change ((shiftEdge N b).1.terminal : AmbientSpace) - ((shiftEdge N b).1.initial : AmbientSpace) =
    (b.1.terminal : AmbientSpace) - (b.1.initial : AmbientSpace)
  rw [h₁, h₂]
  abel
theorem coeffs_constantFinestForm (hL : 0 < L) (ξ : Fin 4 → ComplexMatrix2) (a : Fin 3)
    (b : PosEdge L k 0) :
    (FullSpace.edgePauliCoordinates L k 0).coeffs (constantFinestForm L k ξ) (a, b) =
      pauliCoeff a (ξ (edgeAxis b)) := by
  change pauliCoeff a (constantFinestForm L k ξ b.1) = _
  rw [constantFinestForm_apply hL]
theorem descendField_constantFinestForm (hL : 0 < L) (hT : ∀ N, ShiftSurjectiveOnEdges L k 0 N)
    (ξ : Fin 4 → ComplexMatrix2) (a : Fin 3) (b : PosEdge L k 0) :
    descendField (colourEdges L k 0) 1
        ((FullSpace.edgePauliCoordinates L k 0).coeffs (constantFinestForm L k ξ))
        ((colourEdges L k 0).mkQuot 1 (a, b)) =
      pauliCoeff a (ξ (edgeAxis b)) := by
  refine (descendField_mkQuot (colourEdges L k 0) ?_ (a, b)).trans
    (coeffs_constantFinestForm hL ξ a b)
  · rintro m ⟨a', b'⟩
    change (FullSpace.edgePauliCoordinates L k 0).coeffs (constantFinestForm L k ξ)
      (a', shiftEdge ((1 : ℕ) • m) b') = _
    refine (coeffs_constantFinestForm hL ξ a' _).trans ?_
    rw [edgeAxis_shiftEdge hL _ (hT _)]
    exact (coeffs_constantFinestForm hL ξ a' b').symm
theorem tripleIndexFunction_translate (hL : 0 < L) (A J : (colourEdges L k 0).UnitQuot → ℂ)
    (M : (colourEdges L k k).UnitQuot → ℂ) (m : Fin 4 → ℤ) (ι : FieldIdx L k hL) :
    FullSpace.tripleIndexFunction L k hL A J M ((fieldPeriodicData L k hL).translate ((1 : ℕ) • m) ι) =
      FullSpace.tripleIndexFunction L k hL A J M ι := by
  obtain ⟨p, ι⟩ := ι
  cases p with
  | background =>
    change A ((colourEdges L k 0).mkQuot 1 (ι.1, shiftEdge ((1 : ℕ) • m) ι.2)) =
      A ((colourEdges L k 0).mkQuot 1 ι)
    congr 1
    exact (Quot.sound ⟨m, rfl⟩).symm
  | source =>
    change J ((colourEdges L k 0).mkQuot 1 (ι.1, shiftEdge ((1 : ℕ) • m) ι.2)) =
      J ((colourEdges L k 0).mkQuot 1 ι)
    congr 1
    exact (Quot.sound ⟨m, rfl⟩).symm
  | coarse =>
    change M ((colourEdges L k k).mkQuot 1 (ι.1, shiftEdge ((1 : ℕ) • m) ι.2)) =
      M ((colourEdges L k k).mkQuot 1 ι)
    congr 1
    exact (Quot.sound ⟨m, rfl⟩).symm
theorem constantFieldAmplitude_background (hL : 0 < L) (hT : ∀ N, ShiftSurjectiveOnEdges L k 0 N)
    (ξ : Fin 4 → ComplexMatrix2) (a : Fin 3) (b : PosEdge L k 0) :
    constantFieldAmplitude L k hL ξ
        ((fieldPeriodicData L k hL).mkQuot 1 ⟨FieldComponent.background, (a, b)⟩) =
      pauliCoeff a (ξ (edgeAxis b)) := by
  refine (descendField_mkQuot (fieldPeriodicData L k hL)
    (tripleIndexFunction_translate hL _ _ _) _).trans ?_
  exact descendField_constantFinestForm hL hT ξ a b
theorem constantFieldAmplitude_other (hL : 0 < L) (ξ : Fin 4 → ComplexMatrix2) (ι : FieldIdx L k hL)
    (hι : ι.1 = FieldComponent.source ∨ ι.1 = FieldComponent.coarse) :
    constantFieldAmplitude L k hL ξ ((fieldPeriodicData L k hL).mkQuot 1 ι) = 0 := by
  refine (descendField_mkQuot (fieldPeriodicData L k hL)
    (tripleIndexFunction_translate hL _ _ _) _).trans ?_
  obtain ⟨p, ι⟩ := ι
  cases p with
  | background => simp at hι
  | source => rfl
  | coarse => rfl
end Amplitude
section Parts
variable {L n k : ℕ}
theorem mem_complexEdgeForms_of_mem {i : ℕ} {B : Edge L n k i → ComplexMatrix2}
    (h : B ∈ edgeFormSpace L n k i) : B ∈ complexEdgeForms L n k i := by apply _root_.YangMills.Construction.Tower.LevelwiseMeans.mem_complexEdgeForms_of_mem <;> assumption
theorem periodicField_decomp (ζ : PeriodicField L n k) :
    ∃ (ζr ζi : PeriodicField L n k) (r r' : RealPeriodicField L n k),
      ζr.RealizedBy r ∧ ζi.RealizedBy r' ∧ ζ = ζr + Complex.I • ζi := by apply _root_.YangMills.Construction.Tower.SecondDerivNearSymbol.periodicField_decomp <;> assumption
def backgroundOnly (g : edgeFormSpace L n k 0) : PeriodicField L n k :=
  (⟨g, mem_complexEdgeForms_of_mem g.2⟩, 0, 0)
theorem backgroundOnly_realizedBy (g : edgeFormSpace L n k 0) :
    (backgroundOnly g).RealizedBy (g, 0, 0) :=
  ⟨rfl, rfl, rfl⟩
theorem isComplexSecondDeriv_backgroundOnly_eq_zero
    (β : PeriodicField L n k →ₗ[ℂ] PeriodicField L n k →ₗ[ℂ] ℂ)
    (hβ : IsComplexSecondDeriv L n k β) (g : edgeFormSpace L n k 0)
    (hg : ∀ r, fieldFunctionalSecondDeriv L n k (g, 0, 0) r = 0) (ζ : PeriodicField L n k) :
    β (backgroundOnly g) ζ = 0 := by
  obtain ⟨ζr, ζi, r, r', hr, hr', rfl⟩ := periodicField_decomp ζ
  rw [map_add, map_smul, hβ _ _ _ _ (backgroundOnly_realizedBy g) hr,
    hβ _ _ _ _ (backgroundOnly_realizedBy g) hr', hg, hg]
  simp
end Parts
section Wave
variable {L n k : ℕ}
def axisCharacter (ν : Fin 4) (x : Vertex L n k 0) : ℂ :=
  (AddCircle.toCircle ((x : FourTorus L n) ν) : ℂ)
def circlePhase (L n : ℕ) (t : ℝ) : ℂ :=
  Complex.exp (((2 * Real.pi / torusSide L n * t : ℝ) : ℂ) * Complex.I)
theorem circlePhase_add (t u : ℝ) :
    circlePhase L n (t + u) = circlePhase L n t * circlePhase L n u := by
  simp only [circlePhase, ← Complex.exp_add]
  congr 1
  push_cast
  ring
theorem axisCharacter_projVertex (ν : Fin 4) (x : FullSpace.Vertex L k 0) :
    axisCharacter ν (FullSpace.projVertex L n k 0 x) = circlePhase L n ((x : AmbientSpace) ν) := by
  change ((AddCircle.toCircle (((x : AmbientSpace) ν : ℝ) :
    AddCircle (torusSide L n)) : Circle) : ℂ) = _
  rw [AddCircle.toCircle_apply_mk, Circle.coe_exp]
  rfl
def vertexRePart (ν : Fin 4) (a : Fin 3) : Vertex L n k 0 → ComplexMatrix2 :=
  fun x => (axisCharacter ν x).re • pauliFamily a
def vertexImPart (ν : Fin 4) (a : Fin 3) : Vertex L n k 0 → ComplexMatrix2 :=
  fun x => (axisCharacter ν x).im • pauliFamily a
theorem vertexCoboundary_mem {l : Vertex L n k 0 → ComplexMatrix2}
    (hl : ∀ x, l x ∈ hermitianTraceless) :
    vertexCoboundary l ∈ edgeFormSpace L n k 0 := by
  refine ⟨fun e _ => hermitianTraceless.sub_mem (hl _) (hl _), fun e => ?_⟩
  change l e.source - l e.target = -(l e.target - l e.source)
  abel
def coboundaryRe (ν : Fin 4) (a : Fin 3) : edgeFormSpace L n k 0 :=
  ⟨vertexCoboundary (vertexRePart ν a), vertexCoboundary_mem fun _ =>
    hermitianTraceless.smul_mem _ (pauliFamily_mem_hermitianTraceless a)⟩
def coboundaryIm (ν : Fin 4) (a : Fin 3) : edgeFormSpace L n k 0 :=
  ⟨vertexCoboundary (vertexImPart ν a), vertexCoboundary_mem fun _ =>
    hermitianTraceless.smul_mem _ (pauliFamily_mem_hermitianTraceless a)⟩
def gradientWave (L n k : ℕ) (z : ℂ) (ν : Fin 4) (a : Fin 3) : PeriodicField L n k :=
  z⁻¹ • (backgroundOnly (coboundaryRe ν a) + Complex.I • backgroundOnly (coboundaryIm ν a))
theorem re_smul_add_I_smul_im_smul (w : ℂ) (P : ComplexMatrix2) :
    w.re • P + Complex.I • (w.im • P) = w • P := by
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, Complex.real_smul, smul_eq_mul]
  conv_rhs => rw [← Complex.re_add_im w]
  ring
theorem gradientWave_apply (z : ℂ) (ν : Fin 4) (a : Fin 3) (e : Edge L n k 0) :
    ((gradientWave L n k z ν a).1 : Edge L n k 0 → ComplexMatrix2) e =
      z⁻¹ • ((axisCharacter ν e.target - axisCharacter ν e.source) • pauliFamily a) := by
  change z⁻¹ • ((vertexRePart ν a e.target - vertexRePart ν a e.source) +
    Complex.I • (vertexImPart ν a e.target - vertexImPart ν a e.source)) = _
  congr 1
  rw [sub_smul, ← re_smul_add_I_smul_im_smul (axisCharacter ν e.target),
    ← re_smul_add_I_smul_im_smul (axisCharacter ν e.source), smul_sub]
  simp only [vertexRePart, vertexImPart]
  abel
theorem gradientWave_snd (z : ℂ) (ν : Fin 4) (a : Fin 3) :
    (gradientWave L n k z ν a).2 = 0 := by
  simp [gradientWave, backgroundOnly]
theorem isComplexSecondDeriv_gradientWave_eq_zero (hOn : HessianVanishesOnGaugeDirections)
    (hS : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hk : 1 ≤ k)
    (β : PeriodicField L n k →ₗ[ℂ] PeriodicField L n k →ₗ[ℂ] ℂ)
    (hβ : IsComplexSecondDeriv L n k β) (z : ℂ) (ν : Fin 4) (a : Fin 3)
    (ζ : PeriodicField L n k) : β (gradientWave L n k z ν a) ζ = 0 := by
  have hre := isComplexSecondDeriv_backgroundOnly_eq_zero β hβ (coboundaryRe ν a) fun r =>
    hOn L n k hS hn hk (vertexRePart ν a)
      (fun x _ => hermitianTraceless.smul_mem _ (pauliFamily_mem_hermitianTraceless a)) _ rfl r
  have him := isComplexSecondDeriv_backgroundOnly_eq_zero β hβ (coboundaryIm ν a) fun r =>
    hOn L n k hS hn hk (vertexImPart ν a)
      (fun x _ => hermitianTraceless.smul_mem _ (pauliFamily_mem_hermitianTraceless a)) _ rfl r
  simp only [gradientWave, map_smul, map_add, LinearMap.smul_apply, LinearMap.add_apply, hre, him]
  simp
end Wave
section PlaneWave
variable {L n k : ℕ}
open LocalKernels.Periodisation (ProjEdgesCompatible ProjCellsClassified)
def axisMomentum (L n : ℕ) (ν : Fin 4) : AmbientSpace :=
  Pi.single ν (2 * Real.pi / torusSide L n)
theorem exp_bilinDot_axisMomentum (ν : Fin 4) (y : AmbientSpace) :
    Complex.exp (Complex.I * bilinDot (toComplexVec (axisMomentum L n ν)) (toComplexVec y)) =
      circlePhase L n (y ν) := by
  have h : bilinDot (toComplexVec (axisMomentum L n ν)) (toComplexVec y) =
      ((2 * Real.pi / torusSide L n * y ν : ℝ) : ℂ) := by
    simp only [bilinDot, toComplexVec, axisMomentum]
    rw [Finset.sum_eq_single ν]
    · simp
    · intro μ _ hμ
      simp [Pi.single_eq_of_ne hμ]
    · intro h
      exact absurd (Finset.mem_univ _) h
  rw [h, mul_comm]
  rfl
theorem terminal_coord (b : PosEdge L k 0) (ν : Fin 4) :
    (b.1.terminal : AmbientSpace) ν =
      (b.1.initial : AmbientSpace) ν +
        (Pi.single (edgeAxis b) (meshAt L k 0) : AmbientSpace) ν := by
  have h := congrFun (congrArg Subtype.val (edgeAxis_spec b)) ν
  have h' : (b.1.terminal : AmbientSpace) ν - (b.1.initial : AmbientSpace) ν =
      (Pi.single (edgeAxis b) (meshAt L k 0) : AmbientSpace) ν := h
  linarith
theorem circlePhase_zero : circlePhase L n 0 = 1 := by
  simp [circlePhase]
theorem pauliCoeff_gradientWave_background (hImg : ProjEdgesCompatible L n k 0) {z : ℂ}
    (hz : z = circlePhase L n (meshAt L k 0) - 1) (hz₀ : z ≠ 0) (ν : Fin 4) (a a' : Fin 3)
    (b : PosEdge L k 0) :
    pauliCoeff a' (((gradientWave L n k z ν a).1 : Edge L n k 0 → ComplexMatrix2)
        (LocalKernels.projPositiveEdge L n k 0 b).1) =
      circlePhase L n ((b.1.initial : AmbientSpace) ν) *
        pauliCoeff a' ((Pi.single ν (pauliFamily a) : Fin 4 → ComplexMatrix2) (edgeAxis b)) := by
  rw [gradientWave_apply, hImg.2.1 b, (hImg.1 _).2, (hImg.1 _).1, axisCharacter_projVertex,
    axisCharacter_projVertex, terminal_coord b ν, circlePhase_add]
  by_cases hd : edgeAxis b = ν
  · rw [hd]
    simp only [Pi.single_eq_same]
    have h₁ : circlePhase L n ((b.1.initial : AmbientSpace) ν) * circlePhase L n (meshAt L k 0) -
        circlePhase L n ((b.1.initial : AmbientSpace) ν) =
        circlePhase L n ((b.1.initial : AmbientSpace) ν) * z := by
      rw [hz]; ring
    rw [h₁, smul_smul]
    have h₂ : z⁻¹ * (circlePhase L n ((b.1.initial : AmbientSpace) ν) * z) =
        circlePhase L n ((b.1.initial : AmbientSpace) ν) := by
      field_simp
    rw [h₂, pauliCoeff_smul _
      (mem_traceless_of_mem_hermitianTraceless (pauliFamily_mem_hermitianTraceless a))]
  · have hne : ν ≠ edgeAxis b := fun h => hd h.symm
    rw [Pi.single_eq_of_ne hne, Pi.single_eq_of_ne hd, circlePhase_zero, mul_one, sub_self,
      zero_smul, smul_zero, pauliCoeff_zero, mul_zero]
theorem gradientWave_pauliCoeffs (hL : 0 < L) (hT : ∀ N, ShiftSurjectiveOnEdges L k 0 N)
    (hImg : ProjEdgesCompatible L n k 0) {z : ℂ}
    (hz : z = circlePhase L n (meshAt L k 0) - 1) (hz₀ : z ≠ 0) (ν : Fin 4) (a : Fin 3) :
    (gradientWave L n k z ν a).pauliCoeffs hL =
      blochWave (fieldPeriodicData L k hL) (toComplexVec (axisMomentum L n ν))
        (constantFieldAmplitude L k hL (Pi.single ν (pauliFamily a))) := by
  funext ι
  obtain ⟨p, ι⟩ := ι
  cases p with
  | background =>
    have h₁ := pauliCoeff_gradientWave_background hImg hz hz₀ ν a ι.1 ι.2
    have h₂ := constantFieldAmplitude_background hL hT (Pi.single ν (pauliFamily a)) ι.1 ι.2
    have h₃ := exp_bilinDot_axisMomentum (L := L) (n := n) ν (ι.2.1.initial : AmbientSpace)
    refine h₁.trans ?_
    rw [← h₂, ← h₃]
    rfl
  | source =>
    have h₂ := constantFieldAmplitude_other hL (Pi.single ν (pauliFamily a))
      (⟨FieldComponent.source, ι⟩ : FieldIdx L k hL) (Or.inl rfl)
    have h₁ : (gradientWave L n k z ν a).pauliCoeffs hL ⟨FieldComponent.source, ι⟩ = 0 := by
      change pauliCoeff ι.1
        (((gradientWave L n k z ν a).2.1 : Edge L n k 0 → ComplexMatrix2) _) = 0
      rw [gradientWave_snd]
      exact pauliCoeff_zero _
    rw [h₁]
    change 0 = _ * constantFieldAmplitude L k hL _ _
    rw [h₂, mul_zero]
  | coarse =>
    have h₂ := constantFieldAmplitude_other hL (Pi.single ν (pauliFamily a))
      (⟨FieldComponent.coarse, ι⟩ : FieldIdx L k hL) (Or.inr rfl)
    have h₁ : (gradientWave L n k z ν a).pauliCoeffs hL ⟨FieldComponent.coarse, ι⟩ = 0 := by
      change pauliCoeff ι.1
        (((gradientWave L n k z ν a).2.2 : Edge L n k k → ComplexMatrix2) _) = 0
      rw [gradientWave_snd]
      exact pauliCoeff_zero _
    rw [h₁]
    change 0 = _ * constantFieldAmplitude L k hL _ _
    rw [h₂, mul_zero]
theorem complexEdgeForm_ext {i : ℕ}
    (hOr : ∀ e : Edge L n k i, Xor e.IsPositivelyOriented e.opposite.IsPositivelyOriented)
    {B B' : complexEdgeForms L n k i}
    (h : ∀ (a : Fin 3) (c : PositiveEdge L n k i),
      pauliCoeff a ((B : Edge L n k i → ComplexMatrix2) c.1) =
        pauliCoeff a ((B' : Edge L n k i → ComplexMatrix2) c.1)) : B = B' := by
  have hp : ∀ e : Edge L n k i, e.IsPositivelyOriented →
      (B : Edge L n k i → ComplexMatrix2) e = (B' : Edge L n k i → ComplexMatrix2) e :=
    fun e he => eq_of_pauliCoeff_eq (B.2.1 e he) (B'.2.1 e he) fun a => h a ⟨e, he⟩
  apply Subtype.ext
  funext e
  by_cases he : e.IsPositivelyOriented
  · exact hp e he
  · have hr : e.opposite.IsPositivelyOriented := by
      rcases hOr e with h₁ | h₁
      · exact absurd h₁.1 he
      · exact h₁.1
    have h₂ := hp _ hr
    rw [B.2.2 e, B'.2.2 e] at h₂
    exact neg_injective h₂
theorem pauliCoeffs_injective (hL : 0 < L)
    (h₀ : Function.Surjective (LocalKernels.projPositiveEdge L n k 0))
    (hk : Function.Surjective (LocalKernels.projPositiveEdge L n k k))
    (hOr₀ : ∀ e : Edge L n k 0, Xor e.IsPositivelyOriented e.opposite.IsPositivelyOriented)
    (hOrk : ∀ e : Edge L n k k, Xor e.IsPositivelyOriented e.opposite.IsPositivelyOriented)
    {ζ ζ' : PeriodicField L n k} (h : ζ.pauliCoeffs hL = ζ'.pauliCoeffs hL) : ζ = ζ' := by
  refine Prod.ext (complexEdgeForm_ext hOr₀ fun a c => ?_)
    (Prod.ext (complexEdgeForm_ext hOr₀ fun a c => ?_) (complexEdgeForm_ext hOrk fun a c => ?_))
  · obtain ⟨b, rfl⟩ := h₀ c
    exact congrFun h ⟨FieldComponent.background, (a, b)⟩
  · obtain ⟨b, rfl⟩ := h₀ c
    exact congrFun h ⟨FieldComponent.source, (a, b)⟩
  · obtain ⟨b, rfl⟩ := hk c
    exact congrFun h ⟨FieldComponent.coarse, (a, b)⟩
end PlaneWave
section Expansion
variable {L k : ℕ}
theorem constantFieldAmplitude_expand (hL : 0 < L) (hT : ∀ N, ShiftSurjectiveOnEdges L k 0 N)
    (ξ : Fin 4 → ComplexMatrix2) (c : (fieldPeriodicData L k hL).UnitQuot) :
    constantFieldAmplitude L k hL ξ c =
      ∑ q : Fin 4 × Fin 3, pauliCoeff q.2 (ξ q.1) *
        constantFieldAmplitude L k hL (Pi.single q.1 (pauliFamily q.2)) c := by
  obtain ⟨ι, rfl⟩ : ∃ ι, (fieldPeriodicData L k hL).mkQuot 1 ι = c := Quot.exists_rep c
  obtain ⟨p, ι⟩ := ι
  cases p with
  | background =>
    have h₁ := fun (q : Fin 4 × Fin 3) =>
      constantFieldAmplitude_background hL hT (Pi.single q.1 (pauliFamily q.2)) ι.1 ι.2
    refine (constantFieldAmplitude_background hL hT ξ ι.1 ι.2).trans ?_
    have h₂ : ∀ q : Fin 4 × Fin 3, pauliCoeff q.2 (ξ q.1) *
        constantFieldAmplitude L k hL (Pi.single q.1 (pauliFamily q.2))
          ((fieldPeriodicData L k hL).mkQuot 1 ⟨FieldComponent.background, ι⟩) =
        pauliCoeff q.2 (ξ q.1) * pauliCoeff ι.1
          ((Pi.single q.1 (pauliFamily q.2) : Fin 4 → ComplexMatrix2) (edgeAxis ι.2)) := fun q =>
      congrArg (pauliCoeff q.2 (ξ q.1) * ·) (h₁ q)
    rw [Finset.sum_congr rfl fun q _ => h₂ q, Fintype.sum_prod_type,
      Finset.sum_eq_single (edgeAxis ι.2)]
    · simp [pauliCoeff_pauliFamily]
    · intro ν _ hν
      refine Finset.sum_eq_zero fun a _ => ?_
      rw [Pi.single_eq_of_ne hν.symm, pauliCoeff_zero, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h
  | source =>
    have h₀ := fun ξ' => constantFieldAmplitude_other hL ξ'
      (⟨FieldComponent.source, ι⟩ : FieldIdx L k hL) (Or.inl rfl)
    refine (h₀ ξ).trans (Finset.sum_eq_zero fun q _ => ?_).symm
    exact mul_eq_zero_of_right _ (h₀ _)
  | coarse =>
    have h₀ := fun ξ' => constantFieldAmplitude_other hL ξ'
      (⟨FieldComponent.coarse, ι⟩ : FieldIdx L k hL) (Or.inr rfl)
    refine (h₀ ξ).trans (Finset.sum_eq_zero fun q _ => ?_).symm
    exact mul_eq_zero_of_right _ (h₀ _)
theorem bilinear_sum_eq_zero {K Q : Type} [Fintype K] [Fintype Q] (g : K → K → ℂ) (ε : K → ℂ)
    (w : Q → ℂ) (A : Q → K → ℂ) (h : ∀ q, ∑ c, ∑ c', g c c' * A q c * ε c' = 0) :
    ∑ c, ∑ c', g c c' * (∑ q, w q * A q c) * ε c' = 0 := by
  have h₁ : ∀ c c', g c c' * (∑ q, w q * A q c) * ε c' =
      ∑ q, w q * (g c c' * A q c * ε c') := by
    intro c c'
    rw [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun q _ => by ring
  simp only [h₁]
  rw [Finset.sum_congr rfl fun c _ => Finset.sum_comm, Finset.sum_comm]
  refine Finset.sum_eq_zero fun q _ => ?_
  simp only [← Finset.mul_sum]
  rw [h q, mul_zero]
end Expansion
section Sides
variable {L n k : ℕ}
theorem torusSide_natCast (L n : ℕ) : ((2 * L ^ n : ℕ) : ℝ) = torusSide L n := by
  simp [torusSide]
theorem two_le_torusSide (hL : 0 < L) (n : ℕ) : 2 ≤ torusSide L n := by
  have h₁ : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have h₂ : (1 : ℝ) ≤ (L : ℝ) ^ n := one_le_pow₀ h₁
  simp only [torusSide]
  linarith
theorem axisMomentum_mem_dualLattice (ν : Fin 4) : axisMomentum L n ν ∈ dualLattice (2 * L ^ n) := by
  change ∃ c : Fin 4 → ℤ, ∀ μ, axisMomentum L n ν μ =
    (c μ : ℝ) * (2 * Real.pi / ((2 * L ^ n : ℕ) : ℝ))
  refine ⟨Pi.single ν 1, fun μ => ?_⟩
  rw [torusSide_natCast]
  by_cases h : μ = ν
  · subst h
    simp [axisMomentum]
  · simp [axisMomentum, Pi.single_eq_of_ne h]
theorem circlePhase_meshAt_sub_one_ne_zero (hL : 0 < L) :
    circlePhase L n (meshAt L k 0) - 1 ≠ 0 := by
  intro h
  have h₁ : circlePhase L n (meshAt L k 0) = 1 := sub_eq_zero.1 h
  rw [circlePhase, Complex.exp_eq_one_iff] at h₁
  obtain ⟨m, hm⟩ := h₁
  have hs := two_le_torusSide hL n
  have hs₀ : 0 < torusSide L n := by linarith
  have hη : 0 < meshAt L k 0 := zpow_pos (Nat.cast_pos.2 hL) _
  have hη₁ : meshAt L k 0 ≤ 1 :=
    zpow_le_one_of_nonpos₀ (by exact_mod_cast hL) (by simp)
  have hπ : (Real.pi : ℝ) ≠ 0 := Real.pi_ne_zero
  have h₂ : ((2 * Real.pi / torusSide L n * meshAt L k 0 : ℝ) : ℂ) =
      ((m * (2 * Real.pi) : ℝ) : ℂ) := by
    apply mul_right_cancel₀ Complex.I_ne_zero
    rw [hm]
    push_cast
    ring
  have h₃ : 2 * Real.pi / torusSide L n * meshAt L k 0 = m * (2 * Real.pi) := by
    exact_mod_cast h₂
  have h₄ : meshAt L k 0 / torusSide L n = m := by
    field_simp at h₃ ⊢
    nlinarith [h₃, Real.pi_pos]
  have h₅ : (0 : ℝ) < m := by
    rw [← h₄]
    positivity
  have h₆ : (m : ℝ) < 1 := by
    rw [← h₄, div_lt_one hs₀]
    linarith
  have h₇ : 0 < m := by exact_mod_cast h₅
  have h₈ : m < 1 := by exact_mod_cast h₆
  omega
theorem tendsto_torusSide (hL : 1 < L) : Tendsto (fun n => torusSide L n) atTop atTop := by
  have h : Tendsto (fun n : ℕ => (L : ℝ) ^ n) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by exact_mod_cast hL)
  exact h.const_mul_atTop two_pos
theorem tendsto_exp_decay (hL : 1 < L) (C c : ℝ) (hc : 0 < c) :
    Tendsto (fun n : ℕ => C * Real.exp (-c * ((2 * L ^ n : ℕ) : ℝ))) atTop (𝓝 0) := by
  simp only [torusSide_natCast]
  have h₁ : Tendsto (fun n => -c * torusSide L n) atTop atBot :=
    (tendsto_torusSide hL).const_mul_atTop_of_neg (by linarith)
  have h₂ := (Real.tendsto_exp_atBot.comp h₁).const_mul C
  simpa using h₂
theorem exists_of_eventuallyForSides (hL : 1 < L) {P : ℕ → Prop}
    (h : PeriodicOperators.Tempered.EventuallyForSides L P) :
    ∃ N, ∀ n, N ≤ n → 0 < n ∧ P n := by
  obtain ⟨s₀, ⟨m₀, hm₀, rfl⟩, hs⟩ := h
  refine ⟨m₀, fun n hn => ?_⟩
  have hn₀ : 0 < n := hm₀.trans_le hn
  refine ⟨hn₀, hs _ ⟨n, hn₀, rfl⟩ ?_ n hn₀ rfl⟩
  simp only [torusSide]
  have := pow_le_pow_right₀ (show (1 : ℝ) ≤ L by exact_mod_cast hL.le) hn
  linarith
theorem tendsto_toComplexVec_axisMomentum (hL : 1 < L) (ν : Fin 4) :
    Tendsto (fun n => toComplexVec (axisMomentum L n ν)) atTop (𝓝 0) := by
  have hc : Continuous fun t : ℝ => toComplexVec (Pi.single ν t) := by
    refine continuous_pi fun μ => ?_
    by_cases h : μ = ν
    · subst h
      simpa [toComplexVec] using Complex.continuous_ofReal
    · simpa [toComplexVec, Pi.single_eq_of_ne h] using continuous_const
  have h₀ : Tendsto (fun n => 2 * Real.pi / torusSide L n) atTop (𝓝 0) :=
    (tendsto_torusSide hL).const_div_atTop _
  have h₁ := (hc.tendsto 0).comp h₀
  have h₂ : toComplexVec (Pi.single ν (0 : ℝ)) = 0 := by
    funext μ
    by_cases h : μ = ν
    · subst h
      simp [toComplexVec]
    · simp [toComplexVec, Pi.single_eq_of_ne h]
  rw [h₂] at h₁
  exact h₁
theorem finite_positiveEdge (hL : 0 < L) (i : ℕ) : Finite (PositiveEdge L n k i) := by apply _root_.YangMills.SharedProofs.p11983 <;> assumption
end Sides
section Main
variable {L k : ℕ}
open LocalKernels.Periodisation (ProjEdgesCompatible ProjCellsClassified)
theorem xor_positive_reverse (hOr : PeriodicLattice.OppositeBonds.OppositeAndPositiveRestriction)
    (hS : Conventions.IsAdmissibleBlockingFactor L) {n i : ℕ} (hn : 0 < n) (hi : i ≤ k)
    (e : Edge L n k i) : Xor e.IsPositivelyOriented e.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.Tower.SecondDerivNearSymbol.xor_positive_opposite <;> assumption
theorem complexSecondDeriv_blochWaveField_eq_zero (hExt : HessianAndComplexExtensionHolds)
    (hOn : HessianVanishesOnGaugeDirections)
    (hCells : LocalKernels.PeriodicLiftCells.CellsAndClassesHold)
    (hTrans : FullLatticeOverTorus.FullLatticeOverTorusClaim)
    (hOr : PeriodicLattice.OppositeBonds.OppositeAndPositiveRestriction)
    (hL : 0 < L) (hS : Conventions.IsAdmissibleBlockingFactor L) (hk : 1 ≤ k) {n : ℕ} (hn : 0 < n)
    (ν : Fin 4) (a : Fin 3) (ζ : PeriodicField L n k) :
    complexSecondDeriv L n k
      (blochWaveField L n k hL (toComplexVec (axisMomentum L n ν))
        (constantFieldAmplitude L k hL (Pi.single ν (pauliFamily a)))) ζ = 0 := by
  have hb₀ : Finite (PositiveEdge L n k 0) := finite_positiveEdge hL 0
  have hbk : Finite (PositiveEdge L n k k) := finite_positiveEdge hL k
  let _ : Fintype (PositiveEdge L n k 0) := Fintype.ofFinite _
  let _ : Fintype (PositiveEdge L n k k) := Fintype.ofFinite _
  have e := hExt L n k hS hn hk
  have hc₀ := (hCells L hS k n hn).1 0 (Nat.zero_le k)
  have hck := (hCells L hS k n hn).1 k le_rfl
  have hT : ∀ N, ShiftSurjectiveOnEdges L k 0 N :=
    fun N => ((hTrans L hS k 0 (Nat.zero_le k) n hn).2.2.1 N).2.1
  have hwave := gradientWave_pauliCoeffs (n := n) hL hT hc₀.2 rfl
    (circlePhase_meshAt_sub_one_ne_zero hL) ν a
  have hspec := Classical.epsilon_spec
    (p := fun ζ' : PeriodicField L n k => ζ'.pauliCoeffs hL =
      blochWave (fieldPeriodicData L k hL) (toComplexVec (axisMomentum L n ν))
        (constantFieldAmplitude L k hL (Pi.single ν (pauliFamily a)))) ⟨_, hwave⟩
  have heq : blochWaveField L n k hL (toComplexVec (axisMomentum L n ν))
      (constantFieldAmplitude L k hL (Pi.single ν (pauliFamily a))) =
      gradientWave L n k (circlePhase L n (meshAt L k 0) - 1) ν a :=
    pauliCoeffs_injective hL (hc₀.1 .edge).1 (hck.1 .edge).1
      (xor_positive_reverse hOr hS hn (Nat.zero_le k)) (xor_positive_reverse hOr hS hn le_rfl)
      (hspec.trans hwave.symm)
  rw [heq]
  exact isComplexSecondDeriv_gradientWave_eq_zero hOn hS hn hk _ e.isComplexSecondDeriv _ ν a ζ
theorem zero_mem_interior_imStrip {δ : ℝ} (hδ : 0 < δ) :
    (0 : Fin 4 → ℂ) ∈ interior (imStrip δ) := by
  rw [mem_interior_iff_mem_nhds]
  have h₁ : ∀ μ : Fin 4, ∀ᶠ κ : Fin 4 → ℂ in 𝓝 0, |(κ μ).im| < δ := fun μ => by
    have hc : Continuous fun κ : Fin 4 → ℂ => |(κ μ).im| :=
      continuous_abs.comp (Complex.continuous_im.comp (continuous_apply μ))
    refine (hc.tendsto 0).eventually (Iio_mem_nhds ?_)
    simpa using hδ
  filter_upwards [eventually_all.2 h₁] with κ hκ μ
  exact (hκ μ).le
theorem toComplexVec_mem_imStrip {δ : ℝ} (hδ : 0 < δ) (y : AmbientSpace) :
    toComplexVec y ∈ imStrip δ := fun μ => by
  simpa [toComplexVec] using hδ.le
end Main
theorem norm_sub_le_of_two {X A B : ℂ} {u v : ℝ} (h₁ : ‖X - A‖ ≤ u) (h₂ : ‖X - B‖ ≤ v) :
    ‖A - B‖ ≤ u + v := by
  have h : A - B = (X - B) - (X - A) := by ring
  rw [h]
  exact (norm_sub_le _ _).trans (by linarith)
theorem symmetricAndKillsConstantForms_holds
    (hClose : SecondDerivNearSymbol.SecondDerivCloseToSymbol)
    (hExt : HessianAndComplexExtensionHolds)
    (hOn : HessianVanishesOnGaugeDirections)
    (hCoef : FullSpace.SymbolCoefficients.SymbolCoefficientsExist)
    (hWidth : FullSpace.JointWidthAndTransposeTheorem)
    (hCells : LocalKernels.PeriodicLiftCells.CellsAndClassesHold)
    (hPer : LocalKernels.IndexSetPeriodicity.Statement)
    (hTrans : FullLatticeOverTorus.FullLatticeOverTorusClaim)
    (hOr : PeriodicLattice.OppositeBonds.OppositeAndPositiveRestriction) :
    SymmetricAndKillsConstantForms := by
  intro L hL hS k hk
  have hL₁ : 1 < L := by
    have := hS.2
    omega
  obtain ⟨C, c, -, hc, hLarge⟩ := hClose L hL hS k hk
  obtain ⟨N, hN⟩ := exists_of_eventuallyForSides hL₁ hLarge
  have hR := tendsto_exp_decay hL₁ C c hc
  have hneg : -toComplexVec (0 : AmbientSpace) = 0 := by
    funext μ
    simp [toComplexVec]
  have hzero : toComplexVec (0 : AmbientSpace) = 0 := by
    funext μ
    simp [toComplexVec]
  have hsym : ∀ εPlus εMinus : (fieldPeriodicData L k hL).UnitQuot → ℂ,
      secondVariationSymbol L k hL 0 εPlus εMinus =
        secondVariationSymbol L k hL 0 εMinus εPlus := by
    intro εPlus εMinus
    set P := wNorm ((fieldPeriodicData L k hL).quotWeight 1) εPlus
    set M := wNorm ((fieldPeriodicData L k hL).quotWeight 1) εMinus
    have hb : ∀ n, N ≤ n → ‖secondVariationSymbol L k hL 0 εPlus εMinus -
        secondVariationSymbol L k hL 0 εMinus εPlus‖ ≤
        C * Real.exp (-c * ((2 * L ^ n : ℕ) : ℝ)) * P * M +
          C * Real.exp (-c * ((2 * L ^ n : ℕ) : ℝ)) * M * P := by
      intro n hn
      obtain ⟨hn₀, hP⟩ := hN n hn
      have h₁ := hP 0 (zero_mem _) εPlus εMinus
      have h₂ := hP 0 (zero_mem _) εMinus εPlus
      rw [hneg, hzero] at h₁ h₂
      have hb₀ : Finite (PositiveEdge L n k 0) := finite_positiveEdge hL 0
      have hbk : Finite (PositiveEdge L n k k) := finite_positiveEdge hL k
      let _ : Fintype (PositiveEdge L n k 0) := Fintype.ofFinite _
      let _ : Fintype (PositiveEdge L n k k) := Fintype.ofFinite _
      have e := hExt L n k hS hn₀ hk
      rw [e.complexSecondDeriv_symm] at h₂
      exact norm_sub_le_of_two h₁ h₂
    have hlim : Tendsto (fun n : ℕ => C * Real.exp (-c * ((2 * L ^ n : ℕ) : ℝ)) * P * M +
        C * Real.exp (-c * ((2 * L ^ n : ℕ) : ℝ)) * M * P) atTop (𝓝 0) := by
      simpa using ((hR.mul_const P).mul_const M).add ((hR.mul_const M).mul_const P)
    have h₀ := ge_of_tendsto hlim (eventually_atTop.2 ⟨N, hb⟩)
    exact sub_eq_zero.1 (norm_le_zero_iff.1 h₀)
  obtain ⟨hw, -⟩ := hWidth L hL hS k hk
  have hδ₀ : 0 < FullSpace.jointInvertibilityWidth L k hL := hw.1.1
  obtain ⟨δP, hδP, -, a, ha, hgive⟩ := hCoef L hL hS k hk _ hw
  have hδP₀ : 0 < δP := hδ₀.trans hδP
  have hfinite : Finite (fieldPeriodicData L k hL).UnitQuot :=
    ((hPer L hS k).2 (LocalKernels.fieldIndices L k hL)).1.finite_quot
  let _ := Fintype.ofFinite (fieldPeriodicData L k hL).UnitQuot
  have hsum : ∀ p ∈ imStrip (FullSpace.jointInvertibilityWidth L k hL),
      ∀ εPlus εMinus : (fieldPeriodicData L k hL).UnitQuot → ℂ,
      secondVariationSymbol L k hL p εPlus εMinus =
        ∑ c, ∑ c', a c c' p * εPlus c * εMinus c' := by
    intro p hp εPlus εMinus
    rw [hgive p hp εPlus εMinus, finsum_eq_sum_of_fintype]
    exact Finset.sum_congr rfl fun c _ => finsum_eq_sum_of_fintype _
  have hcont : ∀ c c', ContinuousAt (a c c') 0 := by
    intro c c'
    obtain ⟨ho, hcn, -⟩ := (ha c c').1
    have h₁ := (hcn.continuousAt
      (ho.mem_nhds (zero_mem_interior_imStrip hδP₀)))
    exact (continuous_apply (0 : Fin 1)).continuousAt.comp h₁
  have h0strip : (0 : Fin 4 → ℂ) ∈ imStrip (FullSpace.jointInvertibilityWidth L k hL) := by
    rw [← hzero]
    exact toComplexVec_mem_imStrip hδ₀ 0
  have hdir : ∀ (ν : Fin 4) (t : Fin 3) (ε : (fieldPeriodicData L k hL).UnitQuot → ℂ),
      secondVariationSymbol L k hL 0
        (constantFieldAmplitude L k hL (Pi.single ν (pauliFamily t))) ε = 0 := by
    intro ν t ε
    set A := constantFieldAmplitude L k hL (Pi.single ν (pauliFamily t))
    set P := wNorm ((fieldPeriodicData L k hL).quotWeight 1) A
    set M := wNorm ((fieldPeriodicData L k hL).quotWeight 1) ε
    have hΨ : ContinuousAt (fun p => ∑ c, ∑ c', a c c' p * A c * ε c') 0 := by
      refine tendsto_finsetSum _ fun c _ => tendsto_finsetSum _ fun c' _ => ?_
      exact ((hcont c c').tendsto.mul_const _).mul_const _
    have ht := hΨ.tendsto.comp (tendsto_toComplexVec_axisMomentum hL₁ ν)
    have hb : ∀ n, N ≤ n → ‖((fun p => ∑ c, ∑ c', a c c' p * A c * ε c') ∘
        fun n => toComplexVec (axisMomentum L n ν)) n‖ ≤
        C * Real.exp (-c * ((2 * L ^ n : ℕ) : ℝ)) * P * M := by
      intro n hn
      obtain ⟨hn₀, hP⟩ := hN n hn
      have h₁ := hP (axisMomentum L n ν) (axisMomentum_mem_dualLattice ν) A ε
      rw [complexSecondDeriv_blochWaveField_eq_zero hExt hOn hCells hTrans hOr hL hS hk hn₀,
        mul_zero, zero_sub, norm_neg, hsum _ (toComplexVec_mem_imStrip hδ₀ _)] at h₁
      exact h₁
    have hlim : Tendsto (fun n : ℕ => C * Real.exp (-c * ((2 * L ^ n : ℕ) : ℝ)) * P * M) atTop
        (𝓝 0) := by
      simpa using (hR.mul_const P).mul_const M
    have h₀ := le_of_tendsto_of_tendsto ht.norm hlim (eventually_atTop.2 ⟨N, hb⟩)
    rw [hsum 0 h0strip]
    exact norm_le_zero_iff.1 h₀
  have hT : ∀ N', ShiftSurjectiveOnEdges L k 0 N' :=
    fun N' => ((hTrans L hS k 0 (Nat.zero_le k) 1 one_pos).2.2.1 N').2.1
  refine ⟨hsym, fun ξ _ ε => ?_⟩
  have hz : secondVariationSymbol L k hL 0 (constantFieldAmplitude L k hL ξ) ε = 0 := by
    rw [hsum 0 h0strip]
    simp only [constantFieldAmplitude_expand hL hT ξ]
    refine bilinear_sum_eq_zero (fun c c' => a c c' 0) ε _ _ fun q => ?_
    rw [← hsum 0 h0strip]
    exact hdir q.1 q.2 ε
  exact ⟨hz, (hsym _ _).trans hz⟩
end YangMills.Construction.Tower.SymbolAtZero
end
