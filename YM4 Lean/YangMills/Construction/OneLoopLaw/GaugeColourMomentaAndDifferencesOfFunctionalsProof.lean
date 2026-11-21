import YangMills.Construction.Matrices.CalculusOfTheFieldsOnPowersOfGProof
import YangMills.Construction.Towers.FactsOfTheMatricesOfAPeriodicFunctionProof
import YangMills.Construction.Lattice.FormOnTheLieAlgebraAndTransposesProof
import YangMills.Construction.LawByMomentsOfTheFlow.HessianOfAStepOnEveryChainTorusProof
import YangMills.Construction.Matrices.UnitaryLogarithmClosedForm
import YangMills.Construction.OneLoopLaw.CoefficientOfATemperedFunctional
import YangMills.Construction.OneLoopLaw.FirstDerivativeOfAMemberVanishesProof
import YangMills.Construction.OneLoopLaw.CoefficientOfAFunctional
import YangMills.Construction.PeriodicOperators.RiemannSumsAndShifts
import Mathlib
import YangMills.Construction.OneLoopLaw.PlaneWavesUnderMotionsOfTheLatticeProof
import YangMills.Construction.OneLoopLaw.PolarisationOfAMember
import YangMills.Construction.OneLoopLaw.PolarisationOfBondFormsOnATorus
import YangMills.Construction.OneLoopLaw.PolarisationVanishesOnGaugeDirections
import YangMills.Construction.PeriodicLattice.WilsonMeasureIsometryInvarianceProof
import YangMills.Construction.PeriodicOperators.FunctionalDeterminesItsPolarisationSymbol
import YangMills.Construction.Towers.FactsOfTheLeftChart
set_option autoImplicit false

section
open Set
noncomputable section
namespace YangMills.Construction.OneLoopLaw.GaugeColourMomenta
variable {L : ℕ}
def FirstVariationVanishes (F : PeriodicOperators.Tempered.FieldFamily L) (n : ℕ) : Prop :=
  ∀ C ∈ Tower.edgeFormSpace L n 0 0,
    Tower.leftDeriv (k := 0) (j := 0) (F n) (PeriodicOperators.Tempered.identityField L n) C = 0
def HessianAdjointInvariant (F : PeriodicOperators.Tempered.FieldFamily L) (n : ℕ) : Prop :=
  ∀ g ∈ PeriodicLattice.compactGaugeGroup, ∀ A ∈ Tower.complexEdgeForms L n 0 0,
    ∀ A' ∈ Tower.complexEdgeForms L n 0 0,
      PeriodicOperators.Tempered.complexHessian F n (Tower.adjointForm (k := 0) (j := 0) (fun _ => g) A)
          (Tower.adjointForm (k := 0) (j := 0) (fun _ => g) A') =
        PeriodicOperators.Tempered.complexHessian F n A A'
def HessianKillsCoboundaries (F : PeriodicOperators.Tempered.FieldFamily L) (n : ℕ) : Prop :=
  ∀ φ : Tower.Vertex L n 0 0 → Matrices.ComplexMatrix2,
    (∀ x, φ x ∈ PeriodicLattice.complexLieAlgebra) →
    ∀ A' ∈ Tower.complexEdgeForms L n 0 0,
      PeriodicOperators.Tempered.complexHessian F n (Tower.vertexCoboundary (k := 0) (j := 0) φ) A' = 0
def HessianColourDiagonal (F : PeriodicOperators.Tempered.FieldFamily L) (n : ℕ) : Prop :=
  ∀ q ∈ PeriodicOperators.dualLattice (2 * L ^ n), ∀ μ ν : Fin 4, ∃ c : ℂ, ∀ a b : Fin 3,
    PeriodicOperators.Tempered.complexHessian F n
        (PeriodicOperators.Tempered.fourierModeForm L n a q μ)
        (PeriodicOperators.Tempered.fourierModeForm L n b (-q) ν) = if a = b then c else 0
def HessianVanishesOffAntipodal (F : PeriodicOperators.Tempered.FieldFamily L) (n : ℕ) : Prop :=
  ∀ (a b : Fin 3) (μ ν : Fin 4), ∀ q ∈ PeriodicOperators.dualLattice (2 * L ^ n),
    ∀ q' ∈ PeriodicOperators.dualLattice (2 * L ^ n),
      q + q' ∉ PeriodicOperators.RiemannSums.periodLattice →
        PeriodicOperators.Tempered.complexHessian F n
          (PeriodicOperators.Tempered.fourierModeForm L n a q μ)
          (PeriodicOperators.Tempered.fourierModeForm L n b q' ν) = 0
def HessianSymbolOfDifference (F F' : PeriodicOperators.Tempered.FieldFamily L) : Prop :=
  ∀ ξ ∈ PeriodicOperators.Tempered.symbolDomain L F ∩ PeriodicOperators.Tempered.symbolDomain L F',
    ξ ∈ PeriodicOperators.Tempered.symbolDomain L (F - F') ∧
      ∀ μ ν : Fin 4, PeriodicOperators.Tempered.hessianSymbol L (F - F') μ ν ξ =
        PeriodicOperators.Tempered.hessianSymbol L F μ ν ξ -
          PeriodicOperators.Tempered.hessianSymbol L F' μ ν ξ
def GaugeColourMomentumClaim : Prop :=
  ∀ (L : ℕ) (hL : 0 < L), Conventions.IsAdmissibleBlockingFactor L →
    (∀ F : PeriodicOperators.Tempered.FieldFamily L,
      PeriodicOperators.Tempered.IsLatticeFunctional L F →
      PeriodicOperators.Tempered.EventuallyForSides L fun n =>
        FirstVariationVanishes F n ∧ HessianAdjointInvariant F n ∧
          HessianKillsCoboundaries F n ∧ HessianColourDiagonal F n ∧
            HessianVanishesOffAntipodal F n) ∧
    ∀ F F' : PeriodicOperators.Tempered.FieldFamily L,
      PeriodicOperators.Tempered.IsTemperedFunctional L F →
      PeriodicOperators.Tempered.IsTemperedFunctional L F' →
        (PeriodicOperators.Tempered.EventuallyForSides L fun n =>
            PeriodicOperators.Tempered.IsAdmissibleMember (F n) ∧
              PeriodicOperators.Tempered.IsAdmissibleMember (F' n)) ∧
          PeriodicOperators.Tempered.IsTemperedFunctional L (F - F') ∧
            HessianSymbolOfDifference F F' ∧
              OneLoopLaw.FunctionalStiffness.stiffnessConstant hL (F - F') =
                OneLoopLaw.FunctionalStiffness.stiffnessConstant hL F -
                  OneLoopLaw.FunctionalStiffness.stiffnessConstant hL F'
end YangMills.Construction.OneLoopLaw.GaugeColourMomenta
end
end

open Set Filter
open scoped Topology ContDiff Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.OneLoopLaw.GaugeColourMomenta
open Tower PeriodicOperators PeriodicOperators.Tempered PeriodicOperators.RiemannSums Matrices
open Matrices.PowerExpCharts (expChartI)
open InfiniteLattice (AmbientSpace)
section EventualSides
variable {L : ℕ}
private theorem eventuallyForSides_mono {P Q : ℕ → Prop} (h : EventuallyForSides L P)
    (hpq : ∀ n, 0 < n → P n → Q n) : EventuallyForSides L Q := by
  obtain ⟨s₀, h₀, h⟩ := h
  exact ⟨s₀, h₀, fun s hs hle n hn e => hpq n hn (h s hs hle n hn e)⟩
private theorem eventuallyForSides_and {P Q : ℕ → Prop} (hP : EventuallyForSides L P)
    (hQ : EventuallyForSides L Q) : EventuallyForSides L fun n => P n ∧ Q n := by
  obtain ⟨s₀, h₀, h⟩ := hP
  obtain ⟨s₁, h₁, h'⟩ := hQ
  rcases le_total s₀ s₁ with hle | hle
  · exact ⟨s₁, h₁, fun s hs hs₁ n hn e => ⟨h s hs (hle.trans hs₁) n hn e, h' s hs hs₁ n hn e⟩⟩
  · exact ⟨s₀, h₀, fun s hs hs₀ n hn e => ⟨h s hs hs₀ n hn e, h' s hs (hle.trans hs₀) n hn e⟩⟩
abbrev _root_.YangMills.SharedProofs.p21504 := @eventuallyForSides_and
end EventualSides
section SecondDerivatives
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
private theorem deriv_deriv_line_eq_fderiv_fderiv {φ : V → ℝ} (h : ContDiffAt ℝ 2 φ 0)
    (Y Y' : V) :
    deriv (fun s : ℝ => deriv (fun t : ℝ => φ (s • Y + t • Y')) 0) 0 =
      fderiv ℝ (fderiv ℝ φ) 0 Y Y' := by apply _root_.YangMills.Construction.MomentLaw.TrivialHessian.deriv_deriv_two_param <;> assumption
private theorem fderiv_fderiv_sub {φ φ' : V → ℝ} (h : ContDiffAt ℝ 2 φ 0)
    (h' : ContDiffAt ℝ 2 φ' 0) :
    fderiv ℝ (fderiv ℝ fun x => φ x - φ' x) 0 =
      fderiv ℝ (fderiv ℝ φ) 0 - fderiv ℝ (fderiv ℝ φ') 0 := by
  have hd : ∀ᶠ x in 𝓝 (0 : V), DifferentiableAt ℝ φ x :=
    (h.eventually (by simp)).mono fun x hx => hx.differentiableAt (by simp)
  have hd' : ∀ᶠ x in 𝓝 (0 : V), DifferentiableAt ℝ φ' x :=
    (h'.eventually (by simp)).mono fun x hx => hx.differentiableAt (by simp)
  have he : (fderiv ℝ fun x => φ x - φ' x) =ᶠ[𝓝 0] fun x => fderiv ℝ φ x - fderiv ℝ φ' x := by
    filter_upwards [hd, hd'] with x hx hx'
    exact fderiv_fun_sub hx hx'
  have hD : DifferentiableAt ℝ (fderiv ℝ φ) 0 :=
    (h.fderiv_right (m := 1) (by norm_num)).differentiableAt (by simp)
  have hD' : DifferentiableAt ℝ (fderiv ℝ φ') 0 :=
    (h'.fderiv_right (m := 1) (by norm_num)).differentiableAt (by simp)
  rw [he.fderiv_eq]
  exact fderiv_fun_sub hD hD'
end SecondDerivatives
section HolomorphicDifferences
private theorem isHolomorphicIn_sub {N N' : ℕ} {O O' : Set (Coordinates.ComplexCoordinates N)}
    {f g : Coordinates.ComplexCoordinates N → Coordinates.ComplexCoordinates N'}
    (hf : Coordinates.ComplexCoordinates.IsHolomorphicIn O f)
    (hg : Coordinates.ComplexCoordinates.IsHolomorphicIn O' g) :
    Coordinates.ComplexCoordinates.IsHolomorphicIn (O ∩ O') fun z => f z - g z := by
  refine ⟨hf.1.inter hg.1, (hf.2.1.mono inter_subset_left).sub (hg.2.1.mono inter_subset_right),
    fun a ha j => ?_⟩
  filter_upwards [hf.2.2 a ha.1 j, hg.2.2 a ha.2 j] with ζ h h'
  exact h.sub h'
variable {σ : Type} [Fintype σ]
private abbrev toScalarCoord : ℂ ≃ Coordinates.ComplexCoordinates 1 :=
  (Equiv.funUnique (Fin 1) ℂ).symm
private theorem toScalarCoord_sub (z w : ℂ) :
    toScalarCoord (z - w) = toScalarCoord z - toScalarCoord w := by
  funext i
  rfl
private theorem holomorphicScalar_sub {b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless}
    {W W' : Set (σ ⊕ Empty → ComplexMatrix2)} {Φ Φ' : (σ ⊕ Empty → ComplexMatrix2) → ℂ}
    (h : PowerExpCharts.HolomorphicScalar b W Φ)
    (h' : PowerExpCharts.HolomorphicScalar b W' Φ') :
    PowerExpCharts.HolomorphicScalar b (W ∩ W') fun x => Φ x - Φ' x := by
  obtain ⟨⟨A, hA, rfl⟩, hc, hl⟩ := h
  obtain ⟨⟨A', hA', rfl⟩, hc', hl'⟩ := h'
  refine ⟨⟨A ∩ A', hA.inter hA', by ext x; simp only [mem_inter_iff]; tauto⟩, ?_, ?_⟩
  · have h1 := (hc.mono (inter_subset_left (t := A' ∩ _))).sub
      (hc'.mono (inter_subset_right (s := A ∩ _)))
    refine h1.congr fun x _ => ?_
    exact toScalarCoord_sub _ _
  · intro p hp
    obtain ⟨O, h0, hO, ⟨hO₁, hO₂⟩, hν⟩ := hl p hp.1
    obtain ⟨O', h0', hO', ⟨hO₁', hO₂'⟩, hν'⟩ := hl' p hp.2
    refine ⟨O ∩ O', ⟨h0, h0'⟩, fun X hX => ⟨hO X hX.1, hO' X hX.2⟩, ⟨?_, ?_⟩, fun ν => ?_⟩
    · exact fun X hX => hO₁ hX.1
    · intro X hX
      obtain ⟨s, hs, hB⟩ := hO₂ X hX.1
      obtain ⟨s', hs', hB'⟩ := hO₂' X hX.2
      exact ⟨min s s', lt_min hs hs', fun Y hY hn =>
        ⟨hB Y hY (hn.trans_le (min_le_left _ _)), hB' Y hY (hn.trans_le (min_le_right _ _))⟩⟩
    · have h1 := isHolomorphicIn_sub (hν ν) (hν' ν)
      have e : (toScalarCoord ∘ ((fun x => Φ x - Φ' x) ∘ GroupLieProduct.expChartAt p) ∘
          GroupLieProduct.tupleOfCoords b ν) = fun z =>
            (toScalarCoord ∘ (Φ ∘ GroupLieProduct.expChartAt p) ∘
              GroupLieProduct.tupleOfCoords b ν) z -
            (toScalarCoord ∘ (Φ' ∘ GroupLieProduct.expChartAt p) ∘
              GroupLieProduct.tupleOfCoords b ν) z := by
        funext z
        exact toScalarCoord_sub _ _
      rw [e]
      exact h1
end HolomorphicDifferences
section EdgeForms
variable {L n : ℕ}
private theorem opposite_positive_of_not {b : UnitEdge L n} (hb : ¬ b.IsPositivelyOriented) :
    b.opposite.IsPositivelyOriented := by apply _root_.YangMills.SharedProofs.p9846 <;> assumption
private theorem xor_positive_opposite (hL : 2 ≤ L) (hn : 0 < n) (b : UnitEdge L n) :
    Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented :=
  PeriodicLattice.MatrixValued.xor_isPositivelyOriented_opposite (L := L) (m := n)
    (j := PeriodicLattice.levelDepth 0 0)
    (by omega) (by simp [PeriodicLattice.levelDepth]; omega) b
private theorem extendOddly_mem_complex (hL : 2 ≤ L) (hn : 0 < n)
    {f : UnitEdge L n → ComplexMatrix2}
    (hf : ∀ b : UnitEdge L n, b.IsPositivelyOriented → f b ∈ ComplexMatrix2.traceless) :
    extendOddly (k := 0) (j := 0) f ∈ complexEdgeForms L n 0 0 := by
  have hrr : ∀ b : UnitEdge L n, b.opposite.opposite = b :=
    fun b => PeriodicLattice.Bond.ext rfl rfl
  refine ⟨fun b hb => ?_, fun b => ?_⟩
  · simp only [extendOddly, if_pos hb]
    exact hf b hb
  · by_cases h : b.IsPositivelyOriented
    · have hr : ¬b.opposite.IsPositivelyOriented := by
        rcases xor_positive_opposite hL hn b with ⟨-, h'⟩ | ⟨-, h'⟩
        · exact h'
        · exact absurd h h'
      simp only [extendOddly, if_pos h, if_neg hr, hrr]
    · simp only [extendOddly, if_neg h, if_pos (opposite_positive_of_not h), neg_neg]
private abbrev constAdjoint (v : ComplexMatrix2) (B : UnitEdge L n → ComplexMatrix2) :
    UnitEdge L n → ComplexMatrix2 :=
  adjointForm (k := 0) (j := 0) (fun _ => v) B
private def modeForm (L n : ℕ) (p : AmbientSpace) (μ : Fin 4) (X : ComplexMatrix2) :
    UnitEdge L n → ComplexMatrix2 :=
  open Classical in
  extendOddly (k := 0) (j := 0) fun b =>
    if b.target - b.source = PeriodicLattice.unitStep L n _ μ then
      phase p (b.source : PeriodicLattice.FourTorus L n) • X
    else 0
private theorem fourierModeForm_eq_modeForm (a : Fin 3) (p : AmbientSpace) (μ : Fin 4) :
    fourierModeForm L n a p μ = modeForm L n p μ (ComplexMatrix2.pauliFamily a) := rfl
private theorem modeForm_mem (hL : 2 ≤ L) (hn : 0 < n) (p : AmbientSpace) (μ : Fin 4)
    {X : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.traceless) :
    modeForm L n p μ X ∈ complexEdgeForms L n 0 0 := by
  refine extendOddly_mem_complex hL hn fun b _ => ?_
  split_ifs
  · exact ComplexMatrix2.traceless.smul_mem _ hX
  · exact ComplexMatrix2.traceless.zero_mem
private theorem modeForm_smul (c : ℂ) (p : AmbientSpace) (μ : Fin 4) (X : ComplexMatrix2) :
    modeForm L n p μ (c • X) = c • modeForm L n p μ X := by
  funext b
  simp only [modeForm, extendOddly, Pi.smul_apply]
  split_ifs <;> simp [smul_smul, mul_comm]
private theorem conj_smul (v : ComplexMatrix2) (c : ℂ) (X : ComplexMatrix2) :
    ComplexMatrix2.conjugateBy v (c • X) = c • ComplexMatrix2.conjugateBy v X := by apply _root_.YangMills.Construction.LieInnerProductProof.conjugateBy_smul <;> assumption
private theorem conj_zero (v : ComplexMatrix2) : ComplexMatrix2.conjugateBy v 0 = 0 := by
  simp [ComplexMatrix2.conjugateBy]
private theorem conj_neg (v X : ComplexMatrix2) :
    ComplexMatrix2.conjugateBy v (-X) = -ComplexMatrix2.conjugateBy v X := by
  simp [ComplexMatrix2.conjugateBy]
private theorem conj_add (v X Y : ComplexMatrix2) :
    ComplexMatrix2.conjugateBy v (X + Y) =
      ComplexMatrix2.conjugateBy v X + ComplexMatrix2.conjugateBy v Y := by
  simp [ComplexMatrix2.conjugateBy, mul_add, add_mul]
private theorem constAdjoint_modeForm (v : ComplexMatrix2) (p : AmbientSpace) (μ : Fin 4)
    (X : ComplexMatrix2) :
    constAdjoint v (modeForm L n p μ X) = modeForm L n p μ (ComplexMatrix2.conjugateBy v X) := by
  funext b
  by_cases hb : b.IsPositivelyOriented
  · simp only [constAdjoint, adjointForm, modeForm, extendOddly, if_pos hb]
    split_ifs <;> simp [conj_smul, conj_zero]
  · have hr := opposite_positive_of_not hb
    simp only [constAdjoint, adjointForm, modeForm, extendOddly, if_neg hb, if_pos hr]
    split_ifs <;> simp [conj_smul, conj_zero]
private theorem comp_constAdjoint (v : ComplexMatrix2) (φ : ComplexMatrix2 → ComplexMatrix2)
    (hodd : ∀ X, φ (-X) = -φ X)
    (hφ : ∀ X, φ (ComplexMatrix2.conjugateBy v X) = ComplexMatrix2.conjugateBy v (φ X))
    (B : UnitEdge L n → ComplexMatrix2) :
    (fun b => φ (constAdjoint v B b)) = constAdjoint v fun b => φ (B b) := by
  funext b
  simp only [constAdjoint, adjointForm, extendOddly]
  split_ifs <;> simp [hodd, hφ]
private theorem constAdjoint_linComb (v : ComplexMatrix2) (a c : ℂ)
    (R R' : UnitEdge L n → ComplexMatrix2) :
    constAdjoint v (a • R + c • R') = a • constAdjoint v R + c • constAdjoint v R' := by
  funext b
  simp only [constAdjoint, adjointForm, extendOddly, Pi.add_apply, Pi.smul_apply, conj_add,
    conj_smul]
  split_ifs <;> simp [add_comm]
private theorem hermPart_mem {X : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.traceless) :
    (2⁻¹ : ℂ) • (X + X.conjTranspose) ∈ ComplexMatrix2.hermitianTraceless := by
  have ht : Matrix.trace X = 0 := hX
  refine ⟨?_, ?_⟩
  · simp [Matrix.conjTranspose_smul, Matrix.conjTranspose_add, add_comm]
  · simp [ComplexMatrix2.fullTrace, Matrix.trace_smul, Matrix.trace_add,
      Matrix.trace_conjTranspose, ht]
abbrev _root_.YangMills.SharedProofs.p48895 := @hermPart_mem
private theorem antiHermPart_mem {X : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.traceless) :
    (2 * Complex.I)⁻¹ • (X - X.conjTranspose) ∈ ComplexMatrix2.hermitianTraceless := by
  have ht : Matrix.trace X = 0 := hX
  have hc : star ((2 * Complex.I)⁻¹ : ℂ) = -(2 * Complex.I)⁻¹ := by
    simp [Complex.conj_I]
  refine ⟨?_, ?_⟩
  · rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.conjTranspose_conjTranspose,
      hc, neg_smul, ← smul_neg, neg_sub]
  · simp [ComplexMatrix2.fullTrace, Matrix.trace_smul, Matrix.trace_sub,
      Matrix.trace_conjTranspose, ht]
abbrev _root_.YangMills.SharedProofs.p51273 := @antiHermPart_mem
private theorem realComponent_mem {B : UnitEdge L n → ComplexMatrix2}
    (hB : B ∈ complexEdgeForms L n 0 0) : realComponent B ∈ edgeFormSpace L n 0 0 := by
  refine ⟨fun b hb => hermPart_mem (hB.1 b hb), fun b => ?_⟩
  simp only [realComponent, hB.2 b, Matrix.conjTranspose_neg, ← neg_add, smul_neg]
abbrev _root_.YangMills.SharedProofs.p16359 := @realComponent_mem
private theorem imagComponent_mem {B : UnitEdge L n → ComplexMatrix2}
    (hB : B ∈ complexEdgeForms L n 0 0) : imagComponent B ∈ edgeFormSpace L n 0 0 := by
  refine ⟨fun b hb => antiHermPart_mem (hB.1 b hb), fun b => ?_⟩
  simp only [imagComponent, hB.2 b, Matrix.conjTranspose_neg, sub_neg_eq_add, ← smul_neg,
    neg_sub, neg_add_eq_sub]
abbrev _root_.YangMills.SharedProofs.p9724 := @imagComponent_mem
private theorem mem_complex_of_mem_real {R : UnitEdge L n → ComplexMatrix2}
    (hR : R ∈ edgeFormSpace L n 0 0) : R ∈ complexEdgeForms L n 0 0 :=
  ⟨fun b hb => (hR.1 b hb).2, hR.2⟩
abbrev _root_.YangMills.DeltaSharedProofs.p8199 := @mem_complex_of_mem_real
private theorem expTwist_identity {X : UnitEdge L n → ComplexMatrix2}
    (hX : ∀ b : UnitEdge L n, X b.opposite = -X b) :
    PeriodicLattice.expTwist X (identityField L n) =
      fun b => ComplexMatrix2.matExp (Complex.I • X b) := by
  funext b
  by_cases hb : b.IsPositivelyOriented
  · simp [PeriodicLattice.expTwist, hb, identityField]
  · simp only [PeriodicLattice.expTwist, hb, if_false, identityField, mul_one, hX b, smul_neg]
    rw [← Matrix.exp_neg, neg_neg]
abbrev _root_.YangMills.SharedProofs.p79696 := @expTwist_identity
private theorem value_mem_hermitianTraceless {X : UnitEdge L n → ComplexMatrix2}
    (hX : X ∈ edgeFormSpace L n 0 0) (b : UnitEdge L n) :
    X b ∈ ComplexMatrix2.hermitianTraceless := by
  by_cases hb : b.IsPositivelyOriented
  · exact hX.1 b hb
  · have h := ComplexMatrix2.hermitianTraceless.neg_mem (hX.1 _ (opposite_positive_of_not hb))
    rwa [hX.2 b, neg_neg] at h
abbrev _root_.YangMills.DeltaSharedProofs.p500934 := @value_mem_hermitianTraceless
private theorem expTwist_mem_fieldSpace
    (hexp : ∀ Y ∈ ComplexMatrix2.hermitianTraceless,
      ComplexMatrix2.matExp (Complex.I • Y) ∈ ComplexMatrix2.specialUnitary)
    {X : UnitEdge L n → ComplexMatrix2} (hX : X ∈ edgeFormSpace L n 0 0) :
    PeriodicLattice.expTwist X (identityField L n) ∈ fieldSpace L n 0 0 := by
  rw [expTwist_identity hX.2]
  refine ⟨fun b _ => hexp _ (value_mem_hermitianTraceless hX b), fun b _ => ?_⟩
  simp only [hX.2 b, smul_neg]
  exact Matrix.exp_neg _
abbrev _root_.YangMills.SharedProofs.p92839 := @expTwist_mem_fieldSpace
private theorem identityField_mem :
    identityField L n ∈ fieldsIn L n 0 0 PeriodicLattice.complexGaugeGroup := by
  refine ⟨fun b _ => ?_, fun b _ => ?_⟩
  · simp [identityField, ComplexMatrix2.unitDeterminant]
  · simp [identityField]
abbrev _root_.YangMills.DeltaSharedProofs.p33329 := @identityField_mem
private theorem fieldOfPositiveValues_exp (X : UnitEdge L n → ComplexMatrix2) :
    fieldOfPositiveValues (k := 0) (j := 0)
        (fun b : PositiveUnitEdge L n => ComplexMatrix2.matExp (Complex.I • X b.1) * 1) =
      PeriodicLattice.expTwist X (identityField L n) := by
  funext b
  unfold fieldOfPositiveValues PeriodicLattice.expTwist
  by_cases hb : b.IsPositivelyOriented
  · simp [hb, identityField]
  · simp [hb, opposite_positive_of_not hb, identityField]
abbrev _root_.YangMills.SharedProofs.p49750 := @fieldOfPositiveValues_exp
private def lieValues (B : UnitEdge L n → ComplexMatrix2) (hB : B ∈ edgeFormSpace L n 0 0) :
    PositiveUnitEdge L n → ComplexMatrix2.LieElement :=
  fun b => (⟨B b.1, hB.1 b.1 b.2⟩ : ComplexMatrix2.hermitianTraceless)
private theorem exists_smooth_chart (hc : PowerExpCharts.ExpChartsStatement)
    (hp : OneLoop.PauliMatrixRelations) [inst₀ : Fintype (PositiveUnitEdge L n)]
    {f : (UnitEdge L n → ComplexMatrix2) → ℝ} (hF : IsAdmissibleMember f) :
    ∃ φ : (PositiveUnitEdge L n → ComplexMatrix2.LieElement) → ℝ, ContDiffAt ℝ 2 φ 0 ∧
      ∀ (B : UnitEdge L n → ComplexMatrix2) (hB : B ∈ edgeFormSpace L n 0 0)
        (B' : UnitEdge L n → ComplexMatrix2) (hB' : B' ∈ edgeFormSpace L n 0 0) (s t : ℝ),
        f (PeriodicLattice.expTwist (algebraMap ℝ ℂ s • B + algebraMap ℝ ℂ t • B')
            (identityField L n)) =
          φ (s • lieValues B hB + t • lieValues B' hB') := by
  obtain ⟨inst, O, hO, h1, hf⟩ := hF.analytic
  obtain rfl : inst = inst₀ := Subsingleton.elim _ _
  obtain ⟨β, -⟩ := hp.2.2.2.1
  have : Nonempty (PositiveUnitEdge L n) :=
    ⟨⟨PeriodicLattice.Bond.forwardFrom 0 0, 0, by simp [PeriodicLattice.Bond.forwardFrom]⟩⟩
  obtain ⟨hcharts, -, -, -, -, -, -, hread⟩ := hc (PositiveUnitEdge L n) Unit
  set p₀ : PositiveUnitEdge L n → ComplexMatrix2 := fun _ => 1 with hp₀
  have hp₀G : p₀ ∈ specialUnitaryPower (PositiveUnitEdge L n) := by
    obtain ⟨O', -, e⟩ := hO
    rw [e] at h1
    exact h1.2
  have hchart : ∀ Y, expChartI p₀ Y =
      fun s => ComplexMatrix2.matExp (Complex.I • (Y s).toMatrix) * p₀ s :=
    fun Y => ((hcharts p₀ hp₀G).2.1 Y).2.1
  obtain ⟨N, hN, -, hsmooth, -⟩ := (((hread β).1 O hO).1 _ (hf β)).1.1 p₀ h1
  refine ⟨(fun w => f (fieldOfPositiveValues (k := 0) (j := 0) w)) ∘ expChartI p₀,
    (hsmooth.contDiffAt hN).of_le (WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤)),
    fun B hB B' hB' s t => ?_⟩
  rw [← fieldOfPositiveValues_exp]
  simp only [Function.comp, hchart]
  congr 2
private theorem hessianAtIdentity_sub (hc : PowerExpCharts.ExpChartsStatement)
    (hp : OneLoop.PauliMatrixRelations) {F F' : FieldFamily L} (hF : IsAdmissibleMember (F n))
    (hF' : IsAdmissibleMember (F' n)) {R R' : UnitEdge L n → ComplexMatrix2}
    (hR : R ∈ edgeFormSpace L n 0 0) (hR' : R' ∈ edgeFormSpace L n 0 0) :
    hessianAtIdentity (F - F') n R R' =
      hessianAtIdentity F n R R' - hessianAtIdentity F' n R R' := by
  obtain ⟨inst, -⟩ := hF.analytic
  obtain ⟨φ, h2, hφ⟩ := exists_smooth_chart hc hp hF
  obtain ⟨φ', h2', hφ'⟩ := exists_smooth_chart hc hp hF'
  have e₁ : hessianAtIdentity F n R R' =
      fderiv ℝ (fderiv ℝ φ) 0 (lieValues R hR) (lieValues R' hR') := by
    unfold hessianAtIdentity leftSecondDeriv mixedDirectionalDeriv
    simp only [hφ R hR R' hR']
    exact deriv_deriv_line_eq_fderiv_fderiv h2 _ _
  have e₂ : hessianAtIdentity F' n R R' =
      fderiv ℝ (fderiv ℝ φ') 0 (lieValues R hR) (lieValues R' hR') := by
    unfold hessianAtIdentity leftSecondDeriv mixedDirectionalDeriv
    simp only [hφ' R hR R' hR']
    exact deriv_deriv_line_eq_fderiv_fderiv h2' _ _
  have e₃ : hessianAtIdentity (F - F') n R R' =
      fderiv ℝ (fderiv ℝ fun x => φ x - φ' x) 0 (lieValues R hR) (lieValues R' hR') := by
    unfold hessianAtIdentity leftSecondDeriv mixedDirectionalDeriv
    simp only [Pi.sub_apply, hφ R hR R' hR', hφ' R hR R' hR']
    exact deriv_deriv_line_eq_fderiv_fderiv (h2.sub h2') _ _
  rw [e₁, e₂, e₃, fderiv_fderiv_sub h2 h2']
  rfl
private theorem complexHessian_sub (hc : PowerExpCharts.ExpChartsStatement)
    (hp : OneLoop.PauliMatrixRelations) {F F' : FieldFamily L} (hF : IsAdmissibleMember (F n))
    (hF' : IsAdmissibleMember (F' n)) {B B' : UnitEdge L n → ComplexMatrix2}
    (hB : B ∈ complexEdgeForms L n 0 0) (hB' : B' ∈ complexEdgeForms L n 0 0) :
    complexHessian (F - F') n B B' = complexHessian F n B B' - complexHessian F' n B B' := by
  have a₁ := realComponent_mem hB
  have a₂ := imagComponent_mem hB
  have a₃ := realComponent_mem hB'
  have a₄ := imagComponent_mem hB'
  simp only [complexHessian]
  rw [hessianAtIdentity_sub hc hp hF hF' a₁ a₃, hessianAtIdentity_sub hc hp hF hF' a₂ a₄,
    hessianAtIdentity_sub hc hp hF hF' a₁ a₄, hessianAtIdentity_sub hc hp hF hF' a₂ a₃]
  push_cast
  ring
end EdgeForms
section ConstantGauge
variable {L n : ℕ}
private theorem inv_eq_star_of_mem {v : ComplexMatrix2}
    (hv : v ∈ PeriodicLattice.compactGaugeGroup) : v⁻¹ = star v := by apply _root_.YangMills.Construction.PeriodicLattice.IsometryInvariance.inv_eq_star_of_mem <;> assumption
private theorem det_eq_one_of_mem {v : ComplexMatrix2}
    (hv : v ∈ PeriodicLattice.compactGaugeGroup) : v.det = 1 := by apply _root_.YangMills.SharedProofs.p157 <;> assumption
private theorem conj_conjTranspose {v : ComplexMatrix2}
    (hv : v ∈ PeriodicLattice.compactGaugeGroup) (X : ComplexMatrix2) :
    (ComplexMatrix2.conjugateBy v X).conjTranspose =
      ComplexMatrix2.conjugateBy v X.conjTranspose := by
  simp only [ComplexMatrix2.conjugateBy, inv_eq_star_of_mem hv, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, mul_assoc]
private theorem realComponent_constAdjoint {v : ComplexMatrix2}
    (hv : v ∈ PeriodicLattice.compactGaugeGroup) (B : UnitEdge L n → ComplexMatrix2) :
    realComponent (constAdjoint v B) = constAdjoint v (realComponent B) := by
  refine comp_constAdjoint v (fun X => (2⁻¹ : ℂ) • (X + X.conjTranspose)) (fun X => ?_)
    (fun X => ?_) B
  · simp only [Matrix.conjTranspose_neg, ← neg_add, smul_neg]
  · simp only [conj_conjTranspose hv, conj_smul, conj_add]
private theorem imagComponent_constAdjoint {v : ComplexMatrix2}
    (hv : v ∈ PeriodicLattice.compactGaugeGroup) (B : UnitEdge L n → ComplexMatrix2) :
    imagComponent (constAdjoint v B) = constAdjoint v (imagComponent B) := by
  refine comp_constAdjoint v (fun X => (2 * Complex.I)⁻¹ • (X - X.conjTranspose)) (fun X => ?_)
    (fun X => ?_) B
  · simp only [Matrix.conjTranspose_neg, sub_neg_eq_add, ← smul_neg, neg_sub, neg_add_eq_sub]
  · simp only [conj_conjTranspose hv, conj_smul, sub_eq_add_neg, conj_add, conj_neg]
private theorem expTwist_constAdjoint (hgauge : LeftChartFacts.GaugeEquivarianceForms L n 0 0)
    {v : ComplexMatrix2} (hv : v ∈ PeriodicLattice.compactGaugeGroup)
    {C : UnitEdge L n → ComplexMatrix2} (hC : C ∈ complexEdgeForms L n 0 0) :
    PeriodicLattice.expTwist (constAdjoint v C) (identityField L n) =
      PeriodicLattice.gaugeTransform (fun _ : Vertex L n 0 0 => v)
        (PeriodicLattice.expTwist C (identityField L n)) := by
  have hu : PeriodicLattice.IsGaugeMap PeriodicLattice.complexGaugeGroup
      (fun _ : Vertex L n 0 0 => v) := fun _ => by
    simpa [ComplexMatrix2.unitDeterminant] using det_eq_one_of_mem hv
  have h := (hgauge (fun _ => v) hu).1 _ identityField_mem C hC
  have hone : PeriodicLattice.gaugeTransform (fun _ : Vertex L n 0 0 => v) (identityField L n) =
      identityField L n := by
    funext b
    simp only [PeriodicLattice.gaugeTransform, identityField, mul_one]
    exact Matrix.mul_nonsing_inv _ (by simp [det_eq_one_of_mem hv])
  rw [hone] at h
  exact h
private theorem hessianAtIdentity_constAdjoint
    (hexp : ∀ Y ∈ ComplexMatrix2.hermitianTraceless,
      ComplexMatrix2.matExp (Complex.I • Y) ∈ ComplexMatrix2.specialUnitary)
    (hgauge : LeftChartFacts.GaugeEquivarianceForms L n 0 0) {F : FieldFamily L}
    (hF : IsAdmissibleMember (F n)) {v : ComplexMatrix2}
    (hv : v ∈ PeriodicLattice.compactGaugeGroup)
    {R R' : UnitEdge L n → ComplexMatrix2} (hR : R ∈ edgeFormSpace L n 0 0)
    (hR' : R' ∈ edgeFormSpace L n 0 0) :
    hessianAtIdentity F n (constAdjoint v R) (constAdjoint v R') =
      hessianAtIdentity F n R R' := by
  have hcomb : ∀ p : ℝ × ℝ,
      algebraMap ℝ ℂ p.1 • R + algebraMap ℝ ℂ p.2 • R' ∈ edgeFormSpace L n 0 0 := by
    intro p
    rw [algebraMap_smul, algebraMap_smul]
    exact (edgeFormSpace L n 0 0).add_mem ((edgeFormSpace L n 0 0).smul_mem _ hR)
      ((edgeFormSpace L n 0 0).smul_mem _ hR')
  have htend : Tendsto (fun p : ℝ × ℝ => PeriodicLattice.expTwist
        (algebraMap ℝ ℂ p.1 • R + algebraMap ℝ ℂ p.2 • R') (identityField L n))
      (𝓝 (0, 0)) (𝓝[fieldSpace L n 0 0] fun _ => (1 : ComplexMatrix2)) := by
    refine tendsto_nhdsWithin_iff.2
      ⟨?_, Eventually.of_forall fun p => expTwist_mem_fieldSpace hexp (hcomb p)⟩
    refine tendsto_pi_nhds.2 fun b => ?_
    simp only [expTwist_identity (hcomb _).2]
    have hc : Continuous fun p : ℝ × ℝ => ComplexMatrix2.matExp (Complex.I •
        ((algebraMap ℝ ℂ p.1 • R + algebraMap ℝ ℂ p.2 • R') b)) := by
      let _ : NormedAlgebra ℚ ComplexMatrix2 := NormedAlgebra.restrictScalars ℚ ℂ ComplexMatrix2
      refine NormedSpace.exp_continuous.comp ?_
      simp only [Pi.add_apply, Pi.smul_apply]
      fun_prop
    have h0 := hc.tendsto ((0 : ℝ), (0 : ℝ))
    simpa using h0
  have hkey : ∀ᶠ p : ℝ × ℝ in 𝓝 (0, 0),
      F n (PeriodicLattice.expTwist
          (algebraMap ℝ ℂ p.1 • constAdjoint v R + algebraMap ℝ ℂ p.2 • constAdjoint v R')
          (identityField L n)) =
        F n (PeriodicLattice.expTwist (algebraMap ℝ ℂ p.1 • R + algebraMap ℝ ℂ p.2 • R')
          (identityField L n)) := by
    filter_upwards [htend.eventually hF.globalGauge] with p hp
    rw [← constAdjoint_linComb v _ _ R R',
      expTwist_constAdjoint hgauge hv (mem_complex_of_mem_real (hcomb p))]
    exact hp v hv
  have hcurry := hkey.curry_nhds
  have hinner : (fun s : ℝ => deriv (fun t : ℝ => F n (PeriodicLattice.expTwist
        (algebraMap ℝ ℂ s • constAdjoint v R + algebraMap ℝ ℂ t • constAdjoint v R')
        (identityField L n))) 0) =ᶠ[𝓝 0]
      fun s : ℝ => deriv (fun t : ℝ => F n (PeriodicLattice.expTwist
        (algebraMap ℝ ℂ s • R + algebraMap ℝ ℂ t • R') (identityField L n))) 0 := by
    filter_upwards [hcurry] with s hs
    exact Filter.EventuallyEq.deriv_eq hs
  exact hinner.deriv_eq
private theorem complexHessian_constAdjoint
    (hexp : ∀ Y ∈ ComplexMatrix2.hermitianTraceless,
      ComplexMatrix2.matExp (Complex.I • Y) ∈ ComplexMatrix2.specialUnitary)
    (hgauge : LeftChartFacts.GaugeEquivarianceForms L n 0 0) {F : FieldFamily L}
    (hF : IsAdmissibleMember (F n)) {v : ComplexMatrix2}
    (hv : v ∈ PeriodicLattice.compactGaugeGroup)
    {B B' : UnitEdge L n → ComplexMatrix2} (hB : B ∈ complexEdgeForms L n 0 0)
    (hB' : B' ∈ complexEdgeForms L n 0 0) :
    complexHessian F n (constAdjoint v B) (constAdjoint v B') = complexHessian F n B B' := by
  have hrp := fun {R R' : UnitEdge L n → ComplexMatrix2} (hR : R ∈ edgeFormSpace L n 0 0)
      (hR' : R' ∈ edgeFormSpace L n 0 0) => hessianAtIdentity_constAdjoint hexp hgauge hF hv hR hR'
  have a₁ := realComponent_mem hB
  have a₂ := imagComponent_mem hB
  have a₃ := realComponent_mem hB'
  have a₄ := imagComponent_mem hB'
  simp only [complexHessian]
  rw [realComponent_constAdjoint hv B, imagComponent_constAdjoint hv B,
    realComponent_constAdjoint hv B', imagComponent_constAdjoint hv B', hrp a₁ a₃, hrp a₂ a₄,
    hrp a₁ a₄, hrp a₂ a₃]
end ConstantGauge
section PauliSymmetries
private theorem pauliFamily_mul_self (a : Fin 3) :
    ComplexMatrix2.pauliFamily a * ComplexMatrix2.pauliFamily a = 1 := by apply _root_.YangMills.Construction.SpinHarmonics.FieldCalculus.pauli_mul_self <;> assumption
private theorem pauliFamily_conjTranspose (a : Fin 3) :
    (ComplexMatrix2.pauliFamily a).conjTranspose = ComplexMatrix2.pauliFamily a := by apply _root_.YangMills.Construction.Tower.PeriodicMultiplierMatrices.pauliFamily_conjTranspose <;> assumption
private theorem pauliFamily_mem_traceless (a : Fin 3) :
    ComplexMatrix2.pauliFamily a ∈ ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.OneLoopLaw.PlaneWaveSymmetries.pauliFamily_mem_traceless <;> assumption
private theorem pauliFamily_anticomm {a b : Fin 3} (h : a ≠ b) :
    ComplexMatrix2.pauliFamily a * ComplexMatrix2.pauliFamily b =
      -(ComplexMatrix2.pauliFamily b * ComplexMatrix2.pauliFamily a) := by
  ext i j
  fin_cases a <;> fin_cases b <;> first
    | exact absurd rfl h
    | (fin_cases i <;> fin_cases j <;>
        simp [ComplexMatrix2.pauliFamily, OneLoop.pauliX, OneLoop.pauliY,
          OneLoop.pauliZ, Matrix.mul_apply, Fin.sum_univ_two])
private theorem pauliFamily_det (a : Fin 3) : (ComplexMatrix2.pauliFamily a).det = -1 := by
  fin_cases a <;>
    simp [ComplexMatrix2.pauliFamily, OneLoop.pauliX, OneLoop.pauliY,
      OneLoop.pauliZ, Matrix.det_fin_two]
private theorem pauliFamily_add_det {a b : Fin 3} (h : a ≠ b) :
    (ComplexMatrix2.pauliFamily a + ComplexMatrix2.pauliFamily b).det = -2 := by
  fin_cases a <;> fin_cases b <;> first
    | exact absurd rfl h
    | (simp [ComplexMatrix2.pauliFamily, OneLoop.pauliX, OneLoop.pauliY,
          OneLoop.pauliZ, Matrix.det_fin_two]
       try ring_nf
       try simp
       try norm_num)
private theorem I_smul_mul_negI_smul {m : ComplexMatrix2} (hm : m * m = 1) :
    (Complex.I • m) * ((-Complex.I) • m) = 1 := by
  rw [smul_mul_smul_comm, hm]
  simp
private theorem conj_I_smul {m : ComplexMatrix2} (hm : m * m = 1) (X : ComplexMatrix2) :
    ComplexMatrix2.conjugateBy (Complex.I • m) X = m * X * m := by
  have h : (Complex.I • m)⁻¹ = (-Complex.I) • m :=
    Matrix.inv_eq_right_inv (I_smul_mul_negI_smul hm)
  simp only [ComplexMatrix2.conjugateBy, h]
  simp [smul_smul]
private theorem I_smul_mem_compact {m : ComplexMatrix2} (hh : m.conjTranspose = m)
    (hm : m * m = 1) (hd : m.det = -1) : Complex.I • m ∈ PeriodicLattice.compactGaugeGroup := by
  change _ ∈ ComplexMatrix2.specialUnitary
  rw [Matrix.mem_specialUnitaryGroup_iff, Matrix.mem_unitaryGroup_iff]
  refine ⟨?_, ?_⟩
  · have h : star (Complex.I • m) = (-Complex.I) • m := by
      rw [star_smul, Matrix.star_eq_conjTranspose, hh]
      simp
    rw [h]
    exact I_smul_mul_negI_smul hm
  · rw [Matrix.det_smul, hd]
    simp
private def invSqrtTwo : ℂ := ((Real.sqrt 2)⁻¹ : ℝ)
private theorem invSqrtTwo_mul_self : invSqrtTwo * invSqrtTwo = 2⁻¹ := by
  have h : ((Real.sqrt 2)⁻¹ : ℝ) * (Real.sqrt 2)⁻¹ = 2⁻¹ := by
    rw [← mul_inv, Real.mul_self_sqrt (by norm_num)]
  have h' := congrArg (fun x : ℝ => (x : ℂ)) h
  simpa [invSqrtTwo] using h'
private theorem invSqrtTwo_star : star invSqrtTwo = invSqrtTwo := by
  simp [invSqrtTwo]
private theorem add_mul_mul_add {A B : ComplexMatrix2} (hA : A * A = 1) (hB : B * B = 1)
    (hAB : A * B = -(B * A)) : (A + B) * A * (A + B) = (2 : ℂ) • B := by
  have e : (A + B) * A * (A + B) = A * A * A + A * A * B + B * (A * A) + B * (A * B) := by
    noncomm_ring
  have e' : B * -(B * A) = -(B * B * A) := by noncomm_ring
  rw [e, hAB, hA, e', hB, two_smul]
  simp only [mul_one, one_mul]
  abel
private theorem add_mul_self_of_anticomm {A B : ComplexMatrix2} (hA : A * A = 1)
    (hB : B * B = 1) (hAB : A * B = -(B * A)) : (A + B) * (A + B) = (2 : ℂ) • (1 : ComplexMatrix2) := by
  have e : (A + B) * (A + B) = A * A + A * B + B * A + B * B := by noncomm_ring
  rw [e, hAB, hA, hB, two_smul]
  simp
private theorem exists_swap_pauli {a b : Fin 3} (h : a ≠ b) :
    ∃ v ∈ PeriodicLattice.compactGaugeGroup,
      ComplexMatrix2.conjugateBy v (ComplexMatrix2.pauliFamily a) = ComplexMatrix2.pauliFamily b ∧
      ComplexMatrix2.conjugateBy v (ComplexMatrix2.pauliFamily b) = ComplexMatrix2.pauliFamily a := by
  set m : ComplexMatrix2 :=
    invSqrtTwo • (ComplexMatrix2.pauliFamily a + ComplexMatrix2.pauliFamily b) with hmdef
  have hsq : m * m = 1 := by
    rw [hmdef, smul_mul_smul_comm, add_mul_self_of_anticomm (pauliFamily_mul_self a)
      (pauliFamily_mul_self b) (pauliFamily_anticomm h), invSqrtTwo_mul_self, smul_smul]
    simp
  have hh : m.conjTranspose = m := by
    rw [hmdef, Matrix.conjTranspose_smul, invSqrtTwo_star, Matrix.conjTranspose_add,
      pauliFamily_conjTranspose, pauliFamily_conjTranspose]
  have hd : m.det = -1 := by
    rw [hmdef, Matrix.det_smul, pauliFamily_add_det h]
    simp only [Fintype.card_fin, pow_two, invSqrtTwo_mul_self]
    norm_num
  refine ⟨Complex.I • m, I_smul_mem_compact hh hsq hd, ?_, ?_⟩
  · rw [conj_I_smul hsq, hmdef, smul_mul_assoc, mul_smul_comm, smul_mul_assoc, smul_smul,
      invSqrtTwo_mul_self, mul_assoc (ComplexMatrix2.pauliFamily a + ComplexMatrix2.pauliFamily b),
      ← mul_assoc (ComplexMatrix2.pauliFamily a + ComplexMatrix2.pauliFamily b),
      add_mul_mul_add (pauliFamily_mul_self a) (pauliFamily_mul_self b) (pauliFamily_anticomm h),
      smul_smul]
    simp
  · have e : ComplexMatrix2.pauliFamily a + ComplexMatrix2.pauliFamily b =
        ComplexMatrix2.pauliFamily b + ComplexMatrix2.pauliFamily a := add_comm _ _
    rw [conj_I_smul hsq, hmdef, smul_mul_assoc, mul_smul_comm, smul_mul_assoc, smul_smul,
      invSqrtTwo_mul_self, e, add_mul_mul_add (pauliFamily_mul_self b) (pauliFamily_mul_self a)
        (pauliFamily_anticomm h.symm), smul_smul]
    simp
private theorem exists_flip_pauli {a b : Fin 3} (h : a ≠ b) :
    ∃ v ∈ PeriodicLattice.compactGaugeGroup,
      ComplexMatrix2.conjugateBy v (ComplexMatrix2.pauliFamily a) = ComplexMatrix2.pauliFamily a ∧
      ComplexMatrix2.conjugateBy v (ComplexMatrix2.pauliFamily b) =
        (-1 : ℂ) • ComplexMatrix2.pauliFamily b := by
  refine ⟨Complex.I • ComplexMatrix2.pauliFamily a, I_smul_mem_compact (pauliFamily_conjTranspose a)
    (pauliFamily_mul_self a) (pauliFamily_det a), ?_, ?_⟩
  · rw [conj_I_smul (pauliFamily_mul_self a), pauliFamily_mul_self, one_mul]
  · rw [conj_I_smul (pauliFamily_mul_self a), pauliFamily_anticomm h.symm.symm, neg_mul, mul_assoc,
      pauliFamily_mul_self]
    simp
end PauliSymmetries
section ColourStructure
variable {L n : ℕ}
private theorem complexHessian_zero_left {F : FieldFamily L}
    (hf : ComplexHessianOfMember.Properties F n) {B : UnitEdge L n → ComplexMatrix2}
    (hB : B ∈ complexEdgeForms L n 0 0) : complexHessian F n 0 B = 0 := by
  have h := hf.linear_left 1 0 (zero_mem _) 0 (zero_mem _) B hB
  simpa using h
abbrev _root_.YangMills.SharedProofs.p5135 := @complexHessian_zero_left
private theorem complexHessian_smul_right {F : FieldFamily L}
    (hf : ComplexHessianOfMember.Properties F n) (c : ℂ) {B B' : UnitEdge L n → ComplexMatrix2}
    (hB : B ∈ complexEdgeForms L n 0 0) (hB' : B' ∈ complexEdgeForms L n 0 0) :
    complexHessian F n B (c • B') = c * complexHessian F n B B' := by
  have h := hf.linear_left c B' hB' 0 (zero_mem _) B hB
  rw [add_zero, complexHessian_zero_left hf hB, add_zero] at h
  rw [hf.symm B hB _ (Submodule.smul_mem _ c hB'), h, hf.symm B' hB' B hB]
private theorem hessianColourDiagonal_of_member
    (hexp : ∀ Y ∈ ComplexMatrix2.hermitianTraceless,
      ComplexMatrix2.matExp (Complex.I • Y) ∈ ComplexMatrix2.specialUnitary)
    (hgauge : LeftChartFacts.GaugeEquivarianceForms L n 0 0) (hL : 2 ≤ L) (hn : 0 < n)
    {F : FieldFamily L} (hF : IsAdmissibleMember (F n))
    (hf : ComplexHessianOfMember.Properties F n) :
    HessianColourDiagonal F n := by
  intro p _ μ ν
  have hw : ∀ (q : AmbientSpace) (κ : Fin 4) (a : Fin 3),
      modeForm L n q κ (ComplexMatrix2.pauliFamily a) ∈ complexEdgeForms L n 0 0 :=
    fun q κ a => modeForm_mem hL hn q κ (pauliFamily_mem_traceless a)
  have hinv : ∀ {v : ComplexMatrix2}, v ∈ PeriodicLattice.compactGaugeGroup → ∀ a a' : Fin 3,
      complexHessian F n (modeForm L n p μ (ComplexMatrix2.conjugateBy v (ComplexMatrix2.pauliFamily a)))
          (modeForm L n (-p) ν (ComplexMatrix2.conjugateBy v (ComplexMatrix2.pauliFamily a'))) =
        complexHessian F n (fourierModeForm L n a p μ) (fourierModeForm L n a' (-p) ν) := by
    intro v hv a a'
    rw [← constAdjoint_modeForm, ← constAdjoint_modeForm]
    exact complexHessian_constAdjoint hexp hgauge hF hv (hw _ _ _) (hw _ _ _)
  have hoff : ∀ a a' : Fin 3, a ≠ a' →
      complexHessian F n (fourierModeForm L n a p μ) (fourierModeForm L n a' (-p) ν) = 0 := by
    intro a a' h
    obtain ⟨v, hv, h₁, h₂⟩ := exists_flip_pauli h
    have e := hinv hv a a'
    rw [h₁, h₂, modeForm_smul, complexHessian_smul_right hf _ (hw _ _ _) (hw _ _ _)] at e
    change (-1 : ℂ) * complexHessian F n (fourierModeForm L n a p μ)
      (fourierModeForm L n a' (-p) ν) = _ at e
    linear_combination (-1 / 2 : ℂ) * e
  have hdiag : ∀ a b : Fin 3,
      complexHessian F n (fourierModeForm L n a p μ) (fourierModeForm L n a (-p) ν) =
        complexHessian F n (fourierModeForm L n b p μ) (fourierModeForm L n b (-p) ν) := by
    intro a b
    by_cases h : a = b
    · rw [h]
    · obtain ⟨v, hv, h₁, -⟩ := exists_swap_pauli h
      have e := hinv hv a a
      rw [h₁] at e
      exact e.symm
  refine ⟨complexHessian F n (fourierModeForm L n 0 p μ) (fourierModeForm L n 0 (-p) ν),
    fun a a' => ?_⟩
  split_ifs with h
  · rw [← h]
    exact hdiag a 0
  · exact hoff a a' h
private theorem vertexCoboundary_eq_covDiff (l : Vertex L n 0 0 → ComplexMatrix2) :
    vertexCoboundary (k := 0) (j := 0) l =
      covDiff (k := 0) (j := 0) (identityField L n) l := by
  funext b
  by_cases hb : b.IsPositivelyOriented
  · simp [covDiff, extendOddly, hb, vertexCoboundary, identityField, ComplexMatrix2.conjugateBy]
  · simp only [covDiff, extendOddly, if_neg hb, vertexCoboundary]
    change l b.target - l b.source = -(ComplexMatrix2.conjugateBy 1 (l b.source) - l b.target)
    simp [ComplexMatrix2.conjugateBy]
end ColourStructure
section DifferencesOfFunctionals
variable {L : ℕ}
private theorem isAdmissibleMember_sub {n : ℕ} {f f' : (UnitEdge L n → ComplexMatrix2) → ℝ}
    (h : IsAdmissibleMember f) (h' : IsAdmissibleMember f') : IsAdmissibleMember (f - f') := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨inst, O, hO, h1, hf⟩ := h.analytic
    obtain ⟨inst', O', hO', h1', hf'⟩ := h'.analytic
    obtain rfl : inst = inst' := Subsingleton.elim _ _
    refine ⟨inst, O ∩ O', ?_, ⟨h1, h1'⟩, fun β p hp => ?_⟩
    · obtain ⟨A, hA, e⟩ := hO
      obtain ⟨A', hA', e'⟩ := hO'
      exact ⟨A ∩ A', hA.inter hA', by rw [e, e']; ext x; simp only [mem_inter_iff]; tauto⟩
    · obtain ⟨W, Φ, hpW, hΦ, hv⟩ := hf β p hp.1
      obtain ⟨W', Φ', hpW', hΦ', hv'⟩ := hf' β p hp.2
      refine ⟨W ∩ W', fun x => Φ x - Φ' x, ⟨hpW, hpW'⟩, holomorphicScalar_sub hΦ hΦ',
        fun x hx hxW => ?_⟩
      simp only [hv x hx.1 hxW.1, hv' x hx.2 hxW.2, Pi.sub_apply, Complex.ofReal_sub]
  · simp [h.map_identity, h'.map_identity]
  · obtain ⟨W, hW, hg⟩ := h.locallyGauge
    obtain ⟨W', hW', hg'⟩ := h'.locallyGauge
    refine ⟨W ∩ W', Filter.Eventually.and hW hW', (Filter.Eventually.and hg hg').mono ?_⟩
    rintro U ⟨a, b⟩ v hv hvW
    simp only [Pi.sub_apply, a v hv hvW.1, b v hv hvW.2]
  · refine (Filter.Eventually.and h.globalGauge h'.globalGauge).mono ?_
    rintro U ⟨a, b⟩ g hg
    simp only [Pi.sub_apply, a g hg, b g hg]
  · refine (Filter.Eventually.and h.symmetry h'.symmetry).mono ?_
    rintro U ⟨a, b⟩ σ hσ hσ'
    simp only [Pi.sub_apply, a σ hσ hσ', b σ hσ hσ']
private theorem isLatticeFunctional_sub {F F' : FieldFamily L} (hF : IsLatticeFunctional L F)
    (hF' : IsLatticeFunctional L F') : IsLatticeFunctional L (F - F') :=
  eventuallyForSides_mono (eventuallyForSides_and hF hF') fun _ _ h =>
    isAdmissibleMember_sub h.1 h.2
private theorem imStrip_min_left {δ δ' : ℝ} : imStrip (min δ δ') ⊆ imStrip δ :=
  fun _ h μ => (h μ).trans (min_le_left _ _)
private theorem imStrip_min_right {δ δ' : ℝ} : imStrip (min δ δ') ⊆ imStrip δ' :=
  fun _ h μ => (h μ).trans (min_le_right _ _)
private theorem isTemperedWitness_sub (hc : PowerExpCharts.ExpChartsStatement)
    (hp : OneLoop.PauliMatrixRelations) (hL : 2 ≤ L) {F F' : FieldFamily L}
    (hF : IsLatticeFunctional L F) (hF' : IsLatticeFunctional L F') {δ δ' : ℝ}
    {π π' : SymbolArray} {e e' : ℕ → ℝ} (c : IsTemperedWitness L F δ π e)
    (c' : IsTemperedWitness L F' δ' π' e') :
    IsTemperedWitness L (F - F') (min δ δ') (π - π') (e + e') := by
  refine ⟨lt_min c.delta_pos c'.delta_pos, ?_, ?_, ?_, ?_⟩
  · obtain ⟨O, hO, hh⟩ := c.analytic
    obtain ⟨O', hO', hh'⟩ := c'.analytic
    refine ⟨O ∩ O', fun κ hκ => ⟨hO (imStrip_min_left hκ), hO' (imStrip_min_right hκ)⟩,
      fun μ ν => ⟨isHolomorphicIn_sub (hh μ ν).1 (hh' μ ν).1, ?_⟩⟩
    obtain ⟨C, hC⟩ := (hh μ ν).2
    obtain ⟨C', hC'⟩ := (hh' μ ν).2
    exact ⟨C + C', fun κ hκ =>
      (norm_sub_le _ _).trans (add_le_add (hC κ hκ.1) (hC' κ hκ.2))⟩
  · exact eventuallyForSides_mono (eventuallyForSides_and c.err_nonneg c'.err_nonneg)
      fun n _ h => add_nonneg h.1 h.2
  · have h := c.err_tendsto.add c'.err_tendsto
    rw [add_zero] at h
    exact h
  · refine eventuallyForSides_mono
      (eventuallyForSides_and (eventuallyForSides_and hF hF') (eventuallyForSides_and c.approx c'.approx)) ?_
    rintro n hn ⟨⟨m, m'⟩, b, b'⟩ p hpm a a' μ ν
    rw [fourierModeForm_eq_modeForm, fourierModeForm_eq_modeForm,
      complexHessian_sub hc hp m m' (modeForm_mem hL hn _ _ (pauliFamily_mem_traceless _))
        (modeForm_mem hL hn _ _ (pauliFamily_mem_traceless _))]
    have e₁ := b p hpm a a' μ ν
    have e₂ := b' p hpm a a' μ ν
    rw [fourierModeForm_eq_modeForm, fourierModeForm_eq_modeForm] at e₁ e₂
    refine le_trans (le_of_eq ?_) ((norm_sub_le _ _).trans (add_le_add e₁ e₂))
    congr 1
    split_ifs
    · simp only [Pi.sub_apply]
      ring
    · ring
private theorem hessianSymbol_spec (hD : HessianSymbolDetermined.Claim)
    (hs : Conventions.IsAdmissibleBlockingFactor L) {F : FieldFamily L}
    (hF : IsTemperedFunctional L F) : IsHessianSymbol L F (hessianSymbol L F) := by
  obtain ⟨P, hP, -⟩ := (hD L hs F hF).2
  exact Classical.epsilon_spec (p := IsHessianSymbol L F) ⟨P, hP⟩
private theorem hessianSymbolOfDifference_of_tempered (hc : PowerExpCharts.ExpChartsStatement)
    (hp : OneLoop.PauliMatrixRelations) (hD : HessianSymbolDetermined.Claim)
    (hs : Conventions.IsAdmissibleBlockingFactor L) (hL : 2 ≤ L) {F F' : FieldFamily L}
    (hF : IsTemperedFunctional L F) (hF' : IsTemperedFunctional L F')
    (hd : IsTemperedFunctional L (F - F')) : HessianSymbolOfDifference F F' := by
  rintro κ ⟨⟨δ, π, e, c, hκ⟩, δ', π', e', c', hκ'⟩
  have c'' := isTemperedWitness_sub hc hp hL hF.1 hF'.1 c c'
  have hκ'' : κ ∈ imStrip (min δ δ') := by
    rcases le_total δ δ' with h | h
    · rwa [min_eq_left h]
    · rwa [min_eq_right h]
  refine ⟨⟨_, _, _, c'', hκ''⟩, fun μ ν => ?_⟩
  rw [hessianSymbol_spec hD hs hd _ _ _ c'' μ ν hκ'',
    hessianSymbol_spec hD hs hF _ _ _ c μ ν hκ,
    hessianSymbol_spec hD hs hF' _ _ _ c' μ ν hκ']
  rfl
private theorem eq_zero_of_transverseTensor_isBigO {d : ℝ}
    (h : (fun p : AmbientSpace => ((TemperedStiffness.transverseTensor d 0 1 p : ℝ) : ℂ)) =O[𝓝 0]
      fun p => TorusMetric.euclidNormVec p ^ 4) : d = 0 := by
  set w : AmbientSpace := ![1, 1, 0, 0] with hw
  have hcurve : Tendsto (fun t : ℝ => t • w) (𝓝 0) (𝓝 0) := by
    have hc : Continuous fun t : ℝ => t • w := by fun_prop
    simpa using hc.tendsto 0
  obtain ⟨C, hC⟩ := (h.comp_tendsto hcurve).bound
  have hsum : ∀ t : ℝ, ∑ μ, (t • w) μ ^ 2 = 2 * t ^ 2 := by
    intro t
    simp [Fin.sum_univ_four, hw]
    ring
  have hE : ∀ t : ℝ, TorusMetric.euclidNormVec (t • w) ^ 2 = 2 * t ^ 2 := by
    intro t
    rw [TorusMetric.euclidNormVec, Real.sq_sqrt (by positivity), hsum]
  have hE4 : ∀ t : ℝ, TorusMetric.euclidNormVec (t • w) ^ 4 = 4 * t ^ 4 := by
    intro t
    have : TorusMetric.euclidNormVec (t • w) ^ 4 = (TorusMetric.euclidNormVec (t • w) ^ 2) ^ 2 := by
      ring
    rw [this, hE]
    ring
  have hT : ∀ t : ℝ, TemperedStiffness.transverseTensor d 0 1 (t • w) = -(d * t ^ 2) := by
    intro t
    have h0 : (t • w) 0 = t := by simp [hw]
    have h1 : (t • w) 1 = t := by simp [hw]
    simp only [TemperedStiffness.transverseTensor, h0, h1]
    rw [if_neg (by decide)]
    ring
  have hbound : ∀ᶠ t in 𝓝[≠] (0 : ℝ), |d| ≤ C * (4 * t ^ 2) := by
    filter_upwards [nhdsWithin_le_nhds hC, self_mem_nhdsWithin] with t ht ht0
    have ht0' : t ≠ 0 := ht0
    simp only [Function.comp, hT, hE4] at ht
    rw [Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_neg, abs_mul,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ t ^ 2),
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ 4 * t ^ 4)] at ht
    have hpos : 0 < t ^ 2 := by positivity
    have e : C * (4 * t ^ 4) = C * (4 * t ^ 2) * t ^ 2 := by ring
    rw [e] at ht
    exact le_of_mul_le_mul_right ht hpos
  have hlim : Tendsto (fun t : ℝ => C * (4 * t ^ 2)) (𝓝[≠] 0) (𝓝 0) := by
    have hc : Continuous fun t : ℝ => C * (4 * t ^ 2) := by fun_prop
    have h0 := hc.tendsto 0
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero] at h0
    exact h0.mono_left nhdsWithin_le_nhds
  have hle : |d| ≤ 0 := ge_of_tendsto hlim hbound
  exact abs_eq_zero.1 (le_antisymm hle (abs_nonneg d))
private theorem stiffnessConstant_sub (hc : PowerExpCharts.ExpChartsStatement)
    (hp : OneLoop.PauliMatrixRelations)
    (hC : TemperedStiffness.TemperedStiffnessClaim) (hL : 0 < L) (hL2 : 2 ≤ L)
    (hs : Conventions.IsAdmissibleBlockingFactor L) {F F' : FieldFamily L}
    (hF : IsTemperedFunctional L F) (hF' : IsTemperedFunctional L F') :
    FunctionalStiffness.stiffnessConstant hL (F - F') =
      FunctionalStiffness.stiffnessConstant hL F - FunctionalStiffness.stiffnessConstant hL F' := by
  obtain ⟨hFf, δ, π, e, c⟩ := hF
  obtain ⟨hFf', δ', π', e', c'⟩ := hF'
  have c'' := isTemperedWitness_sub hc hp hL2 hFf hFf' c c'
  obtain ⟨-, -, -, b, hb, -, hf⟩ := hC L hL hs F δ π e hFf c
  obtain ⟨-, -, -, b', hb', -, hf'⟩ := hC L hL hs F' δ' π' e' hFf' c'
  obtain ⟨-, -, -, b'', hb'', -, hf''⟩ :=
    hC L hL hs (F - F') _ _ _ (isLatticeFunctional_sub hFf hFf') c''
  have h01 : (0 : Fin 4) ≠ 1 := by decide
  rw [(hf 0 1 h01).eq_coeff, (hf' 0 1 h01).eq_coeff, (hf'' 0 1 h01).eq_coeff]
  have hz : b'' - b + b' = 0 := by
    refine eq_zero_of_transverseTensor_isBigO ?_
    refine (((hb 0 1).sub (hb' 0 1)).sub (hb'' 0 1)).congr_left fun p => ?_
    simp only [TemperedStiffness.transverseTensor, Pi.sub_apply]
    push_cast
    ring
  linarith
end DifferencesOfFunctionals
theorem gaugeColourMomentumClaim_holds (h₁ : MemberFirstDerivativeVanishes)
    (h₂ : GaugeDirectionHessian.HessianKillsGaugeDirections)
    (h₃ : BondFormHessianOnTorus.PlaneWaveExpansion) (h₄ : ComplexHessianOfMember.Statement)
    (h₅ : LeftChartFacts.HoldEverywhere) (h₆ : ComplexMatrix2.UnitaryLogarithmProperties)
    (h₇ : PowerExpCharts.ExpChartsStatement) (h₈ : OneLoop.PauliMatrixRelations)
    (h₉ : HessianSymbolDetermined.Claim)
    (h₁₀ : TemperedStiffness.TemperedStiffnessClaim) : GaugeColourMomentumClaim := by
  intro L hL hs
  have hL2 : 2 ≤ L := by
    have := hs.2
    omega
  have hexp : ∀ Y ∈ ComplexMatrix2.hermitianTraceless,
      ComplexMatrix2.matExp (Complex.I • Y) ∈ ComplexMatrix2.specialUnitary :=
    fun Y hY => (h₆.1 Y hY).2.2.2
  refine ⟨fun F hF => eventuallyForSides_mono hF fun n hn hm => ⟨?_, ?_, ?_, ?_, ?_⟩,
    fun F F' hF hF' => ?_⟩
  · exact fun C hC => h₁ L n hs hn (F n) hm C hC
  · have hgauge : LeftChartFacts.GaugeEquivarianceForms L n 0 0 :=
      ((h₅ L 0 0 0 0 hs le_rfl le_rfl le_rfl).2.1 n hn).2.2.2.2.1
    exact fun v hv B hB B' hB' => complexHessian_constAdjoint hexp hgauge hm hv hB hB'
  · intro l hl B' hB'
    rw [vertexCoboundary_eq_covDiff]
    exact h₂ L n hs hn F hm l hl B' hB'
  · have hgauge : LeftChartFacts.GaugeEquivarianceForms L n 0 0 :=
      ((h₅ L 0 0 0 0 hs le_rfl le_rfl le_rfl).2.1 n hn).2.2.2.2.1
    exact hessianColourDiagonal_of_member hexp hgauge hL2 hn hm (h₄ L n hs hn F hm)
  · exact (h₃ L n hs hn F hm).1
  · obtain ⟨hf, δ, π, e, c⟩ := id hF
    obtain ⟨hf', δ', π', e', c'⟩ := id hF'
    have hd : IsTemperedFunctional L (F - F') :=
      ⟨isLatticeFunctional_sub hf hf', _, _, _, isTemperedWitness_sub h₇ h₈ hL2 hf hf' c c'⟩
    exact ⟨eventuallyForSides_and hf hf', hd,
      hessianSymbolOfDifference_of_tempered h₇ h₈ h₉ hs hL2 hF hF' hd,
      stiffnessConstant_sub h₇ h₈ h₁₀ hL hL2 hs hF hF'⟩
end YangMills.Construction.OneLoopLaw.GaugeColourMomenta
end
