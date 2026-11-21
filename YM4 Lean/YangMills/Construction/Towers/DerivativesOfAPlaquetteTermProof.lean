import YangMills.Construction.Towers.GaugeDirectionsInTheLeftChartProof
import YangMills.Construction.Matrices.LieAlgebraNormAdjointIsometryLemmas
import YangMills.Construction.RunningCouplingSlope.PlainStepNearTheFreeStepProof
import YangMills.Construction.Towers.DerivativesOfAPlaquetteTerm
import Mathlib
set_option autoImplicit false
open Set Filter
open scoped Topology Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.Tower.FaceTermDerivatives
open YangMills.Construction.Matrices
def TwoJet (P P₁ : ℂ → ComplexMatrix2) (P₂ : ComplexMatrix2) : Prop :=
  (∀ t, HasDerivAt P (P₁ t) t) ∧ HasDerivAt P₁ P₂ 0
theorem twoJet_matExp_line (Y : ComplexMatrix2) :
    TwoJet (fun t => ComplexMatrix2.matExp ((Complex.I * t) • Y))
      (fun t => ComplexMatrix2.matExp ((Complex.I * t) • Y) * (Complex.I • Y))
      ((Complex.I • Y) * (Complex.I • Y)) := by
  have hline : ∀ t : ℂ, (Complex.I * t) • Y = t • (Complex.I • Y) := fun t => by
    rw [smul_smul, mul_comm]
  have h : ∀ t : ℂ, HasDerivAt (fun u : ℂ => ComplexMatrix2.matExp (u • (Complex.I • Y)))
      (ComplexMatrix2.matExp (t • (Complex.I • Y)) * (Complex.I • Y)) t := fun t =>
    hasDerivAt_exp_smul_const (Complex.I • Y) t
  simp only [hline]
  refine ⟨h, ?_⟩
  have h₂ := (h 0).mul_const (Complex.I • Y)
  simpa using h₂
theorem TwoJet.mul {P P₁ Q Q₁ : ℂ → ComplexMatrix2} {P₂ Q₂ : ComplexMatrix2}
    (hP : TwoJet P P₁ P₂) (hQ : TwoJet Q Q₁ Q₂) :
    TwoJet (fun t => P t * Q t) (fun t => P₁ t * Q t + P t * Q₁ t)
      (P₂ * Q 0 + P₁ 0 * Q₁ 0 + (P₁ 0 * Q₁ 0 + P 0 * Q₂)) :=
  ⟨fun t => (hP.1 t).fun_mul (hQ.1 t), (hP.2.fun_mul (hQ.1 0)).fun_add ((hP.1 0).fun_mul hQ.2)⟩
theorem I_smul_mul_I_smul_eq_neg_mul (A B : ComplexMatrix2) :
    (Complex.I • A) * (Complex.I • B) = -(A * B) := by
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Complex.I_mul_I, neg_smul, one_smul]
theorem commutatorSum_eq_expand (Y : Fin 4 → ComplexMatrix2) :
    commutatorSum Y = (Y 0 * Y 1 - Y 1 * Y 0) + (Y 0 * Y 2 - Y 2 * Y 0) +
      (Y 0 * Y 3 - Y 3 * Y 0) + (Y 1 * Y 2 - Y 2 * Y 1) + (Y 1 * Y 3 - Y 3 * Y 1) +
      (Y 2 * Y 3 - Y 3 * Y 2) := by
  have h0 : Finset.Ioi (0 : Fin 4) = {1, 2, 3} := by decide
  have h1 : Finset.Ioi (1 : Fin 4) = {2, 3} := by decide
  have h2 : Finset.Ioi (2 : Fin 4) = {3} := by decide
  have h3 : Finset.Ioi (3 : Fin 4) = ∅ := by decide
  simp only [commutatorSum, Fin.sum_univ_four, h0, h1, h2, h3]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton,
    Finset.sum_insert (by decide), Finset.sum_singleton, Finset.sum_singleton, Finset.sum_empty]
  abel
theorem twoJet_expProduct (Y : Fin 4 → ComplexMatrix2) :
    ∃ (P₁ : ℂ → ComplexMatrix2) (P₂ : ComplexMatrix2), TwoJet (expProduct Y) P₁ P₂ ∧
      P₁ 0 = Complex.I • ∑ i, Y i ∧
      P₂ = -((∑ i, Y i) * ∑ i, Y i) - commutatorSum Y := by
  have h := TwoJet.mul (TwoJet.mul (TwoJet.mul (twoJet_matExp_line (Y 0))
    (twoJet_matExp_line (Y 1))) (twoJet_matExp_line (Y 2))) (twoJet_matExp_line (Y 3))
  refine ⟨_, _, h, ?_, ?_⟩
  · simp [Fin.sum_univ_four, smul_add]
  · simp only [mul_zero, zero_smul, NormedSpace.exp_zero, one_mul, mul_one,
      I_smul_mul_I_smul_eq_neg_mul, commutatorSum_eq_expand, Fin.sum_univ_four, mul_add, add_mul]
    noncomm_ring
theorem mul_self_eq_halfTrace_smul_one {S : ComplexMatrix2} (h : ComplexMatrix2.fullTrace S = 0) :
    S * S = ComplexMatrix2.halfTrace (S * S) • (1 : ComplexMatrix2) := by apply _root_.YangMills.SharedProofs.p123376 <;> assumption
theorem inv_eq_trace_smul_one_sub {W : ComplexMatrix2} (h : W.det = 1) :
    W⁻¹ = ComplexMatrix2.fullTrace W • (1 : ComplexMatrix2) - W := by
  refine Matrix.inv_eq_right_inv ?_
  have h' : W 0 0 * W 1 1 - W 0 1 * W 1 0 = 1 := by simpa [Matrix.det_fin_two] using h
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ComplexMatrix2.fullTrace, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two] <;>
    first | linear_combination h' | ring
theorem fullTrace_commutatorSum (Y : Fin 4 → ComplexMatrix2) :
    ComplexMatrix2.fullTrace (commutatorSum Y) = 0 := by
  simp only [commutatorSum_eq_expand, ComplexMatrix2.fullTrace, Matrix.trace_add, Matrix.trace_sub]
  simp only [Matrix.trace_mul_comm (Y 1) (Y 0), Matrix.trace_mul_comm (Y 2) (Y 0),
    Matrix.trace_mul_comm (Y 3) (Y 0), Matrix.trace_mul_comm (Y 2) (Y 1),
    Matrix.trace_mul_comm (Y 3) (Y 1), Matrix.trace_mul_comm (Y 3) (Y 2)]
  ring
def lineTerm (Y : Fin 4 → ComplexMatrix2) (W : ComplexMatrix2) (t : ℂ) : ℂ :=
  1 - (1 / 2) * ComplexMatrix2.fullTrace (expProduct Y t * W)
theorem lineTerm_derivs (Y : Fin 4 → ComplexMatrix2) {W : ComplexMatrix2}
    (hY : ComplexMatrix2.fullTrace (∑ i, Y i) = 0) (hW : W.det = 1) :
    Differentiable ℂ (lineTerm Y W) ∧
      HasDerivAt (lineTerm Y W) (firstDerivExpr Y W) 0 ∧
      HasDerivAt (deriv (lineTerm Y W)) (secondDerivExpr Y W) 0 := by
  obtain ⟨P₁, P₂, hJ, h₁, h₂⟩ := twoJet_expProduct Y
  let l : ComplexMatrix2 →L[ℂ] ℂ := LinearMap.toContinuousLinearMap
    ((Matrix.traceLinearMap (Fin 2) ℂ ℂ) ∘ₗ (LinearMap.mulRight ℂ W))
  have hl : ∀ X : ComplexMatrix2, l X = ComplexMatrix2.fullTrace (X * W) := fun X => rfl
  have hd : ∀ t, HasDerivAt (lineTerm Y W) (-((1 / 2) * l (P₁ t))) t := fun t => by
    have h := ((l.hasFDerivAt.comp_hasDerivAt t (hJ.1 t)).const_mul (1 / 2 : ℂ)).const_sub 1
    exact h
  have hderiv : deriv (lineTerm Y W) = fun t => -((1 / 2) * l (P₁ t)) :=
    funext fun t => (hd t).deriv
  have hd₂ : HasDerivAt (deriv (lineTerm Y W)) (-((1 / 2) * l P₂)) 0 := by
    rw [hderiv]
    exact ((l.hasFDerivAt.comp_hasDerivAt 0 hJ.2).const_mul (1 / 2 : ℂ)).neg
  refine ⟨fun t => (hd t).differentiableAt, ?_, ?_⟩
  · convert hd 0 using 1
    rw [h₁, hl, firstDerivExpr, Matrix.smul_mul]
    simp only [ComplexMatrix2.fullTrace, Matrix.trace_smul, smul_eq_mul]
    ring
  · convert hd₂ using 1
    set S := ∑ i, Y i with hS
    set C := commutatorSum Y with hC
    have hSS : ComplexMatrix2.fullTrace (S * S * W) =
        ComplexMatrix2.halfTrace (S * S) * ComplexMatrix2.fullTrace W := by
      conv_lhs => rw [mul_self_eq_halfTrace_smul_one hY]
      simp [ComplexMatrix2.fullTrace, Matrix.trace_smul]
    have hCW : ComplexMatrix2.fullTrace (C * (W - W⁻¹)) = 2 * ComplexMatrix2.fullTrace (C * W) := by
      rw [inv_eq_trace_smul_one_sub hW]
      have h₀ : ComplexMatrix2.fullTrace C = 0 := fullTrace_commutatorSum Y
      have h₃ : W - (ComplexMatrix2.fullTrace W • (1 : ComplexMatrix2) - W) =
          (2 : ℂ) • W - ComplexMatrix2.fullTrace W • (1 : ComplexMatrix2) := by
        rw [two_smul]
        abel
      rw [h₃, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_one]
      simp only [ComplexMatrix2.fullTrace] at h₀ ⊢
      rw [Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_smul, h₀]
      simp
    rw [h₂, hl, secondDerivExpr, sub_mul, neg_mul]
    simp only [ComplexMatrix2.fullTrace] at hSS hCW ⊢
    rw [Matrix.trace_sub, Matrix.trace_neg, hSS, hCW]
    ring
theorem deriv_deriv_comp_add (G : ℂ → ℂ) :
    deriv (fun s => deriv (fun t => G (s + t)) 0) 0 = deriv (deriv G) 0 := by
  have h : (fun s => deriv (fun t => G (s + t)) 0) = deriv G := by
    funext s
    have := deriv_comp_const_add (f := G) s 0
    simpa using this
  rw [h]
theorem finset_sum_derivs {ι : Type*} (s : Finset ι) (g : ι → ℂ → ℂ) (a b : ι → ℂ)
    (hd : ∀ i ∈ s, Differentiable ℂ (g i)) (h₁ : ∀ i ∈ s, HasDerivAt (g i) (a i) 0)
    (h₂ : ∀ i ∈ s, HasDerivAt (deriv (g i)) (b i) 0) :
    deriv (fun t => ∑ i ∈ s, g i t) 0 = ∑ i ∈ s, a i ∧
      deriv (deriv fun t => ∑ i ∈ s, g i t) 0 = ∑ i ∈ s, b i := by
  have hfun : deriv (fun t => ∑ i ∈ s, g i t) = fun t => ∑ i ∈ s, deriv (g i) t := by
    funext t
    exact deriv_fun_sum fun i hi => (hd i hi).differentiableAt
  refine ⟨?_, ?_⟩
  · rw [hfun]
    exact Finset.sum_congr rfl fun i hi => (h₁ i hi).deriv
  · rw [hfun]
    exact (HasDerivAt.fun_sum h₂).deriv
theorem directionalDeriv_eq_deriv_line {α : Type*} (φ : (α → ComplexMatrix2) → ℂ)
    (B : α → ComplexMatrix2) :
    directionalDeriv ℂ φ B = deriv (fun z : ℂ => φ (z • B)) 0 := rfl
theorem mixedDirectionalDeriv_self_eq {α : Type*} (φ : (α → ComplexMatrix2) → ℂ)
    (B : α → ComplexMatrix2) :
    mixedDirectionalDeriv ℂ φ B B = deriv (deriv fun z : ℂ => φ (z • B)) 0 := by
  have h := deriv_deriv_comp_add fun z : ℂ => φ (z • B)
  simp only [add_smul] at h
  exact h
def cycleWord (V : Fin 4 → ComplexMatrix2) : ComplexMatrix2 := V 0 * V 1 * (V 2)⁻¹ * (V 3)⁻¹
def cycleTransported (V A : Fin 4 → ComplexMatrix2) : Fin 4 → ComplexMatrix2 :=
  fun i => transportSign i •
    ComplexMatrix2.conjugateBy (![1, V 0, V 0 * V 1 * (V 2)⁻¹, cycleWord V] i) (A i)
theorem conjugateBy_smul (g : ComplexMatrix2) (c : ℂ) (X : ComplexMatrix2) :
    ComplexMatrix2.conjugateBy g (c • X) = c • ComplexMatrix2.conjugateBy g X := by apply _root_.YangMills.Construction.LieInnerProductProof.conjugateBy_smul <;> assumption
theorem conjugateBy_neg (g X : ComplexMatrix2) :
    ComplexMatrix2.conjugateBy g (-X) = -ComplexMatrix2.conjugateBy g X := by
  simp [ComplexMatrix2.conjugateBy]
theorem mul_matExp_eq (hE : ComplexMatrix2.NormExpLogBasics) {g : ComplexMatrix2} (hg : IsUnit g)
    (X : ComplexMatrix2) :
    g * ComplexMatrix2.matExp X =
      ComplexMatrix2.matExp (ComplexMatrix2.conjugateBy g X) * g := by
  have h := (hE.2.1 X).2.2.2.2.2.2 g hg
  have hg' : IsUnit g.det := (Matrix.isUnit_iff_isUnit_det g).1 hg
  rw [ComplexMatrix2.conjugateBy, ← h, Matrix.nonsing_inv_mul_cancel_right _ _ hg']
theorem isUnit_of_det_eq_one {V : ComplexMatrix2} (h : V.det = 1) : IsUnit V := by apply _root_.YangMills.Construction.PeriodicLattice.ImageBondEquivariance.isUnit_of_det_eq_one <;> assumption
theorem det_inv_of_det_eq_one {V : ComplexMatrix2} (h : V.det = 1) : (V⁻¹).det = 1 := by apply _root_.YangMills.Construction.PeriodicLattice.ImageBondEquivariance.det_inv_of_det_eq_one <;> assumption
theorem det_cycleWord {V : Fin 4 → ComplexMatrix2} (hV : ∀ i, (V i).det = 1) :
    (cycleWord V).det = 1 := by
  simp [cycleWord, Matrix.det_mul, hV]
theorem cycleWord_twisted (hE : ComplexMatrix2.NormExpLogBasics) {V : Fin 4 → ComplexMatrix2}
    (A : Fin 4 → ComplexMatrix2) (hV : ∀ i, (V i).det = 1) (t : ℂ) :
    cycleWord (fun i => ComplexMatrix2.matExp (Complex.I • (t • A i)) * V i) =
      expProduct (cycleTransported V A) t * cycleWord V := by
  have hI : ∀ i, Complex.I • (t • A i) = (Complex.I * t) • A i := fun i => smul_smul _ _ _
  have hinv : ∀ i, (ComplexMatrix2.matExp ((Complex.I * t) • A i) * V i)⁻¹ =
      (V i)⁻¹ * ComplexMatrix2.matExp (-((Complex.I * t) • A i)) := fun i => by
    rw [Matrix.mul_inv_rev, (hE.2.1 _).2.2.2.2.1]
  have hg₂ : IsUnit (V 0 * V 1 * (V 2)⁻¹) :=
    isUnit_of_det_eq_one (by simp [Matrix.det_mul, hV])
  have hg₃ : IsUnit (cycleWord V) := isUnit_of_det_eq_one (det_cycleWord hV)
  have e₁ := mul_matExp_eq hE (isUnit_of_det_eq_one (hV 0)) ((Complex.I * t) • A 1)
  have e₂ := mul_matExp_eq hE hg₂ (-((Complex.I * t) • A 2))
  have e₃ := mul_matExp_eq hE hg₃ (-((Complex.I * t) • A 3))
  have v₀ : (Complex.I * t) • cycleTransported V A 0 = (Complex.I * t) • A 0 := by
    simp [cycleTransported, transportSign, ComplexMatrix2.conjugateBy]
  have v₁ : (Complex.I * t) • cycleTransported V A 1 =
      ComplexMatrix2.conjugateBy (V 0) ((Complex.I * t) • A 1) := by
    simp [cycleTransported, transportSign, conjugateBy_smul]
  have v₂ : (Complex.I * t) • cycleTransported V A 2 =
      ComplexMatrix2.conjugateBy (V 0 * V 1 * (V 2)⁻¹) (-((Complex.I * t) • A 2)) := by
    simp [cycleTransported, transportSign, conjugateBy_smul, conjugateBy_neg]
  have v₃ : (Complex.I * t) • cycleTransported V A 3 =
      ComplexMatrix2.conjugateBy (cycleWord V) (-((Complex.I * t) • A 3)) := by
    simp [cycleTransported, transportSign, conjugateBy_smul, conjugateBy_neg]
  simp only [cycleWord] at e₃ v₃ ⊢
  simp only [hI, hinv, expProduct, v₀, v₁, v₂, v₃]
  calc _ = ComplexMatrix2.matExp ((Complex.I * t) • A 0) *
        (V 0 * ComplexMatrix2.matExp ((Complex.I * t) • A 1)) * V 1 *
        (V 2)⁻¹ * ComplexMatrix2.matExp (-((Complex.I * t) • A 2)) * (V 3)⁻¹ *
        ComplexMatrix2.matExp (-((Complex.I * t) • A 3)) := by simp only [mul_assoc]
    _ = ComplexMatrix2.matExp ((Complex.I * t) • A 0) *
        ComplexMatrix2.matExp (ComplexMatrix2.conjugateBy (V 0) ((Complex.I * t) • A 1)) *
        (V 0 * V 1 * (V 2)⁻¹ * ComplexMatrix2.matExp (-((Complex.I * t) • A 2))) * (V 3)⁻¹ *
        ComplexMatrix2.matExp (-((Complex.I * t) • A 3)) := by rw [e₁]; simp only [mul_assoc]
    _ = ComplexMatrix2.matExp ((Complex.I * t) • A 0) *
        ComplexMatrix2.matExp (ComplexMatrix2.conjugateBy (V 0) ((Complex.I * t) • A 1)) *
        ComplexMatrix2.matExp
          (ComplexMatrix2.conjugateBy (V 0 * V 1 * (V 2)⁻¹) (-((Complex.I * t) • A 2))) *
        (V 0 * V 1 * (V 2)⁻¹ * (V 3)⁻¹ * ComplexMatrix2.matExp (-((Complex.I * t) • A 3))) := by
      rw [e₂]; simp only [mul_assoc]
    _ = _ := by rw [e₃]; simp only [mul_assoc]
theorem fullTrace_conjugateBy {g : ComplexMatrix2} (hg : g.det = 1) (X : ComplexMatrix2) :
    ComplexMatrix2.fullTrace (ComplexMatrix2.conjugateBy g X) = ComplexMatrix2.fullTrace X := by apply _root_.YangMills.DeltaSharedProofs.p68910 <;> assumption
theorem fullTrace_sum_cycleTransported {V A : Fin 4 → ComplexMatrix2} (hV : ∀ i, (V i).det = 1)
    (hA : ∀ i, ComplexMatrix2.fullTrace (A i) = 0) :
    ComplexMatrix2.fullTrace (∑ i, cycleTransported V A i) = 0 := by
  have hT : ∀ i, (![1, V 0, V 0 * V 1 * (V 2)⁻¹, cycleWord V] i : ComplexMatrix2).det = 1 := by
    intro i
    fin_cases i
    · simp
    · simpa using hV 0
    · simp [Matrix.det_mul, hV]
    · simpa using det_cycleWord hV
  have h : ∀ i, ComplexMatrix2.fullTrace (cycleTransported V A i) = 0 := fun i => by
    simp only [cycleTransported, ComplexMatrix2.fullTrace, Matrix.trace_smul]
    have := fullTrace_conjugateBy (hT i) (A i)
    simp only [ComplexMatrix2.fullTrace] at this hA
    rw [this, hA i, smul_zero]
  simp only [ComplexMatrix2.fullTrace, Matrix.trace_sum] at h ⊢
  exact Finset.sum_eq_zero fun i _ => h i
theorem lineTerm_of_cycleWord (hE : ComplexMatrix2.NormExpLogBasics) {V A : Fin 4 → ComplexMatrix2}
    (hV : ∀ i, (V i).det = 1) :
    (fun t : ℂ => 1 - (1 / 2) * ComplexMatrix2.fullTrace
        (cycleWord fun i => ComplexMatrix2.matExp (Complex.I • (t • A i)) * V i)) =
      lineTerm (cycleTransported V A) (cycleWord V) := by
  funext t
  rw [cycleWord_twisted hE A hV t, lineTerm]
theorem secondDerivExpr_one (Y : Fin 4 → ComplexMatrix2) :
    secondDerivExpr Y 1 = ComplexMatrix2.halfTrace ((∑ i, Y i) * ∑ i, Y i) := by
  simp [secondDerivExpr, ComplexMatrix2.fullTrace]
theorem firstDerivExpr_zero_left (W : ComplexMatrix2) : firstDerivExpr 0 W = 0 := by
  simp [firstDerivExpr]
theorem secondDerivExpr_zero_left (W : ComplexMatrix2) : secondDerivExpr 0 W = 0 := by
  simp [secondDerivExpr, commutatorSum]
section FiniteSide
variable {L n k j : ℕ}
theorem plaquetteHolonomy_eq_faceEdges (V : Edge L n k j → ComplexMatrix2) (p : Face L n k j) :
    PeriodicLattice.plaquetteHolonomy V p = V (faceEdge p 0) * V (faceEdge p 1) *
      V (faceEdge p 2).opposite * V (faceEdge p 3).opposite := by
  simp [PeriodicLattice.plaquetteHolonomy, PeriodicLattice.pathHolonomy,
    PeriodicLattice.Plaquette.boundaryBonds, faceEdge, faceEdges, mul_assoc]
theorem faceEdge_mem_faceEdges (p : Face L n k j) (i : Fin 4) :
    faceEdge p i ∈ faceEdges p := List.getElem_mem _
theorem plaquetteHolonomy_expTwist
    (hnr : ∀ b : Edge L n k j, b.IsPositivelyOriented → ¬ b.opposite.IsPositivelyOriented)
    {p : Face L n k j} (hp : ∀ b ∈ faceEdges p, b.IsPositivelyOriented)
    (A U : Edge L n k j → ComplexMatrix2) :
    PeriodicLattice.plaquetteHolonomy (PeriodicLattice.expTwist A U) p =
      cycleWord fun i =>
        ComplexMatrix2.matExp (Complex.I • A (faceEdge p i)) * U (faceEdge p i) := by
  have hfor : ∀ i, PeriodicLattice.expTwist A U (faceEdge p i) =
      ComplexMatrix2.matExp (Complex.I • A (faceEdge p i)) * U (faceEdge p i) := fun i =>
    if_pos (hp _ (faceEdge_mem_faceEdges p i))
  have hrev : ∀ i, PeriodicLattice.expTwist A U (faceEdge p i).opposite =
      (ComplexMatrix2.matExp (Complex.I • A (faceEdge p i)) * U (faceEdge p i))⁻¹ := fun i =>
    if_neg (hnr _ (hp _ (faceEdge_mem_faceEdges p i)))
  rw [plaquetteHolonomy_eq_faceEdges, hfor, hfor, hrev, hrev]
  rfl
theorem cycleWord_of_field {U : Edge L n k j → ComplexMatrix2}
    (hU : U ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup) (B : Edge L n k j → ComplexMatrix2)
    (p : Face L n k j) :
    PeriodicLattice.plaquetteHolonomy U p = cycleWord (fun i => U (faceEdge p i)) ∧
      transportedForm U B p =
        cycleTransported (fun i => U (faceEdge p i)) (fun i => B (faceEdge p i)) := by
  have h : PeriodicLattice.plaquetteHolonomy U p = cycleWord (fun i => U (faceEdge p i)) := by
    rw [plaquetteHolonomy_eq_faceEdges, hU.2 _ (mem_univ _), hU.2 _ (mem_univ _)]
    rfl
  refine ⟨h, ?_⟩
  funext i
  simp only [transportedForm, faceTransports, h, cycleTransported]
theorem faceTerm_derivs (hE : ComplexMatrix2.NormExpLogBasics)
    (hnr : ∀ b : Edge L n k j, b.IsPositivelyOriented → ¬ b.opposite.IsPositivelyOriented)
    {p : Face L n k j} (hp : ∀ b ∈ faceEdges p, b.IsPositivelyOriented)
    {U B : Edge L n k j → ComplexMatrix2}
    (hU : U ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup)
    (hB : B ∈ complexEdgeForms L n k j) :
    (∀ t : ℂ, PeriodicLattice.plaquetteHolonomy (PeriodicLattice.expTwist (t • B) U) p =
      expProduct (transportedForm U B p) t * PeriodicLattice.plaquetteHolonomy U p) ∧
    Differentiable ℂ (fun t : ℂ => complexFaceTerm (PeriodicLattice.expTwist (t • B) U) p) ∧
    HasDerivAt (fun t : ℂ => complexFaceTerm (PeriodicLattice.expTwist (t • B) U) p)
      (firstDerivExpr (transportedForm U B p) (PeriodicLattice.plaquetteHolonomy U p)) 0 ∧
    HasDerivAt (deriv fun t : ℂ => complexFaceTerm (PeriodicLattice.expTwist (t • B) U) p)
      (secondDerivExpr (transportedForm U B p) (PeriodicLattice.plaquetteHolonomy U p)) 0 := by
  obtain ⟨hw, hy⟩ := cycleWord_of_field hU B p
  have hV : ∀ i, (U (faceEdge p i)).det = 1 := fun i => hU.1 _ (mem_univ _)
  have hA : ∀ i, ComplexMatrix2.fullTrace (B (faceEdge p i)) = 0 := fun i =>
    hB.1 _ (hp _ (faceEdge_mem_faceEdges p i))
  have hline : (fun t : ℂ => complexFaceTerm (PeriodicLattice.expTwist (t • B) U) p) =
      lineTerm (transportedForm U B p) (PeriodicLattice.plaquetteHolonomy U p) := by
    rw [hw, hy, ← lineTerm_of_cycleWord hE hV]
    funext t
    simp only [complexFaceTerm, PeriodicLattice.plaquetteEnergy,
      plaquetteHolonomy_expTwist hnr hp, Pi.smul_apply]
  have hj := lineTerm_derivs (transportedForm U B p)
    (W := PeriodicLattice.plaquetteHolonomy U p)
    (by rw [hy]; exact fullTrace_sum_cycleTransported hV hA) (by rw [hw]; exact det_cycleWord hV)
  rw [hline]
  refine ⟨fun t => ?_, hj⟩
  rw [plaquetteHolonomy_expTwist hnr hp, hw, hy]
  exact cycleWord_twisted hE _ hV t
theorem sum_transportedForm_one (B : Edge L n k j → ComplexMatrix2) (p : Face L n k j) :
    ∑ i, transportedForm (fun _ => (1 : ComplexMatrix2)) B p i = edgeCoboundary B p := by
  have hv : PeriodicLattice.plaquetteHolonomy (fun _ : Edge L n k j => (1 : ComplexMatrix2)) p = 1 := by
    rw [plaquetteHolonomy_eq_faceEdges]
    simp
  simp [Fin.sum_univ_four, transportedForm, faceTransports, hv, transportSign,
    ComplexMatrix2.conjugateBy, edgeCoboundary, faceEdge, faceEdges, sub_eq_add_neg]
theorem one_mem_fieldsIn :
    (fun _ => (1 : ComplexMatrix2)) ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup := by apply _root_.YangMills.SharedProofs.p71645 <;> assumption
theorem holdsOnPeriodicLevel (hE : ComplexMatrix2.NormExpLogBasics)
    (hnr : ∀ b : Edge L n k j, b.IsPositivelyOriented → ¬ b.opposite.IsPositivelyOriented)
    (hpos : ∀ p : Face L n k j, ∀ b ∈ faceEdges p, b.IsPositivelyOriented)
    (hfin : (univ : Set (Face L n k j)).Finite) : HoldsOnPeriodicLevel L n k j := by
  intro B hB
  have hs : ∀ p, p ∈ hfin.toFinset := fun p => by simp
  have main : ∀ U ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup,
      (∀ p : Face L n k j, HoldsAtFace U B p) ∧
      (∑ᶠ p : Face L n k j, secondDerivExpr (transportedForm U B p)
        (PeriodicLattice.plaquetteHolonomy U p)) = complexActionHessian U B B ∧
      (∑ᶠ p : Face L n k j, firstDerivExpr (transportedForm U B p)
        (PeriodicLattice.plaquetteHolonomy U p)) = complexActionDeriv U B := by
    intro U hU
    have hat := fun p => faceTerm_derivs hE hnr (hpos p) hU hB
    have hG : (fun z : ℂ => complexAction (PeriodicLattice.expTwist (z • B) U)) =
        fun z => ∑ p ∈ hfin.toFinset,
          complexFaceTerm (PeriodicLattice.expTwist (z • B) U) p := by
      funext z
      exact finsum_eq_sum_of_support_subset _ fun p _ => hs p
    obtain ⟨h₁, h₂⟩ := finset_sum_derivs hfin.toFinset
      (fun p (t : ℂ) => complexFaceTerm (PeriodicLattice.expTwist (t • B) U) p)
      (fun p => firstDerivExpr (transportedForm U B p) (PeriodicLattice.plaquetteHolonomy U p))
      (fun p => secondDerivExpr (transportedForm U B p) (PeriodicLattice.plaquetteHolonomy U p))
      (fun p _ => (hat p).2.1) (fun p _ => (hat p).2.2.1) (fun p _ => (hat p).2.2.2)
    refine ⟨fun p => ⟨(hat p).1, (hat p).2.2.1, (hat p).2.2.2⟩, ?_, ?_⟩
    · rw [finsum_eq_sum_of_support_subset _ fun p _ => hs p, ← h₂, ← hG]
      exact (mixedDirectionalDeriv_self_eq
        (fun X => complexAction (PeriodicLattice.expTwist X U)) B).symm
    · rw [finsum_eq_sum_of_support_subset _ fun p _ => hs p, ← h₁, ← hG]
      exact (directionalDeriv_eq_deriv_line
        (fun X => complexAction (PeriodicLattice.expTwist X U)) B).symm
  refine ⟨main, ?_⟩
  rw [← (main _ one_mem_fieldsIn).2.1]
  refine finsum_congr fun p => ?_
  have hv : PeriodicLattice.plaquetteHolonomy (fun _ : Edge L n k j => (1 : ComplexMatrix2)) p = 1 := by
    rw [plaquetteHolonomy_eq_faceEdges]
    simp
  rw [hv, secondDerivExpr_one, sum_transportedForm_one]
end FiniteSide
section Infinite
variable {a : ℝ}
theorem link_pos_or_opposite_pos (b : InfiniteLattice.Link a) :
    b.IsPositivelyOriented ∨ b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.InfiniteLattice.GibbsForms.isPositivelyOriented_or_opposite <;> assumption
theorem link_opposite_not_pos (ha : 0 < a) {b : InfiniteLattice.Link a}
    (h : b.IsPositivelyOriented) : ¬ b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.InfiniteLattice.Link.opposite_not_isPositivelyOriented <;> assumption
theorem fullSpace_faceVariable_eq (V : InfiniteLattice.Link a → ComplexMatrix2)
    (p : InfiniteLattice.ElementaryPlaquette a) :
    FullSpace.faceVariable V p = V (FullSpace.faceEdge p 0) * V (FullSpace.faceEdge p 1) *
      V (FullSpace.faceEdge p 2).opposite * V (FullSpace.faceEdge p 3).opposite := by
  simp [FullSpace.faceVariable, FullSpace.linkHolonomy, FullSpace.faceBoundary,
    FullSpace.faceEdge, FullSpace.faceEdges, mul_assoc]
theorem fullSpace_faceEdge_mem (p : InfiniteLattice.ElementaryPlaquette a) (i : Fin 4) :
    FullSpace.faceEdge p i ∈ FullSpace.faceEdges p := List.getElem_mem _
theorem fullSpace_faceVariable_expTwist (ha : 0 < a) {p : InfiniteLattice.ElementaryPlaquette a}
    (hp : ∀ b ∈ FullSpace.faceEdges p, b.IsPositivelyOriented)
    (A U : InfiniteLattice.Link a → ComplexMatrix2) :
    FullSpace.faceVariable (FullSpace.expTwist A U) p =
      cycleWord fun i =>
        ComplexMatrix2.matExp (Complex.I • A (FullSpace.faceEdge p i)) *
          U (FullSpace.faceEdge p i) := by
  have hfor : ∀ i, FullSpace.expTwist A U (FullSpace.faceEdge p i) =
      ComplexMatrix2.matExp (Complex.I • A (FullSpace.faceEdge p i)) *
        U (FullSpace.faceEdge p i) := fun i =>
    if_pos (hp _ (fullSpace_faceEdge_mem p i))
  have hrev : ∀ i, FullSpace.expTwist A U (FullSpace.faceEdge p i).opposite =
      (ComplexMatrix2.matExp (Complex.I • A (FullSpace.faceEdge p i)) *
        U (FullSpace.faceEdge p i))⁻¹ :=
    fun i => if_neg (link_opposite_not_pos ha (hp _ (fullSpace_faceEdge_mem p i)))
  rw [fullSpace_faceVariable_eq, hfor, hfor, hrev, hrev]
  rfl
theorem fullSpace_expTwist_isField (hX : ComplexMatrix2.ExpLogEstimates) (ha : 0 < a)
    {A U : InfiniteLattice.Link a → ComplexMatrix2}
    (hA : FullSpace.IsEdgeFormIn PeriodicLattice.complexLieAlgebra A)
    (hU : FullSpace.IsFieldIn PeriodicLattice.complexGaugeGroup U) :
    FullSpace.IsFieldIn PeriodicLattice.complexGaugeGroup (FullSpace.expTwist A U) := by
  have hdet : ∀ b : InfiniteLattice.Link a, b.IsPositivelyOriented →
      (ComplexMatrix2.matExp (Complex.I • A b) * U b).det = 1 := fun b hb => by
    have hU' : (U b).det = 1 := hU.1 b
    have htr : ComplexMatrix2.fullTrace (A b) = 0 := hA.1 b hb
    have hI : ComplexMatrix2.fullTrace (Complex.I • A b) = 0 := by
      simp only [ComplexMatrix2.fullTrace] at htr ⊢
      rw [Matrix.trace_smul, htr, smul_zero]
    rw [Matrix.det_mul, hX.2.2.2.2.2.1, hU', hI]
    simp
  refine ⟨fun b => ?_, fun b => ?_⟩
  · by_cases hb : b.IsPositivelyOriented
    · show (FullSpace.expTwist A U b).det = 1
      rw [FullSpace.expTwist, if_pos hb]
      exact hdet b hb
    · have hr := (link_pos_or_opposite_pos b).resolve_left hb
      show (FullSpace.expTwist A U b).det = 1
      rw [FullSpace.expTwist, if_neg hb]
      exact det_inv_of_det_eq_one (hdet _ hr)
  · by_cases hb : b.IsPositivelyOriented
    · have hr := link_opposite_not_pos ha hb
      rw [FullSpace.expTwist, if_neg hr, FullSpace.expTwist, if_pos hb]
      rfl
    · have hr := (link_pos_or_opposite_pos b).resolve_left hb
      rw [FullSpace.expTwist, if_pos hr, FullSpace.expTwist, if_neg hb,
        Matrix.nonsing_inv_nonsing_inv]
      rw [hdet _ hr]
      exact isUnit_one
theorem fullSpace_cycleWord_of_field {U : InfiniteLattice.Link a → ComplexMatrix2}
    (hU : FullSpace.IsFieldIn PeriodicLattice.complexGaugeGroup U)
    (B : InfiniteLattice.Link a → ComplexMatrix2) (p : InfiniteLattice.ElementaryPlaquette a) :
    FullSpace.faceVariable U p = cycleWord (fun i => U (FullSpace.faceEdge p i)) ∧
      FullSpace.transportedForm U B p =
        cycleTransported (fun i => U (FullSpace.faceEdge p i))
          (fun i => B (FullSpace.faceEdge p i)) := by
  have h : FullSpace.faceVariable U p = cycleWord (fun i => U (FullSpace.faceEdge p i)) := by
    rw [fullSpace_faceVariable_eq, hU.2, hU.2]
    rfl
  refine ⟨h, ?_⟩
  funext i
  simp only [FullSpace.transportedForm, FullSpace.faceTransports, h, cycleTransported]
theorem fullSpace_sum_transportedForm_one (B : InfiniteLattice.Link a → ComplexMatrix2)
    (p : InfiniteLattice.ElementaryPlaquette a) :
    ∑ i, FullSpace.transportedForm (fun _ => (1 : ComplexMatrix2)) B p i =
      FullSpace.edgeCoboundary B p := by
  have hv : FullSpace.faceVariable (fun _ : InfiniteLattice.Link a => (1 : ComplexMatrix2)) p = 1 := by
    rw [fullSpace_faceVariable_eq]
    simp
  simp [Fin.sum_univ_four, FullSpace.transportedForm, FullSpace.faceTransports, hv, transportSign,
    ComplexMatrix2.conjugateBy, FullSpace.edgeCoboundary, FullSpace.faceEdge, FullSpace.faceEdges,
    sub_eq_add_neg]
end Infinite
section Levels
variable {L k j : ℕ}
theorem fullSpace_faceTerm_derivs (hE : ComplexMatrix2.NormExpLogBasics)
    (ha : 0 < meshAt L k j) {p : FullSpace.Face L k j}
    (hp : ∀ b ∈ FullSpace.faceEdges p, b.IsPositivelyOriented)
    {U B : FullSpace.Edge L k j → ComplexMatrix2}
    (hU : U ∈ FullSpace.fieldsValuedIn L k j PeriodicLattice.complexGaugeGroup)
    (hB : B ∈ FullSpace.complexEdgeForms (meshAt L k j)) :
    (∀ t : ℂ, FullSpace.faceVariable (FullSpace.expTwist (t • B) U) p =
      expProduct (FullSpace.transportedForm U B p) t * FullSpace.faceVariable U p) ∧
    Differentiable ℂ
      (fun t : ℂ => FullSpace.complexFaceTerm (FullSpace.expTwist (t • B) U) p) ∧
    HasDerivAt (fun t : ℂ => FullSpace.complexFaceTerm (FullSpace.expTwist (t • B) U) p)
      (firstDerivExpr (FullSpace.transportedForm U B p) (FullSpace.faceVariable U p)) 0 ∧
    HasDerivAt (deriv fun t : ℂ => FullSpace.complexFaceTerm (FullSpace.expTwist (t • B) U) p)
      (secondDerivExpr (FullSpace.transportedForm U B p) (FullSpace.faceVariable U p)) 0 := by
  obtain ⟨hw, hy⟩ := fullSpace_cycleWord_of_field hU B p
  have hV : ∀ i, (U (FullSpace.faceEdge p i)).det = 1 := fun i => hU.1 _
  have hA : ∀ i, ComplexMatrix2.fullTrace (B (FullSpace.faceEdge p i)) = 0 := fun i =>
    hB.1 _ (hp _ (fullSpace_faceEdge_mem p i))
  have hline : (fun t : ℂ => FullSpace.complexFaceTerm (FullSpace.expTwist (t • B) U) p) =
      lineTerm (FullSpace.transportedForm U B p) (FullSpace.faceVariable U p) := by
    rw [hw, hy, ← lineTerm_of_cycleWord hE hV]
    funext t
    simp only [FullSpace.complexFaceTerm, fullSpace_faceVariable_expTwist ha hp, Pi.smul_apply]
  have hj := lineTerm_derivs (FullSpace.transportedForm U B p)
    (W := FullSpace.faceVariable U p)
    (by rw [hy]; exact fullTrace_sum_cycleTransported hV hA) (by rw [hw]; exact det_cycleWord hV)
  rw [hline]
  refine ⟨fun t => ?_, hj⟩
  rw [fullSpace_faceVariable_expTwist ha hp, hw, hy]
  exact cycleWord_twisted hE _ hV t
end Levels
theorem isHolomorphicVia_of_differentiable {τ : Type} [Fintype τ] {m : ℕ} (ν : τ ≃ Fin m)
    {F : (τ → ComplexMatrix2) → ℂ} (hF : Differentiable ℂ F) :
    Coordinates.ComplexCoordinates.IsHolomorphicVia (GroupLieProduct.matrixPiEquiv ν)
      (Equiv.funUnique (Fin 1) ℂ).symm univ F := by
  let e := GroupLieProduct.matrixPiEquiv ν
  let pos : Fin (Coordinates.ComplexCoordinates.productDim
      fun _ : Fin m => Coordinates.ComplexCoordinates.Component.matrix) → (i : Fin m) × Fin 4 :=
    fun q => (finSigmaFinEquiv
      (n := fun i => ((fun _ : Fin m => Coordinates.ComplexCoordinates.Component.matrix) i).dim)).symm q
  have key : ∀ (z : τ → ComplexMatrix2) (q), e z q =
      Coordinates.ComplexCoordinates.matrixEquiv (z (ν.symm (pos q).1)) (pos q).2 :=
    fun _ _ => rfl
  let eL : (τ → ComplexMatrix2) ≃ₗ[ℂ] Coordinates.ComplexCoordinates
      (Coordinates.ComplexCoordinates.productDim
        fun _ : Fin m => Coordinates.ComplexCoordinates.Component.matrix) :=
    { e with
      map_add' := fun x y => by
        funext q
        exact key (x + y) q
      map_smul' := fun t x => by
        funext q
        exact key (t • x) q }
  let eC := eL.toContinuousLinearEquiv
  have himage : e '' univ = univ := Set.image_univ_of_surjective e.surjective
  have hdiff : Differentiable ℂ ((Equiv.funUnique (Fin 1) ℂ).symm ∘ F ∘ e.symm) := by
    have h₁ : Differentiable ℂ (F ∘ eC.symm) := hF.comp eC.symm.differentiable
    exact differentiable_pi.2 fun _ => h₁
  refine ⟨himage ▸ isOpen_univ, hdiff.continuous.continuousOn, fun z _ i => ?_⟩
  refine Eventually.of_forall fun ζ => ?_
  have hd : DifferentiableAt ℂ
      (fun ζ : ℂ => z + ζ • Coordinates.ComplexCoordinates.stdBasisVector i) ζ := by
    fun_prop
  exact DifferentiableAt.comp (g := (Equiv.funUnique (Fin 1) ℂ).symm ∘ F ∘ e.symm) ζ
    hdiff.differentiableAt hd
section Levels
variable {L k j : ℕ}
def extendByZero (F : Finset (FullSpace.Edge L k j)) (w : F → ComplexMatrix2)
    (b : FullSpace.Edge L k j) : ComplexMatrix2 :=
  open Classical in if h : b ∈ F then w ⟨b, h⟩ else 0
def adjugateInverse (X : ComplexMatrix2) : ComplexMatrix2 :=
  ComplexMatrix2.fullTrace X • (1 : ComplexMatrix2) - X
def presentedFaceTerm (F : Finset (FullSpace.Edge L k j)) (w : F → ComplexMatrix2)
    (p : FullSpace.Face L k j) : ℂ :=
  1 - (1 / 2) * ComplexMatrix2.fullTrace (_root_.YangMills.Construction.Tower.FaceTermDerivatives.extendByZero F w (FullSpace.faceEdge p 0) *
    _root_.YangMills.Construction.Tower.FaceTermDerivatives.extendByZero F w (FullSpace.faceEdge p 1) *
    adjugateInverse (_root_.YangMills.Construction.Tower.FaceTermDerivatives.extendByZero F w (FullSpace.faceEdge p 2)) *
    adjugateInverse (_root_.YangMills.Construction.Tower.FaceTermDerivatives.extendByZero F w (FullSpace.faceEdge p 3)))
def traceCLM : ComplexMatrix2 →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap (Matrix.traceLinearMap (Fin 2) ℂ ℂ)
theorem differentiable_extendByZero (F : Finset (FullSpace.Edge L k j))
    (b : FullSpace.Edge L k j) :
    Differentiable ℂ fun q : F ⊕ Empty → ComplexMatrix2 =>
      _root_.YangMills.Construction.Tower.FaceTermDerivatives.extendByZero F (fun c => q (.inl c)) b := by
  by_cases h : b ∈ F
  · simp only [_root_.YangMills.Construction.Tower.FaceTermDerivatives.extendByZero, dif_pos h]
    exact differentiable_apply _
  · simp only [_root_.YangMills.Construction.Tower.FaceTermDerivatives.extendByZero, dif_neg h]
    exact differentiable_const _
theorem differentiable_adjugateInverse {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : E → ComplexMatrix2} (hf : Differentiable ℂ f) :
    Differentiable ℂ fun x => adjugateInverse (f x) := by
  have h : Differentiable ℂ fun x => traceCLM (f x) := traceCLM.differentiable.comp hf
  exact (h.smul_const (1 : ComplexMatrix2)).sub hf
theorem differentiable_presentedFaceTerm (F : Finset (FullSpace.Edge L k j))
    (p : FullSpace.Face L k j) :
    Differentiable ℂ fun q : F ⊕ Empty → ComplexMatrix2 =>
      presentedFaceTerm F (fun c => q (.inl c)) p := by
  have h := (((differentiable_extendByZero F (FullSpace.faceEdge p 0)).mul
    (differentiable_extendByZero F (FullSpace.faceEdge p 1))).mul
    (differentiable_adjugateInverse
      (differentiable_extendByZero F (FullSpace.faceEdge p 2)))).mul
    (differentiable_adjugateInverse
      (differentiable_extendByZero F (FullSpace.faceEdge p 3)))
  have h₂ := (traceCLM.differentiable.comp h).const_mul (1 / 2 : ℂ)
  exact (differentiable_const 1).sub h₂
theorem presentedFaceTerm_eq {F : Finset (FullSpace.Edge L k j)}
    {U : FullSpace.Edge L k j → ComplexMatrix2}
    (hU : U ∈ FullSpace.fieldsValuedIn L k j PeriodicLattice.complexGaugeGroup)
    {p : FullSpace.Face L k j} (hp : ∀ i, FullSpace.faceEdge p i ∈ F) :
    presentedFaceTerm F (FullSpace.restrictToEdges F U) p = FullSpace.complexFaceTerm U p := by
  have hv : ∀ i, _root_.YangMills.Construction.Tower.FaceTermDerivatives.extendByZero F (FullSpace.restrictToEdges F U) (FullSpace.faceEdge p i) =
      U (FullSpace.faceEdge p i) := fun i => dif_pos (hp i)
  have hi : ∀ i, adjugateInverse (U (FullSpace.faceEdge p i)) =
      (U (FullSpace.faceEdge p i))⁻¹ := fun i => (inv_eq_trace_smul_one_sub (hU.1 _)).symm
  simp only [presentedFaceTerm, hv, hi, FullSpace.complexFaceTerm,
    (fullSpace_cycleWord_of_field hU 0 p).1, cycleWord]
theorem exists_holomorphic_presentation
    (hC : GroupLieProduct.ExpChartHolomorphy.ExpChartTheory)
    (β : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless)
    {h : (FullSpace.Edge L k j → ComplexMatrix2) → ℂ} (Ω : Finset (FullSpace.Face L k j))
    (hh : ∀ U, h U = ∑ p ∈ Ω, FullSpace.complexFaceTerm U p)
    {F : Finset (FullSpace.Edge L k j)} (hF : FullSpace.IsFinitePositiveEdgeSet F)
    (hΩ : ∀ p ∈ Ω, ∀ i, FullSpace.faceEdge p i ∈ F) {U : FullSpace.Edge L k j → ComplexMatrix2}
    (hU : U ∈ FullSpace.fieldsValuedIn L k j PeriodicLattice.complexGaugeGroup) :
    ∃ w : FullSpace.LocalData L k j ℂ,
      FullSpace.IsLocalPresentation PeriodicLattice.complexGaugeGroup
        (FullSpace.fieldsValuedIn L k j PeriodicLattice.complexGaugeGroup) h U
        w.support w.region w.fn ∧
      FullSpace.holomorphicPresentations L k j β (Equiv.funUnique (Fin 1) ℂ).symm
        w.support w.region w.fn := by
  let f : (F → ComplexMatrix2) → ℂ := fun w => ∑ p ∈ Ω, presentedFaceTerm F w p
  refine ⟨⟨F, FullSpace.edgeProduct PeriodicLattice.complexGaugeGroup F, f⟩,
    ⟨hF, ⟨univ, isOpen_univ, (univ_inter _).symm⟩, fun b => hU.1 _, fun U' hU' _ => ?_⟩, ?_⟩
  · show h U' = ∑ p ∈ Ω, presentedFaceTerm F (FullSpace.restrictToEdges F U') p
    rw [hh]
    exact Finset.sum_congr rfl fun p hp => (presentedFaceTerm_eq hU' (hΩ p hp)).symm
  · show GroupLieProduct.IsHolomorphicToCoords β (Equiv.funUnique (Fin 1) ℂ).symm
      (GroupLieProduct.asGroupFactors '' FullSpace.edgeProduct PeriodicLattice.complexGaugeGroup F)
      fun q => f fun b => q (.inl b)
    have hset : GroupLieProduct.asGroupFactors ''
          FullSpace.edgeProduct PeriodicLattice.complexGaugeGroup F =
        univ ∩ GroupLieProduct F Empty := by
      ext q
      constructor
      · rintro ⟨V, hV, rfl⟩
        refine ⟨trivial, ?_⟩
        rintro (i | c)
        · exact hV i
        · exact c.elim
      · rintro ⟨-, hq⟩
        refine ⟨fun b => q (.inl b), fun b => hq (.inl b), ?_⟩
        funext i
        rcases i with i | c
        · rfl
        · exact c.elim
    have hdiff : Differentiable ℂ fun q : F ⊕ Empty → ComplexMatrix2 => f fun b => q (.inl b) := by
      have hs := Differentiable.fun_sum (𝕜 := ℂ) (u := Ω)
        (A := fun p (q : F ⊕ Empty → ComplexMatrix2) => presentedFaceTerm F (fun c => q (.inl c)) p)
        fun p _ => differentiable_presentedFaceTerm F p
      exact hs
    have hth := isHolomorphicVia_of_differentiable (Fintype.equivFin (F ⊕ Empty)) hdiff
    rw [hset]
    exact (((hC.2.2.2.1 F Empty).2.2 ℂ 1 _ _ _ univ _ hth).2 β)
theorem valueViaPresentation_eventuallyEq (hX : ComplexMatrix2.ExpLogEstimates)
    (ha : 0 < meshAt L k j) {K : FullSpace.PresentationClass L k j ℂ}
    {h : (FullSpace.Edge L k j → ComplexMatrix2) → ℂ} {U B : FullSpace.Edge L k j → ComplexMatrix2}
    (hU : U ∈ FullSpace.fieldsValuedIn L k j PeriodicLattice.complexGaugeGroup)
    (hB : B ∈ FullSpace.complexEdgeForms (meshAt L k j))
    (hex : ∃ w : FullSpace.LocalData L k j ℂ,
      FullSpace.IsLocalPresentation PeriodicLattice.complexGaugeGroup
        (FullSpace.fieldsValuedIn L k j PeriodicLattice.complexGaugeGroup) h U
        w.support w.region w.fn ∧
      K w.support w.region w.fn) :
    (fun z : ℂ => FullSpace.valueViaPresentation PeriodicLattice.complexGaugeGroup
        (FullSpace.fieldsValuedIn L k j PeriodicLattice.complexGaugeGroup) K h U (z • B)) =ᶠ[𝓝 0]
      fun z => h (FullSpace.expTwist (z • B) U) := by
  have hw := Classical.epsilon_spec hex
  set w := FullSpace.chosenPresentation PeriodicLattice.complexGaugeGroup
    (FullSpace.fieldsValuedIn L k j PeriodicLattice.complexGaugeGroup) K h U with hwdef
  obtain ⟨⟨hF, ⟨O', hO', hO⟩, hUO, hval⟩, -⟩ : FullSpace.IsLocalPresentation
        PeriodicLattice.complexGaugeGroup
        (FullSpace.fieldsValuedIn L k j PeriodicLattice.complexGaugeGroup) h U
        w.support w.region w.fn ∧
      K w.support w.region w.fn := hw
  let c : ℂ → w.support → ComplexMatrix2 := fun z b =>
    ComplexMatrix2.matExp (Complex.I • (z • B) b) * U b
  have hc : Continuous c := by
    refine continuous_pi fun b => ?_
    have h₁ : Continuous fun z : ℂ => ComplexMatrix2.matExp (z • (Complex.I • B b)) :=
      continuous_iff_continuousAt.2 fun z =>
        (hasDerivAt_exp_smul_const (Complex.I • B b) z).continuousAt
    have h₂ : (fun z : ℂ => ComplexMatrix2.matExp (Complex.I • (z • B) b)) =
        fun z : ℂ => ComplexMatrix2.matExp (z • (Complex.I • B b)) := by
      funext z
      rw [Pi.smul_apply, smul_comm]
    rw [← h₂] at h₁
    exact h₁.mul continuous_const
  have hc0 : c 0 = FullSpace.restrictToEdges w.support U := by
    funext b
    simp [c, FullSpace.restrictToEdges]
  have hUO' : FullSpace.restrictToEdges w.support U ∈ O' := by
    rw [hO] at hUO
    exact hUO.1
  have hnear : ∀ᶠ z in 𝓝 (0 : ℂ), c z ∈ O' :=
    hc.continuousAt.eventually (by rw [hc0]; exact hO'.mem_nhds hUO')
  filter_upwards [hnear] with z hz
  have hconf : FullSpace.expTwist (z • B) U ∈
      FullSpace.fieldsValuedIn L k j PeriodicLattice.complexGaugeGroup :=
    fullSpace_expTwist_isField hX ha ((FullSpace.complexEdgeForms _).smul_mem z hB) hU
  have hbv : FullSpace.restrictToEdges w.support (FullSpace.expTwist (z • B) U) = c z := by
    funext b
    exact if_pos (hF.2 b b.2)
  have hmem : FullSpace.restrictToEdges w.support (FullSpace.expTwist (z • B) U) ∈ w.region := by
    rw [hO, hbv]
    refine ⟨hz, fun b => ?_⟩
    have := hconf.1 b
    rw [← hbv]
    exact this
  rw [hval _ hconf hmem, hbv]
  rfl
theorem holdsOnFullSpaceLevel (hE : ComplexMatrix2.NormExpLogBasics)
    (hX : ComplexMatrix2.ExpLogEstimates)
    (hC : GroupLieProduct.ExpChartHolomorphy.ExpChartTheory)
    (ha : 0 < meshAt L k j)
    (hW : FaceEdgeFinsets.Unbounded.HoldsOnFullSpace L k j) : HoldsOnFullSpaceLevel L k j := by
  intro B hB
  have hpos := hW.1.2
  refine ⟨fun U hU p => ?_, fun hfs => ?_⟩
  · have hat := fullSpace_faceTerm_derivs hE ha (hpos p) hU hB
    exact ⟨hat.1, hat.2.2.1, hat.2.2.2⟩
  have hSpos : ∀ b ∈ FullSpace.edgeSupport B, b.IsPositivelyOriented := fun b hb => hb.1
  obtain ⟨hΩfin, -, -, -⟩ := hW.2.1 _ hfs hSpos
  obtain ⟨hbf, hbne, hbpos⟩ := hW.2.2 _ hfs hSpos
  have hF : FullSpace.IsFinitePositiveEdgeSet hbf.toFinset :=
    ⟨by simpa using hbne, fun b hb => hbpos b (by simpa using hb)⟩
  have hΩF : ∀ p ∈ hΩfin.toFinset, ∀ i, FullSpace.faceEdge p i ∈ hbf.toFinset := fun p hp i => by
    rw [Set.Finite.mem_toFinset]
    exact Or.inr ⟨p, by simpa using hp, fullSpace_faceEdge_mem p i⟩
  have hY : ∀ (U : FullSpace.Edge L k j → ComplexMatrix2) (p : FullSpace.Face L k j),
      p ∉ hΩfin.toFinset → FullSpace.transportedForm U B p = 0 := fun U p hp => by
    funext i
    have hzero : B (FullSpace.faceEdge p i) = 0 := by
      by_contra hne
      refine hp ?_
      rw [Set.Finite.mem_toFinset]
      exact ⟨_, ⟨hpos p _ (fullSpace_faceEdge_mem p i), hne⟩, fullSpace_faceEdge_mem p i⟩
    simp [FullSpace.transportedForm, hzero, ComplexMatrix2.conjugateBy]
  have main : ∀ U ∈ FullSpace.fieldsValuedIn L k j PeriodicLattice.complexGaugeGroup,
      (∑ᶠ p : FullSpace.Face L k j, secondDerivExpr (FullSpace.transportedForm U B p)
        (FullSpace.faceVariable U p)) = FullSpace.complexActionHessian U B B ∧
      (∑ᶠ p : FullSpace.Face L k j, firstDerivExpr (FullSpace.transportedForm U B p)
        (FullSpace.faceVariable U p)) = FullSpace.complexActionDeriv U B := by
    intro U hU
    have hat := fun p => fullSpace_faceTerm_derivs hE ha (hpos p) hU hB
    have hsum : ∀ U' : FullSpace.Edge L k j → ComplexMatrix2,
        FullSpace.faceTermSum (FaceEdgeFinsets.Unbounded.facesMeeting (FullSpace.edgeSupport B))
          U' = ∑ p ∈ hΩfin.toFinset, FullSpace.complexFaceTerm U' p := fun U' =>
      finsum_mem_eq_finite_toFinset_sum _ hΩfin
    have hex := exists_holomorphic_presentation hC OneLoop.pauliBasis hΩfin.toFinset hsum hF
      hΩF hU
    have hline := valueViaPresentation_eventuallyEq hX ha hU hB hex
    obtain ⟨h₁, h₂⟩ := finset_sum_derivs hΩfin.toFinset
      (fun p (t : ℂ) => FullSpace.complexFaceTerm (FullSpace.expTwist (t • B) U) p)
      (fun p => firstDerivExpr (FullSpace.transportedForm U B p) (FullSpace.faceVariable U p))
      (fun p => secondDerivExpr (FullSpace.transportedForm U B p) (FullSpace.faceVariable U p))
      (fun p _ => (hat p).2.1) (fun p _ => (hat p).2.2.1) (fun p _ => (hat p).2.2.2)
    have hG : (fun z : ℂ => FullSpace.faceTermSum
          (FaceEdgeFinsets.Unbounded.facesMeeting (FullSpace.edgeSupport B))
          (FullSpace.expTwist (z • B) U)) =
        fun z => ∑ p ∈ hΩfin.toFinset,
          FullSpace.complexFaceTerm (FullSpace.expTwist (z • B) U) p :=
      funext fun z => hsum _
    rw [← hG] at h₁ h₂
    constructor
    · rw [finsum_eq_sum_of_support_subset (s := hΩfin.toFinset) _ fun p hp => by
        by_contra hn
        exact hp (by
          show secondDerivExpr _ _ = 0
          rw [hY U p hn]
          exact secondDerivExpr_zero_left _), ← h₂,
        ← hline.deriv.deriv_eq, FullSpace.complexActionHessian, union_self]
      exact (mixedDirectionalDeriv_self_eq _ B).symm
    · rw [finsum_eq_sum_of_support_subset (s := hΩfin.toFinset) _ fun p hp => by
        by_contra hn
        exact hp (by
          show firstDerivExpr _ _ = 0
          rw [hY U p hn]
          exact firstDerivExpr_zero_left _), ← h₁, ← hline.deriv_eq]
      exact (directionalDeriv_eq_deriv_line _ B).symm
  refine ⟨main, ?_⟩
  have hone : (fun _ => (1 : ComplexMatrix2)) ∈
      FullSpace.fieldsValuedIn L k j PeriodicLattice.complexGaugeGroup :=
    ⟨fun _ => Matrix.det_one, fun _ => inv_one.symm⟩
  rw [← (main _ hone).1]
  refine finsum_congr fun p => ?_
  have hv : FullSpace.faceVariable (fun _ : FullSpace.Edge L k j => (1 : ComplexMatrix2)) p = 1 := by
    rw [fullSpace_faceVariable_eq]
    simp
  rw [hv, secondDerivExpr_one, fullSpace_sum_transportedForm_one]
end Levels
theorem statement_holds (hE : ComplexMatrix2.NormExpLogBasics)
    (hX : ComplexMatrix2.ExpLogEstimates)
    (hC : GroupLieProduct.ExpChartHolomorphy.ExpChartTheory)
    (hF : FaceEdgeFinsets.FacesAndEdgesFinite) : Statement := by
  intro L hL k j hj
  have hL0 : (0 : ℝ) < L := by
    have := hL.2
    exact_mod_cast (by omega : 0 < L)
  refine ⟨fun n hn => ?_, ?_⟩
  · obtain ⟨⟨-, hpos⟩, -, -, hfin, -⟩ := (hF L hL k j hj).1 n hn
    refine holdsOnPeriodicLevel hE (fun b hb hr => ?_) hpos hfin
    rcases PeriodicLattice.MatrixValued.xor_isPositivelyOriented_opposite (by have := hL.2; omega)
      (by show -(n : ℤ) < (k : ℤ) - (j : ℤ); omega) b with ⟨-, h'⟩ | ⟨-, h⟩
    · exact h' hr
    · exact h hb
  · exact holdsOnFullSpaceLevel hE hX hC (zpow_pos hL0 _) (hF L hL k j hj).2
end YangMills.Construction.Tower.FaceTermDerivatives
end
