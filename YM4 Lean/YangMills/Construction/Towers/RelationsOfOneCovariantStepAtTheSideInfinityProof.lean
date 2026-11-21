import YangMills.Construction.Towers.ComplexAveragesFormedLevelByLevelProof
import YangMills.Construction.Matrices.UnitaryLogConjugation
import YangMills.Construction.Towers.ConfigurationsFormedLevelByLevelOnThePolydiscs
import YangMills.Construction.Towers.FactsOfTheLeftChart
import YangMills.Construction.Towers.GaugeDirectionsInTheLeftChartProof
import YangMills.Construction.Towers.KernelsOfThreeMapsOfATowerProof
import YangMills.Construction.Towers.LinearityOfTheCovariantStepAtTheSideInfinity
import YangMills.Construction.Towers.RelationsOfOneCovariantStepAtTheSideInfinity
import Mathlib
set_option autoImplicit false
open Set Filter YangMills.Construction.Matrices YangMills.Construction.Matrices.GroupLieProduct YangMills.Construction.Coordinates
open scoped Topology Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.StepRelations
open YangMills.Construction.Tower.LeftChartFields
open YangMills.Construction.Tower.BondSetFields YangMills.Construction.Tower.DoubleBlockPolydisc
open YangMills.Construction.Tower.MeanStableFields.Infinite
section UnimodularRules
open YangMills.Construction.Coordinates.ComplexCoordinates
variable {ι : Type} [Fintype ι]
theorem inv_mem_unitDeterminant {X : ComplexMatrix2} (h : X ∈ ComplexMatrix2.unitDeterminant) :
    X⁻¹ ∈ ComplexMatrix2.unitDeterminant := by apply _root_.YangMills.SharedProofs.p413 <;> assumption
theorem inv_inv_of_mem_unitDeterminant {X : ComplexMatrix2}
    (h : X ∈ ComplexMatrix2.unitDeterminant) : X⁻¹⁻¹ = X := by apply _root_.YangMills.Construction.Tower.LevelwiseMeans.inv_inv_of_mem_unitDeterminant <;> assumption
variable (H : ExpChartHolomorphy.ExpChartTheory)
  (β : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless)
include H
theorem component_isHolomorphicToUnimodular {W : Set (ι ⊕ Empty → ComplexMatrix2)}
    (hW : ComplexMatrix2.IsRelativelyOpen (GroupLieProduct ι Empty) W) (i : ι) :
    IsHolomorphicToUnimodular β W fun P => P (.inl i) := by apply _root_.YangMills.Construction.Tower.LevelwiseMeans.isHolomorphicToUnimodular_component <;> assumption
end UnimodularRules
section FactorPoints
variable {σ : Type}
theorem asGroupFactors_image (U : Set (σ → ComplexMatrix2)) :
    asGroupFactors '' U = leftComponents ⁻¹' U := by apply _root_.YangMills.Construction.Tower.LevelwiseMeans.image_asGroupFactors <;> assumption
theorem asGroupFactors_leftComponents (P : σ ⊕ Empty → ComplexMatrix2) :
    asGroupFactors (leftComponents P) = P := by apply _root_.YangMills.Construction.Tower.LevelwiseMeans.asGroupFactors_leftComponents <;> assumption
theorem asGroupFactors_mem_iff {w : σ → ComplexMatrix2} :
    asGroupFactors w ∈ GroupLieProduct σ Empty ↔ w ∈ unimodularPi σ := by apply _root_.YangMills.Construction.Tower.LevelwiseMeans.asGroupFactors_mem_iff <;> assumption
end FactorPoints
abbrev scalarCoords : ℂ ≃ ComplexCoordinates 1 := (Equiv.funUnique (Fin 1) ℂ).symm
theorem differentiableAt_along_leftChart (H : ExpChartHolomorphy.ExpChartTheory) {Λ : LatticeData}
    (hΛ : Λ.HolomorphicGradientExists) {σ : Type} [Fintype σ] [Nonempty σ]
    (ι : σ → Λ.PosLink) {U₀ : Set (σ → ComplexMatrix2)}
    (hU₀ : ComplexMatrix2.IsRelativelyOpen (unimodularPi σ) U₀)
    {Φ : (σ → ComplexMatrix2) → ComplexMatrix2}
    (hent : ∀ (β : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless) (r s : Fin 2),
      IsHolomorphicToCoords β scalarCoords (leftComponents ⁻¹' U₀)
        fun P => Φ (leftComponents P) r s)
    {U : Λ.Link → ComplexMatrix2} (hU : U ∈ Λ.fields PeriodicLattice.complexGaugeGroup)
    (hUU : (fun s => U (Λ.incl (ι s))) ∈ U₀) {B : Λ.Link → ComplexMatrix2} (hB : B ∈ Λ.cforms) :
    DifferentiableAt ℂ (fun t : ℂ => Φ fun s =>
      leftExpMul (t • B (Λ.incl (ι s))) (U (Λ.incl (ι s)))) 0 := by apply _root_.YangMills.Construction.Tower.LevelwiseMeans.differentiableAt_along_leftChart <;> assumption
section MatrixCurves
theorem hasDerivAt_restrict_real {g : ℂ → ComplexMatrix2} {d : ComplexMatrix2} {t₀ : ℝ}
    (h : HasDerivAt g d (t₀ : ℂ)) : HasDerivAt (fun t : ℝ => g (t : ℂ)) d t₀ := by
  refine hasDerivAt_pi.2 fun a => hasDerivAt_pi.2 fun b => ?_
  have h1 : HasDerivAt (fun t => g t a b) (d a b) (t₀ : ℂ) :=
    hasDerivAt_pi.1 (hasDerivAt_pi.1 h a) b
  exact h1.comp_ofReal
theorem matExp_inv (X : ComplexMatrix2) :
    (ComplexMatrix2.matExp X)⁻¹ = ComplexMatrix2.matExp (-X) := by apply _root_.YangMills.SharedProofs.p3399 <;> assumption
theorem hasDerivAt_matExp_smul (X : ComplexMatrix2) (s : ℂ) :
    HasDerivAt (fun s : ℂ => ComplexMatrix2.matExp (s • X)) (ComplexMatrix2.matExp (s • X) * X) s :=
  hasDerivAt_exp_smul_const X s
def twistedConj (A B M : ComplexMatrix2) (s : ℂ) : ComplexMatrix2 :=
  ComplexMatrix2.matExp (s • (Complex.I • A)) * M * ComplexMatrix2.matExp (s • (-(Complex.I • B)))
theorem hasDerivAt_twistedConj (A B M : ComplexMatrix2) (s : ℂ) :
    HasDerivAt (twistedConj A B M)
      (ComplexMatrix2.matExp (s • (Complex.I • A)) * (Complex.I • A) * M *
          ComplexMatrix2.matExp (s • (-(Complex.I • B))) +
        ComplexMatrix2.matExp (s • (Complex.I • A)) * M *
          (ComplexMatrix2.matExp (s • (-(Complex.I • B))) * (-(Complex.I • B)))) s :=
  ((hasDerivAt_matExp_smul _ s).mul_const M).mul (hasDerivAt_matExp_smul _ s)
theorem hasDerivAt_twistedConj_zero (A B M : ComplexMatrix2) :
    HasDerivAt (twistedConj A B M) (Complex.I • (A * M - M * B)) 0 := by
  have h := hasDerivAt_twistedConj A B M 0
  have e : ComplexMatrix2.matExp ((0 : ℂ) • (Complex.I • A)) * (Complex.I • A) * M *
        ComplexMatrix2.matExp ((0 : ℂ) • (-(Complex.I • B))) +
      ComplexMatrix2.matExp ((0 : ℂ) • (Complex.I • A)) * M *
        (ComplexMatrix2.matExp ((0 : ℂ) • (-(Complex.I • B))) * (-(Complex.I • B))) =
      Complex.I • (A * M - M * B) := by
    simp [ComplexMatrix2.matExp, NormedSpace.exp_zero, sub_eq_add_neg]
  rwa [e] at h
theorem twistedConj_zero (A B M : ComplexMatrix2) : twistedConj A B M 0 = M := by
  simp [twistedConj, ComplexMatrix2.matExp, NormedSpace.exp_zero]
theorem matExp_mul_mul_inv_eq_twistedConj (A B M : ComplexMatrix2) (s : ℂ) :
    ComplexMatrix2.matExp (Complex.I • (s • A)) * M *
        (ComplexMatrix2.matExp (Complex.I • (s • B)))⁻¹ = twistedConj A B M s := by
  rw [matExp_inv, twistedConj, smul_comm Complex.I s A, smul_comm Complex.I s B, smul_neg]
end MatrixCurves
section FieldCurves
variable {L k j : ℕ}
theorem opposite_isPositivelyOriented_of_not (hL : Conventions.IsAdmissibleBlockingFactor L)
    {b : Edge L k j} (hb : ¬ b.IsPositivelyOriented) : b.opposite.IsPositivelyOriented := by
  have ha : 0 < meshAt L k j := by
    have hL0 : (0 : ℝ) < L := by exact_mod_cast (by have := hL.2; omega : 0 < L)
    exact zpow_pos hL0 _
  have h := InfiniteLattice.xor_mem_positiveLinks ha b
  simp only [InfiniteLattice.mem_positiveLinks_iff] at h
  rcases h with ⟨h₁, -⟩ | ⟨h₁, -⟩
  · exact absurd h₁ hb
  · exact h₁
theorem not_opposite_isPositivelyOriented (hL : Conventions.IsAdmissibleBlockingFactor L)
    {b : Edge L k j} (hb : b.IsPositivelyOriented) : ¬ b.opposite.IsPositivelyOriented := by
  have ha : 0 < meshAt L k j := by
    have hL0 : (0 : ℝ) < L := by exact_mod_cast (by have := hL.2; omega : 0 < L)
    exact zpow_pos hL0 _
  have h := InfiniteLattice.xor_mem_positiveLinks ha b
  simp only [InfiniteLattice.mem_positiveLinks_iff] at h
  rcases h with ⟨-, h₂⟩ | ⟨-, h₂⟩
  · exact h₂
  · exact absurd hb h₂
theorem extendOddly_congr (hL : Conventions.IsAdmissibleBlockingFactor L)
    {f g : Edge L k j → ComplexMatrix2}
    (h : ∀ b : Edge L k j, b.IsPositivelyOriented → f b = g b) : extendOddly f = extendOddly g := by
  funext b
  by_cases hb : b.IsPositivelyOriented
  · simp only [extendOddly, if_pos hb, h b hb]
  · simp only [extendOddly, if_neg hb, h _ (opposite_isPositivelyOriented_of_not hL hb)]
theorem conjugateBy_smul_add (W X Y : ComplexMatrix2) (z : ℂ) :
    ComplexMatrix2.conjugateBy W (z • X + Y) =
      z • ComplexMatrix2.conjugateBy W X + ComplexMatrix2.conjugateBy W Y := by
  simp [ComplexMatrix2.conjugateBy, mul_add, add_mul]
theorem conjugateBy_neg (W X : ComplexMatrix2) :
    ComplexMatrix2.conjugateBy W (-X) = -ComplexMatrix2.conjugateBy W X := by
  simp [ComplexMatrix2.conjugateBy]
theorem covDiff_smul_add {a : ℝ} (U : InfiniteLattice.Link a → ComplexMatrix2)
    (f f' : InfiniteLattice.LatticePoint a → ComplexMatrix2) (z : ℂ) :
    covDiff U (z • f + f') = z • covDiff U f + covDiff U f' := by
  funext b
  by_cases hb : b.IsPositivelyOriented
  · simp only [covDiff, extendOddly, if_pos hb, Pi.add_apply, Pi.smul_apply,
      conjugateBy_smul_add, smul_sub]
    abel
  · simp only [covDiff, extendOddly, if_neg hb, Pi.add_apply, Pi.smul_apply,
      conjugateBy_smul_add, smul_sub, smul_neg]
    abel
theorem covDiff_neg {a : ℝ} (U : InfiniteLattice.Link a → ComplexMatrix2)
    (f : InfiniteLattice.LatticePoint a → ComplexMatrix2) :
    covDiff U (-f) = -covDiff U f := by
  funext b
  by_cases hb : b.IsPositivelyOriented
  · simp only [covDiff, extendOddly, if_pos hb, Pi.neg_apply, conjugateBy_neg]
    abel
  · simp only [covDiff, extendOddly, if_neg hb, Pi.neg_apply, conjugateBy_neg]
    abel
theorem mem_complexGaugeGroup_of_compact {X : ComplexMatrix2}
    (h : X ∈ PeriodicLattice.compactGaugeGroup) : X ∈ PeriodicLattice.complexGaugeGroup :=
  (Matrix.mem_specialUnitaryGroup_iff.1 h).2
def gaugeOrbitCurve (f : Vertex L k j → ComplexMatrix2) (V : Edge L k j → ComplexMatrix2) (t : ℝ) :
    Edge L k j → ComplexMatrix2 :=
  gaugeAct (expVertexFn ((t : ℂ) • f)) V
theorem gaugeOrbitCurve_apply (f : Vertex L k j → ComplexMatrix2) (V : Edge L k j → ComplexMatrix2)
    (t : ℝ) (b : Edge L k j) :
    gaugeOrbitCurve f V t b = twistedConj (f b.initial) (f b.terminal) (V b) t :=
  matExp_mul_mul_inv_eq_twistedConj _ _ _ _
theorem gaugeOrbitCurve_zero (f : Vertex L k j → ComplexMatrix2) (V : Edge L k j → ComplexMatrix2) :
    gaugeOrbitCurve f V 0 = V := by
  funext b
  rw [gaugeOrbitCurve_apply, Complex.ofReal_zero, twistedConj_zero]
theorem expVertexFn_mem_compact (hI : ComplexMatrix2.UnitaryLogConjugationProperties)
    {f : Vertex L k j → ComplexMatrix2} (hf : ∀ x, f x ∈ ComplexMatrix2.hermitianTraceless) (t : ℝ)
    (x : Vertex L k j) : expVertexFn ((t : ℂ) • f) x ∈ PeriodicLattice.compactGaugeGroup := by
  have e : ((t : ℂ) • f) x = t • f x := by
    ext a b
    simp
  have h := (hI.1 (t • f x) (ComplexMatrix2.hermitianTraceless.smul_mem t (hf x))).2.2
  show ComplexMatrix2.matExp (Complex.I • ((t : ℂ) • f) x) ∈ _
  rw [e]
  exact h
theorem gaugeOrbitCurve_isFieldIn (hI : ComplexMatrix2.UnitaryLogConjugationProperties)
    {f : Vertex L k j → ComplexMatrix2} (hf : ∀ x, f x ∈ ComplexMatrix2.hermitianTraceless)
    {V : Edge L k j → ComplexMatrix2} (hV : V ∈ fieldsValuedIn L k j PeriodicLattice.complexGaugeGroup)
    (t : ℝ) : IsFieldIn PeriodicLattice.complexGaugeGroup (gaugeOrbitCurve f V t) := by
  have hu : ∀ x, expVertexFn ((t : ℂ) • f) x ∈ PeriodicLattice.complexGaugeGroup :=
    fun x => mem_complexGaugeGroup_of_compact (expVertexFn_mem_compact hI hf t x)
  refine ⟨fun b => ?_, fun b => ?_⟩
  · have h1 : (expVertexFn ((t : ℂ) • f) b.initial).det = 1 := hu _
    have h2 : ((expVertexFn ((t : ℂ) • f) b.terminal)⁻¹).det = 1 := inv_mem_unitDeterminant (hu _)
    have h3 : (V b).det = 1 := hV.1 b
    show (expVertexFn ((t : ℂ) • f) b.initial * V b *
      (expVertexFn ((t : ℂ) • f) b.terminal)⁻¹).det = 1
    rw [Matrix.det_mul, Matrix.det_mul, h1, h2, h3]
    simp
  · show expVertexFn ((t : ℂ) • f) b.opposite.initial * V b.opposite *
        (expVertexFn ((t : ℂ) • f) b.opposite.terminal)⁻¹ =
      (expVertexFn ((t : ℂ) • f) b.initial * V b *
        (expVertexFn ((t : ℂ) • f) b.terminal)⁻¹)⁻¹
    rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, inv_inv_of_mem_unitDeterminant (hu _), hV.2 b,
      mul_assoc]
    rfl
theorem gaugeOrbitCurve_differentiableAt (f : Vertex L k j → ComplexMatrix2)
    (V : Edge L k j → ComplexMatrix2) (b : Edge L k j) (t : ℝ) :
    DifferentiableAt ℝ (fun t => gaugeOrbitCurve f V t b) t := by
  have h := (hasDerivAt_restrict_real
    (hasDerivAt_twistedConj (f b.initial) (f b.terminal) (V b) (t : ℂ))).differentiableAt
  have e : (fun t => gaugeOrbitCurve f V t b) =
      fun t : ℝ => twistedConj (f b.initial) (f b.terminal) (V b) (t : ℂ) :=
    funext fun t => gaugeOrbitCurve_apply f V t b
  rw [e]
  exact h
theorem gaugeOrbitCurve_isCurve (hI : ComplexMatrix2.UnitaryLogConjugationProperties)
    {f : Vertex L k j → ComplexMatrix2} (hf : ∀ x, f x ∈ ComplexMatrix2.hermitianTraceless)
    {V : Edge L k j → ComplexMatrix2} (hV : V ∈ fieldsValuedIn L k j PeriodicLattice.complexGaugeGroup) :
    IsDifferentiableFieldCurve PeriodicLattice.complexGaugeGroup univ (gaugeOrbitCurve f V) :=
  ⟨⟨isOpen_univ, ordConnected_univ, mem_univ _⟩,
    fun t _ => gaugeOrbitCurve_isFieldIn hI hf hV t,
    fun b _ t _ => (gaugeOrbitCurve_differentiableAt f V b t).differentiableWithinAt⟩
theorem gaugeOrbitCurve_tendsto (f : Vertex L k j → ComplexMatrix2) (V : Edge L k j → ComplexMatrix2)
    (b : Edge L k j) : Tendsto (fun t => gaugeOrbitCurve f V t b) (𝓝 0) (𝓝 (V b)) := by
  have h := (gaugeOrbitCurve_differentiableAt f V b 0).continuousAt.tendsto
  rwa [gaugeOrbitCurve_zero] at h
theorem inv_eq_adjugate_of_mem {X : ComplexMatrix2} (h : X ∈ ComplexMatrix2.unitDeterminant) :
    X⁻¹ = X.adjugate := by apply _root_.YangMills.Construction.Tower.LevelwiseMeans.MeanData.inv_eq_adjugate_of_mem <;> assumption
theorem expTwist_zero_smul {V : Edge L k j → ComplexMatrix2}
    (hV : V ∈ fieldsValuedIn L k j PeriodicLattice.complexGaugeGroup) (B : Edge L k j → ComplexMatrix2) :
    expTwist ((0 : ℂ) • B) V = V := by
  funext b
  unfold expTwist
  split_ifs with hb
  · simp [ComplexMatrix2.matExp, NormedSpace.exp_zero]
  · have h : ((V b.opposite)⁻¹) = V b := by
      rw [hV.2 b]
      exact inv_inv_of_mem_unitDeterminant (hV.1 b)
    simpa [ComplexMatrix2.matExp, NormedSpace.exp_zero] using h
theorem leftExp_values (hA : LeftChartFields.Claim)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hj : j ≤ k) {V B : Edge L k j → ComplexMatrix2}
    (hV : V ∈ fieldsValuedIn L k j PeriodicLattice.complexGaugeGroup)
    (hB : B ∈ complexEdgeForms (meshAt L k j)) (b : Edge L k j) (hb : b.IsPositivelyOriented) :
    (∀ t : ℂ, ComplexMatrix2.matExp (Complex.I • (t • B) b) * V b ∈
        PeriodicLattice.complexGaugeGroup) ∧
      Continuous (fun t : ℂ => ComplexMatrix2.matExp (Complex.I • (t • B) b) * V b) := by
  have hv := (((hA.2.2 L k j hL hj).2.1).1).2 V hV B hB ⟨b, hb⟩
  refine ⟨hv.1, ?_⟩
  have e : (fun t : ℂ => ComplexMatrix2.matExp (Complex.I • (t • B) b) * V b) =
      fun t : ℂ => ComplexMatrix2.matExp (t • (Complex.I • B b)) * V b := by
    funext t
    rw [Pi.smul_apply, smul_comm]
  rw [e]
  exact continuous_iff_continuousAt.2 fun t =>
    ((hasDerivAt_matExp_smul (Complex.I • B b) t).mul_const (V b)).continuousAt
theorem expTwist_isFieldIn (hA : LeftChartFields.Claim)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hj : j ≤ k) {V B : Edge L k j → ComplexMatrix2}
    (hV : V ∈ fieldsValuedIn L k j PeriodicLattice.complexGaugeGroup)
    (hB : B ∈ complexEdgeForms (meshAt L k j)) (t : ℂ) :
    IsFieldIn PeriodicLattice.complexGaugeGroup (expTwist (t • B) V) := by
  classical
  have hmem : ∀ b, expTwist (t • B) V b ∈ PeriodicLattice.complexGaugeGroup := by
    intro b
    by_cases hb : b.IsPositivelyOriented
    · simp only [expTwist, if_pos hb]
      exact (leftExp_values hA hL hj hV hB b hb).1 t
    · simp only [expTwist, if_neg hb]
      exact inv_mem_unitDeterminant
        ((leftExp_values hA hL hj hV hB _ (opposite_isPositivelyOriented_of_not hL hb)).1 t)
  refine ⟨hmem, fun b => ?_⟩
  by_cases hb : b.IsPositivelyOriented
  · have hn := not_opposite_isPositivelyOriented hL hb
    simp only [expTwist, if_neg hn, if_pos hb, InfiniteLattice.Link.opposite_opposite]
  · have hr := opposite_isPositivelyOriented_of_not hL hb
    simp only [expTwist, if_pos hr, if_neg hb]
    exact (inv_inv_of_mem_unitDeterminant ((leftExp_values hA hL hj hV hB _ hr).1 t)).symm
theorem expTwist_tendsto (hA : LeftChartFields.Claim)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hj : j ≤ k) {V B : Edge L k j → ComplexMatrix2}
    (hV : V ∈ fieldsValuedIn L k j PeriodicLattice.complexGaugeGroup)
    (hB : B ∈ complexEdgeForms (meshAt L k j)) (b : Edge L k j) :
    Tendsto (fun t : ℂ => expTwist (t • B) V b) (𝓝 0) (𝓝 (V b)) := by
  classical
  have hzero : ∀ b : Edge L k j,
      ComplexMatrix2.matExp (Complex.I • ((0 : ℂ) • B) b) * V b = V b := by
    intro b
    simp [ComplexMatrix2.matExp, NormedSpace.exp_zero]
  by_cases hb : b.IsPositivelyOriented
  · have h := (leftExp_values hA hL hj hV hB b hb).2.continuousAt (x := 0) |>.tendsto
    rw [hzero] at h
    refine h.congr fun t => ?_
    simp only [expTwist, if_pos hb]
  · have hr := opposite_isPositivelyOriented_of_not hL hb
    have h := (leftExp_values hA hL hj hV hB _ hr).2.continuousAt (x := 0) |>.tendsto
    rw [hzero] at h
    have h2 : Tendsto (fun t : ℂ =>
        (ComplexMatrix2.matExp (Complex.I • (t • B) b.opposite) * V b.opposite).adjugate) (𝓝 0)
        (𝓝 (V b.opposite).adjugate) :=
      (Continuous.matrix_adjugate continuous_id).continuousAt.tendsto.comp h
    have e : (V b.opposite).adjugate = V b := by
      rw [← inv_eq_adjugate_of_mem (hV.1 _), hV.2 b]
      exact inv_inv_of_mem_unitDeterminant (hV.1 b)
    rw [e] at h2
    refine h2.congr fun t => ?_
    simp only [expTwist, if_neg hb]
    exact (inv_eq_adjugate_of_mem ((leftExp_values hA hL hj hV hB _ hr).1 t)).symm
theorem hasDerivAt_expTwist {V B : Edge L k j → ComplexMatrix2} (b : Edge L k j)
    (hb : b.IsPositivelyOriented) (t : ℝ) :
    HasDerivAt (fun t : ℝ => expTwist ((t : ℂ) • B) V b)
      (ComplexMatrix2.matExp ((t : ℂ) • (Complex.I • B b)) * (Complex.I • B b) * V b) t := by
  have h := hasDerivAt_restrict_real
    ((hasDerivAt_matExp_smul (Complex.I • B b) (t : ℂ)).mul_const (V b))
  refine h.congr_of_eventuallyEq (Eventually.of_forall fun s => ?_)
  show expTwist ((s : ℂ) • B) V b = _
  simp only [expTwist, if_pos hb]
  rw [Pi.smul_apply, smul_comm]
theorem expTwist_isCurve (hA : LeftChartFields.Claim)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hj : j ≤ k) {V B : Edge L k j → ComplexMatrix2}
    (hV : V ∈ fieldsValuedIn L k j PeriodicLattice.complexGaugeGroup)
    (hB : B ∈ complexEdgeForms (meshAt L k j)) :
    IsDifferentiableFieldCurve PeriodicLattice.complexGaugeGroup univ
      (fun t : ℝ => expTwist ((t : ℂ) • B) V) :=
  ⟨⟨isOpen_univ, ordConnected_univ, mem_univ _⟩,
    fun t _ => expTwist_isFieldIn hA hL hj hV hB (t : ℂ),
    fun b hb t _ => (hasDerivAt_expTwist b hb t).differentiableAt.differentiableWithinAt⟩
theorem curveTangent_expTwist (hL : Conventions.IsAdmissibleBlockingFactor L)
    {V B : Edge L k j → ComplexMatrix2}
    (hV : V ∈ fieldsValuedIn L k j PeriodicLattice.complexGaugeGroup)
    (hB : B ∈ complexEdgeForms (meshAt L k j)) :
    curveTangent (fun t : ℝ => expTwist ((t : ℂ) • B) V) = B := by
  classical
  have hpos : ∀ b : Edge L k j, b.IsPositivelyOriented →
      Complex.I⁻¹ • (deriv (fun t : ℝ => expTwist ((t : ℂ) • B) V b) 0 *
        (expTwist (((0 : ℝ) : ℂ) • B) V b)⁻¹) = B b := by
    intro b hb
    have hd := (hasDerivAt_expTwist (V := V) (B := B) b hb 0).deriv
    rw [hd, Complex.ofReal_zero, expTwist_zero_smul hV]
    have hinv : V b * (V b)⁻¹ = 1 := by
      refine Matrix.mul_nonsing_inv _ ?_
      have e : (V b).det = 1 := hV.1 b
      rw [e]
      exact isUnit_one
    simp only [zero_smul, ComplexMatrix2.matExp, NormedSpace.exp_zero, one_mul]
    rw [mul_assoc, hinv, mul_one, smul_smul, inv_mul_cancel₀ Complex.I_ne_zero, one_smul]
  funext b
  unfold curveTangent extendOddly
  by_cases hb : b.IsPositivelyOriented
  · rw [if_pos hb]
    exact hpos b hb
  · rw [if_neg hb]
    show -(Complex.I⁻¹ • (deriv (fun t : ℝ => expTwist ((t : ℂ) • B) V b.opposite) 0 *
      (expTwist (((0 : ℝ) : ℂ) • B) V b.opposite)⁻¹)) = B b
    rw [hpos _ (opposite_isPositivelyOriented_of_not hL hb), hB.2 b, neg_neg]
end FieldCurves
section PolydiscOfCube
variable {L k j : ℕ}
theorem isOpen_operatorNorm_sub_one_lt {r : ℝ} :
    IsOpen {X : ComplexMatrix2 | ComplexMatrix2.operatorNorm (X - 1) < r} :=
  isOpen_lt (continuous_norm.comp (continuous_id.sub continuous_const)) continuous_const
theorem eventually_mem_nearIdentityPolydisc {T : Type} {l : Filter T}
    {f : T → Edge L k j → ComplexMatrix2} {V : Edge L k j → ComplexMatrix2} {ρ : ℝ}
    {c : Edge L k (j + 1)} (hfin : (doubleCubeLinks L (meshAt L k j) c).Finite)
    (hc : ∀ t, IsFieldIn PeriodicLattice.complexGaugeGroup (f t))
    (ht : ∀ b, Tendsto (fun t => f t b) l (𝓝 (V b)))
    (hV : V ∈ nearIdentityPolydisc L k j ρ c) : ∀ᶠ t in l, f t ∈ nearIdentityPolydisc L k j ρ c := by
  have hn : ∀ᶠ t in l, ∀ b ∈ doubleCubeLinks L (meshAt L k j) c,
      ComplexMatrix2.operatorNorm (f t b - 1) < ρ := by
    refine (eventually_all_finite hfin).2 fun b hb => ?_
    exact (ht b).eventually (isOpen_operatorNorm_sub_one_lt.mem_nhds (hV.2 b hb))
  filter_upwards [hn] with t h
  exact ⟨⟨fun b _ => (hc t).1 b, fun b _ => (hc t).2 b⟩, h⟩
theorem eq_fieldOfValues_of_mem (hL : Conventions.IsAdmissibleBlockingFactor L)
    {c : Edge L k (j + 1)}
    (hrev : ∀ b ∈ doubleCubeLinks L (meshAt L k j) c,
      b.opposite ∈ doubleCubeLinks L (meshAt L k j) c)
    {ρ : ℝ} {V : Edge L k j → ComplexMatrix2} (hV : V ∈ nearIdentityPolydisc L k j ρ c)
    (b : Edge L k j) (hb : b ∈ doubleCubeLinks L (meshAt L k j) c) :
    V b = DoubleBlockPolydisc.Infinite.fieldOfValues L k j c (fun b => V b.1) b := by
  classical
  unfold DoubleBlockPolydisc.Infinite.fieldOfValues extendFromPositive
  by_cases hp : b.IsPositivelyOriented
  · rw [dif_pos (⟨hb, hp⟩ : b ∈ DoubleBlockPolydisc.Infinite.doubleBlockBonds L k j c ∧
      b.IsPositivelyOriented)]
  · have hrp : b.opposite.IsPositivelyOriented := opposite_isPositivelyOriented_of_not hL hp
    rw [dif_neg (fun h : b ∈ DoubleBlockPolydisc.Infinite.doubleBlockBonds L k j c ∧
        b.IsPositivelyOriented => hp h.2),
      dif_pos (⟨hrev b hb, hrp⟩ : b.opposite ∈ DoubleBlockPolydisc.Infinite.doubleBlockBonds L k j c ∧
        b.opposite.IsPositivelyOriented)]
    have e : (V b.opposite)⁻¹ = ((V b)⁻¹)⁻¹ := congrArg (·⁻¹) (hV.1.2 b hb)
    exact (e.trans (inv_inv_of_mem_unitDeterminant (hV.1.1 b hb))).symm
theorem mem_nearIdentityPolydisc_of_eqOn {c : Edge L k (j + 1)}
    (hrev : ∀ b ∈ doubleCubeLinks L (meshAt L k j) c,
      b.opposite ∈ doubleCubeLinks L (meshAt L k j) c)
    {ρ : ℝ} {V V' : Edge L k j → ComplexMatrix2} (hV : V ∈ nearIdentityPolydisc L k j ρ c)
    (he : ∀ b ∈ doubleCubeLinks L (meshAt L k j) c, V b = V' b) :
    V' ∈ nearIdentityPolydisc L k j ρ c := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.mem_nearIdentityPolydisc_congr <;> assumption
theorem complexContourMean_congr (hS : _root_.YangMills.Construction.Tower.SmoothingNearIdentity)
    (hQ : SublatticesSymmetriesScalingsAndProjections.Statement)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hj : j < k)
    {c : Edge L k (j + 1)} (hc : c.IsPositivelyOriented) {x : Vertex L k j}
    (hx : x ∈ cubeVertices L (meshAt L k j) c.initial)
    {V V' : Edge L k j → ComplexMatrix2}
    (hV : V ∈ nearIdentityPolydisc L k j (polydiscRadius L) c)
    (hV' : V' ∈ nearIdentityPolydisc L k j (polydiscRadius L) c)
    (he : ∀ b ∈ doubleCubeLinks L (meshAt L k j) c, V b = V' b) :
    complexContourMean L V c.initial x = complexContourMean L V' c.initial x := by
  have hL0 : 0 < L := by
    have := hL.2
    omega
  have hadm := (hS.1 L hL).2.2.fullSpace k j hj c hc
  have hQ' := ((hQ L hL0 hL k).2.2.2.2.2.2 (by omega) 1 one_pos).2 j hj c hc
  have e1 := hQ'.complexContourMean_eq V (hadm.subset_complexDomain hV) c.initial (Or.inl rfl) x hx
  have e2 := hQ'.complexContourMean_eq V' (hadm.subset_complexDomain hV') c.initial (Or.inl rfl) x hx
  refine e1.trans (Eq.trans ?_ e2.symm)
  congr 1
  funext z
  unfold projField
  split_ifs with h
  · exact he _ h.choose_spec.1
  · rfl
theorem complexSmoothing_congr (hS : _root_.YangMills.Construction.Tower.SmoothingNearIdentity)
    (hQ : SublatticesSymmetriesScalingsAndProjections.Statement)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hj : j < k) {c : Edge L k (j + 1)}
    (hc : c.IsPositivelyOriented) {V V' : Edge L k j → ComplexMatrix2}
    (hV : V ∈ nearIdentityPolydisc L k j (polydiscRadius L) c)
    (hV' : V' ∈ nearIdentityPolydisc L k j (polydiscRadius L) c)
    (he : ∀ b ∈ doubleCubeLinks L (meshAt L k j) c, V b = V' b) :
    complexSmoothing L V c = complexSmoothing L V' c := by
  have hL0 : 0 < L := by
    have := hL.2
    omega
  have hadm := (hS.1 L hL).2.2.fullSpace k j hj c hc
  have hQ' := ((hQ L hL0 hL k).2.2.2.2.2.2 (by omega) 1 one_pos).2 j hj c hc
  have e1 := hQ'.complexSmoothing_eq V (hadm.subset_complexDomain hV)
  have e2 := hQ'.complexSmoothing_eq V' (hadm.subset_complexDomain hV')
  refine e1.trans (Eq.trans ?_ e2.symm)
  congr 1
  funext x
  unfold projField
  split_ifs with h
  · exact he _ h.choose_spec.1
  · rfl
def contourOnFinset (c : Edge L k (j + 1)) (F : Finset (Edge L k j))
    (hF : (F : Set (Edge L k j)) = DoubleBlockPolydisc.Infinite.positiveDoubleBlockBonds L k j c)
    (x : Vertex L k j) (w : F → ComplexMatrix2) : ComplexMatrix2 :=
  complexContourMean L
    (DoubleBlockPolydisc.Infinite.fieldOfValues L k j c (pointOfFinset c F hF w)) c.initial x
theorem smoothingOnFinset_restrictToEdges (hS : _root_.YangMills.Construction.Tower.SmoothingNearIdentity)
    (hQ : SublatticesSymmetriesScalingsAndProjections.Statement)
    (hP : DoubleBlockPolydisc.PolydiscsHold)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hj : j < k) {c : Edge L k (j + 1)}
    (hc : c.IsPositivelyOriented) (F : Finset (Edge L k j))
    (hF : (F : Set (Edge L k j)) = DoubleBlockPolydisc.Infinite.positiveDoubleBlockBonds L k j c)
    {V : Edge L k j → ComplexMatrix2}
    (hV : V ∈ nearIdentityPolydisc L k j (polydiscRadius L) c) :
    smoothingOnFinset c F hF (restrictToEdges F V) = complexSmoothing L V c := by
  have hrev := ((hP L hL k j hj).2 c hc).finite_open.opposite_mem
  have hag := eq_fieldOfValues_of_mem hL hrev hV
  exact (complexSmoothing_congr hS hQ hL hj hc hV
    (mem_nearIdentityPolydisc_of_eqOn hrev hV hag) hag).symm
theorem contourOnFinset_restrictToEdges (hS : _root_.YangMills.Construction.Tower.SmoothingNearIdentity)
    (hQ : SublatticesSymmetriesScalingsAndProjections.Statement)
    (hP : DoubleBlockPolydisc.PolydiscsHold)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hj : j < k) {c : Edge L k (j + 1)}
    (hc : c.IsPositivelyOriented) (F : Finset (Edge L k j))
    (hF : (F : Set (Edge L k j)) = DoubleBlockPolydisc.Infinite.positiveDoubleBlockBonds L k j c)
    {x : Vertex L k j} (hx : x ∈ cubeVertices L (meshAt L k j) c.initial)
    {V : Edge L k j → ComplexMatrix2}
    (hV : V ∈ nearIdentityPolydisc L k j (polydiscRadius L) c) :
    contourOnFinset c F hF x (restrictToEdges F V) = complexContourMean L V c.initial x := by
  have hrev := ((hP L hL k j hj).2 c hc).finite_open.opposite_mem
  have hag := eq_fieldOfValues_of_mem hL hrev hV
  exact (complexContourMean_congr hS hQ hL hj hc hx hV
    (mem_nearIdentityPolydisc_of_eqOn hrev hV hag) hag).symm
theorem isRelativelyOpen_leftComponents_preimage {σ : Type} {U : Set (σ → ComplexMatrix2)}
    (h : ComplexMatrix2.IsRelativelyOpen (unimodularPi σ) U) :
    ComplexMatrix2.IsRelativelyOpen (GroupLieProduct σ Empty) (leftComponents ⁻¹' U) := by apply _root_.YangMills.Construction.Tower.LevelwiseMeans.isRelativelyOpen_preimage_leftComponents <;> assumption
theorem isRelativelyOpen_polydiscOnFinset {c : Edge L k (j + 1)} (F : Finset (Edge L k j))
    (hF : (F : Set (Edge L k j)) = DoubleBlockPolydisc.Infinite.positiveDoubleBlockBonds L k j c)
    (ho : ComplexMatrix2.IsRelativelyOpen
      (unimodularPi (DoubleBlockPolydisc.Infinite.positiveDoubleBlockBonds L k j c))
      (DoubleBlockPolydisc.Infinite.polydiscPositive L k j (polydiscRadius L) c)) :
    ComplexMatrix2.IsRelativelyOpen (unimodularPi F) (polydiscOnFinset c F hF) := by apply _root_.YangMills.Construction.Tower.MeanStableFields.Infinite.isRelativelyOpen_polydiscOnFinset <;> assumption
theorem isHolomorphicToCoords_polydiscOnFinset (H : ExpChartHolomorphy.ExpChartTheory)
    {E : Type} {m : ℕ} (e : E ≃ ComplexCoordinates m)
    (β : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless) {c : Edge L k (j + 1)}
    (F : Finset (Edge L k j))
    (hF : (F : Set (Edge L k j)) = DoubleBlockPolydisc.Infinite.positiveDoubleBlockBonds L k j c)
    (ho : ComplexMatrix2.IsRelativelyOpen
      (unimodularPi (DoubleBlockPolydisc.Infinite.positiveDoubleBlockBonds L k j c))
      (DoubleBlockPolydisc.Infinite.polydiscPositive L k j (polydiscRadius L) c))
    [Fintype (DoubleBlockPolydisc.Infinite.positiveDoubleBlockBonds L k j c)]
    {Φ : (DoubleBlockPolydisc.Infinite.positiveDoubleBlockBonds L k j c → ComplexMatrix2) → E}
    (hh : IsHolomorphicToCoords β e (leftComponents ⁻¹'
        DoubleBlockPolydisc.Infinite.polydiscPositive L k j (polydiscRadius L) c)
      fun P => Φ (leftComponents P)) :
    IsHolomorphicToCoords β e (asGroupFactors '' polydiscOnFinset c F hF)
      fun P => Φ (pointOfFinset c F hF fun b => P (.inl b)) := by
  have hW : ComplexMatrix2.IsRelativelyOpen (GroupLieProduct F Empty)
      (asGroupFactors '' polydiscOnFinset c F hF) := by
    rw [asGroupFactors_image]
    exact isRelativelyOpen_leftComponents_preimage (isRelativelyOpen_polydiscOnFinset F hF ho)
  have hmemF : ∀ s : DoubleBlockPolydisc.Infinite.positiveDoubleBlockBonds L k j c, s.1 ∈ F :=
    fun s => by
      have : s.1 ∈ (F : Set (Edge L k j)) := by
        rw [hF]
        exact s.2
      exact this
  let Ψ : (F ⊕ Empty → ComplexMatrix2) →
      DoubleBlockPolydisc.Infinite.positiveDoubleBlockBonds L k j c ⊕ Empty → ComplexMatrix2 :=
    fun P => asGroupFactors (pointOfFinset c F hF (leftComponents P))
  have hΨ : IsHolomorphicToProduct β (asGroupFactors '' polydiscOnFinset c F hF) Ψ :=
    ⟨hW, fun s => component_isHolomorphicToUnimodular H β hW ⟨s.1, hmemF s⟩, fun e => e.elim⟩
  obtain ⟨_, _, hcomp⟩ := H.2.2.2.2.1 F Empty _ Empty β _ Ψ hΨ.1 hΨ E m e _ _ hh
  have e' : asGroupFactors '' polydiscOnFinset c F hF ∩
      Ψ ⁻¹' (leftComponents ⁻¹'
        DoubleBlockPolydisc.Infinite.polydiscPositive L k j (polydiscRadius L) c) =
      asGroupFactors '' polydiscOnFinset c F hF := by
    refine inter_eq_left.2 ?_
    rintro _ ⟨w, hw, rfl⟩
    exact hw
  rw [e'] at hcomp
  exact hcomp
end PolydiscOfCube
section RealStep
variable {L k j : ℕ}
theorem smoothingMap_isHolomorphic (hW : MeanStableFields.MeanStableFieldsHold)
    (hO : IteratedMeans.IteratedMeansHold)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hj : j < k)
    (β : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless) :
    IsHolomorphicFieldMap β (smallComplexFields L k j) (smoothingMap L k j) := by
  have hW' := (hW L hL k (by omega)).2
  have hO' := (hO L hL k (by omega)).2
  exact ⟨hW'.isFinitelyOpen_nearOne j hj, fun V hV => hO'.meanStep_mem j hj V hV,
    fun c hc => hW'.holomorphic_smoothing j hj c hc β⟩
theorem mul_inv_of_mem_complexGaugeGroup {M : ComplexMatrix2}
    (h : M ∈ PeriodicLattice.complexGaugeGroup) : M * M⁻¹ = 1 := by apply _root_.YangMills.SharedProofs.p13806 <;> assumption
theorem inv_I_smul_mul_inv {A B M : ComplexMatrix2} (h : M ∈ PeriodicLattice.complexGaugeGroup) :
    Complex.I⁻¹ • ((Complex.I • (A * M - M * B)) * M⁻¹) = A - ComplexMatrix2.conjugateBy M B := by
  rw [smul_mul_assoc, smul_smul, inv_mul_cancel₀ Complex.I_ne_zero, one_smul, sub_mul, mul_assoc A,
    mul_inv_of_mem_complexGaugeGroup h, mul_one]
  rfl
theorem complexSmoothingDeriv_neg_covDiff (H : ExpChartHolomorphy.ExpChartTheory)
    (hS : _root_.YangMills.Construction.Tower.SmoothingNearIdentity)
    (hQ : SublatticesSymmetriesScalingsAndProjections.Statement)
    (hP : DoubleBlockPolydisc.PolydiscsHold) (hC : LeftChartFacts.HoldEverywhere)
    (hW : MeanStableFields.MeanStableFieldsHold)
    (hO : IteratedMeans.IteratedMeansHold)
    (hI : ComplexMatrix2.UnitaryLogConjugationProperties)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hj : j < k) {V : Edge L k j → ComplexMatrix2}
    (hV : V ∈ smallComplexFields L k j) {f : Vertex L k j → ComplexMatrix2}
    (hf : ∀ x, f x ∈ ComplexMatrix2.hermitianTraceless) (hf' : ∀ x, f x ∈ ComplexMatrix2.traceless)
    {c : Edge L k (j + 1)} (hc : c.IsPositivelyOriented) :
    complexSmoothingDeriv V (-covDiff V f) c =
      f (toFiner (meshAt L k j) c.initial) -
        ComplexMatrix2.conjugateBy (complexSmoothing L V c) (f (toFiner (meshAt L k j) c.terminal)) := by
  classical
  have hW' := (hW L hL k (by omega)).2
  have hO' := (hO L hL k (by omega)).2
  have hfacts := hC L k j (j + 1) j hL hj.le hj hj.le
  have hpoly := ((hP L hL k j hj).2 c hc).finite_open
  have hadm := (hS.1 L hL).2.2.fullSpace k j hj c hc
  have hVp := hW'.mem_polydisc j hj c hc V hV
  obtain ⟨F, hF, hpr⟩ := hW'.polydisc_presentation j hj c hc
  obtain ⟨inst, hh⟩ := ((hP L hL k j hj).2 c hc).holomorphic_smoothing
  have hK : holomorphicPresentations L k j OneLoop.pauliBasis
      Coordinates.ComplexCoordinates.matrixEquiv F (polydiscOnFinset c F hF)
      (smoothingOnFinset c F hF) :=
    isHolomorphicToCoords_polydiscOnFinset H Coordinates.ComplexCoordinates.matrixEquiv
      OneLoop.pauliBasis F hF hpoly.isRelativelyOpen (Φ := fun v => complexSmoothing L
        (DoubleBlockPolydisc.Infinite.fieldOfValues L k j c v) c)
      (hh.toMatrices _)
  have hm := hfacts.2.2.1.2.2.1 OneLoop.pauliBasis _ _
    (smoothingMap_isHolomorphic hW hO hL hj OneLoop.pauliBasis) V hV
  have hd := (hm univ (gaugeOrbitCurve f V) (gaugeOrbitCurve_isCurve hI hf hV.1)
    (gaugeOrbitCurve_zero f V) c hc).2 F _ _ (hpr V hV) hK
  have htan : curveTangent (gaugeOrbitCurve f V) = -covDiff V f :=
    (hfacts.2.2.2.2.2.1.1 V hV.1 f hf').2.2.1
  rw [htan] at hd
  have hMg : complexSmoothing L V c ∈ PeriodicLattice.complexGaugeGroup :=
    (hO'.meanStep_mem j hj V hV).1 c
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ), gaugeOrbitCurve f V t ∈
      nearIdentityPolydisc L k j (polydiscRadius L) c :=
    eventually_mem_nearIdentityPolydisc hpoly.finite (gaugeOrbitCurve_isFieldIn hI hf hV.1)
      (gaugeOrbitCurve_tendsto f V) hVp
  have hconj : HasDerivAt (fun t : ℝ => twistedConj (f (toFiner (meshAt L k j) c.initial))
        (f (toFiner (meshAt L k j) c.terminal)) (complexSmoothing L V c) (t : ℂ) *
        (complexSmoothing L V c)⁻¹)
      ((Complex.I • (f (toFiner (meshAt L k j) c.initial) * complexSmoothing L V c -
        complexSmoothing L V c * f (toFiner (meshAt L k j) c.terminal))) *
        (complexSmoothing L V c)⁻¹) 0 :=
    (hasDerivAt_restrict_real (t₀ := 0) (by simpa using hasDerivAt_twistedConj_zero _ _ _)).mul_const _
  have heq : (fun t => smoothingOnFinset c F hF (restrictToEdges F (gaugeOrbitCurve f V t)) *
      (smoothingMap L k j V c)⁻¹) =ᶠ[𝓝 0] fun t : ℝ =>
        twistedConj (f (toFiner (meshAt L k j) c.initial))
          (f (toFiner (meshAt L k j) c.terminal)) (complexSmoothing L V c) (t : ℂ) *
        (complexSmoothing L V c)⁻¹ := by
    filter_upwards [hev] with t ht
    rw [smoothingOnFinset_restrictToEdges hS hQ hP hL hj hc F hF ht]
    have hcov := (hadm.gauge_covariant V hVp _ (fun x => expVertexFn_mem_compact hI hf t x)).2.1
    have e : complexSmoothing L (gaugeOrbitCurve f V t) c =
        twistedConj (f (toFiner (meshAt L k j) c.initial))
          (f (toFiner (meshAt L k j) c.terminal)) (complexSmoothing L V c) (t : ℂ) :=
      hcov.trans (matExp_mul_mul_inv_eq_twistedConj _ _ _ _)
    rw [e]
    rfl
  have hu := (hconj.congr_of_eventuallyEq heq).unique hd
  have e2 := congrArg (fun X : ComplexMatrix2 => Complex.I⁻¹ • X) hu
  simp only [smul_smul, inv_mul_cancel₀ Complex.I_ne_zero, one_smul] at e2
  exact e2.symm.trans (inv_I_smul_mul_inv hMg)
theorem exists_hasDerivAt_contourOnFinset (H : ExpChartHolomorphy.ExpChartTheory)
    (hS : _root_.YangMills.Construction.Tower.SmoothingNearIdentity)
    (hQ : SublatticesSymmetriesScalingsAndProjections.Statement)
    (hP : DoubleBlockPolydisc.PolydiscsHold) (hC : LeftChartFacts.HoldEverywhere)
    (hW : MeanStableFields.MeanStableFieldsHold)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hj : j < k) {V : Edge L k j → ComplexMatrix2}
    (hV : V ∈ smallComplexFields L k j) {c : Edge L k (j + 1)}
    (hc : c.IsPositivelyOriented) {x : Vertex L k j}
    (hx : x ∈ cubeVertices L (meshAt L k j) c.initial) (F : Finset (Edge L k j))
    (hF : (F : Set (Edge L k j)) = DoubleBlockPolydisc.Infinite.positiveDoubleBlockBonds L k j c)
    (hpr : ∀ U ∈ MeanStableFields.Infinite.fieldsNearOne L k j,
      IsLocalPresentation PeriodicLattice.complexGaugeGroup
        (MeanStableFields.Infinite.fieldsNearOne L k j)
        (fun V => complexSmoothing L V c) U F (polydiscOnFinset c F hF)
        (smoothingOnFinset c F hF)) :
    ∃ D : (Edge L k j → ComplexMatrix2) → ComplexMatrix2, ∀ (I : Set ℝ)
      (γ : ℝ → Edge L k j → ComplexMatrix2),
      IsDifferentiableFieldCurve PeriodicLattice.complexGaugeGroup I γ → γ 0 = V →
        HasDerivAt (fun t => contourOnFinset c F hF x (restrictToEdges F (γ t)))
          (D (curveTangent γ)) 0 := by
  classical
  have hW' := (hW L hL k (by omega)).2
  have hfacts := hC L k j (j + 1) j hL hj.le hj hj.le
  have hpoly := (hP L hL k j hj).2 c hc
  obtain ⟨inst, hh⟩ := hpoly.holomorphic_contourMean c.initial (Or.inl rfl) x hx
  have hK : ∀ r s : Fin 2, holomorphicPresentations L k j OneLoop.pauliBasis scalarCoords F
      (polydiscOnFinset c F hF) (fun w => contourOnFinset c F hF x w r s) := fun r s =>
    isHolomorphicToCoords_polydiscOnFinset H scalarCoords OneLoop.pauliBasis F hF
      hpoly.finite_open.isRelativelyOpen (Φ := fun v => complexContourMean L
        (DoubleBlockPolydisc.Infinite.fieldOfValues L k j c v) c.initial x r s)
      (hh.entries _ r s)
  have hpres : ∀ r s : Fin 2, ∀ U ∈ smallComplexFields L k j,
      IsLocalPresentation PeriodicLattice.complexGaugeGroup (smallComplexFields L k j)
        (fun V' => complexContourMean L V' c.initial x r s) U F (polydiscOnFinset c F hF)
        (fun w => contourOnFinset c F hF x w r s) := fun r s U hU =>
    ⟨(hpr U hU).1, (hpr U hU).2.1, (hpr U hU).2.2.1, fun U' hU' _ => by
      show complexContourMean L U' c.initial x r s =
        contourOnFinset c F hF x (restrictToEdges F U') r s
      rw [contourOnFinset_restrictToEdges hS hQ hP hL hj hc F hF hx
        (hW'.mem_polydisc j hj c hc U' hU')]⟩
  have hfun : ∀ r s : Fin 2, IsHolomorphicFn OneLoop.pauliBasis scalarCoords
      (smallComplexFields L k j)
      (fun V' => complexContourMean L V' c.initial x r s) := fun r s =>
    ⟨hW'.isFinitelyOpen_nearOne j hj, fun U hU => hU.1, fun U hU =>
      ⟨F, _, _, hpres r s U hU, hK r s⟩⟩
  refine ⟨fun T => Matrix.of fun r s => holLeftDeriv OneLoop.pauliBasis
    scalarCoords (smallComplexFields L k j)
    (fun V' => complexContourMean L V' c.initial x r s) V T,
    fun I γ hγ h0 => hasDerivAt_pi.2 fun r => hasDerivAt_pi.2 fun s => ?_⟩
  exact ((hfacts.2.2.1.2.2.2 OneLoop.pauliBasis _ _ (hfun r s) V hV) I γ hγ h0).2
    F _ _ (hpres r s V hV) (hK r s)
theorem logDirectionalDeriv_contourMean (H : ExpChartHolomorphy.ExpChartTheory)
    (hS : _root_.YangMills.Construction.Tower.SmoothingNearIdentity)
    (hG : ComplexMeanLiesInComplexGaugeGroup)
    (hA : LeftChartFields.Claim)
    (hQ : SublatticesSymmetriesScalingsAndProjections.Statement)
    (hP : DoubleBlockPolydisc.PolydiscsHold) (hC : LeftChartFacts.HoldEverywhere)
    (hW : MeanStableFields.MeanStableFieldsHold)
    (hI : ComplexMatrix2.UnitaryLogConjugationProperties)
    (hN : CovariantStepComplexLinear)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hj : j < k) {V : Edge L k j → ComplexMatrix2}
    (hV : V ∈ smallComplexFields L k j) {f : Vertex L k j → ComplexMatrix2}
    (hf : ∀ x, f x ∈ ComplexMatrix2.hermitianTraceless) (hf' : ∀ x, f x ∈ ComplexMatrix2.traceless)
    (y : Vertex L k (j + 1)) {x : Vertex L k j} (hx : x ∈ cubeVertices L (meshAt L k j) y) :
    logDirectionalDeriv ℂ (fun X => complexContourMean L (expTwist X V) y x)
        (complexContourMean L V y x) (-covDiff V f) =
      f (toFiner (meshAt L k j) y) -
        ComplexMatrix2.conjugateBy (complexContourMean L V y x) (f x) := by
  classical
  obtain ⟨c, hc, hcy⟩ : ∃ c : Edge L k (j + 1), c.IsPositivelyOriented ∧ y = c.initial :=
    ⟨InfiniteLattice.Link.forwardFrom y 0,
      InfiniteLattice.mem_positiveLinks_iff.1 ⟨y, 0, rfl⟩, rfl⟩
  subst hcy
  have hk : 1 ≤ k := by omega
  have hW' := (hW L hL k hk).2
  have hfacts := hC L k j (j + 1) j hL hj.le hj hj.le
  have hpoly := (hP L hL k j hj).2 c hc
  have hfo := hpoly.finite_open
  have hadm := (hS.1 L hL).2.2.fullSpace k j hj c hc
  have hVp := hW'.mem_polydisc j hj c hc V hV
  obtain ⟨F, hF, hpr⟩ := hW'.polydisc_presentation j hj c hc
  have hT : -covDiff V f ∈ complexEdgeForms (meshAt L k j) :=
    neg_mem ((hN L hL k j hj V hV).2.2.1 f hf').1
  obtain ⟨D, hD⟩ := exists_hasDerivAt_contourOnFinset H hS hQ hP hC hW hL hj hV hc hx F hF hpr
  have hd1 := hD univ (gaugeOrbitCurve f V) (gaugeOrbitCurve_isCurve hI hf hV.1)
    (gaugeOrbitCurve_zero f V)
  have htan : curveTangent (gaugeOrbitCurve f V) = -covDiff V f :=
    (hfacts.2.2.2.2.2.1.1 V hV.1 f hf').2.2.1
  rw [htan] at hd1
  have hd2 := hD univ (fun t : ℝ => expTwist ((t : ℂ) • -covDiff V f) V)
    (expTwist_isCurve hA hL hj.le hV.1 hT)
    (by simpa using expTwist_zero_smul hV.1 (-covDiff V f))
  rw [curveTangent_expTwist hL hV.1 hT] at hd2
  have hgroup : ∀ V' : Edge L k j → ComplexMatrix2, V' ∈ complexDomainNearOne L c →
      complexContourMean L V' c.initial x ∈ PeriodicLattice.complexGaugeGroup := fun V' hV' =>
    ((hG.2 L k (j + 1) hL (Nat.succ_le_succ (Nat.zero_le j)) (Nat.succ_le_of_lt hj)).2 c V' hc
      hV').1 c.initial (Or.inl rfl) x hx
  have hCg := hgroup V (hadm.subset_complexDomain hVp)
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ), gaugeOrbitCurve f V t ∈
      nearIdentityPolydisc L k j (polydiscRadius L) c :=
    eventually_mem_nearIdentityPolydisc hfo.finite (gaugeOrbitCurve_isFieldIn hI hf hV.1)
      (gaugeOrbitCurve_tendsto f V) hVp
  have hconj : HasDerivAt (fun t : ℝ => twistedConj (f (toFiner (meshAt L k j) c.initial)) (f x)
        (complexContourMean L V c.initial x) (t : ℂ))
      (Complex.I • (f (toFiner (meshAt L k j) c.initial) * complexContourMean L V c.initial x -
        complexContourMean L V c.initial x * f x)) 0 :=
    hasDerivAt_restrict_real (t₀ := 0) (by simpa using hasDerivAt_twistedConj_zero _ _ _)
  have heq : (fun t => contourOnFinset c F hF x (restrictToEdges F (gaugeOrbitCurve f V t))) =ᶠ[𝓝 0]
      fun t : ℝ => twistedConj (f (toFiner (meshAt L k j) c.initial)) (f x)
        (complexContourMean L V c.initial x) (t : ℂ) := by
    filter_upwards [hev] with t ht
    rw [contourOnFinset_restrictToEdges hS hQ hP hL hj hc F hF hx ht]
    have hcov := (hadm.gauge_covariant V hVp _ (fun x => expVertexFn_mem_compact hI hf t x)).2.2
      c.initial (Or.inl rfl) x hx
    exact hcov.trans (matExp_mul_mul_inv_eq_twistedConj _ _ _ _)
  have hu := (hconj.congr_of_eventuallyEq heq).unique hd1
  let W : ℂ → ComplexMatrix2 := fun t => complexContourMean L
    (expTwist (t • -covDiff V f) V) c.initial x
  have hevC : ∀ᶠ t in 𝓝 (0 : ℂ), expTwist (t • -covDiff V f) V ∈
      nearIdentityPolydisc L k j (polydiscRadius L) c :=
    eventually_mem_nearIdentityPolydisc hfo.finite (expTwist_isFieldIn hA hL hj.le hV.1 hT)
      (expTwist_tendsto hA hL hj.le hV.1 hT) hVp
  have hWd : DifferentiableAt ℂ W 0 := by
    obtain ⟨inst, h⟩ := hpoly.holomorphic_contourMean c.initial (Or.inl rfl) x hx
    have hne : Nonempty (DoubleBlockPolydisc.Infinite.positiveDoubleBlockBonds L k j c) :=
      hfo.positive_nonempty.to_subtype
    have hd := differentiableAt_along_leftChart H (((hA.2.2 L k j hL hj.le).2.1).2.2.2)
      (Λ := fullData L k j) (σ := DoubleBlockPolydisc.Infinite.positiveDoubleBlockBonds L k j c)
      (fun s => (⟨s.1, s.2.2⟩ : PositiveEdge (meshAt L k j)))
      hfo.isRelativelyOpen
      (Φ := fun v => complexContourMean L
        (DoubleBlockPolydisc.Infinite.fieldOfValues L k j c v) c.initial x) h.entries hV.1
      ⟨_, ⟨_, hVp, rfl⟩, rfl⟩ hT
    refine hd.congr_of_eventuallyEq ?_
    filter_upwards [hevC] with t ht
    have hag := eq_fieldOfValues_of_mem hL hfo.opposite_mem ht
    show complexContourMean L (expTwist (t • -covDiff V f) V) c.initial x = _
    rw [complexContourMean_congr hS hQ hL hj hc hx ht
      (mem_nearIdentityPolydisc_of_eqOn hfo.opposite_mem ht hag) hag]
    congr 2
    funext s
    show expTwist (t • -covDiff V f) V s.1 = _
    simp only [expTwist, if_pos s.2.2]
    rfl
  have hWr : HasDerivAt (fun t : ℝ => W (t : ℂ)) (deriv W 0) 0 :=
    hasDerivAt_restrict_real (t₀ := 0) (by simpa using hWd.hasDerivAt)
  have hevR : ∀ᶠ t : ℝ in 𝓝 (0 : ℝ), expTwist ((t : ℂ) • -covDiff V f) V ∈
      nearIdentityPolydisc L k j (polydiscRadius L) c :=
    eventually_mem_nearIdentityPolydisc hfo.finite
      (fun t => expTwist_isFieldIn hA hL hj.le hV.1 hT (t : ℂ))
      (fun b => (expTwist_tendsto hA hL hj.le hV.1 hT b).comp
        (Complex.continuous_ofReal.tendsto' 0 0 (by simp))) hVp
  have heq2 : (fun t : ℝ => contourOnFinset c F hF x
      (restrictToEdges F (expTwist ((t : ℂ) • -covDiff V f) V))) =ᶠ[𝓝 0]
      fun t : ℝ => W (t : ℂ) := by
    filter_upwards [hevR] with t ht
    exact contourOnFinset_restrictToEdges hS hQ hP hL hj hc F hF hx ht
  have hu2 := (hWr.congr_of_eventuallyEq heq2).unique hd2
  obtain ⟨ρ₀, hρ₀, hball⟩ := Metric.eventually_nhds_iff_ball.1 hevC
  have hmaps : MapsTo W (Metric.ball 0 ρ₀) PeriodicLattice.complexGaugeGroup := fun t ht =>
    hgroup _ (hadm.subset_complexDomain (hball t ht))
  have hlog := (hA.2.1 ρ₀ hρ₀ W hmaps hWd).2.2.1
  have hW0 : W 0 = complexContourMean L V c.initial x := by
    show complexContourMean L (expTwist ((0 : ℂ) • -covDiff V f) V) c.initial x = _
    rw [expTwist_zero_smul hV.1]
  have e2 : (fun t : ℂ => ComplexMatrix2.logSeries (complexContourMean L
      (expTwist (algebraMap ℂ ℂ t • -covDiff V f) V) c.initial x *
        (complexContourMean L V c.initial x)⁻¹)) =
      fun t : ℂ => ComplexMatrix2.logSeries (W t * (W 0)⁻¹) := by
    funext t
    simp only [Algebra.algebraMap_self, RingHom.id_apply]
    rw [hW0]
  unfold logDirectionalDeriv
  rw [e2, hlog, hu2, ← hu, hW0]
  exact inv_I_smul_mul_inv hCg
theorem cubeVertices_finite_ncard (hZ : BlockStructure)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hj : j < k) (y : Vertex L k (j + 1)) :
    (cubeVertices L (meshAt L k j) y).Finite ∧
      (cubeVertices L (meshAt L k j) y).ncard = L ^ 4 := by
  obtain ⟨-, -, hcard, hsub⟩ := (hZ L k (j + 1) hL (by omega) (by omega) (by omega)).2.1 y
  have hcard' : (cube L (meshAt L k j) y).ncard = L ^ 4 := hcard
  have hsub' : cube L (meshAt L k j) y ⊆
      (InfiniteLattice.latticeSubgroup (meshAt L k j) : Set InfiniteLattice.AmbientSpace) := hsub
  have hpos : 0 < L := by
    have := hL.2
    omega
  have hfin : (cube L (meshAt L k j) y).Finite :=
    Set.finite_of_ncard_pos (by rw [hcard']; positivity)
  have himage : Subtype.val '' cubeVertices L (meshAt L k j) y = cube L (meshAt L k j) y := by
    ext p
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact hz
    · intro hp
      exact ⟨⟨p, hsub' hp⟩, hp, rfl⟩
  refine ⟨Set.Finite.of_finite_image (by rw [himage]; exact hfin)
    Subtype.val_injective.injOn, ?_⟩
  rw [← Set.ncard_image_of_injective _ Subtype.val_injective, himage]
  exact hcard'
theorem weight_finsum_const (hZ : BlockStructure) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hj : j < k) (y : Vertex L k (j + 1)) (A : ComplexMatrix2) :
    PeriodicLattice.inverseFourthPowerWeight L • ∑ᶠ x ∈ cubeVertices L (meshAt L k j) y, A = A := by
  obtain ⟨hfin, hcard⟩ := cubeVertices_finite_ncard hZ hL hj y
  have hL0 : (L : ℂ) ≠ 0 := by
    have : L ≠ 0 := by
      have := hL.2
      omega
    exact_mod_cast this
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin, Finset.sum_const,
    ← Set.ncard_eq_toFinset_card _ hfin, hcard, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  have e : PeriodicLattice.inverseFourthPowerWeight L * ((L ^ 4 : ℕ) : ℂ) = 1 := by
    simp only [PeriodicLattice.inverseFourthPowerWeight]
    push_cast
    rw [zpow_neg]
    field_simp
  rw [e, one_smul]
end RealStep
section ComplexSplitting
variable {L k j : ℕ}
def hermitianComponent (X : ComplexMatrix2) : ComplexMatrix2 := (2⁻¹ : ℂ) • (X + X.conjTranspose)
def imaginaryComponent (X : ComplexMatrix2) : ComplexMatrix2 :=
  ((2 * Complex.I)⁻¹ : ℂ) • (X - X.conjTranspose)
theorem trace_conjTranspose_eq_zero {X : ComplexMatrix2} (h : X ∈ ComplexMatrix2.traceless) :
    X.conjTranspose.trace = 0 := by
  have e : X.trace = 0 := h
  rw [Matrix.trace_conjTranspose, e, star_zero]
theorem hermitianComponent_mem {X : ComplexMatrix2} (h : X ∈ ComplexMatrix2.traceless) :
    hermitianComponent X ∈ ComplexMatrix2.hermitianTraceless := by
  have e : X.trace = 0 := h
  refine ⟨?_, ?_⟩
  · simp [hermitianComponent, Matrix.conjTranspose_smul, add_comm]
  · simp [hermitianComponent, Matrix.trace_smul, Matrix.trace_add, e,
      trace_conjTranspose_eq_zero h]
theorem imaginaryComponent_mem {X : ComplexMatrix2} (h : X ∈ ComplexMatrix2.traceless) :
    imaginaryComponent X ∈ ComplexMatrix2.hermitianTraceless := by
  have e : X.trace = 0 := h
  refine ⟨?_, ?_⟩
  · have hc : star ((2 * Complex.I)⁻¹ : ℂ) = -((2 * Complex.I)⁻¹ : ℂ) := by
      simp [Complex.conj_I]
    simp only [imaginaryComponent, Matrix.conjTranspose_smul, Matrix.conjTranspose_sub,
      Matrix.conjTranspose_conjTranspose, hc, neg_smul, ← smul_neg, neg_sub]
  · simp [imaginaryComponent, Matrix.trace_smul, Matrix.trace_sub, e,
      trace_conjTranspose_eq_zero h]
theorem traceless_of_mem_hermitianTraceless {X : ComplexMatrix2}
    (h : X ∈ ComplexMatrix2.hermitianTraceless) : X ∈ ComplexMatrix2.traceless := h.2
theorem I_smul_imaginaryComponent_add_hermitianComponent (X : ComplexMatrix2) :
    Complex.I • imaginaryComponent X + hermitianComponent X = X := by
  have h2 : (2 : ℂ) ≠ 0 := two_ne_zero
  have e : Complex.I • ((2 * Complex.I)⁻¹ : ℂ) • (X - X.conjTranspose) =
      (2⁻¹ : ℂ) • (X - X.conjTranspose) := by
    rw [smul_smul]
    congr 1
    field_simp [Complex.I_ne_zero]
  rw [imaginaryComponent, hermitianComponent, e, ← smul_add]
  have : X - X.conjTranspose + (X + X.conjTranspose) = (2 : ℂ) • X := by
    rw [two_smul]
    abel
  rw [this, smul_smul, inv_mul_cancel₀ h2, one_smul]
theorem extendOddly_ext (hL : Conventions.IsAdmissibleBlockingFactor L)
    {f g : Edge L k j → ComplexMatrix2}
    (h : ∀ b : Edge L k j, b.IsPositivelyOriented → extendOddly f b = extendOddly g b) :
    extendOddly f = extendOddly g := by
  refine extendOddly_congr hL fun b hb => ?_
  have := h b hb
  simpa only [extendOddly, if_pos hb] using this
theorem neg_mem_hermitianTraceless_pi {f : Vertex L k j → ComplexMatrix2}
    (hf : ∀ x, f x ∈ ComplexMatrix2.hermitianTraceless) :
    ∀ x, (-f) x ∈ ComplexMatrix2.hermitianTraceless :=
  fun x => ComplexMatrix2.hermitianTraceless.neg_mem (hf x)
theorem neg_mem_traceless_pi {f : Vertex L k j → ComplexMatrix2}
    (hf : ∀ x, f x ∈ ComplexMatrix2.traceless) : ∀ x, (-f) x ∈ ComplexMatrix2.traceless :=
  fun x => ComplexMatrix2.traceless.neg_mem (hf x)
end ComplexSplitting
theorem covariantStepRelations_holds (H : ExpChartHolomorphy.ExpChartTheory)
    (hS : _root_.YangMills.Construction.Tower.SmoothingNearIdentity)
    (hG : ComplexMeanLiesInComplexGaugeGroup)
    (hA : LeftChartFields.Claim)
    (hQ : SublatticesSymmetriesScalingsAndProjections.Statement)
    (hP : DoubleBlockPolydisc.PolydiscsHold) (hC : LeftChartFacts.HoldEverywhere)
    (hW : MeanStableFields.MeanStableFieldsHold)
    (hO : IteratedMeans.IteratedMeansHold)
    (hZ : BlockStructure)
    (hI : ComplexMatrix2.UnitaryLogConjugationProperties)
    (hN : CovariantStepComplexLinear) : CovariantStepRelations := by
  intro L hL k j hj V hV f hf
  classical
  have hLin := hN L hL k j hj V hV
  have real1 : ∀ m : Vertex L k j → ComplexMatrix2,
      (∀ x, m x ∈ ComplexMatrix2.hermitianTraceless) →
      complexSmoothingDeriv V (covDiff V m) =
        covDiff (smoothingMap L k j V) (restrictVertexFunction (meshAt L k (j + 1)) m) := by
    intro m hm
    unfold complexSmoothingDeriv holLeftDifferential
    conv_rhs => unfold covDiff
    refine extendOddly_ext hL fun c hc => ?_
    have h := complexSmoothingDeriv_neg_covDiff H hS hQ hP hC hW hO hI hL hj hV
      (neg_mem_hermitianTraceless_pi hm)
      (neg_mem_traceless_pi fun x => traceless_of_mem_hermitianTraceless (hm x)) hc
    rw [covDiff_neg, neg_neg] at h
    refine h.trans ?_
    show _ = covDiff (smoothingMap L k j V)
      (restrictVertexFunction (meshAt L k (j + 1)) m) c
    simp only [covDiff, extendOddly, if_pos hc, restrictVertexFunction, Pi.neg_apply,
      conjugateBy_neg, smoothingMap]
    abel
  have real2 : ∀ m : Vertex L k j → ComplexMatrix2,
      (∀ x, m x ∈ ComplexMatrix2.hermitianTraceless) →
      contourLogDrift V (covDiff V m) =
        adjointCubeAverage V m - restrictVertexFunction (meshAt L k (j + 1)) m := by
    intro m hm
    funext y
    obtain ⟨hfin, -⟩ := cubeVertices_finite_ncard hZ hL hj y
    have hterm : ∀ x ∈ cubeVertices L (meshAt L k j) y,
        logDirectionalDeriv ℂ (fun X => complexContourMean L (expTwist X V) y x)
            (complexContourMean L V y x) (covDiff V m) =
          ComplexMatrix2.conjugateBy (complexContourMean L V y x) (m x) -
            m (toFiner (meshAt L k j) y) := by
      intro x hx
      have h := logDirectionalDeriv_contourMean H hS hG hA hQ hP hC hW hI hN hL hj hV
        (neg_mem_hermitianTraceless_pi hm)
        (neg_mem_traceless_pi fun x => traceless_of_mem_hermitianTraceless (hm x)) y hx
      rw [covDiff_neg, neg_neg] at h
      refine h.trans ?_
      simp only [Pi.neg_apply, conjugateBy_neg]
      abel
    have e1 : contourLogDrift V (covDiff V m) y =
        PeriodicLattice.inverseFourthPowerWeight L • ∑ᶠ x ∈ cubeVertices L (meshAt L k j) y,
          (ComplexMatrix2.conjugateBy (complexContourMean L V y x) (m x) -
            m (toFiner (meshAt L k j) y)) :=
      congrArg _ (finsum_mem_congr rfl hterm)
    rw [e1, finsum_mem_sub_distrib _ _ hfin, smul_sub, weight_finsum_const hZ hL hj]
    rfl
  let q : Vertex L k j → ComplexMatrix2 := fun x => imaginaryComponent (f x)
  let p : Vertex L k j → ComplexMatrix2 := fun x => hermitianComponent (f x)
  have hq : ∀ x, q x ∈ ComplexMatrix2.hermitianTraceless := fun x => imaginaryComponent_mem (hf x)
  have hp : ∀ x, p x ∈ ComplexMatrix2.hermitianTraceless := fun x => hermitianComponent_mem (hf x)
  have hq' : ∀ x, q x ∈ ComplexMatrix2.traceless :=
    fun x => traceless_of_mem_hermitianTraceless (hq x)
  have hp' : ∀ x, p x ∈ ComplexMatrix2.traceless :=
    fun x => traceless_of_mem_hermitianTraceless (hp x)
  have hsplit : f = Complex.I • q + p :=
    funext fun x => (I_smul_imaginaryComponent_add_hermitianComponent (f x)).symm
  have hDq := (hLin.2.2.1 q hq').1
  have hDp := (hLin.2.2.1 p hp').1
  have hDf : covDiff V f = Complex.I • covDiff V q + covDiff V p := by
    rw [hsplit]
    exact covDiff_smul_add V q p Complex.I
  have haf : adjointCubeAverage V f =
      Complex.I • adjointCubeAverage V q + adjointCubeAverage V p := by
    rw [hsplit]
    exact (hLin.2.2.2 q p hq' hp' Complex.I).2
  have hrf : restrictVertexFunction (meshAt L k (j + 1)) f =
      Complex.I • restrictVertexFunction (meshAt L k (j + 1)) q +
        restrictVertexFunction (meshAt L k (j + 1)) p := by
    rw [hsplit]
    rfl
  have first : complexSmoothingDeriv V (covDiff V f) =
      covDiff (smoothingMap L k j V) (restrictVertexFunction (meshAt L k (j + 1)) f) := by
    rw [hDf, (hLin.2.1 _ hDq _ hDp Complex.I).1, real1 q hq, real1 p hp, hrf, covDiff_smul_add]
  have second : contourLogDrift V (covDiff V f) =
      adjointCubeAverage V f - restrictVertexFunction (meshAt L k (j + 1)) f := by
    rw [hDf, (hLin.2.1 _ hDq _ hDp Complex.I).2, real2 q hq, real2 p hp, haf, hrf, smul_sub]
    abel
  refine ⟨first, second, ?_⟩
  show complexSmoothingDeriv V (covDiff V f) +
    covDiff (smoothingMap L k j V) (contourLogDrift V (covDiff V f)) = _
  have e := covDiff_smul_add (smoothingMap L k j V)
    (adjointCubeAverage V f - restrictVertexFunction (meshAt L k (j + 1)) f)
    (restrictVertexFunction (meshAt L k (j + 1)) f) 1
  rw [one_smul, one_smul, sub_add_cancel] at e
  rw [first, second, e]
  exact add_comm _ _
end YangMills.Construction.Tower.FullSpace.StepRelations
end
