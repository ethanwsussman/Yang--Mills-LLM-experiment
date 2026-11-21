import YangMills.Construction.RunningCouplingSlope.PlainAverageNearOneOnTheWholeProof
import YangMills.Construction.RunningCouplingSlope.PlainIteratesOfAFieldOnTheWholeProof
import YangMills.Construction.Towers.GaugeCovarianceOfTheCovariantAveragesAtTheSideInfinityProof
import YangMills.Construction.Towers.LinearityOfTheCovariantStepAtTheSideInfinityProof
import YangMills.Construction.Towers.TheMapsOfOneStepKeepRealFunctions
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open Set Filter Topology
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope.FullLattice
namespace CompactMeanStep
open Tower Matrices Matrix
private instance : CompleteSpace ComplexMatrix2 := FiniteDimensional.complete ℂ ComplexMatrix2
section MatrixFacts
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
private theorem analyticAt_matrix_inv {f : E → ComplexMatrix2} {x : E} (hf : AnalyticAt ℂ f x)
    (hu : IsUnit (Matrix.det (f x))) : AnalyticAt ℂ (fun y => (f y)⁻¹) x := by apply _root_.YangMills.SharedProofs.p7089 <;> assumption
private theorem analyticAt_matrix_entry {f : E → ComplexMatrix2} {x : E} (hf : AnalyticAt ℂ f x)
    (a b : Fin 2) : AnalyticAt ℂ (fun y => f y a b) x :=
  ((LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℂ ℂ a b :
    ComplexMatrix2 →ₗ[ℂ] ℂ)).analyticAt _).comp hf
private theorem analyticAt_matrix_det {f : E → ComplexMatrix2} {x : E} (hf : AnalyticAt ℂ f x) :
    AnalyticAt ℂ (fun y => Matrix.det (f y)) x := by
  have e : (fun y => Matrix.det (f y)) = fun y => f y 0 0 * f y 1 1 - f y 0 1 * f y 1 0 := by
    funext y
    exact Matrix.det_fin_two _
  rw [e]
  exact ((analyticAt_matrix_entry hf 0 0).mul (analyticAt_matrix_entry hf 1 1)).sub
    ((analyticAt_matrix_entry hf 0 1).mul (analyticAt_matrix_entry hf 1 0))
abbrev _root_.YangMills.SharedProofs.p3818 := @analyticAt_matrix_det
private theorem inv_inv_of_mem_complexGaugeGroup {X : ComplexMatrix2}
    (h : X ∈ PeriodicLattice.complexGaugeGroup) : X⁻¹⁻¹ = X := by apply _root_.YangMills.SharedProofs.p6288 <;> assumption
end MatrixFacts
section Links
variable {a : ℝ}
private theorem isPositivelyOriented_or_opposite (b : InfiniteLattice.Link a) :
    b.IsPositivelyOriented ∨ b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.InfiniteLattice.GibbsForms.isPositivelyOriented_or_opposite <;> assumption
private theorem extendOddly_of_positive (f : InfiniteLattice.Link a → ComplexMatrix2)
    {b : InfiniteLattice.Link a} (hb : b.IsPositivelyOriented) :
    FullSpace.extendOddly f b = f b := if_pos hb
private theorem extendOddly_of_not_positive (f : InfiniteLattice.Link a → ComplexMatrix2)
    {b : InfiniteLattice.Link a} (hb : ¬ b.IsPositivelyOriented) :
    FullSpace.extendOddly f b = -f b.opposite := by apply _root_.YangMills.Construction.Tower.FullSpace.CovarianceProof.extendOddly_of_not_pos <;> assumption
private theorem cubeVertices_finite (L : ℕ) {a : ℝ} (a' : ℝ) (y : InfiniteLattice.LatticePoint a) :
    (FullSpace.cubeVertices L a' y : Set (InfiniteLattice.LatticePoint a')).Finite := by apply _root_.YangMills.Construction.Tower.FullSpace.LinearityProof.cubeVertices_finite <;> assumption
end Links
section MeanAlongParameter
variable {L k j : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
private theorem linkHolonomy_analyticAt {a : ℝ} {W : E → InfiniteLattice.Link a → ComplexMatrix2}
    {q : E} (hW : ∀ b, AnalyticAt ℂ (fun x => W x b) q) (l : List (InfiniteLattice.Link a)) :
    AnalyticAt ℂ (fun x => FullSpace.linkHolonomy (W x) l) q := by
  induction l with
  | nil => simpa [FullSpace.linkHolonomy] using analyticAt_const
  | cons b l ih =>
    have e : (fun x => FullSpace.linkHolonomy (W x) (b :: l)) =
        fun x => W x b * FullSpace.linkHolonomy (W x) l := by
      funext x
      simp [FullSpace.linkHolonomy]
    rw [e]
    exact (hW b).fun_mul ih
private theorem det_linkHolonomy {a : ℝ} (V : InfiniteLattice.Link a → ComplexMatrix2)
    (hV : ∀ b, Matrix.det (V b) = 1) (l : List (InfiniteLattice.Link a)) :
    Matrix.det (FullSpace.linkHolonomy V l) = 1 := by
  induction l with
  | nil => simp [FullSpace.linkHolonomy]
  | cons b l ih =>
    have : Matrix.det ((l.map V).prod) = 1 := ih
    simp [FullSpace.linkHolonomy, Matrix.det_mul, hV, this]
private theorem contourMean_analyticAt {W : E → FullSpace.Edge L k j → ComplexMatrix2} {q : E}
    (hW : ∀ b, AnalyticAt ℂ (fun x => W x b) q) (hdet : ∀ b, Matrix.det (W q b) = 1)
    (c : FullSpace.Edge L k (j + 1)) : AnalyticAt ℂ (fun x => contourMean (W x) c) q := by
  have hfin := cubeVertices_finite L (meshAt L k j) c.initial
  have hcv : ∀ x π, AnalyticAt ℂ (fun w => contourHolonomy (W w) c x π) q := fun x π => by
    have hu : IsUnit (Matrix.det (FullSpace.linkHolonomy (W q)
        (contourLeg c.terminal (FullSpace.shifted c x) π))) := by
      rw [det_linkHolonomy _ hdet]
      exact isUnit_one
    exact ((linkHolonomy_analyticAt hW _).fun_mul (linkHolonomy_analyticAt hW _)).fun_mul
      (analyticAt_matrix_inv (linkHolonomy_analyticAt hW _) hu)
  have e : (fun x => contourMean (W x) c) = fun w =>
      ((1 / 24 : ℂ) * PeriodicLattice.inverseFourthPowerWeight L) • ∑ x ∈ hfin.toFinset,
        ∑ π : Equiv.Perm (Fin 4), contourHolonomy (W w) c x π := by
    funext w
    rw [contourMean, finsum_mem_eq_finite_toFinset_sum _ hfin]
  rw [e]
  exact analyticAt_const.fun_smul (Finset.analyticAt_fun_sum _ fun x _ =>
    Finset.analyticAt_fun_sum _ fun π _ => hcv x π)
abbrev _root_.YangMills.SharedProofs.p59327 := @contourMean_analyticAt
private theorem meanRadius_analyticAt {W : E → FullSpace.Edge L k j → ComplexMatrix2} {q : E}
    (hW : ∀ b, AnalyticAt ℂ (fun x => W x b) q) (hdet : ∀ b, Matrix.det (W q b) = 1)
    {c : FullSpace.Edge L k (j + 1)} (hs : Matrix.det (contourMean (W q) c) ∈ Complex.slitPlane) :
    AnalyticAt ℂ (fun x => meanRadius (W x) c) q :=
  (analyticAt_matrix_det (contourMean_analyticAt hW hdet c)).cpow analyticAt_const hs
private theorem normalizedMean_analyticAt {W : E → FullSpace.Edge L k j → ComplexMatrix2} {q : E}
    (hW : ∀ b, AnalyticAt ℂ (fun x => W x b) q) (hdet : ∀ b, Matrix.det (W q b) = 1)
    {c : FullSpace.Edge L k (j + 1)} (hs : Matrix.det (contourMean (W q) c) ∈ Complex.slitPlane)
    (hr : meanRadius (W q) c ≠ 0) : AnalyticAt ℂ (fun x => normalizedMean (W x) c) q :=
  ((meanRadius_analyticAt hW hdet hs).inv hr).fun_smul (contourMean_analyticAt hW hdet c)
private theorem normalizedMean_mem {V : FullSpace.Edge L k j → ComplexMatrix2}
    {c : FullSpace.Edge L k (j + 1)} (hr : meanRadius V c ≠ 0) :
    normalizedMean V c ∈ PeriodicLattice.complexGaugeGroup := by
  change Matrix.det (normalizedMean V c) = 1
  have hsq : (meanRadius V c) ^ 2 = Matrix.det (contourMean V c) := by
    have := Complex.cpow_nat_inv_pow (Matrix.det (contourMean V c)) (n := 2) (by norm_num)
    simpa [meanRadius] using this
  rw [normalizedMean, Matrix.det_smul, Fintype.card_fin, inv_pow, ← hsq]
  exact inv_mul_cancel₀ (pow_ne_zero 2 hr)
abbrev _root_.YangMills.SharedProofs.p29259 := @normalizedMean_mem
private theorem normalizedMean_eventually_mem {W : E → FullSpace.Edge L k j → ComplexMatrix2}
    {q : E} (hW : ∀ b, AnalyticAt ℂ (fun x => W x b) q) (hdet : ∀ b, Matrix.det (W q b) = 1)
    {c : FullSpace.Edge L k (j + 1)} (hs : Matrix.det (contourMean (W q) c) ∈ Complex.slitPlane)
    (hr : meanRadius (W q) c ≠ 0) :
    ∀ᶠ x in 𝓝 q, normalizedMean (W x) c ∈ PeriodicLattice.complexGaugeGroup :=
  ((meanRadius_analyticAt hW hdet hs).continuousAt.eventually_ne hr).mono
    fun _ h => normalizedMean_mem h
end MeanAlongParameter
section Quaternionic
private def IsQuaternionic (A : ComplexMatrix2) : Prop := Matrix.adjugate A = Aᴴ
private theorem isQuaternionic_of_mem {g : ComplexMatrix2}
    (hg : g ∈ ComplexMatrix2.specialUnitary) : IsQuaternionic g := by apply _root_.YangMills.DeltaSharedProofs.p2612 <;> assumption
private theorem IsQuaternionic.add {A B : ComplexMatrix2} (hA : IsQuaternionic A)
    (hB : IsQuaternionic B) : IsQuaternionic (A + B) := by apply _root_.YangMills.DeltaSharedProofs.p501936 <;> assumption
private theorem IsQuaternionic.real_smul (r : ℝ) {A : ComplexMatrix2} (hA : IsQuaternionic A) :
    IsQuaternionic ((r : ℂ) • A) := by apply _root_.YangMills.DeltaSharedProofs.p500416 <;> assumption
private theorem isQuaternionic_zero : IsQuaternionic 0 := by apply _root_.YangMills.DeltaSharedProofs.p502226 <;> assumption
private theorem isQuaternionic_sum {ι : Type*} (s : Finset ι) (f : ι → ComplexMatrix2)
    (h : ∀ i ∈ s, IsQuaternionic (f i)) : IsQuaternionic (∑ i ∈ s, f i) := by apply _root_.YangMills.DeltaSharedProofs.p502446 <;> assumption
private theorem IsQuaternionic.det_nonneg_real {A : ComplexMatrix2} (hA : IsQuaternionic A) :
    ∃ d : ℝ, 0 ≤ d ∧ Matrix.det A = (d : ℂ) := by apply _root_.YangMills.DeltaSharedProofs.p501399 <;> assumption
private theorem inv_mem_specialUnitary {g : ComplexMatrix2}
    (hg : g ∈ ComplexMatrix2.specialUnitary) : g⁻¹ ∈ ComplexMatrix2.specialUnitary := by apply _root_.YangMills.Construction.Tower.WilsonAnalyticity.inv_mem_specialUnitary <;> assumption
end Quaternionic
section TwistedFamilies
variable {L k j : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
private theorem meshAt_pos (hL : Conventions.IsAdmissibleBlockingFactor L) (k j : ℕ) :
    0 < meshAt L k j := by apply _root_.YangMills.Construction.Tower.BlockPathContourPivotProof.Periodic.meshAt_pos <;> assumption
private theorem matExp_zero : ComplexMatrix2.matExp (0 : ComplexMatrix2) = 1 :=
  NormedSpace.exp_zero
private theorem expTwist_apply_of_eq_zero {V X : FullSpace.Edge L k j → ComplexMatrix2}
    {P : Set (FullSpace.Edge L k j)} (hP : ∀ b ∈ P, b.opposite ∈ P)
    (hV : V ∈ FullSpace.fieldsValuedIn L k j PeriodicLattice.complexGaugeGroup)
    (h : ∀ b ∈ P, X b = 0) {b : FullSpace.Edge L k j} (hb : b ∈ P) :
    FullSpace.expTwist X V b = V b := by
  unfold FullSpace.expTwist
  split_ifs
  · rw [h b hb, smul_zero, matExp_zero, one_mul]
  · rw [h _ (hP b hb), smul_zero, matExp_zero, one_mul, hV.2 b]
    exact inv_inv_of_mem_complexGaugeGroup (hV.1 b)
abbrev _root_.YangMills.SharedProofs.p9435 := @expTwist_apply_of_eq_zero
private theorem expTwist_eq_self {V X : FullSpace.Edge L k j → ComplexMatrix2}
    (hV : V ∈ FullSpace.fieldsValuedIn L k j PeriodicLattice.complexGaugeGroup)
    (h : ∀ b, X b = 0) : FullSpace.expTwist X V = V :=
  funext fun b => expTwist_apply_of_eq_zero (P := Set.univ) (fun _ _ => mem_univ _) hV
    (fun b _ => h b) (mem_univ b)
private theorem expTwist_family_analyticAt {V : FullSpace.Edge L k j → ComplexMatrix2}
    (hdet : ∀ b, Matrix.det (V b) = 1) {X : E → FullSpace.Edge L k j → ComplexMatrix2}
    (hX : ∀ b, ∃ m : E →L[ℂ] ComplexMatrix2, ∀ q, X q b = m q) {q₀ : E}
    (h0 : ∀ b, X q₀ b = 0) (b : FullSpace.Edge L k j) :
    AnalyticAt ℂ (fun q => FullSpace.expTwist (X q) V b) q₀ := by
  have hval : ∀ b' : FullSpace.Edge L k j,
      AnalyticAt ℂ (fun q => ComplexMatrix2.matExp (Complex.I • X q b') * V b') q₀ := fun b' => by
    obtain ⟨m, hm⟩ := hX b'
    let m' : E →L[ℂ] ComplexMatrix2 := (Complex.I • ContinuousLinearMap.id ℂ ComplexMatrix2).comp m
    have h1 : AnalyticAt ℂ (fun q => ComplexMatrix2.matExp (Complex.I • m q)) q₀ :=
      AnalyticAt.comp (g := NormedSpace.exp) (f := m')
        (NormedSpace.exp_analytic (𝕂 := ℂ) (m' q₀)) (m'.analyticAt _)
    simp only [hm]
    exact h1.fun_mul analyticAt_const
  by_cases hb : b.IsPositivelyOriented
  · refine (hval b).congr (Eventually.of_forall fun q => ?_)
    exact (if_pos hb : FullSpace.expTwist (X q) V b = _).symm
  · have hu : IsUnit (Matrix.det
        (ComplexMatrix2.matExp (Complex.I • X q₀ b.opposite) * V b.opposite)) := by
      rw [h0, smul_zero, matExp_zero, one_mul, hdet]
      exact isUnit_one
    refine (analyticAt_matrix_inv (hval b.opposite) hu).congr (Eventually.of_forall fun q => ?_)
    exact (if_neg hb : FullSpace.expTwist (X q) V b = _).symm
abbrev _root_.YangMills.SharedProofs.p50643 := @expTwist_family_analyticAt
end TwistedFamilies
section CompactValues
variable {L k j : ℕ}
private theorem linkHolonomy_mem {a : ℝ} (V : InfiniteLattice.Link a → ComplexMatrix2)
    (hV : ∀ b, V b ∈ ComplexMatrix2.specialUnitary) (l : List (InfiniteLattice.Link a)) :
    FullSpace.linkHolonomy V l ∈ ComplexMatrix2.specialUnitary := by apply _root_.YangMills.SharedProofs.p48031 <;> assumption
private theorem meanWeight_eq_real (hL : 0 < L) :
    ((1 / 24 : ℂ) * PeriodicLattice.inverseFourthPowerWeight L) =
      ((1 / (24 * (L : ℝ) ^ 4) : ℝ) : ℂ) := by apply _root_.YangMills.SharedProofs.p3617 <;> assumption
private theorem normalizedMean_mem_compact (hL : Conventions.IsAdmissibleBlockingFactor L)
    {V : FullSpace.Edge L k j → ComplexMatrix2}
    (hVs : ∀ b, V b ∈ PeriodicLattice.compactGaugeGroup) {c : FullSpace.Edge L k (j + 1)}
    (hr0 : meanRadius V c ≠ 0) : normalizedMean V c ∈ PeriodicLattice.compactGaugeGroup := by
  have hLpos : 0 < L := by
    have := hL.2
    omega
  have hu : normalizedMean V c ∈ PeriodicLattice.complexGaugeGroup := normalizedMean_mem hr0
  have hVs' : ∀ b, V b ∈ ComplexMatrix2.specialUnitary := hVs
  have hfin := cubeVertices_finite L (meshAt L k j) c.initial
  have hcv : ∀ x π, contourHolonomy V c x π ∈ ComplexMatrix2.specialUnitary := fun x π =>
    ComplexMatrix2.specialUnitary.mul_mem
      (ComplexMatrix2.specialUnitary.mul_mem (linkHolonomy_mem V hVs' _)
        (linkHolonomy_mem V hVs' _))
      (inv_mem_specialUnitary (linkHolonomy_mem V hVs' _))
  have hq : IsQuaternionic (contourMean V c) := by
    rw [contourMean, finsum_mem_eq_finite_toFinset_sum _ hfin, meanWeight_eq_real hLpos]
    refine IsQuaternionic.real_smul _ (isQuaternionic_sum _ _ fun x _ =>
      isQuaternionic_sum _ _ fun π _ => isQuaternionic_of_mem (hcv x π))
  obtain ⟨d, hd0, hd⟩ := hq.det_nonneg_real
  have hlen : meanRadius V c = (d : ℂ) ^ (1 / 2 : ℂ) := by
    rw [meanRadius, hd]
  have hreal : meanRadius V c = ((d ^ (1 / 2 : ℝ) : ℝ) : ℂ) := by
    rw [hlen, Complex.ofReal_cpow hd0]
    norm_num
  have hqu : IsQuaternionic (normalizedMean V c) := by
    rw [normalizedMean, hreal, ← Complex.ofReal_inv]
    exact IsQuaternionic.real_smul _ hq
  have hdet : Matrix.det (normalizedMean V c) = 1 := hu
  change normalizedMean V c ∈ ComplexMatrix2.specialUnitary
  rw [Matrix.mem_specialUnitaryGroup_iff]
  refine ⟨(Matrix.mem_unitaryGroup_iff').2 ?_, hdet⟩
  have h1 : Matrix.adjugate (normalizedMean V c) * normalizedMean V c = 1 := by
    rw [Matrix.adjugate_mul, hdet, one_smul]
  rw [← h1]
  congr 1
  exact hqu.symm
private def meanLogDeriv (V B : FullSpace.Edge L k j → ComplexMatrix2)
    (c : FullSpace.Edge L k (j + 1)) : ComplexMatrix2 :=
  logDirectionalDeriv ℂ (fun X => normalizedMean (FullSpace.expTwist X V) c)
    (normalizedMean V c) B
private theorem meanLogDeriv_mem (hA : LeftChartFields.Claim)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hj : j < k)
    {V : FullSpace.Edge L k j → ComplexMatrix2}
    (hV : V ∈ FullSpace.fieldsValuedIn L k j PeriodicLattice.complexGaugeGroup)
    (hVr : ∀ b, V b ∈ PeriodicLattice.compactGaugeGroup) {c : FullSpace.Edge L k (j + 1)}
    (hs : Matrix.det (contourMean V c) ∈ Complex.slitPlane) (hr : meanRadius V c ≠ 0)
    {B : FullSpace.Edge L k j → ComplexMatrix2} (hB : B ∈ FullSpace.edgeFormSpace (meshAt L k j)) :
    meanLogDeriv V B c ∈ ComplexMatrix2.hermitianTraceless := by
  have hdet : ∀ b, Matrix.det (V b) = 1 := fun b => hV.1 b
  let W : ℂ → FullSpace.Edge L k j → ComplexMatrix2 := fun t => FullSpace.expTwist (t • B) V
  have hXl : ∀ b, ∃ m : ℂ →L[ℂ] ComplexMatrix2, ∀ t : ℂ, (t • B) b = m t := fun b =>
    ⟨(ContinuousLinearMap.id ℂ ℂ).smulRight (B b), fun t => by simp⟩
  have hW : ∀ b, AnalyticAt ℂ (fun t => W t b) 0 :=
    expTwist_family_analyticAt hdet hXl (q₀ := (0 : ℂ)) fun b => by simp
  have hW0 : W 0 = V := expTwist_eq_self hV fun b => by simp
  have hdet0 : ∀ b, Matrix.det (W 0 b) = 1 := fun b => by
    rw [hW0]
    exact hdet b
  have hs0 : Matrix.det (contourMean (W 0) c) ∈ Complex.slitPlane := by
    rw [hW0]
    exact hs
  have hr0 : meanRadius (W 0) c ≠ 0 := by
    rw [hW0]
    exact hr
  have hF := normalizedMean_analyticAt hW hdet0 hs0 hr0
  have hg := normalizedMean_eventually_mem hW hdet0 hs0 hr0
  have hlen := meanRadius_analyticAt hW hdet0 hs0
  set F : ℂ → ComplexMatrix2 := fun t => normalizedMean (W t) c with hFdef
  have hD : HasDerivAt F (deriv F 0) 0 := hF.differentiableAt.hasDerivAt
  have e1 : meanLogDeriv V B c = Complex.I⁻¹ • (deriv F 0 * (normalizedMean V c)⁻¹) := by
    have hlog := fun (ρ : ℝ) (hρ : 0 < ρ) => hA.2.1 ρ hρ
    obtain ⟨r, hr', hball⟩ := Metric.eventually_nhds_iff_ball.1 hg
    obtain ⟨-, -, e, -⟩ := hlog r hr' F (fun t ht => hball t ht) hD.differentiableAt
    rw [hD.deriv] at e
    have e0 : F 0 = normalizedMean V c := by
      show normalizedMean (W 0) c = _
      rw [hW0]
    rw [e0] at e
    exact e
  let γ : ℝ → ComplexMatrix2 := fun s => F (s : ℂ)
  have hof : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 0 := Complex.ofRealCLM.hasDerivAt
  have hγ : HasDerivAt γ (deriv F 0) 0 := by
    have hD' : HasDerivAt F (deriv F 0) (((0 : ℝ) : ℂ)) := by
      rw [Complex.ofReal_zero]
      exact hD
    have h3 := HasDerivAt.scomp (0 : ℝ) (g₁ := F) (h := fun s : ℝ => (s : ℂ)) hD' hof
    rw [one_smul] at h3
    exact h3
  have hcont : ContinuousAt (fun s : ℝ => (s : ℂ)) 0 := Complex.continuous_ofReal.continuousAt
  have hne : ∀ᶠ s : ℝ in 𝓝 0, meanRadius (W s) c ≠ 0 := by
    have h1 : ContinuousAt (fun s : ℝ => meanRadius (W s) c) 0 :=
      ContinuousAt.comp (g := fun t => meanRadius (W t) c) (f := fun s : ℝ => (s : ℂ))
        (by simpa using hlen.continuousAt) hcont
    exact h1.eventually_ne (by simpa using hr0)
  have hWr : ∀ (s : ℝ) b, W s b ∈ PeriodicLattice.compactGaugeGroup := by
    have hreal : V ∈ FullSpace.fieldsValuedIn L k j PeriodicLattice.compactGaugeGroup :=
      ⟨hVr, hV.2⟩
    have hgp : ∀ (s : ℝ) (b : FullSpace.Edge L k j), b.IsPositivelyOriented →
        ComplexMatrix2.matExp (Complex.I • ((s : ℂ) • B) b) * V b ∈
          PeriodicLattice.compactGaugeGroup := fun s b hb =>
      (((hA.2.2 L k j hL hj.le).2.1.1).1 V hreal B hB ⟨b, hb⟩).1 s
    intro s b
    by_cases hb : b.IsPositivelyOriented
    · have e : W s b = ComplexMatrix2.matExp (Complex.I • ((s : ℂ) • B) b) * V b := if_pos hb
      rw [e]
      exact hgp s b hb
    · have e : W s b = (ComplexMatrix2.matExp (Complex.I • ((s : ℂ) • B) b.opposite) *
          V b.opposite)⁻¹ := if_neg hb
      rw [e]
      exact inv_mem_specialUnitary (hgp s _ ((isPositivelyOriented_or_opposite b).resolve_left hb))
  obtain ⟨r, hr', hball⟩ := Metric.eventually_nhds_iff_ball.1 hne
  have hI : IsOpenIntervalAroundZero (Metric.ball (0 : ℝ) r) := by
    refine ⟨Metric.isOpen_ball, ?_, Metric.mem_ball_self hr'⟩
    rw [Real.ball_eq_Ioo]
    exact Set.ordConnected_Ioo
  have hm : MapsTo γ (Metric.ball (0 : ℝ) r) PeriodicLattice.compactGaugeGroup := fun s hs' =>
    normalizedMean_mem_compact hL (hWr s) (hball s hs')
  obtain ⟨-, -, -, e2⟩ := (hA.1 _ hI).1 γ hm hγ.differentiableAt
  rw [hγ.deriv] at e2
  have e0 : γ 0 = normalizedMean V c := by
    show normalizedMean (W ((0 : ℝ) : ℂ)) c = _
    rw [Complex.ofReal_zero, hW0]
  rw [e0] at e2
  rw [e1]
  exact e2
private theorem conjugateBy_mem {A X : ComplexMatrix2} (hA : A ∈ PeriodicLattice.compactGaugeGroup)
    (hX : X ∈ ComplexMatrix2.hermitianTraceless) :
    ComplexMatrix2.conjugateBy A X ∈ ComplexMatrix2.hermitianTraceless := by apply _root_.YangMills.SharedProofs.p2904 <;> assumption
private theorem meanCovariantStep_of_positive (V B : FullSpace.Edge L k j → ComplexMatrix2)
    {c : FullSpace.Edge L k (j + 1)} (hc : c.IsPositivelyOriented) :
    meanCovariantStep V B c = meanLogDeriv V B c +
      (ComplexMatrix2.conjugateBy (normalizedMean V c) (FullSpace.contourLogDrift V B c.terminal) -
        FullSpace.contourLogDrift V B c.initial) := by
  unfold meanCovariantStep FullSpace.covDiff
  simp only [Pi.add_apply, extendOddly_of_positive _ hc]
  rfl
abbrev _root_.YangMills.DeltaSharedProofs.p501203 := @meanCovariantStep_of_positive
end CompactValues
end CompactMeanStep
open CompactMeanStep Tower Matrices in
theorem meanStepAtCompactFields_holds (hN : NormalizedMeanNearIdentity)
    (hS : SmoothingNearIdentity)
    (hA : LeftChartFields.Claim)
    (hR : FullSpace.RealityOfOneStep.Statement) :
    MeanStepAtCompactFields := by
  intro L hL
  obtain ⟨δ₁, hδ₁, H⟩ := hN L hL 1 one_pos
  have hρ : 0 < polydiscRadius L := (hS.1 L hL).2.2.pos
  refine ⟨min δ₁ (polydiscRadius L), lt_min hδ₁ hρ, ?_⟩
  intro k j hj V hV hVr
  have hnear := fun (c : FullSpace.Edge L k (j + 1)) (hc : c.IsPositivelyOriented) =>
    H k j hj V hV.1 (fun b => (hV.2 b).trans_le (min_le_left _ _)) c hc
  have hsm : V ∈ FullSpace.smallComplexFields L k j :=
    ⟨hV.1, fun b => (hV.2 b).trans_le (min_le_right _ _)⟩
  have hcf : V ∈ FullSpace.fieldSpace L k j := ⟨hVr, hV.1.2⟩
  obtain ⟨-, -, -, hD, -⟩ := hR L hL k j hj V hsm hcf
  have hpos : ∀ B ∈ FullSpace.edgeFormSpace (meshAt L k j), ∀ c : FullSpace.Edge L k (j + 1),
      c.IsPositivelyOriented → meanCovariantStep V B c ∈ ComplexMatrix2.hermitianTraceless := by
    intro B hB c hc
    rw [meanCovariantStep_of_positive V B hc]
    have hd := hD B hB
    exact ComplexMatrix2.hermitianTraceless.add_mem
      (meanLogDeriv_mem hA hL hj hV.1 hVr (hnear c hc).1 (hnear c hc).2.1 hB)
      (ComplexMatrix2.hermitianTraceless.sub_mem
        (conjugateBy_mem ((hnear c hc).2.2.2.2 hVr).2.2 (hd _ (mem_univ _))) (hd _ (mem_univ _)))
  refine ⟨fun c => ?_, fun c hc => ?_, fun B hB c => ?_⟩
  · by_cases hc : c.IsPositivelyOriented
    · have e : nextMeanIterate V c = normalizedMean V c := if_pos hc
      rw [e]
      exact ((hnear c hc).2.2.2.2 hVr).2.2
    · have hr' := (isPositivelyOriented_or_opposite c).resolve_left hc
      have e : nextMeanIterate V c = (normalizedMean V c.opposite)⁻¹ := if_neg hc
      rw [e]
      exact inv_mem_specialUnitary ((hnear _ hr').2.2.2.2 hVr).2.2
  · have h := ((hnear c hc).2.2.2.2 hVr).1
    rw [h]
    simp
  · by_cases hc : c.IsPositivelyOriented
    · exact hpos B hB c hc
    · have hr' := (isPositivelyOriented_or_opposite c).resolve_left hc
      have ha := meshAt_pos hL k (j + 1)
      have e : meanCovariantStep V B c = -meanCovariantStep V B c.opposite := by
        unfold meanCovariantStep FullSpace.covDiff
        simp only [Pi.add_apply, extendOddly_of_not_positive _ hc, extendOddly_of_positive _ hr',
          neg_add]
      rw [e]
      exact ComplexMatrix2.hermitianTraceless.neg_mem (hpos B hB _ hr')
end YangMills.Construction.RunningCouplingSlope.FullLattice
end
