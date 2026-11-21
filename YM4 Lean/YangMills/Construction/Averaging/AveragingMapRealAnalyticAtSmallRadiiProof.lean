import YangMills.Construction.Averaging.AveragingMapRealAnalyticAtSmallRadii
import YangMills.Construction.Averaging.EverySmallRadiusServes
import YangMills.Construction.Coordinates.PowerSeriesHolomorphy
import YangMills.Construction.Lattice.AveragesAndWeightsProof
import YangMills.Construction.Lattice.CovariantAdjointsBySummationByParts
import YangMills.Construction.Lattice.DoubleBlockContours
import YangMills.Construction.Matrices.EntrywiseHolomorphicMaps
import YangMills.Construction.Matrices.ExpLogEstimates
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Averaging.SmallFieldAnalyticity
open Set PeriodicLattice Matrices Coordinates
open scoped Topology Matrix.Norms.L2Operator
section Differentiability
def matrixEntriesCLE : ComplexMatrix2 ≃L[ℂ] ComplexCoordinates 4 :=
  LinearEquiv.toContinuousLinearEquiv
    { ComplexCoordinates.matrixEquiv with
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
def familyEntriesCLE (n : ℕ) : (Fin n → ComplexMatrix2) ≃L[ℂ]
    ComplexCoordinates (ComplexCoordinates.productDim
      fun _ : Fin n => ComplexCoordinates.Component.matrix) :=
  LinearEquiv.toContinuousLinearEquiv
    { ComplexCoordinates.productEquiv fun _ : Fin n => ComplexCoordinates.Component.matrix with
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
theorem isHolomorphicIn_of_differentiableAt {N N' : ℕ} {O : Set (ComplexCoordinates N)}
    (hO : IsOpen O) {f : ComplexCoordinates N → ComplexCoordinates N'}
    (hf : ∀ a ∈ O, DifferentiableAt ℂ f a) : ComplexCoordinates.IsHolomorphicIn O f := by
  refine ⟨hO, fun a ha => (hf a ha).continuousAt.continuousWithinAt, fun a ha j => ?_⟩
  have hg : Continuous fun ζ : ℂ => a + ζ • ComplexCoordinates.stdBasisVector j := by fun_prop
  have h0 : ∀ᶠ ζ in 𝓝 (0 : ℂ), a + ζ • ComplexCoordinates.stdBasisVector j ∈ O :=
    hg.continuousAt.eventually_mem (by simpa using hO.mem_nhds ha)
  filter_upwards [h0] with ζ hζ
  exact DifferentiableAt.comp (𝕜 := ℂ) ζ (hf _ hζ) (by fun_prop)
theorem differentiableAt_of_isHolomorphicIn
    (hP : ComplexCoordinates.PowerSeriesHolomorphy.Properties) {N N' : ℕ}
    {O : Set (ComplexCoordinates N)} {f : ComplexCoordinates N → ComplexCoordinates N'}
    (hf : ComplexCoordinates.IsHolomorphicIn O f) {a : ComplexCoordinates N} (ha : a ∈ O) :
    DifferentiableAt ℂ f a := by
  obtain ⟨T, hT⟩ := ((hP.1 N O hf.1).1 N' f hf).2.2.1 a ha
  exact (hasFDerivAt_of_restrictScalars ℝ hT rfl).differentiableAt
theorem differentiableAt_of_isHolomorphicVia_matrix
    (hP : ComplexCoordinates.PowerSeriesHolomorphy.Properties) {D : Set ComplexMatrix2}
    {f : ComplexMatrix2 → ComplexMatrix2}
    (hf : ComplexCoordinates.IsHolomorphicVia ComplexCoordinates.matrixEquiv
      ComplexCoordinates.matrixEquiv D f) {X : ComplexMatrix2} (hX : X ∈ D) :
    DifferentiableAt ℂ f X := by
  have h₁ : DifferentiableAt ℂ (ComplexCoordinates.matrixEquiv ∘ f ∘
      ComplexCoordinates.matrixEquiv.symm) (matrixEntriesCLE X) :=
    differentiableAt_of_isHolomorphicIn hP hf (mem_image_of_mem _ hX)
  have h₂ := matrixEntriesCLE.symm.differentiableAt.comp X
    (h₁.comp X matrixEntriesCLE.differentiableAt)
  refine h₂.congr_of_eventuallyEq (Filter.Eventually.of_forall fun Y => ?_)
  show f Y = ComplexCoordinates.matrixEquiv.symm (ComplexCoordinates.matrixEquiv
    (f (ComplexCoordinates.matrixEquiv.symm (ComplexCoordinates.matrixEquiv Y))))
  simp
theorem differentiableAt_inv_of_isUnit {X : ComplexMatrix2} (hX : IsUnit X) :
    DifferentiableAt ℂ (fun X : ComplexMatrix2 => X⁻¹) X := by
  have h : (fun X : ComplexMatrix2 => X⁻¹) = Ring.inverse := by
    funext X
    exact Matrix.nonsing_inv_eq_ringInverse X
  rw [h]
  exact differentiableAt_inverse hX
theorem isUnit_inv_of_isUnit {X : ComplexMatrix2} (hX : IsUnit X) : IsUnit X⁻¹ := by
  rw [Matrix.nonsing_inv_eq_ringInverse]
  exact hX.ringInverse
theorem inv_mem_complexGaugeGroup {X : ComplexMatrix2} (hX : X ∈ complexGaugeGroup) :
    X⁻¹ ∈ complexGaugeGroup := by
  have h : X.det = 1 := hX
  show (X⁻¹).det = 1
  rw [Matrix.det_nonsing_inv, h]
  simp
variable {L m : ℕ} {j j' : ℤ}
theorem differentiableAt_comp_reindex
    (hP : ComplexCoordinates.PowerSeriesHolomorphy.Properties) (c : Bond L m j)
    {n n' : ℕ} (ν : positiveBondsInDoubleBlock (j' := j') c ≃ Fin n')
    (ρ : positiveBondsInDoubleBlock (j' := j') c → Fin n)
    {O : Set (positiveBondsInDoubleBlock (j' := j') c → ComplexMatrix2)}
    {f : (positiveBondsInDoubleBlock (j' := j') c → ComplexMatrix2) → ComplexMatrix2}
    (hf : ComplexCoordinates.IsHolomorphicVia (SmallRadius.doubleBlockEquiv c ν)
      ComplexCoordinates.matrixEquiv O f)
    (X : Fin n → ComplexMatrix2) (hX : (fun p => X (ρ p)) ∈ O) :
    DifferentiableAt ℂ (fun X : Fin n → ComplexMatrix2 => f fun p => X (ρ p)) X := by
  let R : (Fin n → ComplexMatrix2) →L[ℂ] (Fin n' → ComplexMatrix2) :=
    ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (ρ (ν.symm i))
  let e := SmallRadius.doubleBlockEquiv c ν
  have he : ∀ Y : Fin n → ComplexMatrix2, e (fun p => Y (ρ p)) = familyEntriesCLE n' (R Y) :=
    fun _ => rfl
  have h₁ : DifferentiableAt ℂ (ComplexCoordinates.matrixEquiv ∘ f ∘ e.symm)
      (familyEntriesCLE n' (R X)) :=
    differentiableAt_of_isHolomorphicIn hP hf ⟨_, hX, he X⟩
  have h₂ : DifferentiableAt ℂ (fun Y => familyEntriesCLE n' (R Y)) X :=
    (familyEntriesCLE n').differentiableAt.comp X R.differentiableAt
  have h₃ := matrixEntriesCLE.symm.differentiableAt.comp X (h₁.comp X h₂)
  refine h₃.congr_of_eventuallyEq (Filter.Eventually.of_forall fun Y => ?_)
  show f (fun p => Y (ρ p)) = ComplexCoordinates.matrixEquiv.symm
    (ComplexCoordinates.matrixEquiv (f (e.symm (familyEntriesCLE n' (R Y)))))
  rw [← he, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
theorem differentiableAt_extendByInverses {n : ℕ} (P : Set (Bond L m j')) (ρ : P → Fin n)
    (X : Fin n → ComplexMatrix2) (hX : ∀ p, IsUnit (X (ρ p))) (b : Bond L m j') :
    DifferentiableAt ℂ
      (fun X : Fin n → ComplexMatrix2 => extendByInverses P (fun p => X (ρ p)) b) X := by
  unfold extendByInverses
  by_cases h : b ∈ P
  · simp only [dif_pos h]
    exact differentiableAt_apply _ _
  · by_cases h' : b.opposite ∈ P
    · simp only [dif_neg h, dif_pos h']
      exact DifferentiableAt.comp (𝕜 := ℂ) X (differentiableAt_inv_of_isUnit (hX _))
        (differentiableAt_apply _ _)
    · simp only [dif_neg h, dif_neg h']
      exact differentiableAt_const _
theorem differentiableAt_pathHolonomy_extendByInverses {n : ℕ} (P : Set (Bond L m j'))
    (ρ : P → Fin n) (X : Fin n → ComplexMatrix2) (hX : ∀ p, IsUnit (X (ρ p)))
    (Γ : List (Bond L m j')) :
    DifferentiableAt ℂ
      (fun X : Fin n → ComplexMatrix2 => pathHolonomy (extendByInverses P fun p => X (ρ p)) Γ)
      X := by
  induction Γ with
  | nil => simp [pathHolonomy]
  | cons b Γ ih =>
    simp only [pathHolonomy, List.map_cons, List.prod_cons]
    exact (differentiableAt_extendByInverses P ρ X hX b).mul ih
theorem isUnit_extendByInverses (P : Set (Bond L m j')) (V : P → ComplexMatrix2)
    (hV : ∀ p, IsUnit (V p)) (b : Bond L m j') : IsUnit (extendByInverses P V b) := by
  unfold extendByInverses
  by_cases h : b ∈ P
  · simp only [dif_pos h]
    exact hV _
  · by_cases h' : b.opposite ∈ P
    · simp only [dif_neg h, dif_pos h']
      exact isUnit_inv_of_isUnit (hV _)
    · simp only [dif_neg h, dif_neg h']
      exact isUnit_one
theorem extendByInverses_mem_complexGaugeGroup (P : Set (Bond L m j')) (V : P → ComplexMatrix2)
    (hV : ∀ p, V p ∈ complexGaugeGroup) (b : Bond L m j') :
    extendByInverses P V b ∈ complexGaugeGroup := by
  unfold extendByInverses
  by_cases h : b ∈ P
  · simp only [dif_pos h]
    exact hV _
  · by_cases h' : b.opposite ∈ P
    · simp only [dif_neg h, dif_pos h']
      exact inv_mem_complexGaugeGroup (hV _)
    · simp only [dif_neg h, dif_neg h']
      show (1 : ComplexMatrix2).det = 1
      simp
theorem isUnit_pathHolonomy (U : Bond L m j' → ComplexMatrix2) (hU : ∀ b, IsUnit (U b))
    (Γ : List (Bond L m j')) : IsUnit (pathHolonomy U Γ) := by
  induction Γ with
  | nil => simp [pathHolonomy]
  | cons b Γ ih =>
    simp only [pathHolonomy, List.map_cons, List.prod_cons]
    exact (hU b).mul ih
theorem pathHolonomy_mem_complexGaugeGroup (U : Bond L m j' → ComplexMatrix2)
    (hU : ∀ b, U b ∈ complexGaugeGroup) (Γ : List (Bond L m j')) :
    pathHolonomy U Γ ∈ complexGaugeGroup := by
  induction Γ with
  | nil =>
    show (pathHolonomy U []).det = 1
    simp [pathHolonomy]
  | cons b Γ ih =>
    have h₁ : (U b).det = 1 := hU b
    have h₂ : (pathHolonomy U Γ).det = 1 := ih
    show (pathHolonomy U (b :: Γ)).det = 1
    have : pathHolonomy U (b :: Γ) = U b * pathHolonomy U Γ := by
      simp [pathHolonomy]
    rw [this, Matrix.det_mul, h₁, h₂, one_mul]
end Differentiability
section Formula
variable {L m : ℕ} {j j' : ℤ}
def axialTransport (c : Bond L m j)
    (V : positiveBondsInDoubleBlock (j' := j') c → ComplexMatrix2) : ComplexMatrix2 :=
  holonomyInDoubleBlock c V (axialPath (c.source.toSublattice j') (c.target.toSublattice j'))
def crossingMatrix (c : Bond L m j)
    (V : positiveBondsInDoubleBlock (j' := j') c → ComplexMatrix2) (x : Site L m j') :
    ComplexMatrix2 :=
  contourVariable c V c.source x * holonomyInDoubleBlock c V (crossingPath c x) *
    contourVariableInverse c V c.target (shiftAcross c x) * (axialTransport c V)⁻¹
def averageFormula (S : Finset (Site L m j')) (c : Bond L m j)
    (V : positiveBondsInDoubleBlock (j' := j') c → ComplexMatrix2) : ComplexMatrix2 :=
  ComplexMatrix2.matExp (inverseFourthPowerWeight L •
      ∑ x ∈ S, ComplexMatrix2.logSeries (crossingMatrix c V x)) *
    axialTransport c V
theorem differentiableAt_crossingMatrix
    (hP : ComplexCoordinates.PowerSeriesHolomorphy.Properties) (c : Bond L m j)
    {n n' : ℕ} (ν : positiveBondsInDoubleBlock (j' := j') c ≃ Fin n')
    (ρ : positiveBondsInDoubleBlock (j' := j') c → Fin n)
    {O : Set (positiveBondsInDoubleBlock (j' := j') c → ComplexMatrix2)} (x : Site L m j')
    (hA : ComplexCoordinates.IsHolomorphicVia (SmallRadius.doubleBlockEquiv c ν)
      ComplexCoordinates.matrixEquiv O (fun V => contourVariable c V c.source x))
    (hB : ComplexCoordinates.IsHolomorphicVia (SmallRadius.doubleBlockEquiv c ν)
      ComplexCoordinates.matrixEquiv O
      (fun V => contourVariableInverse c V c.target (shiftAcross c x)))
    (X : Fin n → ComplexMatrix2) (hX : (fun p => X (ρ p)) ∈ O) (hu : ∀ p, IsUnit (X (ρ p))) :
    DifferentiableAt ℂ
      (fun X : Fin n → ComplexMatrix2 => crossingMatrix c (fun p => X (ρ p)) x) X := by
  have hT : DifferentiableAt ℂ
      (fun X : Fin n → ComplexMatrix2 => axialTransport c (fun p => X (ρ p))) X :=
    differentiableAt_pathHolonomy_extendByInverses _ ρ X hu _
  have hH : DifferentiableAt ℂ (fun X : Fin n → ComplexMatrix2 =>
      holonomyInDoubleBlock c (fun p => X (ρ p)) (crossingPath c x)) X :=
    differentiableAt_pathHolonomy_extendByInverses _ ρ X hu _
  have hTu : IsUnit (axialTransport c (fun p => X (ρ p))) :=
    isUnit_pathHolonomy _ (isUnit_extendByInverses _ _ hu) _
  have hTi : DifferentiableAt ℂ
      (fun X : Fin n → ComplexMatrix2 => (axialTransport c (fun p => X (ρ p)))⁻¹) X :=
    DifferentiableAt.comp (𝕜 := ℂ) X (differentiableAt_inv_of_isUnit hTu) hT
  exact (((differentiableAt_comp_reindex hP c ν ρ hA X hX).mul hH).mul
    (differentiableAt_comp_reindex hP c ν ρ hB X hX)).mul hTi
theorem differentiableAt_averageFormula
    (hP : ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (S : Finset (Site L m j')) (c : Bond L m j) {n : ℕ}
    (ρ : positiveBondsInDoubleBlock (j' := j') c → Fin n) (X : Fin n → ComplexMatrix2)
    (hu : ∀ p, IsUnit (X (ρ p)))
    (hW : ∀ x ∈ S, DifferentiableAt ℂ
      (fun X : Fin n → ComplexMatrix2 => crossingMatrix c (fun p => X (ρ p)) x) X)
    (hlog : ∀ x ∈ S, crossingMatrix c (fun p => X (ρ p)) x ∈ ComplexMatrix2.logBall) :
    DifferentiableAt ℂ
      (fun X : Fin n → ComplexMatrix2 => averageFormula S c (fun p => X (ρ p))) X := by
  have hT : DifferentiableAt ℂ
      (fun X : Fin n → ComplexMatrix2 => axialTransport c (fun p => X (ρ p))) X :=
    differentiableAt_pathHolonomy_extendByInverses _ ρ X hu _
  have hsum : DifferentiableAt ℂ (fun X : Fin n → ComplexMatrix2 =>
      ∑ x ∈ S, ComplexMatrix2.logSeries (crossingMatrix c (fun p => X (ρ p)) x)) X :=
    DifferentiableAt.fun_sum fun x hx =>
      DifferentiableAt.comp (𝕜 := ℂ) (g := ComplexMatrix2.logSeries)
        (f := fun X : Fin n → ComplexMatrix2 => crossingMatrix c (fun p => X (ρ p)) x) X
        (differentiableAt_of_isHolomorphicVia_matrix hP hP.2.2.2.2.2 (hlog x hx)) (hW x hx)
  have hsmul : DifferentiableAt ℂ (fun X : Fin n → ComplexMatrix2 => inverseFourthPowerWeight L •
      ∑ x ∈ S, ComplexMatrix2.logSeries (crossingMatrix c (fun p => X (ρ p)) x)) X :=
    hsum.const_smul (inverseFourthPowerWeight L)
  have hexp : DifferentiableAt ℂ (fun X : Fin n → ComplexMatrix2 =>
      ComplexMatrix2.matExp (inverseFourthPowerWeight L •
        ∑ x ∈ S, ComplexMatrix2.logSeries (crossingMatrix c (fun p => X (ρ p)) x))) X :=
    DifferentiableAt.comp (𝕜 := ℂ) (g := ComplexMatrix2.matExp) X
      (differentiableAt_of_isHolomorphicVia_matrix hP hP.2.2.2.2.1 (mem_univ _)) hsmul
  exact hexp.mul hT
theorem averageFormula_mem_complexGaugeGroup (hE : ComplexMatrix2.ExpLogEstimates)
    (S : Finset (Site L m j')) (c : Bond L m j)
    (V : positiveBondsInDoubleBlock (j' := j') c → ComplexMatrix2)
    (hV : ∀ p, V p ∈ complexGaugeGroup)
    (hvar : ∀ x ∈ S, contourVariable c V c.source x ∈ complexGaugeGroup ∧
      contourVariableInverse c V c.target (shiftAcross c x) ∈ complexGaugeGroup)
    (hW : ∀ x ∈ S, ComplexMatrix2.operatorNorm (crossingMatrix c V x - 1) < 9 / 10) :
    averageFormula S c V ∈ complexGaugeGroup := by
  have hhol : ∀ Γ : List (Bond L m j'), (holonomyInDoubleBlock c V Γ).det = 1 := fun Γ =>
    pathHolonomy_mem_complexGaugeGroup _ (extendByInverses_mem_complexGaugeGroup _ V hV) Γ
  have hT : (axialTransport c V).det = 1 := hhol _
  have hdet : ∀ x ∈ S, (crossingMatrix c V x).det = 1 := by
    intro x hx
    have h₁ : (contourVariable c V c.source x).det = 1 := (hvar x hx).1
    have h₂ : (contourVariableInverse c V c.target (shiftAcross c x)).det = 1 := (hvar x hx).2
    have h₃ : ((axialTransport c V)⁻¹).det = 1 :=
      inv_mem_complexGaugeGroup (X := axialTransport c V) hT
    unfold crossingMatrix
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_mul, h₁, h₂, h₃, hhol]
    simp
  have htr : ComplexMatrix2.fullTrace (inverseFourthPowerWeight L •
      ∑ x ∈ S, ComplexMatrix2.logSeries (crossingMatrix c V x)) = 0 := by
    simp only [ComplexMatrix2.fullTrace, Matrix.trace_smul, Matrix.trace_sum]
    rw [Finset.sum_eq_zero, smul_zero]
    intro x hx
    exact (hE.2.2.2.2.2.2.1 _ (hdet x hx) (hW x hx).le).1
  show (averageFormula S c V).det = 1
  unfold averageFormula
  rw [Matrix.det_mul, hT, mul_one, hE.2.2.2.2.2.1, htr, Complex.exp_zero]
theorem matExp_I_smul_mem_specialUnitary (hE : ComplexMatrix2.ExpLogEstimates)
    {Y : ComplexMatrix2} (hY : Y ∈ ComplexMatrix2.hermitianTraceless) :
    ComplexMatrix2.matExp (Complex.I • Y) ∈
      (ComplexMatrix2.specialUnitary : Set ComplexMatrix2) := by
  have hstar : star (Complex.I • Y) = -(Complex.I • Y) := by
    have h : star Y = Y := hY.1.symm
    rw [star_smul, h]
    simp
  have hdet : (ComplexMatrix2.matExp (Complex.I • Y)).det = 1 := by
    rw [hE.2.2.2.2.2.1]
    have ht : ComplexMatrix2.fullTrace (Complex.I • Y) = 0 := by
      have : ComplexMatrix2.fullTrace Y = 0 := hY.2
      simp only [ComplexMatrix2.fullTrace, Matrix.trace_smul] at this ⊢
      rw [this, smul_zero]
    rw [ht, Complex.exp_zero]
  refine Matrix.mem_specialUnitaryGroup_iff.mpr ⟨?_, hdet⟩
  rw [Matrix.mem_unitaryGroup_iff]
  show ComplexMatrix2.matExp (Complex.I • Y) * star (NormedSpace.exp (Complex.I • Y)) = 1
  rw [NormedSpace.star_exp, hstar]
  show NormedSpace.exp (Complex.I • Y) * NormedSpace.exp (-(Complex.I • Y)) = 1
  rw [← Matrix.exp_add_of_commute (Complex.I • Y) (-(Complex.I • Y))
    (Commute.neg_right (Commute.refl (Complex.I • Y))), add_neg_cancel, NormedSpace.exp_zero]
end Formula
section Reindexing
theorem isRealAnalyticBetween_congr {ι κ : Type} [Fintype ι] [Fintype κ]
    {s : ι → ComplexMatrix2.FactorKind} {t : κ → ComplexMatrix2.FactorKind}
    {D : Set (ι → ComplexMatrix2)} {f g : (ι → ComplexMatrix2) → κ → ComplexMatrix2}
    (h : ComplexMatrix2.IsRealAnalyticBetween s t D f) (hfg : ∀ v ∈ D, g v = f v) :
    ComplexMatrix2.IsRealAnalyticBetween s t D g := by
  refine ⟨h.1, fun x hx => ?_⟩
  obtain ⟨W, F, hxW, hF, hev⟩ := h.2 x hx
  refine ⟨W, F, hxW, hF, ?_⟩
  filter_upwards [hev, self_mem_nhdsWithin] with y hy hyD
  rw [hfg y hyD, hy]
def reindexCLM {ι ι' : Type} (a : ι ≃ ι') : (ι → ComplexMatrix2) →L[ℂ] (ι' → ComplexMatrix2) :=
  ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (a.symm i)
theorem reindexCLM_mem_complexifiedProduct {ι ι' : Type} (a : ι ≃ ι') (v : ι → ComplexMatrix2) :
    reindexCLM a v ∈
        ComplexMatrix2.complexifiedProduct (fun _ : ι' => ComplexMatrix2.FactorKind.group) ↔
      v ∈ ComplexMatrix2.complexifiedProduct (fun _ : ι => ComplexMatrix2.FactorKind.group) := by
  constructor
  · intro h i
    simpa [reindexCLM] using h (a i)
  · intro h i
    exact h _
theorem reindexCLM_mem_compactProduct {ι ι' : Type} (a : ι ≃ ι') (v : ι → ComplexMatrix2) :
    reindexCLM a v ∈
        ComplexMatrix2.compactProduct (fun _ : ι' => ComplexMatrix2.FactorKind.group) ↔
      v ∈ ComplexMatrix2.compactProduct (fun _ : ι => ComplexMatrix2.FactorKind.group) := by
  constructor
  · intro h i
    simpa [reindexCLM] using h (a i)
  · intro h i
    exact h _
theorem isHolomorphicBetween_reindex {ι ι' κ κ' : Type} [Fintype ι] [Fintype ι'] [Fintype κ]
    [Fintype κ'] (a : ι ≃ ι') (b : κ ≃ κ') {W : Set (ι' → ComplexMatrix2)}
    {h : (ι' → ComplexMatrix2) → κ' → ComplexMatrix2}
    (hh : ComplexMatrix2.IsHolomorphicBetween (fun _ : ι' => ComplexMatrix2.FactorKind.group)
      (fun _ : κ' => ComplexMatrix2.FactorKind.group) W h) :
    ComplexMatrix2.IsHolomorphicBetween (fun _ : ι => ComplexMatrix2.FactorKind.group)
      (fun _ : κ => ComplexMatrix2.FactorKind.group)
      (reindexCLM a ⁻¹' W) (fun v i => h (reindexCLM a v) (b i)) := by
  obtain ⟨⟨O, hO, hW⟩, hmaps, hloc⟩ := hh
  refine ⟨⟨reindexCLM a ⁻¹' O, hO.preimage (reindexCLM a).continuous, ?_⟩, ?_, ?_⟩
  · rw [hW]
    ext v
    simp only [mem_preimage, mem_inter_iff, reindexCLM_mem_complexifiedProduct]
  · intro v hv i
    exact hmaps hv (b i)
  · intro x hx
    obtain ⟨F, hF, hev⟩ := hloc _ hx
    refine ⟨fun v i => F (reindexCLM a v) (b i), ?_, ?_⟩
    · have h₁ : AnalyticAt ℂ (fun v => F (reindexCLM a v)) x :=
        AnalyticAt.fun_comp hF ((reindexCLM a).analyticAt x)
      have h₂ : AnalyticAt ℂ (reindexCLM b.symm) (F (reindexCLM a x)) :=
        (reindexCLM b.symm).analyticAt _
      exact AnalyticAt.fun_comp (f := fun v => F (reindexCLM a v)) h₂ h₁
    · have ht : Filter.Tendsto (reindexCLM a) (𝓝[reindexCLM a ⁻¹' W] x)
          (𝓝[W] (reindexCLM a x)) :=
        (reindexCLM a).continuous.continuousWithinAt.tendsto_nhdsWithin (mapsTo_preimage _ _)
      filter_upwards [ht.eventually hev] with y hy
      funext i
      rw [hy]
theorem isRelativelyOpen_compactProduct_reindex {ι ι' : Type} (a : ι ≃ ι')
    {D : Set (ι' → ComplexMatrix2)}
    (hD : ComplexMatrix2.IsRelativelyOpen
      (ComplexMatrix2.compactProduct fun _ : ι' => ComplexMatrix2.FactorKind.group) D) :
    ComplexMatrix2.IsRelativelyOpen
      (ComplexMatrix2.compactProduct fun _ : ι => ComplexMatrix2.FactorKind.group)
      (reindexCLM a ⁻¹' D) := by
  obtain ⟨O, hO, rfl⟩ := hD
  refine ⟨reindexCLM a ⁻¹' O, hO.preimage (reindexCLM a).continuous, ?_⟩
  ext v
  simp only [mem_preimage, mem_inter_iff, reindexCLM_mem_compactProduct]
theorem isRealAnalyticBetween_reindex {ι ι' κ κ' : Type} [Fintype ι] [Fintype ι'] [Fintype κ]
    [Fintype κ'] (a : ι ≃ ι') (b : κ ≃ κ') {D : Set (ι' → ComplexMatrix2)}
    {f : (ι' → ComplexMatrix2) → κ' → ComplexMatrix2}
    (hf : ComplexMatrix2.IsRealAnalyticBetween (fun _ : ι' => ComplexMatrix2.FactorKind.group)
      (fun _ : κ' => ComplexMatrix2.FactorKind.group) D f) :
    ComplexMatrix2.IsRealAnalyticBetween (fun _ : ι => ComplexMatrix2.FactorKind.group)
      (fun _ : κ => ComplexMatrix2.FactorKind.group)
      (reindexCLM a ⁻¹' D) (fun v i => f (reindexCLM a v) (b i)) := by
  refine ⟨isRelativelyOpen_compactProduct_reindex a hf.1, fun x hx => ?_⟩
  obtain ⟨W, h, hxW, hh, hev⟩ := hf.2 _ hx
  refine ⟨reindexCLM a ⁻¹' W, fun v i => h (reindexCLM a v) (b i), hxW,
    isHolomorphicBetween_reindex a b hh, ?_⟩
  have ht : Filter.Tendsto (reindexCLM a) (𝓝[reindexCLM a ⁻¹' D] x) (𝓝[D] _) :=
    (reindexCLM a).continuous.continuousWithinAt.tendsto_nhdsWithin (mapsTo_preimage _ _)
  filter_upwards [ht.eventually hev] with y hy
  funext i
  rw [hy]
theorem isOpen_setOf_near_one {E ι : Type} [TopologicalSpace E] {A : Set E} (hA : IsOpen A)
    (S : Finset ι) (f : ι → E → ComplexMatrix2) (hf : ∀ x ∈ S, ContinuousOn (f x) A) :
    IsOpen {X | X ∈ A ∧ ∀ x ∈ S, ComplexMatrix2.operatorNorm (f x X - 1) < 9 / 10} := by
  have hB : IsOpen {Y : ComplexMatrix2 | ComplexMatrix2.operatorNorm (Y - 1) < 9 / 10} :=
    isOpen_lt (continuous_norm.comp (continuous_id.sub continuous_const)) continuous_const
  have hset : {X | X ∈ A ∧ ∀ x ∈ S, ComplexMatrix2.operatorNorm (f x X - 1) < 9 / 10} =
      A ∩ ⋂ x ∈ S,
        (A ∩ f x ⁻¹' {Y : ComplexMatrix2 | ComplexMatrix2.operatorNorm (Y - 1) < 9 / 10}) := by
    ext X
    simp only [mem_ofPred_eq, mem_inter_iff, mem_iInter, mem_preimage]
    exact ⟨fun h => ⟨h.1, fun x hx => ⟨h.1, h.2 x hx⟩⟩, fun h => ⟨h.1, fun x hx => (h.2 x hx).2⟩⟩
  rw [hset]
  exact hA.inter (isOpen_biInter_finset fun x hx => (hf x hx).isOpen_inter_preimage hA hB)
end Reindexing
section Lattice
variable {L m K k : ℕ}
theorem isPositivelyOriented_or_opposite {j : ℤ} (b : Bond L m j) :
    b.IsPositivelyOriented ∨ b.opposite.IsPositivelyOriented := by apply _root_.YangMills.SharedProofs.p7155 <;> assumption
theorem inv_inv_of_mem_specialUnitary {X : ComplexMatrix2}
    (hX : X ∈ (ComplexMatrix2.specialUnitary : Set ComplexMatrix2)) : X⁻¹⁻¹ = X := by
  refine Matrix.nonsing_inv_nonsing_inv X ?_
  rw [(Matrix.mem_specialUnitaryGroup_iff.mp hX).2]
  exact isUnit_one
theorem fieldOfPositiveValues_valuesOnPositiveBonds {j' : ℤ} {U : Bond L m j' → ComplexMatrix2}
    (hU : U ∈ compactGaugeFields L m j') :
    fieldOfPositiveValues (valuesOnPositiveBonds U) = U := by
  funext b
  by_cases hb : b.IsPositivelyOriented
  · exact dif_pos hb
  · have hr := (isPositivelyOriented_or_opposite b).resolve_left hb
    have h : fieldOfPositiveValues (valuesOnPositiveBonds U) b =
        (valuesOnPositiveBonds U ⟨b.opposite, hr⟩)⁻¹ := (dif_neg hb).trans (dif_pos hr)
    rw [h]
    show (U b.opposite)⁻¹ = U b
    rw [hU.2 b (mem_univ b)]
    exact inv_inv_of_mem_specialUnitary (hU.1 b (mem_univ _))
theorem finite_site_of_fintype_positivelyOrientedBond {j : ℤ}
    [Fintype (PositivelyOrientedBond L m j)] : Finite (Site L m j) := by
  refine Finite.of_injective (fun x : Site L m j =>
    (⟨Bond.forwardFrom x 0, 0, by simp [Bond.forwardFrom]⟩ : PositivelyOrientedBond L m j)) ?_
  intro a b h
  exact congrArg (fun p : PositivelyOrientedBond L m j => p.1.source) h
theorem coe_toSublattice {j j' : ℤ} (hL : 0 < L) (h : j ≤ j') (y : Site L m j) :
    ((y.toSublattice j' : Site L m j') : FourTorus L m) = y := by apply _root_.YangMills.Construction.SeparatedSequences.BlockAverages.coe_toSublattice <;> assumption
theorem toSublattice_unitStep_succ (hL : 0 < L) (ν : Fin 4) :
    (unitStep L m (levelDepth K (k + 1)) ν).toSublattice (levelDepth K k) =
      L • unitStep L m (levelDepth K k) ν := by
  apply Subtype.ext
  rw [coe_toSublattice hL (by simp only [levelDepth]; push_cast; omega)]
  have hsp : meshSize L (levelDepth K (k + 1)) = (L : ℝ) * meshSize L (levelDepth K k) := by
    have hL' : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
    simp only [meshSize, levelDepth]
    have : -((K : ℤ) - ((k + 1 : ℕ) : ℤ)) = 1 + -((K : ℤ) - (k : ℤ)) := by push_cast; ring
    rw [this, zpow_add₀ hL', zpow_one]
  ext μ
  simp only [unitStep, AddSubmonoidClass.coe_nsmul, Pi.smul_apply, pointOnAxis]
  by_cases h : μ = ν
  · subst h
    simp only [Pi.single_eq_same]
    rw [hsp, ← AddCircle.coe_nsmul, nsmul_eq_mul]
  · simp [Pi.single_eq_of_ne h]
theorem shiftAcross_eq_add (hL : 0 < L) {ν : Fin 4} (c : BondAtLevel L m K (k + 1))
    (hν : c.target - c.source = unitStep L m (levelDepth K (k + 1)) ν) (x : SiteAtLevel L m K k) :
    shiftAcross c x = x + L • unitStep L m (levelDepth K k) ν := by
  rw [shiftAcross, hν, toSublattice_unitStep_succ hL]
theorem toSublattice_mem_sitesInBlock (hL : 0 < L) (y : SiteAtLevel L m K (k + 1)) :
    y.toSublattice (levelDepth K k) ∈ sitesInBlock (levelDepth K k) y := by
  have hle : levelDepth K (k + 1) ≤ levelDepth K k := by
    simp only [levelDepth]; push_cast; omega
  have hstep : levelDepth K (k + 1) + ((1 : ℕ) : ℤ) = levelDepth K k := by
    simp only [levelDepth]; push_cast; ring
  show ((y.toSublattice (levelDepth K k) : SiteAtLevel L m K k) : FourTorus L m) ∈
    refinedBlock 1 y
  refine ⟨?_, ?_⟩
  · rw [coe_toSublattice hL hle]
    show TorusMetric.torusSupNorm (((y : FourTorus L m)) - (y : FourTorus L m)) ≤
      meshSize L _ / 2
    rw [sub_self]
    have hz : TorusMetric.torusSupNorm (0 : FourTorus L m) ≤ 0 := by
      refine csInf_le_of_le ⟨0, ?_⟩ ⟨0, ?_, ?_⟩ le_rfl
      · rintro _ ⟨u, -, rfl⟩
        exact (abs_nonneg (u 0)).trans (Finset.le_sup' (fun ν => |u ν|) (Finset.mem_univ 0))
      · funext μ
        simp [TorusMetric.torusProj]
      · simp [TorusMetric.supNormVec]
    have hs : 0 < meshSize L (levelDepth K (k + 1)) := by
      unfold meshSize
      have : (0 : ℝ) < L := by exact_mod_cast hL
      positivity
    linarith
  · rw [hstep]
    exact (y.toSublattice (levelDepth K k)).2
theorem extendByInverses_restrict {U : BondAtLevel L m K k → ComplexMatrix2}
    (hU : U ∈ compactGaugeFields L m (levelDepth K k)) (c : BondAtLevel L m K (k + 1))
    (b : BondAtLevel L m K k) (ht : (b.source : FourTorus L m) ∈ bondDoubleBlock c)
    (hh : (b.target : FourTorus L m) ∈ bondDoubleBlock c) :
    extendByInverses (positiveBondsInDoubleBlock c) (restrictToPositiveDoubleBlock c U) b =
      U b := by
  unfold extendByInverses
  by_cases h : b ∈ positiveBondsInDoubleBlock (j' := levelDepth K k) c
  · rw [dif_pos h]; rfl
  · rw [dif_neg h]
    have hb : b ∈ bondsInDoubleBlock (j' := levelDepth K k) c := ⟨ht, hh⟩
    have hnp : ¬ b.IsPositivelyOriented := fun hp => h ⟨hp, hb⟩
    have hrp := (isPositivelyOriented_or_opposite b).resolve_left hnp
    have h' : b.opposite ∈ positiveBondsInDoubleBlock (j' := levelDepth K k) c := ⟨hrp, hh, ht⟩
    rw [dif_pos h']
    show (U b.opposite)⁻¹ = U b
    rw [hU.2 b (mem_univ b)]
    exact inv_inv_of_mem_specialUnitary (hU.1 b (mem_univ _))
theorem holonomyInDoubleBlock_restrict {U : BondAtLevel L m K k → ComplexMatrix2}
    (hU : U ∈ compactGaugeFields L m (levelDepth K k)) (c : BondAtLevel L m K (k + 1))
    (Γ : List (BondAtLevel L m K k))
    (hΓ : ∀ b ∈ Γ, (b.source : FourTorus L m) ∈ bondDoubleBlock c ∧
      (b.target : FourTorus L m) ∈ bondDoubleBlock c) :
    holonomyInDoubleBlock c (restrictToPositiveDoubleBlock c U) Γ = pathHolonomy U Γ := by
  unfold holonomyInDoubleBlock pathHolonomy
  congr 1
  apply List.map_congr_left
  intro b hb
  exact extendByInverses_restrict hU c b (hΓ b hb).1 (hΓ b hb).2
theorem crossingPath_subset_bondDoubleBlock (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hm : 0 < m) (hk : k < K) (hC : DoubleBlock.DoubleBlockContoursStatement)
    (c : BondAtLevel L m K (k + 1)) (hc : c.IsPositivelyOriented) {x : SiteAtLevel L m K k}
    (hx : x ∈ sitesInBlock (levelDepth K k) c.source) :
    shiftAcross c x ∈ sitesInBlock (levelDepth K k) c.target ∧
    (∀ b ∈ crossingPath c x,
      (b.source : FourTorus L m) ∈ bondDoubleBlock c ∧
        (b.target : FourTorus L m) ∈ bondDoubleBlock c) ∧
    ∀ b ∈ axialPath (c.source.toSublattice (levelDepth K k))
        (c.target.toSublattice (levelDepth K k)),
      (b.source : FourTorus L m) ∈ bondDoubleBlock c ∧
        (b.target : FourTorus L m) ∈ bondDoubleBlock c := by
  obtain ⟨ν, hν⟩ := hc
  have hLpos : 0 < L := by have := hL.2; omega
  have hhead : c.target = c.source + unitStep L m (levelDepth K (k + 1)) ν := by
    rw [← hν]; abel
  obtain ⟨-, hsite⟩ := (hC L m K hL.1 hL.2 hm k hk c).1 c.source (Or.inl rfl)
  obtain ⟨⟨n, hn⟩, hall⟩ := hsite x hx
  obtain ⟨-, h2, -⟩ := hall n hn
  let σ : AxisOrdering c.source x := (offsetAxes c.source x).equivFin.symm
  obtain ⟨𝔞, -, hpath⟩ := h2 _ ⟨σ, rfl⟩
  have hA := (hC L m K hL.1 hL.2 hm k hk c).2 ν hhead x hx σ 𝔞 hpath
  obtain ⟨hx', -, -, -, -, -, -, -, -, -, -, hb1, hb2⟩ := hA
  have hxeq := shiftAcross_eq_add hLpos c hν x
  refine ⟨?_, ?_, hb2⟩
  · rw [hxeq]
    exact hx'
  · rw [crossingPath, hxeq]
    exact hb1
theorem crossingMatrix_restrict (hL : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m)
    (hk : k < K)
    (hC : DoubleBlock.DoubleBlockContoursStatement) {ω : ℝ} (c : BondAtLevel L m K (k + 1))
    (hc : c.IsPositivelyOriented) (hcon : SmallRadius.PropertiesAtBond ω k c)
    {U : BondAtLevel L m K k → ComplexMatrix2}
    (hU : U ∈ (smallPlaquetteFields ω c : Set (BondAtLevel L m K k → ComplexMatrix2)))
    {x : SiteAtLevel L m K k} (hx : x ∈ sitesInBlock (levelDepth K k) c.source) :
    crossingMatrix c (restrictToPositiveDoubleBlock c U) x = crossingDefect U c x := by
  obtain ⟨hx', h1, h2⟩ := crossingPath_subset_bondDoubleBlock hL hm hk hC c hc hx
  unfold crossingMatrix crossingDefect axialTransport parallelTransport
  rw [← (hcon.contourVariable_extends U hU c.source (by simp) x hx).1,
    ← (hcon.contourVariable_extends U hU c.target (by simp) _ hx').2,
    holonomyInDoubleBlock_restrict hU.1 c _ h1, holonomyInDoubleBlock_restrict hU.1 c _ h2]
theorem exp_sum_log_mul_mem_specialUnitary (hE : ComplexMatrix2.ExpLogEstimates) {ι : Type}
    (S : Finset ι) (W : ι → ComplexMatrix2)
    (hW : ∀ x ∈ S, W x ∈ (ComplexMatrix2.specialUnitary : Set ComplexMatrix2) ∧
      ComplexMatrix2.operatorNorm (W x - 1) < 1) {T : ComplexMatrix2}
    (hT : T ∈ (ComplexMatrix2.specialUnitary : Set ComplexMatrix2)) :
    ComplexMatrix2.matExp (inverseFourthPowerWeight L •
        ∑ x ∈ S, ComplexMatrix2.logSeries (W x)) * T ∈
      (ComplexMatrix2.specialUnitary : Set ComplexMatrix2) := by
  have hex : ∀ x ∈ S, ∃ Y ∈ ComplexMatrix2.hermitianTraceless,
      ComplexMatrix2.logSeries (W x) = Complex.I • Y := by
    intro x hx
    obtain ⟨H, -, -, -, -, -, h⟩ := hE.2.2.2.2.2.2.2.1 (W x)
      (Matrix.specialUnitaryGroup_le_unitaryGroup (hW x hx).1) (hW x hx).2
    exact (h (Matrix.mem_specialUnitaryGroup_iff.mp (hW x hx).1).2).2.2.1
  choose! Y hY hlog using hex
  have hsum : inverseFourthPowerWeight L • ∑ x ∈ S, ComplexMatrix2.logSeries (W x) =
      Complex.I • (((L : ℝ) ^ (-4 : ℤ) : ℝ) • ∑ x ∈ S, Y x) := by
    rw [Finset.sum_congr rfl hlog, ← Finset.smul_sum, smul_comm]
    congr 1
  rw [hsum]
  exact ComplexMatrix2.specialUnitary.mul_mem (matExp_I_smul_mem_specialUnitary hE
    (ComplexMatrix2.hermitianTraceless.smul_mem _
      (ComplexMatrix2.hermitianTraceless.sum_mem fun x hx => hY x hx))) hT
end Lattice
section Main
variable {L m K k : ℕ}
theorem averageFormula_restrict (hL : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m)
    (hk : k < K)
    (hC : DoubleBlock.DoubleBlockContoursStatement) (hE : ComplexMatrix2.ExpLogEstimates)
    {ω : ℝ} (c : BondAtLevel L m K (k + 1)) (hc : c.IsPositivelyOriented)
    (hcon : SmallRadius.PropertiesAtBond ω k c) (S : Finset (SiteAtLevel L m K k))
    (hS : ∀ x, x ∈ S ↔ x ∈ sitesInBlock (levelDepth K k) c.source)
    {U : BondAtLevel L m K k → ComplexMatrix2}
    (hU : U ∈ (smallPlaquetteFields ω c : Set (BondAtLevel L m K k → ComplexMatrix2))) :
    averageFormula S c (restrictToPositiveDoubleBlock c U) = blockAverage ω U c ∧
      averageFormula S c (restrictToPositiveDoubleBlock c U) ∈
        (ComplexMatrix2.specialUnitary : Set ComplexMatrix2) := by
  classical
  have hbound := hcon.crossingDefect_near hc U hU
  have hcase : IsRegularAveragingCase ω U c :=
    ⟨hU.2, fun x hx => (hcon.contourMean_spec U hU c.source (by simp) x hx).1,
      fun x hx => (hcon.contourMean_spec U hU c.target (by simp) x hx).1,
      fun x hx => (hbound x hx).2.trans (by norm_num)⟩
  have hfin : (sitesInBlock (levelDepth K k) c.source).Finite :=
    S.finite_toSet.subset fun x hx => (hS x).2 hx
  have hset : hfin.toFinset = S := by
    ext x
    rw [Set.Finite.mem_toFinset, hS]
  have hsum : ∑ x ∈ S, ComplexMatrix2.logSeries
        (crossingMatrix c (restrictToPositiveDoubleBlock c U) x) =
      ∑ᶠ x ∈ sitesInBlock (levelDepth K k) c.source,
        ComplexMatrix2.logSeries (crossingDefect U c x) := by
    rw [finsum_mem_eq_finite_toFinset_sum _ hfin, hset]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [crossingMatrix_restrict hL hm hk hC c hc hcon hU ((hS x).1 hx)]
  have htr : axialTransport c (restrictToPositiveDoubleBlock c U) = parallelTransport U c := by
    obtain ⟨x, hx⟩ : ∃ x, x ∈ sitesInBlock (levelDepth K k) c.source :=
      ⟨_, toSublattice_mem_sitesInBlock (by have := hL.2; omega) c.source⟩
    exact holonomyInDoubleBlock_restrict hU.1 c _
      (crossingPath_subset_bondDoubleBlock hL hm hk hC c hc hx).2.2
  have hmap : averageFormula S c (restrictToPositiveDoubleBlock c U) = blockAverage ω U c := by
    unfold averageFormula
    rw [hsum, htr]
    unfold blockAverage blockAverageOnPositive
    rw [if_pos hc, if_pos hcase]
    rfl
  refine ⟨hmap, ?_⟩
  unfold averageFormula
  rw [htr]
  have hTmem : parallelTransport U c ∈ (ComplexMatrix2.specialUnitary : Set ComplexMatrix2) := by
    refine Submonoid.list_prod_mem _ ?_
    intro X hX
    obtain ⟨b, -, rfl⟩ := List.mem_map.mp hX
    exact hU.1.1 b (mem_univ b)
  have hlogs : ∑ x ∈ S, ComplexMatrix2.logSeries
        (crossingMatrix c (restrictToPositiveDoubleBlock c U) x) =
      ∑ x ∈ S, ComplexMatrix2.logSeries (crossingDefect U c x) :=
    Finset.sum_congr rfl fun x hx => by
      rw [crossingMatrix_restrict hL hm hk hC c hc hcon hU ((hS x).1 hx)]
  rw [hlogs]
  exact exp_sum_log_mul_mem_specialUnitary hE S _ (fun x hx =>
    ⟨(hbound x ((hS x).1 hx)).1, (hbound x ((hS x).1 hx)).2.trans (by norm_num)⟩) hTmem
theorem blockAverage_isRealAnalyticBetween (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hm : 0 < m)
    (hk : k < K) (hC : DoubleBlock.DoubleBlockContoursStatement)
    (hP : ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (hH : EntrywiseHolomorphy.RestrictionStatement)
    (hE : ComplexMatrix2.ExpLogEstimates) {ω : ℝ} (c : BondAtLevel L m K (k + 1))
    (hc : c.IsPositivelyOriented) (hcon : SmallRadius.PropertiesAtBond ω k c)
    [Fintype (PositivelyOrientedBond L m (levelDepth K k))] :
    ComplexMatrix2.IsRealAnalyticBetween
      (fun _ : PositivelyOrientedBond L m (levelDepth K k) => ComplexMatrix2.FactorKind.group)
      (fun _ : Fin 1 => ComplexMatrix2.FactorKind.group)
      (valuesOnPositiveBonds ''
        (smallPlaquetteFields ω c : Set (BondAtLevel L m K k → ComplexMatrix2)))
      fun v _ => blockAverage ω (fieldOfPositiveValues v) c := by
  classical
  have hL0 : 0 < L := by have := hL.2; omega
  set D := valuesOnPositiveBonds ''
    (smallPlaquetteFields ω c : Set (BondAtLevel L m K k → ComplexMatrix2)) with hDdef
  have hSite : Finite (SiteAtLevel L m K k) := finite_site_of_fintype_positivelyOrientedBond
  let S : Finset (SiteAtLevel L m K k) :=
    (Set.toFinite (sitesInBlock (levelDepth K k) c.source)).toFinset
  have hS : ∀ x, x ∈ S ↔ x ∈ sitesInBlock (levelDepth K k) c.source := fun x =>
    Set.Finite.mem_toFinset _
  let n := Fintype.card (PositivelyOrientedBond L m (levelDepth K k))
  let μ : PositivelyOrientedBond L m (levelDepth K k) ≃ Fin n := Fintype.equivFin _
  have hn : 1 ≤ n := by
    have : Nonempty (PositivelyOrientedBond L m (levelDepth K k)) :=
      ⟨⟨Bond.forwardFrom 0 0, 0, by simp [Bond.forwardFrom]⟩⟩
    exact Fintype.card_pos
  let ρ : positiveBondsInDoubleBlock (j' := levelDepth K k) c → Fin n :=
    fun b => μ ⟨b.1, b.2.1⟩
  have hinj : Function.Injective ρ := by
    intro a b h
    have := μ.injective h
    exact Subtype.ext
      (congrArg (fun p : PositivelyOrientedBond L m (levelDepth K k) => p.1) this)
  have : Finite (positiveBondsInDoubleBlock (j' := levelDepth K k) c) :=
    Finite.of_injective ρ hinj
  obtain ⟨n', ⟨ν⟩⟩ :=
    Finite.exists_equiv_fin (positiveBondsInDoubleBlock (j' := levelDepth K k) c)
  let A : Set (Fin n → ComplexMatrix2) :=
    {X | (fun p => X (ρ p)) ∈ invertibleContourSet (j' := levelDepth K k) c}
  have hcont : Continuous fun (X : Fin n → ComplexMatrix2)
      (p : positiveBondsInDoubleBlock (j' := levelDepth K k) c) => X (ρ p) :=
    continuous_pi fun b => continuous_apply _
  have hAopen : IsOpen A := hcon.isOpen_invertibleContourSet.preimage hcont
  have hunit : ∀ X ∈ A, ∀ p, IsUnit (X (ρ p)) := fun X hX p => hX.1 p
  have hbondTail : ∀ x ∈ S, ComplexCoordinates.IsHolomorphicVia
      (SmallRadius.doubleBlockEquiv c ν) ComplexCoordinates.matrixEquiv
      (invertibleContourSet (j' := levelDepth K k) c)
      (fun V => contourVariable c V c.source x) := fun x hx =>
    (hcon.holomorphic_contourVariable c.source (by simp) x ((hS x).1 hx) n' ν).1
  have hhead : ∀ x ∈ S, shiftAcross c x ∈ sitesInBlock (levelDepth K k) c.target :=
    fun x hx => (crossingPath_subset_bondDoubleBlock hL hm hk hC c hc ((hS x).1 hx)).1
  have hbondHead : ∀ x ∈ S, ComplexCoordinates.IsHolomorphicVia
      (SmallRadius.doubleBlockEquiv c ν) ComplexCoordinates.matrixEquiv
      (invertibleContourSet (j' := levelDepth K k) c)
      (fun V => contourVariableInverse c V c.target (shiftAcross c x)) := fun x hx =>
    (hcon.holomorphic_contourVariable c.target (by simp) _ (hhead x hx) n' ν).2
  have hWd : ∀ X ∈ A, ∀ x ∈ S, DifferentiableAt ℂ
      (fun X : Fin n → ComplexMatrix2 => crossingMatrix c (fun p => X (ρ p)) x) X :=
    fun X hX x hx => differentiableAt_crossingMatrix hP c ν ρ x (hbondTail x hx)
      (hbondHead x hx) X hX (hunit X hX)
  let F : (Fin n → ComplexMatrix2) → ComplexMatrix2 :=
    fun X => averageFormula S c (fun p => X (ρ p))
  let O : Set (Fin n → ComplexMatrix2) := {X | X ∈ A ∧ ∀ x ∈ S,
    ComplexMatrix2.operatorNorm (crossingMatrix c (fun p => X (ρ p)) x - 1) < 9 / 10}
  have hOopen : IsOpen O := isOpen_setOf_near_one hAopen S
    (fun x X => crossingMatrix c (fun p => X (ρ p)) x)
    (fun x hx X hX => (hWd X hX x hx).continuousAt.continuousWithinAt)
  have hFd : ∀ X ∈ O, DifferentiableAt ℂ F X := fun X hX =>
    differentiableAt_averageFormula hP S c ρ X (hunit X hX.1) (fun x hx => hWd X hX.1 x hx)
      (fun x hx => (hX.2 x hx).trans (by norm_num))
  have hF : EntrywiseHolomorphy.IsEntrywiseHolomorphic O F := by
    have hImg : IsOpen (familyEntriesCLE n '' O) :=
      (familyEntriesCLE n).toHomeomorph.isOpenMap O hOopen
    refine isHolomorphicIn_of_differentiableAt hImg ?_
    rintro _ ⟨X, hX, rfl⟩
    have h₁ : DifferentiableAt ℂ F
        ((familyEntriesCLE n).symm (familyEntriesCLE n X)) := by
      rw [ContinuousLinearEquiv.symm_apply_apply]
      exact hFd X hX
    exact matrixEntriesCLE.differentiableAt.comp _
      (h₁.comp _ (familyEntriesCLE n).symm.differentiableAt)
  have hsl : ∀ X ∈ O ∩ EntrywiseHolomorphy.unimodularPow n,
      F X ∈ ComplexMatrix2.unitDeterminant := by
    rintro X ⟨hX, hXc⟩
    refine averageFormula_mem_complexGaugeGroup hE S c _ (fun p => hXc _) (fun x hx => ?_) hX.2
    exact ⟨((hcon.contourVariable_values c.source (by simp) x ((hS x).1 hx) _ hX.1).2.2
        fun p => hXc _).1,
      ((hcon.contourVariable_values c.target (by simp) _ (hhead x hx) _ hX.1).2.2
        fun p => hXc _).2⟩
  have hback : ∀ v, reindexCLM μ.symm (reindexCLM μ v) = v := by
    intro v
    funext b
    simp [reindexCLM]
  have hback' : ∀ X, reindexCLM μ (reindexCLM μ.symm X) = X := by
    intro X
    funext b
    simp [reindexCLM]
  have hread : ∀ U : BondAtLevel L m K k → ComplexMatrix2,
      (fun p => reindexCLM μ (valuesOnPositiveBonds U) (ρ p)) =
        restrictToPositiveDoubleBlock c U := by
    intro U
    funext b
    simp [reindexCLM, ρ, valuesOnPositiveBonds, restrictToPositiveDoubleBlock]
  have hset : reindexCLM μ ⁻¹' (reindexCLM μ.symm ⁻¹' D) = D := by
    ext v
    simp only [mem_preimage, hback]
  have hDopen : ComplexMatrix2.IsRelativelyOpen (EntrywiseHolomorphy.unitaryPow n)
      (reindexCLM μ.symm ⁻¹' D) :=
    isRelativelyOpen_compactProduct_reindex μ.symm
      (hcon.realAnalytic_contourMean inferInstance c.source (by simp) _
        (toSublattice_mem_sitesInBlock hL0 c.source)).1.1
  have hsub : reindexCLM μ.symm ⁻¹' D ⊆ O ∩ EntrywiseHolomorphy.unitaryPow n := by
    intro X hX
    obtain ⟨U, hU, hUX⟩ := hX
    have hXU : X = reindexCLM μ (valuesOnPositiveBonds U) := by rw [hUX, hback']
    refine ⟨⟨?_, fun x hx => ?_⟩, ?_⟩
    · show (fun p => X (ρ p)) ∈ invertibleContourSet (j' := levelDepth K k) c
      rw [hXU, hread]
      exact hcon.image_restrict_subset ⟨U, hU, rfl⟩
    · show ComplexMatrix2.operatorNorm (crossingMatrix c (fun p => X (ρ p)) x - 1) < 9 / 10
      rw [hXU, hread, crossingMatrix_restrict hL hm hk hC c hc hcon hU ((hS x).1 hx)]
      exact (hcon.crossingDefect_near hc U hU x ((hS x).1 hx)).2.trans (by norm_num)
    · intro i
      rw [hXU]
      exact hU.1.1 _ (mem_univ _)
  have hin : ∀ X ∈ reindexCLM μ.symm ⁻¹' D,
      F X ∈ (ComplexMatrix2.specialUnitary : Set ComplexMatrix2) := by
    intro X hX
    obtain ⟨U, hU, hUX⟩ := hX
    have hXU : X = reindexCLM μ (valuesOnPositiveBonds U) := by rw [hUX, hback']
    show averageFormula S c (fun p => X (ρ p)) ∈ _
    rw [hXU, hread]
    exact (averageFormula_restrict hL hm hk hC hE c hc hcon S hS hU).2
  have main := (hH n hn O hOopen F hF hsl).2 _ hsub hDopen hin
  have hre := isRealAnalyticBetween_reindex μ (Equiv.ofUnique (Fin 1) Unit) main
  rw [hset] at hre
  refine isRealAnalyticBetween_congr hre ?_
  rintro _ ⟨U, hU, rfl⟩
  funext _
  show blockAverage ω (fieldOfPositiveValues (valuesOnPositiveBonds U)) c =
    averageFormula S c (fun p => reindexCLM μ (valuesOnPositiveBonds U) (ρ p))
  rw [fieldOfPositiveValues_valuesOnPositiveBonds hU.1, hread]
  exact (averageFormula_restrict hL hm hk hC hE c hc hcon S hS hU).1.symm
end Main
theorem blockAverageRealAnalyticOnSmallFields_holds (hR : SmallRadius.EverySmallRadiusSuffices)
    (hC : DoubleBlock.DoubleBlockContoursStatement)
    (hP : ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (hH : EntrywiseHolomorphy.RestrictionStatement)
    (hE : ComplexMatrix2.ExpLogEstimates) : BlockAverageRealAnalyticOnSmallFields := by
  intro s ω hω k hk c hc _
  exact blockAverage_isRealAnalyticBetween s.isAdmissible s.m.pos hk hC hP hH hE c hc
    (hR s ω hω k hk c)
end YangMills.Construction.Averaging.SmallFieldAnalyticity
end
