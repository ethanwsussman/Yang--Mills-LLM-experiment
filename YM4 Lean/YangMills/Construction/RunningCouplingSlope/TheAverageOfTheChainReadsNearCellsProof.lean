import YangMills.Construction.RunningCouplingSlope.CellsOfABlockAreNearProof
import YangMills.Construction.RunningCouplingSlope.CoordinateFamiliesAreClosed
import YangMills.Construction.RunningCouplingSlope.PlainIteratesOfAFieldOnTheWholeProof
import YangMills.Construction.RunningCouplingSlope.TheAverageOfTheChainReadsNearCells
import YangMills.Construction.RunningCouplingSlope.TheKernelOfTheHessianOfTheWholeChainDecaysProof
import YangMills.Construction.RunningCouplingSlope.TheOtherConstraintReadsNearCellsProof
import YangMills.Construction.Towers.TheActionAndCurrentTermsOfTheKernelAreLocalProof
import YangMills.Construction.Towers.WhatTheMapsOfOneStepOfATowerRead
import Mathlib
set_option autoImplicit false
open Filter Metric
open scoped Topology Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope.ComposedAverageLocality
open Tower TorusMetric Matrices
section RowColumnBound
variable {a b : Type} [Fintype a] [Fintype b] [DecidableEq b]
private theorem opNorm_le_sqrt_of_row_col_sums (A : Matrix a b ℂ) {R S : ℝ} (hR : 0 ≤ R) (hS : 0 ≤ S)
    (hrow : ∀ p, ∑ q, ‖A p q‖ ≤ R) (hcol : ∀ q, ∑ p, ‖A p q‖ ≤ S) :
    ‖A‖ ≤ Real.sqrt (R * S) := by apply _root_.YangMills.SharedProofs.p34885 <;> assumption
private theorem sum_le_card_mul_of_le_ite {α : Type} [Fintype α] {P : α → Prop} [DecidablePred P]
    {c : ℝ} {N : ℕ} (hc : 0 ≤ c) (hN : (Finset.univ.filter P).card ≤ N) {f : α → ℝ}
    (hf : ∀ x, f x ≤ if P x then c else 0) : ∑ x, f x ≤ N * c := by
  calc ∑ x, f x ≤ ∑ x, (if P x then c else 0) := Finset.sum_le_sum fun x _ => hf x
    _ = ((Finset.univ.filter P).card : ℝ) * c := by
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    _ ≤ N * c := mul_le_mul_of_nonneg_right (by exact_mod_cast hN) hc
end RowColumnBound
section PauliCoeffs
private def pauliCoeffForm (a : Fin 3) : ComplexMatrix2 →ₗ[ℂ] ℂ where
  toFun X := (1 / 2 : ℂ) * Matrix.trace (ComplexMatrix2.pauliFamily a * X)
  map_add' X Y := by rw [mul_add, Matrix.trace_add, mul_add]
  map_smul' c X := by
    simp only [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, RingHom.id_apply]
    ring
private def pauliCoeffCLM (a : Fin 3) : ComplexMatrix2 →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap (pauliCoeffForm a)
private theorem pauliCoeffForm_sum_smul (a : Fin 3) (u : Fin 3 → ℂ) :
    pauliCoeffForm a (∑ γ, u γ • ComplexMatrix2.pauliFamily γ) = u a := by
  show (1 / 2 : ℂ) * Matrix.trace (ComplexMatrix2.pauliFamily a * ∑ γ, u γ • ComplexMatrix2.pauliFamily γ) = u a
  rw [ComplexMatrix2.sum_smul_pauliFamily]
  obtain ⟨h0, h1, h2⟩ := ComplexMatrix2.pauliFamily_apply
  fin_cases a
  · show (1 / 2 : ℂ) * Matrix.trace (ComplexMatrix2.pauliFamily 0 * _) = u 0
    rw [h0]
    simp [Matrix.trace, Fin.sum_univ_two, Matrix.mul_apply]
    ring
  · show (1 / 2 : ℂ) * Matrix.trace (ComplexMatrix2.pauliFamily 1 * _) = u 1
    rw [h1]
    simp [Matrix.trace, Fin.sum_univ_two, Matrix.mul_apply]
    ring_nf
    simp only [Complex.I_sq]
    ring
  · show (1 / 2 : ℂ) * Matrix.trace (ComplexMatrix2.pauliFamily 2 * _) = u 2
    rw [h2]
    simp [Matrix.trace, Fin.sum_univ_two, Matrix.mul_apply]
    ring
private theorem sum_pauliCoeff_smul {X : ComplexMatrix2} (h : X ∈ ComplexMatrix2.traceless) :
    ∑ a, pauliCoeff a X • ComplexMatrix2.pauliFamily a = X := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.sum_pauliCoeff_smul <;> assumption
private theorem pauliCoeff_eq_clm {X : ComplexMatrix2} (h : X ∈ ComplexMatrix2.traceless) (a : Fin 3) :
    pauliCoeff a X = pauliCoeffCLM a X := by
  have e := pauliCoeffForm_sum_smul a fun a => pauliCoeff a X
  rw [sum_pauliCoeff_smul h] at e
  exact e.symm
private theorem pauliFamily_mem_traceless (a : Fin 3) :
    ComplexMatrix2.pauliFamily a ∈ ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.OneLoopLaw.PlaneWaveSymmetries.pauliFamily_mem_traceless <;> assumption
private theorem sum_smul_pauliFamily_mem (u : Fin 3 → ℂ) :
    ∑ γ, u γ • ComplexMatrix2.pauliFamily γ ∈ ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.Tower.ThreeMapKernels.sum_smul_pauli_mem <;> assumption
private theorem pauliCoeff_sum_smul (a : Fin 3) (u : Fin 3 → ℂ) :
    pauliCoeff a (∑ γ, u γ • ComplexMatrix2.pauliFamily γ) = u a := by
  rw [pauliCoeff_eq_clm (sum_smul_pauliFamily_mem u)]
  exact pauliCoeffForm_sum_smul a u
abbrev _root_.YangMills.DeltaSharedProofs.p502539 := @pauliCoeff_sum_smul
private theorem conjugateBy_mem_traceless (g : ComplexMatrix2) {X : ComplexMatrix2}
    (h : X ∈ ComplexMatrix2.traceless) : ComplexMatrix2.conjugateBy g X ∈ ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.PeriodicLattice.conjugateBy_mem_traceless <;> assumption
private theorem conjugateBy_sum_smul (g : ComplexMatrix2) (u : Fin 3 → ℂ) :
    ComplexMatrix2.conjugateBy g (∑ b, u b • ComplexMatrix2.pauliFamily b) =
      ∑ b, u b • ComplexMatrix2.conjugateBy g (ComplexMatrix2.pauliFamily b) := by apply _root_.YangMills.Construction.Tower.FullSpace.KernelTermsLocality.conjugateBy_sum_smul <;> assumption
private def pauliComponentBound : ℝ :=
  (∑ a, ‖pauliCoeffCLM a‖) * (3 * ∑ b, ComplexMatrix2.operatorNorm (ComplexMatrix2.pauliFamily b))
private theorem pauliComponentBound_nonneg : 0 ≤ pauliComponentBound :=
  mul_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _)
    (mul_nonneg (by norm_num) (Finset.sum_nonneg fun _ _ => norm_nonneg _))
private theorem pauliCoeff_image_le {T : ComplexMatrix2 → ComplexMatrix2}
    (hT : StepKernels.IsBoundedTracelessEndo T 3) (a b : Fin 3) :
    ‖pauliCoeff a (T (ComplexMatrix2.pauliFamily b))‖ ≤ pauliComponentBound := by
  rw [pauliCoeff_eq_clm (hT.mapsTo _ (pauliFamily_mem_traceless b))]
  refine ((pauliCoeffCLM a).le_opNorm _).trans ?_
  have h1 : ‖pauliCoeffCLM a‖ ≤ ∑ a, ‖pauliCoeffCLM a‖ :=
    Finset.single_le_sum (f := fun a => ‖pauliCoeffCLM a‖) (fun _ _ => norm_nonneg _)
      (Finset.mem_univ a)
  have h2 : ComplexMatrix2.operatorNorm (ComplexMatrix2.pauliFamily b) ≤
      ∑ b, ComplexMatrix2.operatorNorm (ComplexMatrix2.pauliFamily b) :=
    Finset.single_le_sum (f := fun b => ComplexMatrix2.operatorNorm (ComplexMatrix2.pauliFamily b))
      (fun _ _ => norm_nonneg _) (Finset.mem_univ b)
  have h3 : ‖T (ComplexMatrix2.pauliFamily b)‖ ≤
      3 * ∑ b, ComplexMatrix2.operatorNorm (ComplexMatrix2.pauliFamily b) :=
    (hT.norm_le _ (pauliFamily_mem_traceless b)).trans (by linarith)
  exact mul_le_mul h1 h3 (norm_nonneg _) (Finset.sum_nonneg fun _ _ => norm_nonneg _)
end PauliCoeffs
section LevelStep
variable {L n k j : ℕ}
private def levelStepMatrix (V : Edge L n k j → ComplexMatrix2) :
    Matrix (Fin 3 × Vertex L n k (j + 1)) (Fin 3 × Vertex L n k j) ℂ :=
  open Classical in fun p q =>
    if q.2 ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) p.2 then
      PeriodicLattice.inverseFourthPowerWeight L * pauliCoeff p.1
        (ComplexMatrix2.conjugateBy (PeriodicLattice.complexMeanContourHolonomy V p.2 q.2)
          (ComplexMatrix2.pauliFamily q.1))
    else 0
private theorem finsum_block_eq_sum_ite [Fintype (Vertex L n k j)] (y : Vertex L n k (j + 1))
    (f : Vertex L n k j → ComplexMatrix2) :
    ∑ᶠ x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y, f x =
      ∑ x, open Classical in
        if x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y then f x else 0 := by
  classical
  rw [finsum_mem_def, finsum_eq_sum_of_fintype]
  exact Finset.sum_congr rfl fun x _ => Set.indicator_apply _ _ _
private theorem levelStep_mulVec [Fintype (Vertex L n k j)] (V : Edge L n k j → ComplexMatrix2)
    {l : Vertex L n k j → ComplexMatrix2} (hl : ∀ x, l x ∈ ComplexMatrix2.traceless) :
    (∀ y, adjointCubeAverage V l y ∈ ComplexMatrix2.traceless) ∧
      ∀ p, toPauliCoeffs (adjointCubeAverage V l) p =
        (levelStepMatrix V).mulVec (toPauliCoeffs l) p := by
  classical
  have mem : ∀ y, adjointCubeAverage V l y ∈ ComplexMatrix2.traceless := fun y => by
    unfold adjointCubeAverage
    rw [finsum_block_eq_sum_ite]
    refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun x _ => ?_)
    split_ifs
    · exact conjugateBy_mem_traceless _ (hl x)
    · exact Submodule.zero_mem _
  refine ⟨mem, fun p => ?_⟩
  obtain ⟨a, y⟩ := p
  show pauliCoeff a (adjointCubeAverage V l y) =
    ∑ q, levelStepMatrix V (a, y) q * toPauliCoeffs l q
  rw [pauliCoeff_eq_clm (mem y), Fintype.sum_prod_type_right]
  unfold adjointCubeAverage
  rw [finsum_block_eq_sum_ite, map_smul, map_sum, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases hx : x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y
  · simp only [levelStepMatrix, if_pos hx]
    have e : ComplexMatrix2.conjugateBy (PeriodicLattice.complexMeanContourHolonomy V y x) (l x) =
        ∑ b, pauliCoeff b (l x) •
          ComplexMatrix2.conjugateBy (PeriodicLattice.complexMeanContourHolonomy V y x)
            (ComplexMatrix2.pauliFamily b) := by
      rw [← conjugateBy_sum_smul, sum_pauliCoeff_smul (hl x)]
    rw [e, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [map_smul, smul_eq_mul, pauliCoeff_eq_clm (conjugateBy_mem_traceless _ (pauliFamily_mem_traceless b))]
    simp only [toPauliCoeffs]
    ring
  · simp [levelStepMatrix, hx]
end LevelStep
section Composition
variable {L n k : ℕ} [∀ j, Fintype (Vertex L n k j)] [∀ j, DecidableEq (Fin 3 × Vertex L n k j)]
private def composedMatrix (X : ChainPoint L n k) :
    (j : ℕ) → Matrix (Fin 3 × Vertex L n k j) (Fin 3 × Vertex L n k 0) ℂ
  | 0 => 1
  | j + 1 => levelStepMatrix (levelField X j) * composedMatrix X j
private theorem composed_mulVec (X : ChainPoint L n k) {l : Vertex L n k 0 → ComplexMatrix2}
    (hl : ∀ x, l x ∈ ComplexMatrix2.traceless) (j : ℕ) :
    (∀ y, composedCubeAverage X j l y ∈ ComplexMatrix2.traceless) ∧
      toPauliCoeffs (composedCubeAverage X j l) = (composedMatrix X j).mulVec (toPauliCoeffs l) := by
  induction j with
  | zero =>
    refine ⟨hl, ?_⟩
    show toPauliCoeffs l = (1 : Matrix _ _ ℂ).mulVec (toPauliCoeffs l)
    rw [Matrix.one_mulVec]
  | succ j ih =>
    obtain ⟨h₁, h₂⟩ := ih
    obtain ⟨h₃, h₄⟩ := levelStep_mulVec (levelField X j) h₁
    refine ⟨h₃, funext fun p => ?_⟩
    show toPauliCoeffs (adjointCubeAverage (levelField X j) (composedCubeAverage X j l)) p =
      (levelStepMatrix (levelField X j) * composedMatrix X j).mulVec (toPauliCoeffs l) p
    rw [h₄ p, h₂, Matrix.mulVec_mulVec]
private theorem composedAverageMatrix_eq (z : TripleCoordIndex L n k → ℂ) :
    composedAverageMatrix z = composedMatrix (complexChainPoint z) k := by
  classical
  ext p q
  have hl : ∀ x, ofPauliCoeffs (UnitGaugeDirections.basisFunction q) x ∈ ComplexMatrix2.traceless :=
    fun x => sum_smul_pauliFamily_mem _
  have h := congrFun (composed_mulVec (complexChainPoint z) hl k).2 p
  have e : toPauliCoeffs (ofPauliCoeffs (UnitGaugeDirections.basisFunction q)) =
      UnitGaugeDirections.basisFunction q :=
    funext fun ι => pauliCoeff_sum_smul ι.1 _
  show toPauliCoeffs (composedCubeAverage (complexChainPoint z) k
    (ofPauliCoeffs (UnitGaugeDirections.basisFunction q))) p = _
  rw [h, e]
  simp [Matrix.mulVec, dotProduct, UnitGaugeDirections.basisFunction]
end Composition
section CellGeometry
variable {L n k : ℕ}
private theorem meshSize_levelDepth_le_one (hL : 1 ≤ (L : ℝ)) {j : ℕ} (hj : j ≤ k) :
    PeriodicLattice.meshSize L (PeriodicLattice.levelDepth k j) ≤ 1 := by
  simp only [PeriodicLattice.meshSize, PeriodicLattice.levelDepth]
  exact zpow_le_one_of_nonpos₀ hL (by omega)
private theorem cellDist_le_of_near (hC : NeighbouringFineVertexCells)
    (hL : Conventions.IsAdmissibleBlockingFactor L) {j j' : ℕ} (x : Vertex L n k j)
    (x' : Vertex L n k j') {t : ℝ} (ht : 0 ≤ t)
    (h : ∀ μ, ‖((x : PeriodicLattice.FourTorus L n) - (x' : PeriodicLattice.FourTorus L n)) μ‖ ≤ t) :
    cellDist (levelVertexCell x) (levelVertexCell x') ≤ 2 * (t + 1) := by apply _root_.YangMills.SharedProofs.p26872 <;> assumption
private theorem cellDist_block_le (hC : NeighbouringFineVertexCells)
    (hL : Conventions.IsAdmissibleBlockingFactor L) {j j' : ℕ} (hj : j < k)
    (y : Vertex L n k (j + 1)) (x : Vertex L n k j')
    (hx : (x : PeriodicLattice.FourTorus L n) ∈ PeriodicLattice.unitBlock y) :
    cellDist (levelVertexCell x) (levelVertexCell y) ≤ 3 := by
  have hL1 : (1 : ℝ) ≤ L := by
    have := hL.2
    exact_mod_cast (by omega : 1 ≤ L)
  have hη := meshSize_levelDepth_le_one (k := k) hL1 (Nat.succ_le_of_lt hj)
  have key : ∀ μ, ‖((x : PeriodicLattice.FourTorus L n) - (y : PeriodicLattice.FourTorus L n)) μ‖ ≤
      1 / 2 := by
    intro μ
    have h := hx.1
    change torusSupNorm _ ≤ _ at h
    rw [SeparatedSequence.torusSupNorm_le_iff] at h
    have := h μ
    linarith
  have := cellDist_le_of_near hC hL x y (t := 1 / 2) (by norm_num) key
  linarith
end CellGeometry
section Holonomies
variable {L n k j : ℕ}
private theorem analyticAt_matrix_inv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : E → ComplexMatrix2} {x : E} (hf : AnalyticAt ℂ f x) (hu : IsUnit (Matrix.det (f x))) :
    AnalyticAt ℂ (fun y => (f y)⁻¹) x := by apply _root_.YangMills.SharedProofs.p7089 <;> assumption
private theorem positive_or_opposite_positive (b : Edge L n k j) :
    b.IsPositivelyOriented ∨ b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.Tower.TrivialFieldAverages.edge_positive_or_opposite <;> assumption
private theorem extend_restrict_eq {ℬ : Set (Edge L n k j)} {V : Edge L n k j → ComplexMatrix2}
    (hV : PeriodicLattice.IsGaugeField PeriodicLattice.complexGaugeGroup ℬ V) {b : Edge L n k j}
    (hb : b ∈ ℬ) (hr : b.opposite ∈ ℬ) :
    PeriodicLattice.extendFromPositive ℬ (PeriodicLattice.restrictToPositive ℬ V) b = V b := by
  have hrr : b.opposite.opposite = b := PeriodicLattice.Bond.ext rfl rfl
  unfold PeriodicLattice.extendFromPositive
  by_cases h : b.IsPositivelyOriented
  · rw [dif_pos ⟨hb, h⟩]
    rfl
  · have h' := (positive_or_opposite_positive b).resolve_left h
    rw [dif_neg fun t => h t.2, dif_pos ⟨hr, h'⟩]
    show (V b.opposite)⁻¹ = V b
    have e := hV.2 b.opposite hr
    rw [hrr] at e
    exact e.symm
private theorem analyticAt_holonomy {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {W : E → Edge L n k j → ComplexMatrix2} {z₀ : E} {ρ : ℝ} {c : Edge L n k (j + 1)}
    {x : Vertex L n k j}
    (hserve : PolydiscIsAdmissible ρ c)
    (hx : x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) c.source)
    (hread : Tower.UnitScale.OneStep.DependsOnlyOn Set.univ
      (Tower.OneStep.blockInnerEdges c.source) fun V : Edge L n k j → ComplexMatrix2 =>
        PeriodicLattice.complexMeanContourHolonomy V c.source x)
    (han : ∀ b, AnalyticAt ℂ (fun z => W z b) z₀)
    (hin : ∀ᶠ z in 𝓝 z₀, W z ∈ nearIdentityPolydisc ρ c) :
    AnalyticAt ℂ (fun z => PeriodicLattice.complexMeanContourHolonomy (W z) c.source x) z₀ := by
  obtain ⟨inst, -, -, hloc⟩ := (hserve.holomorphic_contourMean c.source (Or.inl rfl) x hx).1
  let v : E → PeriodicLattice.PositiveBondOf
      (PeriodicLattice.bondsInDoubleBlock c : Set (Edge L n k j)) → ComplexMatrix2 :=
    fun z => PeriodicLattice.restrictToPositive _ (W z)
  have hv : AnalyticAt ℂ v z₀ := analyticAt_pi_iff.2 fun b => han b.1
  obtain ⟨F, hFa, hFe⟩ := hloc (v z₀) ⟨W z₀, hin.self_of_nhds, rfl⟩
  have hF0 : AnalyticAt ℂ (fun w => F w ()) (v z₀) := analyticAt_pi_iff.1 hFa ()
  have hcomp : AnalyticAt ℂ (fun z => F (v z) ()) z₀ := AnalyticAt.comp hF0 hv
  refine hcomp.congr ?_
  have tend : Tendsto v (𝓝 z₀)
      (𝓝[PeriodicLattice.restrictToPositive
        (PeriodicLattice.bondsInDoubleBlock c : Set (Edge L n k j)) ''
        nearIdentityPolydisc ρ c] (v z₀)) :=
    tendsto_nhdsWithin_iff.2 ⟨hv.continuousAt.tendsto, hin.mono fun z hz => ⟨W z, hz, rfl⟩⟩
  filter_upwards [tend.eventually hFe, hin] with z h₁ h₂
  have e := congrFun h₁ ()
  rw [← e]
  refine hread _ (Set.mem_univ _) _ (Set.mem_univ _) fun b hb => ?_
  have hbℬ : b ∈ (PeriodicLattice.bondsInDoubleBlock c : Set (Edge L n k j)) :=
    ⟨Or.inl hb.1, Or.inl hb.2⟩
  have hrℬ : b.opposite ∈ (PeriodicLattice.bondsInDoubleBlock c : Set (Edge L n k j)) :=
    ⟨Or.inl hb.2, Or.inl hb.1⟩
  exact extend_restrict_eq h₂.1 hbℬ hrℬ
end Holonomies
section StepLocality
variable {L n k : ℕ}
private def levelStepBound (L : ℕ) : ℝ :=
  Real.sqrt ((3 * (L : ℝ) ^ 4 * (‖PeriodicLattice.inverseFourthPowerWeight L‖ * pauliComponentBound)) *
    (3 * (‖PeriodicLattice.inverseFourthPowerWeight L‖ * pauliComponentBound)))
private theorem levelStepBound_nonneg (L : ℕ) : 0 ≤ levelStepBound L := Real.sqrt_nonneg _
private theorem card_block_le (hB : BlockStructure) (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hn : 0 < n) {j : ℕ} (hj : j < k) [Fintype (Vertex L n k j)] (y : Vertex L n k (j + 1))
    [DecidablePred fun x : Vertex L n k j =>
      x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y] :
    (Finset.univ.filter fun x : Vertex L n k j =>
      x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y).card ≤ L ^ 4 := by
  classical
  have hb := ((hB L k (j + 1) hL (by omega) (by omega) hj).1 n hn).1 y
  have hcard : (PeriodicLattice.unitBlock y).ncard = L ^ 4 := hb.2.2.1
  have hL0 : 0 < L := by
    have := hL.2
    omega
  have hfin : (PeriodicLattice.unitBlock y).Finite :=
    Set.finite_of_ncard_pos (by rw [hcard]; positivity)
  set S := Finset.univ.filter fun x : Vertex L n k j =>
    x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y with hS
  have e : (S.image fun x : Vertex L n k j => (x : PeriodicLattice.FourTorus L n)).card = S.card :=
    Finset.card_image_of_injective _ Subtype.val_injective
  rw [← e, ← hcard, ← Set.ncard_coe_finset]
  refine Set.ncard_le_ncard (fun p hp => ?_) hfin
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hp)
  exact (Finset.mem_filter.1 hx).2
private theorem card_blocks_containing_le_one (hB : BlockStructure)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) {j : ℕ} (hj : j < k)
    [Fintype (Vertex L n k (j + 1))] (x : Vertex L n k j)
    [DecidablePred fun y : Vertex L n k (j + 1) =>
      x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y] :
    (Finset.univ.filter fun y : Vertex L n k (j + 1) =>
      x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y).card ≤ 1 := by
  have h := ((hB L k (j + 1) hL (by omega) (by omega) hj).1 n hn).2.1.2.1 x
  refine Finset.card_le_one.2 fun a ha b hb => h.unique (Finset.mem_filter.1 ha).2
    (Finset.mem_filter.1 hb).2
variable [∀ j, Fintype (Vertex L n k j)] [∀ j, DecidableEq (Fin 3 × Vertex L n k j)]
  [Fintype (TripleCoordIndex L n k)]
private theorem levelStep_isLocallyHolomorphic (hS : StepKernels.StepKernelBounds)
    (hW : StepMapsLocalityStatement) (hC : NeighbouringFineVertexCells)
    (hB : BlockStructure)
    (hP : IsAdmissiblePolydiscRadius L (polydiscRadius L))
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) {j : ℕ} (hj : j < k) {ρ r : ℝ}
    (hr : 0 ≤ r)
    {W : (TripleCoordIndex L n k → ℂ) → Edge L n k j → ComplexMatrix2}
    (hconf : ∀ z ∈ ball (0 : TripleCoordIndex L n k → ℂ) ρ,
      W z ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup)
    (han : ∀ b, AnalyticOnNhd ℂ (fun z => W z b) (ball 0 ρ))
    (hnear : ∀ z ∈ ball (0 : TripleCoordIndex L n k → ℂ) ρ, ∀ b,
      ComplexMatrix2.operatorNorm (W z b - 1) < 3 / 4 * polydiscRadius L)
    (hreads : ∀ b : Edge L n k j, ∀ z ∈ ball (0 : TripleCoordIndex L n k → ℂ) ρ,
      ∀ z' ∈ ball (0 : TripleCoordIndex L n k → ℂ) ρ,
      (∀ i, cellDist (tripleCoordIndexCell i) (levelVertexCell b.source) ≤ r → z i = z' i) →
        W z b = W z' b) :
    IsLocallyHolomorphicFamily tripleCoordIndexCell
      (fun p : Fin 3 × Vertex L n k j => levelVertexCell p.2)
      (fun p : Fin 3 × Vertex L n k (j + 1) => levelVertexCell p.2)
      (fun z => levelStepMatrix (W z)) ρ (levelStepBound L) (r + 3) := by
  classical
  have hρ := hP.pos
  have edgeOf : ∀ y : Vertex L n k (j + 1), ∃ c : Edge L n k (j + 1),
      c.source = y ∧ c.IsPositivelyOriented :=
    fun y => ⟨PeriodicLattice.Bond.forwardFrom y 0, rfl, ⟨0, add_sub_cancel_left _ _⟩⟩
  have inPoly : ∀ z ∈ ball (0 : TripleCoordIndex L n k → ℂ) ρ, ∀ c : Edge L n k (j + 1),
      W z ∈ nearIdentityPolydisc (polydiscRadius L) c := fun z hz c =>
    ⟨⟨fun b _ => (hconf z hz).1 b (Set.mem_univ _), fun b _ => (hconf z hz).2 b (Set.mem_univ _)⟩,
      fun b _ => (hnear z hz b).trans (by linarith)⟩
  have entry : ∀ z ∈ ball (0 : TripleCoordIndex L n k → ℂ) ρ, ∀ (a b : Fin 3)
      (y : Vertex L n k (j + 1)) (x : Vertex L n k j),
      x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y →
      ‖pauliCoeff a (ComplexMatrix2.conjugateBy (PeriodicLattice.complexMeanContourHolonomy (W z) y x)
        (ComplexMatrix2.pauliFamily b))‖ ≤ pauliComponentBound := by
    intro z hz a b y x hx
    obtain ⟨c, rfl, hc⟩ := edgeOf y
    exact pauliCoeff_image_le ((hS L hL n k j hn hj c hc (W z) (hconf z hz) (hnear z hz)).2.2
      c.source (Or.inl rfl) x hx) a b
  have hw : 0 ≤ ‖PeriodicLattice.inverseFourthPowerWeight L‖ * pauliComponentBound :=
    mul_nonneg (norm_nonneg _) pauliComponentBound_nonneg
  have normEntry : ∀ z ∈ ball (0 : TripleCoordIndex L n k → ℂ) ρ, ∀ (a b : Fin 3)
      (y : Vertex L n k (j + 1)) (x : Vertex L n k j),
      ‖levelStepMatrix (W z) (a, y) (b, x)‖ ≤
        if x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y then
          ‖PeriodicLattice.inverseFourthPowerWeight L‖ * pauliComponentBound else 0 := by
    intro z hz a b y x
    by_cases hx : x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y
    · simp only [levelStepMatrix, if_pos hx, norm_mul]
      exact mul_le_mul_of_nonneg_left (entry z hz a b y x hx) (norm_nonneg _)
    · simp [levelStepMatrix, hx]
  refine ⟨fun p q z₀ hz₀ => ?_, fun z hz => ?_, fun p q z hz z' hz' h => ?_, fun z hz p q hlt => ?_⟩
  · obtain ⟨a, y⟩ := p
    obtain ⟨b, x⟩ := q
    by_cases hx : x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y
    · obtain ⟨c, rfl, hc⟩ := edgeOf y
      have hserve := hP.periodic n k j hn hj c hc
      have hin : ∀ᶠ z in 𝓝 z₀, z ∈ ball (0 : TripleCoordIndex L n k → ℂ) ρ :=
        isOpen_ball.mem_nhds hz₀
      have hg : AnalyticAt ℂ
          (fun z => PeriodicLattice.complexMeanContourHolonomy (W z) c.source x) z₀ :=
        analyticAt_holonomy hserve hx
          ((((hW L k j hL hj).1 n hn).atVertex c.source).holonomy x hx)
          (fun b => han b z₀ hz₀) (hin.mono fun z hz => inPoly z hz c)
      have hsm := hserve.contourMean_near_one (W z₀) (inPoly z₀ hz₀ c) c.source (Or.inl rfl) x hx
      have hu : IsUnit (PeriodicLattice.complexMeanContourHolonomy (W z₀) c.source x) := by
        refine ⟨Units.oneSub (1 - PeriodicLattice.complexMeanContourHolonomy (W z₀) c.source x) ?_, ?_⟩
        · rw [norm_sub_rev]
          exact hsm.trans (by norm_num)
        · simp
      have hgi := analyticAt_matrix_inv hg ((Matrix.isUnit_iff_isUnit_det _).1 hu)
      have e : (fun z => levelStepMatrix (W z) (a, c.source) (b, x)) = fun z =>
          PeriodicLattice.inverseFourthPowerWeight L * pauliCoeffCLM a
            (PeriodicLattice.complexMeanContourHolonomy (W z) c.source x * ComplexMatrix2.pauliFamily b *
              (PeriodicLattice.complexMeanContourHolonomy (W z) c.source x)⁻¹) := funext fun z => by
        simp only [levelStepMatrix, if_pos hx]
        rw [pauliCoeff_eq_clm (conjugateBy_mem_traceless _ (pauliFamily_mem_traceless b))]
        rfl
      show AnalyticAt ℂ (fun z => levelStepMatrix (W z) (a, c.source) (b, x)) z₀
      rw [e]
      exact analyticAt_const.mul
        (AnalyticAt.comp ((pauliCoeffCLM a).analyticAt _) ((hg.mul analyticAt_const).mul hgi))
    · simp only [levelStepMatrix, if_neg hx]
      exact analyticAt_const
  · refine (opNorm_le_sqrt_of_row_col_sums (levelStepMatrix (W z)) (R := 3 * (L : ℝ) ^ 4 *
      (‖PeriodicLattice.inverseFourthPowerWeight L‖ * pauliComponentBound))
      (S := 3 * (‖PeriodicLattice.inverseFourthPowerWeight L‖ * pauliComponentBound))
      (by positivity) (by positivity) (fun p => ?_) fun q => ?_)
    · obtain ⟨a, y⟩ := p
      rw [Fintype.sum_prod_type_right]
      have h := sum_le_card_mul_of_le_ite (P := fun x : Vertex L n k j =>
        x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y)
        (c := 3 * (‖PeriodicLattice.inverseFourthPowerWeight L‖ * pauliComponentBound)) (N := L ^ 4)
        (by positivity) (card_block_le hB hL hn hj y)
        (f := fun x => ∑ b, ‖levelStepMatrix (W z) (a, y) (b, x)‖) ?_
      · push_cast at h
        linarith
      · intro x
        have h₁ : ∀ b, ‖levelStepMatrix (W z) (a, y) (b, x)‖ ≤ _ := fun b => normEntry z hz a b y x
        refine (Finset.sum_le_sum fun b _ => h₁ b).trans ?_
        by_cases hx : x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y <;> simp [hx]
    · obtain ⟨b, x⟩ := q
      rw [Fintype.sum_prod_type_right]
      have h := sum_le_card_mul_of_le_ite (P := fun y : Vertex L n k (j + 1) =>
        x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y)
        (c := 3 * (‖PeriodicLattice.inverseFourthPowerWeight L‖ * pauliComponentBound)) (N := 1)
        (by positivity) (card_blocks_containing_le_one hB hL hn hj x)
        (f := fun y => ∑ a, ‖levelStepMatrix (W z) (a, y) (b, x)‖) ?_
      · push_cast at h
        linarith
      · intro y
        have h₁ : ∀ a, ‖levelStepMatrix (W z) (a, y) (b, x)‖ ≤ _ := fun a => normEntry z hz a b y x
        refine (Finset.sum_le_sum fun a _ => h₁ a).trans ?_
        by_cases hx : x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y <;> simp [hx]
  · obtain ⟨a, y⟩ := p
    obtain ⟨b, x⟩ := q
    by_cases hx : x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y
    · have e : PeriodicLattice.complexMeanContourHolonomy (W z) y x =
          PeriodicLattice.complexMeanContourHolonomy (W z') y x := by
        refine (((hW L k j hL hj).1 n hn).atVertex y).holonomy x hx _ (Set.mem_univ _) _
          (Set.mem_univ _) fun b hb => hreads b z hz z' hz' fun i hi => h i ?_
        have h₁ := cellDist_block_le hC hL hj y b.source hb.1
        exact ((hC L hL n k).2.1 _ _ _).trans (by linarith)
      simp only [levelStepMatrix, if_pos hx, e]
    · simp only [levelStepMatrix, if_neg hx]
  · obtain ⟨a, y⟩ := p
    obtain ⟨b, x⟩ := q
    have hx : x ∉ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y := fun hx => by
      have h₁ := cellDist_block_le hC hL hj y x hx
      have h₂ := (hC L hL n k).1 (levelVertexCell y) (levelVertexCell x)
      have h₃ : r + 3 < cellDist (levelVertexCell y) (levelVertexCell x) := hlt
      linarith
    simp only [levelStepMatrix, if_neg hx]
private theorem composed_isLocallyHolomorphic (K : LocallyHolomorphicFamiliesClosedOn L n k) {ρ r : ℝ}
    (hr : 0 ≤ r) (hB : 0 ≤ levelStepBound L)
    (H : ∀ j < k, IsLocallyHolomorphicFamily tripleCoordIndexCell
      (fun p : Fin 3 × Vertex L n k j => levelVertexCell p.2)
      (fun p : Fin 3 × Vertex L n k (j + 1) => levelVertexCell p.2)
      (fun z => levelStepMatrix (levelField (complexChainPoint z) j)) ρ (levelStepBound L) r)
    (j : ℕ) (hj : j ≤ k) :
    IsLocallyHolomorphicFamily tripleCoordIndexCell
      (fun p : Fin 3 × Vertex L n k 0 => levelVertexCell p.2)
      (fun p : Fin 3 × Vertex L n k j => levelVertexCell p.2)
      (fun z => composedMatrix (complexChainPoint z) j) ρ (levelStepBound L ^ j) (j * r) := by
  induction j with
  | zero =>
    have h := K.one (I := TripleCoordIndex L n k) tripleCoordIndexCell
      (fun p : Fin 3 × Vertex L n k 0 => levelVertexCell p.2) ρ 0 le_rfl
    exact K.mono le_rfl (by simp) (by simp) h
  | succ j ih =>
    have h := K.mul hr (mul_nonneg (Nat.cast_nonneg j) hr) (H j (by omega)) (ih (by omega))
    exact K.mono le_rfl (le_of_eq (by rw [pow_succ]; ring)) (le_of_eq (by push_cast; ring)) h
end StepLocality
section Coordinates
variable {L n k : ℕ}
private theorem nonempty_pauliCoordinates (hC : PauliCoordsOrthonormal)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n)
    [Fintype (Fin 3 × PositiveEdge L n k 0)]
    [∀ i : Fin k, Fintype (Fin 3 × PositiveEdge L n k (i + 1))]
    [Fintype (Fin 3 × PositiveEdge L n k k)] [Fintype (Fin 3 × Vertex L n k 0)]
    [Fintype (Fin 3 × Vertex L n k k)] : Nonempty (PauliCoordinates L n k) := by apply _root_.YangMills.SharedProofs.p4012 <;> assumption
end Coordinates
theorem composedAverageIsLocallyHolomorphic_holds (hcl : LocallyHolomorphicFamiliesClosed)
    (hF : LevelFieldsHolomorphicAndLocal)
    (hA : SmoothingNearIdentity)
    (hS : StepKernels.StepKernelBounds)
    (hW : StepMapsLocalityStatement)
    (hC : NeighbouringFineVertexCells)
    (hB : BlockStructure)
    (hY : PauliCoordsOrthonormal) :
    ComposedAverageIsLocallyHolomorphic := by
  classical
  intro L hL k hk
  obtain ⟨ρ₄, C₄, r₄, p₄, c₄, s₄, H⟩ := hF L hL k hk
  have hP := (hA.1 L hL).2.2
  have hρL : 0 < polydiscRadius L := hP.pos
  have hC₁ : 0 < C₄ + 1 := by linarith
  have ht : 0 < 3 / 4 * polydiscRadius L / (C₄ + 1) := by positivity
  refine ⟨min ρ₄ (3 / 4 * polydiscRadius L / (C₄ + 1)), levelStepBound L ^ k,
    (k : ℝ) * (r₄ + 3), lt_min p₄ ht, pow_nonneg (levelStepBound_nonneg L) k, by positivity, ?_⟩
  filter_upwards [H, eventually_gt_atTop 0] with n a hn
  intro iW iB iS dS iT
  haveI : NeZero L := ⟨by have := hL.2; omega⟩
  letI fs : ∀ j, Fintype (Vertex L n k j) := fun j => Fintype.ofFinite _
  letI ds : ∀ j, DecidableEq (Fin 3 × Vertex L n k j) := fun _ => Classical.decEq _
  letI f₀ : Fintype (Fin 3 × PositiveEdge L n k 0) := Fintype.ofFinite _
  letI f₁ : ∀ i : Fin k, Fintype (Fin 3 × PositiveEdge L n k (i + 1)) :=
    fun _ => Fintype.ofFinite _
  obtain rfl : iW = instFintypeSum _ _ := Subsingleton.elim _ _
  obtain rfl : iS = instFintypeProd _ _ := Subsingleton.elim _ _
  obtain rfl : iT = instFintypeProd _ _ := Subsingleton.elim _ _
  obtain rfl : dS = ds 0 := Subsingleton.elim _ _
  obtain ⟨P⟩ := nonempty_pauliCoordinates (k := k) hY hL hn
  obtain ⟨-, hc, hb, -⟩ := a P
  have hsub : ball (0 : TripleCoordIndex L n k → ℂ) (min ρ₄ (3 / 4 * polydiscRadius L / (C₄ + 1))) ⊆
      ball 0 ρ₄ := ball_subset_ball (min_le_left _ _)
  have step : ∀ j < k, IsLocallyHolomorphicFamily tripleCoordIndexCell
      (fun p : Fin 3 × Vertex L n k j => levelVertexCell p.2)
      (fun p : Fin 3 × Vertex L n k (j + 1) => levelVertexCell p.2)
      (fun z => levelStepMatrix (levelField (complexChainPoint z) j))
      (min ρ₄ (3 / 4 * polydiscRadius L / (C₄ + 1))) (levelStepBound L) (r₄ + 3) := by
    intro j hj
    refine levelStep_isLocallyHolomorphic hS hW hC hB hP hL hn hj s₄
      (fun z hz => hc j hj.le z (hsub hz))
      (fun b => (hb j hj.le b).1.mono hsub) (fun z hz b => ?_)
      (fun b z hz z' hz' h => (hb j hj.le b).2.2 z (hsub hz) z' (hsub hz') h)
    have h₁ := (hb j hj.le b).2.1 z (hsub hz)
    have h₂ : ‖z‖ < 3 / 4 * polydiscRadius L / (C₄ + 1) :=
      (mem_ball_zero_iff.1 hz).trans_le (min_le_right _ _)
    have h₃ : (C₄ + 1) * ‖z‖ < 3 / 4 * polydiscRadius L := by
      rwa [lt_div_iff₀ hC₁, mul_comm] at h₂
    nlinarith [norm_nonneg z]
  have e : (composedAverageMatrix (L := L) (n := n) (k := k)) =
      fun z => composedMatrix (complexChainPoint z) k := funext composedAverageMatrix_eq
  rw [e]
  exact composed_isLocallyHolomorphic (hcl L n k) (by linarith) (levelStepBound_nonneg L) step k le_rfl
end YangMills.Construction.RunningCouplingSlope.ComposedAverageLocality
end
