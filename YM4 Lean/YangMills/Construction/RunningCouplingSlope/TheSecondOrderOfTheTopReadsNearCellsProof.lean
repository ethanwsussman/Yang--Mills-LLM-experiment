import YangMills.Construction.RunningCouplingSlope.TheHessianOfTheSoftActionReadsNearCellsProof
import YangMills.Construction.RunningCouplingSlope.TheSecondOrderOfTheTopReadsNearCells
import YangMills.Construction.SourcesOnAFlow.BoundedMapsHolomorphicAlongLinesAreAnalytic
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YangMills.Construction
open Filter Metric
open YangMills.Construction.Tower YangMills.Construction.RunningCouplingSlope YangMills.Construction.Matrices
open scoped Topology Matrix.Norms.L2Operator ComplexConjugate
namespace RunningCouplingSlope
namespace TopSecondVariationLocal
section SecondDerivative
variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
private def secondDeriv (g : E → F) (x u v : E) : F := fderiv ℂ (fderiv ℂ g) x u v
private lemma analyticOnNhd_secondDeriv [CompleteSpace E] [CompleteSpace F] {g : E → F} {s : Set E}
    (hg : AnalyticOnNhd ℂ g s) (u v : E) : AnalyticOnNhd ℂ (fun x => secondDeriv g x u v) s := by
  intro x hx
  have h2 : AnalyticAt ℂ (fderiv ℂ (fderiv ℂ g)) x := hg.fderiv.fderiv x hx
  have e : (fun x => secondDeriv g x u v) =
      ((ContinuousLinearMap.apply ℂ F v).comp
        (ContinuousLinearMap.apply ℂ (E →L[ℂ] F) u)) ∘ fderiv ℂ (fderiv ℂ g) := by
    funext y
    simp [secondDeriv]
  rw [e]
  exact ContinuousLinearMap.analyticAt _ _ |>.comp h2
private lemma hasDerivAt_line (y v : E) :
    HasDerivAt (fun t : ℝ => y + (t : ℂ) • v) v 0 := by apply _root_.YangMills.SharedProofs.p26497 <;> assumption
private lemma hasDerivAt_comp_line {g : E → F} {y v : E}
    (hg : DifferentiableAt ℂ g y) :
    HasDerivAt (fun t : ℝ => g (y + (t : ℂ) • v)) (fderiv ℂ g y v) 0 := by
  have h1 : HasFDerivAt g ((fderiv ℂ g y).restrictScalars ℝ) (y + ((0 : ℝ) : ℂ) • v) := by
    simpa using hg.hasFDerivAt.restrictScalars ℝ
  exact h1.comp_hasDerivAt (0 : ℝ) (hasDerivAt_line y v)
private lemma eventually_hasDerivAt_inner [CompleteSpace F] {g : E → F} {x u v : E}
    (hg : AnalyticAt ℂ g x) :
    ∀ᶠ s : ℝ in 𝓝 0, HasDerivAt (fun t : ℝ => g (x + (s : ℂ) • u + (t : ℂ) • v))
      (fderiv ℂ g (x + (s : ℂ) • u) v) 0 := by
  have ht : Tendsto (fun s : ℝ => x + (s : ℂ) • u) (𝓝 0) (𝓝 x) := by
    have := (hasDerivAt_line x u).continuousAt.tendsto
    simpa using this
  filter_upwards [ht.eventually hg.eventually_analyticAt] with s hs
  exact hasDerivAt_comp_line hs.differentiableAt
private lemma hasDerivAt_outer [CompleteSpace E] [CompleteSpace F] {g : E → F} {x u v : E}
    (hg : AnalyticAt ℂ g x) :
    HasDerivAt (fun s : ℝ => fderiv ℂ g (x + (s : ℂ) • u) v) (secondDeriv g x u v) 0 := by
  have h1 : AnalyticAt ℂ (fderiv ℂ g) x := hg.fderiv
  have h2 := hasDerivAt_comp_line (v := u) h1.differentiableAt
  have h3 := ((ContinuousLinearMap.apply ℂ F v).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt
    (0 : ℝ) h2
  exact h3
private lemma deriv_deriv_line_eq [CompleteSpace E] [CompleteSpace F] {g : E → F} {x u v : E}
    (hg : AnalyticAt ℂ g x) :
    deriv (fun s : ℝ => deriv (fun t : ℝ => g (x + (s : ℂ) • u + (t : ℂ) • v)) 0) 0 =
      secondDeriv g x u v := by
  have h : (fun s : ℝ => deriv (fun t : ℝ => g (x + (s : ℂ) • u + (t : ℂ) • v)) 0) =ᶠ[𝓝 0]
      fun s : ℝ => fderiv ℂ g (x + (s : ℂ) • u) v := by
    filter_upwards [eventually_hasDerivAt_inner (u := u) (v := v) hg] with s hs
    exact hs.deriv
  rw [h.deriv_eq]
  exact (hasDerivAt_outer hg).deriv
private lemma secondDeriv_congr [CompleteSpace E] [CompleteSpace F] {g g' : E → F}
    {x x' u v u' v' : E} (hg : AnalyticAt ℂ g x)
    (hg' : AnalyticAt ℂ g' x')
    (h : ∀ᶠ p : ℝ × ℝ in 𝓝 0, g (x + (p.1 : ℂ) • u + (p.2 : ℂ) • v) =
      g' (x' + (p.1 : ℂ) • u' + (p.2 : ℂ) • v')) :
    secondDeriv g x u v = secondDeriv g' x' u' v' := by
  rw [← deriv_deriv_line_eq hg, ← deriv_deriv_line_eq hg']
  have h0 : ∀ᶠ p : ℝ × ℝ in 𝓝 ((0 : ℝ), (0 : ℝ)), g (x + (p.1 : ℂ) • u + (p.2 : ℂ) • v) =
      g' (x' + (p.1 : ℂ) • u' + (p.2 : ℂ) • v') := h
  rw [nhds_prod_eq] at h0
  have h1 := h0.curry
  have h2 : (fun s : ℝ => deriv (fun t : ℝ => g (x + (s : ℂ) • u + (t : ℂ) • v)) 0) =ᶠ[𝓝 0]
      fun s : ℝ => deriv (fun t : ℝ => g' (x' + (s : ℂ) • u' + (t : ℂ) • v')) 0 := by
    filter_upwards [h1] with s hs
    exact Filter.EventuallyEq.deriv_eq hs
  exact h2.deriv_eq
private lemma secondDeriv_zero_left (g : E → F) (x v : E) : secondDeriv g x 0 v = 0 := by
  simp [secondDeriv]
private lemma secondDeriv_zero_right (g : E → F) (x u : E) : secondDeriv g x u 0 = 0 := by
  simp [secondDeriv]
private lemma norm_fderiv_apply_le_div [CompleteSpace F] {g : E → F} {x v : E} {R M r : ℝ}
    (hg : DifferentiableOn ℂ g (ball x R)) (hM : ∀ y ∈ ball x R, ‖g y‖ ≤ M) (hv : ‖v‖ ≤ 1)
    (hr : 0 < r) (hrR : r < R) : ‖fderiv ℂ g x v‖ ≤ M / r := by
  have hmaps : ∀ t : ℂ, t ∈ closedBall (0 : ℂ) r → x + t • v ∈ ball x R := by
    intro t ht
    have ht' : ‖t‖ ≤ r := by simpa using ht
    rw [mem_ball, dist_eq_norm]
    have : x + t • v - x = t • v := by abel
    rw [this, norm_smul]
    calc ‖t‖ * ‖v‖ ≤ r * 1 := mul_le_mul ht' hv (norm_nonneg _) hr.le
      _ < R := by linarith
  have hφ : DifferentiableOn ℂ (fun t : ℂ => g (x + t • v)) (closedBall 0 r) := by
    intro t ht
    have h1 : DifferentiableAt ℂ (fun t : ℂ => x + t • v) t := by fun_prop
    have h2 : DifferentiableAt ℂ g (x + t • v) :=
      (hg _ (hmaps t ht)).differentiableAt (isOpen_ball.mem_nhds (hmaps t ht))
    exact (h2.comp t h1).differentiableWithinAt
  have hc := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr (hφ.diffContOnCl_ball subset_rfl)
    (C := M) (fun t ht => hM _ (hmaps t (sphere_subset_closedBall ht)))
  have hx : DifferentiableAt ℂ g x :=
    (hg x (mem_ball_self (hr.trans hrR))).differentiableAt
      (isOpen_ball.mem_nhds (mem_ball_self (hr.trans hrR)))
  have hd : HasDerivAt (fun t : ℂ => g (x + t • v)) (fderiv ℂ g x v) 0 := by
    have h1 : HasDerivAt (fun t : ℂ => x + t • v) v 0 := by
      simpa using ((hasDerivAt_id (0 : ℂ)).smul_const v).const_add x
    have h2 : HasFDerivAt g (fderiv ℂ g x) (x + (0 : ℂ) • v) := by simpa using hx.hasFDerivAt
    exact h2.comp_hasDerivAt (0 : ℂ) h1
  rwa [hd.deriv] at hc
private lemma norm_secondDeriv_le [CompleteSpace E] [CompleteSpace F] {g : E → F} {x u v : E}
    {R M : ℝ} (hR : 0 < R)
    (hg : AnalyticOnNhd ℂ g (ball x R)) (hM : ∀ y ∈ ball x R, ‖g y‖ ≤ M)
    (hu : ‖u‖ ≤ 1) (hv : ‖v‖ ≤ 1) : ‖secondDeriv g x u v‖ ≤ 16 * M / R ^ 2 := by
  have hdg : DifferentiableOn ℂ g (ball x R) := hg.differentiableOn
  have hsub : ∀ y ∈ ball x (R / 2), ball y (R / 2) ⊆ ball x R := by
    intro y hy
    refine (ball_subset_ball' ?_)
    have : dist y x < R / 2 := hy
    linarith
  have h1 : ∀ y ∈ ball x (R / 2), ‖fderiv ℂ g y v‖ ≤ M / (R / 4) := by
    intro y hy
    exact norm_fderiv_apply_le_div (R := R / 2) (hdg.mono (hsub y hy))
      (fun w hw => hM w (hsub y hy hw)) hv (by positivity) (by linarith)
  have hx : x ∈ ball x R := mem_ball_self hR
  have hd1 : DifferentiableOn ℂ (fun y => fderiv ℂ g y v) (ball x (R / 2)) := by
    intro y hy
    have hy' : y ∈ ball x R := ball_subset_ball (by linarith) hy
    have h2 : AnalyticAt ℂ (fderiv ℂ g) y := (hg y hy').fderiv
    exact (h2.differentiableAt.clm_apply (differentiableAt_const v)).differentiableWithinAt
  have h3 := norm_fderiv_apply_le_div (R := R / 2) (r := R / 4) (x := x) (v := u) hd1 h1 hu
    (by positivity) (by linarith)
  have h4 : fderiv ℂ (fun y => fderiv ℂ g y v) x u = secondDeriv g x u v := by
    have h2 : AnalyticAt ℂ (fderiv ℂ g) x := (hg x hx).fderiv
    have := ((ContinuousLinearMap.apply ℂ F v).hasFDerivAt.comp x
      h2.differentiableAt.hasFDerivAt).fderiv
    have e : (fun y => fderiv ℂ g y v) = (ContinuousLinearMap.apply ℂ F v) ∘ fderiv ℂ g := rfl
    rw [e, this]
    simp [secondDeriv]
  rw [h4] at h3
  refine h3.trans (le_of_eq ?_)
  field_simp
  ring
end SecondDerivative
section SchurTest
variable {m : Type} [Fintype m] [DecidableEq m]
private lemma opNorm_le_of_schur (A : Matrix m m ℂ) {K : ℝ} (hK : 0 ≤ K)
    (hr : ∀ p, ∑ q, ‖A p q‖ ≤ K) (hc : ∀ q, ∑ p, ‖A p q‖ ≤ K) : ‖A‖ ≤ K := by apply _root_.YangMills.SharedProofs.p42812 <;> assumption
end SchurTest
private def pauliCoord (a : Fin 3) : ComplexMatrix2 →ₗ[ℂ] ℂ where
  toFun X := ![(X 0 1 + X 1 0) / 2, (X 1 0 - X 0 1) / (2 * Complex.I), X 0 0] a
  map_add' X Y := by fin_cases a <;> simp <;> ring
  map_smul' c X := by fin_cases a <;> simp <;> ring
private def pauliCoordL (a : Fin 3) : ComplexMatrix2 →L[ℂ] ℂ := (pauliCoord a).toContinuousLinearMap
private lemma diag_sum_eq_zero {X : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.traceless) :
    X 0 0 + X 1 1 = 0 := by
  have h : Matrix.trace X = 0 := hX
  simpa [Matrix.trace_fin_two] using h
private lemma sum_pauliCoordL_smul {X : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.traceless) :
    ∑ a, pauliCoordL a X • ComplexMatrix2.pauliFamily a = X := by
  have h := diag_sum_eq_zero hX
  have e : ∑ a, pauliCoordL a X • ComplexMatrix2.pauliFamily a =
      !![pauliCoordL 2 X, pauliCoordL 0 X - Complex.I * pauliCoordL 1 X;
        pauliCoordL 0 X + Complex.I * pauliCoordL 1 X, -pauliCoordL 2 X] :=
    ComplexMatrix2.sum_smul_pauliFamily fun a => pauliCoordL a X
  rw [e]
  have hI : Complex.I ≠ 0 := Complex.I_ne_zero
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauliCoordL, pauliCoord] <;> (try field_simp) <;>
    first | ring1 | linear_combination (-1 : ℂ) * h
private lemma pauliCoeff_eq_pauliCoordL {X : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.traceless)
    (a : Fin 3) : pauliCoeff a X = pauliCoordL a X := by
  simp only [pauliCoeff, dif_pos hX]
  fin_cases a <;> rfl
private lemma pauliFamily_mem (a : Fin 3) : ComplexMatrix2.pauliFamily a ∈ ComplexMatrix2.traceless := by apply _root_.YangMills.Construction.OneLoopLaw.PlaneWaveSymmetries.pauliFamily_mem_traceless <;> assumption
private def expProd (A B : ComplexMatrix2) : ComplexMatrix2 :=
  ComplexMatrix2.matExp (Complex.I • A) * ComplexMatrix2.matExp (Complex.I • B)
private def expProdLog (A B : ComplexMatrix2) : ComplexMatrix2 :=
  Complex.I⁻¹ • ComplexMatrix2.logSeries (expProd A B)
private lemma analyticAt_const_smul' {F : Type} [NormedAddCommGroup F] [NormedSpace ℂ F] (c : ℂ)
    {f : F → ComplexMatrix2} {x : F} (hf : AnalyticAt ℂ f x) : AnalyticAt ℂ (fun q => c • f q) x :=
  AnalyticAt.comp (g := c • ContinuousLinearMap.id ℂ ComplexMatrix2) (f := f)
    (ContinuousLinearMap.analyticAt _ _) hf
private lemma analyticAt_expProd (p : ComplexMatrix2 × ComplexMatrix2) :
    AnalyticAt ℂ (fun q : ComplexMatrix2 × ComplexMatrix2 => expProd q.1 q.2) p := by apply _root_.YangMills.DeltaSharedProofs.p501919 <;> assumption
private lemma analyticAt_expProdLog (hS : PeriodicLattice.LogSeriesNearOne)
    {p : ComplexMatrix2 × ComplexMatrix2} (hp : ‖expProd p.1 p.2 - 1‖ < 1) :
    AnalyticAt ℂ (fun q : ComplexMatrix2 × ComplexMatrix2 => expProdLog q.1 q.2) p := by apply _root_.YangMills.DeltaSharedProofs.p502181 <;> assumption
private lemma expProdLog_spec (hS : PeriodicLattice.LogSeriesNearOne)
    (hE : ComplexMatrix2.ExpLogEstimates) {A B : ComplexMatrix2} (hA : A ∈ ComplexMatrix2.traceless)
    (hB : B ∈ ComplexMatrix2.traceless) (h : ‖expProd A B - 1‖ < 9 / 10) :
    expProdLog A B ∈ ComplexMatrix2.traceless ∧
      ComplexMatrix2.matExp (Complex.I • expProdLog A B) = expProd A B := by apply _root_.YangMills.DeltaSharedProofs.p502490 <;> assumption
private lemma exists_small_expProdLog (hS : PeriodicLattice.LogSeriesNearOne) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ A B : ComplexMatrix2, ‖A‖ < δ → ‖B‖ < δ →
      ‖expProd A B - 1‖ < 9 / 10 ∧ ∀ a, ‖pauliCoordL a (expProdLog A B)‖ < ρ := by
  have h0 : expProd 0 0 = 1 := by simp [expProd]
  have hc : ContinuousAt (fun q : ComplexMatrix2 × ComplexMatrix2 => expProd q.1 q.2) 0 :=
    (analyticAt_expProd 0).continuousAt
  have h1 : ∀ᶠ q : ComplexMatrix2 × ComplexMatrix2 in 𝓝 0, ‖expProd q.1 q.2 - 1‖ < 9 / 10 := by
    have : Tendsto (fun q : ComplexMatrix2 × ComplexMatrix2 => ‖expProd q.1 q.2 - 1‖)
        (𝓝 0) (𝓝 0) := by
      have h := (hc.tendsto.sub_const 1).norm
      simpa [h0] using h
    exact this.eventually (gt_mem_nhds (by norm_num))
  have hj0 : expProdLog 0 0 = 0 := by
    simp [expProdLog, h0, hS.2.1]
  have hja : AnalyticAt ℂ (fun q : ComplexMatrix2 × ComplexMatrix2 => expProdLog q.1 q.2) 0 :=
    analyticAt_expProdLog hS (by simp [h0])
  have h2 : ∀ a, ∀ᶠ q : ComplexMatrix2 × ComplexMatrix2 in 𝓝 0,
      ‖pauliCoordL a (expProdLog q.1 q.2)‖ < ρ := by
    intro a
    have hc' : ContinuousAt (fun q : ComplexMatrix2 × ComplexMatrix2 =>
        pauliCoordL a (expProdLog q.1 q.2)) 0 :=
      (pauliCoordL a).continuous.continuousAt.comp hja.continuousAt
    have : Tendsto (fun q : ComplexMatrix2 × ComplexMatrix2 =>
        ‖pauliCoordL a (expProdLog q.1 q.2)‖) (𝓝 0) (𝓝 0) := by
      have h := hc'.tendsto.norm
      simpa [hj0] using h
    exact this.eventually (gt_mem_nhds hρ)
  have h3 : ∀ᶠ q : ComplexMatrix2 × ComplexMatrix2 in 𝓝 0, ‖expProd q.1 q.2 - 1‖ < 9 / 10 ∧
      ∀ a, ‖pauliCoordL a (expProdLog q.1 q.2)‖ < ρ := h1.and (eventually_all.2 h2)
  obtain ⟨δ, hδ, hb⟩ := Metric.eventually_nhds_iff_ball.1 h3
  refine ⟨δ, hδ, fun A B hA hB => hb (A, B) ?_⟩
  rw [mem_ball_zero_iff, Prod.norm_def]
  exact max_lt hA hB
section MovedCoordinates
variable {L n k : ℕ}
private def colourIndex : LevelFormIndex L n k → Fin 3
  | .inl p => p.1
  | .inr p => p.2.1
private def withColour (a : Fin 3) : LevelFormIndex L n k → LevelFormIndex L n k
  | .inl p => .inl (a, p.2)
  | .inr p => .inr ⟨p.1, (a, p.2.2)⟩
@[simp] private lemma withColour_withColour (a b : Fin 3) (p : LevelFormIndex L n k) :
    withColour a (withColour b p) = withColour a p := by
  rcases p with p | p <;> rfl
@[simp] private lemma colourIndex_withColour (a : Fin 3) (p : LevelFormIndex L n k) :
    colourIndex (withColour a p) = a := by
  rcases p with p | p <;> rfl
private lemma cell_withColour (a : Fin 3) (p : LevelFormIndex L n k) :
    levelFormIndexCell (withColour a p) = levelFormIndexCell p := by
  rcases p with p | p <;> rfl
private def edgeMatrix (f : LevelFormIndex L n k → ℂ) (p : LevelFormIndex L n k) : ComplexMatrix2 :=
  ∑ a, f (withColour a p) • ComplexMatrix2.pauliFamily a
private lemma edgeMatrix_mem (f : LevelFormIndex L n k → ℂ) (p : LevelFormIndex L n k) :
    edgeMatrix f p ∈ ComplexMatrix2.traceless :=
  ComplexMatrix2.traceless.sum_mem fun a _ =>
    ComplexMatrix2.traceless.smul_mem _ (pauliFamily_mem a)
private def formPart (z : TripleCoordIndex L n k → ℂ) : LevelFormIndex L n k → ℂ :=
  fun q => z (.inl q)
private def movedCoords (z : TripleCoordIndex L n k → ℂ) (ε : LevelFormIndex L n k → ℂ) :
    TripleCoordIndex L n k → ℂ :=
  Sum.elim (fun p => pauliCoordL (colourIndex p) (expProdLog (edgeMatrix ε p) (edgeMatrix (formPart z) p)))
    fun r => z (.inr r)
private lemma edgeMatrix_movedCoords (hS : PeriodicLattice.LogSeriesNearOne)
    (hE : ComplexMatrix2.ExpLogEstimates) {z : TripleCoordIndex L n k → ℂ}
    {ε : LevelFormIndex L n k → ℂ} (p : LevelFormIndex L n k)
    (h : ‖expProd (edgeMatrix ε p) (edgeMatrix (formPart z) p) - 1‖ < 9 / 10) :
    edgeMatrix (formPart (movedCoords z ε)) p =
      expProdLog (edgeMatrix ε p) (edgeMatrix (formPart z) p) := by
  have hj := (expProdLog_spec hS hE (edgeMatrix_mem ε p) (edgeMatrix_mem _ p) h).1
  rw [← sum_pauliCoordL_smul hj]
  simp [edgeMatrix, formPart, movedCoords]
private lemma complexFineValues_eq (z : TripleCoordIndex L n k → ℂ) (b : PositiveEdge L n k 0) :
    complexFineValues z b.1 = edgeMatrix (formPart z) (.inl (0, b)) := by
  simp only [complexFineValues, edgeFormOfPositiveValues, dif_pos b.2]
  rfl
private lemma complexLevelValues_eq (z : TripleCoordIndex L n k → ℂ) (i : Fin k)
    (c : PositiveEdge L n k (i + 1)) :
    complexLevelValues z i c = edgeMatrix (formPart z) (.inr ⟨i, (0, c)⟩) := rfl
private lemma opposite_isPositive {j : ℕ} (b : Edge L n k j) (hb : ¬ b.IsPositivelyOriented) :
    b.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.Tower.IteratedMeans.opposite_isPositivelyOriented_of_not <;> assumption
private lemma expMove_complexChainPoint (hS : PeriodicLattice.LogSeriesNearOne)
    (hE : ComplexMatrix2.ExpLogEstimates) {z : TripleCoordIndex L n k → ℂ}
    {ε : LevelFormIndex L n k → ℂ} (ξ : LevelForms L n k)
    (h1 : ∀ b : PositiveEdge L n k 0,
      (ξ.1 : Edge L n k 0 → ComplexMatrix2) b.1 = edgeMatrix ε (.inl (0, b)))
    (h2 : ∀ (i : Fin k) (c : PositiveEdge L n k (i + 1)),
      (ξ.2 i : Edge L n k (i + 1) → ComplexMatrix2) c.1 = edgeMatrix ε (.inr ⟨i, (0, c)⟩))
    (h : ∀ p, ‖expProd (edgeMatrix ε p) (edgeMatrix (formPart z) p) - 1‖ < 9 / 10) :
    expMove ξ (complexChainPoint z) = complexChainPoint (movedCoords z ε) := by
  have core : ∀ p : LevelFormIndex L n k,
      ComplexMatrix2.matExp (Complex.I • edgeMatrix ε p) *
          ComplexMatrix2.matExp (Complex.I • edgeMatrix (formPart z) p) =
        ComplexMatrix2.matExp (Complex.I • edgeMatrix (formPart (movedCoords z ε)) p) := by
    intro p
    rw [edgeMatrix_movedCoords hS hE p (h p),
      (expProdLog_spec hS hE (edgeMatrix_mem ε p) (edgeMatrix_mem _ p) (h p)).2]
    rfl
  have base : ∀ b : PositiveEdge L n k 0,
      ComplexMatrix2.matExp (Complex.I • (ξ.1 : Edge L n k 0 → ComplexMatrix2) b.1) *
          (PeriodicLattice.expTwist (complexFineValues z) (unitPoint L n k).fine b.1) =
        PeriodicLattice.expTwist (complexFineValues (movedCoords z ε))
          (unitPoint L n k).fine b.1 := by
    intro b
    simp only [PeriodicLattice.expTwist, if_pos b.2, unitPoint, mul_one, complexFineValues_eq, h1]
    exact core _
  unfold expMove complexChainPoint
  congr 1
  · funext b
    by_cases hb : b.IsPositivelyOriented
    · have := base ⟨b, hb⟩
      simpa only [PeriodicLattice.expTwist, if_pos hb] using this
    · have hr := opposite_isPositive b hb
      have := base ⟨b.opposite, hr⟩
      simp only [PeriodicLattice.expTwist, if_pos hr] at this
      simp only [PeriodicLattice.expTwist, if_neg hb, if_pos hr]
      exact congrArg _ this
  · funext i c
    have := core (.inr ⟨i, (0, c)⟩)
    simp only [unitPoint, mul_one, complexLevelValues_eq, h2]
    exact this
end MovedCoordinates
section CellCounts
variable {L n k : ℕ}
private lemma refinedBlock_facts (hLat : PeriodicLattice.CoordinateDescription)
    (hCell : NeighbouringFineVertexCells) (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n)
    (y : Vertex L n k k) :
    (PeriodicLattice.refinedBlock k y).Finite ∧
      (PeriodicLattice.refinedBlock k y).ncard = L ^ (4 * k) ∧
      ∀ {j : ℕ} (_ : j ≤ k) (x : Vertex L n k j), levelVertexCell x = y →
        (x : PeriodicLattice.FourTorus L n) ∈ PeriodicLattice.refinedBlock k y := by apply _root_.YangMills.SharedProofs.p41695 <;> assumption
private def axisOf {j : ℕ} (b : PositiveEdge L n k j) : Fin 4 := b.2.choose
private lemma edge_eq {j : ℕ} (p q : PositiveEdge L n k j)
    (ht : (p.1.source : PeriodicLattice.FourTorus L n) = q.1.source) (hd : axisOf p = axisOf q) :
    p = q := by
  apply Subtype.ext
  have h1 := p.2.choose_spec
  have h2 := q.2.choose_spec
  have ht' : p.1.source = q.1.source := Subtype.ext ht
  have h3 : p.1.target = q.1.target := by
    have e1 : p.1.target = p.1.source + PeriodicLattice.unitStep L n _ (axisOf p) := by
      rw [← sub_eq_iff_eq_add']; exact h1
    have e2 : q.1.target = q.1.source + PeriodicLattice.unitStep L n _ (axisOf q) := by
      rw [← sub_eq_iff_eq_add']; exact h2
    rw [e1, e2, ht', hd]
  exact PeriodicLattice.Bond.ext ht' h3
private lemma card_fibre_le {ι κ Y P : Type} [Fintype ι] [Fintype κ] (c : ι → Y) (y : Y)
    [DecidablePred fun p => c p = y] (pt : ι → P) (lab : ι → κ) (B : Set P) (hB : B.Finite)
    (hmem : ∀ p, c p = y → pt p ∈ B)
    (hinj : ∀ p q, c p = y → c q = y → lab p = lab q → pt p = pt q → p = q) :
    (Finset.univ.filter fun p => c p = y).card ≤ Fintype.card κ * B.ncard := by apply _root_.YangMills.SharedProofs.p5765 <;> assumption
private abbrev FormLabel (k : ℕ) : Type := Fin (k + 1) × Fin 3 × Fin 4
private def formPoint : LevelFormIndex L n k → PeriodicLattice.FourTorus L n
  | .inl p => p.2.1.source
  | .inr p => p.2.2.1.source
private def formLabel : LevelFormIndex L n k → FormLabel k
  | .inl p => (0, p.1, axisOf p.2)
  | .inr p => (⟨p.1 + 1, by have := p.1.2; omega⟩, p.2.1, axisOf p.2.2)
private lemma formLabel_injective (p q : LevelFormIndex L n k) (hl : formLabel p = formLabel q)
    (hp : formPoint p = formPoint q) : p = q := by
  rcases p with ⟨c, b⟩ | ⟨i, c, b⟩ <;> rcases q with ⟨c', b'⟩ | ⟨i', c', b'⟩
  · simp only [formLabel, Prod.mk.injEq, true_and] at hl
    simp only [formPoint] at hp
    obtain rfl := hl.1
    rw [edge_eq b b' hp hl.2]
  · simp only [formLabel, Prod.mk.injEq] at hl
    have := congrArg Fin.val hl.1
    simp at this
  · simp only [formLabel, Prod.mk.injEq] at hl
    have := congrArg Fin.val hl.1
    simp at this
  · simp only [formLabel, Prod.mk.injEq] at hl
    have h1 := congrArg Fin.val hl.1
    simp only [Nat.add_right_cancel_iff] at h1
    obtain rfl : i = i' := Fin.ext h1
    simp only [formPoint] at hp
    obtain rfl := hl.2.1
    rw [edge_eq b b' hp hl.2.2]
open Classical in
private lemma card_form_cell (hLat : PeriodicLattice.CoordinateDescription)
    (hCell : NeighbouringFineVertexCells) (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n)
    [Fintype (LevelFormIndex L n k)] (y : Vertex L n k k) :
    (Finset.univ.filter fun p : LevelFormIndex L n k => levelFormIndexCell p = y).card ≤
      Fintype.card (FormLabel k) * L ^ (4 * k) := by apply _root_.YangMills.DeltaSharedProofs.p502328 <;> assumption
private def intBox (R : ℝ) : Finset (Fin 4 → ℤ) :=
  Fintype.piFinset fun _ => Finset.Icc (-((⌈R⌉₊ + 1 : ℕ) : ℤ)) ((⌈R⌉₊ + 1 : ℕ) : ℤ)
private lemma coe_offsetSite (y : Vertex L n k k) (m : Fin 4 → ℤ) (μ : Fin 4) :
    ((PeriodicLattice.offsetSite y m : Vertex L n k k) : PeriodicLattice.FourTorus L n) μ =
      (y : PeriodicLattice.FourTorus L n) μ +
        (((m μ : ℝ)) : AddCircle (PeriodicLattice.torusSide L n)) := by apply _root_.YangMills.SharedProofs.p56430 <;> assumption
private lemma exists_offset_of_near (hLat : PeriodicLattice.CoordinateDescription)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (y y' : Vertex L n k k) {R : ℝ}
    (h : cellDist y' y ≤ R) :
    ∃ m ∈ intBox R, y' = PeriodicLattice.offsetSite y m := by apply _root_.YangMills.DeltaSharedProofs.p502225 <;> assumption
open Classical in
private lemma card_near_le' (hLat : PeriodicLattice.CoordinateDescription)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) {ι : Type} [Fintype ι]
    (c : ι → Vertex L n k k) {D : ℕ}
    (hD : ∀ y, (Finset.univ.filter fun p => c p = y).card ≤ D) (y : Vertex L n k k) (R : ℝ) :
    (Finset.univ.filter fun p => cellDist (c p) y ≤ R).card ≤ D * (intBox R).card := by apply _root_.YangMills.DeltaSharedProofs.p502568 <;> assumption
end CellCounts
private def adjugateL : ComplexMatrix2 →L[ℂ] ComplexMatrix2 :=
  LinearMap.toContinuousLinearMap
    { toFun := fun X => !![X 1 1, -X 0 1; -X 1 0, X 0 0]
      map_add' := fun X Y => by
        ext i j
        fin_cases i <;> fin_cases j <;> simp <;> ring
      map_smul' := fun c X => by
        ext i j
        fin_cases i <;> fin_cases j <;> simp }
private lemma adjugateL_apply (X : ComplexMatrix2) :
    adjugateL X = !![X 1 1, -X 0 1; -X 1 0, X 0 0] := rfl
private lemma adjugateL_eq_inv {X : ComplexMatrix2} (h : X.det = 1) : adjugateL X = X⁻¹ := by
  have e : X⁻¹ = Matrix.adjugate X := by simp [Matrix.inv_def, h]
  rw [e, Matrix.adjugate_fin_two, adjugateL_apply]
private def pauliSumL {X : Type} [Fintype X] (idx : Fin 3 → X) : (X → ℂ) →L[ℂ] ComplexMatrix2 :=
  ∑ a, (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : X => ℂ) (idx a)).smulRight
    (ComplexMatrix2.pauliFamily a)
private lemma pauliSumL_apply {X : Type} [Fintype X] (idx : Fin 3 → X) (f : X → ℂ) :
    pauliSumL idx f = ∑ a, f (idx a) • ComplexMatrix2.pauliFamily a := by
  simp [pauliSumL]
private def pauliNormSum : ℝ := ∑ a, ‖ComplexMatrix2.pauliFamily a‖
private lemma pauliNormSum_nonneg : 0 ≤ pauliNormSum := Finset.sum_nonneg fun _ _ => norm_nonneg _
private lemma norm_pauliSumL_le {X : Type} [Fintype X] (idx : Fin 3 → X) (f : X → ℂ) :
    ‖pauliSumL idx f‖ ≤ pauliNormSum * ‖f‖ := by
  rw [pauliSumL_apply, pauliNormSum, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => ?_)
  rw [norm_smul, mul_comm]
  exact mul_le_mul_of_nonneg_left (norm_le_pi_norm f _) (norm_nonneg _)
private def traceCLM : ComplexMatrix2 →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap (Matrix.traceLinearMap (Fin 2) ℂ ℂ)
private def conjCoords {X : Type} (z : X → ℂ) : X → ℂ := fun i => conj (z i)
private lemma norm_conjCoords_le {X : Type} [Fintype X] (z : X → ℂ) : ‖conjCoords z‖ ≤ ‖z‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_
  simpa [conjCoords] using norm_le_pi_norm z i
private lemma conjCoords_real {X : Type} (x : X → ℝ) :
    conjCoords (complexifyCoords x) = complexifyCoords x := by
  funext i
  simp [conjCoords, complexifyCoords]
private lemma analyticOnNhd_conj_conjCoords (hB : ComplexAnalysis.BoundedLineHolomorphicIsAnalytic)
    {X : Type} [Fintype X] {f : (X → ℂ) → ℂ} {R M : ℝ}
    (hf : ∀ z, ‖z‖ < R → AnalyticAt ℂ f z) (hM : ∀ z, ‖z‖ < R → ‖f z‖ ≤ M) :
    AnalyticOnNhd ℂ (fun z => conj (f (conjCoords z))) (ball 0 R) := by
  have hc : ∀ z : X → ℂ, ‖z‖ < R → ‖conjCoords z‖ < R := fun z h => (norm_conjCoords_le z).trans_lt h
  refine hB (X → ℂ) ℂ _ _ M isOpen_ball (fun z hz => ?_) fun x hx v => ?_
  · have hz' : ‖z‖ < R := by simpa using hz
    simpa using hM _ (hc z hz')
  · have hx' : ‖x‖ < R := by simpa using hx
    have h1 : DifferentiableAt ℂ (fun t : ℂ => conjCoords x + t • conjCoords v) 0 := by fun_prop
    have h2 : DifferentiableAt ℂ f (conjCoords x + (0 : ℂ) • conjCoords v) := by
      simpa using (hf _ (hc x hx')).differentiableAt
    have h3 : DifferentiableAt ℂ (fun t : ℂ => f (conjCoords x + t • conjCoords v)) 0 :=
      DifferentiableAt.comp (0 : ℂ) h2 h1
    have h4 : DifferentiableAt ℂ (fun t : ℂ => f (conjCoords x + t • conjCoords v)) (conj 0) := by
      simpa using h3
    have h5 := h4.conj_conj
    have e : (fun t : ℂ => conj (f (conjCoords (x + t • v)))) =
        (conj ∘ (fun t : ℂ => f (conjCoords x + t • conjCoords v)) ∘ conj) := by
      funext t
      have : conjCoords (x + t • v) = conjCoords x + conj t • conjCoords v := by
        funext i
        simp [conjCoords]
      simp [this]
    rw [e]
    simpa using h5
private lemma sum_le_of_support {ι : Type} [Fintype ι] (f : ι → ℝ) (S : Finset ι) {N : ℕ} {B : ℝ}
    (hB : 0 ≤ B) (h0 : ∀ i, i ∉ S → f i = 0) (hb : ∀ i, f i ≤ B) (hc : S.card ≤ N) :
    ∑ i, f i ≤ N * B := by
  have h1 : ∑ i, f i = ∑ i ∈ S, f i :=
    (Finset.sum_subset (Finset.subset_univ S) fun i _ hi => h0 i hi).symm
  rw [h1]
  calc ∑ i ∈ S, f i ≤ ∑ _i ∈ S, B := Finset.sum_le_sum fun i _ => hb i
    _ = S.card * B := by simp
    _ ≤ N * B := mul_le_mul_of_nonneg_right (by exact_mod_cast hc) hB
private lemma deriv_deriv_congr' {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] {f g : ℝ → ℝ → F}
    (h : ∀ᶠ w : ℝ × ℝ in 𝓝 0, f w.1 w.2 = g w.1 w.2) :
    deriv (fun s => deriv (fun t => f s t) 0) 0 = deriv (fun s => deriv (fun t => g s t) 0) 0 := by
  have h0 : ∀ᶠ w : ℝ × ℝ in 𝓝 ((0 : ℝ), (0 : ℝ)), f w.1 w.2 = g w.1 w.2 := h
  rw [nhds_prod_eq] at h0
  have h1 := h0.curry
  have h2 : (fun s => deriv (fun t => f s t) 0) =ᶠ[𝓝 0] fun s => deriv (fun t => g s t) 0 := by
    filter_upwards [h1] with s hs
    exact Filter.EventuallyEq.deriv_eq hs
  exact h2.deriv_eq
section TopTerms
variable {L n k : ℕ}
private def topField (z : TripleCoordIndex L n k → ℂ) (c : PositiveEdge L n k k) : ComplexMatrix2 :=
  levelField (complexChainPoint z) k c.1
private def topCell (c : PositiveEdge L n k k) : Vertex L n k k := levelVertexCell c.1.source
variable [Fintype (LevelFormIndex L n k)] [Fintype (Fin 3 × PositiveEdge L n k k)]
private abbrev CoordPair (L n k : ℕ) : Type :=
  (TripleCoordIndex L n k → ℂ) × (LevelFormIndex L n k → ℂ)
private def topTerm (c : PositiveEdge L n k k) (q : CoordPair L n k) : ComplexMatrix2 :=
  Complex.I⁻¹ • ComplexMatrix2.logSeries (topField (movedCoords q.1 q.2) c * adjugateL (topField q.1 c))
private structure TopHypotheses (ρ₁ ρ r : ℝ) : Prop where
  pos : 0 < ρ
  sub : ρ ≤ ρ₁
  nonneg : 0 ≤ r
  det : ∀ z : TripleCoordIndex L n k → ℂ, ‖z‖ < ρ₁ → ∀ c, (topField z c).det = 1
  near : ∀ z : TripleCoordIndex L n k → ℂ, ‖z‖ < ρ₁ → ∀ c, ‖topField z c - 1‖ ≤ 1 / 8
  an : ∀ (c : PositiveEdge L n k k) (z : TripleCoordIndex L n k → ℂ), ‖z‖ < ρ₁ →
    AnalyticAt ℂ (fun z => topField z c) z
  rd : ∀ (c : PositiveEdge L n k k) (z z' : TripleCoordIndex L n k → ℂ), ‖z‖ < ρ₁ → ‖z'‖ < ρ₁ →
    (∀ i, cellDist (tripleCoordIndexCell i) (topCell c) ≤ r → z i = z' i) →
      topField z c = topField z' c
  prod : ∀ (z : TripleCoordIndex L n k → ℂ) (ε : LevelFormIndex L n k → ℂ), ‖z‖ < ρ → ‖ε‖ < ρ →
    ∀ p, ‖expProd (edgeMatrix ε p) (edgeMatrix (formPart z) p) - 1‖ < 9 / 10
  mv : ∀ (z : TripleCoordIndex L n k → ℂ) (ε : LevelFormIndex L n k → ℂ), ‖z‖ < ρ → ‖ε‖ < ρ →
    ‖movedCoords z ε‖ < ρ₁
private lemma edgeMatrix_eq_pauliSumL (f : LevelFormIndex L n k → ℂ) (p : LevelFormIndex L n k) :
    edgeMatrix f p = pauliSumL (fun a => withColour a p) f := by
  rw [pauliSumL_apply]
  rfl
private lemma formPart_edgeMatrix_eq (z : TripleCoordIndex L n k → ℂ) (p : LevelFormIndex L n k) :
    edgeMatrix (formPart z) p =
      pauliSumL (fun a => (Sum.inl (withColour a p) : TripleCoordIndex L n k)) z := by
  rw [pauliSumL_apply]
  rfl
private lemma analyticAt_movedCoords (hS : PeriodicLattice.LogSeriesNearOne) (q : CoordPair L n k)
    (h : ∀ p, ‖expProd (edgeMatrix q.2 p) (edgeMatrix (formPart q.1) p) - 1‖ < 9 / 10) :
    AnalyticAt ℂ (fun q : CoordPair L n k => movedCoords q.1 q.2) q := by
  refine analyticAt_pi_iff.2 fun i => ?_
  rcases i with p | r
  · have h1 : AnalyticAt ℂ (fun q : CoordPair L n k => edgeMatrix q.2 p) q := by
      simp only [edgeMatrix_eq_pauliSumL]
      have h0 : AnalyticAt ℂ (pauliSumL (fun a => withColour a p)) q.2 :=
        ContinuousLinearMap.analyticAt _ _
      exact AnalyticAt.comp (g := pauliSumL (fun a => withColour a p))
        (f := fun q : CoordPair L n k => q.2) h0 analyticAt_snd
    have h2 : AnalyticAt ℂ (fun q : CoordPair L n k => edgeMatrix (formPart q.1) p) q := by
      simp only [formPart_edgeMatrix_eq]
      have h0 : AnalyticAt ℂ
          (pauliSumL (fun a => (Sum.inl (withColour a p) : TripleCoordIndex L n k))) q.1 :=
        ContinuousLinearMap.analyticAt _ _
      exact AnalyticAt.comp (g := pauliSumL (fun a => (Sum.inl (withColour a p) : TripleCoordIndex L n k)))
        (f := fun q : CoordPair L n k => q.1) h0 analyticAt_fst
    have h3 : AnalyticAt ℂ (fun q : ComplexMatrix2 × ComplexMatrix2 => expProdLog q.1 q.2)
        (edgeMatrix q.2 p, edgeMatrix (formPart q.1) p) :=
      analyticAt_expProdLog hS (lt_trans (h p) (by norm_num))
    have h4 : AnalyticAt ℂ (fun q : CoordPair L n k =>
        expProdLog (edgeMatrix q.2 p) (edgeMatrix (formPart q.1) p)) q :=
      AnalyticAt.comp (g := fun q : ComplexMatrix2 × ComplexMatrix2 => expProdLog q.1 q.2)
        (f := fun q : CoordPair L n k => (edgeMatrix q.2 p, edgeMatrix (formPart q.1) p)) h3
        (h1.prod h2)
    exact ((pauliCoordL (colourIndex p)).analyticAt _).comp h4
  · have e : (fun q : CoordPair L n k => movedCoords q.1 q.2 (Sum.inr r)) =
        fun q => (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : TripleCoordIndex L n k => ℂ)
          (Sum.inr r)) q.1 := rfl
    rw [e]
    have h0 : AnalyticAt ℂ (ContinuousLinearMap.proj (R := ℂ)
        (φ := fun _ : TripleCoordIndex L n k => ℂ) (Sum.inr r)) q.1 :=
      ContinuousLinearMap.analyticAt _ _
    exact AnalyticAt.comp (g := ContinuousLinearMap.proj (R := ℂ)
      (φ := fun _ : TripleCoordIndex L n k => ℂ) (Sum.inr r)) (f := fun q : CoordPair L n k => q.1)
      h0 analyticAt_fst
private lemma norm_mul_adjugate_sub_one_le (hE : ComplexMatrix2.ExpLogEstimates)
    {W W' : ComplexMatrix2} (hW : W.det = 1)
    (h : ‖W - 1‖ ≤ 1 / 8) (h' : ‖W' - 1‖ ≤ 1 / 8) : ‖W' * adjugateL W - 1‖ ≤ 1 / 2 := by
  have h1 : ‖W - 1‖ < 1 := by linarith
  have h2 := (hE.2.2.2.1 (W - 1) h1).2.2.2.1
  have e1 : 1 + (W - 1) = W := by abel
  rw [e1, ← adjugateL_eq_inv hW] at h2
  have h3 : ‖W - 1‖ / (1 - ‖W - 1‖) ≤ 1 / 7 := by
    rw [div_le_iff₀ (by linarith)]
    linarith
  have h4 : ‖adjugateL W - 1‖ ≤ 1 / 7 := h2.trans h3
  have e2 : W' * adjugateL W - 1 =
      (W' - 1) + (adjugateL W - 1) + (W' - 1) * (adjugateL W - 1) := by noncomm_ring
  rw [e2]
  calc ‖(W' - 1) + (adjugateL W - 1) + (W' - 1) * (adjugateL W - 1)‖
      ≤ ‖W' - 1‖ + ‖adjugateL W - 1‖ + ‖W' - 1‖ * ‖adjugateL W - 1‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) (norm_mul_le _ _))
    _ ≤ 1 / 8 + 1 / 7 + 1 / 8 * (1 / 7) := by
        gcongr
    _ ≤ 1 / 2 := by norm_num
variable {ρ₁ ρ r : ℝ}
private lemma analyticAt_topTerm (hS : PeriodicLattice.LogSeriesNearOne)
    (hE : ComplexMatrix2.ExpLogEstimates) (h : TopHypotheses (L := L) (n := n) (k := k) ρ₁ ρ r)
    (c : PositiveEdge L n k k) {q : CoordPair L n k} (hq : ‖q‖ < ρ) :
    AnalyticAt ℂ (topTerm c) q := by
  have h1 : ‖q.1‖ < ρ := lt_of_le_of_lt (norm_fst_le q) hq
  have h2 : ‖q.2‖ < ρ := lt_of_le_of_lt (norm_snd_le q) hq
  have h1' : ‖q.1‖ < ρ₁ := lt_of_lt_of_le h1 h.sub
  have a1 : AnalyticAt ℂ (fun q : CoordPair L n k => topField (movedCoords q.1 q.2) c) q :=
    AnalyticAt.comp (g := fun z => topField z c) (f := fun q : CoordPair L n k => movedCoords q.1 q.2)
      (h.an c _ (h.mv _ _ h1 h2)) (analyticAt_movedCoords hS q (h.prod _ _ h1 h2))
  have a2 : AnalyticAt ℂ (fun q : CoordPair L n k => topField q.1 c) q :=
    AnalyticAt.comp (g := fun z => topField z c) (f := fun q : CoordPair L n k => q.1)
      (h.an c _ h1') analyticAt_fst
  have a3 : AnalyticAt ℂ (fun q : CoordPair L n k => adjugateL (topField q.1 c)) q :=
    (adjugateL.analyticAt _).comp a2
  have a4 : AnalyticAt ℂ (fun q : CoordPair L n k =>
      topField (movedCoords q.1 q.2) c * adjugateL (topField q.1 c)) q := a1.mul a3
  have hlog : ‖topField (movedCoords q.1 q.2) c * adjugateL (topField q.1 c) - 1‖ ≤ 1 / 2 :=
    norm_mul_adjugate_sub_one_le hE (h.det _ h1' c) (h.near _ h1' c) (h.near _ (h.mv _ _ h1 h2) c)
  have a5 : AnalyticAt ℂ ComplexMatrix2.logSeries
      (topField (movedCoords q.1 q.2) c * adjugateL (topField q.1 c)) :=
    hS.1 _ (by
      change ‖_ - 1‖ < 1
      linarith)
  exact analyticAt_const_smul' _ (AnalyticAt.comp (g := ComplexMatrix2.logSeries)
    (f := fun q : CoordPair L n k =>
      topField (movedCoords q.1 q.2) c * adjugateL (topField q.1 c)) a5 a4)
private lemma norm_topTerm_le (hE : ComplexMatrix2.ExpLogEstimates)
    (h : TopHypotheses (L := L) (n := n) (k := k) ρ₁ ρ r)
    (c : PositiveEdge L n k k) {q : CoordPair L n k} (hq : ‖q‖ < ρ) : ‖topTerm c q‖ ≤ 1 := by
  have h1 : ‖q.1‖ < ρ := lt_of_le_of_lt (norm_fst_le q) hq
  have h2 : ‖q.2‖ < ρ := lt_of_le_of_lt (norm_snd_le q) hq
  have h1' : ‖q.1‖ < ρ₁ := lt_of_lt_of_le h1 h.sub
  have hlog : ‖topField (movedCoords q.1 q.2) c * adjugateL (topField q.1 c) - 1‖ ≤ 1 / 2 :=
    norm_mul_adjugate_sub_one_le hE (h.det _ h1' c) (h.near _ h1' c) (h.near _ (h.mv _ _ h1 h2) c)
  set X := topField (movedCoords q.1 q.2) c * adjugateL (topField q.1 c) with hX
  have h3 := hE.2.2.2.1 (X - 1) (by linarith)
  have e : 1 + (X - 1) = X := by abel
  rw [e] at h3
  have h4 : ‖ComplexMatrix2.logSeries X‖ ≤ 1 := by
    refine (h3.1.trans h3.2.1).trans ?_
    rw [div_le_iff₀ (by linarith)]
    linarith
  simp only [topTerm, ← hX, norm_smul, norm_inv, Complex.norm_I, inv_one, one_mul]
  exact h4
private lemma movedCoords_local {y : Vertex L n k k} {R : ℝ} {z z' : TripleCoordIndex L n k → ℂ}
    {ε ε' : LevelFormIndex L n k → ℂ}
    (hz : ∀ i, cellDist (tripleCoordIndexCell i) y ≤ R → z i = z' i)
    (hε : ∀ p, cellDist (levelFormIndexCell p) y ≤ R → ε p = ε' p)
    (i : TripleCoordIndex L n k) (hi : cellDist (tripleCoordIndexCell i) y ≤ R) :
    movedCoords z ε i = movedCoords z' ε' i := by
  rcases i with p | r
  · have hp : cellDist (levelFormIndexCell p) y ≤ R := hi
    have e1 : edgeMatrix ε p = edgeMatrix ε' p := by
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [hε _ (by rw [cell_withColour]; exact hp)]
    have e2 : edgeMatrix (formPart z) p = edgeMatrix (formPart z') p := by
      refine Finset.sum_congr rfl fun a _ => ?_
      have : formPart z (withColour a p) = formPart z' (withColour a p) :=
        hz (.inl (withColour a p)) (by
          change cellDist (levelFormIndexCell (withColour a p)) y ≤ R
          rw [cell_withColour]
          exact hp)
      rw [this]
    simp only [movedCoords, Sum.elim_inl, e1, e2]
  · exact hz _ hi
private lemma topTerm_local (h : TopHypotheses (L := L) (n := n) (k := k) ρ₁ ρ r)
    (c : PositiveEdge L n k k)
    {q q' : CoordPair L n k} (hq : ‖q‖ < ρ) (hq' : ‖q'‖ < ρ)
    (hz : ∀ i, cellDist (tripleCoordIndexCell i) (topCell c) ≤ r → q.1 i = q'.1 i)
    (hε : ∀ p, cellDist (levelFormIndexCell p) (topCell c) ≤ r → q.2 p = q'.2 p) :
    topTerm c q = topTerm c q' := by
  have h1 : ‖q.1‖ < ρ := lt_of_le_of_lt (norm_fst_le q) hq
  have h2 : ‖q.2‖ < ρ := lt_of_le_of_lt (norm_snd_le q) hq
  have h1' : ‖q'.1‖ < ρ := lt_of_le_of_lt (norm_fst_le q') hq'
  have h2' : ‖q'.2‖ < ρ := lt_of_le_of_lt (norm_snd_le q') hq'
  have e1 : topField q.1 c = topField q'.1 c :=
    h.rd c _ _ (lt_of_lt_of_le h1 h.sub) (lt_of_lt_of_le h1' h.sub) hz
  have e2 : topField (movedCoords q.1 q.2) c = topField (movedCoords q'.1 q'.2) c :=
    h.rd c _ _ (h.mv _ _ h1 h2) (h.mv _ _ h1' h2') (movedCoords_local hz hε)
  simp only [topTerm, e1, e2]
end TopTerms
section SecondKernels
variable {L n k : ℕ} [Fintype (LevelFormIndex L n k)] [Fintype (Fin 3 × PositiveEdge L n k k)]
  [DecidableEq (LevelFormIndex L n k)]
private def coordDir (p : LevelFormIndex L n k) : CoordPair L n k := (0, Pi.single p 1)
private lemma norm_coordDir_le (p : LevelFormIndex L n k) : ‖coordDir p‖ ≤ 1 := by apply _root_.YangMills.DeltaSharedProofs.p501125 <;> assumption
private def secondKernel (z : TripleCoordIndex L n k → ℂ) (c : PositiveEdge L n k k)
    (p q : LevelFormIndex L n k) : ComplexMatrix2 :=
  secondDeriv (topTerm c) ((z, 0) : CoordPair L n k) (coordDir p) (coordDir q)
variable {ρ₁ ρ r : ℝ}
private lemma norm_basePair (z : TripleCoordIndex L n k → ℂ) : ‖((z, 0) : CoordPair L n k)‖ = ‖z‖ := by
  simp [Prod.norm_def]
private lemma analyticAt_secondKernel (hS : PeriodicLattice.LogSeriesNearOne)
    (hE : ComplexMatrix2.ExpLogEstimates) (h : TopHypotheses (L := L) (n := n) (k := k) ρ₁ ρ r)
    (c : PositiveEdge L n k k) (p q : LevelFormIndex L n k) {z : TripleCoordIndex L n k → ℂ}
    (hz : ‖z‖ < ρ) : AnalyticAt ℂ (fun z => secondKernel z c p q) z := by
  have hs : AnalyticOnNhd ℂ (topTerm (L := L) (n := n) (k := k) c) (ball 0 ρ) := fun y hy =>
    analyticAt_topTerm hS hE h c (by simpa using hy)
  have h1 := analyticOnNhd_secondDeriv hs (coordDir p) (coordDir q) ((z, 0) : CoordPair L n k)
    (by simpa [norm_basePair] using hz)
  have h2 : AnalyticAt ℂ (fun z : TripleCoordIndex L n k → ℂ => ((z, 0) : CoordPair L n k)) z :=
    analyticAt_id.prod analyticAt_const
  exact AnalyticAt.comp (g := fun x => secondDeriv (topTerm c) x (coordDir p) (coordDir q))
    (f := fun z : TripleCoordIndex L n k → ℂ => ((z, 0) : CoordPair L n k)) h1 h2
private lemma norm_secondKernel_le (hS : PeriodicLattice.LogSeriesNearOne)
    (hE : ComplexMatrix2.ExpLogEstimates) (h : TopHypotheses (L := L) (n := n) (k := k) ρ₁ ρ r)
    (c : PositiveEdge L n k k) (p q : LevelFormIndex L n k) {z : TripleCoordIndex L n k → ℂ}
    (hz : ‖z‖ < ρ / 2) : ‖secondKernel z c p q‖ ≤ 16 * 1 / (ρ / 2) ^ 2 := by
  have hR : 0 < ρ / 2 := half_pos h.pos
  have hin : ∀ y ∈ ball ((z, 0) : CoordPair L n k) (ρ / 2), ‖y‖ < ρ := by
    intro y hy
    have h1 : ‖y - ((z, 0) : CoordPair L n k)‖ < ρ / 2 := by simpa [dist_eq_norm] using hy
    have h2 : ‖y‖ ≤ ‖y - ((z, 0) : CoordPair L n k)‖ + ‖((z, 0) : CoordPair L n k)‖ := by
      simpa using norm_add_le (y - ((z, 0) : CoordPair L n k)) ((z, 0) : CoordPair L n k)
    rw [norm_basePair] at h2
    linarith
  exact norm_secondDeriv_le hR (fun y hy => analyticAt_topTerm hS hE h c (hin y hy))
    (fun y hy => norm_topTerm_le hE h c (hin y hy)) (norm_coordDir_le p) (norm_coordDir_le q)
private lemma eventually_norm_line_lt {x u v : CoordPair L n k} (hx : ‖x‖ < ρ) :
    ∀ᶠ w : ℝ × ℝ in 𝓝 0, ‖x + (w.1 : ℂ) • u + (w.2 : ℂ) • v‖ < ρ := by
  have hc : Continuous fun w : ℝ × ℝ => ‖x + (w.1 : ℂ) • u + (w.2 : ℂ) • v‖ := by
    have h1 : Continuous fun w : ℝ × ℝ => (w.1 : ℂ) := Complex.continuous_ofReal.comp continuous_fst
    have h2 : Continuous fun w : ℝ × ℝ => (w.2 : ℂ) := Complex.continuous_ofReal.comp continuous_snd
    exact ((continuous_const.add (h1.smul continuous_const)).add
      (h2.smul continuous_const)).norm
  have h0 : ‖x + (((0 : ℝ × ℝ).1 : ℝ) : ℂ) • u + (((0 : ℝ × ℝ).2 : ℝ) : ℂ) • v‖ < ρ := by
    simpa using hx
  exact hc.continuousAt.eventually (gt_mem_nhds h0)
private lemma secondKernel_eq_zero_left (hS : PeriodicLattice.LogSeriesNearOne)
    (hE : ComplexMatrix2.ExpLogEstimates) (h : TopHypotheses (L := L) (n := n) (k := k) ρ₁ ρ r)
    (c : PositiveEdge L n k k) {p : LevelFormIndex L n k} (q : LevelFormIndex L n k)
    {z : TripleCoordIndex L n k → ℂ} (hz : ‖z‖ < ρ)
    (hp : r < cellDist (levelFormIndexCell p) (topCell c)) : secondKernel z c p q = 0 := by
  have hx : ‖((z, 0) : CoordPair L n k)‖ < ρ := by rwa [norm_basePair]
  have ha := analyticAt_topTerm hS hE h c hx
  have key : secondDeriv (topTerm c) ((z, 0) : CoordPair L n k) (coordDir p) (coordDir q) =
      secondDeriv (topTerm c) ((z, 0) : CoordPair L n k) 0 (coordDir q) := by
    refine secondDeriv_congr ha ha ?_
    filter_upwards [eventually_norm_line_lt (u := coordDir p) (v := coordDir q) hx,
      eventually_norm_line_lt (u := 0) (v := coordDir q) hx] with w h1 h2
    refine topTerm_local h c h1 h2 (fun i _ => ?_) fun i hi => ?_
    · simp [coordDir]
    · have hne : i ≠ p := fun e => absurd hi (by rw [e]; exact not_le.2 hp)
      simp [coordDir, Pi.single_eq_of_ne hne]
  rw [secondKernel, key, secondDeriv_zero_left]
private lemma secondKernel_eq_zero_right (hS : PeriodicLattice.LogSeriesNearOne)
    (hE : ComplexMatrix2.ExpLogEstimates) (h : TopHypotheses (L := L) (n := n) (k := k) ρ₁ ρ r)
    (c : PositiveEdge L n k k) (p : LevelFormIndex L n k) {q : LevelFormIndex L n k}
    {z : TripleCoordIndex L n k → ℂ} (hz : ‖z‖ < ρ)
    (hq : r < cellDist (levelFormIndexCell q) (topCell c)) : secondKernel z c p q = 0 := by
  have hx : ‖((z, 0) : CoordPair L n k)‖ < ρ := by rwa [norm_basePair]
  have ha := analyticAt_topTerm hS hE h c hx
  have key : secondDeriv (topTerm c) ((z, 0) : CoordPair L n k) (coordDir p) (coordDir q) =
      secondDeriv (topTerm c) ((z, 0) : CoordPair L n k) (coordDir p) 0 := by
    refine secondDeriv_congr ha ha ?_
    filter_upwards [eventually_norm_line_lt (u := coordDir p) (v := coordDir q) hx,
      eventually_norm_line_lt (u := coordDir p) (v := 0) hx] with w h1 h2
    refine topTerm_local h c h1 h2 (fun i _ => ?_) fun i hi => ?_
    · simp [coordDir]
    · have hne : i ≠ q := fun e => absurd hi (by rw [e]; exact not_le.2 hq)
      simp [coordDir, Pi.single_eq_of_ne hne]
  rw [secondKernel, key, secondDeriv_zero_right]
private lemma secondKernel_local (hS : PeriodicLattice.LogSeriesNearOne)
    (hE : ComplexMatrix2.ExpLogEstimates) (h : TopHypotheses (L := L) (n := n) (k := k) ρ₁ ρ r)
    (c : PositiveEdge L n k k) (p q : LevelFormIndex L n k)
    {z z' : TripleCoordIndex L n k → ℂ} (hz : ‖z‖ < ρ) (hz' : ‖z'‖ < ρ)
    (he : ∀ i, cellDist (tripleCoordIndexCell i) (topCell c) ≤ r → z i = z' i) :
    secondKernel z c p q = secondKernel z' c p q := by
  have hx : ‖((z, 0) : CoordPair L n k)‖ < ρ := by rwa [norm_basePair]
  have hx' : ‖((z', 0) : CoordPair L n k)‖ < ρ := by rwa [norm_basePair]
  refine secondDeriv_congr (analyticAt_topTerm hS hE h c hx) (analyticAt_topTerm hS hE h c hx') ?_
  filter_upwards [eventually_norm_line_lt (u := coordDir p) (v := coordDir q) hx,
    eventually_norm_line_lt (u := coordDir p) (v := coordDir q) hx'] with w h1 h2
  refine topTerm_local h c h1 h2 (fun i hi => ?_) fun i _ => ?_
  · simpa [coordDir] using he i hi
  · simp
end SecondKernels
section KernelEntries
variable {L n k : ℕ} [Fintype (LevelFormIndex L n k)] [Fintype (Fin 3 × PositiveEdge L n k k)]
  [DecidableEq (LevelFormIndex L n k)] [Fintype (PositiveEdge L n k k)]
private def topCoordMatrix (z : TripleCoordIndex L n k → ℂ) (c : PositiveEdge L n k k) : ComplexMatrix2 :=
  pauliSumL (fun a => (Sum.inr (Sum.inr (a, c)) : TripleCoordIndex L n k)) z
private def entryPart (z : TripleCoordIndex L n k → ℂ) (c : PositiveEdge L n k k)
    (p q : LevelFormIndex L n k) : ℂ :=
  (1 / 2 : ℂ) * traceCLM (topCoordMatrix z c * secondKernel z c p q)
private def holoKernel (z : TripleCoordIndex L n k → ℂ) :
    Matrix (LevelFormIndex L n k) (LevelFormIndex L n k) ℂ :=
  fun p q => ∑ c, entryPart z c p q
private def symKernel (z : TripleCoordIndex L n k → ℂ) :
    Matrix (LevelFormIndex L n k) (LevelFormIndex L n k) ℂ :=
  fun p q => (1 / 2 : ℂ) * (holoKernel z p q + conj (holoKernel (conjCoords z) p q))
private def entryCap (ρ : ℝ) : ℝ :=
  1 / 2 * (‖traceCLM‖ * ((pauliNormSum * ρ) * (16 * 1 / (ρ / 2) ^ 2)))
private lemma entryCap_nonneg {ρ : ℝ} (hρ : 0 < ρ) : 0 ≤ entryCap ρ := by
  have := pauliNormSum_nonneg
  unfold entryCap
  positivity
variable {ρ₁ ρ r : ℝ}
private lemma norm_entryPart_le (hS : PeriodicLattice.LogSeriesNearOne)
    (hE : ComplexMatrix2.ExpLogEstimates) (h : TopHypotheses (L := L) (n := n) (k := k) ρ₁ ρ r)
    (c : PositiveEdge L n k k) (p q : LevelFormIndex L n k) {z : TripleCoordIndex L n k → ℂ}
    (hz : ‖z‖ < ρ / 2) : ‖entryPart z c p q‖ ≤ entryCap ρ := by
  have hρ := h.pos
  have h1 : ‖topCoordMatrix z c‖ ≤ pauliNormSum * ρ :=
    (norm_pauliSumL_le _ z).trans (mul_le_mul_of_nonneg_left (by linarith) pauliNormSum_nonneg)
  have h2 := norm_secondKernel_le hS hE h c p q hz
  have h3 : ‖topCoordMatrix z c * secondKernel z c p q‖ ≤
      (pauliNormSum * ρ) * (16 * 1 / (ρ / 2) ^ 2) :=
    (norm_mul_le _ _).trans (mul_le_mul h1 h2 (norm_nonneg _)
      (mul_nonneg pauliNormSum_nonneg hρ.le))
  have h4 := traceCLM.le_opNorm (topCoordMatrix z c * secondKernel z c p q)
  rw [entryPart, norm_mul, entryCap]
  have e : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by simp
  rw [e]
  exact mul_le_mul_of_nonneg_left (h4.trans (mul_le_mul_of_nonneg_left h3 (norm_nonneg _)))
    (by norm_num)
private lemma entryPart_eq_zero_left (hS : PeriodicLattice.LogSeriesNearOne)
    (hE : ComplexMatrix2.ExpLogEstimates) (h : TopHypotheses (L := L) (n := n) (k := k) ρ₁ ρ r)
    (c : PositiveEdge L n k k) {p : LevelFormIndex L n k} (q : LevelFormIndex L n k)
    {z : TripleCoordIndex L n k → ℂ} (hz : ‖z‖ < ρ)
    (hp : r < cellDist (levelFormIndexCell p) (topCell c)) : entryPart z c p q = 0 := by
  simp [entryPart, secondKernel_eq_zero_left hS hE h c q hz hp]
private lemma entryPart_eq_zero_right (hS : PeriodicLattice.LogSeriesNearOne)
    (hE : ComplexMatrix2.ExpLogEstimates) (h : TopHypotheses (L := L) (n := n) (k := k) ρ₁ ρ r)
    (c : PositiveEdge L n k k) (p : LevelFormIndex L n k) {q : LevelFormIndex L n k}
    {z : TripleCoordIndex L n k → ℂ} (hz : ‖z‖ < ρ)
    (hq : r < cellDist (levelFormIndexCell q) (topCell c)) : entryPart z c p q = 0 := by
  simp [entryPart, secondKernel_eq_zero_right hS hE h c p hz hq]
private structure CellDistIsMetric (L n k : ℕ) : Prop where
  symm : ∀ y y' : Vertex L n k k, cellDist y y' = cellDist y' y
  tri : ∀ y y' y'' : Vertex L n k k, cellDist y y'' ≤ cellDist y y' + cellDist y' y''
private lemma entryPart_local (hS : PeriodicLattice.LogSeriesNearOne)
    (hE : ComplexMatrix2.ExpLogEstimates) (h : TopHypotheses (L := L) (n := n) (k := k) ρ₁ ρ r)
    (hd : CellDistIsMetric L n k) (c : PositiveEdge L n k k) (p q : LevelFormIndex L n k)
    {z z' : TripleCoordIndex L n k → ℂ} (hz : ‖z‖ < ρ) (hz' : ‖z'‖ < ρ)
    (he : ∀ i, cellDist (tripleCoordIndexCell i) (levelFormIndexCell p) ≤ 2 * r → z i = z' i) :
    entryPart z c p q = entryPart z' c p q := by
  by_cases hp : r < cellDist (levelFormIndexCell p) (topCell c)
  · rw [entryPart_eq_zero_left hS hE h c q hz hp, entryPart_eq_zero_left hS hE h c q hz' hp]
  · have hp' := not_lt.1 hp
    have hn : ∀ i, cellDist (tripleCoordIndexCell i) (topCell c) ≤ r → z i = z' i := by
      intro i hi
      refine he i ((hd.tri _ (topCell c) _).trans ?_)
      rw [hd.symm (topCell c)]
      linarith
    have e1 := secondKernel_local hS hE h c p q hz hz' hn
    have e2 : topCoordMatrix z c = topCoordMatrix z' c := by
      simp only [topCoordMatrix, pauliSumL_apply]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [he (.inr (.inr (a, c))) ?_]
      change cellDist (topCell c) (levelFormIndexCell p) ≤ 2 * r
      rw [hd.symm]
      linarith [h.nonneg]
    simp only [entryPart, e1, e2]
private lemma analyticAt_entryPart (hS : PeriodicLattice.LogSeriesNearOne)
    (hE : ComplexMatrix2.ExpLogEstimates) (h : TopHypotheses (L := L) (n := n) (k := k) ρ₁ ρ r)
    (c : PositiveEdge L n k k) (p q : LevelFormIndex L n k) {z : TripleCoordIndex L n k → ℂ}
    (hz : ‖z‖ < ρ) : AnalyticAt ℂ (fun z => entryPart z c p q) z := by
  have h0 : AnalyticAt ℂ
      (pauliSumL (fun a => (Sum.inr (Sum.inr (a, c)) : TripleCoordIndex L n k))) z :=
    ContinuousLinearMap.analyticAt _ _
  have h1 : AnalyticAt ℂ (fun z => topCoordMatrix z c * secondKernel z c p q) z :=
    h0.mul (analyticAt_secondKernel hS hE h c p q hz)
  have h2 : AnalyticAt ℂ traceCLM (topCoordMatrix z c * secondKernel z c p q) :=
    ContinuousLinearMap.analyticAt _ _
  have h3 : AnalyticAt ℂ (fun z => traceCLM (topCoordMatrix z c * secondKernel z c p q)) z :=
    AnalyticAt.comp (g := traceCLM) (f := fun z => topCoordMatrix z c * secondKernel z c p q) h2 h1
  exact analyticAt_const.mul h3
private lemma analyticAt_holoKernel (hS : PeriodicLattice.LogSeriesNearOne)
    (hE : ComplexMatrix2.ExpLogEstimates) (h : TopHypotheses (L := L) (n := n) (k := k) ρ₁ ρ r)
    (p q : LevelFormIndex L n k) {z : TripleCoordIndex L n k → ℂ} (hz : ‖z‖ < ρ) :
    AnalyticAt ℂ (fun z => holoKernel z p q) z :=
  Finset.analyticAt_fun_sum _ fun c _ => analyticAt_entryPart hS hE h c p q hz
open Classical in
private lemma norm_holoKernel_le (hS : PeriodicLattice.LogSeriesNearOne)
    (hE : ComplexMatrix2.ExpLogEstimates) (h : TopHypotheses (L := L) (n := n) (k := k) ρ₁ ρ r)
    (hd : CellDistIsMetric L n k) {N : ℕ}
    (hN : ∀ y : Vertex L n k k, (Finset.univ.filter fun c : PositiveEdge L n k k =>
      cellDist (topCell c) y ≤ r).card ≤ N)
    (p q : LevelFormIndex L n k) {z : TripleCoordIndex L n k → ℂ} (hz : ‖z‖ < ρ / 2) :
    ‖holoKernel z p q‖ ≤ N * entryCap ρ := by
  have hz' : ‖z‖ < ρ := by linarith [h.pos]
  refine (norm_sum_le _ _).trans (sum_le_of_support _ (Finset.univ.filter fun c =>
    cellDist (topCell c) (levelFormIndexCell p) ≤ r) (entryCap_nonneg h.pos) ?_
    (fun c => norm_entryPart_le hS hE h c p q hz) (hN _))
  intro c hc
  have hc' : r < cellDist (levelFormIndexCell p) (topCell c) := by
    rw [hd.symm]
    simpa using hc
  rw [entryPart_eq_zero_left hS hE h c q hz' hc', norm_zero]
private lemma symKernel_far (hS : PeriodicLattice.LogSeriesNearOne)
    (hE : ComplexMatrix2.ExpLogEstimates) (h : TopHypotheses (L := L) (n := n) (k := k) ρ₁ ρ r)
    (hd : CellDistIsMetric L n k) {p q : LevelFormIndex L n k} {z : TripleCoordIndex L n k → ℂ}
    (hz : ‖z‖ < ρ)
    (hpq : 2 * r < cellDist (levelFormIndexCell p) (levelFormIndexCell q)) :
    symKernel z p q = 0 := by
  have key : ∀ w : TripleCoordIndex L n k → ℂ, ‖w‖ < ρ → holoKernel w p q = 0 := by
    intro w hw
    refine Finset.sum_eq_zero fun c _ => ?_
    by_cases hp : r < cellDist (levelFormIndexCell p) (topCell c)
    · exact entryPart_eq_zero_left hS hE h c q hw hp
    · refine entryPart_eq_zero_right hS hE h c p hw ?_
      have h1 := hd.tri (levelFormIndexCell p) (topCell c) (levelFormIndexCell q)
      rw [hd.symm (topCell c)] at h1
      linarith [not_lt.1 hp]
  simp [symKernel, key z hz, key _ ((norm_conjCoords_le z).trans_lt hz)]
private lemma symKernel_local (hS : PeriodicLattice.LogSeriesNearOne)
    (hE : ComplexMatrix2.ExpLogEstimates) (h : TopHypotheses (L := L) (n := n) (k := k) ρ₁ ρ r)
    (hd : CellDistIsMetric L n k) (p q : LevelFormIndex L n k)
    {z z' : TripleCoordIndex L n k → ℂ} (hz : ‖z‖ < ρ) (hz' : ‖z'‖ < ρ)
    (he : ∀ i, cellDist (tripleCoordIndexCell i) (levelFormIndexCell p) ≤ 2 * r → z i = z' i) :
    symKernel z p q = symKernel z' p q := by
  have e1 : holoKernel z p q = holoKernel z' p q :=
    Finset.sum_congr rfl fun c _ => entryPart_local hS hE h hd c p q hz hz' he
  have e2 : holoKernel (conjCoords z) p q = holoKernel (conjCoords z') p q :=
    Finset.sum_congr rfl fun c _ => entryPart_local hS hE h hd c p q
      ((norm_conjCoords_le z).trans_lt hz) ((norm_conjCoords_le z').trans_lt hz') fun i hi => by
        simp only [conjCoords, he i hi]
  simp only [symKernel, e1, e2]
open Classical in
private theorem symKernel_isLocallyHolomorphic (hB : ComplexAnalysis.BoundedLineHolomorphicIsAnalytic)
    (hS : PeriodicLattice.LogSeriesNearOne)
    (hE : ComplexMatrix2.ExpLogEstimates) (h : TopHypotheses (L := L) (n := n) (k := k) ρ₁ ρ r)
    (hd : CellDistIsMetric L n k) {N N' : ℕ}
    (hN : ∀ y : Vertex L n k k, (Finset.univ.filter fun c : PositiveEdge L n k k =>
      cellDist (topCell c) y ≤ r).card ≤ N)
    (hN' : ∀ y : Vertex L n k k, (Finset.univ.filter fun p : LevelFormIndex L n k =>
      cellDist (levelFormIndexCell p) y ≤ 2 * r).card ≤ N') :
    IsLocallyHolomorphicFamily tripleCoordIndexCell levelFormIndexCell levelFormIndexCell
      (symKernel (L := L) (n := n) (k := k)) (ρ / 2) (N' * (N * entryCap ρ)) (2 * r) := by
  have hρ := h.pos
  have hnn : 0 ≤ (N : ℝ) * entryCap ρ := mul_nonneg (Nat.cast_nonneg _) (entryCap_nonneg hρ)
  have hb : ∀ z : TripleCoordIndex L n k → ℂ, ‖z‖ < ρ / 2 → ∀ p q,
      ‖symKernel z p q‖ ≤ N * entryCap ρ := by
    intro z hz p q
    have h1 := norm_holoKernel_le hS hE h hd hN p q hz
    have h2 := norm_holoKernel_le hS hE h hd hN p q ((norm_conjCoords_le z).trans_lt hz)
    rw [symKernel, norm_mul]
    have e : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by simp
    rw [e]
    have h3 := norm_add_le (holoKernel z p q) (conj (holoKernel (conjCoords z) p q))
    rw [Complex.norm_conj] at h3
    linarith
  refine ⟨fun p q z hz => ?_, fun z hz => ?_, fun p q z hz z' hz' he => ?_,
    fun z hz p q hpq => ?_⟩
  · have hz' : ‖z‖ < ρ / 2 := by simpa using hz
    have a1 : AnalyticAt ℂ (fun z => holoKernel z p q) z :=
      analyticAt_holoKernel hS hE h p q (by linarith)
    have a2 : AnalyticAt ℂ (fun z => conj (holoKernel (conjCoords z) p q)) z :=
      analyticOnNhd_conj_conjCoords hB (R := ρ / 2) (M := N * entryCap ρ)
        (f := fun z => holoKernel z p q)
        (fun w hw => analyticAt_holoKernel hS hE h p q (by linarith))
        (fun w hw => norm_holoKernel_le hS hE h hd hN p q hw) z hz
    exact analyticAt_const.mul (a1.add a2)
  · have hz' : ‖z‖ < ρ / 2 := by simpa using hz
    have hz2 : ‖z‖ < ρ := by linarith
    refine opNorm_le_of_schur _ (mul_nonneg (Nat.cast_nonneg _) hnn) (fun p => ?_) fun q => ?_
    · refine sum_le_of_support _ (Finset.univ.filter fun q =>
        cellDist (levelFormIndexCell q) (levelFormIndexCell p) ≤ 2 * r) hnn ?_
        (fun q => hb z hz' p q) (hN' _)
      intro q hq
      have hq' : 2 * r < cellDist (levelFormIndexCell p) (levelFormIndexCell q) := by
        rw [hd.symm]
        simpa using hq
      rw [symKernel_far hS hE h hd hz2 hq', norm_zero]
    · refine sum_le_of_support _ (Finset.univ.filter fun p =>
        cellDist (levelFormIndexCell p) (levelFormIndexCell q) ≤ 2 * r) hnn ?_
        (fun p => hb z hz' p q) (hN' _)
      intro p hp
      have hp' : 2 * r < cellDist (levelFormIndexCell p) (levelFormIndexCell q) := by
        simpa using hp
      rw [symKernel_far hS hE h hd hz2 hp', norm_zero]
  · have h1 : ‖z‖ < ρ := by
      have : ‖z‖ < ρ / 2 := by simpa using hz
      linarith
    have h2 : ‖z'‖ < ρ := by
      have : ‖z'‖ < ρ / 2 := by simpa using hz'
      linarith
    exact symKernel_local hS hE h hd p q h1 h2 he
  · have h1 : ‖z‖ < ρ := by
      have : ‖z‖ < ρ / 2 := by simpa using hz
      linarith
    exact symKernel_far hS hE h hd h1 hpq
end KernelEntries
section RealPoints
variable {L n k : ℕ} [Fintype (LevelFormIndex L n k)] [Fintype (Fin 3 × PositiveEdge L n k k)]
  [DecidableEq (LevelFormIndex L n k)] [Fintype (PositiveEdge L n k k)]
private lemma pair_eq_sum (v : LevelFormIndex L n k → ℂ) :
    (((0 : TripleCoordIndex L n k → ℂ), v) : CoordPair L n k) = ∑ p, v p • coordDir p := by
  ext i
  · simp [coordDir, Prod.fst_sum]
  · simp [coordDir, Prod.snd_sum, Finset.sum_apply, Pi.single_apply]
private lemma secondDeriv_eq_sum (g : CoordPair L n k → ComplexMatrix2) (x : CoordPair L n k)
    (v v' : LevelFormIndex L n k → ℂ) :
    secondDeriv g x ((0 : TripleCoordIndex L n k → ℂ), v) ((0 : TripleCoordIndex L n k → ℂ), v') =
      ∑ p, ∑ q, (v p * v' q) • secondDeriv g x (coordDir p) (coordDir q) := by
  rw [pair_eq_sum v, pair_eq_sum v']
  simp only [secondDeriv, map_sum, map_smul, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => by rw [mul_comm]
private lemma dot_holoKernel (z : TripleCoordIndex L n k → ℂ) (v v' : LevelFormIndex L n k → ℂ) :
    v ⬝ᵥ (holoKernel z).mulVec v' = ∑ c, (1 / 2 : ℂ) * traceCLM (topCoordMatrix z c *
      secondDeriv (topTerm c) ((z, 0) : CoordPair L n k) ((0 : TripleCoordIndex L n k → ℂ), v)
        ((0 : TripleCoordIndex L n k → ℂ), v')) := by
  have hc : ∀ c : PositiveEdge L n k k, (1 / 2 : ℂ) * traceCLM (topCoordMatrix z c *
      secondDeriv (topTerm c) ((z, 0) : CoordPair L n k) ((0 : TripleCoordIndex L n k → ℂ), v)
        ((0 : TripleCoordIndex L n k → ℂ), v')) =
      ∑ p, ∑ q, v p * (entryPart z c p q * v' q) := by
    intro c
    rw [secondDeriv_eq_sum, Finset.mul_sum, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.mul_sum, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [mul_smul_comm, map_smul, entryPart, secondKernel, smul_eq_mul]
    ring
  simp only [hc]
  rw [Finset.sum_comm]
  simp only [dotProduct, Matrix.mulVec, holoKernel]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Finset.sum_mul, Finset.mul_sum]
private lemma dot_symKernel (x : TripleCoordIndex L n k → ℝ) (v v' : LevelFormIndex L n k → ℝ) :
    complexifyCoords v ⬝ᵥ (symKernel (complexifyCoords x)).mulVec (complexifyCoords v') =
      (((complexifyCoords v ⬝ᵥ (holoKernel (complexifyCoords x)).mulVec
        (complexifyCoords v')).re : ℝ) : ℂ) := by
  set A := complexifyCoords v ⬝ᵥ (holoKernel (complexifyCoords x)).mulVec
    (complexifyCoords v') with hA
  let Bm : Matrix (LevelFormIndex L n k) (LevelFormIndex L n k) ℂ :=
    fun p q => conj (holoKernel (complexifyCoords x) p q)
  have hconj : conj A = complexifyCoords v ⬝ᵥ Bm.mulVec (complexifyCoords v') := by
    simp only [hA, Bm, dotProduct, Matrix.mulVec, map_sum, map_mul, complexifyCoords,
      Complex.conj_ofReal]
  have hk : symKernel (complexifyCoords x) =
      (1 / 2 : ℂ) • (holoKernel (complexifyCoords x) + Bm) := by
    ext p q
    simp [symKernel, conjCoords_real, Bm]
    rfl
  have e : complexifyCoords v ⬝ᵥ (symKernel (complexifyCoords x)).mulVec
      (complexifyCoords v') = (1 / 2 : ℂ) * (A + conj A) := by
    rw [hconj, hA, hk, Matrix.smul_mulVec, Matrix.add_mulVec, dotProduct_smul, dotProduct_add,
      smul_eq_mul]
  rw [e, Complex.add_conj]
  push_cast
  ring
end RealPoints
section RealTie
variable {L n k : ℕ} [Fintype (LevelFormIndex L n k)] [Fintype (Fin 3 × PositiveEdge L n k k)]
  [DecidableEq (LevelFormIndex L n k)] [Fintype (PositiveEdge L n k k)]
  [Fintype (GhostCoordIndex L n k)] [Fintype (Fin 3 × Vertex L n k 0)] [Fintype (Fin 3 × Vertex L n k k)]
private lemma formCoords_fine_value (P : PauliCoordinates L n k) (η : LevelForms L n k)
    (b : PositiveEdge L n k 0) :
    (η.1 : Edge L n k 0 → ComplexMatrix2) b.1 =
      edgeMatrix (complexifyCoords (P.formCoords η)) (.inl (0, b)) := by
  have hm : (η.1 : Edge L n k 0 → ComplexMatrix2) b.1 ∈ ComplexMatrix2.traceless := (η.1.2.1 b.1 b.2).2
  conv_lhs => rw [← sum_pauliCoordL_smul hm]
  refine Finset.sum_congr rfl fun a _ => ?_
  have e := P.formCoords_base η (a, b)
  simp only [toPauliCoeffs, restrictToPositiveEdges] at e
  rw [pauliCoeff_eq_pauliCoordL hm] at e
  rw [e]
  rfl
private lemma formCoords_level_value (P : PauliCoordinates L n k) (η : LevelForms L n k) (i : Fin k)
    (c : PositiveEdge L n k (i + 1)) :
    (η.2 i : Edge L n k (i + 1) → ComplexMatrix2) c.1 =
      edgeMatrix (complexifyCoords (P.formCoords η)) (.inr ⟨i, (0, c)⟩) := by
  have hm : (η.2 i : Edge L n k (i + 1) → ComplexMatrix2) c.1 ∈ ComplexMatrix2.traceless :=
    ((η.2 i).2.1 c.1 c.2).2
  conv_lhs => rw [← sum_pauliCoordL_smul hm]
  refine Finset.sum_congr rfl fun a _ => ?_
  have e := P.formCoords_level η i (a, c)
  simp only [toPauliCoeffs, restrictToPositiveEdges] at e
  rw [pauliCoeff_eq_pauliCoordL hm] at e
  rw [e]
  rfl
variable {ρ₁ ρ r : ℝ}
private lemma topLog_eq_topTerm (hS : PeriodicLattice.LogSeriesNearOne)
    (hE : ComplexMatrix2.ExpLogEstimates) (h : TopHypotheses (L := L) (n := n) (k := k) ρ₁ ρ r)
    (P : PauliCoordinates L n k) {z : TripleCoordIndex L n k → ℂ} (η : LevelForms L n k)
    (hz : ‖z‖ < ρ) (hη : ‖complexifyCoords (P.formCoords η)‖ < ρ) (c : PositiveEdge L n k k) :
    topLog (complexChainPoint z) η c = topTerm c (z, complexifyCoords (P.formCoords η)) := by
  have hm := expMove_complexChainPoint hS hE (z := z) (ε := complexifyCoords (P.formCoords η)) η
    (formCoords_fine_value P η) (formCoords_level_value P η) (h.prod _ _ hz hη)
  have e : (levelField (complexChainPoint z) k c.1)⁻¹ = adjugateL (topField z c) :=
    (adjugateL_eq_inv (h.det z (lt_of_lt_of_le hz h.sub) c)).symm
  simp only [topLog, topTerm, hm, e]
  rfl
private lemma line_pair_eq (P : PauliCoordinates L n k) (z : TripleCoordIndex L n k → ℂ)
    (ξ ξ' : LevelForms L n k) (s t : ℝ) :
    ((z, 0) : CoordPair L n k) + (s : ℂ) • ((0, complexifyCoords (P.formCoords ξ)) : CoordPair L n k) +
      (t : ℂ) • ((0, complexifyCoords (P.formCoords ξ')) : CoordPair L n k) =
    (z, complexifyCoords (P.formCoords (s • ξ + t • ξ'))) := by
  ext i
  · simp
  · simp [complexifyCoords]
private lemma topSecondVariation_eq (hS : PeriodicLattice.LogSeriesNearOne)
    (hE : ComplexMatrix2.ExpLogEstimates) (h : TopHypotheses (L := L) (n := n) (k := k) ρ₁ ρ r)
    (P : PauliCoordinates L n k) {z : TripleCoordIndex L n k → ℂ} (hz : ‖z‖ < ρ)
    (ξ ξ' : LevelForms L n k) (c : PositiveEdge L n k k) :
    topSecondVariation (complexChainPoint z) ξ ξ' c =
      secondDeriv (topTerm c) ((z, 0) : CoordPair L n k) (0, complexifyCoords (P.formCoords ξ))
        (0, complexifyCoords (P.formCoords ξ')) := by
  have hx : ‖((z, 0) : CoordPair L n k)‖ < ρ := by rwa [norm_basePair]
  rw [← deriv_deriv_line_eq (analyticAt_topTerm hS hE h c hx)]
  refine deriv_deriv_congr' ?_
  filter_upwards [eventually_norm_line_lt (u := (0, complexifyCoords (P.formCoords ξ)))
    (v := (0, complexifyCoords (P.formCoords ξ'))) hx] with w hw
  rw [line_pair_eq] at hw ⊢
  exact topLog_eq_topTerm hS hE h P _ hz (lt_of_le_of_lt (by
    rw [Prod.norm_def]
    exact le_max_right _ _) hw) c
private lemma topCoord_value (P : PauliCoordinates L n k) (x : TripleCoordIndex L n k → ℝ)
    (c : PositiveEdge L n k k) :
    ((tripleOfCoords P x).2.2 : Edge L n k k → ComplexMatrix2) c.1 =
      topCoordMatrix (complexifyCoords x) c := by
  have hm : ((tripleOfCoords P x).2.2 : Edge L n k k → ComplexMatrix2) c.1 ∈ ComplexMatrix2.traceless :=
    ((tripleOfCoords P x).2.2.2.1 c.1 c.2).2
  rw [topCoordMatrix, pauliSumL_apply]
  conv_lhs => rw [← sum_pauliCoordL_smul hm]
  refine Finset.sum_congr rfl fun a _ => ?_
  have e := P.topFormCoords_apply (tripleOfCoords P x).2.2 (a, c)
  simp only [toPauliCoeffs, restrictToPositiveEdges] at e
  rw [pauliCoeff_eq_pauliCoordL hm] at e
  rw [e]
  simp [tripleOfCoords, complexifyCoords]
private lemma traceFinsumPairing_eq (P : PauliCoordinates L n k) (x : TripleCoordIndex L n k → ℝ)
    (T : PositiveEdge L n k k → ComplexMatrix2) :
    traceFinsumPairing
        (restrictToPositiveEdges ((tripleOfCoords P x).2.2 : Edge L n k k → ComplexMatrix2)) T =
      ∑ c, (1 / 2 : ℂ) * traceCLM (topCoordMatrix (complexifyCoords x) c * T c) := by
  rw [traceFinsumPairing, finsum_eq_sum_of_fintype]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [restrictToPositiveEdges, topCoord_value]
  rfl
private theorem symKernel_tie (hS : PeriodicLattice.LogSeriesNearOne)
    (hE : ComplexMatrix2.ExpLogEstimates) (h : TopHypotheses (L := L) (n := n) (k := k) ρ₁ ρ r)
    (P : PauliCoordinates L n k) (x : TripleCoordIndex L n k → ℝ)
    (hpt : complexChainPoint (complexifyCoords x) = pointOfCoords P x)
    (hx : ‖complexifyCoords x‖ < ρ) (ξ ξ' : LevelForms L n k) :
    (((traceFinsumPairing
        (restrictToPositiveEdges ((tripleOfCoords P x).2.2 : Edge L n k k → ComplexMatrix2))
        (topSecondVariation (pointOfCoords P x) ξ ξ')).re : ℝ) : ℂ) =
      complexifyCoords (P.formCoords ξ) ⬝ᵥ
        (symKernel (complexifyCoords x)).mulVec (complexifyCoords (P.formCoords ξ')) := by
  rw [dot_symKernel, dot_holoKernel, traceFinsumPairing_eq, ← hpt]
  congr 2
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [topSecondVariation_eq hS hE h P hx ξ ξ' c]
end RealTie
private lemma norm_edgeMatrix_le {L n k : ℕ} [Fintype (LevelFormIndex L n k)]
    [Fintype (Fin 3 × PositiveEdge L n k k)] (f : LevelFormIndex L n k → ℂ) (p : LevelFormIndex L n k) :
    ‖edgeMatrix f p‖ ≤ pauliNormSum * ‖f‖ := by
  rw [edgeMatrix_eq_pauliSumL]
  exact norm_pauliSumL_le _ f
private lemma norm_formPart_le {L n k : ℕ} [Fintype (LevelFormIndex L n k)]
    [Fintype (Fin 3 × PositiveEdge L n k k)] (z : TripleCoordIndex L n k → ℂ) :
    ‖formPart z‖ ≤ ‖z‖ :=
  (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => norm_le_pi_norm z (.inl i)
private lemma exists_radii (hS : PeriodicLattice.LogSeriesNearOne) {ρ₀ C₀ : ℝ} (hρ₀ : 0 < ρ₀)
    (hC₀ : 0 ≤ C₀) : ∃ ρ₁ ρ : ℝ, 0 < ρ ∧ ρ ≤ ρ₁ ∧ ρ₁ ≤ ρ₀ ∧ C₀ * ρ₁ ≤ 1 / 8 ∧
      ∀ (L n k : ℕ) [Fintype (LevelFormIndex L n k)] [Fintype (Fin 3 × PositiveEdge L n k k)]
        (z : TripleCoordIndex L n k → ℂ) (ε : LevelFormIndex L n k → ℂ), ‖z‖ < ρ → ‖ε‖ < ρ →
        (∀ p, ‖expProd (edgeMatrix ε p) (edgeMatrix (formPart z) p) - 1‖ < 9 / 10) ∧
          ‖movedCoords z ε‖ < ρ₁ := by
  set ρ₁ := min ρ₀ (1 / (8 * (C₀ + 1))) with hρ₁d
  have hρ₁ : 0 < ρ₁ := lt_min hρ₀ (by positivity)
  obtain ⟨δ, hδ, hj⟩ := exists_small_expProdLog hS hρ₁
  have hK := pauliNormSum_nonneg
  set ρ := min ρ₁ (δ / (pauliNormSum + 1)) with hρd
  have hρ : 0 < ρ := lt_min hρ₁ (by positivity)
  have hsmall : ∀ t : ℝ, 0 ≤ t → t < ρ → pauliNormSum * t < δ := by
    intro t ht0 ht
    have h1 : t < δ / (pauliNormSum + 1) := lt_of_lt_of_le ht (min_le_right _ _)
    rw [lt_div_iff₀ (by linarith)] at h1
    nlinarith
  refine ⟨ρ₁, ρ, hρ, min_le_left _ _, min_le_left _ _, ?_, ?_⟩
  · have h1 : ρ₁ ≤ 1 / (8 * (C₀ + 1)) := min_le_right _ _
    calc C₀ * ρ₁ ≤ C₀ * (1 / (8 * (C₀ + 1))) := mul_le_mul_of_nonneg_left h1 hC₀
      _ ≤ 1 / 8 := by
        rw [mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
        linarith
  · intro L n k _ _ z ε hz hε
    have hA : ∀ p, ‖edgeMatrix ε p‖ < δ := fun p =>
      lt_of_le_of_lt (norm_edgeMatrix_le ε p) (hsmall _ (norm_nonneg _) hε)
    have hB : ∀ p, ‖edgeMatrix (formPart z) p‖ < δ := fun p =>
      lt_of_le_of_lt (norm_edgeMatrix_le _ p)
        (hsmall _ (norm_nonneg _) (lt_of_le_of_lt (norm_formPart_le z) hz))
    refine ⟨fun p => (hj _ _ (hA p) (hB p)).1, ?_⟩
    refine (pi_norm_lt_iff hρ₁).2 fun i => ?_
    rcases i with p | r
    · exact (hj _ _ (hA p) (hB p)).2 _
    · exact lt_of_le_of_lt (norm_le_pi_norm z _) (lt_of_lt_of_le hz (min_le_left _ _))
private lemma topHypotheses_of_fields {L n k : ℕ} [Fintype (LevelFormIndex L n k)]
    [Fintype (Fin 3 × PositiveEdge L n k k)]
    {ρ₀ C₀ r₀ ρ₁ ρ : ℝ} (hρ : 0 < ρ) (hsub : ρ ≤ ρ₁) (hρ₁ : ρ₁ ≤ ρ₀) (hC₀ : 0 ≤ C₀)
    (hC : C₀ * ρ₁ ≤ 1 / 8) (hr₀ : 0 ≤ r₀)
    (hroom : ∀ (z : TripleCoordIndex L n k → ℂ) (ε : LevelFormIndex L n k → ℂ), ‖z‖ < ρ → ‖ε‖ < ρ →
      (∀ p, ‖expProd (edgeMatrix ε p) (edgeMatrix (formPart z) p) - 1‖ < 9 / 10) ∧
        ‖movedCoords z ε‖ < ρ₁)
    (hcfg : ∀ j ≤ k, ∀ z ∈ Metric.ball (0 : TripleCoordIndex L n k → ℂ) ρ₀,
      levelField (complexChainPoint z) j ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup)
    (hf : ∀ j ≤ k, ∀ b : Edge L n k j,
      AnalyticOnNhd ℂ (fun z => levelField (complexChainPoint z) j b) (Metric.ball 0 ρ₀) ∧
      (∀ z ∈ Metric.ball (0 : TripleCoordIndex L n k → ℂ) ρ₀,
        ComplexMatrix2.operatorNorm (levelField (complexChainPoint z) j b - 1) ≤ C₀ * ‖z‖) ∧
      ∀ z ∈ Metric.ball (0 : TripleCoordIndex L n k → ℂ) ρ₀,
        ∀ z' ∈ Metric.ball (0 : TripleCoordIndex L n k → ℂ) ρ₀,
        (∀ i, cellDist (tripleCoordIndexCell i) (levelVertexCell b.source) ≤ r₀ → z i = z' i) →
          levelField (complexChainPoint z) j b = levelField (complexChainPoint z') j b) :
    TopHypotheses (L := L) (n := n) (k := k) ρ₁ ρ r₀ := by
  have mem : ∀ z : TripleCoordIndex L n k → ℂ, ‖z‖ < ρ₁ →
      z ∈ Metric.ball (0 : TripleCoordIndex L n k → ℂ) ρ₀ :=
    fun z hz => by simpa using lt_of_lt_of_le hz hρ₁
  refine ⟨hρ, hsub, hr₀, fun z hz c => ?_, fun z hz c => ?_, fun c z hz => ?_,
    fun c z z' hz hz' he => ?_, fun z ε hz hε => (hroom z ε hz hε).1,
    fun z ε hz hε => (hroom z ε hz hε).2⟩
  · exact (hcfg k le_rfl z (mem z hz)).1 c.1 (Set.mem_univ _)
  · refine ((hf k le_rfl c.1).2.1 z (mem z hz)).trans ?_
    exact (mul_le_mul_of_nonneg_left hz.le hC₀).trans hC
  · exact (hf k le_rfl c.1).1 z (mem z hz)
  · exact (hf k le_rfl c.1).2.2 z (mem z hz) z' (mem z' hz') he
open Classical in
private lemma card_topCell_le {L n k : ℕ} (hLat : PeriodicLattice.CoordinateDescription)
    (hCell : NeighbouringFineVertexCells) (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n)
    [Fintype (PositiveEdge L n k k)] (y : Vertex L n k k) :
    (Finset.univ.filter fun c : PositiveEdge L n k k => topCell c = y).card ≤
      Fintype.card (Fin 4) * L ^ (4 * k) := by
  obtain ⟨hf, hc, hm⟩ := refinedBlock_facts (k := k) hLat hCell hL hn y
  rw [← hc]
  refine card_fibre_le (ι := PositiveEdge L n k k) topCell y
    (fun c => (c.1.source : PeriodicLattice.FourTorus L n)) axisOf _ hf ?_ ?_
  · intro c hc'
    exact hm le_rfl c.1.source hc'
  · exact fun p q _ _ hl hp => edge_eq p q hp hl
end TopSecondVariationLocal
open TopSecondVariationLocal in
theorem topSecondVariationIsLocal_holds
    (hF : LevelFieldsHolomorphicAndLocal)
    (hB : ComplexAnalysis.BoundedLineHolomorphicIsAnalytic)
    (hM : PeriodicLattice.ElementaryStepFacts)
    (hE : ComplexMatrix2.ExpLogEstimates)
    (hLat : PeriodicLattice.CoordinateDescription)
    (hCell : NeighbouringFineVertexCells) :
    TopSecondVariationIsLocal := by
  intro L hL k hk
  obtain ⟨ρ₀, C₀, r₀, hρ₀, hC₀, hr₀, hev⟩ := hF L hL k hk
  have hS : PeriodicLattice.LogSeriesNearOne :=
    (hM L 1 1 0 hL Nat.one_pos Nat.one_pos).2.2.1
  obtain ⟨ρ₁, ρ, hρ, hsub, hρ₁, hC, hroom⟩ := exists_radii hS hρ₀ hC₀
  set NT : ℕ := Fintype.card (Fin 4) * L ^ (4 * k) * (intBox r₀).card with hNT
  set NJ : ℕ := Fintype.card (FormLabel k) * L ^ (4 * k) * (intBox (2 * r₀)).card with hNJ
  refine ⟨ρ / 2, NJ * (NT * entryCap ρ), 2 * r₀, by positivity,
    mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (entryCap_nonneg hρ)),
    by positivity, ?_⟩
  filter_upwards [hev, eventually_gt_atTop 0] with n hn hn0
  intro _ _ _ _ _ _ _ _ _ P
  classical
  obtain ⟨hpt, hcfg, hf, -⟩ := hn P
  have hfin : Finite (PositiveEdge L n k k) :=
    Finite.of_injective (fun c => ((0 : Fin 3), c)) fun a b e => (Prod.ext_iff.1 e).2
  letI : Fintype (PositiveEdge L n k k) := Fintype.ofFinite _
  have hs : TopHypotheses (L := L) (n := n) (k := k) ρ₁ ρ r₀ :=
    topHypotheses_of_fields hρ hsub hρ₁ hC₀ hC hr₀ (hroom L n k) hcfg hf
  have hcell := hCell L hL n k
  have hd : CellDistIsMetric L n k := ⟨hcell.1, hcell.2.1⟩
  have hcT : ∀ y : Vertex L n k k, (Finset.univ.filter fun c : PositiveEdge L n k k =>
      cellDist (topCell c) y ≤ r₀).card ≤ NT := fun y =>
    card_near_le' hLat hL hn0 topCell (fun y => card_topCell_le hLat hCell hL hn0 y) y r₀
  have hcJ : ∀ y : Vertex L n k k, (Finset.univ.filter fun p : LevelFormIndex L n k =>
      cellDist (levelFormIndexCell p) y ≤ 2 * r₀).card ≤ NJ := fun y =>
    card_near_le' hLat hL hn0 levelFormIndexCell
      (fun y => card_form_cell hLat hCell hL hn0 y) y (2 * r₀)
  refine ⟨symKernel, symKernel_isLocallyHolomorphic hB hS hE hs hd hcT hcJ, ?_⟩
  have hball : ∀ᶠ x : TripleCoordIndex L n k → ℝ in 𝓝 0, ‖complexifyCoords x‖ < ρ := by
    have hc : Continuous fun x : TripleCoordIndex L n k → ℝ => ‖complexifyCoords x‖ := by
      refine (continuous_pi fun i => ?_).norm
      exact Complex.continuous_ofReal.comp (continuous_apply i)
    have h0 : ‖complexifyCoords (0 : TripleCoordIndex L n k → ℝ)‖ < ρ := by
      have : complexifyCoords (0 : TripleCoordIndex L n k → ℝ) = 0 := by
        funext i
        simp [complexifyCoords]
      rw [this, norm_zero]
      exact hρ
    exact hc.continuousAt.eventually (gt_mem_nhds h0)
  filter_upwards [hball] with x hx ξ ξ'
  exact symKernel_tie hS hE hs P x (hpt x) hx ξ ξ'
end RunningCouplingSlope
end YangMills.Construction
end
