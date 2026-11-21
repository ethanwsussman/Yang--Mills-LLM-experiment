import YangMills.Construction.Lattice.GaugeCovarianceOfHolonomyProof
import YangMills.Construction.Towers.AveragedContoursOnThePolydiscs
import YangMills.Construction.Towers.BlocksOfATower
import YangMills.Construction.Towers.ConfigurationsFormedLevelByLevelOnThePolydiscsProof
import YangMills.Construction.Towers.CovariantDifferenceRelationsOfAStepOfASide
import YangMills.Construction.Towers.CurvesAtAFiniteSideInTheLeftChart
import YangMills.Construction.Towers.GaugeDirectionsInTheLeftChart
import YangMills.Construction.Towers.LinearityOfTheCovariantMapsOfAStepOnTheSides
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Set Filter YangMills.Construction.Matrices YangMills.Construction.Matrices.GroupLieProduct
open scoped Topology Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.Tower.CovDiffStep
open YangMills.Construction.Tower.MeanStableFields (fieldsNearOne IsHolomorphicOnFields)
variable {L n k j j' : ℕ}
theorem opposite_isPositivelyOriented_of_not {e : Edge L n k j} (he : ¬ e.IsPositivelyOriented) :
    e.opposite.IsPositivelyOriented := by apply _root_.YangMills.Construction.Tower.IteratedMeans.opposite_isPositivelyOriented_of_not <;> assumption
theorem forwardFrom_isPositivelyOriented (y : Vertex L n k j) (μ : Fin 4) :
    (PeriodicLattice.Bond.forwardFrom y μ : Edge L n k j).IsPositivelyOriented :=
  ⟨μ, by show y + PeriodicLattice.unitStep L n _ μ - y = _; abel⟩
theorem extendOddly_congr {f g : Edge L n k j → ComplexMatrix2}
    (h : ∀ c : Edge L n k j, c.IsPositivelyOriented → f c = g c) : extendOddly f = extendOddly g := by
  funext e
  unfold extendOddly
  by_cases he : e.IsPositivelyOriented
  · simp only [if_pos he, h e he]
  · simp only [if_neg he, h _ (opposite_isPositivelyOriented_of_not he)]
theorem inv_mem_unitDeterminant {X : ComplexMatrix2} (h : X ∈ ComplexMatrix2.unitDeterminant) :
    X⁻¹ ∈ ComplexMatrix2.unitDeterminant := by apply _root_.YangMills.SharedProofs.p413 <;> assumption
theorem inv_inv_of_mem_unitDeterminant {X : ComplexMatrix2}
    (h : X ∈ ComplexMatrix2.unitDeterminant) : X⁻¹⁻¹ = X := by apply _root_.YangMills.Construction.Tower.LevelwiseMeans.inv_inv_of_mem_unitDeterminant <;> assumption
theorem mul_inv_of_mem_unitDeterminant {X : ComplexMatrix2}
    (h : X ∈ ComplexMatrix2.unitDeterminant) : X * X⁻¹ = 1 := by apply _root_.YangMills.DeltaSharedProofs.p2618 <;> assumption
theorem fieldOfPositiveValues_restrict
    {V : Edge L n k j → ComplexMatrix2} (hV : V ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup) :
    fieldOfPositiveValues (restrictToPositiveEdges V) = V := by
  funext e
  unfold fieldOfPositiveValues
  by_cases he : e.IsPositivelyOriented
  · rw [dif_pos he]
    rfl
  · rw [dif_neg he, dif_pos (opposite_isPositivelyOriented_of_not he)]
    show (V e.opposite)⁻¹ = V e
    rw [hV.2 e trivial]
    exact inv_inv_of_mem_unitDeterminant (hV.1 e trivial)
theorem fieldOfPositiveValues_mem
    (ho : ∀ e : Edge L n k j, Xor e.IsPositivelyOriented e.opposite.IsPositivelyOriented)
    {w : PositiveEdge L n k j → ComplexMatrix2} (hw : ∀ c, w c ∈ ComplexMatrix2.unitDeterminant) :
    fieldOfPositiveValues w ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup := by
  refine ⟨fun e _ => ?_, fun e _ => ?_⟩
  · unfold fieldOfPositiveValues
    by_cases he : e.IsPositivelyOriented
    · rw [dif_pos he]
      exact hw _
    · rw [dif_neg he, dif_pos (opposite_isPositivelyOriented_of_not he)]
      exact inv_mem_unitDeterminant (hw _)
  · unfold fieldOfPositiveValues
    by_cases he : e.IsPositivelyOriented
    · have hr : ¬ e.opposite.IsPositivelyOriented := by
        rcases ho e with h | h
        · exact h.2
        · exact absurd he h.2
      rw [dif_pos he, dif_neg hr, dif_pos (show e.opposite.opposite.IsPositivelyOriented from he)]
      rfl
    · rw [dif_neg he, dif_pos (opposite_isPositivelyOriented_of_not he),
        dif_pos (opposite_isPositivelyOriented_of_not he)]
      exact (inv_inv_of_mem_unitDeterminant (hw _)).symm
theorem isHolomorphicFieldMap_of_components {β : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless}
    {D : Set (Edge L n k j → ComplexMatrix2)} {F : (Edge L n k j → ComplexMatrix2) → Edge L n k j' → ComplexMatrix2}
    (hD : IsOpenFieldSet PeriodicLattice.complexGaugeGroup D)
    (hc : MapsTo F D (fieldsIn L n k j' PeriodicLattice.complexGaugeGroup))
    (hF : ∀ c : Edge L n k j', c.IsPositivelyOriented → IsHolomorphicOnFields β D fun V => F V c)
    (fin : Fintype (PositiveEdge L n k j')) {c₀ : Edge L n k j'} (hc₀ : c₀.IsPositivelyOriented) :
    IsHolomorphicFieldMap β D F := by
  obtain ⟨-, inst, h₀⟩ := hF c₀ hc₀
  refine ⟨hD, hc, inst, fin, h₀.1, fun c => ?_, fun e => e.elim⟩
  obtain ⟨-, inst', h⟩ := hF c.1 c.2
  obtain rfl : inst' = inst := Subsingleton.elim _ _
  exact h
theorem apply_mem_unitDeterminant {β : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless}
    {D : Set (Edge L n k j → ComplexMatrix2)}
    {h : (Edge L n k j → ComplexMatrix2) → ComplexMatrix2} (hh : IsHolomorphicOnFields β D h)
    {V : Edge L n k j → ComplexMatrix2} (hV : V ∈ D) : h V ∈ ComplexMatrix2.unitDeterminant := by
  obtain ⟨hD, inst, hg⟩ := hh
  have h1 := hg.2.1 (⟨_, ⟨V, hV, rfl⟩, rfl⟩ :
    asGroupFactors (restrictToPositiveEdges V) ∈ asGroupFactors '' (restrictToPositiveEdges '' D))
  have h2 : fieldOfPositiveValues (fun e => asGroupFactors (restrictToPositiveEdges V) (.inl e)) = V :=
    fieldOfPositiveValues_restrict (hD.1 hV)
  simpa only [h2] using h1
theorem complexBlockAverageStep_eq {i : ℕ} (V : Edge L n k i → ComplexMatrix2) :
    PeriodicLattice.complexBlockAverageStep i V =
      fieldOfPositiveValues fun c : PositiveEdge L n k (i + 1) =>
        PeriodicLattice.complexBlockAverage V c.1 := by
  funext e
  unfold fieldOfPositiveValues
  by_cases he : e.IsPositivelyOriented
  · rw [dif_pos he]
    rfl
  · have hr := opposite_isPositivelyOriented_of_not he
    rw [dif_neg he, dif_pos hr]
    unfold PeriodicLattice.complexBlockAverageStep PeriodicLattice.complexBlockAverage
    rw [if_neg he]
    exact congrArg (·⁻¹) (if_pos hr).symm
theorem curveTangent_congr {γ₁ γ₂ : ℝ → Edge L n k j' → ComplexMatrix2}
    (h : ∀ c : Edge L n k j', c.IsPositivelyOriented → (fun t => γ₁ t c) =ᶠ[𝓝 0] fun t => γ₂ t c) :
    curveTangent γ₁ = curveTangent γ₂ := by
  unfold curveTangent
  refine extendOddly_congr fun c hc => ?_
  have e : γ₁ 0 c = γ₂ 0 c := (h c hc).self_of_nhds
  rw [(h c hc).deriv_eq, e]
theorem covDiff_neg (V : Edge L n k j → ComplexMatrix2) (l : Vertex L n k j → ComplexMatrix2) :
    covDiff V (-l) = -covDiff V l := by
  funext e
  simp only [covDiff, extendOddly, Pi.neg_apply, ComplexMatrix2.conjugateBy]
  split_ifs <;> simp <;> abel
theorem covDiff_smul_add (V : Edge L n k j → ComplexMatrix2) (c : ℂ)
    (l l' : Vertex L n k j → ComplexMatrix2) :
    covDiff V (c • l + l') = c • covDiff V l + covDiff V l' := by
  funext e
  simp only [covDiff, extendOddly, Pi.add_apply, Pi.smul_apply, ComplexMatrix2.conjugateBy]
  split_ifs <;> simp only [mul_add, add_mul, Matrix.mul_smul, Matrix.smul_mul, smul_sub, smul_neg] <;>
    abel
theorem hasDerivAt_matExp_I_smul (a : ComplexMatrix2) (s : ℝ) :
    HasDerivAt (fun t : ℝ => ComplexMatrix2.matExp (Complex.I • ((t : ℂ) • a)))
      (ComplexMatrix2.matExp ((s : ℂ) • (Complex.I • a)) * (Complex.I • a)) s := by
  have h₁ := hasDerivAt_exp_smul_const (𝕂 := ℂ) (Complex.I • a) (s : ℂ)
  have hr : HasDerivAt (fun t : ℝ => ((t : ℂ))) (1 : ℂ) s := Complex.ofRealCLM.hasDerivAt
  have h' := HasDerivAt.scomp s (h := fun t : ℝ => ((t : ℂ))) h₁ hr
  rw [one_smul] at h'
  have e : (fun t : ℝ => ComplexMatrix2.matExp (Complex.I • ((t : ℂ) • a))) =
      (fun z : ℂ => ComplexMatrix2.matExp (z • (Complex.I • a))) ∘ fun t : ℝ => (t : ℂ) := by
    funext t
    simp only [Function.comp]
    rw [smul_comm Complex.I (t : ℂ) a]
  rw [e]
  exact h'
theorem matExp_inv (Z : ComplexMatrix2) :
    (ComplexMatrix2.matExp Z)⁻¹ = ComplexMatrix2.matExp (-Z) := (Matrix.exp_neg Z).symm
theorem hasDerivAt_conjugatedCurve (a c H : ComplexMatrix2) (s : ℝ) :
    HasDerivAt (fun t : ℝ => ComplexMatrix2.matExp (Complex.I • ((t : ℂ) • a)) * H *
      (ComplexMatrix2.matExp (Complex.I • ((t : ℂ) • c)))⁻¹)
      (ComplexMatrix2.matExp ((s : ℂ) • (Complex.I • a)) * (Complex.I • a) * H *
          ComplexMatrix2.matExp (Complex.I • ((s : ℂ) • (-c))) +
        ComplexMatrix2.matExp (Complex.I • ((s : ℂ) • a)) * H *
          (ComplexMatrix2.matExp ((s : ℂ) • (Complex.I • (-c))) * (Complex.I • (-c)))) s := by
  have e : (fun t : ℝ => ComplexMatrix2.matExp (Complex.I • ((t : ℂ) • a)) * H *
      (ComplexMatrix2.matExp (Complex.I • ((t : ℂ) • c)))⁻¹) =
      (fun t : ℝ => ComplexMatrix2.matExp (Complex.I • ((t : ℂ) • a)) * H) *
        (fun t : ℝ => ComplexMatrix2.matExp (Complex.I • ((t : ℂ) • (-c)))) := by
    funext t
    simp only [Pi.mul_apply]
    rw [matExp_inv, smul_neg, smul_neg]
  rw [e]
  exact ((hasDerivAt_matExp_I_smul a s).mul_const H).mul (hasDerivAt_matExp_I_smul (-c) s)
theorem matExp_eq_one {z : ComplexMatrix2} (h : z = 0) : ComplexMatrix2.matExp z = 1 := by
  rw [h]
  exact NormedSpace.exp_zero
theorem deriv_conjugatedCurve (a c H : ComplexMatrix2) (hH : H ∈ ComplexMatrix2.unitDeterminant) :
    Complex.I⁻¹ • (deriv (fun t : ℝ => ComplexMatrix2.matExp (Complex.I • ((t : ℂ) • a)) * H *
      (ComplexMatrix2.matExp (Complex.I • ((t : ℂ) • c)))⁻¹) 0 * H⁻¹) =
      a - ComplexMatrix2.conjugateBy H c := by
  rw [(hasDerivAt_conjugatedCurve a c H 0).deriv]
  rw [matExp_eq_one (z := ((0 : ℝ) : ℂ) • (Complex.I • a)) (by simp),
    matExp_eq_one (z := Complex.I • (((0 : ℝ) : ℂ) • a)) (by simp),
    matExp_eq_one (z := ((0 : ℝ) : ℂ) • (Complex.I • (-c))) (by simp),
    matExp_eq_one (z := Complex.I • (((0 : ℝ) : ℂ) • (-c))) (by simp)]
  have hI : Complex.I⁻¹ * Complex.I = 1 := inv_mul_cancel₀ Complex.I_ne_zero
  simp only [one_mul, mul_one, add_mul, Matrix.smul_mul, Matrix.mul_smul, smul_add, smul_smul, hI,
    one_smul, mul_neg, neg_mul, smul_neg, ComplexMatrix2.conjugateBy, mul_assoc,
    mul_inv_of_mem_unitDeterminant hH]
  abel
def gaugeOrbitCurve (V : Edge L n k j → ComplexMatrix2) (l : Vertex L n k j → ComplexMatrix2) (t : ℝ) :
    Edge L n k j → ComplexMatrix2 :=
  PeriodicLattice.gaugeTransform (expVertexFn ((t : ℂ) • l)) V
theorem gaugeOrbitCurve_zero (V : Edge L n k j → ComplexMatrix2) (l : Vertex L n k j → ComplexMatrix2) :
    gaugeOrbitCurve V l 0 = V := by
  funext e
  simp [gaugeOrbitCurve, PeriodicLattice.gaugeTransform, expVertexFn, ComplexMatrix2.matExp,
    NormedSpace.exp_zero]
theorem gaugeTransform_mem {V : Edge L n k j → ComplexMatrix2}
    (hV : V ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup)
    {u : Vertex L n k j → ComplexMatrix2} (hu : u ∈ gaugeGroupAt L n k j) :
    PeriodicLattice.gaugeTransform u V ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup := by
  have hd : ∀ x, u x ∈ ComplexMatrix2.unitDeterminant := fun x =>
    (Matrix.mem_specialUnitaryGroup_iff.1 (hu x)).2
  refine ⟨fun e _ => ?_, fun e _ => ?_⟩
  · have h1 : (V e).det = 1 := hV.1 e trivial
    have h2 : (u e.source).det = 1 := hd _
    have h3 : ((u e.target)⁻¹).det = 1 := inv_mem_unitDeterminant (hd _)
    show (u e.source * V e * (u e.target)⁻¹).det = 1
    rw [Matrix.det_mul, Matrix.det_mul, h1, h2, h3]
    simp
  · show u e.target * V e.opposite * (u e.source)⁻¹ = (u e.source * V e * (u e.target)⁻¹)⁻¹
    rw [hV.2 e trivial, Matrix.mul_inv_rev, Matrix.mul_inv_rev, inv_inv_of_mem_unitDeterminant (hd _),
      mul_assoc]
variable (hI : ComplexMatrix2.UnitaryLogarithmProperties)
include hI
theorem expVertexFn_mem {l : Vertex L n k j → ComplexMatrix2}
    (hl : ∀ x, l x ∈ ComplexMatrix2.hermitianTraceless) (t : ℝ) :
    expVertexFn ((t : ℂ) • l) ∈ gaugeGroupAt L n k j := by
  intro z
  have hz : (t : ℂ) • l z ∈ ComplexMatrix2.hermitianTraceless := by
    have := ComplexMatrix2.hermitianTraceless.smul_mem t (hl z)
    simpa [Complex.coe_smul] using this
  exact (hI.1 _ hz).2.2.2
theorem gaugeOrbitCurve_isDifferentiable {V : Edge L n k j → ComplexMatrix2}
    (hV : V ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup)
    {l : Vertex L n k j → ComplexMatrix2} (hl : ∀ x, l x ∈ ComplexMatrix2.hermitianTraceless) :
    IsDifferentiableFieldCurve PeriodicLattice.complexGaugeGroup univ (gaugeOrbitCurve V l) :=
  ⟨⟨isOpen_univ, ordConnected_univ, mem_univ _⟩,
    fun t _ => gaugeTransform_mem hV (expVertexFn_mem hI hl t),
    fun e _ t _ =>
      (hasDerivAt_conjugatedCurve (l e.source) (l e.target) (V e) t).differentiableAt.differentiableWithinAt⟩
section HermitianDirections
omit hI
theorem weight_finsum_const (hL : L ≠ 0) {y : Vertex L n k (j + 1)}
    (hsub : PeriodicLattice.unitBlock y ⊆
      (PeriodicLattice.sublattice L n (PeriodicLattice.levelDepth k j) :
        Set (PeriodicLattice.FourTorus L n)))
    (hcard : (PeriodicLattice.unitBlock y).ncard = L ^ 4) (v : ComplexMatrix2) :
    (PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y).Finite ∧
      PeriodicLattice.inverseFourthPowerWeight L •
        ∑ᶠ _x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y, v = v := by
  have hpos : 0 < (PeriodicLattice.unitBlock y).ncard := by
    rw [hcard]
    exact pow_pos (Nat.pos_of_ne_zero hL) 4
  have hb : (PeriodicLattice.unitBlock y).Finite := Set.finite_of_ncard_pos hpos
  have hfin : (PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y).Finite :=
    Set.Finite.of_finite_image (f := Subtype.val)
      (hb.subset (by rintro _ ⟨x, hx, rfl⟩; exact hx)) Subtype.val_injective.injOn
  refine ⟨hfin, ?_⟩
  have himage : Subtype.val '' (PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y) =
      PeriodicLattice.unitBlock y := by
    ext p
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro hp
      exact ⟨⟨p, hsub hp⟩, hp, rfl⟩
  have hcount : (PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y).ncard = L ^ 4 := by
    rw [← hcard, ← himage, Set.ncard_image_of_injective _ Subtype.val_injective]
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin, Finset.sum_const,
    ← Set.ncard_eq_toFinset_card _ hfin, hcount, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  have hL' : (L : ℝ) ≠ 0 := by exact_mod_cast hL
  have e : PeriodicLattice.inverseFourthPowerWeight L * ((L ^ 4 : ℕ) : ℂ) = 1 := by
    have e' : (L : ℝ) ^ (-4 : ℤ) * ((L ^ 4 : ℕ) : ℝ) = 1 := by
      rw [zpow_neg]
      push_cast
      rw [show ((4 : ℤ)) = ((4 : ℕ) : ℤ) from rfl, zpow_natCast]
      exact inv_mul_cancel₀ (pow_ne_zero 4 hL')
    unfold PeriodicLattice.inverseFourthPowerWeight
    exact_mod_cast congrArg (fun r : ℝ => (r : ℂ)) e'
  rw [e, one_smul]
include hI
variable (hS : SmoothingNearIdentity)
  (hP1 : MeanStableFields.MeanStableFieldsHold)
  (hCu : FiniteLevelCurveDifferentials.Statement)
  (hGD : GaugeOrbitTangentInLeftChart.Statement)
  (hE : PeriodicLattice.BondEndpointsOrientation.Statement)
  (hE6 : BondSetFields.ProductStructureHolds)
  (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hj : j < k)
  {V : Edge L n k j → ComplexMatrix2} (hV : V ∈ smallComplexFields L n k j)
  {l : Vertex L n k j → ComplexMatrix2} (hl : ∀ x, l x ∈ ComplexMatrix2.hermitianTraceless)
include hS hP1 hCu hGD hE hE6 hL hn hj hV hl
theorem xor_isPositivelyOriented (e : Edge L n k (j + 1)) :
    Xor e.IsPositivelyOriented e.opposite.IsPositivelyOriented :=
  ((hE ⟨L, hL, ⟨k, by omega⟩, ⟨n, hn⟩⟩ (j + 1) hj).2.2.2 e).2.2.2.2.2
theorem curveTangent_gaugeOrbitCurve :
    curveTangent (gaugeOrbitCurve V (-l)) = covDiff V l := by
  have h := (((hGD L k j hL hj.le).1 n hn).1 V hV.1 (-l)
    (fun x => ComplexMatrix2.traceless.neg_mem (hl x).2)).2.2.1
  show curveTangent (fun t : ℝ => PeriodicLattice.gaugeTransform
    (expVertexFn ((t : ℂ) • (-l))) V) = _
  rw [h, covDiff_neg, neg_neg]
theorem complexSmoothingDeriv_covDiff_hermitian :
    complexSmoothingDeriv V (covDiff V l) =
      covDiff (PeriodicLattice.complexBlockAverageStep j V) (restrictVertexFunction (j + 1) l) := by
  have hk : 1 ≤ k := by omega
  have hP' := (hP1 L hL k hk).1 n hn
  have hfinb : Finite (Edge L n k (j + 1)) :=
    Set.finite_univ_iff.1 ((hE6 L hL k (j + 1) hj).1 n hn).2.1
  have fin : Fintype (PositiveEdge L n k (j + 1)) := Fintype.ofFinite _
  let β : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless := OneLoop.pauliBasis
  have ho := xor_isPositivelyOriented hI hS hP1 hCu hGD hE hE6 hL hn hj hV hl
  have hmaps : MapsTo (PeriodicLattice.complexBlockAverageStep (L := L) (m := n) (K := k) j)
      (fieldsNearOne L n k j)
      (fieldsIn L n k (j + 1) PeriodicLattice.complexGaugeGroup) := by
    intro W hW
    rw [complexBlockAverageStep_eq]
    exact fieldOfPositiveValues_mem ho fun c =>
      apply_mem_unitDeterminant (hP'.holomorphic_smoothing j hj c.1 c.2 β) hW
  have hhol : IsHolomorphicFieldMap β (fieldsNearOne L n k j)
      (PeriodicLattice.complexBlockAverageStep (L := L) (m := n) (K := k) j) :=
    isHolomorphicFieldMap_of_components (hP'.isOpen_nearOne j hj) hmaps
      (fun c hc => hP'.holomorphic_smoothing j hj c hc β) fin
      (forwardFrom_isPositivelyOriented (0 : Vertex L n k (j + 1)) 0)
  have hl' : ∀ x, (-l) x ∈ ComplexMatrix2.hermitianTraceless := fun x =>
    ComplexMatrix2.hermitianTraceless.neg_mem (hl x)
  have h1 := ((hCu L k j (j + 1) hL hj.le hj n hn).2.2.1 β _ _ hhol V hV) univ (gaugeOrbitCurve V (-l))
    (gaugeOrbitCurve_isDifferentiable hI hV.1 hl') (gaugeOrbitCurve_zero V _)
  have t1 := h1.2
  rw [curveTangent_gaugeOrbitCurve hI hS hP1 hCu hGD hE hE6 hL hn hj hV hl] at t1
  show holLeftDifferential _ _ _ = _
  rw [← t1]
  have hMV : PeriodicLattice.complexBlockAverageStep j V ∈
      fieldsIn L n k (j + 1) PeriodicLattice.complexGaugeGroup := hmaps hV
  have hr : ∀ y, restrictVertexFunction (j + 1) (-l) y ∈ ComplexMatrix2.traceless := fun y =>
    (hl' _).2
  have h2 := (((hGD L k (j + 1) hL hj).1 n hn).1 _ hMV (restrictVertexFunction (j + 1) (-l)) hr).2.2.1
  have hneg : covDiff (PeriodicLattice.complexBlockAverageStep j V) (restrictVertexFunction (j + 1) l) =
      -covDiff (PeriodicLattice.complexBlockAverageStep j V) (restrictVertexFunction (j + 1) (-l)) := by
    rw [← covDiff_neg]
    congr 1
    funext y
    show l _ = -(-l _)
    rw [neg_neg]
  rw [hneg, ← h2]
  refine curveTangent_congr fun c hc => Eventually.of_forall fun t => ?_
  have hpoly := hP'.mem_polydisc j hj c hc V hV
  have hcov := ((hS.1 L hL).2.2.periodic n k j hn hj c hc).gauge_covariant V hpoly
    (expVertexFn ((t : ℂ) • (-l))) (expVertexFn_mem hI hl' t)
  exact hcov.2.1
theorem logDeriv_contour_hermitian (hO2 : PolydiscContours.ContourHolomorphyHolds)
    (y : Vertex L n k (j + 1)) {x : Vertex L n k j}
    (hx : x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y) :
    logDirectionalDeriv ℂ
      (fun X => PeriodicLattice.complexMeanContourHolonomy (PeriodicLattice.expTwist X V) y x)
      (PeriodicLattice.complexMeanContourHolonomy V y x) (covDiff V l) =
      ComplexMatrix2.conjugateBy (PeriodicLattice.complexMeanContourHolonomy V y x) (l x) -
        restrictVertexFunction (j + 1) l y := by
  have hk : 1 ≤ k := by omega
  have hP' := (hP1 L hL k hk).1 n hn
  have hfinb : Finite (Edge L n k (j + 1)) :=
    Set.finite_univ_iff.1 ((hE6 L hL k (j + 1) hj).1 n hn).2.1
  have fin : Fintype (PositiveEdge L n k (j + 1)) := Fintype.ofFinite _
  let β : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless := OneLoop.pauliBasis
  have ho := xor_isPositivelyOriented hI hS hP1 hCu hGD hE hE6 hL hn hj hV hl
  have hc : (PeriodicLattice.Bond.forwardFrom y 0 : Edge L n k (j + 1)).IsPositivelyOriented :=
    forwardFrom_isPositivelyOriented y 0
  have hy : y ∈ ({(PeriodicLattice.Bond.forwardFrom y 0 : Edge L n k (j + 1)).source,
      (PeriodicLattice.Bond.forwardFrom y 0 : Edge L n k (j + 1)).target} :
      Set (Vertex L n k (j + 1))) := Or.inl rfl
  have hg := (((hO2 L hL k j hj).1 n hn _ hc).holomorphicOn_fieldsNearOne y hy x hx).isHolomorphicOnFields β
  let h : (Edge L n k j → ComplexMatrix2) → ComplexMatrix2 :=
    fun W => PeriodicLattice.complexMeanContourHolonomy W y x
  let F : (Edge L n k j → ComplexMatrix2) → Edge L n k (j + 1) → ComplexMatrix2 :=
    fun W => fieldOfPositiveValues fun _ => h W
  have hFpos : ∀ (W : Edge L n k j → ComplexMatrix2) (c : Edge L n k (j + 1)),
      c.IsPositivelyOriented → F W c = h W :=
    fun W c hc' => dif_pos hc'
  have hmaps : MapsTo F (fieldsNearOne L n k j)
      (fieldsIn L n k (j + 1) PeriodicLattice.complexGaugeGroup) :=
    fun W hW => fieldOfPositiveValues_mem ho fun _ => apply_mem_unitDeterminant hg hW
  have hhol : IsHolomorphicFieldMap β (fieldsNearOne L n k j) F := by
    refine isHolomorphicFieldMap_of_components (hP'.isOpen_nearOne j hj) hmaps (fun c hc' => ?_) fin hc
    have e : (fun W => F W c) = h := funext fun W => hFpos W c hc'
    rw [e]
    exact hg
  have hl' : ∀ x, (-l) x ∈ ComplexMatrix2.hermitianTraceless := fun x =>
    ComplexMatrix2.hermitianTraceless.neg_mem (hl x)
  have h1 := ((hCu L k j (j + 1) hL hj.le hj n hn).2.2.1 β _ _ hhol V hV) univ (gaugeOrbitCurve V (-l))
    (gaugeOrbitCurve_isDifferentiable hI hV.1 hl') (gaugeOrbitCurve_zero V _)
  have t1 := h1.2
  rw [curveTangent_gaugeOrbitCurve hI hS hP1 hCu hGD hE hE6 hL hn hj hV hl] at t1
  have e1 := congrFun t1 (PeriodicLattice.Bond.forwardFrom y 0)
  simp only [curveTangent, holLeftDifferential, extendOddly, if_pos hc] at e1
  have e2 : (fun t => F (gaugeOrbitCurve V (-l) t) (PeriodicLattice.Bond.forwardFrom y 0)) =
      fun t => h (gaugeOrbitCurve V (-l) t) := funext fun t => hFpos _ _ hc
  have e3 : (fun X => F (PeriodicLattice.expTwist X V) (PeriodicLattice.Bond.forwardFrom y 0)) =
      fun X => h (PeriodicLattice.expTwist X V) := funext fun X => hFpos _ _ hc
  rw [e2, e3, hFpos _ _ hc, hFpos _ _ hc, gaugeOrbitCurve_zero V] at e1
  have hpoly := hP'.mem_polydisc j hj _ hc V hV
  have hcov : (fun t : ℝ => h (gaugeOrbitCurve V (-l) t)) = fun t : ℝ =>
      ComplexMatrix2.matExp (Complex.I • ((t : ℂ) • (-l (y.toSublattice (PeriodicLattice.levelDepth k j))))) *
        h V * (ComplexMatrix2.matExp (Complex.I • ((t : ℂ) • (-l x))))⁻¹ := by
    funext t
    exact (((hS.1 L hL).2.2.periodic n k j hn hj _ hc).gauge_covariant V hpoly
      (expVertexFn ((t : ℂ) • (-l))) (expVertexFn_mem hI hl' t)).2.2 y hy x hx
  have hHm : h V ∈ ComplexMatrix2.unitDeterminant := apply_mem_unitDeterminant hg hV
  show logDirectionalDeriv ℂ (fun X => h (PeriodicLattice.expTwist X V)) (h V)
    (covDiff V l) = ComplexMatrix2.conjugateBy (h V) (l x) - _
  rw [← e1, hcov, deriv_conjugatedCurve _ _ _ hHm]
  have hAd : ComplexMatrix2.conjugateBy (h V) (-l x) = -ComplexMatrix2.conjugateBy (h V) (l x) := by
    simp [ComplexMatrix2.conjugateBy]
  rw [hAd]
  show -l (y.toSublattice (PeriodicLattice.levelDepth k j)) - -ComplexMatrix2.conjugateBy (h V) (l x) =
    ComplexMatrix2.conjugateBy (h V) (l x) - l (y.toSublattice (PeriodicLattice.levelDepth k j))
  abel
theorem contourLogDrift_covDiff_hermitian (hO2 : PolydiscContours.ContourHolomorphyHolds)
    (hBlk : BlockStructure) :
    contourLogDrift V (covDiff V l) = adjointCubeAverage V l - restrictVertexFunction (j + 1) l := by
  funext y
  have hL0 : L ≠ 0 := by
    have := hL.2
    omega
  obtain ⟨-, -, hcard, hsub⟩ := ((hBlk L k (j + 1) hL (by omega) (by omega) hj).1 n hn).1 y
  obtain ⟨hfin, hw⟩ := weight_finsum_const (j := j) hL0 hsub hcard (restrictVertexFunction (j + 1) l y)
  show PeriodicLattice.inverseFourthPowerWeight L •
      ∑ᶠ x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y,
      logDirectionalDeriv ℂ
        (fun X => PeriodicLattice.complexMeanContourHolonomy (PeriodicLattice.expTwist X V) y x)
        (PeriodicLattice.complexMeanContourHolonomy V y x) (covDiff V l) =
    PeriodicLattice.inverseFourthPowerWeight L •
      (∑ᶠ x ∈ PeriodicLattice.sitesInBlock (PeriodicLattice.levelDepth k j) y,
        ComplexMatrix2.conjugateBy (PeriodicLattice.complexMeanContourHolonomy V y x) (l x)) -
      restrictVertexFunction (j + 1) l y
  rw [finsum_mem_congr rfl fun x hx =>
    logDeriv_contour_hermitian hI hS hP1 hCu hGD hE hE6 hL hn hj hV hl hO2 y hx,
    finsum_mem_sub_distrib _ _ hfin, smul_sub, hw]
end HermitianDirections
omit hI
theorem exists_hermitian_parts {X : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.traceless) :
    ∃ a b : ComplexMatrix2, a ∈ ComplexMatrix2.hermitianTraceless ∧
      b ∈ ComplexMatrix2.hermitianTraceless ∧ X = Complex.I • b + a := by
  have ht : Matrix.trace X = 0 := hX
  have ht' : Matrix.trace X.conjTranspose = 0 := by
    rw [Matrix.trace_conjTranspose, ht, star_zero]
  refine ⟨(2⁻¹ : ℂ) • (X + X.conjTranspose), (-(Complex.I * 2⁻¹)) • (X - X.conjTranspose),
    ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
  · rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_conjTranspose,
      add_comm X.conjTranspose X]
    simp
  · show Matrix.trace _ = 0
    rw [Matrix.trace_smul, Matrix.trace_add, ht, ht']
    simp
  · rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.conjTranspose_conjTranspose]
    ext r s
    simp
    ring
  · show Matrix.trace _ = 0
    rw [Matrix.trace_smul, Matrix.trace_sub, ht, ht']
    simp
  · ext r s
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
    have hI2 : Complex.I * Complex.I = -1 := Complex.I_mul_I
    linear_combination ((1 / 2 : ℂ) * (X r s - X.conjTranspose r s)) * hI2
end YangMills.Construction.Tower.CovDiffStep
namespace YangMills.Construction.Tower.CovDiffStep
open YangMills.Construction.Tower.MeanStableFields (fieldsNearOne)
theorem covDiffStepRelations_holds (hLin : StepMapsComplexLinear.Claim)
    (hS : SmoothingNearIdentity)
    (hP1 : MeanStableFields.MeanStableFieldsHold)
    (hO2 : PolydiscContours.ContourHolomorphyHolds)
    (hCu : FiniteLevelCurveDifferentials.Statement)
    (hGD : GaugeOrbitTangentInLeftChart.Statement)
    (hE : PeriodicLattice.BondEndpointsOrientation.Statement)
    (hE6 : BondSetFields.ProductStructureHolds)
    (hBlk : BlockStructure)
    (hI : ComplexMatrix2.UnitaryLogarithmProperties) :
    CovDiffStepRelations := by
  intro L hL n k j hn hj V hV l hl
  choose a b ha hb hab using fun x => exists_hermitian_parts (hl x)
  have hl_eq : l = Complex.I • b + a := funext hab
  have ha' : ∀ x, a x ∈ ComplexMatrix2.traceless := fun x => (ha x).2
  have hb' : ∀ x, b x ∈ ComplexMatrix2.traceless := fun x => (hb x).2
  obtain ⟨-, c2, c3, c4⟩ := hLin L hL n k j hn hj V hV
  have hD : covDiff V l = Complex.I • covDiff V b + covDiff V a := by
    rw [hl_eq]
    exact covDiff_smul_add V _ b a
  have hQ : complexSmoothingDeriv V (covDiff V l) =
      Complex.I • complexSmoothingDeriv V (covDiff V b) + complexSmoothingDeriv V (covDiff V a) := by
    rw [hD]
    exact (c2 _ (c3 b hb').1 _ (c3 a ha').1 Complex.I).1
  have hN : contourLogDrift V (covDiff V l) =
      Complex.I • contourLogDrift V (covDiff V b) + contourLogDrift V (covDiff V a) := by
    rw [hD]
    exact (c2 _ (c3 b hb').1 _ (c3 a ha').1 Complex.I).2
  have hA : adjointCubeAverage V l =
      Complex.I • adjointCubeAverage V b + adjointCubeAverage V a := by
    rw [hl_eq]
    exact (c4 b a hb' ha' Complex.I).2
  have hR : restrictVertexFunction (j + 1) l =
      Complex.I • restrictVertexFunction (j + 1) b + restrictVertexFunction (j + 1) a := by
    rw [hl_eq]
    rfl
  have first : complexSmoothingDeriv V (covDiff V l) =
      covDiff (PeriodicLattice.complexBlockAverageStep j V) (restrictVertexFunction (j + 1) l) := by
    rw [hQ, complexSmoothingDeriv_covDiff_hermitian hI hS hP1 hCu hGD hE hE6 hL hn hj hV ha,
      complexSmoothingDeriv_covDiff_hermitian hI hS hP1 hCu hGD hE hE6 hL hn hj hV hb,
      ← covDiff_smul_add, ← hR]
  have second : contourLogDrift V (covDiff V l) =
      adjointCubeAverage V l - restrictVertexFunction (j + 1) l := by
    rw [hN, contourLogDrift_covDiff_hermitian hI hS hP1 hCu hGD hE hE6 hL hn hj hV ha hO2 hBlk,
      contourLogDrift_covDiff_hermitian hI hS hP1 hCu hGD hE hE6 hL hn hj hV hb hO2 hBlk, hA, hR,
      smul_sub]
    abel
  refine ⟨first, second, ?_⟩
  show complexSmoothingDeriv V (covDiff V l) +
    covDiff (PeriodicLattice.complexBlockAverageStep j V) (contourLogDrift V (covDiff V l)) = _
  have e := covDiff_smul_add (PeriodicLattice.complexBlockAverageStep j V) 1
    (restrictVertexFunction (j + 1) l) (adjointCubeAverage V l - restrictVertexFunction (j + 1) l)
  rw [one_smul, one_smul, add_sub_cancel] at e
  rw [first, second, e]
end YangMills.Construction.Tower.CovDiffStep
