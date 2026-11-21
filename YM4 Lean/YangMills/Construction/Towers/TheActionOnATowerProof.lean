import YangMills.Construction.Lattice.FirstDerivativeOfTheContourVariablesProof
import YangMills.Construction.Lattice.IsometryCovarianceOfHolonomiesAndActions
import YangMills.Construction.Matrices.NormExpLogBasics
import YangMills.Construction.Matrices.UnitaryLogarithmClosedForm
import YangMills.Construction.OneLoop.PauliMatrixRelations
import YangMills.Construction.Towers.CriticalBranchAtTheBottomLevelProof
import YangMills.Construction.Towers.LatticesIsometriesDilationsAndQuotientsOfATower
import Mathlib
set_option autoImplicit false
open Set Filter
open scoped Topology Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.Tower.ActionFacts
open YangMills.Construction.Matrices
variable {L m k : ℕ}
theorem isPolynomial_const (c : ℝ) :
    IsPolynomialInEdgeEntries (L := L) (n := m) (k := k) fun _ => c :=
  ⟨MvPolynomial.C c, fun U _ => by simp⟩
theorem isPolynomial_add {f g : (Edge L m k 0 → ComplexMatrix2) → ℝ}
    (hf : IsPolynomialInEdgeEntries f) (hg : IsPolynomialInEdgeEntries g) :
    IsPolynomialInEdgeEntries fun U => f U + g U := by
  obtain ⟨P, hP⟩ := hf
  obtain ⟨Q, hQ⟩ := hg
  exact ⟨P + Q, fun U hU => by simp [hP U hU, hQ U hU]⟩
theorem isPolynomial_mul {f g : (Edge L m k 0 → ComplexMatrix2) → ℝ}
    (hf : IsPolynomialInEdgeEntries f) (hg : IsPolynomialInEdgeEntries g) :
    IsPolynomialInEdgeEntries fun U => f U * g U := by
  obtain ⟨P, hP⟩ := hf
  obtain ⟨Q, hQ⟩ := hg
  exact ⟨P * Q, fun U hU => by simp [hP U hU, hQ U hU]⟩
theorem isPolynomial_congr {f g : (Edge L m k 0 → ComplexMatrix2) → ℝ}
    (hf : IsPolynomialInEdgeEntries f) (h : ∀ U ∈ fieldSpace L m k 0, g U = f U) :
    IsPolynomialInEdgeEntries g := by
  obtain ⟨P, hP⟩ := hf
  exact ⟨P, fun U hU => by rw [h U hU, hP U hU]⟩
theorem isPolynomial_sum {ι : Type*} (s : Finset ι) {f : ι → (Edge L m k 0 → ComplexMatrix2) → ℝ}
    (hf : ∀ i, IsPolynomialInEdgeEntries (f i)) :
    IsPolynomialInEdgeEntries fun U => ∑ i ∈ s, f i U := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isPolynomial_const (L := L) (m := m) (k := k) 0
  | insert a s ha ih =>
    refine isPolynomial_congr (isPolynomial_add (hf a) ih) fun U _ => ?_
    rw [Finset.sum_insert ha]
def IsPolynomialComplex (g : (Edge L m k 0 → ComplexMatrix2) → ℂ) : Prop :=
  IsPolynomialInEdgeEntries (fun U => (g U).re) ∧
    IsPolynomialInEdgeEntries (fun U => (g U).im)
theorem isPolynomialComplex_add {f g : (Edge L m k 0 → ComplexMatrix2) → ℂ}
    (hf : IsPolynomialComplex f) (hg : IsPolynomialComplex g) :
    IsPolynomialComplex fun U => f U + g U :=
  ⟨by simpa using isPolynomial_add hf.1 hg.1, by simpa using isPolynomial_add hf.2 hg.2⟩
theorem isPolynomialComplex_mul {f g : (Edge L m k 0 → ComplexMatrix2) → ℂ}
    (hf : IsPolynomialComplex f) (hg : IsPolynomialComplex g) :
    IsPolynomialComplex fun U => f U * g U := by
  refine ⟨?_, ?_⟩
  · refine isPolynomial_congr (isPolynomial_add (isPolynomial_mul hf.1 hg.1)
      (isPolynomial_mul (isPolynomial_const (-1)) (isPolynomial_mul hf.2 hg.2))) fun U _ => ?_
    simp only [Complex.mul_re]
    ring
  · refine isPolynomial_congr (isPolynomial_add (isPolynomial_mul hf.1 hg.2)
      (isPolynomial_mul hf.2 hg.1)) fun U _ => ?_
    simp only [Complex.mul_im]
def IsPolynomialMatrix (M : (Edge L m k 0 → ComplexMatrix2) → ComplexMatrix2) : Prop :=
  ∀ r c, IsPolynomialComplex fun U => M U r c
theorem isPolynomialMatrix_mul {M N : (Edge L m k 0 → ComplexMatrix2) → ComplexMatrix2}
    (hM : IsPolynomialMatrix M) (hN : IsPolynomialMatrix N) :
    IsPolynomialMatrix fun U => M U * N U := by
  intro r c
  have h := isPolynomialComplex_add (isPolynomialComplex_mul (hM r 0) (hN 0 c))
    (isPolynomialComplex_mul (hM r 1) (hN 1 c))
  simpa [Matrix.mul_apply, Fin.sum_univ_two] using h
theorem isPolynomialMatrix_edge (b : PositiveEdge L m k 0) :
    IsPolynomialMatrix fun U : Edge L m k 0 → ComplexMatrix2 => U b := by
  intro r c
  exact ⟨⟨MvPolynomial.X (b, r, c, false), fun U _ => by simp [edgeEntryCoordinates]⟩,
    ⟨MvPolynomial.X (b, r, c, true), fun U _ => by simp [edgeEntryCoordinates]⟩⟩
theorem isPolynomialMatrix_conjTranspose {M : (Edge L m k 0 → ComplexMatrix2) → ComplexMatrix2}
    (hM : IsPolynomialMatrix M) : IsPolynomialMatrix fun U => (M U).conjTranspose := by
  intro r c
  refine ⟨?_, ?_⟩
  · refine isPolynomial_congr (hM c r).1 fun U _ => ?_
    simp [Matrix.conjTranspose_apply]
  · refine isPolynomial_congr (isPolynomial_mul (isPolynomial_const (-1)) (hM c r).2)
      fun U _ => ?_
    simp [Matrix.conjTranspose_apply]
theorem inv_eq_conjTranspose_of_mem {X : ComplexMatrix2} (hX : X ∈ ComplexMatrix2.specialUnitary) :
    X⁻¹ = X.conjTranspose := by apply _root_.YangMills.Construction.Tower.WilsonAnalyticity.inv_eq_conjTranspose_of_mem_specialUnitary <;> assumption
theorem field_apply_mem {U : Edge L m k 0 → ComplexMatrix2} (hU : U ∈ fieldSpace L m k 0)
    (b : Edge L m k 0) : U b ∈ ComplexMatrix2.specialUnitary := hU.1 b (mem_univ b)
theorem field_opposite {U : Edge L m k 0 → ComplexMatrix2} (hU : U ∈ fieldSpace L m k 0)
    (b : Edge L m k 0) : U b.opposite = (U b).conjTranspose := by
  rw [hU.2 b (mem_univ b), inv_eq_conjTranspose_of_mem (field_apply_mem hU b)]
theorem faceHolonomy_eq_product {U : Edge L m k 0 → ComplexMatrix2} (hU : U ∈ fieldSpace L m k 0)
    (p : Face L m k 0) :
    PeriodicLattice.plaquetteHolonomy U p =
      U (PeriodicLattice.Bond.forwardFrom p.origin p.firstAxis) *
        U (PeriodicLattice.Bond.forwardFrom
          (p.origin + PeriodicLattice.unitStep L m _ p.firstAxis) p.secondAxis) *
        (U (PeriodicLattice.Bond.forwardFrom
          (p.origin + PeriodicLattice.unitStep L m _ p.secondAxis) p.firstAxis)).conjTranspose *
        (U (PeriodicLattice.Bond.forwardFrom p.origin p.secondAxis)).conjTranspose := by
  simp only [PeriodicLattice.plaquetteHolonomy, PeriodicLattice.pathHolonomy,
    PeriodicLattice.Plaquette.boundaryBonds, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil, mul_one, field_opposite hU, mul_assoc]
def forwardEdge (x : Vertex L m k 0) (μ : Fin 4) : PositiveEdge L m k 0 :=
  ⟨PeriodicLattice.Bond.forwardFrom x μ, μ, by simp [PeriodicLattice.Bond.forwardFrom]⟩
theorem isPolynomial_plaquetteEnergy (p : Face L m k 0) :
    IsPolynomialInEdgeEntries fun U =>
      PeriodicLattice.plaquetteCost (L := L) (m := m) (j := PeriodicLattice.levelDepth k 0) U p := by
  have hM := isPolynomialMatrix_mul (isPolynomialMatrix_mul (isPolynomialMatrix_mul
    (isPolynomialMatrix_edge (forwardEdge p.origin p.firstAxis))
    (isPolynomialMatrix_edge (forwardEdge
      (p.origin + PeriodicLattice.unitStep L m _ p.firstAxis) p.secondAxis)))
    (isPolynomialMatrix_conjTranspose (isPolynomialMatrix_edge (forwardEdge
      (p.origin + PeriodicLattice.unitStep L m _ p.secondAxis) p.firstAxis))))
    (isPolynomialMatrix_conjTranspose (isPolynomialMatrix_edge (forwardEdge p.origin p.secondAxis)))
  have htr := (isPolynomialComplex_add (hM 0 0) (hM 1 1)).1
  refine isPolynomial_congr (isPolynomial_add (isPolynomial_const 1)
    (isPolynomial_mul (isPolynomial_const (-(1 / 2))) htr)) fun U hU => ?_
  simp only [PeriodicLattice.plaquetteCost, faceHolonomy_eq_product hU p, ComplexMatrix2.fullTrace,
    Matrix.trace, Fin.sum_univ_two, Matrix.diag_apply, forwardEdge, Complex.add_re]
  ring
theorem finite_face (hA1 : QuotientLattices.TorusAndSpaceLatticeProperties)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) : Finite (Face L m k 0) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, h⟩ := (hA1 L hL m 0 k hm (Nat.zero_le k)).2.1
  exact h
theorem finite_edge (hA1 : QuotientLattices.TorusAndSpaceLatticeProperties)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) : Finite (Edge L m k 0) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, h, -⟩ := (hA1 L hL m 0 k hm (Nat.zero_le k)).2.1
  exact h
theorem totalAction_eq_sum [Fintype (Face L m k 0)] (U : Edge L m k 0 → ComplexMatrix2) :
    plaquetteAction L m k U = ∑ p : Face L m k 0, PeriodicLattice.plaquetteCost U p := by
  simp only [plaquetteAction, PeriodicLattice.wilsonAction, finsum_eq_sum_of_fintype]
theorem plaquetteHolonomy_mem {U : Edge L m k 0 → ComplexMatrix2} (hU : U ∈ fieldSpace L m k 0)
    (p : Face L m k 0) :
    PeriodicLattice.plaquetteHolonomy U p ∈ ComplexMatrix2.specialUnitary := by
  refine Submonoid.list_prod_mem _ fun x hx => ?_
  obtain ⟨b, -, rfl⟩ := List.mem_map.mp hx
  exact field_apply_mem hU b
theorem plaquetteEnergy_nonneg (hIL : ComplexMatrix2.UnitaryLogarithmProperties)
    {U : Edge L m k 0 → ComplexMatrix2} (hU : U ∈ fieldSpace L m k 0) (p : Face L m k 0) :
    0 ≤ PeriodicLattice.plaquetteCost U p := by
  obtain ⟨t, ht, h⟩ := (hIL.2.1 _ (plaquetteHolonomy_mem hU p)).1
  have h2 := congrArg Complex.re h
  simp only [ComplexMatrix2.halfTrace, Complex.ofReal_re] at h2
  have h3 : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by norm_num
  rw [h3, Complex.re_ofReal_mul] at h2
  simp only [PeriodicLattice.plaquetteCost]
  linarith [ht.2]
theorem totalAction_nonneg (hIL : ComplexMatrix2.UnitaryLogarithmProperties)
    {U : Edge L m k 0 → ComplexMatrix2} (hU : U ∈ fieldSpace L m k 0) :
    0 ≤ plaquetteAction L m k U :=
  finsum_nonneg fun p => plaquetteEnergy_nonneg hIL hU p
theorem totalAction_trivial : plaquetteAction L m k PeriodicLattice.trivialGaugeField = 0 := by
  have h : ∀ p : Face L m k 0,
      PeriodicLattice.plaquetteCost PeriodicLattice.trivialGaugeField p = 0 := by
    intro p
    simp [PeriodicLattice.plaquetteCost, PeriodicLattice.plaquetteHolonomy,
      PeriodicLattice.pathHolonomy, PeriodicLattice.Plaquette.boundaryBonds,
      PeriodicLattice.trivialGaugeField, ComplexMatrix2.fullTrace]
  simp only [plaquetteAction, PeriodicLattice.wilsonAction, h, finsum_zero]
theorem totalAction_gaugeTransform (hG : PeriodicLattice.GaugeCovarianceOfHolonomy)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m)
    {U : Edge L m k 0 → ComplexMatrix2} (hU : U ∈ fieldSpace L m k 0)
    {u : Vertex L m k 0 → ComplexMatrix2} (hu : u ∈ gaugeGroupAt L m k 0) :
    plaquetteAction L m k (PeriodicLattice.gaugeTransform u U) = plaquetteAction L m k U := by
  have hdet : ∀ {X : ComplexMatrix2}, X ∈ ComplexMatrix2.specialUnitary → X.det = 1 := fun hX =>
    (Matrix.mem_specialUnitaryGroup_iff.mp hX).2
  have hcfg : PeriodicLattice.IsGaugeField PeriodicLattice.complexGaugeGroup univ U :=
    ⟨fun b _ => hdet (field_apply_mem hU b), hU.2⟩
  have hcu : PeriodicLattice.IsGaugeMap PeriodicLattice.complexGaugeGroup u :=
    fun x => hdet (hu x)
  have hj : -(m : ℤ) ≤ PeriodicLattice.levelDepth k 0 := by
    simp only [PeriodicLattice.levelDepth]
    omega
  have hp := (hG L m hL.1 hL.2 hm _ hj univ U u u (fun _ _ => mem_univ _) hcfg hcu hcu).2.2
  have h : ∀ p : Face L m k 0,
      PeriodicLattice.plaquetteCost (PeriodicLattice.gaugeTransform u U) p =
        PeriodicLattice.plaquetteCost U p := by
    intro p
    simp only [PeriodicLattice.plaquetteCost, hp p fun _ _ => mem_univ _, ComplexMatrix2.fullTrace]
    rw [Matrix.trace_mul_comm, ← mul_assoc, Matrix.nonsing_inv_mul _ (by simp [hdet (hu _)]),
      one_mul]
  simp only [plaquetteAction, PeriodicLattice.wilsonAction, h]
theorem totalAction_eq_re [Fintype (Face L m k 0)] (U : Edge L m k 0 → ComplexMatrix2) :
    plaquetteAction L m k U = (PeriodicLattice.plaquetteWeightedEnergy (fun _ => 1) U).re := by
  rw [totalAction_eq_sum]
  simp only [PeriodicLattice.plaquetteWeightedEnergy, finsum_eq_sum_of_fintype, Complex.re_sum,
    PeriodicLattice.plaquetteCost, PeriodicLattice.plaquetteEnergy, one_mul]
  refine Finset.sum_congr rfl fun p _ => ?_
  have h3 : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by norm_num
  rw [h3, Complex.sub_re, Complex.re_ofReal_mul, Complex.one_re]
theorem vertexPreimage_eq {f : PeriodicLattice.FourTorus L m → PeriodicLattice.FourTorus L m}
    (hf : Function.Injective f) {x x' : Vertex L m k 0}
    (h : f x' = x) : vertexPreimage f x = x' := by
  have hs : f (vertexPreimage f x) = x :=
    Classical.epsilon_spec (p := fun y : Vertex L m k 0 => f y = x) ⟨x', h⟩
  exact Subtype.ext (hf (hs.trans h.symm))
theorem totalAction_pushField (hA1 : QuotientLattices.TorusAndSpaceLatticeProperties)
    (hT : SublatticesSymmetriesScalingsAndProjections.Statement)
    (hC : PeriodicLattice.IsometryCovariance.Statement)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m)
    {U : Edge L m k 0 → ComplexMatrix2} (hU : U ∈ fieldSpace L m k 0)
    {f : PeriodicLattice.FourTorus L m → PeriodicLattice.FourTorus L m}
    (hf : IsDistancePreserving f) (honto : MapsSublatticeOnto k 0 f) :
    plaquetteAction L m k (pushField f U) = plaquetteAction L m k U := by
  have hL0 : 0 < L := by have := hL.2; omega
  obtain ⟨⟨w, hw, v, hv, hwv⟩, hrest⟩ :=
    (hT L hL0 hL k).2.2.2.1 m hm 0 (Nat.zero_le k) f hf honto
  obtain ⟨-, hbonds, -⟩ := hrest 0 le_rfl
  obtain ⟨π, s, hπ⟩ := (InfiniteLattice.mem_hyperoctahedralLinearGroup_iff w).mp hw
  let r : PeriodicLattice.SignedFrame := (π, s)
  have hr : ∀ x : Fin 4 → ℝ, r.actOnVector x = w x := fun x => by
    funext μ
    simp [PeriodicLattice.SignedFrame.actOnVector, r, hπ]
  let σ : PeriodicLattice.FourTorus L m ≃ PeriodicLattice.FourTorus L m :=
    (PeriodicLattice.SignedFrame.torusEquiv L m r).trans
      (Equiv.addRight (PeriodicLattice.toFourTorus L m v))
  have hσind : PeriodicLattice.IsInducedByAffine σ r v := by
    intro x
    funext μ
    rcases Int.units_eq_one_or (s μ) with h | h <;>
      simp [σ, r, PeriodicLattice.SignedFrame.torusEquiv, PeriodicLattice.signedCoordinatePerm,
        PeriodicLattice.toFourTorus, PeriodicLattice.SignedFrame.actOnVector, h]
  have hσf : ∀ x, σ x = f x := by
    intro x
    obtain ⟨y, rfl⟩ : ∃ y : Fin 4 → ℝ, PeriodicLattice.toFourTorus L m y = x := by
      refine ⟨fun μ => Function.surjInv (QuotientAddGroup.mk_surjective) (x μ), ?_⟩
      funext μ
      exact Function.surjInv_eq QuotientAddGroup.mk_surjective (x μ)
    rw [hσind y, hr y]
    exact (hwv y).symm
  have hinj : Function.Injective f := by
    have : f = σ := funext fun x => (hσf x).symm
    rw [this]
    exact σ.injective
  have hσ : σ ∈ PeriodicLattice.latticeIsometries L m (PeriodicLattice.levelDepth k 0) := by
    obtain ⟨N, hN⟩ := hv
    refine ⟨r, v, ⟨N, fun μ => ?_⟩, hσind⟩
    rw [meshSize_levelDepth]
    exact hN μ
  have hj : -(m : ℤ) ≤ PeriodicLattice.levelDepth k 0 := by
    simp only [PeriodicLattice.levelDepth]
    omega
  have hbond : pushField f U = PeriodicLattice.transportGaugeField σ U := by
    funext b
    obtain ⟨b₀, ht, hh⟩ := hbonds.2 b
    have hex : ∃ b' : Edge L m k 0,
        (b'.source : PeriodicLattice.FourTorus L m) = σ.symm b.source ∧
        (b'.target : PeriodicLattice.FourTorus L m) = σ.symm b.target :=
      ⟨b₀, by rw [ht, ← hσf, Equiv.symm_apply_apply], by rw [hh, ← hσf, Equiv.symm_apply_apply]⟩
    have h1 : PeriodicLattice.bondPreimage σ b = b₀ := by
      simp only [PeriodicLattice.bondPreimage, dif_pos hex]
      have hc := hex.choose_spec
      refine PeriodicLattice.Bond.ext (Subtype.ext ?_) (Subtype.ext ?_)
      · rw [hc.1, ht, ← hσf, Equiv.symm_apply_apply]
      · rw [hc.2, hh, ← hσf, Equiv.symm_apply_apply]
    have h2 : edgePreimage f b = b₀ := by
      have hs : (edgePreimage f b).source = vertexPreimage f b.source ∧
          (edgePreimage f b).target = vertexPreimage f b.target :=
        Classical.epsilon_spec (p := fun b' : Edge L m k 0 =>
          b'.source = vertexPreimage f b.source ∧ b'.target = vertexPreimage f b.target)
          ⟨b₀, (vertexPreimage_eq hinj ht.symm).symm, (vertexPreimage_eq hinj hh.symm).symm⟩
      refine PeriodicLattice.Bond.ext ?_ ?_
      · rw [hs.1, vertexPreimage_eq hinj ht.symm]
      · rw [hs.2, vertexPreimage_eq hinj hh.symm]
    simp only [pushField, PeriodicLattice.transportGaugeField, h1, h2]
  obtain ⟨ε, hε⟩ := hC
  have hw1 := ((hε L m hL hm _ hj σ hσ).1 _ le_rfl).2.2.1 U hU
  have : Finite (Face L m k 0) := finite_face hA1 hL hm
  have := Fintype.ofFinite (Face L m k 0)
  rw [totalAction_eq_re, totalAction_eq_re, hbond]
  exact congrArg Complex.re (hw1.1 fun _ => 1)
theorem matExp_first_order (hExp : ComplexMatrix2.ExpLogEstimates) {Z : ComplexMatrix2}
    (hZ : ‖Z‖ ≤ 1) :
    ‖ComplexMatrix2.matExp Z‖ ≤ 3 ∧ ‖ComplexMatrix2.matExp Z - 1‖ ≤ 3 * ‖Z‖ ∧
      ‖ComplexMatrix2.matExp Z - 1 - Z‖ ≤ 2 * ‖Z‖ ^ 2 := by
  have e0 : ComplexMatrix2.matExp (0 : ComplexMatrix2) = 1 := NormedSpace.exp_zero
  have hr : Real.exp ‖Z‖ ≤ 3 := by
    have h1 : Real.exp ‖Z‖ ≤ Real.exp 1 := Real.exp_le_exp.mpr hZ
    have h2 := Real.exp_one_lt_d9
    linarith
  have hs : Real.exp ‖Z‖ - 1 ≤ 2 * ‖Z‖ := by
    have h1 := Real.abs_exp_sub_one_le (x := ‖Z‖) (by rwa [abs_of_nonneg (norm_nonneg Z)])
    rw [abs_of_nonneg (norm_nonneg Z)] at h1
    exact (le_abs_self _).trans h1
  have h := hExp.2.1 Z 0 ‖Z‖ (by simp)
  rw [e0, sub_zero] at h
  refine ⟨((hExp.1 Z).1).trans hr, h.1.trans ?_, h.2.trans ?_⟩
  · exact mul_le_mul_of_nonneg_right hr (norm_nonneg Z)
  · calc (Real.exp ‖Z‖ - 1) * ‖Z‖ ≤ 2 * ‖Z‖ * ‖Z‖ :=
        mul_le_mul_of_nonneg_right hs (norm_nonneg Z)
      _ = 2 * ‖Z‖ ^ 2 := by ring
theorem product_matExp_step (hExp : ComplexMatrix2.ExpLogEstimates) {P S Z : ComplexMatrix2}
    {c a β : ℝ} (hβ0 : 0 ≤ β) (hβ : β ≤ 1) (hc : 0 ≤ c) (ha : 0 ≤ a)
    (h1 : ‖P - 1 - S‖ ≤ c * β ^ 2) (h2 : ‖S‖ ≤ a * β) (hZ : ‖Z‖ ≤ β) :
    ‖P * ComplexMatrix2.matExp Z - 1 - (S + Z)‖ ≤ (3 * c + 3 * a + 2) * β ^ 2 := by
  obtain ⟨e1, e2, e3⟩ := matExp_first_order hExp (hZ.trans hβ)
  have hid : P * ComplexMatrix2.matExp Z - 1 - (S + Z) =
      (P - 1 - S) * ComplexMatrix2.matExp Z + (ComplexMatrix2.matExp Z - 1 - Z) +
        S * (ComplexMatrix2.matExp Z - 1) := by
    noncomm_ring
  rw [hid]
  have t1 : ‖(P - 1 - S) * ComplexMatrix2.matExp Z‖ ≤ c * β ^ 2 * 3 :=
    (norm_mul_le _ _).trans (mul_le_mul h1 e1 (norm_nonneg _) (by positivity))
  have t2 : ‖ComplexMatrix2.matExp Z - 1 - Z‖ ≤ 2 * β ^ 2 := by
    refine e3.trans ?_
    have : ‖Z‖ ^ 2 ≤ β ^ 2 := pow_le_pow_left₀ (norm_nonneg Z) hZ 2
    linarith
  have t3 : ‖S * (ComplexMatrix2.matExp Z - 1)‖ ≤ a * β * (3 * β) := by
    refine (norm_mul_le _ _).trans (mul_le_mul h2 (e2.trans ?_) (norm_nonneg _) (by positivity))
    linarith
  calc _ ≤ ‖(P - 1 - S) * ComplexMatrix2.matExp Z‖ + ‖ComplexMatrix2.matExp Z - 1 - Z‖ +
        ‖S * (ComplexMatrix2.matExp Z - 1)‖ := norm_add₃_le
    _ ≤ c * β ^ 2 * 3 + 2 * β ^ 2 + a * β * (3 * β) := by gcongr
    _ = (3 * c + 3 * a + 2) * β ^ 2 := by ring
theorem four_matExp_product (hExp : ComplexMatrix2.ExpLogEstimates)
    {Z₁ Z₂ Z₃ Z₄ : ComplexMatrix2} {β : ℝ} (hβ0 : 0 ≤ β) (hβ : β ≤ 1) (h₁ : ‖Z₁‖ ≤ β)
    (h₂ : ‖Z₂‖ ≤ β) (h₃ : ‖Z₃‖ ≤ β) (h₄ : ‖Z₄‖ ≤ β) :
    ‖ComplexMatrix2.matExp Z₁ * ComplexMatrix2.matExp Z₂ * ComplexMatrix2.matExp Z₃ *
        ComplexMatrix2.matExp Z₄ - 1 - (Z₁ + Z₂ + Z₃ + Z₄)‖ ≤ 134 * β ^ 2 := by
  have a0 : ‖ComplexMatrix2.matExp Z₁ - 1 - Z₁‖ ≤ 2 * β ^ 2 := by
    refine (matExp_first_order hExp (h₁.trans hβ)).2.2.trans ?_
    have : ‖Z₁‖ ^ 2 ≤ β ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h₁ 2
    linarith
  have b0 : ‖Z₁‖ ≤ 1 * β := by linarith
  have a1 := product_matExp_step hExp hβ0 hβ (by norm_num) (by norm_num) a0 b0 h₂
  have b1 : ‖Z₁ + Z₂‖ ≤ 2 * β := (norm_add_le _ _).trans (by linarith)
  have a2 := product_matExp_step hExp hβ0 hβ (by norm_num) (by norm_num) a1 b1 h₃
  have b2 : ‖Z₁ + Z₂ + Z₃‖ ≤ 3 * β := (norm_add_le _ _).trans (by linarith)
  have a3 := product_matExp_step hExp hβ0 hβ (by norm_num) (by norm_num) a2 b2 h₄
  refine a3.trans (le_of_eq ?_)
  ring
theorem logSeries_near_one (hExp : ComplexMatrix2.ExpLogEstimates) {X : ComplexMatrix2}
    (h : ‖X - 1‖ ≤ 1 / 2) :
    ‖ComplexMatrix2.logSeries X - (X - 1)‖ ≤ 2 * ‖X - 1‖ ^ 2 := by apply _root_.YangMills.Construction.PeriodicLattice.ContourHolonomyDerivative.logSeries_sub_sub_one_le <;> assumption
theorem norm_I_smul_eq (A : ComplexMatrix2) : ‖Complex.I • A‖ = ‖A‖ := by
  rw [norm_smul, Complex.norm_I, one_mul]
theorem four_matExp_product_log (hExp : ComplexMatrix2.ExpLogEstimates)
    (hIL : ComplexMatrix2.UnitaryLogarithmProperties) {A₁ A₂ A₃ A₄ : ComplexMatrix2} {β : ℝ}
    (i₁ : A₁ ∈ ComplexMatrix2.hermitianTraceless) (i₂ : A₂ ∈ ComplexMatrix2.hermitianTraceless)
    (i₃ : A₃ ∈ ComplexMatrix2.hermitianTraceless) (i₄ : A₄ ∈ ComplexMatrix2.hermitianTraceless)
    (hβ0 : 0 ≤ β) (hβ : β ≤ 1 / 1000) (h₁ : ‖A₁‖ ≤ β) (h₂ : ‖A₂‖ ≤ β) (h₃ : ‖A₃‖ ≤ β)
    (h₄ : ‖A₄‖ ≤ β) :
    ∃ Y ∈ ComplexMatrix2.hermitianTraceless,
      ComplexMatrix2.matExp (Complex.I • Y) =
        ComplexMatrix2.matExp (Complex.I • A₁) * ComplexMatrix2.matExp (Complex.I • A₂) *
          ComplexMatrix2.matExp (Complex.I • -A₃) * ComplexMatrix2.matExp (Complex.I • -A₄) ∧
      ‖Y - (A₁ + A₂ - A₃ - A₄)‖ ≤ 184 * β ^ 2 := by
  set X := ComplexMatrix2.matExp (Complex.I • A₁) * ComplexMatrix2.matExp (Complex.I • A₂) *
        ComplexMatrix2.matExp (Complex.I • -A₃) * ComplexMatrix2.matExp (Complex.I • -A₄)
    with hXdef
  have hmem : ∀ {A : ComplexMatrix2}, A ∈ ComplexMatrix2.hermitianTraceless →
      ComplexMatrix2.matExp (Complex.I • A) ∈ ComplexMatrix2.specialUnitary :=
    fun hA => (hIL.1 _ hA).2.2.2
  have hX : X ∈ ComplexMatrix2.specialUnitary :=
    ComplexMatrix2.specialUnitary.mul_mem (ComplexMatrix2.specialUnitary.mul_mem
      (ComplexMatrix2.specialUnitary.mul_mem (hmem i₁) (hmem i₂))
      (hmem (ComplexMatrix2.hermitianTraceless.neg_mem i₃)))
      (hmem (ComplexMatrix2.hermitianTraceless.neg_mem i₄))
  have hb1 : β ≤ 1 := by linarith
  have hsq : β ^ 2 ≤ β / 1000 := by nlinarith
  have h4 := four_matExp_product hExp hβ0 hb1
    (Z₁ := Complex.I • A₁) (Z₂ := Complex.I • A₂) (Z₃ := Complex.I • -A₃)
    (Z₄ := Complex.I • -A₄)
    (by rwa [norm_I_smul_eq]) (by rwa [norm_I_smul_eq])
    (by rw [norm_I_smul_eq, norm_neg]; exact h₃)
    (by rw [norm_I_smul_eq, norm_neg]; exact h₄)
  have hS : Complex.I • A₁ + Complex.I • A₂ + Complex.I • -A₃ + Complex.I • -A₄ =
      Complex.I • (A₁ + A₂ - A₃ - A₄) := by
    simp only [smul_neg, smul_add, sub_eq_add_neg]
  rw [hS, ← hXdef] at h4
  have hSn : ‖Complex.I • (A₁ + A₂ - A₃ - A₄)‖ ≤ 4 * β := by
    rw [norm_I_smul_eq]
    have : ‖A₁ + A₂ - A₃ - A₄‖ ≤ ‖A₁‖ + ‖A₂‖ + ‖A₃‖ + ‖A₄‖ :=
      (norm_sub_le _ _).trans (add_le_add_left ((norm_sub_le _ _).trans
        (add_le_add_left (norm_add_le _ _) _)) _)
    linarith
  have hX1 : ‖X - 1‖ ≤ 5 * β := by
    have : X - 1 = (X - 1 - Complex.I • (A₁ + A₂ - A₃ - A₄)) +
        Complex.I • (A₁ + A₂ - A₃ - A₄) := by abel
    rw [this]
    refine (norm_add_le _ _).trans ?_
    linarith
  have hX2 : ‖X - 1‖ ≤ 1 / 2 := by linarith
  obtain ⟨H, -, hlog, -, hexp, -, hdet⟩ := hExp.2.2.2.2.2.2.2.1 X
    (Matrix.mem_specialUnitaryGroup_iff.mp hX).1 (by linarith)
  obtain ⟨-, hH, -⟩ := hdet (Matrix.mem_specialUnitaryGroup_iff.mp hX).2
  refine ⟨H, hH, hexp, ?_⟩
  have hlc := logSeries_near_one hExp hX2
  have hid : Complex.I • (H - (A₁ + A₂ - A₃ - A₄)) =
      (ComplexMatrix2.logSeries X - (X - 1)) + (X - 1 - Complex.I • (A₁ + A₂ - A₃ - A₄)) := by
    rw [hlog, smul_sub]
    abel
  have hsq5 : ‖X - 1‖ ^ 2 ≤ (5 * β) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hX1 2
  rw [← norm_I_smul_eq, hid]
  refine (norm_add_le _ _).trans ?_
  nlinarith
theorem halfTrace_mul_self (hP : OneLoop.PauliMatrixRelations) {X : ComplexMatrix2}
    (hX : X ∈ ComplexMatrix2.hermitianTraceless) :
    ComplexMatrix2.halfTrace (X * X) = ((‖X‖ ^ 2 : ℝ) : ℂ) :=
  (hP.2.2.2.2.2.2.2.1 ⟨X, hX.2⟩ hX).symm
theorem energy_cos_expansion (hP : OneLoop.PauliMatrixRelations) {Y S : ComplexMatrix2} {β : ℝ}
    (hY : Y ∈ ComplexMatrix2.hermitianTraceless) (hβ0 : 0 ≤ β) (hβ : β ≤ 1 / 1000)
    (hYS : ‖Y - S‖ ≤ 184 * β ^ 2) (hS : ‖S‖ ≤ 4 * β) :
    |1 - (1 / 2) * (ComplexMatrix2.fullTrace (ComplexMatrix2.matExp (Complex.I • Y))).re -
      1 / 2 * ‖S‖ ^ 2| ≤ 1000 * β ^ 3 := by
  have hcos := hP.2.2.2.2.2.2.2.2.1 Y hY
  have hre := congrArg Complex.re hcos
  simp only [ComplexMatrix2.halfTrace, Complex.ofReal_re] at hre
  have h3 : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by norm_num
  rw [h3, Complex.re_ofReal_mul] at hre
  rw [hre]
  set y := ‖Y‖ with hy
  set s := ‖S‖ with hs
  have hy0 : 0 ≤ y := norm_nonneg _
  have hs0 : 0 ≤ s := norm_nonneg _
  have hsq : β ^ 2 ≤ β / 1000 := by nlinarith
  have hdiff : |y - s| ≤ 184 * β ^ 2 := (abs_norm_sub_norm_le Y S).trans hYS
  have hy5 : y ≤ 5 * β := by
    have := (abs_le.mp hdiff).2
    linarith
  have hy1 : |y| ≤ 1 := by
    rw [abs_of_nonneg hy0]
    linarith
  have hcb := Real.cos_bound hy1
  rw [abs_of_nonneg hy0] at hcb
  have hy4 : y ^ 4 * (5 / 96) ≤ β ^ 3 := by
    have h1 : y ^ 4 ≤ (5 * β) ^ 4 := pow_le_pow_left₀ hy0 hy5 4
    have h2 : β ^ 4 ≤ β ^ 3 / 1000 := by
      have : β ^ 4 = β ^ 3 * β := by ring
      rw [this]
      have hb3 : 0 ≤ β ^ 3 := by positivity
      nlinarith
    nlinarith
  have hdif2 : |y ^ 2 - s ^ 2| ≤ 1656 * β ^ 3 := by
    have : y ^ 2 - s ^ 2 = (y - s) * (y + s) := by ring
    rw [this, abs_mul, abs_of_nonneg (by linarith : 0 ≤ y + s)]
    calc |y - s| * (y + s) ≤ 184 * β ^ 2 * (9 * β) :=
          mul_le_mul hdiff (by linarith) (by linarith) (by positivity)
      _ = 1656 * β ^ 3 := by ring
  have hb3 : 0 ≤ β ^ 3 := by positivity
  have e : 1 - Real.cos y - 1 / 2 * s ^ 2 =
      -(Real.cos y - (1 - y ^ 2 / 2)) + (1 / 2) * (y ^ 2 - s ^ 2) := by ring
  rw [e]
  have a1 := abs_le.mp hcb
  have a2 := abs_le.mp hdif2
  rw [abs_le]
  constructor <;> nlinarith [a1.1, a1.2, a2.1, a2.2]
theorem traceFinsumPairing_self_re {ι : Type*} [Fintype ι] (hP : OneLoop.PauliMatrixRelations)
    {f : ι → ComplexMatrix2} (hf : ∀ i, f i ∈ ComplexMatrix2.hermitianTraceless) :
    (traceFinsumPairing f f).re = ∑ i, ‖f i‖ ^ 2 := by
  simp only [traceFinsumPairing, finsum_eq_sum_of_fintype, Complex.re_sum,
    halfTrace_mul_self hP (hf _), Complex.ofReal_re]
theorem traceFinsumNorm_sq {ι : Type*} [Fintype ι] (hP : OneLoop.PauliMatrixRelations)
    {f : ι → ComplexMatrix2} (hf : ∀ i, f i ∈ ComplexMatrix2.hermitianTraceless) :
    traceFinsumNorm f ^ 2 = ∑ i, ‖f i‖ ^ 2 := by
  rw [traceFinsumNorm, traceFinsumPairing_self_re hP hf, Real.sq_sqrt (by positivity)]
theorem norm_le_traceFinsumNorm {ι : Type*} [Fintype ι] (hP : OneLoop.PauliMatrixRelations)
    {f : ι → ComplexMatrix2} (hf : ∀ i, f i ∈ ComplexMatrix2.hermitianTraceless) (i : ι) :
    ‖f i‖ ≤ traceFinsumNorm f := by
  rw [traceFinsumNorm, traceFinsumPairing_self_re hP hf]
  refine Real.le_sqrt_of_sq_le ?_
  exact Finset.single_le_sum (f := fun i => ‖f i‖ ^ 2) (fun _ _ => by positivity)
    (Finset.mem_univ i)
theorem restrict_mem {B : Edge L m k 0 → ComplexMatrix2} (hB : B ∈ edgeFormSpace L m k 0)
    (b : PositiveEdge L m k 0) :
    restrictToPositiveEdges B b ∈ ComplexMatrix2.hermitianTraceless := hB.1 b.1 b.2
theorem edgeCoboundary_mem {B : Edge L m k 0 → ComplexMatrix2} (hB : B ∈ edgeFormSpace L m k 0)
    (p : Face L m k 0) : edgeCoboundary B p ∈ ComplexMatrix2.hermitianTraceless := by apply _root_.YangMills.Construction.Tower.BottomLevel.edgeCoboundary_mem <;> assumption
theorem norm_forward_le_edgeFormNorm [Fintype (PositiveEdge L m k 0)]
    (hP : OneLoop.PauliMatrixRelations) {B : Edge L m k 0 → ComplexMatrix2}
    (hB : B ∈ edgeFormSpace L m k 0) (x : Vertex L m k 0) (μ : Fin 4) :
    ‖B (PeriodicLattice.Bond.forwardFrom x μ)‖ ≤ edgeFormNorm B :=
  norm_le_traceFinsumNorm hP (restrict_mem hB) (forwardEdge x μ)
theorem forwardFrom_isPositivelyOriented (x : Vertex L m k 0) (μ : Fin 4) :
    (PeriodicLattice.Bond.forwardFrom x μ).IsPositivelyOriented := (forwardEdge x μ).2
theorem expTwist_positive {B : Edge L m k 0 → ComplexMatrix2} {b : Edge L m k 0}
    (hb : b.IsPositivelyOriented) :
    PeriodicLattice.expTwist B PeriodicLattice.trivialGaugeField b =
      ComplexMatrix2.matExp (Complex.I • B b) := by
  simp [PeriodicLattice.expTwist, hb, PeriodicLattice.trivialGaugeField]
theorem expTwist_opposite (hEl : ComplexMatrix2.NormExpLogBasics)
    {B : Edge L m k 0 → ComplexMatrix2} (hB : ∀ b, B b.opposite = -B b) (b : Edge L m k 0) :
    PeriodicLattice.expTwist B PeriodicLattice.trivialGaugeField b.opposite =
      ComplexMatrix2.matExp (Complex.I • -B b) := by
  by_cases h : b.opposite.IsPositivelyOriented
  · rw [expTwist_positive h, hB]
  · have hinv : (ComplexMatrix2.matExp (Complex.I • B b))⁻¹ =
        ComplexMatrix2.matExp (Complex.I • -B b) := by
      rw [smul_neg]
      exact (hEl.2.1 _).2.2.2.2.1
    simp only [PeriodicLattice.expTwist, if_neg h, PeriodicLattice.trivialGaugeField, mul_one]
    exact hinv
theorem plaquetteHolonomy_expTwist (hEl : ComplexMatrix2.NormExpLogBasics)
    {B : Edge L m k 0 → ComplexMatrix2} (hB : ∀ b, B b.opposite = -B b) (p : Face L m k 0) :
    PeriodicLattice.plaquetteHolonomy
        (PeriodicLattice.expTwist B PeriodicLattice.trivialGaugeField) p =
      ComplexMatrix2.matExp (Complex.I • B (PeriodicLattice.Bond.forwardFrom p.origin p.firstAxis)) *
        ComplexMatrix2.matExp (Complex.I • B (PeriodicLattice.Bond.forwardFrom
          (p.origin + PeriodicLattice.unitStep L m _ p.firstAxis) p.secondAxis)) *
        ComplexMatrix2.matExp (Complex.I • -B (PeriodicLattice.Bond.forwardFrom
          (p.origin + PeriodicLattice.unitStep L m _ p.secondAxis) p.firstAxis)) *
        ComplexMatrix2.matExp
          (Complex.I • -B (PeriodicLattice.Bond.forwardFrom p.origin p.secondAxis)) := by
  simp only [PeriodicLattice.plaquetteHolonomy, PeriodicLattice.pathHolonomy,
    PeriodicLattice.Plaquette.boundaryBonds, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil, mul_one]
  rw [expTwist_positive (forwardFrom_isPositivelyOriented _ _),
    expTwist_positive (forwardFrom_isPositivelyOriented _ _),
    expTwist_opposite hEl hB, expTwist_opposite hEl hB]
  simp only [mul_assoc]
theorem plaquetteHolonomy_expTwist_log [Fintype (PositiveEdge L m k 0)]
    (hEl : ComplexMatrix2.NormExpLogBasics) (hExp : ComplexMatrix2.ExpLogEstimates)
    (hIL : ComplexMatrix2.UnitaryLogarithmProperties) (hP : OneLoop.PauliMatrixRelations)
    {B : Edge L m k 0 → ComplexMatrix2} (hB : B ∈ edgeFormSpace L m k 0)
    (hβ : edgeFormNorm B < 1 / 1000) (p : Face L m k 0) :
    ∃ Y ∈ ComplexMatrix2.hermitianTraceless, PeriodicLattice.plaquetteHolonomy
        (PeriodicLattice.expTwist B PeriodicLattice.trivialGaugeField) p =
        ComplexMatrix2.matExp (Complex.I • Y) ∧
      ‖Y - edgeCoboundary B p‖ ≤ 184 * edgeFormNorm B ^ 2 := by
  have hi := fun (x : Vertex L m k 0) (μ : Fin 4) => hB.1 _ (forwardEdge x μ).2
  have hn0 : 0 ≤ edgeFormNorm B := Real.sqrt_nonneg _
  obtain ⟨Y, hY, he, hd⟩ := four_matExp_product_log hExp hIL (hi _ _) (hi _ _) (hi _ _)
    (hi _ _) hn0 hβ.le (norm_forward_le_edgeFormNorm hP hB p.origin p.firstAxis)
    (norm_forward_le_edgeFormNorm hP hB
      (p.origin + PeriodicLattice.unitStep L m _ p.firstAxis) p.secondAxis)
    (norm_forward_le_edgeFormNorm hP hB
      (p.origin + PeriodicLattice.unitStep L m _ p.secondAxis) p.firstAxis)
    (norm_forward_le_edgeFormNorm hP hB p.origin p.secondAxis)
  exact ⟨Y, hY, (plaquetteHolonomy_expTwist hEl hB.2 p).trans he.symm, hd⟩
theorem norm_edgeCoboundary_le [Fintype (PositiveEdge L m k 0)]
    (hP : OneLoop.PauliMatrixRelations) {B : Edge L m k 0 → ComplexMatrix2}
    (hB : B ∈ edgeFormSpace L m k 0) (p : Face L m k 0) :
    ‖edgeCoboundary B p‖ ≤ 4 * edgeFormNorm B := by
  have h₁ := norm_forward_le_edgeFormNorm hP hB p.origin p.firstAxis
  have h₂ := norm_forward_le_edgeFormNorm hP hB
    (p.origin + PeriodicLattice.unitStep L m _ p.firstAxis) p.secondAxis
  have h₃ := norm_forward_le_edgeFormNorm hP hB
    (p.origin + PeriodicLattice.unitStep L m _ p.secondAxis) p.firstAxis
  have h₄ := norm_forward_le_edgeFormNorm hP hB p.origin p.secondAxis
  have h : ‖edgeCoboundary B p‖ ≤ _ :=
    (norm_sub_le _ _).trans (add_le_add_left ((norm_sub_le _ _).trans
      (add_le_add_left (norm_add_le _ _) _)) _)
  refine h.trans ?_
  linarith
theorem holonomyExpansionAtIdentity_holds [Fintype (PositiveEdge L m k 0)]
    (hEl : ComplexMatrix2.NormExpLogBasics) (hExp : ComplexMatrix2.ExpLogEstimates)
    (hIL : ComplexMatrix2.UnitaryLogarithmProperties) (hP : OneLoop.PauliMatrixRelations) :
    HolonomyExpansionAtIdentity L m k := by
  refine ⟨184, 1 / 1000, by norm_num, fun B hB hβ p => ?_⟩
  obtain ⟨Y, -, he, hd⟩ := plaquetteHolonomy_expTwist_log hEl hExp hIL hP hB hβ p
  refine ⟨Complex.I • Y - Complex.I • edgeCoboundary B p, ?_, ?_⟩
  · rw [← smul_sub]
    simpa [norm_I_smul_eq] using hd
  · rw [he, add_sub_cancel]
theorem actionTaylorExpansion_holds [Fintype (PositiveEdge L m k 0)] [Fintype (Face L m k 0)]
    (hEl : ComplexMatrix2.NormExpLogBasics) (hExp : ComplexMatrix2.ExpLogEstimates)
    (hIL : ComplexMatrix2.UnitaryLogarithmProperties) (hP : OneLoop.PauliMatrixRelations) :
    ActionTaylorExpansion L m k := by
  refine ⟨Fintype.card (Face L m k 0) * 1000, 1 / 1000, by norm_num, fun B hB hβ => ?_⟩
  have hn0 : 0 ≤ edgeFormNorm B := Real.sqrt_nonneg _
  rw [totalAction_eq_sum, traceFinsumNorm_sq hP (edgeCoboundary_mem hB), Finset.mul_sum,
    ← Finset.sum_sub_distrib]
  have hterm : ∀ p : Face L m k 0,
      |PeriodicLattice.plaquetteCost
          (PeriodicLattice.expTwist B PeriodicLattice.trivialGaugeField) p -
        1 / 2 * ‖edgeCoboundary B p‖ ^ 2| ≤ 1000 * edgeFormNorm B ^ 3 := by
    intro p
    obtain ⟨Y, hY, he, hd⟩ := plaquetteHolonomy_expTwist_log hEl hExp hIL hP hB hβ p
    simp only [PeriodicLattice.plaquetteCost, he]
    exact energy_cos_expansion hP hY hn0 hβ.le hd (norm_edgeCoboundary_le hP hB p)
  calc _ ≤ ∑ p : Face L m k 0, |PeriodicLattice.plaquetteCost
          (PeriodicLattice.expTwist B PeriodicLattice.trivialGaugeField) p -
        1 / 2 * ‖edgeCoboundary B p‖ ^ 2| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _p : Face L m k 0, 1000 * edgeFormNorm B ^ 3 :=
        Finset.sum_le_sum fun p _ => hterm p
    _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        ring
theorem ofReal_smul_mem_edgeFormSpace {B : Edge L m k 0 → ComplexMatrix2}
    (hB : B ∈ edgeFormSpace L m k 0) (t : ℝ) : (t : ℂ) • B ∈ edgeFormSpace L m k 0 := by
  have h := (edgeFormSpace L m k 0).smul_mem t hB
  have e : (t : ℂ) • B = t • B := by
    funext b
    ext i j
    simp
  rw [e]
  exact h
theorem edgeFormNorm_ofReal_smul [Fintype (PositiveEdge L m k 0)]
    (hP : OneLoop.PauliMatrixRelations) {B : Edge L m k 0 → ComplexMatrix2}
    (hB : B ∈ edgeFormSpace L m k 0) (t : ℝ) :
    edgeFormNorm ((t : ℂ) • B) = |t| * edgeFormNorm B := by
  have h1 := traceFinsumNorm_sq hP (restrict_mem (ofReal_smul_mem_edgeFormSpace hB t))
  have h2 := traceFinsumNorm_sq hP (restrict_mem hB)
  have h1' : edgeFormNorm ((t : ℂ) • B) ^ 2 = _ := h1
  have h2' : edgeFormNorm B ^ 2 = _ := h2
  have hb0 : 0 ≤ edgeFormNorm ((t : ℂ) • B) := Real.sqrt_nonneg _
  have hb1 : 0 ≤ edgeFormNorm B := Real.sqrt_nonneg _
  refine (sq_eq_sq₀ hb0 (mul_nonneg (abs_nonneg t) hb1)).mp ?_
  have e : ∀ b : PositiveEdge L m k 0, ‖restrictToPositiveEdges ((t : ℂ) • B) b‖ ^ 2 =
      t ^ 2 * ‖restrictToPositiveEdges B b‖ ^ 2 := by
    intro b
    have : restrictToPositiveEdges ((t : ℂ) • B) b = (t : ℂ) • restrictToPositiveEdges B b := rfl
    rw [this, norm_smul, Complex.norm_real, mul_pow, Real.norm_eq_abs, sq_abs]
  rw [mul_pow, sq_abs, h1', h2', Finset.mul_sum]
  exact Finset.sum_congr rfl fun b _ => e b
theorem traceFinsumNorm_edgeCoboundary_smul_sq [Fintype (Face L m k 0)]
    (hP : OneLoop.PauliMatrixRelations) {B : Edge L m k 0 → ComplexMatrix2}
    (hB : B ∈ edgeFormSpace L m k 0) (t : ℝ) :
    traceFinsumNorm (edgeCoboundary ((t : ℂ) • B)) ^ 2 =
      t ^ 2 * traceFinsumNorm (edgeCoboundary B) ^ 2 := by
  rw [traceFinsumNorm_sq hP (edgeCoboundary_mem (ofReal_smul_mem_edgeFormSpace hB t)),
    traceFinsumNorm_sq hP (edgeCoboundary_mem hB), Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  have : edgeCoboundary ((t : ℂ) • B) p = (t : ℂ) • edgeCoboundary B p := by
    simp only [edgeCoboundary, Pi.smul_apply, smul_add, smul_sub]
  rw [this, norm_smul, Complex.norm_real, mul_pow, Real.norm_eq_abs, sq_abs]
def actionAlongRay (L m k : ℕ) (B : Edge L m k 0 → ComplexMatrix2) (t : ℝ) : ℝ :=
  plaquetteAction L m k (PeriodicLattice.expTwist ((t : ℂ) • B) PeriodicLattice.trivialGaugeField)
theorem contDiff_matExp_ray (A : ComplexMatrix2) :
    ContDiff ℝ 2 (fun t : ℝ => ComplexMatrix2.matExp (Complex.I • ((t : ℂ) • A))) := by
  have hE : ContDiff ℝ 2 (NormedSpace.exp : ComplexMatrix2 → ComplexMatrix2) :=
    contDiff_iff_contDiffAt.mpr fun x => (NormedSpace.exp_analytic (𝕂 := ℝ) x).contDiffAt
  have hl : ContDiff ℝ 2 (fun t : ℝ => t • (Complex.I • A)) := contDiff_id.smul contDiff_const
  have e : (fun t : ℝ => Complex.I • ((t : ℂ) • A)) = fun t : ℝ => t • (Complex.I • A) := by
    funext t
    ext i j
    simp
    ring
  have := hE.comp hl
  rw [← e] at this
  exact this
theorem contDiff_fullTrace_re :
    ContDiff ℝ 2 (fun M : ComplexMatrix2 => (ComplexMatrix2.fullTrace M).re) := by apply _root_.YangMills.Construction.Tower.BottomLevel.contDiff_re_fullTrace <;> assumption
theorem contDiff_actionAlongRay [Fintype (Face L m k 0)] (hEl : ComplexMatrix2.NormExpLogBasics)
    {B : Edge L m k 0 → ComplexMatrix2} (hB : B ∈ edgeFormSpace L m k 0) :
    ContDiff ℝ 2 (actionAlongRay L m k B) := by
  have e : actionAlongRay L m k B = fun t : ℝ => ∑ p : Face L m k 0,
      (1 - (1 / 2) * (ComplexMatrix2.fullTrace
      (ComplexMatrix2.matExp (Complex.I • ((t : ℂ) •
          B (PeriodicLattice.Bond.forwardFrom p.origin p.firstAxis))) *
        ComplexMatrix2.matExp (Complex.I • ((t : ℂ) • B (PeriodicLattice.Bond.forwardFrom
          (p.origin + PeriodicLattice.unitStep L m _ p.firstAxis) p.secondAxis))) *
        ComplexMatrix2.matExp (Complex.I • ((t : ℂ) • -B (PeriodicLattice.Bond.forwardFrom
          (p.origin + PeriodicLattice.unitStep L m _ p.secondAxis) p.firstAxis))) *
        ComplexMatrix2.matExp (Complex.I • ((t : ℂ) •
          -B (PeriodicLattice.Bond.forwardFrom p.origin p.secondAxis))))).re) := by
    funext t
    rw [actionAlongRay, totalAction_eq_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    simp only [PeriodicLattice.plaquetteCost,
      plaquetteHolonomy_expTwist hEl (ofReal_smul_mem_edgeFormSpace hB t).2 p,
      Pi.smul_apply, smul_neg]
  rw [e]
  refine ContDiff.sum fun p _ => ?_
  refine contDiff_const.sub (contDiff_const.mul (contDiff_fullTrace_re.comp ?_))
  exact (((contDiff_matExp_ray _).mul (contDiff_matExp_ray _)).mul (contDiff_matExp_ray _)).mul
    (contDiff_matExp_ray _)
theorem actionAlongRay_expansion [Fintype (PositiveEdge L m k 0)] [Fintype (Face L m k 0)]
    (hP : OneLoop.PauliMatrixRelations) (hAE : ActionTaylorExpansion L m k)
    {B : Edge L m k 0 → ComplexMatrix2} (hB : B ∈ edgeFormSpace L m k 0) :
    ∃ C ε : ℝ, 0 ≤ C ∧ 0 < ε ∧ ∀ t : ℝ, |t| < ε →
      |actionAlongRay L m k B t - traceFinsumNorm (edgeCoboundary B) ^ 2 / 2 * t ^ 2| ≤
        C * |t| ^ 3 := by
  obtain ⟨C, ε, hε, h⟩ := hAE
  have hn0 : 0 ≤ edgeFormNorm B := Real.sqrt_nonneg _
  refine ⟨|C| * edgeFormNorm B ^ 3, ε / (edgeFormNorm B + 1), by positivity, by positivity,
    fun t ht => ?_⟩
  have hlt : edgeFormNorm ((t : ℂ) • B) < ε := by
    rw [edgeFormNorm_ofReal_smul hP hB]
    rw [lt_div_iff₀ (by positivity)] at ht
    nlinarith [abs_nonneg t]
  have hb := h _ (ofReal_smul_mem_edgeFormSpace hB t) hlt
  rw [traceFinsumNorm_edgeCoboundary_smul_sq hP hB, edgeFormNorm_ofReal_smul hP hB] at hb
  have e : 1 / 2 * (t ^ 2 * traceFinsumNorm (edgeCoboundary B) ^ 2) =
      traceFinsumNorm (edgeCoboundary B) ^ 2 / 2 * t ^ 2 := by ring
  rw [e] at hb
  refine hb.trans ?_
  rw [mul_pow]
  have h3 : 0 ≤ |t| ^ 3 * edgeFormNorm B ^ 3 := by positivity
  calc C * (|t| ^ 3 * edgeFormNorm B ^ 3) ≤ |C| * (|t| ^ 3 * edgeFormNorm B ^ 3) :=
        mul_le_mul_of_nonneg_right (le_abs_self C) h3
    _ = |C| * edgeFormNorm B ^ 3 * |t| ^ 3 := by ring
theorem derivatives_of_quadratic_expansion {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g) {c C ε : ℝ}
    (hC : 0 ≤ C) (hε : 0 < ε) (h : ∀ t : ℝ, |t| < ε → |g t - c / 2 * t ^ 2| ≤ C * |t| ^ 3) :
    HasDerivAt g 0 0 ∧ deriv (deriv g) 0 = c := by
  have hg0 : g 0 = 0 := by
    have := h 0 (by simpa using hε)
    simpa using this
  have hd0 : HasDerivAt g 0 0 := by
    rw [hasDerivAt_iff_isLittleO_nhds_zero]
    refine Asymptotics.IsBigO.trans_isLittleO (g := fun x : ℝ => x ^ 2) ?_
      (Asymptotics.isLittleO_pow_id one_lt_two)
    refine Asymptotics.IsBigO.of_bound (|c| / 2 + C) ?_
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (lt_min hε one_pos)] with x hx
    have hx' : |x| < min ε 1 := by simpa using hx
    have hxe : |x| < ε := hx'.trans_le (min_le_left _ _)
    have hx1 : |x| ≤ 1 := (hx'.trans_le (min_le_right _ _)).le
    have hb := h x hxe
    simp only [zero_add, hg0, sub_zero, smul_zero, Real.norm_eq_abs, abs_pow, sq_abs]
    have h3 : |x| ^ 3 ≤ |x| ^ 2 := by
      have : |x| ^ 3 = |x| ^ 2 * |x| := by ring
      rw [this]
      exact mul_le_of_le_one_right (by positivity) hx1
    have h4 : |c / 2 * x ^ 2| = |c| / 2 * x ^ 2 := by
      rw [abs_mul, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_nonneg (sq_nonneg x)]
    have h5 : |g x| ≤ |g x - c / 2 * x ^ 2| + |c / 2 * x ^ 2| := by
      have := abs_add_le (g x - c / 2 * x ^ 2) (c / 2 * x ^ 2)
      simpa using this
    have h6 : |x| ^ 2 = x ^ 2 := sq_abs x
    nlinarith
  refine ⟨hd0, ?_⟩
  have hdiff : Differentiable ℝ g := hg.differentiable (by norm_num)
  have hg1 : ContDiff ℝ 1 (deriv g) := by
    have h2 : ContDiff ℝ (1 + 1) g := by
      norm_num
      exact hg
    exact (contDiff_succ_iff_deriv.mp h2).2.2
  have hdd : Differentiable ℝ (deriv g) := hg1.differentiable (by norm_num)
  set d := deriv (deriv g) 0 with hd
  have hD : HasDerivAt (deriv g) d 0 := (hdd 0).hasDerivAt
  by_contra hne
  have he : 0 < |c - d| := abs_pos.mpr (sub_ne_zero.mpr fun e => hne e.symm)
  set e := |c - d| with hedef
  have hlo := (hasDerivAt_iff_isLittleO_nhds_zero.mp hD).def (show 0 < e / 8 by positivity)
  obtain ⟨ρ, hρ, hball⟩ := Metric.eventually_nhds_iff.mp hlo
  set t := min (min (ρ / 2) (ε / 2)) (e / (8 * (C + 1))) with ht
  have ht0 : 0 < t := by
    refine lt_min (lt_min (by positivity) (by positivity)) (by positivity)
  have htρ : t < ρ := by
    have : t ≤ ρ / 2 := (min_le_left _ _).trans (min_le_left _ _)
    linarith
  have htε : t < ε := by
    have : t ≤ ε / 2 := (min_le_left _ _).trans (min_le_right _ _)
    linarith
  have htC : C * t ≤ e / 8 := by
    have h1 : t ≤ e / (8 * (C + 1)) := min_le_right _ _
    rw [le_div_iff₀ (by positivity)] at h1
    nlinarith
  have hψ : ∀ x : ℝ, HasDerivAt (fun y => g y - d / 2 * y ^ 2) (deriv g x - d * x) x := by
    intro x
    have h1 := (hdiff x).hasDerivAt
    have h2 : HasDerivAt (fun y : ℝ => d / 2 * y ^ 2) (d * x) x := by
      have h := (hasDerivAt_pow 2 x).const_mul (d / 2)
      refine h.congr_deriv ?_
      rw [show (2 - 1 : ℕ) = 1 from rfl, pow_one]
      push_cast
      ring
    exact h1.sub h2
  have hdg0 : deriv g 0 = 0 := hd0.deriv
  have hbound : ∀ x ∈ Icc 0 t, ‖deriv g x - d * x‖ ≤ e / 8 * t := by
    intro x hx
    have hxρ : dist x 0 < ρ := by
      rw [Real.dist_eq, sub_zero, abs_of_nonneg hx.1]
      exact hx.2.trans_lt htρ
    have h1 := hball hxρ
    simp only [zero_add, hdg0, sub_zero, smul_eq_mul, Real.norm_eq_abs] at h1
    rw [Real.norm_eq_abs, mul_comm d x]
    refine h1.trans ?_
    rw [abs_of_nonneg hx.1]
    exact mul_le_mul_of_nonneg_left hx.2 (by positivity)
  have hmv := (convex_Icc (0 : ℝ) t).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun x _ => (hψ x).hasDerivWithinAt) hbound (left_mem_Icc.mpr ht0.le)
    (right_mem_Icc.mpr ht0.le)
  simp only [hg0, Real.norm_eq_abs, sub_zero, abs_of_pos ht0] at hmv
  have hb := h t (by rwa [abs_of_pos ht0])
  rw [abs_of_pos ht0] at hb
  have hmv' : |g t - d / 2 * t ^ 2| ≤ e / 8 * t * t := by simpa using hmv
  have hid : (c - d) / 2 * t ^ 2 = (g t - d / 2 * t ^ 2) - (g t - c / 2 * t ^ 2) := by ring
  have hab : |c - d| / 2 * t ^ 2 ≤ e / 8 * t * t + C * t ^ 3 := by
    have h1 : |(c - d) / 2 * t ^ 2| = |c - d| / 2 * t ^ 2 := by
      rw [abs_mul, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_nonneg (sq_nonneg t)]
    rw [← h1, hid]
    exact (abs_sub _ _).trans (add_le_add hmv' hb)
  have ht2 : 0 < t ^ 2 := by positivity
  have hfin : e / 2 * t ^ 2 ≤ (e / 4) * t ^ 2 := by
    calc e / 2 * t ^ 2 ≤ e / 8 * t * t + C * t ^ 3 := hab
      _ = e / 8 * t ^ 2 + (C * t) * t ^ 2 := by ring
      _ ≤ e / 8 * t ^ 2 + e / 8 * t ^ 2 := by gcongr
      _ = e / 4 * t ^ 2 := by ring
  nlinarith
theorem leftDeriv_totalAction [Fintype (PositiveEdge L m k 0)] [Fintype (Face L m k 0)]
    (hEl : ComplexMatrix2.NormExpLogBasics) (hP : OneLoop.PauliMatrixRelations)
    (hAE : ActionTaylorExpansion L m k) {B : Edge L m k 0 → ComplexMatrix2}
    (hB : B ∈ edgeFormSpace L m k 0) :
    leftDeriv (fun U => (plaquetteAction L m k U : ℂ)) PeriodicLattice.trivialGaugeField B = 0 := by
  obtain ⟨C, ε, hC, hε, h⟩ := actionAlongRay_expansion hP hAE hB
  have hd := (derivatives_of_quadratic_expansion (contDiff_actionAlongRay hEl hB) hC hε h).1
  have h2 : deriv (fun t : ℝ => ((actionAlongRay L m k B t : ℝ) : ℂ)) 0 = 0 := by
    simpa using hd.ofReal_comp.deriv
  simpa [leftDeriv, directionalDeriv, actionAlongRay] using h2
theorem leftGradient_totalAction [Fintype (PositiveEdge L m k 0)] [Fintype (Face L m k 0)]
    (hEl : ComplexMatrix2.NormExpLogBasics) (hP : OneLoop.PauliMatrixRelations)
    (hAE : ActionTaylorExpansion L m k) :
    leftGradient (fieldSpace L m k 0) (fun U => (plaquetteAction L m k U : ℂ))
      PeriodicLattice.trivialGaugeField = 0 := by
  have hzero : IsLeftGradient (fieldSpace L m k 0) (fun U => (plaquetteAction L m k U : ℂ))
      PeriodicLattice.trivialGaugeField 0 := by
    refine ⟨⟨fun _ _ => ComplexMatrix2.traceless.zero_mem, fun _ => by simp⟩,
      fun _ => ⟨fun _ _ => ComplexMatrix2.hermitianTraceless.zero_mem, fun _ => by simp⟩,
      fun B hB _ => ?_⟩
    rw [leftDeriv_totalAction hEl hP hAE hB]
    simp [edgeFormPairing, traceFinsumPairing, restrictToPositiveEdges, ComplexMatrix2.halfTrace,
      ComplexMatrix2.fullTrace]
  have hspec : IsLeftGradient (fieldSpace L m k 0) (fun U => (plaquetteAction L m k U : ℂ))
      PeriodicLattice.trivialGaugeField
      (leftGradient (fieldSpace L m k 0) (fun U => (plaquetteAction L m k U : ℂ))
        PeriodicLattice.trivialGaugeField) := Classical.epsilon_spec ⟨0, hzero⟩
  set X := leftGradient (fieldSpace L m k 0) (fun U => (plaquetteAction L m k U : ℂ))
    PeriodicLattice.trivialGaugeField with hX
  have hreal : X ∈ edgeFormSpace L m k 0 := hspec.2.1 fun V _ => Complex.ofReal_im _
  have hpair := hspec.2.2 X hreal (Set.toFinite _)
  rw [leftDeriv_totalAction hEl hP hAE hreal] at hpair
  have hre : (traceFinsumPairing (restrictToPositiveEdges X) (restrictToPositiveEdges X)).re = 0 := by
    have : traceFinsumPairing (restrictToPositiveEdges X) (restrictToPositiveEdges X) = 0 := hpair
    rw [this]
    rfl
  rw [traceFinsumPairing_self_re hP (restrict_mem hreal),
    Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => by positivity)] at hre
  have hpos : ∀ b : Edge L m k 0, b.IsPositivelyOriented → X b = 0 := by
    intro b hb
    have := hre ⟨b, hb⟩ (Finset.mem_univ _)
    simpa [restrictToPositiveEdges] using this
  funext b
  obtain ⟨μ, h | h⟩ := b.isNeighbour
  · exact hpos b ⟨μ, h⟩
  · have hr : b.opposite.IsPositivelyOriented := ⟨μ, by
      change b.source - b.target = _
      rw [← neg_sub, h, neg_neg]⟩
    have h1 := hreal.2 b
    rw [hpos _ hr] at h1
    simpa using h1.symm
theorem leftSecondDeriv_totalAction [Fintype (PositiveEdge L m k 0)] [Fintype (Face L m k 0)]
    (hEl : ComplexMatrix2.NormExpLogBasics) (hP : OneLoop.PauliMatrixRelations)
    (hAE : ActionTaylorExpansion L m k) {B : Edge L m k 0 → ComplexMatrix2}
    (hB : B ∈ edgeFormSpace L m k 0) :
    leftSecondDeriv (plaquetteAction L m k) PeriodicLattice.trivialGaugeField B B =
      traceFinsumNorm (edgeCoboundary B) ^ 2 := by
  obtain ⟨C, ε, hC, hε, h⟩ := actionAlongRay_expansion hP hAE hB
  have hd := (derivatives_of_quadratic_expansion (contDiff_actionAlongRay hEl hB) hC hε h).2
  have e : ∀ s : ℝ, deriv (fun t : ℝ => plaquetteAction L m k (PeriodicLattice.expTwist
      (algebraMap ℝ ℂ s • B + algebraMap ℝ ℂ t • B) PeriodicLattice.trivialGaugeField)) 0 =
      deriv (actionAlongRay L m k B) s := by
    intro s
    have e1 : (fun t : ℝ => plaquetteAction L m k (PeriodicLattice.expTwist
        (algebraMap ℝ ℂ s • B + algebraMap ℝ ℂ t • B) PeriodicLattice.trivialGaugeField)) =
        fun t => actionAlongRay L m k B (s + t) := by
      funext t
      simp only [actionAlongRay, Complex.ofReal_add, add_smul, Complex.coe_algebraMap]
    rw [e1, deriv_comp_const_add, add_zero]
  simp only [leftSecondDeriv, mixedDirectionalDeriv, e]
  exact hd
theorem statement_holds (hEl : ComplexMatrix2.NormExpLogBasics)
    (hExp : ComplexMatrix2.ExpLogEstimates) (hIL : ComplexMatrix2.UnitaryLogarithmProperties)
    (hP : OneLoop.PauliMatrixRelations)
    (hG : PeriodicLattice.GaugeCovarianceOfHolonomy)
    (hA1 : QuotientLattices.TorusAndSpaceLatticeProperties)
    (hT : SublatticesSymmetriesScalingsAndProjections.Statement)
    (hC : PeriodicLattice.IsometryCovariance.Statement) :
    Statement := by
  intro L k m hL hm
  have hfp : Finite (Face L m k 0) := finite_face hA1 hL hm
  have hfb : Finite (Edge L m k 0) := finite_edge hA1 hL hm
  have := Fintype.ofFinite (Face L m k 0)
  have := Fintype.ofFinite (PositiveEdge L m k 0)
  have hAE : ActionTaylorExpansion L m k := actionTaylorExpansion_holds hEl hExp hIL hP
  refine ⟨⟨isPolynomial_congr (isPolynomial_sum Finset.univ isPolynomial_plaquetteEnergy)
      fun U _ => totalAction_eq_sum U,
    fun U hU => totalAction_nonneg hIL hU, totalAction_trivial⟩,
    fun U hU u hu => totalAction_gaugeTransform hG hL hm hU hu,
    fun U hU f hf honto => totalAction_pushField hA1 hT hC hL hm hU hf honto,
    holonomyExpansionAtIdentity_holds hEl hExp hIL hP, hAE, leftGradient_totalAction hEl hP hAE,
    fun B hB => leftSecondDeriv_totalAction hEl hP hAE hB⟩
end YangMills.Construction.Tower.ActionFacts
end
