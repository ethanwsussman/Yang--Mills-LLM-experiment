import YangMills.Construction.Towers.ChargedFormInComponents
import YangMills.Construction.Towers.LowerBoundsOfTheAbelianOperatorsProof
import YangMills.Construction.Towers.RelationsOfTheWeylOperators
import Mathlib
set_option autoImplicit false
open YangMills.Construction.Tower.UnitLatticeL2 YangMills.Construction.Tower.UnitaryCombinations
open scoped ComplexConjugate
open Function (support)
noncomputable section
namespace YangMills.Construction.Tower.ConstantFieldSymbols.ChargedPairsFormProof
open MagneticWeyl AbelianFieldDensity AbelianFieldFacts
variable {L : ℕ}
theorem scaledLinearAngle_eq_halfFluxAngle (L : ℕ) (f : ℝ) :
    scaledLinearAngle L f = halfFluxAngle L (2 * f) := by
  funext b
  simp only [scaledLinearAngle, halfFluxAngle]
  ring
theorem magneticWeyl_basisVec (φ : ℝ) (μ : Fin 4) (v : ScalarL2 L) :
    magneticWeyl L φ (basisVec μ) v = magneticTranslation L φ μ v := by
  fin_cases μ <;> simp [magneticWeyl, magneticTranslationProd, basisVec]
theorem covShift_eq_magneticWeyl {φ : ℝ} (hS : CovariantShifts (halfFluxAngle L φ)) (μ : Fin 4)
    (v : ScalarL2 L) :
    covShift (halfFluxAngle L φ) μ v = magneticWeyl L φ (basisVec μ) v := by
  rw [magneticWeyl_basisVec]
  refine lp.ext (funext fun x => ?_)
  ext i
  obtain rfl : i = 0 := Subsingleton.elim _ _
  rw [hS.covShift_apply, magneticTranslation_apply]
theorem opAdjoint_covShift_eq (hR : MagneticWeylRelations) {φ : ℝ}
    (hS : CovariantShifts (halfFluxAngle L φ)) (μ : Fin 4) (v : ScalarL2 L) :
    opAdjoint (covShift (halfFluxAngle L φ) μ) v =
      magneticWeyl L φ (-basisVec μ) v := by
  refine ext_inner_right ℂ fun χ => ?_
  rw [opAdjoint, ContinuousLinearMap.adjoint_inner_left, covShift_eq_magneticWeyl hS,
    (hR L φ (basisVec μ) 0).2.2.1]
theorem coord_apply (w : VectorL2 L 4) (μ : Fin 4) (x : FullSpace.Vertex L 0 0) :
    coord w μ x 0 = w x μ := by
  simp [coord]
theorem halfTrace_add_smul (a b : ℂ) (X Y : Matrices.ComplexMatrix2) :
    Matrices.ComplexMatrix2.halfTrace (a • X + b • Y) =
      a * Matrices.ComplexMatrix2.halfTrace X + b * Matrices.ComplexMatrix2.halfTrace Y := by
  simp only [Matrices.ComplexMatrix2.halfTrace, Matrices.ComplexMatrix2.fullTrace,
    Matrix.trace_add, Matrix.trace_smul, smul_eq_mul]
  ring
theorem offDiagonalComponent_forwardEdge (hA : ChargeAlgebra) {w : VectorL2 L 4}
    {B : FullSpace.Edge L 0 0 → Matrices.ComplexMatrix2} (hw : IsLieFormOf w B)
    (x : FullSpace.Vertex L 0 0) (μ : Fin 4) :
    FullSpace.offDiagonalComponent B (FullSpace.forwardEdge x μ) = w x μ := by
  obtain ⟨-, -, h₁, -, h₂, -, -⟩ := hA
  show 2 * Matrices.ComplexMatrix2.halfTrace
    (B (InfiniteLattice.Link.forwardFrom x μ) * loweringPauli) = _
  rw [hw.2, add_mul, smul_mul_assoc, smul_mul_assoc, halfTrace_add_smul, h₁, h₂]
  ring
theorem diagonalComponent_forwardEdge (hA : ChargeAlgebra) {w : VectorL2 L 4}
    {B : FullSpace.Edge L 0 0 → Matrices.ComplexMatrix2} (hw : IsLieFormOf w B)
    (x : FullSpace.Vertex L 0 0) (μ : Fin 4) :
    FullSpace.diagonalComponent B (FullSpace.forwardEdge x μ) = 0 := by
  obtain ⟨-, -, -, -, -, h₁, h₂⟩ := hA
  show (Matrices.ComplexMatrix2.halfTrace
    (B (InfiniteLattice.Link.forwardFrom x μ) * Matrices.ComplexMatrix2.pauliFamily 2)).re = 0
  rw [hw.2, add_mul, smul_mul_assoc, smul_mul_assoc, halfTrace_add_smul, h₁, h₂]
  simp
theorem hasFiniteEdgeSupport_of_isLieFormOf {w : VectorL2 L 4}
    {B : FullSpace.Edge L 0 0 → Matrices.ComplexMatrix2}
    (hw : IsLieFormOf w B) (hfin : (support fun x => w x).Finite) :
    FullSpace.HasFiniteEdgeSupport B := by
  refine ((hfin.prod (Set.finite_univ (α := Fin 4))).image
    fun c => InfiniteLattice.Link.forwardFrom c.1 c.2).subset ?_
  rintro b ⟨⟨μ, hμ⟩, hb⟩
  have e : InfiniteLattice.Link.forwardFrom b.initial μ = b := by
    refine InfiniteLattice.Link.ext rfl ?_
    change b.initial + _ = b.terminal
    rw [← hμ]
    abel
  refine ⟨(b.initial, μ), ⟨?_, Set.mem_univ _⟩, e⟩
  intro h0
  apply hb
  rw [← e, hw.2]
  have h1 : w b.initial = 0 := h0
  simp [h1]
theorem inner_fin_one (a b : EuclideanSpace ℂ (Fin 1)) : inner ℂ a b = conj (a 0) * b 0 := by
  simp [PiLp.inner_apply, mul_comm]
theorem hasSum_conj_mul (y y' : ScalarL2 L) :
    HasSum (fun x => conj (y x 0) * y' x 0) (inner ℂ y y') := by
  have h := lp.hasSum_inner (𝕜 := ℂ) y y'
  simpa only [inner_fin_one] using h
theorem finsum_eq_of_hasSum {α : Type} {g : α → ℂ} {v : ℂ} (hg : (support g).Finite)
    (h : HasSum g v) : ∑ᶠ a, g a = v := by
  rw [← h.tsum_eq]
  exact (tsum_eq_finsum hg).symm
theorem hasSum_finsum_of_finite {α : Type} {g : α → ℂ} (hg : (support g).Finite) :
    HasSum g (∑ᶠ a, g a) := by
  have h : Summable g := summable_of_hasFiniteSupport hg
  have e := h.hasSum
  rwa [tsum_eq_finsum hg] at e
theorem sum_apply_zero {ι : Type} (s : Finset ι) (v : ι → ScalarL2 L)
    (x : FullSpace.Vertex L 0 0) : (∑ i ∈ s, v i) x 0 = ∑ i ∈ s, v i x 0 := by
  rw [lp.coeFn_sum, Finset.sum_apply]
  simp
theorem sum_filter_lt_fin_four (F : Fin 4 × Fin 4 → ℝ) :
    ∑ c ∈ Finset.univ.filter (fun c : Fin 4 × Fin 4 => c.1 < c.2), F c =
      F (0, 1) + F (0, 2) + F (0, 3) + F (1, 2) + F (1, 3) + F (2, 3) := by apply _root_.YangMills.Construction.Tower.AbelianOperatorBounds.sum_lt_pairs_fin_four <;> assumption
theorem ofReal_im_eq (z : ℂ) : ((z.im : ℝ) : ℂ) = (z - conj z) * (-Complex.I / 2) := by
  apply Complex.ext <;> simp
  ring
theorem sum_phaseWeight_exp (t : ℝ) (i j : Fin 4) (z : ℂ) :
    ∑ s : Bool, phaseWeight i j s *
        Complex.exp (Complex.I * (((if s then t else -t : ℝ)) : ℂ)) * z =
      (if i = j then (Complex.exp (Complex.I * (t : ℂ)) +
          Complex.exp (-(Complex.I * (t : ℂ)))) / 2
        else if i < j then Complex.exp (-(Complex.I * (t : ℂ)))
        else Complex.exp (Complex.I * (t : ℂ))) * z := by
  rw [Fintype.sum_bool]
  rcases lt_trichotomy i j with h | h | h
  · simp [phaseWeight, h, h.ne, h.not_gt]
  · subst h
    simp [phaseWeight]
    ring
  · simp [phaseWeight, h, h.ne', h.not_gt]
theorem faceTerm_expansion (t : ℝ) (y : Fin 4 → ℂ) :
    ((Real.cos t * (0 ^ 2 + ‖∑ i, y i‖ ^ 2) -
        2 * Real.sin t * ∑ c ∈ Finset.univ.filter (fun c : Fin 4 × Fin 4 => c.1 < c.2),
          (y c.1 * conj (y c.2)).im : ℝ) : ℂ) =
      ∑ i, ∑ j, ∑ s : Bool, phaseWeight i j s *
        Complex.exp (Complex.I * (((if s then t else -t : ℝ)) : ℂ)) * (conj (y i) * y j) := by
  simp only [sum_phaseWeight_exp]
  have hc : ((Real.cos t : ℝ) : ℂ) = (Complex.exp (Complex.I * (t : ℂ)) +
      Complex.exp (-(Complex.I * (t : ℂ)))) / 2 := by
    rw [Complex.ofReal_cos, Complex.cos, mul_comm (t : ℂ), neg_mul, mul_comm (t : ℂ)]
  have hs : ((Real.sin t : ℝ) : ℂ) = (Complex.exp (Complex.I * (t : ℂ)) -
      Complex.exp (-(Complex.I * (t : ℂ)))) * (-Complex.I / 2) := by
    rw [Complex.ofReal_sin, Complex.sin, mul_comm (t : ℂ), neg_mul]
    ring_nf
  have hn : ((‖∑ i, y i‖ ^ 2 : ℝ) : ℂ) = (∑ i, y i) * conj (∑ i, y i) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [sum_filter_lt_fin_four]
  generalize Complex.exp (Complex.I * (t : ℂ)) = E at hc hs ⊢
  generalize Complex.exp (-(Complex.I * (t : ℂ))) = E' at hc hs ⊢
  simp only [Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_add, zero_pow, ne_eq,
    OfNat.ofNat_ne_zero, not_false_eq_true, zero_add, hn, hc, hs, ofReal_im_eq,
    Complex.ofReal_ofNat]
  simp only [map_mul, Complex.conj_conj, Fin.sum_univ_four]
  simp only [Fin.isValue, Fin.reduceEq, Fin.reduceLT, ↓reduceIte, map_add]
  linear_combination (-(1 / 2) * (E - E') *
    ((y 0 * conj (y 1) - conj (y 0) * y 1) + (y 0 * conj (y 2) - conj (y 0) * y 2) +
      (y 0 * conj (y 3) - conj (y 0) * y 3) + (y 1 * conj (y 2) - conj (y 1) * y 2) +
      (y 1 * conj (y 3) - conj (y 1) * y 3) + (y 2 * conj (y 3) - conj (y 2) * y 3))) *
    Complex.I_sq
theorem faceAngle_eq (hAng : LinearFieldAngles L) (f : ℝ) (p : FullSpace.Face L 0 0) :
    FullSpace.faceAngle (halfFluxAngle L (2 * f)) p = fluxWeight p.lowAxis p.highAxis * f := by
  rw [← scaledLinearAngle_eq_halfFluxAngle]
  refine (hAng f p).trans ?_
  unfold fluxWeight
  split_ifs <;> simp
theorem weylTerm_eval_mk (m : Fin 4 → ℤ) (a : Fin 4) (g : ℂ) (r φ : ℝ) (w : VectorL2 L 4)
    (x : FullSpace.Vertex L 0 0) :
    WeylTerm.eval ⟨m, a, g, r⟩ L φ w x 0 =
      g * Complex.exp (Complex.I * ((r * φ : ℝ) : ℂ)) * magneticWeyl L φ m (coord w a) x 0 :=
  rfl
theorem faceTerm_eval_eq_faceNumbers (hR : MagneticWeylRelations)
    (hA : ChargeAlgebra) (hAng : LinearFieldAngles L) {f : ℝ}
    {w : VectorL2 L 4} {B : FullSpace.Edge L 0 0 → Matrices.ComplexMatrix2} (hw : IsLieFormOf w B)
    (p : FullSpace.Face L 0 0) (i : Fin 4) :
    (ConstantFieldSymbols.faceTerm p.lowAxis p.highAxis (fluxWeight p.lowAxis p.highAxis) i).eval
        L (2 * f) w p.corner 0 =
      FullSpace.faceNumbers (halfFluxAngle L (2 * f)) (FullSpace.offDiagonalComponent B) p i := by
  have hc : ∀ μ, FullSpace.edgeComponent (FullSpace.offDiagonalComponent B) μ = fun x => w x μ :=
    fun μ => funext fun x => offDiagonalComponent_forwardEdge hA hw x μ
  have h0 := (hR L (2 * f) 0 0).2.1
  have hcov : ∀ (μ ν : Fin 4) (x : FullSpace.Vertex L 0 0),
      FullSpace.chargedShift (halfFluxAngle L (2 * f)) μ (fun y => w y ν) x =
        magneticWeyl L (2 * f) (basisVec μ) (coord w ν) x 0 := by
    intro μ ν x
    rw [magneticWeyl_basisVec, magneticTranslation_apply]
    simp only [coord_apply]
  have hE : 2 * Complex.I * ((FullSpace.faceAngle (halfFluxAngle L (2 * f)) p : ℝ) : ℂ) =
      Complex.I * ((fluxWeight p.lowAxis p.highAxis * (2 * f) : ℝ) : ℂ) := by
    rw [faceAngle_eq hAng]
    push_cast
    ring
  fin_cases i
  · change WeylTerm.eval ⟨0, p.lowAxis, 1, 0⟩ L (2 * f) w p.corner 0 = _
    rw [weylTerm_eval_mk, h0]
    simp [FullSpace.faceNumbers, hc, coord_apply]
  · change WeylTerm.eval ⟨basisVec p.lowAxis, p.highAxis, 1, 0⟩ L (2 * f) w p.corner 0 = _
    rw [weylTerm_eval_mk]
    simp [FullSpace.faceNumbers, hc, hcov]
  · change WeylTerm.eval ⟨basisVec p.highAxis, p.lowAxis, -1, _⟩ L (2 * f) w p.corner 0 = _
    rw [weylTerm_eval_mk]
    simp only [FullSpace.faceNumbers, hc, hcov, hE]
    simp
  · change WeylTerm.eval ⟨0, p.highAxis, -1, _⟩ L (2 * f) w p.corner 0 = _
    rw [weylTerm_eval_mk, h0]
    simp only [FullSpace.faceNumbers, hc, hE, coord_apply]
    simp
theorem faceTerm_eq_sum_pairs (hR : MagneticWeylRelations)
    (hA : ChargeAlgebra) (hAng : LinearFieldAngles L) {f : ℝ}
    {w : VectorL2 L 4} {B : FullSpace.Edge L 0 0 → Matrices.ComplexMatrix2} (hw : IsLieFormOf w B)
    (hzero : ∀ p, FullSpace.edgeDifference (FullSpace.diagonalComponent B) p = 0)
    (d : {d : Fin 4 × Fin 4 // d.1 < d.2}) (x : FullSpace.Vertex L 0 0) (hp : d.1.1 < d.1.2) :
    ((AbelianFieldFacts.faceTerm (halfFluxAngle L (2 * f)) B ⟨x, d.1.1, d.1.2, hp⟩ : ℝ) : ℂ) =
      ∑ i, ∑ j, ∑ s : Bool,
        ((chargedTermPair (Sum.inl (d, i, j, s))).coeff *
          Complex.exp (Complex.I *
            (((chargedTermPair (Sum.inl (d, i, j, s))).freq * (2 * f) : ℝ) : ℂ))) *
        (conj ((chargedTermPair (Sum.inl (d, i, j, s))).conjTerm.eval L (2 * f) w x 0) *
          (chargedTermPair (Sum.inl (d, i, j, s))).term.eval L (2 * f) w x 0) := by
  set p : FullSpace.Face L 0 0 := ⟨x, d.1.1, d.1.2, hp⟩ with hpdef
  have hy : ∀ i, FullSpace.faceNumbers (halfFluxAngle L (2 * f))
      (FullSpace.offDiagonalComponent B) p i =
      (ConstantFieldSymbols.faceTerm d.1.1 d.1.2 (fluxWeight d.1.1 d.1.2) i).eval
        L (2 * f) w x 0 :=
    fun i => (faceTerm_eval_eq_faceNumbers hR hA hAng hw p i).symm
  have ht : FullSpace.faceAngle (halfFluxAngle L (2 * f)) p =
      fluxWeight d.1.1 d.1.2 * f := faceAngle_eq hAng f p
  have := faceTerm_expansion (fluxWeight d.1.1 d.1.2 * f)
    (fun i => (ConstantFieldSymbols.faceTerm d.1.1 d.1.2 (fluxWeight d.1.1 d.1.2) i).eval
      L (2 * f) w x 0)
  simp only [AbelianFieldFacts.faceTerm, hzero, ht, hy]
  refine this.trans ?_
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Fintype.sum_bool, Fintype.sum_bool]
  simp only [chargedTermPair]
  congr 2
  · congr 3
    simp
    ring_nf
  · congr 3
    simp
    ring_nf
def faceEquiv (L : ℕ) :
    ({d : Fin 4 × Fin 4 // d.1 < d.2} × FullSpace.Vertex L 0 0) ≃ FullSpace.Face L 0 0 where
  toFun c := ⟨c.2, c.1.1.1, c.1.1.2, c.1.2⟩
  invFun p := (⟨(p.lowAxis, p.highAxis), p.lowAxis_lt_highAxis⟩, p.corner)
  left_inv _ := rfl
  right_inv _ := rfl
theorem sum_vertexTerm_eval (hR : MagneticWeylRelations) {φ : ℝ}
    (hS : CovariantShifts (halfFluxAngle L φ)) (w : VectorL2 L 4) :
    ∑ a : Fin 4 × Bool, (ConstantFieldSymbols.vertexTerm a.1 a.2).eval L φ w =
      ∑ μ, covShiftAdjSubOne (halfFluxAngle L φ) μ (coord w μ) := by
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [Fintype.sum_bool]
  simp [ConstantFieldSymbols.vertexTerm, WeylTerm.eval, covShiftAdjSubOne,
    opAdjoint_covShift_eq hR hS, (hR L φ 0 0).2.1, sub_eq_add_neg]
theorem chargedPairsFormIdentity_holds (hF : AbelianFieldFacts.AllFacts)
    (hT : ScalarDifferenceAdjoints)
    (hR : MagneticWeylRelations) : ChargedPairsFormIdentity := by
  intro L hL f w B hfin hw
  obtain ⟨-, hA, hrest⟩ := hF
  obtain ⟨-, -, hAng, hθ⟩ := hrest L hL 1 one_pos
  obtain ⟨-, -, hS, -, hQ, -, -⟩ := hθ (halfFluxAngle L (2 * f))
  have hBfin := hasFiniteEdgeSupport_of_isLieFormOf hw hfin
  obtain ⟨hval, hplaq, hsite, -⟩ := hQ B hw.1 hBfin
  rw [scaledLinearAngle_eq_halfFluxAngle]
  have hn : ∀ b, FullSpace.diagonalComponent B b = 0 := by
    intro b
    obtain ⟨c, rfl, -⟩ := hS.existsUnique_forwardEdge b
    exact diagonalComponent_forwardEdge hA hw _ _
  have hd : ∀ p, FullSpace.edgeDifference (FullSpace.diagonalComponent B) p = 0 := by
    intro p
    simp [FullSpace.edgeDifference, hn]
  have ht : ∀ x, FullSpace.vertexAdjoint (FullSpace.diagonalComponent B) x = 0 := by
    intro x
    rw [(hT L hL).2.2.2.2.2.2.1.2.2.2.2]
    simp [hn]
  have hsf : ∀ μ, toScalarL2 (FullSpace.edgeComponent (FullSpace.offDiagonalComponent B) μ) =
      coord w μ := by
    intro μ
    refine lp.ext (funext fun x => ?_)
    ext i
    obtain rfl : i = 0 := Subsingleton.elim _ _
    rw [hval μ x, coord_apply]
    exact offDiagonalComponent_forwardEdge hA hw x μ
  have hc₁ : ((∑ᶠ p, AbelianFieldFacts.faceTerm (halfFluxAngle L (2 * f)) B p : ℝ) : ℂ) =
      ∑ᶠ p, ((AbelianFieldFacts.faceTerm (halfFluxAngle L (2 * f)) B p : ℝ) : ℂ) :=
    Complex.ofRealHom.toAddMonoidHom.map_finsum hplaq
  have hc₂ : ((∑ᶠ x, AbelianFieldFacts.vertexTerm (halfFluxAngle L (2 * f)) B x : ℝ) : ℂ) =
      ∑ᶠ x, ((AbelianFieldFacts.vertexTerm (halfFluxAngle L (2 * f)) B x : ℝ) : ℂ) :=
    Complex.ofRealHom.toAddMonoidHom.map_finsum hsite
  have hG : (support fun p =>
      ((AbelianFieldFacts.faceTerm (halfFluxAngle L (2 * f)) B p : ℝ) : ℂ)).Finite :=
    hplaq.subset fun p hp h0 => hp (by simp [h0])
  have hH : (support fun x =>
      ((AbelianFieldFacts.vertexTerm (halfFluxAngle L (2 * f)) B x : ℝ) : ℂ)).Finite :=
    hsite.subset fun x hx h0 => hx (by simp [h0])
  have hfib : ∀ d : {d : Fin 4 × Fin 4 // d.1 < d.2},
      HasSum (fun x : FullSpace.Vertex L 0 0 =>
          ((AbelianFieldFacts.faceTerm (halfFluxAngle L (2 * f)) B (faceEquiv L (d, x)) : ℝ) : ℂ))
        (∑ i, ∑ j, ∑ s : Bool,
          ((chargedTermPair (Sum.inl (d, i, j, s))).coeff *
            Complex.exp (Complex.I *
              (((chargedTermPair (Sum.inl (d, i, j, s))).freq * (2 * f) : ℝ) : ℂ))) *
          inner ℂ ((chargedTermPair (Sum.inl (d, i, j, s))).conjTerm.eval L (2 * f) w)
            ((chargedTermPair (Sum.inl (d, i, j, s))).term.eval L (2 * f) w)) := by
    intro d
    have h := hasSum_sum fun i (_ : i ∈ Finset.univ) => hasSum_sum fun j (_ : j ∈ Finset.univ) =>
      hasSum_sum fun s (_ : s ∈ (Finset.univ : Finset Bool)) =>
        (hasSum_conj_mul ((chargedTermPair (Sum.inl (d, i, j, s))).conjTerm.eval L (2 * f) w)
          ((chargedTermPair (Sum.inl (d, i, j, s))).term.eval L (2 * f) w)).mul_left
          ((chargedTermPair (Sum.inl (d, i, j, s))).coeff *
            Complex.exp (Complex.I *
              (((chargedTermPair (Sum.inl (d, i, j, s))).freq * (2 * f) : ℝ) : ℂ)))
    have e : ∀ x : FullSpace.Vertex L 0 0,
        ((AbelianFieldFacts.faceTerm (halfFluxAngle L (2 * f)) B (faceEquiv L (d, x)) : ℝ) : ℂ) =
          _ :=
      fun x => faceTerm_eq_sum_pairs hR hA hAng hw hd d x d.2
    rw [funext e]
    exact h
  have hpl : ∑ᶠ p, ((AbelianFieldFacts.faceTerm (halfFluxAngle L (2 * f)) B p : ℝ) : ℂ) =
      ∑ d : {d : Fin 4 × Fin 4 // d.1 < d.2}, ∑ i, ∑ j, ∑ s : Bool,
        ((chargedTermPair (Sum.inl (d, i, j, s))).coeff *
          Complex.exp (Complex.I *
            (((chargedTermPair (Sum.inl (d, i, j, s))).freq * (2 * f) : ℝ) : ℂ))) *
        inner ℂ ((chargedTermPair (Sum.inl (d, i, j, s))).conjTerm.eval L (2 * f) w)
          ((chargedTermPair (Sum.inl (d, i, j, s))).term.eval L (2 * f) w) := by
    have h₁ : HasSum (fun p => ((AbelianFieldFacts.faceTerm (halfFluxAngle L (2 * f)) B p : ℝ) : ℂ))
        (∑ᶠ p, ((AbelianFieldFacts.faceTerm (halfFluxAngle L (2 * f)) B p : ℝ) : ℂ)) := hasSum_finsum_of_finite hG
    have h₂ := ((faceEquiv L).hasSum_iff).2 h₁
    exact (h₂.prod_fiberwise hfib).unique (hasSum_fintype _)
  have hsit : ∑ᶠ x, ((AbelianFieldFacts.vertexTerm (halfFluxAngle L (2 * f)) B x : ℝ) : ℂ) =
      inner ℂ (∑ μ, covShiftAdjSubOne (halfFluxAngle L (2 * f)) μ (coord w μ))
        (∑ μ, covShiftAdjSubOne (halfFluxAngle L (2 * f)) μ (coord w μ)) := by
    refine finsum_eq_of_hasSum hH ?_
    have h := hasSum_conj_mul (∑ μ, covShiftAdjSubOne (halfFluxAngle L (2 * f)) μ (coord w μ))
      (∑ μ, covShiftAdjSubOne (halfFluxAngle L (2 * f)) μ (coord w μ))
    have e : ∀ x : FullSpace.Vertex L 0 0,
        ((AbelianFieldFacts.vertexTerm (halfFluxAngle L (2 * f)) B x : ℝ) : ℂ) =
          conj ((∑ μ, covShiftAdjSubOne (halfFluxAngle L (2 * f)) μ (coord w μ)) x 0) *
            (∑ μ, covShiftAdjSubOne (halfFluxAngle L (2 * f)) μ (coord w μ)) x 0 := by
      intro x
      rw [Complex.conj_mul', sum_apply_zero]
      simp [AbelianFieldFacts.vertexTerm, ht, hsf]
    rw [funext e]
    exact h
  rw [Complex.ofReal_add, hc₁, hc₂, hpl, hsit]
  unfold pairsForm
  rw [Fintype.sum_sum_type]
  congr 1
  · simp only [Fintype.sum_prod_type]
  · rw [← sum_vertexTerm_eval hR hS w, sum_inner]
    simp only [inner_sum]
    symm
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    simp [chargedTermPair]
end YangMills.Construction.Tower.ConstantFieldSymbols.ChargedPairsFormProof
end
