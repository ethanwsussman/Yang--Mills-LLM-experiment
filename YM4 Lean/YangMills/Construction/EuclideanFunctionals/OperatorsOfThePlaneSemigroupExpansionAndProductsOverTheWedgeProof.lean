import YangMills.Construction.ComplexAnalysis.BanachValuedAffineCoordinates
import YangMills.Construction.EuclideanFunctionals.ForwardTubeAndTheSemigroupOfItsOperatorsProof
import YangMills.Construction.EuclideanFunctionals.MeasuresAndOperatorsOfTheReconstruction
import YangMills.Construction.SpectralTheory.CalculusOfBoundedBorelFunctionsOnTheWholeSpace
import Mathlib
set_option autoImplicit false
open Set MeasureTheory Filter Topology
noncomputable section
namespace YangMills.Construction.EuclideanFunctionals.TubeSemigroup
open ForwardTube (lightConePlus lightConeMinus forwardTube closedForwardTube tubeStar embedPlane
  ofLightConeCoords pairTupleEquiv pairTupleEquiv_apply_fst pairTupleEquiv_apply_snd
  HolomorphicVectorOnTuples lightConePlus_ofLightConeCoords lightConeMinus_ofLightConeCoords
  ofLightConeCoords_lightConePlus_lightConeMinus)
section Holomorphy
def pairFlatEquiv (α : Type) (p : ℕ) : (Fin p → α × α) ≃ (Fin (p * 2) → α) :=
  (Equiv.piCongrRight fun _ => (finTwoArrowEquiv α).symm).trans
    ((Equiv.curry (Fin p) (Fin 2) α).symm.trans
      (Equiv.arrowCongr finProdFinEquiv (Equiv.refl α)))
theorem pairFlatEquiv_apply_zero {α : Type} {p : ℕ} (m : Fin p → α × α) (i : Fin p) :
    pairFlatEquiv α p m (finProdFinEquiv (i, 0)) = (m i).1 := by
  simp [pairFlatEquiv, Equiv.arrowCongr, Equiv.curry]
theorem pairFlatEquiv_apply_one {α : Type} {p : ℕ} (m : Fin p → α × α) (i : Fin p) :
    pairFlatEquiv α p m (finProdFinEquiv (i, 1)) = (m i).2 := by
  simp [pairFlatEquiv, Equiv.arrowCongr, Equiv.curry]
theorem flat_ext {α : Type} {p : ℕ} {z z' : Fin (p * 2) → α}
    (h₀ : ∀ i, z (finProdFinEquiv (i, 0)) = z' (finProdFinEquiv (i, 0)))
    (h₁ : ∀ i, z (finProdFinEquiv (i, 1)) = z' (finProdFinEquiv (i, 1))) : z = z' := by
  funext x
  obtain ⟨⟨i, t⟩, rfl⟩ := finProdFinEquiv.surjective x
  exact (Fin.forall_fin_two (p := fun t => z (finProdFinEquiv (i, t)) = z' (finProdFinEquiv (i, t)))).2
    ⟨h₀ i, h₁ i⟩ t
def pairTupleLinearEquiv (p : ℕ) : (Fin p → ℂ × ℂ) ≃ₗ[ℂ] Coordinates.ComplexCoordinates (p * 2) :=
  { pairTupleEquiv p with
    map_add' := fun a b => by
      refine flat_ext (fun i => ?_) (fun i => ?_)
      · show pairTupleEquiv p (a + b) _ = pairTupleEquiv p a _ + pairTupleEquiv p b _
        rw [pairTupleEquiv_apply_fst, pairTupleEquiv_apply_fst, pairTupleEquiv_apply_fst]
        rfl
      · show pairTupleEquiv p (a + b) _ = pairTupleEquiv p a _ + pairTupleEquiv p b _
        rw [pairTupleEquiv_apply_snd, pairTupleEquiv_apply_snd, pairTupleEquiv_apply_snd]
        rfl
    map_smul' := fun s a => by
      refine flat_ext (fun i => ?_) (fun i => ?_)
      · show pairTupleEquiv p (s • a) _ = s * pairTupleEquiv p a _
        rw [pairTupleEquiv_apply_fst, pairTupleEquiv_apply_fst]
        rfl
      · show pairTupleEquiv p (s • a) _ = s * pairTupleEquiv p a _
        rw [pairTupleEquiv_apply_snd, pairTupleEquiv_apply_snd]
        rfl }
def lightConeLinearEquiv : (ℂ × ℂ) ≃ₗ[ℂ] (ℂ × ℂ) where
  toFun v := (lightConePlus v, lightConeMinus v)
  invFun w := ofLightConeCoords w.1 w.2
  map_add' a b := Prod.ext (by simp only [lightConePlus, Prod.fst_add, Prod.snd_add]; ring)
    (by simp only [lightConeMinus, Prod.fst_add, Prod.snd_add]; ring)
  map_smul' s a := Prod.ext (by simp [lightConePlus]; ring) (by simp [lightConeMinus]; ring)
  left_inv v := ofLightConeCoords_lightConePlus_lightConeMinus v
  right_inv w := Prod.ext (lightConePlus_ofLightConeCoords _ _) (lightConeMinus_ofLightConeCoords _ _)
def tupleLightConeEquiv (p : ℕ) : (Fin p → ℂ × ℂ) ≃ₗ[ℂ] (Fin p → ℂ × ℂ) :=
  LinearEquiv.piCongrRight fun _ => lightConeLinearEquiv
def ofFlatLightCone {p : ℕ} (c : Coordinates.ComplexCoordinates (p * 2)) : Fin p → ℂ × ℂ :=
  (tupleLightConeEquiv p).symm ((pairTupleLinearEquiv p).symm c)
theorem lightConePlus_ofFlatLightCone {p : ℕ} (c : Coordinates.ComplexCoordinates (p * 2)) (i : Fin p) :
    lightConePlus (ofFlatLightCone c i) = c (finProdFinEquiv (i, 0)) := by
  have h : ofFlatLightCone c i = ofLightConeCoords ((pairTupleEquiv p).symm c i).1
      ((pairTupleEquiv p).symm c i).2 := rfl
  rw [h, lightConePlus_ofLightConeCoords, ← pairTupleEquiv_apply_fst, Equiv.apply_symm_apply]
theorem lightConeMinus_ofFlatLightCone {p : ℕ} (c : Coordinates.ComplexCoordinates (p * 2)) (i : Fin p) :
    lightConeMinus (ofFlatLightCone c i) = c (finProdFinEquiv (i, 1)) := by
  have h : ofFlatLightCone c i = ofLightConeCoords ((pairTupleEquiv p).symm c i).1
      ((pairTupleEquiv p).symm c i).2 := rfl
  rw [h, lightConeMinus_ofLightConeCoords, ← pairTupleEquiv_apply_snd, Equiv.apply_symm_apply]
theorem ofFlatLightCone_add {p : ℕ} (c w : Coordinates.ComplexCoordinates (p * 2)) :
    ofFlatLightCone (c + w) = ofFlatLightCone c + ofFlatLightCone w := by
  simp [ofFlatLightCone, map_add]
theorem order_pairFlatEquiv {p : ℕ} (m : Fin p → ℕ × ℕ) :
    PowerSeries.MultiIndex.order (pairFlatEquiv ℕ p m) = ∑ i, ((m i).1 + (m i).2) := by
  unfold PowerSeries.MultiIndex.order
  rw [← Equiv.sum_comp finProdFinEquiv, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fin.sum_univ_two, pairFlatEquiv_apply_zero, pairFlatEquiv_apply_one]
theorem monomial_pairFlatEquiv {p : ℕ} (w : Coordinates.ComplexCoordinates (p * 2)) (m : Fin p → ℕ × ℕ) :
    PowerSeries.MultiIndex.monomial w (pairFlatEquiv ℕ p m) =
      ∏ i, w (finProdFinEquiv (i, 0)) ^ (m i).1 * w (finProdFinEquiv (i, 1)) ^ (m i).2 := by
  unfold PowerSeries.MultiIndex.monomial
  rw [← Equiv.prod_comp finProdFinEquiv, Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Fin.prod_univ_two, pairFlatEquiv_apply_zero, pairFlatEquiv_apply_one]
def flatLightConeEquiv (p : ℕ) :
    Coordinates.ComplexCoordinates (p * 2) ≃ₗ[ℂ] Coordinates.ComplexCoordinates (p * 2) :=
  (pairTupleLinearEquiv p).symm ≪≫ₗ tupleLightConeEquiv p ≪≫ₗ pairTupleLinearEquiv p
theorem ofFlatLightCone_flatLightConeEquiv {p : ℕ} (z : Coordinates.ComplexCoordinates (p * 2)) :
    ofFlatLightCone (flatLightConeEquiv p z) = (pairTupleEquiv p).symm z := by
  simp only [ofFlatLightCone, flatLightConeEquiv, LinearEquiv.trans_apply,
    LinearEquiv.symm_apply_apply]
  rfl
theorem holomorphicVectorOnTuples_of_lightConeSeries
    (hHol : BanachValued.AffineCoordinates.HolomorphicCompositionProperties)
    {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℂ Y] [CompleteSpace Y] {p : ℕ} (hp : 1 ≤ p)
    (f : (Fin p → ℂ × ℂ) → Y)
    (h : ∀ v ∈ pi univ fun _ : Fin p => forwardTube, ∃ (ρ : ℝ) (A : (Fin p → ℕ × ℕ) → Y), 0 < ρ ∧
      (∀ i, ρ < (lightConePlus (v i)).re ∧ ρ < (lightConeMinus (v i)).re) ∧
      Summable (fun m : Fin p → ℕ × ℕ => ‖A m‖ * ρ ^ ∑ i, ((m i).1 + (m i).2)) ∧
      ∀ d : Fin p → ℂ × ℂ, (∀ i, ‖lightConePlus (d i)‖ ≤ ρ ∧ ‖lightConeMinus (d i)‖ ≤ ρ) →
        HasSum (fun m : Fin p → ℕ × ℕ =>
          (∏ i, lightConePlus (d i) ^ (m i).1 * lightConeMinus (d i) ^ (m i).2) • A m) (f (v + d))) :
    HolomorphicVectorOnTuples (pi univ fun _ : Fin p => forwardTube) f := by
  classical
  set O' : Set (Coordinates.ComplexCoordinates (p * 2)) := {c | ∀ a, 0 < (c a).re} with hO'def
  have hO' : IsOpen O' := by
    have hi : O' = ⋂ a, {c : Coordinates.ComplexCoordinates (p * 2) | 0 < (c a).re} := by
      ext c
      simp [hO'def]
    rw [hi]
    exact isOpen_iInter_of_finite fun a =>
      isOpen_lt continuous_const (Complex.continuous_re.comp (continuous_apply a))
  set g : Coordinates.ComplexCoordinates (p * 2) → Y := fun c => f (ofFlatLightCone c) with hg
  have hgh : BanachValued.IsHolomorphicOnOpen O' g := by
    refine ⟨hO', Or.inl ⟨by omega, fun c hc => ?_⟩⟩
    have hv : ofFlatLightCone c ∈ pi univ fun _ : Fin p => forwardTube := by
      intro i _
      exact ⟨by rw [lightConePlus_ofFlatLightCone]; exact hc _,
        by rw [lightConeMinus_ofFlatLightCone]; exact hc _⟩
    obtain ⟨ρ, A, hρ, hlt, hsum, hser⟩ := h _ hv
    refine ⟨ρ, fun γ => A ((pairFlatEquiv ℕ p).symm γ), ⟨hρ, ?_, ?_, ?_⟩⟩
    · intro z hz x
      have hzx : ‖z x - c x‖ ≤ ρ := (norm_le_pi_norm (z - c) x).trans hz
      have hre : |(z x - c x).re| ≤ ρ := (Complex.abs_re_le_norm _).trans hzx
      have hcx : ρ < (c x).re := by
        obtain ⟨⟨i, t⟩, rfl⟩ := finProdFinEquiv.surjective x
        refine (Fin.forall_fin_two
          (p := fun t => ρ < (c (finProdFinEquiv (i, t))).re)).2 ⟨?_, ?_⟩ t
        · rw [← lightConePlus_ofFlatLightCone c i]; exact (hlt i).1
        · rw [← lightConeMinus_ofFlatLightCone c i]; exact (hlt i).2
      have := (abs_le.mp hre).1
      simp only [Complex.sub_re] at this
      linarith
    · refine (pairFlatEquiv ℕ p).summable_iff.mp ?_
      refine hsum.congr fun m => ?_
      simp only [Function.comp_apply, Equiv.symm_apply_apply, order_pairFlatEquiv]
    · intro w hw
      refine (pairFlatEquiv ℕ p).hasSum_iff.mp ?_
      have hd := hser (ofFlatLightCone w) fun i =>
        ⟨by rw [lightConePlus_ofFlatLightCone]; exact (norm_le_pi_norm w _).trans hw,
          by rw [lightConeMinus_ofFlatLightCone]; exact (norm_le_pi_norm w _).trans hw⟩
      simp only [lightConePlus_ofFlatLightCone, lightConeMinus_ofFlatLightCone] at hd
      have hfun : ((fun γ => PowerSeries.MultiIndex.monomial w γ • A ((pairFlatEquiv ℕ p).symm γ)) ∘
          pairFlatEquiv ℕ p) = fun m : Fin p → ℕ × ℕ =>
          (∏ i, w (finProdFinEquiv (i, 0)) ^ (m i).1 * w (finProdFinEquiv (i, 1)) ^ (m i).2) •
            A m := by
        funext m
        simp only [Function.comp_apply, Equiv.symm_apply_apply, monomial_pairFlatEquiv]
      rw [hfun]
      show HasSum _ (f (ofFlatLightCone (c + w)))
      rw [ofFlatLightCone_add]
      exact hd
  set M := flatLightConeEquiv p with hM
  set J : Matrix (Fin (p * 2)) (Fin (p * 2)) ℂ := LinearMap.toMatrix' M.toLinearMap with hJdef
  have hJ : IsUnit J := by
    have hinv : J * LinearMap.toMatrix' M.symm.toLinearMap = 1 := by
      rw [hJdef, ← LinearMap.toMatrix'_comp]
      simp
    exact ⟨⟨J, _, hinv, mul_eq_one_comm.mp hinv⟩, rfl⟩
  have hmul : ∀ z, J.mulVec z = M z := fun z => LinearMap.toMatrix'_mulVec _ _
  have key : ∀ z : Coordinates.ComplexCoordinates (p * 2),
      (∀ a, 0 < (M z a).re) ↔ ∀ i, (pairTupleEquiv p).symm z i ∈ forwardTube := by
    intro z
    rw [← ofFlatLightCone_flatLightConeEquiv]
    constructor
    · intro hz i
      exact ⟨by rw [lightConePlus_ofFlatLightCone]; exact hz _,
        by rw [lightConeMinus_ofFlatLightCone]; exact hz _⟩
    · intro hz a
      obtain ⟨⟨i, t⟩, rfl⟩ := finProdFinEquiv.surjective a
      refine (Fin.forall_fin_two
        (p := fun t => 0 < (M z (finProdFinEquiv (i, t))).re)).2 ⟨?_, ?_⟩ t
      · rw [← lightConePlus_ofFlatLightCone (M z) i]; exact (hz i).1
      · rw [← lightConeMinus_ofFlatLightCone (M z) i]; exact (hz i).2
  have hres := ((hHol Y (p * 2) (by omega) O' g hgh).2.2 J 0 hJ).1
  have hset : {z | J.mulVec z + 0 ∈ O'} = pairTupleEquiv p '' (pi univ fun _ => forwardTube) := by
    ext z
    simp only [mem_ofPred_eq, add_zero, hmul, hO'def]
    rw [key]
    constructor
    · intro hz
      exact ⟨(pairTupleEquiv p).symm z, fun i _ => hz i, Equiv.apply_symm_apply _ _⟩
    · rintro ⟨v, hv, rfl⟩ i
      rw [Equiv.symm_apply_apply]
      exact hv i (mem_univ i)
  have hfun : (fun z => g (J.mulVec z + 0)) = f ∘ (pairTupleEquiv p).symm := by
    funext z
    simp only [add_zero, hmul, hg, Function.comp_apply]
    rw [hM, ofFlatLightCone_flatLightConeEquiv]
  rw [hset, hfun] at hres
  exact hres
end Holomorphy
section Calculus
open BorelSpectral WholeSpaceSpectral
open BorelCalculus (IsBoundedFn conjFn)
open SpectralPoint hiding lightConePlus lightConeMinus
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
def liftPlane (f : EPlanePoints → ℂ) : (Fin 2 → ℝ) → ℂ := fun y => f ⟨y, mem_univ y⟩
theorem isBoundedMeasurableFn_liftPlane {f : EPlanePoints → ℂ} (hf : Measurable f) {c : ℝ}
    (hc : ∀ y, ‖f y‖ ≤ c) : IsBoundedMeasurableFn (liftPlane f) :=
  ⟨hf.comp (measurable_id.subtype_mk), c, fun _ => hc _⟩
def wedgeCut (f : EPlanePoints → ℂ) : EPlanePoints → ℂ := wedge.1.indicator f
theorem wedgeCut_of_mem (f : EPlanePoints → ℂ) {y : EPlanePoints} (hy : y ∈ wedge.1) :
    wedgeCut f y = f y :=
  indicator_of_mem hy f
theorem wedgeCut_of_notMem (f : EPlanePoints → ℂ) {y : EPlanePoints} (hy : y ∉ wedge.1) :
    wedgeCut f y = 0 :=
  indicator_of_notMem hy f
theorem measurable_wedgeCut {f : EPlanePoints → ℂ} (hf : Measurable f) : Measurable (wedgeCut f) :=
  hf.indicator wedge.2
theorem norm_wedgeCut_le {f : EPlanePoints → ℂ} {c : ℝ} (hc : 0 ≤ c) (h : ∀ y ∈ wedge.1, ‖f y‖ ≤ c)
    (y : EPlanePoints) : ‖wedgeCut f y‖ ≤ c := by
  by_cases hy : y ∈ wedge.1
  · rw [wedgeCut_of_mem f hy]; exact h y hy
  · rw [wedgeCut_of_notMem f hy]; simpa using hc
def BoundedOnWedge (f : EPlanePoints → ℂ) : Prop :=
  Measurable f ∧ ∃ c : ℝ, 0 ≤ c ∧ ∀ y ∈ wedge.1, ‖f y‖ ≤ c
theorem isBoundedMeasurableFn_wedgeCut {f : EPlanePoints → ℂ} (hf : BoundedOnWedge f) :
    IsBoundedMeasurableFn (liftPlane (wedgeCut f)) := by
  obtain ⟨hm, c, hc, h⟩ := hf
  exact isBoundedMeasurableFn_liftPlane (measurable_wedgeCut hm) (norm_wedgeCut_le hc h)
def overWedge (E : SpectralMeasureOnSpace 2 H) (f : EPlanePoints → ℂ) : H →L[ℂ] H :=
  E.integralOp (wedgeCut f)
theorem zeroExtend_wedge (f : EPlanePoints → ℂ) :
    zeroExtend wedge.1 (fun p : wedge.1 => f p.1) = wedgeCut f := by
  funext y
  by_cases hy : y ∈ wedge.1
  · simp [zeroExtend, wedgeCut_of_mem f hy, hy]
  · simp [zeroExtend, wedgeCut_of_notMem f hy, hy]
theorem integralOpOn_wedge (E : SpectralMeasureOnSpace 2 H) (f : EPlanePoints → ℂ) :
    E.integralOpOn wedge (fun p => f p.1) = overWedge E f := by
  unfold SpectralMeasure.integralOpOn overWedge
  rw [zeroExtend_wedge]
theorem boundedOnWedge_sum {α : Type} (F : Finset α) {g : α → EPlanePoints → ℂ}
    (hg : ∀ a, BoundedOnWedge (g a)) : BoundedOnWedge fun y => ∑ a ∈ F, g a y := by
  classical
  induction F using Finset.induction_on with
  | empty => exact ⟨measurable_const, 0, le_rfl, by simp⟩
  | insert a F ha ih =>
    obtain ⟨hm, c, hc, h⟩ := ih
    obtain ⟨hm', c', hc', h'⟩ := hg a
    refine ⟨?_, c' + c, add_nonneg hc' hc, fun y hy => ?_⟩
    · simp only [Finset.sum_insert ha]
      exact hm'.add hm
    · show ‖∑ b ∈ insert a F, g b y‖ ≤ c' + c
      rw [Finset.sum_insert ha]
      exact (norm_add_le _ _).trans (add_le_add (h' y hy) (h y hy))
variable {E : SpectralMeasureOnSpace 2 H} (R : BoundedCalculusLaws E)
include R
theorem overWedge_add_smul {f g : EPlanePoints → ℂ} (hf : BoundedOnWedge f) (hg : BoundedOnWedge g)
    (s : ℂ) : overWedge E (fun y => f y + s * g y) = overWedge E f + s • overWedge E g := by
  have h := R.add_smul _ _ (isBoundedMeasurableFn_wedgeCut hf) (isBoundedMeasurableFn_wedgeCut hg) s
  have e : wedgeCut (fun y => f y + s * g y) =
      fun y => (liftPlane (wedgeCut f) + s • liftPlane (wedgeCut g)) y.1 := by
    funext y
    by_cases hy : y ∈ wedge.1
    · simp [liftPlane, wedgeCut_of_mem _ hy]
    · simp [liftPlane, wedgeCut_of_notMem _ hy]
  unfold overWedge
  rw [e]
  exact h
theorem overWedge_mul {f g : EPlanePoints → ℂ} (hf : BoundedOnWedge f) (hg : BoundedOnWedge g) :
    overWedge E (fun y => f y * g y) = overWedge E f * overWedge E g := by
  have h := R.mul _ _ (isBoundedMeasurableFn_wedgeCut hf) (isBoundedMeasurableFn_wedgeCut hg)
  have e : wedgeCut (fun y => f y * g y) = fun y => (liftPlane (wedgeCut f) * liftPlane (wedgeCut g)) y.1 := by
    funext y
    by_cases hy : y ∈ wedge.1
    · simp [liftPlane, wedgeCut_of_mem _ hy]
    · simp [liftPlane, wedgeCut_of_notMem _ hy]
  unfold overWedge
  rw [e]
  exact h
theorem overWedge_star {f : EPlanePoints → ℂ} (hf : BoundedOnWedge f) :
    star (overWedge E f) = overWedge E (fun y => (starRingEnd ℂ) (f y)) := by
  have h := R.adjoint _ (isBoundedMeasurableFn_wedgeCut hf)
  have e : wedgeCut (fun y => (starRingEnd ℂ) (f y)) =
      fun y => conjFn (liftPlane (wedgeCut f)) y.1 := by
    funext y
    by_cases hy : y ∈ wedge.1
    · simp [liftPlane, conjFn, wedgeCut_of_mem _ hy]
    · simp [liftPlane, conjFn, wedgeCut_of_notMem _ hy]
  unfold overWedge
  rw [e]
  exact h
theorem overWedge_norm_sq {f : EPlanePoints → ℂ} (hf : BoundedOnWedge f) (ψ : H) :
    ‖overWedge E f ψ‖ ^ 2 = ∫ y, ‖wedgeCut f y‖ ^ 2 ∂E.diagMeasure ψ :=
  R.norm_sq _ (isBoundedMeasurableFn_wedgeCut hf) ψ
theorem overWedge_opNorm_le {f : EPlanePoints → ℂ} (hm : Measurable f) {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ y ∈ wedge.1, ‖f y‖ ≤ c) : ‖overWedge E f‖ ≤ c := by
  refine ContinuousLinearMap.opNorm_le_bound _ hc fun ψ => ?_
  have hn := overWedge_norm_sq R ⟨hm, c, hc, h⟩ ψ
  have hb : ∀ᵐ y ∂E.diagMeasure ψ, ‖‖wedgeCut f y‖ ^ 2‖ ≤ c ^ 2 := by
    refine Eventually.of_forall fun y => ?_
    rw [norm_pow, norm_norm]
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_wedgeCut_le hc h y) 2
  have hi := norm_integral_le_of_norm_le_const hb
  have hu : (E.diagMeasure ψ).real univ = ‖ψ‖ ^ 2 := by
    rw [Measure.real, SpectralMeasure.diagMeasure_univ,
      ENNReal.toReal_ofReal (by positivity)]
  rw [hu, ← hn, norm_pow, norm_norm] at hi
  have : ‖overWedge E f ψ‖ ^ 2 ≤ (c * ‖ψ‖) ^ 2 := by rw [mul_pow]; exact hi
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp this
theorem overWedge_sub_opNorm_le {f g : EPlanePoints → ℂ} (hf : BoundedOnWedge f)
    (hg : BoundedOnWedge g) {c : ℝ} (hc : 0 ≤ c) (h : ∀ y ∈ wedge.1, ‖f y - g y‖ ≤ c) :
    ‖overWedge E f - overWedge E g‖ ≤ c := by
  have e := overWedge_add_smul R hf hg (-1)
  have e' : overWedge E f + (-1 : ℂ) • overWedge E g = overWedge E f - overWedge E g := by
    rw [neg_one_smul, sub_eq_add_neg]
  rw [← e', ← e]
  refine overWedge_opNorm_le R (hf.1.add (measurable_const.mul hg.1)) hc fun y hy => ?_
  have : f y + -1 * g y = f y - g y := by ring
  show ‖f y + -1 * g y‖ ≤ c
  rw [this]
  exact h y hy
theorem overWedge_zero : overWedge E (fun _ => 0) = 0 := by
  have h := overWedge_opNorm_le R (f := fun _ => 0) measurable_const le_rfl (by simp)
  exact norm_le_zero_iff.mp h
theorem overWedge_const_mul {f : EPlanePoints → ℂ} (hf : BoundedOnWedge f) (s : ℂ) :
    overWedge E (fun y => s * f y) = s • overWedge E f := by
  have h0 : BoundedOnWedge fun _ => 0 := ⟨measurable_const, 0, le_rfl, by simp⟩
  have h := overWedge_add_smul R h0 hf s
  simpa [overWedge_zero R] using h
theorem overWedge_sum {α : Type} (F : Finset α) {g : α → EPlanePoints → ℂ}
    (hg : ∀ a, BoundedOnWedge (g a)) :
    overWedge E (fun y => ∑ a ∈ F, g a y) = ∑ a ∈ F, overWedge E (g a) := by
  classical
  induction F using Finset.induction_on with
  | empty => simpa using overWedge_zero R
  | insert a F ha ih =>
    have h := overWedge_add_smul R (hg a) (boundedOnWedge_sum F hg) 1
    simp only [one_mul, one_smul] at h
    simp only [Finset.sum_insert ha]
    rw [h, ih]
end Calculus
section Requirements
open BorelSpectral WholeSpaceSpectral
open SpectralPoint hiding lightConePlus lightConeMinus
open EuclidFunctionalWithRecon
open TubeOperatorForms (WedgeInLightConeCoords)
variable {c : SharpScale} {S : ConnFamily} (σ : EuclidFunctionalWithRecon c S)
theorem wedgeIntegralOp_eq_overWedge (v : ℂ × ℂ) :
    σ.wedgeIntegralOp v = overWedge σ.planeMeasure (planeExpKernel v) :=
  integralOpOn_wedge _ _
theorem wedgeIntegralOp_apply_eq (f : EPlanePoints → ℂ) :
    σ.wedgeOp (fun p => f p.1) = overWedge σ.planeMeasure f :=
  integralOpOn_wedge _ _
theorem continuous_planeExpKernel (v : ℂ × ℂ) : Continuous (planeExpKernel v) := by
  have h₀ : Continuous fun p : EPlanePoints => ((p.1 0 : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp ((continuous_apply 0).comp continuous_subtype_val)
  have h₁ : Continuous fun p : EPlanePoints => ((p.1 1 : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp ((continuous_apply 1).comp continuous_subtype_val)
  exact Complex.continuous_exp.comp ((continuous_const.mul h₀).neg.add (continuous_const.mul h₁))
theorem continuous_planeExpKernel_left (y : EPlanePoints) :
    Continuous fun v : ℂ × ℂ => planeExpKernel v y := by
  unfold planeExpKernel
  fun_prop
theorem lightConePlus_add (v w : ℂ × ℂ) : lightConePlus (v + w) = lightConePlus v + lightConePlus w :=
  congrArg Prod.fst (lightConeLinearEquiv.map_add v w)
theorem lightConeMinus_add (v w : ℂ × ℂ) :
    lightConeMinus (v + w) = lightConeMinus v + lightConeMinus w :=
  congrArg Prod.snd (lightConeLinearEquiv.map_add v w)
theorem lightConePlus_tubeStar (v : ℂ × ℂ) :
    lightConePlus (tubeStar v) = (starRingEnd ℂ) (lightConePlus v) := by apply _root_.YangMills.Construction.EuclideanFunctionals.TubeSemigroup.lightConePlus_tubeStar_eq_conj <;> assumption
theorem lightConeMinus_tubeStar (v : ℂ × ℂ) :
    lightConeMinus (tubeStar v) = (starRingEnd ℂ) (lightConeMinus v) := by apply _root_.YangMills.Construction.EuclideanFunctionals.TubeSemigroup.lightConeMinus_tubeStar_eq_conj <;> assumption
theorem planeExpKernel_mul (v v' : ℂ × ℂ) (p : EPlanePoints) :
    planeExpKernel v p * planeExpKernel v' p = planeExpKernel (v + v') p := by
  unfold planeExpKernel
  rw [← Complex.exp_add]
  congr 1
  simp only [Prod.fst_add, Prod.snd_add]
  ring
theorem conj_planeExpKernel (v : ℂ × ℂ) (p : EPlanePoints) :
    (starRingEnd ℂ) (planeExpKernel v p) = planeExpKernel (tubeStar v) p := by
  unfold planeExpKernel
  rw [← Complex.exp_conj]
  congr 1
  simp [tubeStar]
theorem planeExpKernel_zero (p : EPlanePoints) : planeExpKernel 0 p = 1 := by
  simp [planeExpKernel]
theorem zero_mem_closedForwardTube : (0 : ℂ × ℂ) ∈ closedForwardTube := by
  simp [closedForwardTube, lightConePlus, lightConeMinus]
theorem boundedOnWedge_planeExpKernel (hW : WedgeInLightConeCoords)
    {v : ℂ × ℂ} (hv : v ∈ closedForwardTube) : BoundedOnWedge (planeExpKernel v) :=
  ⟨(continuous_planeExpKernel v).measurable, 1, zero_le_one, hW.2.2 v hv⟩
theorem boundedOnWedge_one : BoundedOnWedge fun _ => 1 :=
  ⟨measurable_const, 1, zero_le_one, by simp⟩
def planeWedgeSet : BorelSubsets (Fin 2 → ℝ) :=
  ⟨{y | |y 1| ≤ y 0}, measurableSet_le (measurable_pi_apply 1).abs (measurable_pi_apply 0)⟩
theorem restrictToUniv_planeWedgeSet : restrictToUniv planeWedgeSet = wedge := rfl
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
theorem isSupportedOn_planeWedgeSet {E : SpectralMeasureOnSpace 2 H}
    (hcar : E ⟨wedge.1ᶜ, wedge.2.compl⟩ = 0) : IsSupportedOn E planeWedgeSet := by
  unfold IsSupportedOn SpectralMeasure.IsCarriedBy
  rw [restrictToUniv_planeWedgeSet]
  exact hcar
theorem overWedge_eq_integralOp {E : SpectralMeasureOnSpace 2 H}
    (hC : SupportLaws E planeWedgeSet) {f : EPlanePoints → ℂ} (hf : Measurable f) {b : ℝ}
    (hb : 0 ≤ b) (hbd : ∀ y, ‖f y‖ ≤ b) : overWedge E f = E.integralOp f := by
  refine hC.congr (liftPlane (wedgeCut f)) (liftPlane f)
    (isBoundedMeasurableFn_wedgeCut ⟨hf, b, hb, fun y _ => hbd y⟩)
    (isBoundedMeasurableFn_liftPlane hf hbd) ?_
  intro x hx
  exact wedgeCut_of_mem f (show (⟨x, mem_univ x⟩ : EPlanePoints) ∈ wedge.1 from hx)
theorem overWedge_one {E : SpectralMeasureOnSpace 2 H} (R : BoundedCalculusLaws E)
    (hC : SupportLaws E planeWedgeSet) : overWedge E (fun _ => 1) = 1 := by
  rw [overWedge_eq_integralOp hC measurable_const zero_le_one (by simp)]
  exact R.one
theorem contractionSemigroup (hW : WedgeInLightConeCoords)
    (R : BoundedCalculusLaws σ.planeMeasure)
    (hC : SupportLaws σ.planeMeasure planeWedgeSet)
    (hImg : σ.MeasureFacts) (hVac : σ.VacEnergyZero) :
    ContractionSemigroup σ := by
  have hT0 : σ.wedgeIntegralOp 0 = 1 := by
    rw [wedgeIntegralOp_eq_overWedge, ← overWedge_one R hC]
    congr 1
    funext p
    exact planeExpKernel_zero p
  refine ⟨hT0, fun v hv v' hv' => ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · refine ⟨?_, ?_⟩
    · rw [lightConePlus_add, Complex.add_re]; exact add_nonneg hv.1 hv'.1
    · rw [lightConeMinus_add, Complex.add_re]; exact add_nonneg hv.2 hv'.2
  · refine ⟨?_, ?_⟩
    · rw [lightConePlus_tubeStar, Complex.conj_re]; exact hv.1
    · rw [lightConeMinus_tubeStar, Complex.conj_re]; exact hv.2
  · rw [wedgeIntegralOp_eq_overWedge]
    exact overWedge_opNorm_le R (continuous_planeExpKernel v).measurable zero_le_one (hW.2.2 v hv)
  · simp only [wedgeIntegralOp_eq_overWedge]
    rw [← overWedge_mul R (boundedOnWedge_planeExpKernel hW hv) (boundedOnWedge_planeExpKernel hW hv')]
    congr 1
    funext p
    exact planeExpKernel_mul v v' p
  · simp only [wedgeIntegralOp_eq_overWedge]
    rw [overWedge_star R (boundedOnWedge_planeExpKernel hW hv)]
    congr 1
    funext p
    exact conj_planeExpKernel v p
  · set Ω := σ.recon.vac with hΩ
    have hf := boundedOnWedge_planeExpKernel hW hv
    have hs := overWedge_add_smul R hf boundedOnWedge_one (-1)
    rw [overWedge_one R hC] at hs
    have hsb : BoundedOnWedge fun y => planeExpKernel v y + -1 * 1 :=
      ⟨hf.1.add measurable_const, 2, by norm_num, fun y hy => by
        refine (norm_add_le _ _).trans ?_
        have := hW.2.2 v hv y hy
        simp only [mul_one, norm_neg, norm_one]
        linarith⟩
    have hn := overWedge_norm_sq R hsb Ω
    have hset : MeasurableSet {y : EPlanePoints | ¬ y.1 0 = 0} :=
      (measurableSet_eq_fun ((measurable_pi_apply 0).comp measurable_subtype_coe)
        measurable_const).compl
    have hμ : σ.planeMeasure.diagMeasure Ω {y : EPlanePoints | ¬ y.1 0 = 0} = 0 := by
      have h₁ : σ.planeMeasure.diagMeasure Ω =
          (σ.spectralMeasureAt Ω).map energyMomentumPlane := hImg.planeDiagMeasure_eq Ω
      rw [h₁, Measure.map_apply measurable_energyMomentumPlane hset]
      exact hVac.2.2
    have hz : ∫ y, ‖wedgeCut (fun y => planeExpKernel v y + -1 * 1) y‖ ^ 2
        ∂σ.planeMeasure.diagMeasure Ω = 0 := by
      refine integral_eq_zero_of_ae ?_
      have hae : ∀ᵐ y ∂σ.planeMeasure.diagMeasure Ω, y.1 0 = 0 := ae_iff.mpr hμ
      filter_upwards [hae] with y hy
      by_cases hw : y ∈ wedge.1
      · have h1 : y.1 1 = 0 := by
          have : |y.1 1| ≤ y.1 0 := hw
          rw [hy] at this
          exact abs_nonpos_iff.mp this
        rw [wedgeCut_of_mem _ hw]
        simp [planeExpKernel, hy, h1]
      · rw [wedgeCut_of_notMem _ hw]
        simp
    rw [hz, hs] at hn
    have h0 : (σ.wedgeIntegralOp v - 1) Ω = 0 := by
      have h2 : (overWedge σ.planeMeasure (planeExpKernel v) + (-1 : ℂ) • 1) Ω = 0 :=
        norm_eq_zero.mp (pow_eq_zero_iff (two_ne_zero) |>.mp hn)
      rw [wedgeIntegralOp_eq_overWedge, sub_eq_add_neg, ← neg_one_smul ℂ (1 : σ.space →L[ℂ] _)]
      exact h2
    have h3 := sub_eq_zero.mp (by simpa using h0 :
      σ.wedgeIntegralOp v Ω - Ω = 0)
    exact h3
theorem strongContinuity (hW : WedgeInLightConeCoords)
    (R : BoundedCalculusLaws σ.planeMeasure) : StrongContinuity σ := by
  intro ψ v hv
  set E := σ.planeMeasure with hE
  let D : ℂ × ℂ → EPlanePoints → ℂ := fun w y => planeExpKernel w y + -1 * planeExpKernel v y
  have hDm : ∀ w, Measurable (D w) := fun w =>
    ((continuous_planeExpKernel w).add
      (continuous_const.mul (continuous_planeExpKernel v))).measurable
  have hD2 : ∀ w ∈ closedForwardTube, ∀ y ∈ wedge.1, ‖D w y‖ ≤ 2 := fun w hw y hy => by
    refine (norm_add_le _ _).trans ?_
    have h₁ := hW.2.2 w hw y hy
    have h₂ := hW.2.2 v hv y hy
    simp only [norm_mul, norm_neg, norm_one, one_mul]
    linarith
  have hsq : ∀ w ∈ closedForwardTube,
      ‖σ.wedgeIntegralOp w ψ - σ.wedgeIntegralOp v ψ‖ ^ 2 =
        ∫ y, ‖wedgeCut (D w) y‖ ^ 2 ∂E.diagMeasure ψ := fun w hw => by
    have hs := overWedge_add_smul R (boundedOnWedge_planeExpKernel hW hw)
      (boundedOnWedge_planeExpKernel hW hv) (-1)
    rw [← overWedge_norm_sq R ⟨hDm w, 2, by norm_num, hD2 w hw⟩ ψ]
    show _ = ‖overWedge E (fun y => planeExpKernel w y + -1 * planeExpKernel v y) ψ‖ ^ 2
    rw [hs, wedgeIntegralOp_eq_overWedge, wedgeIntegralOp_eq_overWedge]
    simp [sub_eq_add_neg]
    rfl
  have hlim : Tendsto (fun w => ∫ y, ‖wedgeCut (D w) y‖ ^ 2 ∂E.diagMeasure ψ)
      (𝓝[closedForwardTube] v) (𝓝 (∫ _, (0 : ℝ) ∂E.diagMeasure ψ)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun _ => (4 : ℝ)) ?_ ?_ ?_ ?_
    · exact Eventually.of_forall fun w =>
        ((measurable_wedgeCut (hDm w)).norm.pow_const 2).aestronglyMeasurable
    · filter_upwards [self_mem_nhdsWithin] with w hw
      refine Eventually.of_forall fun y => ?_
      rw [norm_pow, norm_norm]
      have := norm_wedgeCut_le (by norm_num : (0 : ℝ) ≤ 2) (hD2 w hw) y
      nlinarith [norm_nonneg (wedgeCut (D w) y)]
    · exact integrable_const _
    · refine Eventually.of_forall fun y => ?_
      by_cases hy : y ∈ wedge.1
      · simp only [wedgeCut_of_mem _ hy]
        have hc : Continuous fun w => ‖D w y‖ ^ 2 :=
          (((continuous_planeExpKernel_left y).add continuous_const).norm).pow 2
        have h0 : ‖D v y‖ ^ 2 = 0 := by simp [D]
        have := hc.tendsto v
        rw [h0] at this
        exact this.mono_left nhdsWithin_le_nhds
      · simp only [wedgeCut_of_notMem _ hy]
        simpa using tendsto_const_nhds
  have hsqrt := hlim.sqrt
  simp only [integral_zero, Real.sqrt_zero] at hsqrt
  have hgoal : Tendsto (fun w => ‖σ.wedgeIntegralOp w ψ - σ.wedgeIntegralOp v ψ‖)
      (𝓝[closedForwardTube] v) (𝓝 0) := by
    refine hsqrt.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with w hw
    rw [← hsq w hw, Real.sqrt_sq (norm_nonneg _)]
  exact tendsto_iff_norm_sub_tendsto_zero.mpr hgoal
end Requirements
section Expansion
open BorelSpectral WholeSpaceSpectral
open SpectralPoint hiding lightConePlus lightConeMinus
open EuclidFunctionalWithRecon
open TubeOperatorForms (WedgeInLightConeCoords)
variable {c : SharpScale} {S : ConnFamily} (σ : EuclidFunctionalWithRecon c S)
theorem lightCone_nonneg_of_mem_wedge {p : EPlanePoints} (hp : p ∈ wedge.1) :
    0 ≤ SpectralPoint.lightConePlus p ∧ 0 ≤ SpectralPoint.lightConeMinus p := by
  have h : |p.1 1| ≤ p.1 0 := hp
  have h' := abs_le.mp h
  unfold SpectralPoint.lightConePlus SpectralPoint.lightConeMinus
  constructor <;> linarith [h'.1, h'.2]
theorem continuous_lightConePlus : Continuous SpectralPoint.lightConePlus :=
  continuous_const.mul (((continuous_apply 0).comp continuous_subtype_val).sub
    ((continuous_apply 1).comp continuous_subtype_val))
theorem continuous_lightConeMinus : Continuous SpectralPoint.lightConeMinus :=
  continuous_const.mul (((continuous_apply 0).comp continuous_subtype_val).add
    ((continuous_apply 1).comp continuous_subtype_val))
theorem continuous_expansionKernel (j k : ℕ) (v : ℂ × ℂ) :
    Continuous (expansionKernel j k v) :=
  (((Complex.continuous_ofReal.comp continuous_lightConePlus).pow j).mul
    ((Complex.continuous_ofReal.comp continuous_lightConeMinus).pow k)).mul
    (continuous_planeExpKernel v)
theorem pow_mul_exp_neg_le {ρ s : ℝ} (hρ : 0 < ρ) (hs : 0 ≤ s) (j : ℕ) :
    s ^ j * Real.exp (-(ρ * s)) ≤ j.factorial * (ρ ^ j)⁻¹ := by
  have h := Real.pow_div_factorial_le_exp (ρ * s) (by positivity) j
  have hj : (0 : ℝ) < j.factorial := by positivity
  have hρj : 0 < ρ ^ j := by positivity
  rw [div_le_iff₀ hj, mul_pow] at h
  rw [← div_eq_mul_inv, le_div_iff₀ hρj, Real.exp_neg]
  have he := Real.exp_pos (ρ * s)
  rw [mul_right_comm, ← div_eq_mul_inv, div_le_iff₀ he]
  linarith
theorem norm_expansionKernel_le (hW : WedgeInLightConeCoords) {v : ℂ × ℂ}
    (hv : v ∈ forwardTube) (j k : ℕ) {p : EPlanePoints} (hp : p ∈ wedge.1) :
    ‖expansionKernel j k v p‖ ≤
      (j.factorial * ((lightConePlus v).re ^ j)⁻¹) * (k.factorial * ((lightConeMinus v).re ^ k)⁻¹) := by
  obtain ⟨hu₁, hu₂⟩ := lightCone_nonneg_of_mem_wedge hp
  have hn := (hW.2.1 p v).2.2
  unfold expansionKernel
  rw [norm_mul, norm_mul, norm_pow, norm_pow, hn, Complex.norm_real, Complex.norm_real,
    Real.norm_of_nonneg hu₁, Real.norm_of_nonneg hu₂, sub_eq_add_neg, Real.exp_add]
  have a := pow_mul_exp_neg_le hv.1 hu₁ j
  have b := pow_mul_exp_neg_le hv.2 hu₂ k
  calc SpectralPoint.lightConePlus p ^ j * SpectralPoint.lightConeMinus p ^ k *
        (Real.exp (-((lightConePlus v).re * SpectralPoint.lightConePlus p)) *
          Real.exp (-((lightConeMinus v).re * SpectralPoint.lightConeMinus p)))
      = (SpectralPoint.lightConePlus p ^ j *
          Real.exp (-((lightConePlus v).re * SpectralPoint.lightConePlus p))) *
        (SpectralPoint.lightConeMinus p ^ k *
          Real.exp (-((lightConeMinus v).re * SpectralPoint.lightConeMinus p))) := by
        ring
    _ ≤ _ := mul_le_mul a b (by positivity) (by have := hv.1.lt; positivity)
theorem expansionOp_eq (v : ℂ × ℂ) (j k : ℕ) :
    σ.expansionOp v j k =
      ((-1 : ℂ) ^ (j + k) / ((j.factorial : ℂ) * (k.factorial : ℂ))) •
        overWedge σ.planeMeasure (expansionKernel j k v) := by
  unfold EuclidFunctionalWithRecon.expansionOp
  rw [wedgeIntegralOp_apply_eq]
theorem boundedOnWedge_expansionKernel (hW : WedgeInLightConeCoords) {v : ℂ × ℂ}
    (hv : v ∈ forwardTube) (j k : ℕ) : BoundedOnWedge (expansionKernel j k v) := by
  have h₁ := hv.1.lt
  have h₂ := hv.2.lt
  exact ⟨(continuous_expansionKernel j k v).measurable, _, by positivity,
    fun p hp => norm_expansionKernel_le hW hv j k hp⟩
theorem norm_expansionCoeff (j k : ℕ) :
    ‖(-1 : ℂ) ^ (j + k) / ((j.factorial : ℂ) * (k.factorial : ℂ))‖ =
      ((j.factorial : ℝ) * (k.factorial : ℝ))⁻¹ := by
  simp
theorem norm_expansionOp_le (hW : WedgeInLightConeCoords)
    (R : BoundedCalculusLaws σ.planeMeasure) {v : ℂ × ℂ} (hv : v ∈ forwardTube) (j k : ℕ) :
    ‖σ.expansionOp v j k‖ ≤ ((lightConePlus v).re ^ j)⁻¹ * ((lightConeMinus v).re ^ k)⁻¹ := by
  have h₁ := hv.1.lt
  have h₂ := hv.2.lt
  have hb := overWedge_opNorm_le R (continuous_expansionKernel j k v).measurable
    (by positivity) fun p hp => norm_expansionKernel_le hW hv j k hp
  rw [expansionOp_eq, norm_smul, norm_expansionCoeff]
  calc ((j.factorial : ℝ) * (k.factorial : ℝ))⁻¹ * _
      ≤ ((j.factorial : ℝ) * (k.factorial : ℝ))⁻¹ *
        ((j.factorial * ((lightConePlus v).re ^ j)⁻¹) * (k.factorial * ((lightConeMinus v).re ^ k)⁻¹)) :=
        mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by field_simp
def expansionTerm (x y : ℂ) (v : ℂ × ℂ) (a : ℕ × ℕ) (p : EPlanePoints) : ℂ :=
  (x ^ a.1 * y ^ a.2) * (((-1 : ℂ) ^ (a.1 + a.2) /
    ((a.1.factorial : ℂ) * (a.2.factorial : ℂ))) * expansionKernel a.1 a.2 v p)
theorem hasSum_exp_mul_exp (e x y u u' : ℂ) :
    HasSum (fun a : ℕ × ℕ => (x ^ a.1 * y ^ a.2) * (((-1 : ℂ) ^ (a.1 + a.2) /
      ((a.1.factorial : ℂ) * (a.2.factorial : ℂ))) * (u ^ a.1 * u' ^ a.2 * e)))
      (e * (Complex.exp (-(x * u)) * Complex.exp (-(y * u')))) := by
  have hA : HasSum (fun j : ℕ => (-(x * u)) ^ j / (j.factorial : ℂ)) (Complex.exp (-(x * u))) := by
    rw [Complex.exp_eq_exp_ℂ]
    exact NormedSpace.expSeries_div_hasSum_exp _
  have hB : HasSum (fun j : ℕ => (-(y * u')) ^ j / (j.factorial : ℂ))
      (Complex.exp (-(y * u'))) := by
    rw [Complex.exp_eq_exp_ℂ]
    exact NormedSpace.expSeries_div_hasSum_exp _
  have hs : Summable fun a : ℕ × ℕ => ((-(x * u)) ^ a.1 / (a.1.factorial : ℂ) *
      ((-(y * u')) ^ a.2 / (a.2.factorial : ℂ))) :=
    summable_mul_of_summable_norm (f := fun j : ℕ => (-(x * u)) ^ j / (j.factorial : ℂ))
      (g := fun j : ℕ => (-(y * u')) ^ j / (j.factorial : ℂ)) hA.summable.norm hB.summable.norm
  have hAB := HasSum.mul (f := fun j : ℕ => (-(x * u)) ^ j / (j.factorial : ℂ))
    (g := fun j : ℕ => (-(y * u')) ^ j / (j.factorial : ℂ)) hA hB hs
  have hC := hAB.mul_left e
  have e₂ : (fun a : ℕ × ℕ => (x ^ a.1 * y ^ a.2) * (((-1 : ℂ) ^ (a.1 + a.2) /
      ((a.1.factorial : ℂ) * (a.2.factorial : ℂ))) * (u ^ a.1 * u' ^ a.2 * e))) =
      fun a : ℕ × ℕ => e *
      ((-(x * u)) ^ a.1 / (a.1.factorial : ℂ) * ((-(y * u')) ^ a.2 / (a.2.factorial : ℂ))) := by
    funext a
    rw [neg_pow (x * u), neg_pow (y * u'), mul_pow, mul_pow, pow_add]
    ring
  rw [e₂]
  exact hC
theorem hasSum_expansionTerm (hW : WedgeInLightConeCoords)
    (v w : ℂ × ℂ) (p : EPlanePoints) :
    HasSum (fun a => expansionTerm (lightConePlus w) (lightConeMinus w) v a p)
      (planeExpKernel (v + w) p) := by
  have e₁ : planeExpKernel (v + w) p =
      planeExpKernel v p * (Complex.exp (-(lightConePlus w * (SpectralPoint.lightConePlus p : ℂ))) *
        Complex.exp (-(lightConeMinus w * (SpectralPoint.lightConeMinus p : ℂ)))) := by
    rw [(hW.2.1 p (v + w)).2.1, (hW.2.1 p v).2.1, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    rw [lightConePlus_add, lightConeMinus_add]
    ring
  rw [e₁]
  exact hasSum_exp_mul_exp _ _ _ _ _
theorem norm_expansionTerm_le (hW : WedgeInLightConeCoords) {v : ℂ × ℂ}
    (hv : v ∈ forwardTube) (x y : ℂ) (a : ℕ × ℕ) {p : EPlanePoints} (hp : p ∈ wedge.1) :
    ‖expansionTerm x y v a p‖ ≤
      (‖x‖ / (lightConePlus v).re) ^ a.1 * (‖y‖ / (lightConeMinus v).re) ^ a.2 := by
  have h₁ := hv.1.lt
  have h₂ := hv.2.lt
  have hb := norm_expansionKernel_le hW hv a.1 a.2 hp
  unfold expansionTerm
  rw [norm_mul, norm_mul, norm_mul, norm_expansionCoeff, norm_pow, norm_pow]
  calc ‖x‖ ^ a.1 * ‖y‖ ^ a.2 * (((a.1.factorial : ℝ) * (a.2.factorial : ℝ))⁻¹ * _)
      ≤ ‖x‖ ^ a.1 * ‖y‖ ^ a.2 * (((a.1.factorial : ℝ) * (a.2.factorial : ℝ))⁻¹ *
        ((a.1.factorial * ((lightConePlus v).re ^ a.1)⁻¹) *
          (a.2.factorial * ((lightConeMinus v).re ^ a.2)⁻¹))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hb (by positivity)) (by positivity)
    _ = _ := by
        rw [div_pow, div_pow]
        field_simp
theorem smul_expansionOp_eq_overWedge (hW : WedgeInLightConeCoords)
    (R : BoundedCalculusLaws σ.planeMeasure) {v : ℂ × ℂ} (hv : v ∈ forwardTube) (x y : ℂ)
    (a : ℕ × ℕ) :
    (x ^ a.1 * y ^ a.2) • σ.expansionOp v a.1 a.2 =
      overWedge σ.planeMeasure (expansionTerm x y v a) := by
  have hb := boundedOnWedge_expansionKernel hW hv a.1 a.2
  have hb' : BoundedOnWedge fun p => ((-1 : ℂ) ^ (a.1 + a.2) /
      ((a.1.factorial : ℂ) * (a.2.factorial : ℂ))) * expansionKernel a.1 a.2 v p := by
    obtain ⟨hm, C, hC, h⟩ := hb
    refine ⟨measurable_const.mul hm, ‖(-1 : ℂ) ^ (a.1 + a.2) /
      ((a.1.factorial : ℂ) * (a.2.factorial : ℂ))‖ * C, by positivity, fun p hp => ?_⟩
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (h p hp) (norm_nonneg _)
  unfold expansionTerm
  rw [overWedge_const_mul R hb', overWedge_const_mul R hb, expansionOp_eq]
theorem add_mem_forwardTube {v w : ℂ × ℂ} (hx : ‖lightConePlus w‖ < (lightConePlus v).re)
    (hy : ‖lightConeMinus w‖ < (lightConeMinus v).re) : v + w ∈ forwardTube := by
  refine ⟨?_, ?_⟩
  · rw [lightConePlus_add, Complex.add_re]
    have := (abs_le.mp (Complex.abs_re_le_norm (lightConePlus w))).1
    show 0 < _
    linarith
  · rw [lightConeMinus_add, Complex.add_re]
    have := (abs_le.mp (Complex.abs_re_le_norm (lightConeMinus w))).1
    show 0 < _
    linarith
theorem mem_closedForwardTube_of_mem {v : ℂ × ℂ} (hv : v ∈ forwardTube) : v ∈ closedForwardTube :=
  ⟨hv.1.le, hv.2.le⟩
theorem hasSum_expansionOp (hW : WedgeInLightConeCoords)
    (R : BoundedCalculusLaws σ.planeMeasure) {v w : ℂ × ℂ} (hv : v ∈ forwardTube)
    (hx : ‖lightConePlus w‖ < (lightConePlus v).re) (hy : ‖lightConeMinus w‖ < (lightConeMinus v).re) :
    Summable (fun a : ℕ × ℕ =>
      ‖(lightConePlus w ^ a.1 * lightConeMinus w ^ a.2) • σ.expansionOp v a.1 a.2‖) ∧
    HasSum (fun a : ℕ × ℕ =>
      (lightConePlus w ^ a.1 * lightConeMinus w ^ a.2) • σ.expansionOp v a.1 a.2)
      (σ.wedgeIntegralOp (v + w)) := by
  have h₁ := hv.1.lt
  have h₂ := hv.2.lt
  have hX : ‖lightConePlus w‖ / (lightConePlus v).re < 1 := (div_lt_one h₁).mpr hx
  have hY : ‖lightConeMinus w‖ / (lightConeMinus v).re < 1 := (div_lt_one h₂).mpr hy
  have hX0 : 0 ≤ ‖lightConePlus w‖ / (lightConePlus v).re := by positivity
  have hY0 : 0 ≤ ‖lightConeMinus w‖ / (lightConeMinus v).re := by positivity
  have hm : Summable fun a : ℕ × ℕ =>
      (‖lightConePlus w‖ / (lightConePlus v).re) ^ a.1 *
        (‖lightConeMinus w‖ / (lightConeMinus v).re) ^ a.2 :=
    (summable_geometric_of_lt_one hX0 hX).mul_of_nonneg (summable_geometric_of_lt_one hY0 hY)
      (fun _ => by positivity) (fun _ => by positivity)
  have hn : ∀ a : ℕ × ℕ,
      ‖(lightConePlus w ^ a.1 * lightConeMinus w ^ a.2) • σ.expansionOp v a.1 a.2‖ ≤
        (‖lightConePlus w‖ / (lightConePlus v).re) ^ a.1 *
          (‖lightConeMinus w‖ / (lightConeMinus v).re) ^ a.2 := fun a => by
    rw [norm_smul, norm_mul, norm_pow, norm_pow, div_pow, div_pow, div_eq_mul_inv, div_eq_mul_inv]
    calc _ ≤ ‖lightConePlus w‖ ^ a.1 * ‖lightConeMinus w‖ ^ a.2 *
          (((lightConePlus v).re ^ a.1)⁻¹ * ((lightConeMinus v).re ^ a.2)⁻¹) :=
          mul_le_mul_of_nonneg_left (norm_expansionOp_le σ hW R hv a.1 a.2)
            (by positivity)
      _ = _ := by ring
  have hsn := Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hn hm
  refine ⟨hsn, ?_⟩
  have hvw := add_mem_forwardTube hx hy
  have hT := boundedOnWedge_planeExpKernel hW (mem_closedForwardTube_of_mem hvw)
  have hb : ∀ a, BoundedOnWedge (expansionTerm (lightConePlus w) (lightConeMinus w) v a) := fun a =>
    ⟨(((continuous_const.mul (continuous_const.mul
      (continuous_expansionKernel a.1 a.2 v))).measurable)), _, by positivity,
      fun p hp => norm_expansionTerm_le hW hv _ _ a hp⟩
  show Tendsto _ (SummationFilter.unconditional _).filter _
  rw [SummationFilter.unconditional_filter, Metric.tendsto_nhds]
  intro ε hε
  have hu := tendstoUniformlyOn_tsum hm (s := wedge.1)
    (f := fun a p => expansionTerm (lightConePlus w) (lightConeMinus w) v a p)
    (fun a p hp => norm_expansionTerm_le hW hv _ _ a hp)
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hu (ε / 2) (half_pos hε)] with F hF
  rw [dist_comm, dist_eq_norm]
  have e₁ : ∑ a ∈ F, (lightConePlus w ^ a.1 * lightConeMinus w ^ a.2) • σ.expansionOp v a.1 a.2 =
      overWedge σ.planeMeasure
        (fun p => ∑ a ∈ F, expansionTerm (lightConePlus w) (lightConeMinus w) v a p) := by
    rw [overWedge_sum R F hb]
    exact Finset.sum_congr rfl fun a _ => smul_expansionOp_eq_overWedge σ hW R hv _ _ a
  rw [e₁, wedgeIntegralOp_eq_overWedge]
  refine lt_of_le_of_lt (overWedge_sub_opNorm_le R hT (boundedOnWedge_sum F hb) (half_pos hε).le
    fun p hp => ?_) (half_lt_self hε)
  have h := hF p hp
  rw [(hasSum_expansionTerm hW v w p).tsum_eq, dist_eq_norm] at h
  exact h.le
end Expansion
section Preliminaries
open BorelSpectral WholeSpaceSpectral
open SpectralPoint hiding lightConePlus lightConeMinus
open EuclidFunctionalWithRecon
open TubeOperatorForms (WedgeInLightConeCoords)
variable {c : SharpScale} {S : ConnFamily} (σ : EuclidFunctionalWithRecon c S)
theorem exists_radius_lt {p : ℕ} (hp : 1 ≤ p) (v : Fin p → ℂ × ℂ)
    (hv : v ∈ pi univ fun _ : Fin p => forwardTube) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ i, ρ < (lightConePlus (v i)).re ∧ ρ < (lightConeMinus (v i)).re := by
  have : Nonempty (Fin p) := ⟨⟨0, hp⟩⟩
  obtain ⟨i₀, h₀⟩ := Finite.exists_min fun i => min (lightConePlus (v i)).re (lightConeMinus (v i)).re
  have hpos : 0 < min (lightConePlus (v i₀)).re (lightConeMinus (v i₀)).re :=
    lt_min (hv i₀ (mem_univ _)).1 (hv i₀ (mem_univ _)).2
  refine ⟨_, half_pos hpos, fun i => ?_⟩
  have hh := h₀ i
  exact ⟨lt_of_lt_of_le (half_lt_self hpos) (hh.trans (min_le_left _ _)),
    lt_of_lt_of_le (half_lt_self hpos) (hh.trans (min_le_right _ _))⟩
theorem norm_ofReal_pos {ρ : ℝ} (hρ : 0 < ρ) : ‖(ρ : ℂ)‖ = ρ := by
  rw [Complex.norm_real, Real.norm_of_nonneg hρ.le]
theorem holomorphic_wedgeIntegralOp
    (hHol : BanachValued.AffineCoordinates.HolomorphicCompositionProperties)
    (hW : WedgeInLightConeCoords)
    (R : BoundedCalculusLaws σ.planeMeasure) :
    HolomorphicVectorOnTuples {x : Fin 1 → ℂ × ℂ | x 0 ∈ forwardTube}
      fun x => σ.wedgeIntegralOp (x 0) := by
  have hset : {x : Fin 1 → ℂ × ℂ | x 0 ∈ forwardTube} = pi univ fun _ => forwardTube := by
    ext x
    simp [Set.mem_pi, Fin.forall_fin_one]
  rw [hset]
  refine holomorphicVectorOnTuples_of_lightConeSeries hHol le_rfl _ fun v hv => ?_
  obtain ⟨ρ, hρ, hlt⟩ := exists_radius_lt le_rfl v hv
  have h0 := hv 0 (mem_univ 0)
  have hk := hlt 0
  refine ⟨ρ, fun m => σ.expansionOp (v 0) (m 0).1 (m 0).2, hρ, hlt, ?_, ?_⟩
  · have hs := (hasSum_expansionOp σ hW R (w := ofLightConeCoords ρ ρ) h0
      (by rw [lightConePlus_ofLightConeCoords, norm_ofReal_pos hρ]; exact hk.1)
      (by rw [lightConeMinus_ofLightConeCoords, norm_ofReal_pos hρ]; exact hk.2)).1
    have hc := (Equiv.funUnique (Fin 1) (ℕ × ℕ)).summable_iff.mpr hs
    refine hc.congr fun m => ?_
    simp only [Function.comp_apply, lightConePlus_ofLightConeCoords, lightConeMinus_ofLightConeCoords,
      norm_smul, norm_mul, norm_pow, norm_ofReal_pos hρ, Equiv.funUnique_apply, Fin.default_eq_zero,
      Finset.univ_unique, Finset.sum_singleton, pow_add]
    ring
  · intro d hd
    have hb := hd 0
    have hs := (hasSum_expansionOp σ hW R (w := d 0) h0 (hb.1.trans_lt hk.1)
      (hb.2.trans_lt hk.2)).2
    have hc := (Equiv.funUnique (Fin 1) (ℕ × ℕ)).hasSum_iff.mpr hs
    have e : ((fun a : ℕ × ℕ => (lightConePlus (d 0) ^ a.1 * lightConeMinus (d 0) ^ a.2) •
        σ.expansionOp (v 0) a.1 a.2) ∘ (Equiv.funUnique (Fin 1) (ℕ × ℕ))) =
        fun m : Fin 1 → ℕ × ℕ => (∏ i, lightConePlus (d i) ^ (m i).1 * lightConeMinus (d i) ^ (m i).2) •
          σ.expansionOp (v 0) (m 0).1 (m 0).2 := by
      funext m
      simp [Fin.default_eq_zero]
    rw [e] at hc
    exact hc
def wordCoeff (ψ : σ.space) :
    (p : ℕ) → (Fin (p + 1) → σ.space →L[ℂ] σ.space) → (Fin p → ℂ × ℂ) →
      (Fin p → ℕ × ℕ) → σ.space
  | 0, A, _, _ => A 0 ψ
  | p + 1, A, v, m =>
    A 0 (σ.expansionOp (v 0) (m 0).1 (m 0).2
      (wordCoeff ψ p (Fin.tail A) (Fin.tail v) (Fin.tail m)))
theorem hasSum_apply_prod {α β X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X]
    [CompleteSpace X] {f : α → X →L[ℂ] X} {g : β → X} {T : X →L[ℂ] X} {ξ : X}
    (hf : Summable fun a => ‖f a‖) (hg : Summable fun b => ‖g b‖) (hT : HasSum f T)
    (hξ : HasSum g ξ) :
    Summable (fun x : α × β => ‖f x.1 (g x.2)‖) ∧ HasSum (fun x : α × β => f x.1 (g x.2)) (T ξ) := by
  have hsn : Summable fun x : α × β => ‖f x.1‖ * ‖g x.2‖ :=
    hf.mul_of_nonneg hg (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
  have h₁ : Summable fun x : α × β => ‖f x.1 (g x.2)‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun x => (f x.1).le_opNorm _) hsn
  refine ⟨h₁, ?_⟩
  have hs : Summable fun x : α × β => f x.1 (g x.2) := h₁.of_norm
  have hfib : ∀ a, HasSum (fun b => f a (g b)) (f a ξ) := fun a => (f a).hasSum hξ
  have hout : HasSum (fun a => f a ξ) (T ξ) :=
    (ContinuousLinearMap.apply ℂ X ξ).hasSum hT
  have hp := hs.hasSum.prod_fiberwise hfib
  rw [← hp.unique hout]
  exact hs.hasSum
def consEquiv (p : ℕ) : ((ℕ × ℕ) × (Fin p → ℕ × ℕ)) ≃ (Fin (p + 1) → ℕ × ℕ) where
  toFun x := Fin.cons x.1 x.2
  invFun m := (m 0, Fin.tail m)
  left_inv x := by simp
  right_inv m := Fin.cons_self_tail m
theorem consEquiv_apply (p : ℕ) (x : (ℕ × ℕ) × (Fin p → ℕ × ℕ)) :
    consEquiv p x = Fin.cons x.1 x.2 := rfl
def incrementMonomial {p : ℕ} (d : Fin p → ℂ × ℂ) (m : Fin p → ℕ × ℕ) : ℂ :=
  ∏ i, lightConePlus (d i) ^ (m i).1 * lightConeMinus (d i) ^ (m i).2
theorem hasSum_tubeWord (hW : WedgeInLightConeCoords)
    (R : BoundedCalculusLaws σ.planeMeasure) (ψ : σ.space) :
    ∀ (p : ℕ) (A : Fin (p + 1) → σ.space →L[ℂ] σ.space) (v d : Fin p → ℂ × ℂ),
      v ∈ (pi univ fun _ : Fin p => forwardTube) →
      (∀ i, ‖lightConePlus (d i)‖ < (lightConePlus (v i)).re ∧
        ‖lightConeMinus (d i)‖ < (lightConeMinus (v i)).re) →
      Summable (fun m : Fin p → ℕ × ℕ => ‖incrementMonomial d m • wordCoeff σ ψ p A v m‖) ∧
      HasSum (fun m : Fin p → ℕ × ℕ => incrementMonomial d m • wordCoeff σ ψ p A v m)
        (σ.tubeWord ψ p A (v + d)) := by
  intro p
  induction p with
  | zero =>
    intro A v d _ _
    have h : HasSum (fun m : Fin 0 → ℕ × ℕ => incrementMonomial d m • wordCoeff σ ψ 0 A v m)
        (A 0 ψ) := by
      simp [incrementMonomial, wordCoeff]
    exact ⟨(hasSum_unique _).summable, h⟩
  | succ p ih =>
    intro A v d hv hd
    have hv0 := hv 0 (mem_univ 0)
    have hvt : Fin.tail v ∈ pi univ fun _ : Fin p => forwardTube := fun i _ => hv i.succ (mem_univ _)
    obtain ⟨ha, hb⟩ := hasSum_expansionOp σ hW R (w := d 0) hv0 (hd 0).1 (hd 0).2
    obtain ⟨hc, he⟩ := ih (Fin.tail A) (Fin.tail v) (Fin.tail d) hvt fun i => hd i.succ
    obtain ⟨h₁, h₂⟩ := hasSum_apply_prod ha hc hb he
    have hterm : ∀ x : (ℕ × ℕ) × (Fin p → ℕ × ℕ),
        incrementMonomial d ((consEquiv p) x) •
            wordCoeff σ ψ (p + 1) A v ((consEquiv p) x) =
          A 0 (((lightConePlus (d 0) ^ x.1.1 * lightConeMinus (d 0) ^ x.1.2) •
            σ.expansionOp (v 0) x.1.1 x.1.2)
            (incrementMonomial (Fin.tail d) x.2 •
              wordCoeff σ ψ p (Fin.tail A) (Fin.tail v) x.2)) := by
      rintro ⟨a, b⟩
      have e₁ : incrementMonomial d (Fin.cons a b) =
          (lightConePlus (d 0) ^ a.1 * lightConeMinus (d 0) ^ a.2) *
            incrementMonomial (Fin.tail d) b := by
        unfold incrementMonomial
        rw [Fin.prod_univ_succ]
        simp [Fin.tail]
      simp only [consEquiv_apply, wordCoeff, e₁, Fin.cons_zero, Fin.tail_cons]
      simp only [_root_.smul_apply, map_smul, smul_smul]
      rw [mul_comm]
    refine ⟨?_, ?_⟩
    · refine (consEquiv p).summable_iff.mp ?_
      have hs : Summable fun x : (ℕ × ℕ) × (Fin p → ℕ × ℕ) =>
          ‖A 0‖ * ‖((lightConePlus (d 0) ^ x.1.1 * lightConeMinus (d 0) ^ x.1.2) •
            σ.expansionOp (v 0) x.1.1 x.1.2)
            (incrementMonomial (Fin.tail d) x.2 •
              wordCoeff σ ψ p (Fin.tail A) (Fin.tail v) x.2)‖ := h₁.mul_left _
      refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun x => ?_) hs
      simp only [Function.comp_apply, hterm x]
      exact (A 0).le_opNorm _
    · refine (consEquiv p).hasSum_iff.mp ?_
      have hs := (A 0).hasSum h₂
      have e₂ : σ.tubeWord ψ (p + 1) A (v + d) =
          A 0 (σ.wedgeIntegralOp (v 0 + d 0)
            (σ.tubeWord ψ p (Fin.tail A) (Fin.tail v + Fin.tail d))) := rfl
      rw [e₂]
      have e₃ : ((fun m : Fin (p + 1) → ℕ × ℕ =>
          incrementMonomial d m • wordCoeff σ ψ (p + 1) A v m) ∘
          (consEquiv p)) = fun x => A 0 (((lightConePlus (d 0) ^ x.1.1 * lightConeMinus (d 0) ^ x.1.2) •
            σ.expansionOp (v 0) x.1.1 x.1.2)
            (incrementMonomial (Fin.tail d) x.2 •
              wordCoeff σ ψ p (Fin.tail A) (Fin.tail v) x.2)) := funext hterm
      rw [e₃]
      exact hs
end Preliminaries
section Conclusion
open BorelSpectral WholeSpaceSpectral
open BorelCalculus (IsBoundedFn)
open SpectralPoint hiding lightConePlus lightConeMinus
open EuclidFunctionalWithRecon
open TubeOperatorForms (WedgeInLightConeCoords)
variable {c : SharpScale} {S : ConnFamily} (σ : EuclidFunctionalWithRecon c S)
theorem norm_tubeWord_le (hT : ∀ v ∈ closedForwardTube, ‖σ.wedgeIntegralOp v‖ ≤ 1)
    (ψ : σ.space) :
    ∀ (p : ℕ) (A : Fin (p + 1) → σ.space →L[ℂ] σ.space) (v : Fin p → ℂ × ℂ),
      v ∈ (pi univ fun _ : Fin p => closedForwardTube) →
      ‖σ.tubeWord ψ p A v‖ ≤ (∏ i, ‖A i‖) * ‖ψ‖ := by
  intro p
  induction p with
  | zero =>
    intro A v _
    simpa [EuclidFunctionalWithRecon.tubeWord] using (A 0).le_opNorm ψ
  | succ p ih =>
    intro A v hv
    have h₁ := ih (Fin.tail A) (Fin.tail v) fun i _ => hv i.succ (mem_univ _)
    have h₂ := hT (v 0) (hv 0 (mem_univ 0))
    have e : σ.tubeWord ψ (p + 1) A v = A 0 (σ.wedgeIntegralOp (v 0)
        (σ.tubeWord ψ p (Fin.tail A) (Fin.tail v))) := rfl
    rw [e, Fin.prod_univ_succ, mul_assoc]
    refine ((A 0).le_opNorm _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
    refine ((σ.wedgeIntegralOp (v 0)).le_opNorm _).trans ?_
    calc _ ≤ 1 * ‖σ.tubeWord ψ p (Fin.tail A) (Fin.tail v)‖ :=
          mul_le_mul_of_nonneg_right h₂ (norm_nonneg _)
      _ ≤ _ := by rw [one_mul]; exact h₁
theorem continuousOn_wedgeIntegralOp_apply
    (hT : ∀ v ∈ closedForwardTube, ‖σ.wedgeIntegralOp v‖ ≤ 1)
    (hc : StrongContinuity σ) :
    ContinuousOn (fun x : (ℂ × ℂ) × σ.space => σ.wedgeIntegralOp x.1 x.2)
      (closedForwardTube ×ˢ univ) := by
  rintro ⟨v', ξ'⟩ ⟨hv', -⟩
  unfold ContinuousWithinAt
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hfst : Tendsto (fun x : (ℂ × ℂ) × σ.space => x.1)
      (𝓝[closedForwardTube ×ˢ univ] (v', ξ')) (𝓝[closedForwardTube] v') := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      (continuous_fst.continuousWithinAt) ?_
    filter_upwards [self_mem_nhdsWithin] with x hx using hx.1
  have hsnd : Tendsto (fun x : (ℂ × ℂ) × σ.space => ‖x.2 - ξ'‖)
      (𝓝[closedForwardTube ×ˢ univ] (v', ξ')) (𝓝 0) := by
    have h : Continuous fun x : (ℂ × ℂ) × σ.space => ‖x.2 - ξ'‖ :=
      (continuous_snd.sub continuous_const).norm
    have := h.tendsto (v', ξ')
    simp only [sub_self, norm_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hone : Tendsto (fun x : (ℂ × ℂ) × σ.space =>
      ‖σ.wedgeIntegralOp x.1 ξ' - σ.wedgeIntegralOp v' ξ'‖)
      (𝓝[closedForwardTube ×ˢ univ] (v', ξ')) (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.mp ((hc ξ' v' hv').tendsto.comp hfst)
  have hsum := hsnd.add hone
  rw [add_zero] at hsum
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hsum
  filter_upwards [self_mem_nhdsWithin] with x hx
  have e : σ.wedgeIntegralOp x.1 x.2 - σ.wedgeIntegralOp v' ξ' =
      σ.wedgeIntegralOp x.1 (x.2 - ξ') +
        (σ.wedgeIntegralOp x.1 ξ' - σ.wedgeIntegralOp v' ξ') := by
    rw [map_sub]
    abel
  show ‖σ.wedgeIntegralOp x.1 x.2 - σ.wedgeIntegralOp v' ξ'‖ ≤ _
  rw [e]
  refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
  refine ((σ.wedgeIntegralOp x.1).le_opNorm _).trans ?_
  calc _ ≤ 1 * ‖x.2 - ξ'‖ := mul_le_mul_of_nonneg_right (hT _ hx.1) (norm_nonneg _)
    _ = _ := one_mul _
theorem continuousOn_tubeWord (hT : ∀ v ∈ closedForwardTube, ‖σ.wedgeIntegralOp v‖ ≤ 1)
    (hc : StrongContinuity σ) (ψ : σ.space) :
    ∀ (p : ℕ) (A : Fin (p + 1) → σ.space →L[ℂ] σ.space),
      ContinuousOn (σ.tubeWord ψ p A) (pi univ fun _ : Fin p => closedForwardTube) := by
  intro p
  induction p with
  | zero =>
    intro A
    exact continuousOn_const
  | succ p ih =>
    intro A
    have htail : Continuous fun v : Fin (p + 1) → ℂ × ℂ => (Fin.tail v : Fin p → ℂ × ℂ) :=
      continuous_pi fun i => continuous_apply i.succ
    have hmap : ContinuousOn (fun v : Fin (p + 1) → ℂ × ℂ =>
        (v 0, σ.tubeWord ψ p (Fin.tail A) (Fin.tail v)))
        (pi univ fun _ : Fin (p + 1) => closedForwardTube) :=
      (continuous_apply 0).continuousOn.prodMk
        ((ih (Fin.tail A)).comp htail.continuousOn fun v hv i _ => hv i.succ (mem_univ _))
    have hj := (continuousOn_wedgeIntegralOp_apply σ hT hc).comp hmap
      (fun v hv => ⟨hv 0 (mem_univ 0), mem_univ _⟩)
    exact (A 0).continuous.comp_continuousOn hj
theorem holomorphic_tubeWord
    (hHol : BanachValued.AffineCoordinates.HolomorphicCompositionProperties)
    (hW : WedgeInLightConeCoords)
    (R : BoundedCalculusLaws σ.planeMeasure) (ψ : σ.space) (p : ℕ)
    (A : Fin (p + 1) → σ.space →L[ℂ] σ.space) :
    HolomorphicVectorOnTuples (pi univ fun _ : Fin p => forwardTube) (σ.tubeWord ψ p A) := by
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · have hsub : Subsingleton (Coordinates.ComplexCoordinates (0 * 2)) :=
      ⟨fun a b => funext fun x => absurd x.2 (by simp)⟩
    have hU : pairTupleEquiv 0 '' (pi univ fun _ : Fin 0 => forwardTube) = univ := by
      refine eq_univ_of_forall fun z => ⟨(pairTupleEquiv 0).symm z, ?_, by simp⟩
      exact fun i => i.elim0
    unfold HolomorphicVectorOnTuples BanachValued.IsHolomorphicOnOpen
    rw [hU]
    refine ⟨isOpen_univ, Or.inr ⟨Nat.zero_mul 2, 0, ?_⟩⟩
    exact Set.eq_singleton_iff_unique_mem.mpr ⟨mem_univ _, fun z _ => Subsingleton.elim z 0⟩
  · refine holomorphicVectorOnTuples_of_lightConeSeries hHol hp _ fun v hv => ?_
    obtain ⟨ρ, hρ, hlt⟩ := exists_radius_lt hp v hv
    refine ⟨ρ, wordCoeff σ ψ p A v, hρ, hlt, ?_, ?_⟩
    · have hs := (hasSum_tubeWord σ hW R ψ p A v (fun _ => ofLightConeCoords ρ ρ) hv fun i =>
        ⟨by rw [lightConePlus_ofLightConeCoords, norm_ofReal_pos hρ]; exact (hlt i).1,
          by rw [lightConeMinus_ofLightConeCoords, norm_ofReal_pos hρ]; exact (hlt i).2⟩).1
      refine hs.congr fun m => ?_
      unfold incrementMonomial
      rw [norm_smul, norm_prod, mul_comm]
      congr 1
      simp only [lightConePlus_ofLightConeCoords, lightConeMinus_ofLightConeCoords, norm_pow,
        norm_ofReal_pos hρ, ← pow_add]
      rw [Finset.prod_pow_eq_pow_sum]
    · intro d hd
      exact (hasSum_tubeWord σ hW R ψ p A v d hv fun i =>
        ⟨(hd i).1.trans_lt (hlt i).1, (hd i).2.trans_lt (hlt i).2⟩).2
def energyConeSet : BorelSubsets (Fin 4 → ℝ) :=
  ⟨{x | |x 1| ≤ x 0}, measurableSet_le (measurable_pi_apply 1).abs (measurable_pi_apply 0)⟩
theorem isSupportedOn_energyConeSet (hCone : σ.ConeCondition) :
    IsSupportedOn σ.jointMeasure energyConeSet := by
  have hdot : ∀ p : EMPoints, dot3 (basisVec 0) (SpectralPoint.momentumOf p) = p.1 1 := fun p => by
    simp [dot3, basisVec, SpectralPoint.momentumOf, Fin.sum_univ_three]
  have e : (⟨(restrictToUniv energyConeSet).1ᶜ, (restrictToUniv energyConeSet).2.compl⟩ :
      BorelSubsets EMPoints) = belowAbsMomentum (basisVec 0) := by
    refine Subtype.ext ?_
    ext p
    show ¬ |p.1 1| ≤ p.1 0 ↔
      SpectralPoint.energyOf p < |dot3 (basisVec 0) (SpectralPoint.momentumOf p)|
    rw [hdot, not_le]
    rfl
  unfold IsSupportedOn SpectralMeasure.IsCarriedBy
  rw [e]
  exact hCone
theorem spatialEmbed_first (s : ℝ) :
    spatialEmbed ![s, 0, 0] = s • PeriodicLattice.coordVec 0 := by
  funext i
  fin_cases i <;> simp [spatialEmbed, Fin.snoc, PeriodicLattice.coordVec]; rfl
theorem spatialEmbed_spatialProj_embedFour (y : RealPlane) :
    spatialEmbed (spatialProj (RealPlane.embedFour y)) =
      y 1 • PeriodicLattice.coordVec 0 := by
  funext i
  fin_cases i <;>
    simp [spatialEmbed, Fin.snoc, spatialProj, RealPlane.embedFour,
      PeriodicLattice.coordVec]
theorem embedFour_time (y : RealPlane) : RealPlane.embedFour y 3 = y 0 := by
  simp [RealPlane.embedFour, PeriodicLattice.coordVec]
theorem wedgeIntegralOp_embedPlane (hW : WedgeInLightConeCoords)
    (hImg : σ.MeasureFacts) (hTr : σ.LaplaceFourierRep)
    (hC4 : SupportLaws σ.jointMeasure energyConeSet) (y : RealPlane)
    (hy : 0 ≤ y 0) :
    σ.wedgeIntegralOp (embedPlane y) =
      ResolvedOps.expComplex σ.recon.ham ((y 0 : ℝ) : ℂ) *
        spatialTranslOp σ.jointMeasure (y 1 • PeriodicLattice.coordVec 0) := by
  set V : R4 := y 1 • PeriodicLattice.coordVec 0 with hV
  have hmem : embedPlane y ∈ closedForwardTube := by
    simp [closedForwardTube, lightConePlus, lightConeMinus, embedPlane, hy]
  have hcm : Measurable (wedgeCut (planeExpKernel (embedPlane y))) :=
    measurable_wedgeCut (continuous_planeExpKernel _).measurable
  have hcb : ∀ p, ‖wedgeCut (planeExpKernel (embedPlane y)) p‖ ≤ 1 :=
    norm_wedgeCut_le zero_le_one (hW.2.2 _ hmem)
  have h₁ := hImg.planeIntegralOp_eq _ hcm ⟨1, hcb⟩
  have h₂ := (hTr (y 0) hy ![y 1, 0, 0]).1
  rw [spatialEmbed_first] at h₂
  have e₁ : ResolvedOps.expComplex σ.recon.ham ((y 0 : ℝ) : ℂ) *
      spatialTranslOp σ.jointMeasure V = σ.heatSemigroup (y 0) * σ.translOp V :=
    rfl
  rw [e₁, h₂, wedgeIntegralOp_eq_overWedge]
  show σ.planeIntegralOp _ = _
  rw [h₁]
  unfold SpectralMeasure.integralOpOn
  have hm₂ : Measurable (laplaceFourierKernel (y 0) V) := by
    unfold laplaceFourierKernel
    refine Complex.measurable_exp.comp (Measurable.add ?_ ?_)
    · exact measurable_const.mul (Complex.measurable_ofReal.comp
        (SpectralPoint.measurable_energyOf.comp measurable_subtype_coe))
    · refine measurable_const.mul (Complex.measurable_ofReal.comp ?_)
      unfold dotR4 dot3
      exact Finset.measurable_fun_sum _ fun j _ => measurable_const.mul
        ((SpectralPoint.measurable_momentumOf_apply j).comp measurable_subtype_coe)
  have hb₂ : ∀ p, ‖zeroExtend SpectralPoint.nonnegEnergy.1 (laplaceFourierKernel (y 0) V) p‖ ≤ 1 := by
    intro p
    unfold zeroExtend
    split_ifs with hp
    · unfold laplaceFourierKernel
      rw [Complex.norm_exp]
      have hE : 0 ≤ SpectralPoint.energyOf p := hp
      simp only [Complex.add_re, Complex.neg_re, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im]
      refine Real.exp_le_one_iff.mpr ?_
      nlinarith [mul_nonneg hy hE]
    · simp
  refine hC4.congr (fun x => (wedgeCut (planeExpKernel (embedPlane y)) ∘ energyMomentumPlane)
      ⟨x, mem_univ x⟩) (fun x => zeroExtend SpectralPoint.nonnegEnergy.1 (laplaceFourierKernel (y 0) V)
      ⟨x, mem_univ x⟩) ⟨(hcm.comp measurable_energyMomentumPlane).comp
        measurable_id.subtype_mk, 1, fun _ => hcb _⟩
      ⟨(measurable_zeroExtend SpectralPoint.nonnegEnergy.2 hm₂).comp measurable_id.subtype_mk, 1,
        fun _ => hb₂ _⟩ ?_
  intro x hx
  have hx' : |x 1| ≤ x 0 := hx
  have hE : 0 ≤ x 0 := (abs_nonneg _).trans hx'
  have hw : energyMomentumPlane ⟨x, mem_univ x⟩ ∈ wedge.1 := by
    show |(energyMomentumPlane ⟨x, mem_univ x⟩).1 1| ≤ (energyMomentumPlane ⟨x, mem_univ x⟩).1 0
    simpa [energyMomentumPlane, SpectralPoint.energyOf, SpectralPoint.momentumOf] using hx'
  simp only [Function.comp_apply]
  rw [wedgeCut_of_mem _ hw]
  have hn : (⟨x, mem_univ x⟩ : EMPoints) ∈ SpectralPoint.nonnegEnergy.1 := hE
  unfold zeroExtend
  rw [dif_pos hn]
  unfold planeExpKernel laplaceFourierKernel
  congr 1
  simp [energyMomentumPlane, embedPlane, dotR4, dot3, hV, SpectralPoint.energyOf,
    SpectralPoint.momentumOf, PeriodicLattice.coordVec, Fin.sum_univ_three]
  ring
theorem realPoints (hW : WedgeInLightConeCoords)
    (hImg : σ.MeasureFacts) (hTr : σ.LaplaceFourierRep)
    (hCl : σ.TranslateClasses)
    (hC4 : SupportLaws σ.jointMeasure energyConeSet) : RealPoints σ := by
  intro y hy
  have hop := wedgeIntegralOp_embedPlane σ hW hImg hTr hC4 y hy
  refine ⟨hop, fun F => ?_⟩
  obtain ⟨h, e⟩ := hCl (RealPlane.embedFour y) (by rw [embedFour_time]; exact hy) F
  refine ⟨h, ?_⟩
  have hcl : readClass σ.recon.cls ((planeShift y).actFree F.1) =
      σ.recon.cls ⟨_, h⟩ := dif_pos h
  rw [hcl, ← e, hop, embedFour_time, spatialEmbed_spatialProj_embedFour]
  rfl
end Conclusion
theorem holds (hForms : TubeOperatorForms.Holds)
    (hLink : ReconstructionMeasureOperatorFacts)
    (hCalc : WholeSpaceCalculus.BoundedCalculusTheorem)
    (hHol : BanachValued.AffineCoordinates.HolomorphicCompositionProperties) : Holds := by
  intro c S σ hCone
  have h0 := hForms c S σ 0 zero_mem_closedForwardTube
  have hW := h0.2.1
  have hcar := h0.2.2.1.mp hCone
  obtain ⟨hImg, -, hTr, hVac, hCl, -⟩ := hLink c S σ
  have hE := hCalc σ.space 2 σ.planeMeasure
  have R := hE.1
  have hC := (hE.2.1 planeWedgeSet (isSupportedOn_planeWedgeSet hcar)).1
  have hP := hCalc σ.space 4 σ.jointMeasure
  have hC4 := (hP.2.1 energyConeSet (isSupportedOn_energyConeSet σ hCone)).1
  have hi := contractionSemigroup σ hW R hC hImg hVac
  have hii := strongContinuity σ hW R
  have hT : ∀ v ∈ closedForwardTube, ‖σ.wedgeIntegralOp v‖ ≤ 1 := fun v hv =>
    (hi.2 v hv v hv).2.2.1
  refine ⟨⟨fun v hv p hp => hW.2.2 v hv p hp,
    fun v hv => ((hForms c S σ v hv).2.2.2.1 hCone).1.1, hcar⟩, hi, hii, ?_,
    realPoints σ hW hImg hTr hCl hC4, ?_⟩
  · refine ⟨fun v hv => ⟨fun j k => ⟨continuous_expansionKernel j k v,
      ⟨_, fun p hp => norm_expansionKernel_le hW hv j k hp⟩,
      norm_expansionOp_le σ hW R hv j k⟩, fun w hx hy => ⟨add_mem_forwardTube hx hy,
      hasSum_expansionOp σ hW R hv hx hy⟩⟩, holomorphic_wedgeIntegralOp σ hHol hW R⟩
  · intro p A ψ
    exact ⟨fun v hv => norm_tubeWord_le σ hT ψ p A v hv, continuousOn_tubeWord σ hT hii ψ p A,
      holomorphic_tubeWord σ hHol hW R ψ p A⟩
end YangMills.Construction.EuclideanFunctionals.TubeSemigroup
