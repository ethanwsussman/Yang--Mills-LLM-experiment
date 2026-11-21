import YangMills.Construction.LawByMomentsOfTheFlow.CumulantOfTheBottomCurvature
import YangMills.Construction.LawByMomentsOfTheFlow.CyclicFormulaOfGaussianSquares
import YangMills.Construction.ResponseInTheExpansion.LocalRestrictionOfATupleProof
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace YangMills.Construction.MomentLaw
open TorusFields WeightedResponses
section Coefficients
variable {L : ℕ} [NeZero L]
private def baseCoeff : (s n : ℕ) → (Fin 3 × TorusPlaquette (fineSide L s n) → ℝ) → ChainNoise L s n → ℝ
  | 0, _, c => c
  | s + 1, n, c => Sum.elim (baseCoeff s (n * L) c) (fun _ => 0)
private theorem noisePairing_baseCoeff : ∀ (s n : ℕ) [NeZero n] (c : Fin 3 × TorusPlaquette (fineSide L s n) → ℝ) (X : LevelChain L s n),
    noisePairing s n (baseCoeff s n c) X =
      ∑ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite (fineSide L s n))), ∑ e : Fin 3, c (e, p) * curl (chainBottom s n X e) p := by
  intro s
  induction s with
  | zero => intro n _ c X; rfl
  | succ s ih =>
    intro n _ c X
    have := ih (n * L) c (chainLower X)
    simp only [noisePairing, baseCoeff, Sum.elim_inl, Sum.elim_inr, zero_mul, Finset.sum_const_zero, add_zero]
    exact this
private theorem noiseVariance_baseCoeff (a : ℝ) : ∀ (s n : ℕ) [NeZero n] (c : Fin 3 × TorusPlaquette (fineSide L s n) → ℝ),
    noiseVariance a s n (baseCoeff s n c) = ∑ e : Fin 3, curvatureVariance (fineSide L s n) fun p => c (e, p) := by
  intro s
  induction s with
  | zero => intro n _ c; rfl
  | succ s ih =>
    intro n _ c
    have := ih (n * L) c
    simp only [noiseVariance, baseCoeff, Sum.elim_inl, Sum.elim_inr]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, Finset.sum_const_zero, mul_zero, add_zero]
    exact this
private theorem measurable_chainBottom_apply : ∀ (s n : ℕ) (e : Fin 3) (b : TorusBond (fineSide L s n)),
    Measurable fun X : LevelChain L s n => chainBottom s n X e b := by
  intro s
  induction s with
  | zero =>
    intro n e b
    exact (measurable_pi_apply b).comp (measurable_pi_apply e)
  | succ s ih =>
    intro n e b
    have hb : Measurable fun X : LevelChain L (s + 1) n => (chainLower X : LevelChain L s (n * L)) :=
      measurable_pi_lambda _ fun e' => measurable_pi_lambda _ fun c =>
        (measurable_pi_apply (Sum.inl c)).comp (measurable_pi_apply e')
    exact (ih (n * L) e b).comp hb
end Coefficients
private theorem sum_plaquettesIn {m : ℕ} [NeZero m] (f : TorusPlaquette m → ℝ) :
    ∑ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite m)), f p = ∑ q : OrientedPlaquette m, f q.1 := by apply _root_.YangMills.SharedProofs.p68842 <;> assumption
section Kernel
variable {m : ℕ} [NeZero m]
open Classical in
private theorem torusCurvatureProjection_eq_inner (p p' : OrientedPlaquette m) : torusCurvatureProjection p p' =
    inner ℝ ((curvatureSubspace m).starProjection (EuclideanSpace.single p (1 : ℝ)))
      ((curvatureSubspace m).starProjection (EuclideanSpace.single p' (1 : ℝ))) := by
  rw [Submodule.inner_starProjection_left_eq_right]
  have h := DFunLike.congr_fun (curvatureSubspace m).isIdempotentElem_starProjection (EuclideanSpace.single p' (1 : ℝ))
  have h' : (curvatureSubspace m).starProjection ((curvatureSubspace m).starProjection (EuclideanSpace.single p' (1 : ℝ))) =
      (curvatureSubspace m).starProjection (EuclideanSpace.single p' (1 : ℝ)) := h
  rw [h']
  rfl
variable (m) in
private abbrev orientedCount : ℕ := Fintype.card (OrientedPlaquette m)
variable (m) in
private def orientedEquiv : OrientedPlaquette m ≃ Fin (orientedCount m) := Fintype.equivFin _
variable (m) in
private def projectionMatrix : Matrix (Fin (orientedCount m)) (Fin (orientedCount m)) ℝ := fun a b =>
  torusCurvatureProjection ((orientedEquiv m).symm a) ((orientedEquiv m).symm b)
open Classical in
private theorem projectionMatrix_posSemidef : (projectionMatrix m).PosSemidef := by
  have h := Matrix.posSemidef_gram ℝ (fun a : Fin (orientedCount m) =>
    (curvatureSubspace m).starProjection (EuclideanSpace.single ((orientedEquiv m).symm a) (1 : ℝ)))
  have e : projectionMatrix m = Matrix.gram ℝ (fun a : Fin (orientedCount m) =>
      (curvatureSubspace m).starProjection (EuclideanSpace.single ((orientedEquiv m).symm a) (1 : ℝ))) := by
    ext a b
    rw [Matrix.gram_apply]
    exact torusCurvatureProjection_eq_inner _ _
  rw [e]
  exact h
private theorem curvatureVariance_eq_dotProduct (x : Fin (orientedCount m) → ℝ) (c : TorusPlaquette m → ℝ)
    (hc : ∀ q : OrientedPlaquette m, c q.1 = x (orientedEquiv m q)) :
    curvatureVariance m c = x ⬝ᵥ (projectionMatrix m).mulVec x := by
  simp only [curvatureVariance, dotProduct, Matrix.mulVec, Finset.mul_sum]
  rw [← (orientedEquiv m).sum_comp]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [← (orientedEquiv m).sum_comp]
  refine Finset.sum_congr rfl fun q' _ => ?_
  simp only [projectionMatrix, Equiv.symm_apply_apply, hc]
  ring
end Kernel
section Law
variable {L : ℕ} [NeZero L] {K n : ℕ} [NeZero n]
private def baseCurvatureVec (X : LevelChain L K n) : Fin 3 → EuclideanSpace ℝ (Fin (orientedCount (fineSide L K n))) :=
  fun e => WithLp.toLp 2 fun a => curl (chainBottom K n X e) ((orientedEquiv (fineSide L K n)).symm a).1
private theorem measurable_baseCurvatureVec : Measurable (baseCurvatureVec (L := L) (K := K) (n := n)) := by
  refine measurable_pi_lambda _ fun e => ?_
  refine (MeasurableEquiv.toLp 2 _).measurable.comp (measurable_pi_lambda _ fun a => ?_)
  simp only [curl]
  exact (((measurable_chainBottom_apply K n e _).add (measurable_chainBottom_apply K n e _)).sub
    (measurable_chainBottom_apply K n e _)).sub (measurable_chainBottom_apply K n e _)
private theorem map_baseCurvatureVec (a : ℝ) (μ : Measure (LevelChain L K n)) (hμ : IsProbabilityMeasure μ)
    (h : ∀ co : ChainNoise L K n → ℝ, μ.map (noisePairing K n co) = gaussianReal 0 (noiseVariance a K n co).toNNReal) :
    μ.map baseCurvatureVec = Measure.pi fun _ : Fin 3 => multivariateGaussian 0 (projectionMatrix (fineSide L K n)) := by
  classical
  have hY := measurable_baseCurvatureVec (L := L) (K := K) (n := n)
  refine charFunDual_eq_pi_iff.mp fun Lf => ?_
  set E := EuclideanSpace ℝ (Fin (orientedCount (fineSide L K n))) with hE
  let ℓ : Fin 3 → StrongDual ℝ E := fun e => Lf.comp (.single ℝ (fun _ : Fin 3 => E) e)
  let x : Fin 3 → E := fun e => (InnerProductSpace.toDual ℝ E).symm (ℓ e)
  have hx : ∀ e y, ℓ e y = inner ℝ (x e) y := fun e y => by
    simp [x, InnerProductSpace.toDual_symm_apply]
  have hL : ∀ y : Fin 3 → E, Lf y = ∑ e, inner ℝ (x e) (y e) := fun y => by
    have hy : y = ∑ e, Pi.single e (y e) := (Finset.univ_sum_single y).symm
    conv_lhs => rw [hy]
    rw [map_sum]
    exact Finset.sum_congr rfl fun e _ => hx e (y e)
  let c : Fin 3 × TorusPlaquette (fineSide L K n) → ℝ := fun q =>
    if hq : q.2.2.1 < q.2.2.2 then x q.1 (orientedEquiv _ ⟨q.2, hq⟩) else 0
  have hcq : ∀ (e : Fin 3) (q : OrientedPlaquette (fineSide L K n)), c (e, q.1) = x e (orientedEquiv _ q) := fun e q => by
    simp only [c, q.2, dif_pos]
  have hcomp : (⇑Lf ∘ baseCurvatureVec) = noisePairing K n (baseCoeff K n c) := by
    funext X
    rw [noisePairing_baseCoeff, sum_plaquettesIn, Function.comp_apply, hL, Finset.sum_comm]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [PiLp.inner_apply, ← (orientedEquiv _).sum_comp]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [hcq]
    simp [baseCurvatureVec, mul_comm]
  have hvar : noiseVariance a K n (baseCoeff K n c) = ∑ e, (x e).ofLp ⬝ᵥ (projectionMatrix _).mulVec (x e).ofLp := by
    rw [noiseVariance_baseCoeff]
    exact Finset.sum_congr rfl fun e _ => curvatureVariance_eq_dotProduct _ _ fun q => hcq e q
  have hnn : 0 ≤ noiseVariance a K n (baseCoeff K n c) := by
    rw [hvar]
    exact Finset.sum_nonneg fun e _ => projectionMatrix_posSemidef.dotProduct_mulVec_nonneg _
  rw [charFunDual_eq_charFun_map_one, Measure.map_map Lf.continuous.measurable hY, hcomp, h, charFun_gaussianReal]
  have hone : ∀ e, charFunDual (multivariateGaussian 0 (projectionMatrix (fineSide L K n))) (Lf.comp (.single ℝ (fun _ : Fin 3 => E) e)) =
      Complex.exp (-(((x e).ofLp ⬝ᵥ (projectionMatrix _).mulVec (x e).ofLp : ℝ) : ℂ) / 2) := fun e => by
    rw [← charFun_toDual_symm_eq_charFunDual, charFun_multivariateGaussian projectionMatrix_posSemidef]
    change Complex.exp (((inner ℝ (x e) 0 : ℝ) : ℂ) * Complex.I -
      (((x e).ofLp ⬝ᵥ (projectionMatrix _).mulVec (x e).ofLp : ℝ) : ℂ) / 2) = _
    rw [inner_zero_right]
    congr 1
    simp only [Complex.ofReal_zero, zero_mul, zero_sub]
    ring
  have hprod : ∏ e, charFunDual (multivariateGaussian 0 (projectionMatrix (fineSide L K n)))
      (Lf.comp (.single ℝ (fun _ : Fin 3 => E) e)) =
      ∏ e, Complex.exp (-(((x e).ofLp ⬝ᵥ (projectionMatrix _).mulVec (x e).ofLp : ℝ) : ℂ) / 2) :=
    Finset.prod_congr rfl fun e _ => hone e
  refine Eq.trans ?_ hprod.symm
  rw [← Complex.exp_sum]
  congr 1
  rw [Real.coe_toNNReal _ hnn, hvar, ← Finset.sum_div, Finset.sum_neg_distrib]
  push_cast
  ring
end Law
private theorem list_ofFn_prod_apply {ι : Type} [Fintype ι] [DecidableEq ι] : ∀ (n : ℕ) (A : Fin n → Matrix ι ι ℝ) (i j : ι),
    (List.ofFn A).prod i j = ∑ a : Fin n → ι, (if (Fin.cons i a : Fin (n + 1) → ι) (Fin.last n) = j then 1 else 0) *
      ∏ c : Fin n, A c ((Fin.cons i a : Fin (n + 1) → ι) c.castSucc) (a c) := by
  intro n
  induction n with
  | zero =>
    intro A i j
    simp [Matrix.one_apply]
  | succ n ih =>
    intro A i j
    rw [List.ofFn_succ, List.prod_cons, Matrix.mul_apply]
    rw [← (Fin.consEquiv (fun _ : Fin (n + 1) => ι)).sum_comp, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [ih (fun c => A c.succ) l j, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a' _ => ?_
    have hce : (Fin.consEquiv (fun _ : Fin (n + 1) => ι)) (l, a') = Fin.cons l a' := rfl
    simp only [hce, Fin.prod_univ_succ, Fin.castSucc_zero, Fin.cons_zero, Fin.cons_succ]
    have hl : (Fin.cons i (Fin.cons l a' : Fin (n + 1) → ι) : Fin (n + 2) → ι) (Fin.last (n + 1)) =
        (Fin.cons l a' : Fin (n + 1) → ι) (Fin.last n) := by
      rw [← Fin.succ_last, Fin.cons_succ]
    rw [hl]
    have hc : ∀ c : Fin n, (Fin.cons i (Fin.cons l a' : Fin (n + 1) → ι) : Fin (n + 2) → ι) c.succ.castSucc =
        (Fin.cons l a' : Fin (n + 1) → ι) c.castSucc := by
      intro c
      rw [← Fin.succ_castSucc, Fin.cons_succ]
    simp only [hc]
    ring
private theorem trace_list_ofFn_prod {ι : Type} [Fintype ι] [DecidableEq ι] (k : ℕ) [NeZero k] (A : Fin k → Matrix ι ι ℝ) :
    Matrix.trace (List.ofFn A).prod = ∑ b : Fin k → ι, ∏ c : Fin k, A c (b c) (b (c + 1)) := by
  cases k with
  | zero => exact absurd rfl (NeZero.ne 0)
  | succ m =>
    simp only [Matrix.trace, Matrix.diag]
    simp only [list_ofFn_prod_apply]
    rw [Finset.sum_comm]
    have hlast : ∀ (i : ι) (a : Fin (m + 1) → ι), (Fin.cons i a : Fin (m + 2) → ι) (Fin.last (m + 1)) = a (Fin.last m) := by
      intro i a
      rw [← Fin.succ_last, Fin.cons_succ]
    simp only [hlast, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    let e : (Fin (m + 1) → ι) ≃ (Fin (m + 1) → ι) := (Equiv.addRight (1 : Fin (m + 1))).symm.arrowCongr (Equiv.refl ι)
    have he : ∀ (b : Fin (m + 1) → ι) (c : Fin (m + 1)), e b c = b (c + 1) := fun b c => by
      simp [e, Equiv.arrowCongr]
    rw [← e.sum_comp]
    refine Finset.sum_congr rfl fun b _ => ?_
    refine Finset.prod_congr rfl fun c _ => ?_
    rw [he]
    congr 1
    exact show (Fin.cons (e b (Fin.last m)) (e b) : Fin (m + 2) → ι) c.castSucc = b c from by
      induction c using Fin.cases with
      | zero =>
        simp only [Fin.castSucc_zero, Fin.cons_zero]
        rw [he]; simp
      | succ c' =>
        rw [← Fin.succ_castSucc, Fin.cons_succ, he, Fin.coeSucc_eq_succ]
abbrev _root_.YangMills.SharedProofs.p55566 := @trace_list_ofFn_prod
section Main
variable {L : ℕ} [NeZero L] {K n : ℕ} [NeZero n]
private def weightDiagonal {m : ℕ} [NeZero m] (h : PlaquetteWeight m) : Matrix (Fin (orientedCount m)) (Fin (orientedCount m)) ℝ :=
  Matrix.diagonal fun a => h ((orientedEquiv m).symm a).1
private theorem baseObservable_eq_quadratic (h : PlaquetteWeight (fineSide L K n)) (X : LevelChain L K n) :
    baseObservable h X = ∑ e : Fin 3, (1 / 2) *
      ((fun a => baseCurvatureVec X e a) ⬝ᵥ (weightDiagonal h).mulVec fun a => baseCurvatureVec X e a) := by
  have hs : ∀ q : OrientedPlaquette (fineSide L K n), curlNorm (chainBottom K n X) q.1 ^ 2 =
      ∑ e : Fin 3, curl (chainBottom K n X e) q.1 ^ 2 := fun q =>
    Real.sq_sqrt (Finset.sum_nonneg fun e _ => sq_nonneg _)
  simp only [baseObservable, sum_plaquettesIn, hs, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun e _ => ?_
  simp only [dotProduct, weightDiagonal, Matrix.mulVec_diagonal, Finset.mul_sum]
  rw [← (orientedEquiv _).sum_comp]
  refine Finset.sum_congr rfl fun q _ => ?_
  simp only [baseCurvatureVec, Equiv.symm_apply_apply]
  ring
private theorem jointCumulant_comp {k : ℕ} {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω'] (μ : Measure Ω) {Y : Ω → Ω'}
    (hY : Measurable Y) (F : Fin k → Ω' → ℝ) (hF : ∀ i, Measurable (F i)) :
    jointCumulant μ (fun i ω => F i (Y ω)) = jointCumulant (μ.map Y) F := by
  simp only [jointCumulant]
  refine Finset.sum_congr rfl fun π _ => ?_
  congr 1
  refine Finset.prod_congr rfl fun J _ => ?_
  rw [integral_map hY.aemeasurable (Finset.measurable_prod _ fun i _ => hF i).aestronglyMeasurable]
private theorem trace_weight_projection_prod {m k : ℕ} [NeZero m] [NeZero k] (h : Fin k → PlaquetteWeight m) (σ : Equiv.Perm (Fin k)) :
    Matrix.trace (List.ofFn fun c : Fin k => weightDiagonal (h (σ c)) * projectionMatrix m).prod =
      ∑ p : Fin k → OrientedPlaquette m, (∏ i, h i (p i).1) * ∏ c : Fin k, torusCurvatureProjection (p (σ c)) (p (σ (c + 1))) := by
  rw [trace_list_ofFn_prod, ← (σ.symm.arrowCongr (orientedEquiv m)).sum_comp]
  refine Finset.sum_congr rfl fun p _ => ?_
  have hc : ∀ c : Fin k, (weightDiagonal (h (σ c)) * projectionMatrix m) ((σ.symm.arrowCongr (orientedEquiv m)) p c)
      ((σ.symm.arrowCongr (orientedEquiv m)) p (c + 1)) = h (σ c) (p (σ c)).1 * torusCurvatureProjection (p (σ c)) (p (σ (c + 1))) := by
    intro c
    simp [Matrix.diagonal_mul, weightDiagonal, projectionMatrix, Equiv.arrowCongr]
  simp only [hc, Finset.prod_mul_distrib]
  congr 1
  exact Equiv.prod_comp σ fun i => h i (p i).1
end Main
theorem baseCurvatureCumulant_of_gaussianQuadratic (hC : gaussianQuadraticCumulantStatement) :
    baseCurvatureCumulantStatement := by
  intro L _ a K n _ k _ hk h μ hμ hn
  let Qs : Fin k → Matrix (Fin (orientedCount (fineSide L K n))) (Fin (orientedCount (fineSide L K n))) ℝ :=
    fun i => weightDiagonal (h i)
  have hs : ∀ i, (Qs i).IsSymm := fun i => Matrix.isSymm_diagonal _
  have hcyc := (hC (orientedCount (fineSide L K n)) (projectionMatrix (fineSide L K n)) projectionMatrix_posSemidef k hk Qs hs).2
  let F : Fin k → (Fin 3 → EuclideanSpace ℝ (Fin (orientedCount (fineSide L K n)))) → ℝ := fun i X =>
    ∑ e : Fin 3, (1 / 2) * ((fun a => X e a) ⬝ᵥ (Qs i).mulVec fun a => X e a)
  have hcoord : ∀ (e : Fin 3) (a : Fin (orientedCount (fineSide L K n))),
      Measurable fun X : Fin 3 → EuclideanSpace ℝ (Fin (orientedCount (fineSide L K n))) => X e a := fun e a =>
    ((EuclideanSpace.proj (𝕜 := ℝ) a).continuous.measurable).comp (measurable_pi_apply e)
  have hF : ∀ i, Measurable (F i) := fun i => by
    refine Finset.measurable_sum _ fun e _ => measurable_const.mul ?_
    simp only [dotProduct, Matrix.mulVec]
    refine Finset.measurable_sum _ fun a _ => (hcoord e a).mul ?_
    exact Finset.measurable_sum _ fun b _ => measurable_const.mul (hcoord e b)
  have e1 : jointCumulant μ (fun i X => baseObservable (h i) X) = jointCumulant (μ.map baseCurvatureVec) F := by
    rw [← jointCumulant_comp μ measurable_baseCurvatureVec F hF]
    congr 1
    funext i X
    exact baseObservable_eq_quadratic (h i) X
  rw [e1, map_baseCurvatureVec a μ hμ hn]
  refine hcyc.trans ?_
  rw [mul_assoc]
  congr 2
  exact Finset.sum_congr rfl fun σ _ => trace_weight_projection_prod h σ
end YangMills.Construction.MomentLaw
end
