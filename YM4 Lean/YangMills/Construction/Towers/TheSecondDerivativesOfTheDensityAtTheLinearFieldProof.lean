import YangMills.Construction.OneLoopLaw.CoefficientOfATemperedFunctional
import YangMills.Construction.PeriodicOperators.SumsOfExponentials
import YangMills.Construction.Towers.TheMassiveFunctionalAndTheFunctionOfTheMassiveJets
import YangMills.Construction.Towers.TheRowSumsOfTheSecondDerivativesOfTheDensityVanish
import YangMills.Construction.Towers.TheSecondDerivativesOfTheDensityAreSymmetric
import YangMills.Construction.Towers.TheSecondDerivativesOfTheDensityAtTheLinearField
import YangMills.Construction.Towers.TheSecondDerivativesOfTheDensityDecay
import YangMills.Construction.Towers.TheSecondDerivativesOfTheDensityUnderTranslations
import YangMills.Construction.Towers.TheSumOverTheSitesOfTheSecondDerivativesOfTheDensity
import Mathlib
set_option autoImplicit false
open Filter
open scoped Topology
noncomputable section
namespace YangMills.Construction.Tower.AbelianFieldDensity
namespace LinearAngleSum
section Abstract
variable {G : Type}
theorem hasSum_zero_of_row_sums_zero {P : G → G → ℂ} {w : G → ℂ}
    (hs : Summable fun p : G × G => P p.1 p.2 * w p.1)
    (hrow : ∀ u, HasSum (P u) 0) :
    HasSum (fun p : G × G => P p.1 p.2 * w p.1) 0 := by
  have h := hs.hasSum.prod_fiberwise (fun u => (hrow u).mul_right (w u))
  have h' : HasSum (fun _ : G => (0 : ℂ)) (∑' p : G × G, P p.1 p.2 * w p.1) := by
    simpa using h
  have h0 : (∑' p : G × G, P p.1 p.2 * w p.1) = 0 := h'.unique hasSum_zero
  rw [← h0]
  exact hs.hasSum
theorem sq_le_one_add_sq_mul_one_add_sq {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a ^ 2 ≤ (1 + a) ^ 2 * (1 + b) ^ 2 := by
  have h1 : a ^ 2 ≤ (1 + a) ^ 2 := pow_le_pow_left₀ ha (by linarith) 2
  have h2 : (1 : ℝ) ≤ (1 + b) ^ 2 := one_le_pow₀ (by linarith)
  calc a ^ 2 ≤ (1 + a) ^ 2 * 1 := by simpa using h1
    _ ≤ (1 + a) ^ 2 * (1 + b) ^ 2 := mul_le_mul_of_nonneg_left h2 (by positivity)
theorem add_sq_le_four_mul_weight {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (b + a) ^ 2 ≤ 4 * ((1 + a) ^ 2 * (1 + b) ^ 2) := by
  have h1 : b + a ≤ 2 * ((1 + a) * (1 + b)) := by nlinarith [mul_nonneg ha hb]
  calc (b + a) ^ 2 ≤ (2 * ((1 + a) * (1 + b))) ^ 2 := pow_le_pow_left₀ (by linarith) h1 2
    _ = 4 * ((1 + a) ^ 2 * (1 + b) ^ 2) := by ring
end Abstract
section Group
variable {G : Type} [AddCommGroup G]
def diagonalShear (G : Type) [AddCommGroup G] : G × G ≃ G × G where
  toFun p := (p.2, p.2 + p.1)
  invFun p := (p.2 - p.1, p.1)
  left_inv p := by simp
  right_inv p := by simp
theorem hasSum_mul_sub_sq {P : G → G → ℂ} {X : G → ℂ} {π : G → ℂ} {S : ℂ}
    (hadd : ∀ u n, X (u + n) = X u + X n)
    (sF : Summable fun p : G × G => P p.1 p.2 * (X p.2 - X p.1) ^ 2)
    (hdiag : ∀ n, HasSum (fun u => P u (u + n)) (π n))
    (hπ : HasSum (fun n => π n * X n ^ 2) S) :
    HasSum (fun p : G × G => P p.1 p.2 * (X p.2 - X p.1) ^ 2) S := by
  set f : G × G → ℂ := fun p => P p.1 p.2 * (X p.2 - X p.1) ^ 2 with hf
  have sFe : Summable (f ∘ diagonalShear G) := (diagonalShear G).summable_iff.mpr sF
  have hfib : ∀ n, HasSum (fun u => (f ∘ diagonalShear G) (n, u)) (π n * X n ^ 2) := fun n => by
    have h := (hdiag n).mul_right (X n ^ 2)
    have he : (fun u => (f ∘ diagonalShear G) (n, u)) = fun u => P u (u + n) * X n ^ 2 := by
      funext u
      have : (f ∘ diagonalShear G) (n, u) = P u (u + n) * (X (u + n) - X u) ^ 2 := rfl
      rw [this, hadd]
      ring
    rw [he]
    exact h
  have hS := sFe.hasSum.prod_fiberwise hfib
  have hval : (∑' p, (f ∘ diagonalShear G) p) = S := hS.unique hπ
  refine ((diagonalShear G).hasSum_iff).mp ?_
  rw [← hval]
  exact sFe.hasSum
section Parts
omit [AddCommGroup G]
variable {P : G → G → ℂ} {X : G → ℂ}
theorem summable_mul_sq_left (hs : Summable fun p : G × G => ‖P p.1 p.2‖ * ((1 + ‖X p.1‖) ^ 2 * (1 + ‖X p.2‖) ^ 2)) :
    Summable fun p : G × G => P p.1 p.2 * X p.1 ^ 2 := by
  refine Summable.of_norm_bounded hs fun p => ?_
  rw [norm_mul, norm_pow]
  exact mul_le_mul_of_nonneg_left (sq_le_one_add_sq_mul_one_add_sq (norm_nonneg _) (norm_nonneg _)) (norm_nonneg _)
theorem hasSum_mul_sq_right (hsym : ∀ u v, P u v = P v u)
    (T1 : HasSum (fun p : G × G => P p.1 p.2 * X p.1 ^ 2) 0) :
    HasSum (fun p : G × G => P p.1 p.2 * X p.2 ^ 2) 0 := by
  refine ((Equiv.prodComm G G).hasSum_iff).mp ?_
  have he : ((fun p : G × G => P p.1 p.2 * X p.2 ^ 2) ∘ (Equiv.prodComm G G)) =
      fun p : G × G => P p.1 p.2 * X p.1 ^ 2 := by
    funext p
    change P p.2 p.1 * X p.1 ^ 2 = _
    rw [hsym]
  rw [he]
  exact T1
theorem summable_mul_sub_sq (hs : Summable fun p : G × G => ‖P p.1 p.2‖ * ((1 + ‖X p.1‖) ^ 2 * (1 + ‖X p.2‖) ^ 2)) :
    Summable fun p : G × G => P p.1 p.2 * (X p.2 - X p.1) ^ 2 := by
  refine Summable.of_norm_bounded (hs.mul_left 4) fun p => ?_
  have hb1 : ‖(X p.2 - X p.1) ^ 2‖ ≤ (‖X p.2‖ + ‖X p.1‖) ^ 2 := by
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le _ _) 2
  have hb2 := add_sq_le_four_mul_weight (norm_nonneg (X p.1)) (norm_nonneg (X p.2))
  calc ‖P p.1 p.2 * (X p.2 - X p.1) ^ 2‖ = ‖P p.1 p.2‖ * ‖(X p.2 - X p.1) ^ 2‖ := norm_mul _ _
    _ ≤ ‖P p.1 p.2‖ * (4 * ((1 + ‖X p.1‖) ^ 2 * (1 + ‖X p.2‖) ^ 2)) :=
      mul_le_mul_of_nonneg_left (hb1.trans hb2) (norm_nonneg _)
    _ = 4 * (‖P p.1 p.2‖ * ((1 + ‖X p.1‖) ^ 2 * (1 + ‖X p.2‖) ^ 2)) := by ring
end Parts
theorem hasSum_mul_mul {P : G → G → ℂ} {X : G → ℂ} {π : G → ℂ} {β : ℂ}
    (hadd : ∀ u n, X (u + n) = X u + X n) (hsym : ∀ u v, P u v = P v u)
    (hs : Summable fun p : G × G => ‖P p.1 p.2‖ * ((1 + ‖X p.1‖) ^ 2 * (1 + ‖X p.2‖) ^ 2))
    (hrow : ∀ u, HasSum (P u) 0)
    (hdiag : ∀ n, HasSum (fun u => P u (u + n)) (π n))
    (hπ : HasSum (fun n => -(1 / 2 : ℂ) * (π n * X n ^ 2)) β) :
    HasSum (fun p : G × G => P p.1 p.2 * X p.1 * X p.2) β := by
  have T1 : HasSum (fun p : G × G => P p.1 p.2 * X p.1 ^ 2) 0 :=
    hasSum_zero_of_row_sums_zero (P := P) (w := fun u => X u ^ 2) (summable_mul_sq_left hs) hrow
  have T2 := hasSum_mul_sq_right hsym T1
  have hπ' : HasSum (fun n => π n * X n ^ 2) (-2 * β) := by
    have h := hπ.mul_left (-2 : ℂ)
    have he : (fun n => (-2 : ℂ) * (-(1 / 2 : ℂ) * (π n * X n ^ 2))) = fun n => π n * X n ^ 2 := by
      funext n
      ring
    rw [he] at h
    exact h
  have T3 := hasSum_mul_sub_sq hadd (summable_mul_sub_sq hs) hdiag hπ'
  have hfin := ((T1.add T2).sub T3).mul_left (1 / 2 : ℂ)
  have he : (fun p : G × G => (1 / 2 : ℂ) *
      (P p.1 p.2 * X p.1 ^ 2 + P p.1 p.2 * X p.2 ^ 2 - P p.1 p.2 * (X p.2 - X p.1) ^ 2)) =
      fun p : G × G => P p.1 p.2 * X p.1 * X p.2 := by
    funext p
    ring
  have hv : (1 / 2 : ℂ) * (0 + 0 - -2 * β) = β := by ring
  rw [he, hv] at hfin
  exact hfin
end Group
section Weights
open TorusMetric (euclidNormVec)
open PeriodicOperators (castVec)
def latticeNorm (n : Fin 4 → ℤ) : ℝ := euclidNormVec ((0 : InfiniteLattice.AmbientSpace) + castVec n)
theorem latticeNorm_nonneg (n : Fin 4 → ℤ) : 0 ≤ latticeNorm n := Real.sqrt_nonneg _
theorem latticeNorm_neg (n : Fin 4 → ℤ) : latticeNorm (-n) = latticeNorm n := by
  simp [latticeNorm, euclidNormVec, castVec]
theorem abs_apply_zero_le_latticeNorm (n : Fin 4 → ℤ) : |(n 0 : ℝ)| ≤ latticeNorm n := by
  refine Real.abs_le_sqrt ?_
  have h : ((0 : InfiniteLattice.AmbientSpace) + castVec n) 0 ^ 2 ≤
      ∑ μ, ((0 : InfiniteLattice.AmbientSpace) + castVec n) μ ^ 2 :=
    Finset.single_le_sum (f := fun μ => ((0 : InfiniteLattice.AmbientSpace) + castVec n) μ ^ 2)
      (fun _ _ => sq_nonneg _) (Finset.mem_univ (0 : Fin 4))
  simpa [castVec] using h
theorem one_add_sq_le_mul_exp {c t : ℝ} (hc : 0 < c) (ht : 0 ≤ t) :
    (1 + t) ^ 2 ≤ (1 + 4 / c) ^ 2 * Real.exp (c * t / 2) := by
  have h1 : 1 + t ≤ (1 + 4 / c) * (1 + c * t / 4) := by
    have : (1 + 4 / c) * (1 + c * t / 4) = 1 + c * t / 4 + 4 / c + t := by
      field_simp
      ring
    rw [this]
    have h2 : 0 ≤ c * t / 4 := by positivity
    have h3 : 0 ≤ 4 / c := by positivity
    linarith
  have h2 : 1 + c * t / 4 ≤ Real.exp (c * t / 4) := by
    have := Real.add_one_le_exp (c * t / 4)
    linarith
  have h3 : 1 + t ≤ (1 + 4 / c) * Real.exp (c * t / 4) :=
    h1.trans (mul_le_mul_of_nonneg_left h2 (by positivity))
  calc (1 + t) ^ 2 ≤ ((1 + 4 / c) * Real.exp (c * t / 4)) ^ 2 :=
        pow_le_pow_left₀ (by linarith) h3 2
    _ = (1 + 4 / c) ^ 2 * Real.exp (c * t / 2) := by
        rw [mul_pow, ← Real.exp_nat_mul]
        congr 2
        push_cast
        ring
def decayWeight (c : ℝ) (n : Fin 4 → ℤ) : ℝ := Real.exp (-c * latticeNorm n) * (1 + |(n 0 : ℝ)|) ^ 2
theorem decayWeight_nonneg (c : ℝ) (n : Fin 4 → ℤ) : 0 ≤ decayWeight c n := by
  unfold decayWeight
  positivity
theorem summable_decayWeight (hexp : PeriodicOperators.ExponentialSums.Bounds) {c : ℝ}
    (hc : 0 < c) : Summable (decayWeight c) := by
  have hbase := (((hexp (c / 2) (by positivity)).2.1) 0).1
  refine Summable.of_nonneg_of_le (decayWeight_nonneg c) (fun n => ?_) (hbase.mul_left ((1 + 4 / c) ^ 2))
  have hr := latticeNorm_nonneg n
  have h1 : (1 + |(n 0 : ℝ)|) ^ 2 ≤ (1 + latticeNorm n) ^ 2 :=
    pow_le_pow_left₀ (by positivity) (by linarith [abs_apply_zero_le_latticeNorm n]) 2
  have h2 := h1.trans (one_add_sq_le_mul_exp hc hr)
  calc decayWeight c n ≤ Real.exp (-c * latticeNorm n) * ((1 + 4 / c) ^ 2 * Real.exp (c * latticeNorm n / 2)) :=
        mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
    _ = (1 + 4 / c) ^ 2 * Real.exp (-(c / 2) * latticeNorm n) := by
        rw [mul_left_comm, ← Real.exp_add]
        congr 2
        ring
    _ = (1 + 4 / c) ^ 2 * Real.exp (-(c / 2) * euclidNormVec (0 + castVec n)) := rfl
end Weights
section Lattice
open TorusMetric (euclidNormVec)
open PeriodicOperators (castVec)
def vertexOf (L : ℕ) (n : Fin 4 → ℤ) : FullSpace.Vertex L 0 0 :=
  ⟨fun μ => (n μ : ℝ) * meshAt L 0 0, n, fun _ => rfl⟩
theorem meshAt_zero_zero (L : ℕ) : meshAt L 0 0 = 1 := by
  simp [meshAt]
variable {L : ℕ}
theorem vertexOf_coe (n : Fin 4 → ℤ) (μ : Fin 4) :
    ((vertexOf L n : FullSpace.Vertex L 0 0) : InfiniteLattice.AmbientSpace) μ = (n μ : ℝ) := by
  change (n μ : ℝ) * meshAt L 0 0 = _
  rw [meshAt_zero_zero, mul_one]
theorem vertexOf_add (m n : Fin 4 → ℤ) : vertexOf L (m + n) = vertexOf L m + vertexOf L n := by
  apply Subtype.ext
  funext μ
  simp [vertexOf, add_mul]
theorem vertexOf_zero : vertexOf L 0 = 0 := by
  apply Subtype.ext
  funext μ
  simp [vertexOf]
theorem vertexOf_injective : Function.Injective (vertexOf L) := by
  intro m n h
  funext μ
  have h1 := vertexOf_coe (L := L) m μ
  rw [h, vertexOf_coe] at h1
  exact_mod_cast h1.symm
theorem vertexOf_surjective : Function.Surjective (vertexOf L) := by
  intro x
  obtain ⟨n, hn⟩ := x.2
  exact ⟨n, Subtype.ext (funext fun μ => (hn μ).symm)⟩
def vertexEquiv (L : ℕ) : (Fin 4 → ℤ) ≃ FullSpace.Vertex L 0 0 :=
  Equiv.ofBijective (vertexOf L) ⟨vertexOf_injective, vertexOf_surjective⟩
theorem euclidNormVec_vertexOf_sub (m n : Fin 4 → ℤ) :
    euclidNormVec ((vertexOf L m - vertexOf L n : FullSpace.Vertex L 0 0) : InfiniteLattice.AmbientSpace) =
      latticeNorm (m - n) := by
  unfold latticeNorm euclidNormVec
  congr 1
  refine Finset.sum_congr rfl fun μ _ => ?_
  simp [castVec, vertexOf_coe]
def secondAxisEdge (L : ℕ) (n : Fin 4 → ℤ) : FullSpace.PositiveEdge (meshAt L 0 0) :=
  FullSpace.forwardEdge (vertexOf L n) 1
theorem secondAxisEdge_injective : Function.Injective (secondAxisEdge L) := by
  intro m n h
  exact vertexOf_injective (congrArg (fun b => b.1.initial) h)
theorem linearAbelianAngle_secondAxisEdge (n : Fin 4 → ℤ) :
    FullSpace.linearAbelianAngle (secondAxisEdge L n) = (n 0 : ℝ) := by
  unfold FullSpace.linearAbelianAngle
  rw [if_pos]
  · exact vertexOf_coe n 0
  · change vertexOf L n + InfiniteLattice.axisStep _ 1 - vertexOf L n = _
    simp
theorem exists_secondAxisEdge_eq (b : FullSpace.PositiveEdge (meshAt L 0 0))
    (h : b.1.terminal - b.1.initial = InfiniteLattice.axisStep _ 1) : ∃ n, secondAxisEdge L n = b := by
  obtain ⟨n, hn⟩ := vertexOf_surjective (L := L) b.1.initial
  refine ⟨n, Subtype.ext (InfiniteLattice.Link.ext hn ?_)⟩
  change vertexOf L n + InfiniteLattice.axisStep _ 1 = b.1.terminal
  rw [hn, ← h]
  abel
end Lattice
end LinearAngleSum
open PeriodicOperators (castVec)
open LinearAngleSum
theorem secondDerivativeSumAtLinearAngle_holds
    (hmass : FullSpace.BackgroundJets.MassiveFunctionalAndJets.Claim)
    (hcoef : OneLoopLaw.TemperedStiffness.TemperedStiffnessClaim)
    (hexp : PeriodicOperators.ExponentialSums.Bounds)
    (hsym : SecondDerivativeSymm)
    (hdecay : SecondDerivativeExpDecay)
    (htrans : SecondDerivativeShiftInvariant)
    (hsites : SecondDerivativeSiteSum)
    (hrows : SecondDerivativeRowSumZero) :
    SecondDerivativeSumAtLinearAngle := by
  intro z hz L hL hst
  obtain ⟨⟨hfun, δ, π, e, hch⟩, -⟩ := (hmass L hL hst).1 z hz
  obtain ⟨-, hK, -, b, -, -, hF⟩ := hcoef L hL hst (massiveFieldFamily L z) δ π e hfun hch
  have hform := hF 0 1 (by decide)
  have hcb : massiveStiffness hL z = b := hform.eq_coeff
  obtain ⟨C, c, hc, hdec⟩ := hdecay z hz L hst
  have hdec0 : ∀ (m u v : Fin 4 → ℤ),
      ‖secondDerivative z (vertexOf L m) (secondAxisEdge L u) (secondAxisEdge L v)‖ ≤
        C * Real.exp (-c * (latticeNorm (m - u) + latticeNorm (m - v))) := fun m u v => by
    have h := hdec (vertexOf L m) (secondAxisEdge L u) (secondAxisEdge L v)
    have h1 := euclidNormVec_vertexOf_sub (L := L) m u
    have h2 := euclidNormVec_vertexOf_sub (L := L) m v
    change ‖_‖ ≤ C * Real.exp (-c * (TorusMetric.euclidNormVec
      ((vertexOf L m - vertexOf L u : FullSpace.Vertex L 0 0) : InfiniteLattice.AmbientSpace) +
      TorusMetric.euclidNormVec
      ((vertexOf L m - vertexOf L v : FullSpace.Vertex L 0 0) : InfiniteLattice.AmbientSpace))) at h
    rw [h1, h2] at h
    exact h
  have hC : 0 ≤ C := by
    have h := (norm_nonneg _).trans (hdec0 0 0 0)
    exact nonneg_of_mul_nonneg_left h (Real.exp_pos _)
  have hdiag : ∀ n : Fin 4 → ℤ, HasSum (fun u => secondDerivative z 0 (secondAxisEdge L u)
      (secondAxisEdge L (u + n))) (OneLoopLaw.TemperedStiffness.symbolKernel (π 1 1) n) := by
    intro n
    have hsummable : Summable fun y : FullSpace.Vertex L 0 0 =>
        secondDerivative z y (secondAxisEdge L 0) (secondAxisEdge L n) := by
      refine ((vertexEquiv L).summable_iff).mp ?_
      refine Summable.of_norm_bounded (g := fun m => C * (Real.exp (-c * latticeNorm m) *
        (1 + |(m 0 : ℝ)|) ^ 2)) ((summable_decayWeight hexp hc).mul_left C) fun m => ?_
      have h := hdec0 m 0 n
      rw [sub_zero] at h
      refine h.trans (mul_le_mul_of_nonneg_left ?_ hC)
      have h1 : Real.exp (-c * (latticeNorm m + latticeNorm (m - n))) ≤ Real.exp (-c * latticeNorm m) := by
        refine Real.exp_le_exp.mpr ?_
        nlinarith [latticeNorm_nonneg (m - n)]
      have h2 : (1 : ℝ) ≤ (1 + |(m 0 : ℝ)|) ^ 2 := one_le_pow₀ (by linarith [abs_nonneg (m 0 : ℝ)])
      calc _ ≤ Real.exp (-c * latticeNorm m) := h1
        _ = Real.exp (-c * latticeNorm m) * 1 := (mul_one _).symm
        _ ≤ _ := mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
    have hlim := hsites z hz L hst (0, 1) (n, 1) (vertexOf L 0) (vertexOf L n)
      (fun μ => vertexOf_coe _ μ) (fun μ => vertexOf_coe _ μ)
    have hker := hK (0, 1) (n, 1) 2 2
    simp only [if_true, sub_zero] at hker
    have hval := tendsto_nhds_unique hlim hker
    have hsum : HasSum (fun y : FullSpace.Vertex L 0 0 =>
        secondDerivative z y (secondAxisEdge L 0) (secondAxisEdge L n))
        (OneLoopLaw.TemperedStiffness.symbolKernel (π 1 1) n) := by
      rw [← hval]
      exact hsummable.hasSum
    have hneg := ((Equiv.neg (Fin 4 → ℤ)).trans (vertexEquiv L)).hasSum_iff.mpr hsum
    have he : ((fun y : FullSpace.Vertex L 0 0 =>
        secondDerivative z y (secondAxisEdge L 0) (secondAxisEdge L n)) ∘
          ((Equiv.neg (Fin 4 → ℤ)).trans (vertexEquiv L))) =
        fun u => secondDerivative z 0 (secondAxisEdge L u) (secondAxisEdge L (u + n)) := by
      funext u
      have h := htrans z hz L hst (vertexOf L u) (vertexOf L (-u)) (vertexOf L 0) (vertexOf L n) 1 1
      have h0 : vertexOf L (-u) + vertexOf L u = 0 := by
        rw [← vertexOf_add, neg_add_cancel, vertexOf_zero]
      have h1 : vertexOf L 0 + vertexOf L u = vertexOf L u := by
        rw [← vertexOf_add, zero_add]
      have h2 : vertexOf L n + vertexOf L u = vertexOf L (u + n) := by
        rw [← vertexOf_add, add_comm]
      rw [h0, h1, h2] at h
      exact h.symm
    rw [he] at hneg
    exact hneg
  have hW : Summable fun p : (Fin 4 → ℤ) × (Fin 4 → ℤ) =>
      ‖secondDerivative z 0 (secondAxisEdge L p.1) (secondAxisEdge L p.2)‖ *
        ((1 + ‖((p.1 0 : ℤ) : ℂ)‖) ^ 2 * (1 + ‖((p.2 0 : ℤ) : ℂ)‖) ^ 2) := by
    have hg := (summable_decayWeight hexp hc).mul_of_nonneg (summable_decayWeight hexp hc)
      (decayWeight_nonneg c) (decayWeight_nonneg c)
    refine Summable.of_nonneg_of_le (fun p => by positivity) (fun p => ?_) (hg.mul_left C)
    have h := hdec0 0 p.1 p.2
    rw [vertexOf_zero, zero_sub, zero_sub, latticeNorm_neg, latticeNorm_neg] at h
    have hn1 : ‖((p.1 0 : ℤ) : ℂ)‖ = |(p.1 0 : ℝ)| := by simp
    have hn2 : ‖((p.2 0 : ℤ) : ℂ)‖ = |(p.2 0 : ℝ)| := by simp
    rw [hn1, hn2]
    calc _ ≤ C * Real.exp (-c * (latticeNorm p.1 + latticeNorm p.2)) *
          ((1 + |(p.1 0 : ℝ)|) ^ 2 * (1 + |(p.2 0 : ℝ)|) ^ 2) :=
          mul_le_mul_of_nonneg_right h (by positivity)
      _ = C * (decayWeight c p.1 * decayWeight c p.2) := by
          unfold decayWeight
          rw [show -c * (latticeNorm p.1 + latticeNorm p.2) = -c * latticeNorm p.1 + -c * latticeNorm p.2 by ring,
            Real.exp_add]
          ring
  have hrow : ∀ u : Fin 4 → ℤ, HasSum (fun v => secondDerivative z 0 (secondAxisEdge L u)
      (secondAxisEdge L v)) 0 := fun u =>
    ((vertexEquiv L).hasSum_iff).mpr (hrows z hz L hst (secondAxisEdge L u))
  have hπ : HasSum (fun n : Fin 4 → ℤ => -(1 / 2 : ℂ) *
      (OneLoopLaw.TemperedStiffness.symbolKernel (π 1 1) n * ((n 0 : ℤ) : ℂ) ^ 2)) (b : ℂ) :=
    hform.hasSum_diag
  have hsum := hasSum_mul_mul
    (P := fun u v => secondDerivative z 0 (secondAxisEdge L u) (secondAxisEdge L v))
    (X := fun u : Fin 4 → ℤ => ((u 0 : ℤ) : ℂ))
    (fun u n => by simp) (fun u v => hsym z hz L hst _ _ _) hW hrow hdiag hπ
  have hinj : Function.Injective (Prod.map (secondAxisEdge L) (secondAxisEdge L)) :=
    secondAxisEdge_injective.prodMap secondAxisEdge_injective
  have hoff : ∀ p ∉ Set.range (Prod.map (secondAxisEdge L) (secondAxisEdge L)),
      secondDerivativeTerm z FullSpace.linearAbelianAngle p = 0 := by
    intro p hp
    by_cases h1 : p.1.1.terminal - p.1.1.initial = InfiniteLattice.axisStep _ 1
    · by_cases h2 : p.2.1.terminal - p.2.1.initial = InfiniteLattice.axisStep _ 1
      · obtain ⟨u, hu⟩ := exists_secondAxisEdge_eq p.1 h1
        obtain ⟨v, hv⟩ := exists_secondAxisEdge_eq p.2 h2
        exact absurd ⟨(u, v), Prod.ext hu hv⟩ hp
      · have h0 : (FullSpace.linearAbelianAngle p.2 : ℝ) = 0 := by
          unfold FullSpace.linearAbelianAngle
          exact if_neg h2
        simp [secondDerivativeTerm, h0]
    · have h0 : (FullSpace.linearAbelianAngle p.1 : ℝ) = 0 := by
        unfold FullSpace.linearAbelianAngle
        exact if_neg h1
      simp [secondDerivativeTerm, h0]
  have hterm : HasSum (secondDerivativeTerm (L := L) z FullSpace.linearAbelianAngle) (b : ℂ) := by
    refine (hinj.hasSum_iff hoff).mp ?_
    have he : (secondDerivativeTerm (L := L) z FullSpace.linearAbelianAngle ∘
        Prod.map (secondAxisEdge L) (secondAxisEdge L)) =
        fun p : (Fin 4 → ℤ) × (Fin 4 → ℤ) =>
          secondDerivative z 0 (secondAxisEdge L p.1) (secondAxisEdge L p.2) *
            ((p.1 0 : ℤ) : ℂ) * ((p.2 0 : ℤ) : ℂ) := by
      funext p
      simp [secondDerivativeTerm, linearAbelianAngle_secondAxisEdge]
    rw [he]
    exact hsum
  rw [secondDerivativeSum, hterm.tsum_eq, hcb]
end YangMills.Construction.Tower.AbelianFieldDensity
end
