import YangMills.Construction.IdentificationOfTheOneLoopNumber.MixedVariationOfALogDeterminant
import YangMills.Construction.InfiniteLattice.TransportToATorusProof
import YangMills.Construction.RunningCouplingSlope.CellsOfATower
import Mathlib
import YangMills.Construction.RunningCouplingSlope.SumOfADecayOnATorus
set_option autoImplicit false

noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
open Tower
def MixedDerivLogDetDecays : Prop :=
  ∀ (M θ : ℝ) (D : ℕ), 0 < M → 0 < θ → ∃ C θ' : ℝ, 0 ≤ C ∧ 0 < θ' ∧
    ∀ (L n k : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (c : ι → Vertex L n k k)
      (T : ℝ → ℝ → Matrix ι ι ℂ) (z : Fin 4 → ℤ), Conventions.IsAdmissibleBlockingFactor L → 0 < n →
      (∀ y, (Finset.univ.filter fun p => c p = y).card ≤ D) →
      IsLocalFamily c T z M θ →
        |deriv (fun s => deriv (fun t => Real.log ‖Matrix.det (T s t)‖) 0) 0| ≤
          C * Real.exp (-(θ' * cellDist (cellOfCoords L n k 0) (cellOfCoords L n k z)))
end YangMills.Construction.RunningCouplingSlope
end

open Filter Topology
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
open YangMills.Construction.Tower YangMills.Construction.TorusMetric
variable {L n k : ℕ}
private theorem torusLifts_nonempty {S : ℝ} (x : Torus4 S) :
    (euclidNormVec '' (TorusMetric.torusProj S ⁻¹' {x})).Nonempty := by
  choose v hv using fun μ => QuotientAddGroup.mk_surjective (x μ)
  exact ⟨_, v, funext hv, rfl⟩
private theorem torusEuclidNorm_nonneg {S : ℝ} (x : Torus4 S) : 0 ≤ torusEuclidNorm x := by apply _root_.YangMills.Construction.TestPairs.torusEuclidNorm_nonneg <;> assumption
private theorem torusEuclidNorm_add_le {S : ℝ} (x y : Torus4 S) :
    torusEuclidNorm (x + y) ≤ torusEuclidNorm x + torusEuclidNorm y := by apply _root_.YangMills.Construction.TestPairs.torusEuclidNorm_add_le <;> assumption
private theorem torusEuclidNorm_neg_le {S : ℝ} (x : Torus4 S) :
    torusEuclidNorm (-x) ≤ torusEuclidNorm x := by apply _root_.YangMills.Construction.PeriodicTransport.torusEuclidNorm_neg_le <;> assumption
private theorem cellDist_nonneg' (y y' : Vertex L n k k) : 0 ≤ cellDist y y' :=
  torusEuclidNorm_nonneg _
abbrev _root_.YangMills.SharedProofs.p2231 := @cellDist_nonneg'
private theorem cellDist_comm' (y y' : Vertex L n k k) : cellDist y y' = cellDist y' y := by
  have h : ∀ a b : Vertex L n k k, cellDist a b ≤ cellDist b a := by
    intro a b
    have := torusEuclidNorm_neg_le
      ((b : PeriodicLattice.FourTorus L n) - (a : PeriodicLattice.FourTorus L n))
    rwa [neg_sub] at this
  exact le_antisymm (h _ _) (h _ _)
abbrev _root_.YangMills.SharedProofs.p19196 := @cellDist_comm'
private theorem cellDist_triangle' (a b c : Vertex L n k k) :
    cellDist a c ≤ cellDist a b + cellDist b c := by
  have := torusEuclidNorm_add_le
    ((a : PeriodicLattice.FourTorus L n) - (b : PeriodicLattice.FourTorus L n))
    ((b : PeriodicLattice.FourTorus L n) - (c : PeriodicLattice.FourTorus L n))
  rwa [sub_add_sub_cancel] at this
abbrev _root_.YangMills.SharedProofs.p82152 := @cellDist_triangle'
private theorem exists_int_coords (y : Vertex L n k k) :
    ∃ m : Fin 4 → ℤ, ∀ μ, (y : PeriodicLattice.FourTorus L n) μ =
      (((m μ : ℤ) : ℝ) : AddCircle (PeriodicLattice.torusSide L n)) := by
  obtain ⟨m, hm⟩ := y.2
  refine ⟨m, fun μ => ?_⟩
  rw [hm μ]
  simp [PeriodicLattice.meshSize, PeriodicLattice.levelDepth]
private theorem torusSide_eq_natCast :
    PeriodicLattice.torusSide L n = ((2 * L ^ n : ℕ) : ℝ) := by
  simp [PeriodicLattice.torusSide]
private theorem exists_supDist_chart [NeZero (2 * L ^ n)] :
    ∃ φ : Vertex L n k k → TorusFields.TorusSite (2 * L ^ n), Function.Injective φ ∧
      ∀ y y', (TorusFields.supDist (φ y) (φ y') : ℝ) ≤ cellDist y y' := by
  choose m hm using (exists_int_coords : ∀ y : Vertex L n k k, _)
  refine ⟨fun y μ => ((m y μ : ℤ) : ZMod (2 * L ^ n)), ?_, ?_⟩
  · intro y y' h
    apply Subtype.ext
    funext μ
    have h1 : ((m y μ : ℤ) : ZMod (2 * L ^ n)) = (m y' μ : ℤ) := congrFun h μ
    obtain ⟨a, ha⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1 h1
    rw [hm y μ, hm y' μ, ← sub_eq_zero, ← AddCircle.coe_sub, AddCircle.coe_eq_zero_iff]
    refine ⟨-a, ?_⟩
    have h2 : ((m y' μ - m y μ : ℤ) : ℝ) = (((2 * L ^ n : ℕ) : ℤ) * a : ℤ) := by rw [ha]
    rw [zsmul_eq_mul, torusSide_eq_natCast]
    push_cast at h2 ⊢
    linarith
  · intro y y'
    unfold cellDist
    refine le_csInf (torusLifts_nonempty _) ?_
    rintro _ ⟨v, hv, rfl⟩
    obtain ⟨μ, -, hμ⟩ := Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty
      (fun i => ((((m y i : ℤ) : ZMod (2 * L ^ n)) - ((m y' i : ℤ) : ZMod (2 * L ^ n))).valMinAbs).natAbs)
    have hv' : TorusMetric.torusProj (PeriodicLattice.torusSide L n) v =
      (y : PeriodicLattice.FourTorus L n) - (y' : PeriodicLattice.FourTorus L n) := hv
    have hvμ : ((v μ : ℝ) : AddCircle (PeriodicLattice.torusSide L n)) =
        (y : PeriodicLattice.FourTorus L n) μ - (y' : PeriodicLattice.FourTorus L n) μ :=
      congrFun hv' μ
    rw [hm y μ, hm y' μ, ← AddCircle.coe_sub] at hvμ
    have h0 : ((v μ - (((m y μ : ℤ) : ℝ) - ((m y' μ : ℤ) : ℝ)) : ℝ) :
        AddCircle (PeriodicLattice.torusSide L n)) = 0 := by
      rw [AddCircle.coe_sub, hvμ, sub_self]
    obtain ⟨a, ha⟩ := (AddCircle.coe_eq_zero_iff _).1 h0
    rw [zsmul_eq_mul, torusSide_eq_natCast] at ha
    have hvw : v μ = ((m y μ - m y' μ + a * ((2 * L ^ n : ℕ) : ℤ) : ℤ) : ℝ) := by
      push_cast at ha ⊢
      linarith
    have hcast : (((m y μ - m y' μ + a * ((2 * L ^ n : ℕ) : ℤ) : ℤ)) : ZMod (2 * L ^ n)) =
        ((m y μ : ℤ) : ZMod (2 * L ^ n)) - ((m y' μ : ℤ) : ZMod (2 * L ^ n)) := by
      rw [Int.cast_add, Int.cast_sub, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self, mul_zero, add_zero]
    have h1 := ZMod.natAbs_min_of_le_div_two (2 * L ^ n)
      ((((m y μ : ℤ) : ZMod (2 * L ^ n)) - ((m y' μ : ℤ) : ZMod (2 * L ^ n))).valMinAbs)
      (m y μ - m y' μ + a * ((2 * L ^ n : ℕ) : ℤ))
      (by rw [ZMod.coe_valMinAbs, hcast]) (ZMod.natAbs_valMinAbs_le _)
    have h2 : TorusFields.supDist (fun i => ((m y i : ℤ) : ZMod (2 * L ^ n)))
        (fun i => ((m y' i : ℤ) : ZMod (2 * L ^ n))) =
        ((((m y μ : ℤ) : ZMod (2 * L ^ n)) - ((m y' μ : ℤ) : ZMod (2 * L ^ n))).valMinAbs).natAbs := hμ
    rw [h2]
    calc (((((m y μ : ℤ) : ZMod (2 * L ^ n)) - ((m y' μ : ℤ) : ZMod (2 * L ^ n))).valMinAbs).natAbs : ℝ)
        ≤ ((m y μ - m y' μ + a * ((2 * L ^ n : ℕ) : ℤ)).natAbs : ℝ) := by exact_mod_cast h1
      _ = |v μ| := by rw [hvw, Nat.cast_natAbs, Int.cast_abs]
      _ ≤ euclidNormVec v := by
        refine Real.abs_le_sqrt ?_
        exact Finset.single_le_sum (f := fun i => v i ^ 2) (fun i _ => sq_nonneg _) (Finset.mem_univ μ)
abbrev _root_.YangMills.SharedProofs.p77197 := @exists_supDist_chart
private theorem sum_exp_cellDist_le (hL : 0 < L) {ι : Type} [Fintype ι] (c : ι → Vertex L n k k)
    {D : ℕ} (hD : ∀ (y : Vertex L n k k) (s : Finset ι), (∀ p, p ∈ s ↔ c p = y) → s.card ≤ D)
    {r S : ℝ} (hr : 0 < r)
    (hS : ∀ (N : ℕ) [NeZero N] (y : TorusFields.TorusSite N),
      ∑ x : TorusFields.TorusSite N, Real.exp (-(r * TorusFields.supDist y x)) ≤ S)
    (y₀ : Vertex L n k k) :
    ∑ p, Real.exp (-(r * cellDist (c p) y₀)) ≤ D * S := by
  classical
  have : NeZero (2 * L ^ n) := ⟨by positivity⟩
  obtain ⟨φ, hinj, hle⟩ := exists_supDist_chart (L := L) (n := n) (k := k)
  obtain ⟨g, hg⟩ : ∃ g : TorusFields.TorusSite (2 * L ^ n) → ℝ,
      g = fun x => Real.exp (-(r * TorusFields.supDist (φ y₀) x)) := ⟨_, rfl⟩
  have hg0 : ∀ x, 0 ≤ g x := fun x => by rw [hg]; exact (Real.exp_pos _).le
  have h1 : ∀ p, Real.exp (-(r * cellDist (c p) y₀)) ≤ g (φ (c p)) := by
    intro p
    rw [hg]
    refine Real.exp_le_exp.2 ?_
    have h := hle y₀ (c p)
    rw [cellDist_comm'] at h
    have := mul_le_mul_of_nonneg_left h hr.le
    linarith
  calc ∑ p, Real.exp (-(r * cellDist (c p) y₀))
      ≤ ∑ p, g ((φ ∘ c) p) := Finset.sum_le_sum fun p _ => h1 p
    _ = ∑ b ∈ Finset.univ.image (φ ∘ c), (Finset.univ.filter fun a => (φ ∘ c) a = b).card • g b :=
        Finset.sum_comp g (φ ∘ c)
    _ ≤ ∑ b ∈ Finset.univ.image (φ ∘ c), (D : ℝ) * g b := by
        refine Finset.sum_le_sum fun b hb => ?_
        obtain ⟨p₀, -, rfl⟩ := Finset.mem_image.1 hb
        rw [nsmul_eq_mul]
        refine mul_le_mul_of_nonneg_right ?_ (hg0 _)
        have := hD (c p₀) (Finset.univ.filter fun a => (φ ∘ c) a = (φ ∘ c) p₀)
          (fun p => by simp [hinj.eq_iff])
        exact_mod_cast this
    _ ≤ ∑ b, (D : ℝ) * g b :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          fun b _ _ => mul_nonneg (Nat.cast_nonneg _) (hg0 b)
    _ = (D : ℝ) * ∑ b, g b := (Finset.mul_sum _ _ _).symm
    _ ≤ D * S := by
        refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
        rw [hg]
        exact hS _ _
private theorem norm_entry_le_opNorm {ι ι' : Type} [Fintype ι] [Fintype ι'] [DecidableEq ι]
    (A : Matrix ι' ι ℂ) (p : ι') (q : ι) : ‖A p q‖ ≤ ‖A‖ := by
  have h := Matrix.l2_opNorm_mulVec A (EuclideanSpace.single q (1 : ℂ))
  have h2 : ‖(EuclideanSpace.single q (1 : ℂ) : EuclideanSpace ℂ ι)‖ = 1 := by simp
  rw [h2, mul_one] at h
  refine le_trans ?_ h
  refine le_trans (le_of_eq ?_) (PiLp.norm_apply_le _ p)
  simp
private theorem norm_entry_le_of_local {ι ι' : Type} [Fintype ι] [Fintype ι'] [DecidableEq ι]
    {c : ι → Vertex L n k k} {c' : ι' → Vertex L n k k} {T : Matrix ι' ι ℂ} {M θ : ℝ}
    {m : Vertex L n k k → ℝ} (h : IsLocalOnCells c c' T M θ m) (p : ι') (q : ι) :
    ‖T p q‖ ≤ M * Real.exp (-(θ * cellDist (c' p) (c q))) * m (c' p) := by
  refine le_trans (le_of_eq ?_)
    ((norm_entry_le_opNorm (blockBetween c c' T (c' p) (c q)) p q).trans (h _ _))
  simp [blockBetween]
private theorem eventually_differentiableAt_slice {f : ℝ × ℝ → ℂ} (h : ContDiffAt ℝ 2 f 0) :
    ∀ᶠ s in 𝓝 (0 : ℝ), DifferentiableAt ℝ f (s, 0) := by
  have h1 : ∀ᶠ u in 𝓝 (0 : ℝ × ℝ), ContDiffAt ℝ 2 f u := h.eventually (by simp)
  have h2 : Tendsto (fun s : ℝ => (s, (0 : ℝ))) (𝓝 0) (𝓝 (0 : ℝ × ℝ)) := by
    have h3 : Continuous fun s : ℝ => (s, (0 : ℝ)) := by fun_prop
    exact h3.tendsto 0
  exact (h2.eventually h1).mono fun s hs => hs.differentiableAt (by norm_num)
private theorem hasDerivAt_second_slice {f : ℝ × ℝ → ℂ} {s : ℝ} (h : DifferentiableAt ℝ f (s, 0)) :
    HasDerivAt (fun t => f (s, t)) (fderiv ℝ f (s, 0) (0, 1)) 0 := by
  have h1 : HasDerivAt (fun t : ℝ => (s, t)) ((0 : ℝ), (1 : ℝ)) 0 :=
    (hasDerivAt_const _ s).prodMk (hasDerivAt_id _)
  exact h.hasFDerivAt.comp_hasDerivAt 0 h1
private theorem differentiableAt_first_slice {f : ℝ × ℝ → ℂ} (h : ContDiffAt ℝ 2 f 0) :
    DifferentiableAt ℝ (fun s => f (s, 0)) 0 := by
  have h1 : DifferentiableAt ℝ f ((fun s : ℝ => (s, (0 : ℝ))) 0) := h.differentiableAt (by norm_num)
  have h3 : DifferentiableAt ℝ (fun s : ℝ => (s, (0 : ℝ))) 0 := by fun_prop
  exact DifferentiableAt.comp (0 : ℝ) h1 h3
private theorem differentiableAt_mixed_slice {f : ℝ × ℝ → ℂ} (h : ContDiffAt ℝ 2 f 0) :
    DifferentiableAt ℝ (fun s => deriv (fun t => f (s, t)) 0) 0 := by
  have h1 : ContDiffAt ℝ 1 (fderiv ℝ f) 0 := h.fderiv_right (by norm_num)
  have h2 : DifferentiableAt ℝ (fderiv ℝ f) ((fun s : ℝ => (s, (0 : ℝ))) 0) :=
    h1.differentiableAt (by norm_num)
  have h3 : DifferentiableAt ℝ (fun s : ℝ => (s, (0 : ℝ))) 0 := by fun_prop
  have h4 : DifferentiableAt ℝ (fun s : ℝ => fderiv ℝ f (s, 0)) 0 := DifferentiableAt.comp (0 : ℝ) h2 h3
  have h5 : DifferentiableAt ℝ (fun s : ℝ => fderiv ℝ f (s, 0) (0, 1)) 0 :=
    h4.clm_apply (differentiableAt_const _)
  refine h5.congr_of_eventuallyEq ?_
  filter_upwards [eventually_differentiableAt_slice h] with s hs
  exact (hasDerivAt_second_slice hs).deriv
abbrev _root_.YangMills.SharedProofs.p42628 := @differentiableAt_mixed_slice
private theorem deriv_deriv_log_norm_det
    (hVar : OneLoopCoefficient.hasDerivAt_mixed_logDet_statement)
    {ι : Type} [Fintype ι] [DecidableEq ι] {T : ℝ → ℝ → Matrix ι ι ℂ}
    (smooth : ∀ p q, ContDiffAt ℝ 2 (fun u : ℝ × ℝ => T u.1 u.2 p q) 0)
    (hinv : IsUnit (Matrix.det (T 0 0))) :
    deriv (fun s => deriv (fun t => Real.log ‖Matrix.det (T s t)‖) 0) 0 =
      (((T 0 0)⁻¹ * derivMixed T).trace -
        ((T 0 0)⁻¹ * derivFirst T * ((T 0 0)⁻¹ * derivSecond T)).trace).re := by
  obtain ⟨A, hA⟩ : ∃ A, A = (T 0 0)⁻¹ := ⟨_, rfl⟩
  rw [← hA]
  obtain ⟨K, hK⟩ : ∃ K : ℝ → ℝ → Matrix ι ι ℂ, K = fun s t => A * T s t := ⟨_, rfl⟩
  have hK00 : K 0 0 = 1 := by
    rw [hK, hA]
    exact Matrix.nonsing_inv_mul _ hinv
  have hKe : ∀ s t i j, K s t i j = ∑ r, A i r * T s t r j := by
    intro s t i j
    rw [hK]
    exact Matrix.mul_apply
  have hev : ∀ᶠ s in 𝓝 (0 : ℝ), ∀ p q, DifferentiableAt ℝ (fun t => T s t p q) 0 := by
    have h : ∀ p q, ∀ᶠ s in 𝓝 (0 : ℝ), DifferentiableAt ℝ (fun t => T s t p q) 0 := fun p q =>
      (eventually_differentiableAt_slice (smooth p q)).mono fun s hs =>
        (hasDerivAt_second_slice hs).differentiableAt
    exact eventually_all.2 fun p => eventually_all.2 fun q => h p q
  have hKt : ∀ s, (∀ p q, DifferentiableAt ℝ (fun t => T s t p q) 0) → ∀ i j,
      HasDerivAt (fun t => K s t i j) (∑ r, A i r * deriv (fun t => T s t r j) 0) 0 := by
    intro s hs i j
    simp only [hKe]
    exact HasDerivAt.fun_sum fun r _ => (hs r j).hasDerivAt.const_mul (A i r)
  have h0 : ∀ᶠ u in 𝓝 (0 : ℝ), ∀ i j, DifferentiableAt ℝ (fun t => K u t i j) 0 :=
    hev.mono fun u hu i j => (hKt u hu i j).differentiableAt
  have h1 : ∀ i j, HasDerivAt (fun u => K u 0 i j) ((A * derivFirst T) i j) 0 := by
    intro i j
    simp only [hKe, Matrix.mul_apply]
    exact HasDerivAt.fun_sum fun r _ =>
      (differentiableAt_first_slice (smooth r j)).hasDerivAt.const_mul (A i r)
  have h1' : ∀ i j, HasDerivAt (fun t => K 0 t i j) ((A * derivSecond T) i j) 0 := by
    intro i j
    rw [Matrix.mul_apply]
    exact hKt 0 hev.self_of_nhds i j
  have h2 : ∀ i j, HasDerivAt (fun u => deriv (fun t => K u t i j) 0)
      ((A * derivMixed T) i j) 0 := by
    intro i j
    have h3 : HasDerivAt (fun u => ∑ r, A i r * deriv (fun t => T u t r j) 0)
        ((A * derivMixed T) i j) 0 := by
      rw [Matrix.mul_apply]
      exact HasDerivAt.fun_sum fun r _ =>
        (differentiableAt_mixed_slice (smooth r j)).hasDerivAt.const_mul (A i r)
    refine h3.congr_of_eventuallyEq ?_
    filter_upwards [hev] with u hu
    exact (hKt u hu i j).deriv
  obtain ⟨hdl, hder⟩ := hVar ι K (A * derivFirst T) (A * derivSecond T)
    (A * derivMixed T) h0 h1 h1' h2 (by rw [hK00]; simp [Complex.one_mem_slitPlane])
  have hdetK : ∀ s t, (K s t).det = A.det * (T s t).det := by
    intro s t
    rw [hK]
    exact Matrix.det_mul _ _
  have ha : A.det ≠ 0 := by
    intro h
    have h3 := hdetK 0 0
    rw [hK00, h] at h3
    simp at h3
  have hΔ : ∀ᶠ u in 𝓝 ((0 : ℝ), (0 : ℝ)), (T u.1 u.2).det ≠ 0 := by
    have hc0 : ContinuousAt (fun u : ℝ × ℝ => T u.1 u.2) ((0 : ℝ), (0 : ℝ)) :=
      continuousAt_pi.2 fun p => continuousAt_pi.2 fun q => (smooth p q).continuousAt
    have hc : ContinuousAt (fun u : ℝ × ℝ => (T u.1 u.2).det) ((0 : ℝ), (0 : ℝ)) :=
      (continuous_id.matrix_det).continuousAt.comp hc0
    exact hc.eventually_ne hinv.ne_zero
  have hfun : (fun s => deriv (fun t => Real.log ‖Matrix.det (T s t)‖) 0) =ᶠ[𝓝 0]
      fun s => (deriv (fun t => Complex.log (K s t).det) 0).re := by
    filter_upwards [hΔ.curry_nhds, hdl] with s hs hd
    have h3 : (fun t => Real.log ‖Matrix.det (T s t)‖) =ᶠ[𝓝 0]
        fun t => (Complex.log (K s t).det).re - Real.log ‖A.det‖ := by
      filter_upwards [hs] with t ht
      rw [Complex.log_re, hdetK, norm_mul,
        Real.log_mul (norm_ne_zero_iff.2 ha) (norm_ne_zero_iff.2 ht)]
      ring
    rw [h3.deriv_eq]
    have h4 : HasDerivAt (fun t => (Complex.log (K s t).det).re - Real.log ‖A.det‖)
        (deriv (fun t => Complex.log (K s t).det) 0).re 0 :=
      (Complex.reCLM.hasFDerivAt.comp_hasDerivAt 0 hd.hasDerivAt).sub_const _
    exact h4.deriv
  rw [hfun.deriv_eq]
  have h5 : HasDerivAt (fun s => (deriv (fun t => Complex.log (K s t).det) 0).re) _ 0 :=
    Complex.reCLM.hasFDerivAt.comp_hasDerivAt 0 hder
  rw [h5.deriv, hK00]
  simp only [inv_one, one_mul]
  rfl
private theorem norm_trace_mul_le_sum {ι : Type} [Fintype ι] (A Z : Matrix ι ι ℂ) :
    ‖(A * Z).trace‖ ≤ ∑ p, ∑ q, ‖A p q‖ * ‖Z q p‖ := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun p _ =>
    (norm_sum_le _ _).trans (Finset.sum_le_sum fun q _ => norm_mul_le _ _))
private theorem norm_mul_apply_le_sum {ι : Type} [Fintype ι] (A X : Matrix ι ι ℂ) (p u : ι) :
    ‖(A * X) p u‖ ≤ ∑ q, ‖A p q‖ * ‖X q u‖ := by
  rw [Matrix.mul_apply]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun q _ => norm_mul_le _ _)
private theorem norm_trace_two_le {ι : Type} [Fintype ι] (A Z : Matrix ι ι ℂ) (e : ι → ι → ℝ)
    (eo : ι → ℝ) {R B : ℝ} (hR : 0 ≤ R) (hB : 0 ≤ B) (heo : ∀ q, 0 ≤ eo q)
    (hcol : ∀ q, ∑ p, e p q ≤ B) (ho : ∑ q, eo q ≤ B)
    (hpt : ∀ p q, ‖A p q‖ * ‖Z q p‖ ≤ R * (e p q * eo q)) :
    ‖(A * Z).trace‖ ≤ R * B ^ 2 := by
  calc ‖(A * Z).trace‖ ≤ ∑ p, ∑ q, ‖A p q‖ * ‖Z q p‖ := norm_trace_mul_le_sum A Z
    _ ≤ ∑ p, ∑ q, R * (e p q * eo q) :=
        Finset.sum_le_sum fun p _ => Finset.sum_le_sum fun q _ => hpt p q
    _ = R * ∑ q, eo q * ∑ p, e p q := by
        rw [Finset.sum_comm, Finset.mul_sum]
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [← Finset.mul_sum, Finset.mul_sum (a := eo q)]
        congr 1
        exact Finset.sum_congr rfl fun p _ => mul_comm _ _
    _ ≤ R * ∑ q, eo q * B := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun q _ => ?_) hR
        exact mul_le_mul_of_nonneg_left (hcol q) (heo q)
    _ = R * ((∑ q, eo q) * B) := by rw [Finset.sum_mul]
    _ ≤ R * (B * B) := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ho hB) hR
    _ = R * B ^ 2 := by ring
private theorem norm_trace_four_le {ι : Type} [Fintype ι] (A X Y : Matrix ι ι ℂ) (e : ι → ι → ℝ)
    (eo ew : ι → ℝ) {R B : ℝ} (hR : 0 ≤ R) (hB : 0 ≤ B) (he : ∀ p q, 0 ≤ e p q)
    (heo : ∀ q, 0 ≤ eo q) (hcol : ∀ q, ∑ p, e p q ≤ B) (ho : ∑ q, eo q ≤ B) (hw : ∑ v, ew v ≤ B)
    (hpt : ∀ p q u v, ‖A p q‖ * ‖X q u‖ * (‖A u v‖ * ‖Y v p‖) ≤
      R * (e p q * eo q * e u q * ew v)) :
    ‖(A * X * (A * Y)).trace‖ ≤ R * B ^ 4 := by
  have hin : ∀ p q u, 0 ≤ e p q * eo q * e u q := fun p q u =>
    mul_nonneg (mul_nonneg (he _ _) (heo _)) (he _ _)
  have hswap : ∑ p, ∑ u, ∑ q, e p q * eo q * e u q = ∑ q, ∑ p, ∑ u, e p q * eo q * e u q := by
    rw [Finset.sum_congr rfl fun p _ => Finset.sum_comm, Finset.sum_comm]
  have hq : ∀ q, ∑ p, ∑ u, e p q * eo q * e u q ≤ eo q * (B * B) := by
    intro q
    have h1 : ∑ p, ∑ u, e p q * eo q * e u q = eo q * ((∑ p, e p q) * ∑ u, e u q) := by
      rw [Finset.sum_mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun u _ => by ring
    rw [h1]
    exact mul_le_mul_of_nonneg_left (mul_le_mul (hcol q) (hcol q)
      (Finset.sum_nonneg fun u _ => he u q) hB) (heo q)
  calc ‖(A * X * (A * Y)).trace‖
      ≤ ∑ p, ∑ u, ‖(A * X) p u‖ * ‖(A * Y) u p‖ := norm_trace_mul_le_sum _ _
    _ ≤ ∑ p, ∑ u, (∑ q, ‖A p q‖ * ‖X q u‖) * ∑ v, ‖A u v‖ * ‖Y v p‖ :=
        Finset.sum_le_sum fun p _ => Finset.sum_le_sum fun u _ =>
          mul_le_mul (norm_mul_apply_le_sum _ _ _ _) (norm_mul_apply_le_sum _ _ _ _) (norm_nonneg _)
            (Finset.sum_nonneg fun q _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = ∑ p, ∑ u, ∑ q, ∑ v, ‖A p q‖ * ‖X q u‖ * (‖A u v‖ * ‖Y v p‖) :=
        Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun u _ => Finset.sum_mul_sum _ _ _ _
    _ ≤ ∑ p, ∑ u, ∑ q, R * B * (e p q * eo q * e u q) := by
        refine Finset.sum_le_sum fun p _ => Finset.sum_le_sum fun u _ =>
          Finset.sum_le_sum fun q _ => ?_
        calc ∑ v, ‖A p q‖ * ‖X q u‖ * (‖A u v‖ * ‖Y v p‖)
            ≤ ∑ v, R * (e p q * eo q * e u q * ew v) := Finset.sum_le_sum fun v _ => hpt p q u v
          _ = R * (e p q * eo q * e u q) * ∑ v, ew v := by
              rw [Finset.mul_sum]
              exact Finset.sum_congr rfl fun v _ => by ring
          _ ≤ R * (e p q * eo q * e u q) * B :=
              mul_le_mul_of_nonneg_left hw (mul_nonneg hR (hin p q u))
          _ = R * B * (e p q * eo q * e u q) := by ring
    _ = R * B * ∑ p, ∑ u, ∑ q, e p q * eo q * e u q := by
        simp only [Finset.mul_sum]
    _ ≤ R * B * ∑ q, eo q * (B * B) := by
        rw [hswap]
        exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun q _ => hq q) (mul_nonneg hR hB)
    _ = R * B * ((∑ q, eo q) * (B * B)) := by rw [Finset.sum_mul]
    _ ≤ R * B * (B * (B * B)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ho (mul_nonneg hB hB))
          (mul_nonneg hR hB)
    _ = R * B ^ 4 := by ring
private theorem pointwise_two_le {M θ a b d₁ d₂ w₁ w₂ δ : ℝ} (hM : 0 < M) (hθ : 0 < θ) (hb0 : 0 ≤ b)
    (ha : a ≤ M * Real.exp (-(θ * d₁)) * 1)
    (hb : b ≤ M * Real.exp (-(θ * d₂)) * (Real.exp (-(θ * w₁)) * Real.exp (-(θ * w₂))))
    (hd₁ : 0 ≤ d₁) (hw₂ : 0 ≤ w₂) (hd : d₂ = d₁) (hδ : δ ≤ w₁ + w₂) :
    a * b ≤ M ^ 2 * Real.exp (-(θ / 2 * δ)) *
      (Real.exp (-(θ / 2 * d₁)) * Real.exp (-(θ / 2 * w₁))) := by
  subst hd
  have h1 : a * b ≤ M * Real.exp (-(θ * d₂)) * 1 *
      (M * Real.exp (-(θ * d₂)) * (Real.exp (-(θ * w₁)) * Real.exp (-(θ * w₂)))) :=
    mul_le_mul ha hb hb0 (by positivity)
  have h2 : M * Real.exp (-(θ * d₂)) * 1 *
      (M * Real.exp (-(θ * d₂)) * (Real.exp (-(θ * w₁)) * Real.exp (-(θ * w₂)))) =
      M ^ 2 * Real.exp (-(θ * d₂) + -(θ * d₂) + -(θ * w₁) + -(θ * w₂)) := by
    simp only [Real.exp_add]
    ring
  have h3 : M ^ 2 * Real.exp (-(θ / 2 * δ)) *
      (Real.exp (-(θ / 2 * d₂)) * Real.exp (-(θ / 2 * w₁))) =
      M ^ 2 * Real.exp (-(θ / 2 * δ) + -(θ / 2 * d₂) + -(θ / 2 * w₁)) := by
    simp only [Real.exp_add]
    ring
  rw [h3]
  refine h1.trans (h2.le.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by positivity)))
  have e1 := mul_le_mul_of_nonneg_left hδ hθ.le
  have e2 := mul_nonneg hθ.le hw₂
  have e3 := mul_nonneg hθ.le hd₁
  nlinarith
private theorem pointwise_four_le {M θ a x a' y d₁ d₂ d₂' d₃ d₄ w₁ w₂ δ : ℝ} (hM : 0 < M)
    (hθ : 0 < θ) (hx0 : 0 ≤ x) (ha0' : 0 ≤ a') (hy0 : 0 ≤ y)
    (ha : a ≤ M * Real.exp (-(θ * d₁)) * 1)
    (hx : x ≤ M * Real.exp (-(θ * d₂)) * Real.exp (-(θ * w₁)))
    (ha' : a' ≤ M * Real.exp (-(θ * d₃)) * 1)
    (hy : y ≤ M * Real.exp (-(θ * d₄)) * Real.exp (-(θ * w₂)))
    (hd₂ : 0 ≤ d₂) (hd₃ : 0 ≤ d₃) (hd₄ : 0 ≤ d₄) (hd : d₂' = d₂) (hδ : δ ≤ w₁ + d₁ + d₄ + w₂) :
    a * x * (a' * y) ≤ M ^ 4 * Real.exp (-(θ / 2 * δ)) *
      (Real.exp (-(θ / 2 * d₁)) * Real.exp (-(θ / 2 * w₁)) * Real.exp (-(θ / 2 * d₂')) *
        Real.exp (-(θ / 2 * w₂))) := by
  subst hd
  have h1 : a * x * (a' * y) ≤ M * Real.exp (-(θ * d₁)) * 1 *
      (M * Real.exp (-(θ * d₂')) * Real.exp (-(θ * w₁))) *
      (M * Real.exp (-(θ * d₃)) * 1 * (M * Real.exp (-(θ * d₄)) * Real.exp (-(θ * w₂)))) :=
    mul_le_mul (mul_le_mul ha hx hx0 (by positivity)) (mul_le_mul ha' hy hy0 (by positivity))
      (mul_nonneg ha0' hy0) (by positivity)
  have h2 : M * Real.exp (-(θ * d₁)) * 1 * (M * Real.exp (-(θ * d₂')) * Real.exp (-(θ * w₁))) *
      (M * Real.exp (-(θ * d₃)) * 1 * (M * Real.exp (-(θ * d₄)) * Real.exp (-(θ * w₂)))) =
      M ^ 4 * Real.exp (-(θ * d₁) + -(θ * d₂') + -(θ * w₁) + -(θ * d₃) + -(θ * d₄) + -(θ * w₂)) := by
    simp only [Real.exp_add]
    ring
  have h3 : M ^ 4 * Real.exp (-(θ / 2 * δ)) *
      (Real.exp (-(θ / 2 * d₁)) * Real.exp (-(θ / 2 * w₁)) * Real.exp (-(θ / 2 * d₂')) *
        Real.exp (-(θ / 2 * w₂))) =
      M ^ 4 * Real.exp (-(θ / 2 * δ) + -(θ / 2 * d₁) + -(θ / 2 * w₁) + -(θ / 2 * d₂') +
        -(θ / 2 * w₂)) := by
    simp only [Real.exp_add]
    ring
  rw [h3]
  refine h1.trans (h2.le.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by positivity)))
  have e1 := mul_le_mul_of_nonneg_left hδ hθ.le
  have e2 := mul_nonneg hθ.le hd₂
  have e3 := mul_nonneg hθ.le hd₃
  have e4 := mul_nonneg hθ.le hd₄
  nlinarith
theorem mixedDerivLogDetDecays_holds (hSum : SlopeCoefficient.ExpDecayTorusSumBounded)
    (hVar : OneLoopCoefficient.hasDerivAt_mixed_logDet_statement) :
    MixedDerivLogDetDecays := by
  intro M θ D hM hθ
  obtain ⟨S, hS0, hS⟩ := hSum (θ / 2) (by positivity)
  refine ⟨M ^ 2 * ((D : ℝ) * S) ^ 2 + M ^ 4 * ((D : ℝ) * S) ^ 4, θ / 2, by positivity,
    by positivity, ?_⟩
  intro L n k ι _ _ c T z hL hn hD hloc
  have hL0 : 0 < L := by
    have := hL.2
    omega
  have hD' : ∀ (y : Vertex L n k k) (s : Finset ι), (∀ p, p ∈ s ↔ c p = y) → s.card ≤ D := by
    intro y s hs
    convert hD y
    ext p
    simp [hs]
  have hsum := fun y₀ => sum_exp_cellDist_le hL0 c hD' (half_pos hθ) hS y₀
  have hi := hloc.inv_local
  have hs := hloc.derivFirst_local
  have ht := hloc.derivSecond_local
  have hm := hloc.derivMixed_local
  obtain ⟨o, ho⟩ : ∃ o, o = cellOfCoords L n k 0 := ⟨_, rfl⟩
  obtain ⟨w, hw⟩ : ∃ w, w = cellOfCoords L n k z := ⟨_, rfl⟩
  rw [← ho] at hs hm
  rw [← hw] at ht hm
  rw [← ho, ← hw, deriv_deriv_log_norm_det hVar hloc.contDiffAt hloc.isUnit_det]
  have hfirst : ‖((T 0 0)⁻¹ * derivMixed T).trace‖ ≤
      M ^ 2 * Real.exp (-(θ / 2 * cellDist o w)) * ((D : ℝ) * S) ^ 2 := by
    refine norm_trace_two_le _ _ (fun p q => Real.exp (-(θ / 2 * cellDist (c p) (c q))))
      (fun q => Real.exp (-(θ / 2 * cellDist (c q) o))) (by positivity) (by positivity)
      (fun _ => (Real.exp_pos _).le) (fun q => hsum (c q)) (hsum o) fun p q => ?_
    refine pointwise_two_le hM hθ (norm_nonneg _) (norm_entry_le_of_local hi p q)
      (norm_entry_le_of_local hm q p)
      (cellDist_nonneg' _ _) (cellDist_nonneg' _ _) (cellDist_comm' _ _) ?_
    rw [cellDist_comm' (c q) o]
    exact cellDist_triangle' o (c q) w
  have hsecond : ‖((T 0 0)⁻¹ * derivFirst T * ((T 0 0)⁻¹ * derivSecond T)).trace‖ ≤
      M ^ 4 * Real.exp (-(θ / 2 * cellDist o w)) * ((D : ℝ) * S) ^ 4 := by
    refine norm_trace_four_le _ _ _ (fun p q => Real.exp (-(θ / 2 * cellDist (c p) (c q))))
      (fun q => Real.exp (-(θ / 2 * cellDist (c q) o)))
      (fun v => Real.exp (-(θ / 2 * cellDist (c v) w))) (by positivity) (by positivity)
      (fun _ _ => (Real.exp_pos _).le) (fun _ => (Real.exp_pos _).le) (fun q => hsum (c q))
      (hsum o) (hsum w) fun p q u v => ?_
    refine pointwise_four_le hM hθ (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
      (norm_entry_le_of_local hi p q) (norm_entry_le_of_local hs q u)
      (norm_entry_le_of_local hi u v) (norm_entry_le_of_local ht v p)
      (cellDist_nonneg' _ _) (cellDist_nonneg' _ _) (cellDist_nonneg' _ _)
      (cellDist_comm' _ _) ?_
    have t1 := cellDist_triangle' o (c q) w
    have t2 := cellDist_triangle' (c q) (c p) w
    have t3 := cellDist_triangle' (c p) (c v) w
    have s1 := cellDist_comm' (c q) o
    have s2 := cellDist_comm' (c p) (c q)
    have s3 := cellDist_comm' (c v) (c p)
    linarith
  calc |(((T 0 0)⁻¹ * derivMixed T).trace -
        ((T 0 0)⁻¹ * derivFirst T * ((T 0 0)⁻¹ * derivSecond T)).trace).re|
      ≤ ‖((T 0 0)⁻¹ * derivMixed T).trace -
        ((T 0 0)⁻¹ * derivFirst T * ((T 0 0)⁻¹ * derivSecond T)).trace‖ :=
        Complex.abs_re_le_norm _
    _ ≤ ‖((T 0 0)⁻¹ * derivMixed T).trace‖ +
        ‖((T 0 0)⁻¹ * derivFirst T * ((T 0 0)⁻¹ * derivSecond T)).trace‖ := norm_sub_le _ _
    _ ≤ M ^ 2 * Real.exp (-(θ / 2 * cellDist o w)) * ((D : ℝ) * S) ^ 2 +
        M ^ 4 * Real.exp (-(θ / 2 * cellDist o w)) * ((D : ℝ) * S) ^ 4 :=
        add_le_add hfirst hsecond
    _ = _ := by ring
end YangMills.Construction.RunningCouplingSlope
end
