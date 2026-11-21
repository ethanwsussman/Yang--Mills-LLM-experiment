import YangMills.Construction.Lattice.HolomorphicMapsEqualNearRealPointsAreEqual
import YangMills.Construction.PeriodicLattice.TriplesOnFiniteBondSets
import Mathlib
open Filter Metric Set
open scoped Matrix.Norms.L2Operator Topology
noncomputable section
namespace YangMills.Construction.PeriodicLattice.RealIdentityPrinciple
def IsHolomorphicInEachVariableOn {N : ℕ} (O : Set (Coordinates.ComplexCoordinates N))
    (h : Coordinates.ComplexCoordinates N → ℂ) : Prop :=
  ∀ a ∈ O, ∀ j : Fin N,
    DifferentiableAt ℂ
      (fun ζ : ℂ => h (a + ζ • Coordinates.ComplexCoordinates.stdBasisVector j)) 0
theorem update_mem_ball_pi {N : ℕ} {c z : Coordinates.ComplexCoordinates N} {ρ : ℝ}
    (hz : z ∈ ball c ρ) (k : Fin N)
    {ζ : ℂ} (hζ : ζ ∈ ball (c k) ρ) : Function.update z k ζ ∈ ball c ρ := by
  have hρ : 0 < ρ := pos_of_mem_ball hz
  rw [ball_pi _ hρ] at hz ⊢
  intro i _
  by_cases hi : i = k
  · subst hi
    simpa using hζ
  · simpa [Function.update_of_ne hi] using hz i (mem_univ i)
theorem analyticOnNhd_update {N : ℕ} {O : Set (Coordinates.ComplexCoordinates N)}
    {h : Coordinates.ComplexCoordinates N → ℂ}
    (hh : IsHolomorphicInEachVariableOn O h) {c z : Coordinates.ComplexCoordinates N} {ρ : ℝ}
    (hO : ball c ρ ⊆ O) (hz : z ∈ ball c ρ) (k : Fin N) :
    AnalyticOnNhd ℂ (fun ζ : ℂ => h (Function.update z k ζ)) (ball (c k) ρ) := by
  refine DifferentiableOn.analyticOnNhd ?_ isOpen_ball
  intro ζ₀ hζ₀
  apply DifferentiableAt.differentiableWithinAt
  have h0 := hh _ (hO (update_mem_ball_pi hz k hζ₀)) k
  have heq : (fun ζ : ℂ => h (Function.update z k ζ)) =
      (fun ξ : ℂ => h (Function.update z k ζ₀ +
          ξ • Coordinates.ComplexCoordinates.stdBasisVector k)) ∘
        fun ζ : ℂ => ζ - ζ₀ := by
    funext ζ
    simp only [Function.comp]
    congr 1
    funext i
    by_cases hi : i = k
    · subst hi
      simp [Coordinates.ComplexCoordinates.stdBasisVector]
    · simp [Coordinates.ComplexCoordinates.stdBasisVector, Function.update_of_ne hi,
        Pi.single_eq_of_ne hi]
  rw [heq]
  refine DifferentiableAt.comp ζ₀ ?_ (by fun_prop)
  simpa using h0
theorem eq_zero_on_polydisc {N : ℕ} {O : Set (Coordinates.ComplexCoordinates N)}
    {h : Coordinates.ComplexCoordinates N → ℂ}
    (hh : IsHolomorphicInEachVariableOn O h) {c : Coordinates.ComplexCoordinates N} {ρ : ℝ}
    (hρ : 0 < ρ)
    (hO : ball c ρ ⊆ O) (A : Fin N → Set ℂ) (hA : ∀ j, A j ⊆ ball (c j) ρ)
    (hacc : ∀ j, ∃ᶠ ζ in 𝓝[≠] (c j), ζ ∈ A j)
    (hz : ∀ z ∈ ball c ρ, (∀ j, z j ∈ A j) → h z = 0) :
    ∀ z ∈ ball c ρ, h z = 0 := by
  have key : ∀ k : ℕ, k ≤ N → ∀ z ∈ ball c ρ,
      (∀ j : Fin N, k ≤ j.val → z j ∈ A j) → h z = 0 := by
    intro k
    induction k with
    | zero =>
      intro _ z hzb hzA
      exact hz z hzb fun j => hzA j (Nat.zero_le _)
    | succ k ih =>
      intro hk z hzb hzA
      let kk : Fin N := ⟨k, hk⟩
      have han := analyticOnNhd_update hh hO hzb kk
      have hfreq : ∃ᶠ ζ in 𝓝[≠] (c kk), h (Function.update z kk ζ) = 0 := by
        refine (hacc kk).mono fun ζ hζ => ?_
        refine ih (Nat.le_of_succ_le hk) _ (update_mem_ball_pi hzb kk (hA kk hζ))
          fun j hj => ?_
        by_cases hjk : j = kk
        · subst hjk
          simpa using hζ
        · have hne : j.val ≠ k := fun e => hjk (Fin.ext e)
          simpa [Function.update_of_ne hjk] using hzA j (by omega)
      have hzero := han.eqOn_zero_of_preconnected_of_frequently_eq_zero
        (convex_ball _ _).isPreconnected (mem_ball_self hρ) hfreq
      have hzk : z kk ∈ ball (c kk) ρ := by
        rw [ball_pi _ hρ] at hzb
        exact hzb kk (mem_univ _)
      simpa using hzero hzk
  intro z hzb
  exact key N le_rfl z hzb fun j hj => absurd j.isLt (by omega)
theorem frequently_real_mem_ball {x : ℂ} (hx : x.im = 0) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ᶠ ζ in 𝓝[≠] x, ζ ∈ {ζ : ℂ | ζ.im = 0 ∧ ζ ∈ ball x ρ} := by
  have ht' : Tendsto (fun s : ℝ => x + (s : ℂ)) (𝓝[≠] 0) (𝓝 x) := by
    have hc : Continuous fun s : ℝ => x + (s : ℂ) := by fun_prop
    have := hc.tendsto (0 : ℝ)
    simpa using this.mono_left nhdsWithin_le_nhds
  have ht : Tendsto (fun s : ℝ => x + (s : ℂ)) (𝓝[≠] 0) (𝓝[≠] x) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ht' (by
      filter_upwards [self_mem_nhdsWithin] with s hs
      simpa using hs)
  have he : ∀ᶠ s : ℝ in 𝓝[≠] 0,
      x + (s : ℂ) ∈ {ζ : ℂ | ζ.im = 0 ∧ ζ ∈ ball x ρ} := by
    filter_upwards [ht'.eventually (ball_mem_nhds x hρ)] with s hs
    exact ⟨by simp [hx], hs⟩
  exact ht.frequently he.frequently
theorem eq_zero_of_eq_zero_on_real_ball {N : ℕ} {O : Set (Coordinates.ComplexCoordinates N)}
    {h : Coordinates.ComplexCoordinates N → ℂ} (hopen : IsOpen O) (hconn : IsPreconnected O)
    (hh : IsHolomorphicInEachVariableOn O h) {w₀ : Coordinates.ComplexCoordinates N}
    (hw₀ : ∀ j, (w₀ j).im = 0)
    {ρ : ℝ} (hρ : 0 < ρ) (hball : ball w₀ ρ ⊆ O)
    (hreal : ∀ z ∈ ball w₀ ρ, (∀ j, (z j).im = 0) → h z = 0) : ∀ z ∈ O, h z = 0 := by
  have hstart : w₀ ∈ interior {w | h w = 0} := by
    have hzero := eq_zero_on_polydisc hh hρ hball
      (fun j => {ζ : ℂ | ζ.im = 0 ∧ ζ ∈ ball (w₀ j) ρ}) (fun _ ζ hζ => hζ.2)
      (fun j => frequently_real_mem_ball (hw₀ j) hρ)
      (fun z hz hzA => hreal z hz fun j => (hzA j).1)
    exact mem_interior.2 ⟨ball w₀ ρ, hzero, isOpen_ball, mem_ball_self hρ⟩
  have hclosed : closure (interior {w | h w = 0}) ∩ O ⊆ interior {w | h w = 0} := by
    rintro w ⟨hw, hwO⟩
    obtain ⟨ρ', hρ', hball⟩ := Metric.isOpen_iff.1 hopen w hwO
    have hρ : 0 < ρ' / 2 := by positivity
    obtain ⟨w', hw', hdist⟩ := Metric.mem_closure_iff.1 hw _ hρ
    obtain ⟨ε, hε, hεb⟩ := Metric.mem_nhds_iff.1 (mem_interior_iff_mem_nhds.1 hw')
    have hε' : 0 < min ε (ρ' / 2) := lt_min hε hρ
    have hsub : ball w' (ρ' / 2) ⊆ O := by
      intro x hx
      apply hball
      rw [mem_ball] at hx ⊢
      have := dist_triangle x w' w
      rw [dist_comm w' w] at this
      linarith
    have hzero := eq_zero_on_polydisc hh hρ hsub (fun j => ball (w' j) (min ε (ρ' / 2)))
      (fun j => ball_subset_ball (min_le_right _ _))
      (fun j => (eventually_nhdsWithin_of_eventually_nhds (ball_mem_nhds (w' j) hε')).frequently)
      (fun z _ hzA => by
        have hzb : z ∈ ball w' ε := by
          apply ball_subset_ball (min_le_left ε (ρ' / 2))
          rw [ball_pi _ hε']
          exact fun j _ => hzA j
        exact hεb hzb)
    refine mem_interior.2 ⟨ball w' (ρ' / 2), hzero, isOpen_ball, ?_⟩
    rw [mem_ball]
    exact hdist
  intro z hz
  have hz' : z ∈ interior {w | h w = 0} :=
    hconn.subset_of_closure_inter_subset isOpen_interior ⟨w₀, hball (mem_ball_self hρ), hstart⟩
      hclosed hz
  exact show z ∈ {w | h w = 0} from interior_subset hz'
theorem tupleOfCoords_pauli_apply {I : Type} [Fintype I] (ν : I ≃ Fin (Fintype.card I))
    (w : Coordinates.ComplexCoordinates (Fintype.card I * 3)) (i : I) :
    Matrices.GroupLieProduct.tupleOfCoords OneLoop.pauliBasis ν w i =
      ∑ c, w (finProdFinEquiv (ν i, c)) •
        (OneLoop.pauliBasis c : Matrices.ComplexMatrix2) := by
  simp only [Matrices.GroupLieProduct.tupleOfCoords,
    Coordinates.ComplexCoordinates.tracelessTuple]
theorem mem_supBall_iff {I : Type} [Fintype I] {r : ℝ} (hr : 0 < r)
    {A : I → Matrices.ComplexMatrix2} :
    A ∈ Matrices.GroupLieProduct.supBall I r ↔
      (∀ i, Matrices.ComplexMatrix2.fullTrace (A i) = 0) ∧
        ∀ i, Matrices.ComplexMatrix2.operatorNorm (A i) < r := by
  have hn : Matrices.GroupLieProduct.supNorm A < r ↔
      ∀ i, Matrices.ComplexMatrix2.operatorNorm (A i) < r := by
    constructor
    · intro h i
      exact lt_of_le_of_lt (le_ciSup (f := fun i => Matrices.ComplexMatrix2.operatorNorm (A i))
        (Set.finite_range _).bddAbove i) h
    · intro h
      rcases isEmpty_or_nonempty I with hI | hI
      · simpa [Matrices.GroupLieProduct.supNorm] using hr
      · obtain ⟨i, hi⟩ :=
          exists_eq_ciSup_of_finite (f := fun i => Matrices.ComplexMatrix2.operatorNorm (A i))
        rw [Matrices.GroupLieProduct.supNorm, ← hi]
        exact h i
  constructor
  · rintro ⟨hA, hnorm⟩
    exact ⟨hA, hn.1 hnorm⟩
  · rintro ⟨hA, hnorm⟩
    exact ⟨hA, hn.2 hnorm⟩
theorem pauliBasis_mem_hermitianTraceless (c : Fin 3) :
    ((OneLoop.pauliBasis c : Matrices.ComplexMatrix2.traceless) : Matrices.ComplexMatrix2) ∈
      Matrices.ComplexMatrix2.hermitianTraceless := by
  obtain ⟨h0, h1, h2⟩ := OneLoop.pauliBasis_coe_eq
  have e1 : OneLoop.pauliX = OneLoop.pauliX.conjTranspose := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [OneLoop.pauliX, Matrix.conjTranspose_apply]
  have e2 : OneLoop.pauliY = OneLoop.pauliY.conjTranspose := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [OneLoop.pauliY, Matrix.conjTranspose_apply]
  have e3 : OneLoop.pauliZ = OneLoop.pauliZ.conjTranspose := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [OneLoop.pauliZ, Matrix.conjTranspose_apply]
  have hall : ∀ c : Fin 3,
      ((OneLoop.pauliBasis c : Matrices.ComplexMatrix2.traceless) : Matrices.ComplexMatrix2) =
        ((OneLoop.pauliBasis c : Matrices.ComplexMatrix2.traceless) :
          Matrices.ComplexMatrix2).conjTranspose := by
    intro c
    match c with
    | 0 => rw [h0]; exact e1
    | 1 => rw [h1]; exact e2
    | 2 => rw [h2]; exact e3
  exact ⟨hall c, (OneLoop.pauliBasis c).2⟩
theorem sum_real_smul_pauli_mem {x : Fin 3 → ℂ} (hx : ∀ c, (x c).im = 0) :
    ∑ c, x c • (OneLoop.pauliBasis c : Matrices.ComplexMatrix2) ∈
      Matrices.ComplexMatrix2.hermitianTraceless := by
  refine Submodule.sum_mem _ fun c _ => ?_
  have heq : x c • (OneLoop.pauliBasis c : Matrices.ComplexMatrix2) =
      (x c).re • (OneLoop.pauliBasis c : Matrices.ComplexMatrix2) := by
    ext i j
    have hc : x c = ((x c).re : ℂ) := Complex.ext (by simp) (by simp [hx c])
    simp only [Matrix.smul_apply, smul_eq_mul, Complex.real_smul]
    rw [← hc]
  rw [heq]
  exact Submodule.smul_mem _ _ (pauliBasis_mem_hermitianTraceless c)
theorem sum_repr_smul_pauli (X : Matrices.ComplexMatrix2.traceless) :
    ∑ c, OneLoop.pauliBasis.repr X c • (OneLoop.pauliBasis c : Matrices.ComplexMatrix2) =
      (X : Matrices.ComplexMatrix2) := by
  calc ∑ c, OneLoop.pauliBasis.repr X c • (OneLoop.pauliBasis c : Matrices.ComplexMatrix2)
      = ((∑ c, OneLoop.pauliBasis.repr X c • OneLoop.pauliBasis c :
          Matrices.ComplexMatrix2.traceless) : Matrices.ComplexMatrix2) := by
        simp only [AddSubmonoidClass.coe_finsetSum, Submodule.coe_smul]
    _ = (X : Matrices.ComplexMatrix2) := by rw [Module.Basis.sum_repr]
theorem pauli_repr_im_eq_zero {X : Matrices.ComplexMatrix2.traceless}
    (hX : (X : Matrices.ComplexMatrix2).conjTranspose = X) (c : Fin 3) :
    (OneLoop.pauliBasis.repr X c).im = 0 := by
  have h00 : (starRingEnd ℂ) ((X : Matrices.ComplexMatrix2) 0 0) =
      (X : Matrices.ComplexMatrix2) 0 0 := by
    simpa [Matrix.conjTranspose_apply] using congrFun (congrFun hX 0) 0
  have h01 : (starRingEnd ℂ) ((X : Matrices.ComplexMatrix2) 1 0) =
      (X : Matrices.ComplexMatrix2) 0 1 := by
    simpa [Matrix.conjTranspose_apply] using congrFun (congrFun hX 0) 1
  have h10 : (starRingEnd ℂ) ((X : Matrices.ComplexMatrix2) 0 1) =
      (X : Matrices.ComplexMatrix2) 1 0 := by
    simpa [Matrix.conjTranspose_apply] using congrFun (congrFun hX 1) 0
  have hrepr : OneLoop.pauliBasis.repr X c = OneLoop.pauliCoordinateEquiv X c := by
    simp [OneLoop.pauliBasis]
  rw [hrepr]
  apply Complex.conj_eq_iff_im.1
  fin_cases c
  · simp [OneLoop.pauliCoordinateEquiv, h01, h10, add_comm, map_ofNat]
  · have hI : Complex.I ≠ 0 := Complex.I_ne_zero
    simp [OneLoop.pauliCoordinateEquiv, h01, h10, map_ofNat]
    field_simp
    all_goals ring
  · simpa [OneLoop.pauliCoordinateEquiv] using h00
theorem continuous_tupleOfCoords {I : Type} [Fintype I] (ν : I ≃ Fin (Fintype.card I)) :
    Continuous (Matrices.GroupLieProduct.tupleOfCoords OneLoop.pauliBasis ν) := by
  refine continuous_pi fun i => ?_
  simp only [tupleOfCoords_pauli_apply]
  exact continuous_finsetSum _ fun c _ => (continuous_apply _).smul continuous_const
theorem tupleOfCoords_mem_selfAdjointFunctions {I : Type} [Fintype I]
    (ν : I ≃ Fin (Fintype.card I))
    {z : Coordinates.ComplexCoordinates (Fintype.card I * 3)} (hz : ∀ j, (z j).im = 0) :
    Matrices.GroupLieProduct.tupleOfCoords OneLoop.pauliBasis ν z ∈
      selfAdjointFunctions I := by
  have hsu : ∀ i, Matrices.GroupLieProduct.tupleOfCoords OneLoop.pauliBasis ν z i ∈
      Matrices.ComplexMatrix2.hermitianTraceless := by
    intro i
    rw [tupleOfCoords_pauli_apply]
    exact sum_real_smul_pauli_mem fun c => hz _
  refine ⟨fun i => (hsu i).2, ?_⟩
  funext i
  exact ((hsu i).1).symm
theorem statement_holds : Statement := by
  intro ι τ _ _ r f g S hf hg hS hne hopenS hfg a ha
  classical
  have hr : 0 < r := lt_of_le_of_lt
    (Real.iSup_nonneg fun i => norm_nonneg (a i)) ha.2
  let ν : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  let ν' : τ ≃ Fin (Fintype.card τ) := Fintype.equivFin τ
  let tup := Matrices.GroupLieProduct.tupleOfCoords OneLoop.pauliBasis ν
  let e := Matrices.GroupLieProduct.matrixPiEquiv ν'
  let O : Set (Coordinates.ComplexCoordinates (Fintype.card ι * 3)) :=
    tup ⁻¹' Matrices.GroupLieProduct.supBall ι r
  have hF := (hf OneLoop.pauliBasis ν').2 ν
  have hG := (hg OneLoop.pauliBasis ν').2 ν
  have hopen : IsOpen O := hF.1
  have hconvex : Convex ℝ O := by
    intro w₁ h₁ w₂ h₂ s t hs ht hst
    have hlin : ∀ i, tup (s • w₁ + t • w₂) i = (s : ℂ) • tup w₁ i + (t : ℂ) • tup w₂ i := by
      intro i
      simp only [tup, tupleOfCoords_pauli_apply, Finset.smul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun c _ => ?_
      simp [add_smul, mul_smul]
    obtain ⟨t₁, n₁⟩ := (mem_supBall_iff hr).1 h₁
    obtain ⟨t₂, n₂⟩ := (mem_supBall_iff hr).1 h₂
    refine (mem_supBall_iff hr).2 ⟨fun i => ?_, fun i => ?_⟩
    · rw [hlin i]
      simp only [Matrices.ComplexMatrix2.fullTrace, Matrix.trace_add, Matrix.trace_smul]
        at t₁ t₂ ⊢
      rw [t₁, t₂]
      simp
    · rw [hlin i]
      have hb := convex_Iio r (n₁ i) (n₂ i) hs ht hst
      refine lt_of_le_of_lt ((norm_add_le _ _).trans ?_) hb
      simp [norm_smul, abs_of_nonneg hs, abs_of_nonneg ht]
  have hcoord : ∀ A : ι → Matrices.ComplexMatrix2,
      (hA : ∀ i, A i ∈ Matrices.ComplexMatrix2.traceless) →
      ∃ w : Coordinates.ComplexCoordinates (Fintype.card ι * 3), tup w = A ∧
        ((∀ i, (A i).conjTranspose = A i) → ∀ j, (w j).im = 0) := by
    intro A hA
    refine ⟨fun k => OneLoop.pauliBasis.repr
      ⟨A (ν.symm (finProdFinEquiv.symm k).1), hA _⟩ (finProdFinEquiv.symm k).2, ?_, ?_⟩
    · funext i
      simp only [tup, tupleOfCoords_pauli_apply, Equiv.symm_apply_apply]
      simpa using sum_repr_smul_pauli ⟨A i, hA i⟩
    · intro hher j
      exact pauli_repr_im_eq_zero (hher _) _
  obtain ⟨a₀, ha₀⟩ := hne
  obtain ⟨U, hU, rfl⟩ := hopenS
  obtain ⟨hball₀, hreal₀⟩ := hS ha₀
  obtain ⟨w₀, hw₀, hw₀r⟩ := hcoord a₀ hball₀.1
  have hw₀real : ∀ j, (w₀ j).im = 0 := hw₀r fun i => congrFun hreal₀.2 i
  have hnbhd : IsOpen (O ∩ tup ⁻¹' U) :=
    hopen.inter (hU.preimage (continuous_tupleOfCoords ν))
  have hw₀mem : w₀ ∈ O ∩ tup ⁻¹' U := by
    refine ⟨?_, ?_⟩
    · show tup w₀ ∈ Matrices.GroupLieProduct.supBall ι r
      rw [hw₀]
      exact hball₀
    · show tup w₀ ∈ U
      rw [hw₀]
      exact ha₀.1
  obtain ⟨ρ, hρ, hρb⟩ := Metric.isOpen_iff.1 hnbhd w₀ hw₀mem
  have hzero : ∀ k, ∀ w ∈ O, e (f (tup w)) k - e (g (tup w)) k = 0 := by
    intro k
    refine eq_zero_of_eq_zero_on_real_ball
      (h := fun w => e (f (tup w)) k - e (g (tup w)) k)
      hopen hconvex.isPreconnected ?_ hw₀real hρ (fun x hx => (hρb hx).1) ?_
    · intro w hw j
      have h1 := (hF.2.2 w hw j).self_of_nhds
      have h2 := (hG.2.2 w hw j).self_of_nhds
      exact (differentiableAt_pi.1 h1 k).sub (differentiableAt_pi.1 h2 k)
    · intro z hz hzr
      have hzS : tup z ∈ U ∩ selfAdjointFunctions ι :=
        ⟨(hρb hz).2, tupleOfCoords_mem_selfAdjointFunctions ν hzr⟩
      simp only [hfg hzS, sub_self]
  obtain ⟨w, hw, -⟩ := hcoord a ha.1
  have hwO : w ∈ O := by
    show tup w ∈ Matrices.GroupLieProduct.supBall ι r
    rw [hw]
    exact ha
  apply e.injective
  funext k
  have := hzero k w hwO
  rw [hw] at this
  exact sub_eq_zero.1 this
end YangMills.Construction.PeriodicLattice.RealIdentityPrinciple
