import YangMills.Construction.Torus.GeometryAndFreeKernelOfATestPairProof
import YangMills.Construction.Torus.PointsAndTuplesOfTorusOrFourSpace
import YangMills.Construction.Lattice.CovarianceUnderTheLatticeIsometries
import YangMills.Construction.Lattice.CubesOfTwoStandardPartitionsProof
import YangMills.Construction.Lattice.IsometriesOfALevelAndTheirCubes
import YangMills.Construction.Lattice.SupBallCentre
import YangMills.Construction.LinearAlgebra.NormIsometryOfEuclideanFourSpaceIsAffine
import Mathlib
set_option autoImplicit false
open Set Filter Topology YangMills.Construction.TorusMetric
noncomputable section
namespace YangMills.Construction.PeriodicLattice.LevelIsometryProof
structure IsMonotoneCoordNorm (N : Seminorm ℝ (Fin 4 → ℝ)) : Prop where
  monotone_abs : ∀ a b : Fin 4 → ℝ, (∀ μ, |a μ| ≤ |b μ|) → N a ≤ N b
  sup_le : ∀ a : Fin 4 → ℝ, ‖a‖ ≤ N a
  le_four_sup : ∀ a : Fin 4 → ℝ, N a ≤ 4 * ‖a‖
def torusNormOf {S : ℝ} (N : Seminorm ℝ (Fin 4 → ℝ)) (x : Torus4 S) : ℝ :=
  sInf ((fun v => N v) '' (torusProj S ⁻¹' {x}))
variable {S : ℝ} {N : Seminorm ℝ (Fin 4 → ℝ)}
theorem torusProj_sub (a b : Fin 4 → ℝ) : torusProj S (a - b) = torusProj S a - torusProj S b := by apply _root_.YangMills.Construction.TestPairs.torusProj_map_sub <;> assumption
theorem exists_minimal_lift (x : Torus4 S) : ∃ b, torusProj S b = x ∧ ∀ μ, |b μ| = ‖x μ‖ := by apply _root_.YangMills.Construction.PeriodicLattice.CubeRefinement.exists_torusProj_eq_abs_eq_norm <;> assumption
theorem torusNormOf_eq_of_minimal (hN : IsMonotoneCoordNorm N) {x : Torus4 S} {b : Fin 4 → ℝ}
    (hb : torusProj S b = x) (hb' : ∀ μ, |b μ| = ‖x μ‖) : torusNormOf N x = N b := by
  apply le_antisymm
  · refine csInf_le ⟨0, ?_⟩ ⟨b, hb, rfl⟩
    rintro _ ⟨w, -, rfl⟩
    exact apply_nonneg N w
  · refine le_csInf ⟨_, b, hb, rfl⟩ ?_
    rintro _ ⟨w, hw, rfl⟩
    have hw' : torusProj S w = x := hw
    refine hN.monotone_abs _ _ fun μ => ?_
    rw [hb' μ, ← hw']
    exact addCircle_norm_coe_le_abs _
theorem torusNormOf_torusProj (hN : IsMonotoneCoordNorm N) (hS : 0 < S) {v : Fin 4 → ℝ}
    (h : ∀ μ, |v μ| ≤ S / 2) : torusNormOf N (torusProj S v) = N v := by
  refine torusNormOf_eq_of_minimal hN rfl fun μ => ?_
  have := (AddCircle.norm_coe_eq_abs_iff S hS.ne' (x := v μ)).2
    (by rw [abs_of_pos hS]; exact h μ)
  exact this.symm
theorem norm_le_torusNormOf (hN : IsMonotoneCoordNorm N) (x : Torus4 S) :
    ‖x‖ ≤ torusNormOf N x := by
  obtain ⟨b, hb, hb'⟩ := exists_minimal_lift x
  rw [torusNormOf_eq_of_minimal hN hb hb']
  refine le_trans ?_ (hN.sup_le b)
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun μ => ?_
  rw [← hb' μ]
  exact norm_le_pi_norm b μ
theorem torusNormOf_le_four_norm (hN : IsMonotoneCoordNorm N) (x : Torus4 S) :
    torusNormOf N x ≤ 4 * ‖x‖ := by
  obtain ⟨b, hb, hb'⟩ := exists_minimal_lift x
  rw [torusNormOf_eq_of_minimal hN hb hb']
  refine (hN.le_four_sup b).trans ?_
  gcongr
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun μ => ?_
  have := hb' μ
  rw [Real.norm_eq_abs, this]
  exact norm_le_pi_norm x μ
def PreservesTorusNorm (N : Seminorm ℝ (Fin 4 → ℝ)) (f : Torus4 S → Torus4 S) : Prop :=
  ∀ x y, torusNormOf N (f x - f y) = torusNormOf N (x - y)
theorem PreservesTorusNorm.lipschitzWith (hN : IsMonotoneCoordNorm N) {f : Torus4 S → Torus4 S}
    (hf : PreservesTorusNorm N f) : LipschitzWith 4 f := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [dist_eq_norm, dist_eq_norm]
  calc ‖f x - f y‖ ≤ torusNormOf N (f x - f y) := norm_le_torusNormOf hN _
    _ = torusNormOf N (x - y) := hf x y
    _ ≤ 4 * ‖x - y‖ := torusNormOf_le_four_norm hN _
    _ = _ := by norm_num
theorem PreservesTorusNorm.injective (hN : IsMonotoneCoordNorm N) {f : Torus4 S → Torus4 S}
    (hf : PreservesTorusNorm N f) : Function.Injective f := by
  intro x y h
  have h1 := norm_le_torusNormOf hN (x - y)
  rw [← hf x y, h, sub_self] at h1
  have h2 := torusNormOf_le_four_norm hN (0 : Torus4 S)
  rw [norm_zero, mul_zero] at h2
  exact sub_eq_zero.mp (norm_le_zero_iff.mp (h1.trans h2))
theorem PreservesTorusNorm.iterate_apply {f : Torus4 S → Torus4 S} (hf : PreservesTorusNorm N f)
    (n : ℕ) (x y : Torus4 S) : torusNormOf N (f^[n] x - f^[n] y) = torusNormOf N (x - y) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', hf, ih]
theorem PreservesTorusNorm.surjective [Fact (0 < S)] (hN : IsMonotoneCoordNorm N)
    {f : Torus4 S → Torus4 S} (hf : PreservesTorusNorm N f) : Function.Surjective f := by
  intro x
  by_contra hx
  have hcont := (hf.lipschitzWith hN).continuous
  have hclosed : IsClosed (range f) := (isCompact_range hcont).isClosed
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hclosed.isOpen_compl x hx
  obtain ⟨a, φ, hφ, hlim⟩ := CompactSpace.tendsto_subseq (fun n => f^[n] x)
  have hcau := hlim.cauchySeq
  obtain ⟨n₀, hn₀⟩ := Metric.cauchySeq_iff.1 hcau (δ / 4) (by positivity)
  have hlt : φ n₀ < φ (n₀ + 1) := hφ (Nat.lt_succ_self _)
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_lt hlt
  have hd := hn₀ n₀ le_rfl (n₀ + 1) (by omega)
  simp only [Function.comp_apply] at hd
  rw [hk, dist_eq_norm] at hd
  have hit : f^[φ n₀ + k + 1] x = f^[φ n₀] (f^[k + 1] x) :=
    Function.iterate_add_apply f (φ n₀) (k + 1) x
  rw [hit] at hd
  have h1 : ‖x - f^[k + 1] x‖ < δ := by
    calc ‖x - f^[k + 1] x‖ ≤ torusNormOf N (x - f^[k + 1] x) := norm_le_torusNormOf hN _
      _ = torusNormOf N (f^[φ n₀] x - f^[φ n₀] (f^[k + 1] x)) := (hf.iterate_apply _ _ _).symm
      _ ≤ 4 * ‖f^[φ n₀] x - f^[φ n₀] (f^[k + 1] x)‖ := torusNormOf_le_four_norm hN _
      _ < δ := by linarith
  have h2 : f^[k + 1] x ∈ Metric.ball x δ := by
    rw [Metric.mem_ball, dist_comm, dist_eq_norm]
    exact h1
  refine hball h2 ?_
  rw [Function.iterate_succ_apply']
  exact mem_range_self _
theorem IsMonotoneCoordNorm.continuous (hN : IsMonotoneCoordNorm N) : Continuous fun v => N v := by
  refine (LipschitzWith.of_dist_le_mul (K := 4) fun a b => ?_).continuous
  rw [Real.dist_eq, dist_eq_norm]
  exact (abs_sub_map_le_sub N a b).trans (by simpa using hN.le_four_sup _)
theorem continuous_torusProj : Continuous (torusProj S) := by apply _root_.YangMills.Construction.TestPairs.continuous_torusProj <;> assumption
theorem exists_continuous_lift {f : Torus4 S → Torus4 S} (hf : Continuous f) (x₀ e : Fin 4 → ℝ)
    (he : torusProj S e = f (torusProj S x₀)) :
    ∃ F : (Fin 4 → ℝ) → Fin 4 → ℝ, Continuous F ∧ F x₀ = e ∧
      ∀ x, torusProj S (F x) = f (torusProj S x) := by
  have key : ∀ μ, ∃ F : C(Fin 4 → ℝ, ℝ), F x₀ = e μ ∧
      ∀ x, ((F x : ℝ) : AddCircle S) = f (torusProj S x) μ := by
    intro μ
    let g : C(Fin 4 → ℝ, AddCircle S) :=
      ⟨fun x => f (torusProj S x) μ, (continuous_apply μ).comp (hf.comp continuous_torusProj)⟩
    obtain ⟨F, ⟨h0, h1⟩, -⟩ := (AddCircle.isCoveringMap_coe S).existsUnique_continuousMap_lifts
      g x₀ (e μ) (congrFun he μ)
    exact ⟨F, h0, fun x => congrFun h1 x⟩
  choose F h0 h1 using key
  exact ⟨fun x μ => F μ x, continuous_pi fun μ => (F μ).continuous, funext h0,
    fun x => funext fun μ => h1 μ x⟩
theorem continuous_lift_unique {F G : (Fin 4 → ℝ) → Fin 4 → ℝ} (hF : Continuous F)
    (hG : Continuous G) (h : ∀ x, torusProj S (F x) = torusProj S (G x)) (a : Fin 4 → ℝ)
    (ha : F a = G a) : F = G := by
  funext x μ
  have := (AddCircle.isCoveringMap_coe S).eq_of_comp_eq (g₁ := fun x => F x μ)
    (g₂ := fun x => G x μ) ((continuous_apply μ).comp hF) ((continuous_apply μ).comp hG)
    (funext fun x => congrFun (h x) μ) a (congrFun ha μ)
  exact congrFun this x
section LiftBounds
variable {f : Torus4 S → Torus4 S} {F : (Fin 4 → ℝ) → Fin 4 → ℝ}
theorem lift_locally_isometric (hN : IsMonotoneCoordNorm N) (hS : 0 < S)
    (hf : PreservesTorusNorm N f) (hc : Continuous F)
    (hl : ∀ x, torusProj S (F x) = f (torusProj S x)) (x : Fin 4 → ℝ) :
    ∃ ε > 0, ∀ u v, ‖u - x‖ < ε → ‖v - x‖ < ε → N (F u - F v) = N (u - v) := by
  obtain ⟨δ, hδ, h⟩ := Metric.continuous_iff.1 hc x (S / 8) (by positivity)
  refine ⟨min δ (S / 8), by positivity, fun u v hu hv => ?_⟩
  have hu1 : ‖F u - F x‖ < S / 8 := by
    simpa [dist_eq_norm] using h u (by simpa [dist_eq_norm] using lt_of_lt_of_le hu (min_le_left _ _))
  have hv1 : ‖F v - F x‖ < S / 8 := by
    simpa [dist_eq_norm] using h v (by simpa [dist_eq_norm] using lt_of_lt_of_le hv (min_le_left _ _))
  have hu2 : ‖u - x‖ < S / 8 := lt_of_lt_of_le hu (min_le_right _ _)
  have hv2 : ‖v - x‖ < S / 8 := lt_of_lt_of_le hv (min_le_right _ _)
  have hsmall : ∀ a b c : Fin 4 → ℝ, ‖a - c‖ < S / 8 → ‖b - c‖ < S / 8 →
      ∀ μ, |(a - b) μ| ≤ S / 2 := by
    intro a b c ha hb μ
    have h1 := norm_le_pi_norm (a - b) μ
    have h2 : ‖a - b‖ ≤ ‖a - c‖ + ‖b - c‖ := by
      have : a - b = (a - c) - (b - c) := by abel
      rw [this]
      exact norm_sub_le _ _
    rw [Real.norm_eq_abs] at h1
    linarith
  rw [← torusNormOf_torusProj hN hS (hsmall _ _ _ hu1 hv1),
    ← torusNormOf_torusProj hN hS (hsmall _ _ _ hu2 hv2),
    torusProj_sub, torusProj_sub, hl, hl, hf]
theorem lift_nonexpanding (hN : IsMonotoneCoordNorm N) (hS : 0 < S) (hf : PreservesTorusNorm N f)
    (hc : Continuous F) (hl : ∀ x, torusProj S (F x) = f (torusProj S x)) (x y : Fin 4 → ℝ) :
    N (F y - F x) ≤ N (y - x) := by
  let γ : ℝ → Fin 4 → ℝ := fun t => x + t • (y - x)
  have hγ : Continuous γ := by fun_prop
  let s : Set ℝ := {t | N (F (γ t) - F x) ≤ t * N (y - x)}
  have hclosed : IsClosed s :=
    isClosed_le (hN.continuous.comp ((hc.comp hγ).sub continuous_const))
      (continuous_id.mul continuous_const)
  have h0 : (0 : ℝ) ∈ s := by simp [s, γ]
  have hsub : Icc (0 : ℝ) 1 ⊆ s := by
    refine (hclosed.inter isClosed_Icc).Icc_subset_of_forall_exists_gt h0 ?_
    rintro t ⟨ht, -⟩ t' ht'
    obtain ⟨ε, hε, hloc⟩ := lift_locally_isometric hN hS hf hc hl (γ t)
    set c : ℝ := ε / (‖y - x‖ + 1) with hcdef
    have hcpos : 0 < c := by positivity
    have hcε : c * ‖y - x‖ < ε := by
      have : c * (‖y - x‖ + 1) = ε := by rw [hcdef]; field_simp
      nlinarith
    set t₁ : ℝ := min t' (t + c) with ht₁
    have ht₁t : t < t₁ := lt_min ht' (by linarith)
    have ht₁c : t₁ - t ≤ c := by
      have := min_le_right t' (t + c)
      linarith
    have hd : γ t₁ - γ t = (t₁ - t) • (y - x) := by
      simp only [γ, sub_smul]
      abel
    have hnorm : ‖γ t₁ - γ t‖ < ε := by
      rw [hd, norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith)]
      calc (t₁ - t) * ‖y - x‖ ≤ c * ‖y - x‖ := by gcongr
        _ < ε := hcε
    refine ⟨t₁, ?_, ht₁t, min_le_left _ _⟩
    have hstep := hloc (γ t₁) (γ t) hnorm (by simpa using hε)
    have htri : N (F (γ t₁) - F x) ≤ N (F (γ t₁) - F (γ t)) + N (F (γ t) - F x) := by
      have : F (γ t₁) - F x = (F (γ t₁) - F (γ t)) + (F (γ t) - F x) := by abel
      rw [this]
      exact map_add_le_add N _ _
    have hst : t * N (y - x) ≥ N (F (γ t) - F x) := ht
    have hval : N (γ t₁ - γ t) = (t₁ - t) * N (y - x) := by
      rw [hd, map_smul_eq_mul, Real.norm_eq_abs, abs_of_pos (by linarith)]
    show N (F (γ t₁) - F x) ≤ t₁ * N (y - x)
    rw [hstep, hval] at htri
    nlinarith
  have h1 : (1 : ℝ) ∈ s := hsub ⟨zero_le_one, le_rfl⟩
  have hγ1 : γ 1 = y := by simp [γ]
  have : N (F (γ 1) - F x) ≤ 1 * N (y - x) := h1
  rwa [hγ1, one_mul] at this
end LiftBounds
theorem exists_affine_lift [Fact (0 < S)]
    (mazur : LinearAlgebra.NormIsometry.BijectiveNormIsometryIsAffine)
    (hN : IsMonotoneCoordNorm N) {f : Torus4 S → Torus4 S} (hf : PreservesTorusNorm N f) :
    ∃ (A : (Fin 4 → ℝ) →ₗ[ℝ] (Fin 4 → ℝ)) (v : Fin 4 → ℝ), Function.Bijective A ∧
      (∀ x, N (A x) = N x) ∧ (∀ x, f (torusProj S x) = torusProj S (A x + v)) ∧
      ∀ ν μ, ∃ z : ℤ, A (Pi.single ν 1) μ = z := by
  have hS : 0 < S := Fact.out
  have hcont := (hf.lipschitzWith hN).continuous
  let e : Torus4 S ≃ Torus4 S :=
    Equiv.ofBijective f ⟨hf.injective hN, hf.surjective hN⟩
  have hfe : ∀ a, f (e.symm a) = a := fun a => e.apply_symm_apply a
  have hef : ∀ a, e.symm (f a) = a := fun a => e.symm_apply_apply a
  have hg : PreservesTorusNorm N e.symm := fun a b => by
    have := hf (e.symm a) (e.symm b)
    rw [hfe, hfe] at this
    exact this.symm
  have hgc := (hg.lipschitzWith hN).continuous
  obtain ⟨e0, he0, -⟩ := exists_minimal_lift (f (torusProj S 0))
  obtain ⟨F, hFc, hF0, hF⟩ := exists_continuous_lift hcont 0 e0 he0
  obtain ⟨G, hGc, hG0, hG⟩ := exists_continuous_lift hgc e0 0 (by rw [he0, hef])
  have hGF : ∀ x, G (F x) = x := congrFun (continuous_lift_unique (S := S) (hGc.comp hFc)
    continuous_id (fun x => by simp only [hG, hF, hef]) 0
    (by simp only [hF0, hG0]))
  have hFG : ∀ x, F (G x) = x := congrFun (continuous_lift_unique (S := S) (hFc.comp hGc)
    continuous_id (fun x => by simp only [hG, hF, hfe]) e0
    (by simp only [hF0, hG0]))
  have hiso : ∀ x y, N (F x - F y) = N (x - y) := fun x y => by
    refine le_antisymm (lift_nonexpanding hN hS hf hFc hF y x) ?_
    have := lift_nonexpanding hN hS hg hGc hG (F y) (F x)
    rwa [hGF, hGF] at this
  have hFinj : Function.Injective F := fun a b h => by rw [← hGF a, h, hGF]
  obtain ⟨g, hgF⟩ := mazur N (fun x hx => by
    have := hN.sup_le x
    rw [hx] at this
    exact norm_le_zero_iff.mp this) F
    ⟨hFinj, fun y => ⟨G y, hFG y⟩⟩ hiso
  have hdec : ∀ x, F x = g.linear x + F 0 := fun x => by
    rw [← hgF]
    simpa using congrFun g.decomp x
  refine ⟨g.linear, F 0, ⟨fun a b h => hFinj (by rw [hdec a, hdec b, h]), fun y =>
    ⟨G (y + F 0), ?_⟩⟩, fun x => ?_, fun x => ?_, fun ν μ => ?_⟩
  · have := hdec (G (y + F 0))
    rw [hFG] at this
    exact (add_right_cancel this).symm
  · have h1 := hiso x 0
    rw [hdec x, add_sub_cancel_right, sub_zero] at h1
    exact h1
  · rw [← hdec, hF]
  · have hw : torusProj S (S • (Pi.single ν 1 : Fin 4 → ℝ)) = torusProj S 0 := by
      funext κ
      have : ((S * (Pi.single ν (1 : ℝ) : Fin 4 → ℝ) κ : ℝ) : AddCircle S) = 0 := by
        by_cases h : κ = ν
        · subst h
          simp
        · simp [Pi.single_eq_of_ne h]
      simpa [torusProj] using this
    have h1 : torusProj S (F (S • (Pi.single ν 1 : Fin 4 → ℝ))) = torusProj S (F 0) := by
      rw [hF, hF, hw]
    have h2 : ((g.linear (S • (Pi.single ν 1 : Fin 4 → ℝ)) μ : ℝ) : AddCircle S) = 0 := by
      have h3 := congrFun h1 μ
      rw [hdec (S • (Pi.single ν 1 : Fin 4 → ℝ))] at h3
      simpa [torusProj] using h3
    obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff S).1 h2
    refine ⟨n, ?_⟩
    rw [map_smul, Pi.smul_apply, smul_eq_mul, zsmul_eq_mul] at hn
    exact (mul_right_cancel₀ hS.ne' (by rw [hn]; ring)).symm
theorem eq_signed_basis_of_sum_abs_le_one {z : Fin 4 → ℤ} (h : ∑ μ, |z μ| ≤ 1) (h0 : z ≠ 0) :
    ∃ (ν : Fin 4) (ε : ℤˣ), ∀ μ, z μ = if μ = ν then (ε : ℤ) else 0 := by
  obtain ⟨ν, hν⟩ := Function.ne_iff.1 h0
  have hν' : z ν ≠ 0 := hν
  have habs : 1 ≤ |z ν| := Int.one_le_abs hν'
  have hsplit := Finset.add_sum_erase Finset.univ (fun μ => |z μ|) (Finset.mem_univ ν)
  have hrest : ∑ μ ∈ Finset.univ.erase ν, |z μ| ≤ 0 := by linarith
  have hz1 : |z ν| = 1 := by
    have : 0 ≤ ∑ μ ∈ Finset.univ.erase ν, |z μ| :=
      Finset.sum_nonneg fun _ _ => abs_nonneg _
    linarith
  have hunit : IsUnit (z ν) := Int.isUnit_iff_abs_eq.2 hz1
  obtain ⟨ε, hε⟩ := hunit
  refine ⟨ν, ε, fun μ => ?_⟩
  by_cases hμ : μ = ν
  · subst hμ
    simp [hε]
  · rw [if_neg hμ]
    have h1 : |z μ| ≤ ∑ κ ∈ Finset.univ.erase ν, |z κ| :=
      Finset.single_le_sum (f := fun κ => |z κ|) (fun _ _ => abs_nonneg _)
        (Finset.mem_erase.2 ⟨hμ, Finset.mem_univ μ⟩)
    exact abs_eq_zero.mp (le_antisymm (h1.trans hrest) (abs_nonneg _))
theorem linearMap_apply_eq_sum (A : (Fin 4 → ℝ) →ₗ[ℝ] (Fin 4 → ℝ)) {a : Fin 4 → Fin 4 → ℤ}
    (ha : ∀ ν μ, A (Pi.single ν 1) μ = a ν μ) (x : Fin 4 → ℝ) (μ : Fin 4) :
    A x μ = ∑ ν, x ν * a ν μ := by
  have hx : x = ∑ ν, x ν • (Pi.single ν (1 : ℝ) : Fin 4 → ℝ) := by
    funext κ
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hx]
  simp [map_sum, Finset.sum_apply, ha]
theorem exists_signedFrame_of_columns {A : (Fin 4 → ℝ) →ₗ[ℝ] (Fin 4 → ℝ)}
    (hinj : Function.Injective A) {a : Fin 4 → Fin 4 → ℤ}
    (ha : ∀ ν μ, A (Pi.single ν 1) μ = a ν μ) (hsum : ∀ ν, ∑ μ, |a ν μ| ≤ 1) :
    ∃ r : SignedFrame, ∀ x, A x = r.actOnVector x := by
  have hne : ∀ ν, a ν ≠ 0 := fun ν h => by
    have h1 : A (Pi.single ν 1) = A 0 := by
      funext μ
      simp [ha, h]
    have h2 := congrFun (hinj h1) ν
    simp at h2
  choose τ ε h using fun ν => eq_signed_basis_of_sum_abs_le_one (hsum ν) (hne ν)
  have hτ : Function.Injective τ := by
    intro ν ν' hνν
    by_contra hne'
    have h1 : A (((ε ν' : ℤ) : ℝ) • Pi.single ν 1 - ((ε ν : ℤ) : ℝ) • Pi.single ν' 1) = A 0 := by
      funext μ
      simp only [map_sub, map_smul, Pi.sub_apply, Pi.smul_apply, ha, h, smul_eq_mul, hνν, map_zero,
        Pi.zero_apply]
      split_ifs <;> simp [mul_comm]
    have h2 := congrFun (hinj h1) ν
    simp [Pi.single_eq_of_ne hne'] at h2
  let e : Fin 4 ≃ Fin 4 := Equiv.ofBijective τ (Finite.injective_iff_bijective.1 hτ)
  have he : ∀ μ, τ (e.symm μ) = μ := fun μ => e.apply_symm_apply μ
  refine ⟨(e.symm, fun μ => ε (e.symm μ)), fun x => ?_⟩
  funext μ
  rw [linearMap_apply_eq_sum A ha, Finset.sum_eq_single (e.symm μ)]
  · rw [h, if_pos (he μ).symm, SignedFrame.actOnVector, mul_comm]
  · intro ν _ hν
    have : μ ≠ τ ν := fun hμ => hν (by rw [hμ]; exact (e.symm_apply_apply ν).symm)
    rw [h, if_neg this]
    simp
  · simp
theorem exists_signedFrame_of_rows {A : (Fin 4 → ℝ) →ₗ[ℝ] (Fin 4 → ℝ)}
    (hsurj : Function.Surjective A) {a : Fin 4 → Fin 4 → ℤ}
    (ha : ∀ ν μ, A (Pi.single ν 1) μ = a ν μ) (hsum : ∀ μ, ∑ ν, |a ν μ| ≤ 1) :
    ∃ r : SignedFrame, ∀ x, A x = r.actOnVector x := by
  have hne : ∀ μ, (fun ν => a ν μ) ≠ 0 := fun μ h => by
    obtain ⟨x, hx⟩ := hsurj (Pi.single μ 1)
    have h1 := linearMap_apply_eq_sum A ha x μ
    have h2 : ∀ ν, a ν μ = 0 := fun ν => congrFun h ν
    rw [hx] at h1
    simp [h2] at h1
  choose π ε h using fun μ => eq_signed_basis_of_sum_abs_le_one (hsum μ) (hne μ)
  have hrow : ∀ x μ, A x μ = ((ε μ : ℤ) : ℝ) * x (π μ) := fun x μ => by
    rw [linearMap_apply_eq_sum A ha, Finset.sum_eq_single (π μ)]
    · rw [h, if_pos rfl, mul_comm]
    · intro ν _ hν
      rw [h, if_neg hν]
      simp
    · simp
  have hπ : Function.Injective π := by
    intro μ μ' hμ
    by_contra hne'
    obtain ⟨x, hx⟩ := hsurj (Pi.single μ 1)
    have h1 := hrow x μ
    have h2 := hrow x μ'
    rw [hx] at h1 h2
    have h3 : x (π μ) = 0 := by
      rw [Pi.single_eq_of_ne (Ne.symm hne'), ← hμ] at h2
      have hu : ((ε μ' : ℤ) : ℝ) ≠ 0 := by exact_mod_cast (ε μ').ne_zero
      exact (mul_eq_zero.1 h2.symm).resolve_left hu
    rw [h3] at h1
    simp at h1
  refine ⟨(Equiv.ofBijective π (Finite.injective_iff_bijective.1 hπ), ε), fun x => ?_⟩
  funext μ
  rw [hrow]
  rfl
theorem supNormVec_eq_norm (v : Fin 4 → ℝ) : supNormVec v = ‖v‖ := by
  apply le_antisymm
  · exact Finset.sup'_le _ _ fun μ _ => norm_le_pi_norm v μ
  · refine (pi_norm_le_iff_of_nonneg ?_).2 fun μ => ?_
    · exact (abs_nonneg (v 0)).trans (Finset.le_sup' (fun μ => |v μ|) (Finset.mem_univ (0 : Fin 4)))
    · exact Finset.le_sup' (fun μ => |v μ|) (Finset.mem_univ μ)
def supNormSeminorm : Seminorm ℝ (Fin 4 → ℝ) := normSeminorm ℝ (Fin 4 → ℝ)
def l1NormSeminorm : Seminorm ℝ (Fin 4 → ℝ) :=
  Seminorm.of l1NormVec
    (fun x y => by
      simp only [l1NormVec, Pi.add_apply]
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_le_sum fun μ _ => abs_add_le _ _)
    (fun c x => by simp [l1NormVec, abs_mul, Finset.mul_sum])
theorem euclidNormVec_eq_norm (v : Fin 4 → ℝ) : euclidNormVec v = ‖WithLp.toLp 2 v‖ := by apply _root_.YangMills.Construction.AmbientPoints.euclidNormVec_eq_norm <;> assumption
def euclidNormSeminorm : Seminorm ℝ (Fin 4 → ℝ) :=
  Seminorm.of euclidNormVec
    (fun x y => by
      simp only [euclidNormVec_eq_norm, WithLp.toLp_add]
      exact norm_add_le _ _)
    (fun c x => by
      simp only [euclidNormVec_eq_norm, WithLp.toLp_smul]
      exact norm_smul _ _)
theorem supNormSeminorm_isMonotoneCoordNorm : IsMonotoneCoordNorm supNormSeminorm where
  monotone_abs a b h := by
    show ‖a‖ ≤ ‖b‖
    exact (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun μ => (h μ).trans (norm_le_pi_norm b μ)
  sup_le _ := le_rfl
  le_four_sup a := by
    have : 0 ≤ ‖a‖ := norm_nonneg a
    show ‖a‖ ≤ 4 * ‖a‖
    linarith
theorem l1NormSeminorm_isMonotoneCoordNorm : IsMonotoneCoordNorm l1NormSeminorm where
  monotone_abs a b h := by
    show ∑ μ, |a μ| ≤ ∑ μ, |b μ|
    exact Finset.sum_le_sum fun μ _ => h μ
  sup_le a := by
    show ‖a‖ ≤ ∑ μ, |a μ|
    exact (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _)).2 fun μ =>
      Finset.single_le_sum (f := fun μ => |a μ|) (fun _ _ => abs_nonneg _) (Finset.mem_univ μ)
  le_four_sup a := by
    show ∑ μ, |a μ| ≤ 4 * ‖a‖
    have h : ∀ μ, |a μ| ≤ ‖a‖ := fun μ => norm_le_pi_norm a μ
    rw [Fin.sum_univ_four]
    linarith [h 0, h 1, h 2, h 3]
theorem euclidNormSeminorm_isMonotoneCoordNorm : IsMonotoneCoordNorm euclidNormSeminorm where
  monotone_abs a b h := by
    show Real.sqrt (∑ μ, a μ ^ 2) ≤ Real.sqrt (∑ μ, b μ ^ 2)
    exact Real.sqrt_le_sqrt (Finset.sum_le_sum fun μ _ => sq_le_sq.2 (h μ))
  sup_le a := by
    show ‖a‖ ≤ Real.sqrt (∑ μ, a μ ^ 2)
    exact (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun μ =>
      Real.abs_le_sqrt (Finset.single_le_sum (f := fun μ => a μ ^ 2) (fun _ _ => sq_nonneg _)
        (Finset.mem_univ μ))
  le_four_sup a := by
    show Real.sqrt (∑ μ, a μ ^ 2) ≤ 4 * ‖a‖
    have hn : 0 ≤ ‖a‖ := norm_nonneg a
    refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
    have h : ∀ μ, a μ ^ 2 ≤ ‖a‖ ^ 2 := fun μ => sq_le_sq.2 (by
      rw [abs_of_nonneg hn]
      exact norm_le_pi_norm a μ)
    rw [Fin.sum_univ_four]
    nlinarith [h 0, h 1, h 2, h 3, sq_nonneg ‖a‖]
theorem sum_abs_pi_single (ν : Fin 4) : ∑ μ, |(Pi.single ν (1 : ℝ) : Fin 4 → ℝ) μ| = 1 := by
  rw [Finset.sum_eq_single ν]
  · simp
  · intro μ _ h
    simp [Pi.single_eq_of_ne h]
  · simp
theorem sum_sq_pi_single (ν : Fin 4) : ∑ μ, (Pi.single ν (1 : ℝ) : Fin 4 → ℝ) μ ^ 2 = 1 := by
  rw [Finset.sum_eq_single ν]
  · simp
  · intro μ _ h
    simp [Pi.single_eq_of_ne h]
  · simp
theorem bijective_and_exists_signedFrame [Fact (0 < S)]
    (mazur : LinearAlgebra.NormIsometry.BijectiveNormIsometryIsAffine)
    {f : Torus4 S → Torus4 S}
    (h : (∀ x y, _root_.YangMills.Construction.TorusMetric.torusSupNorm (f x - f y) = _root_.YangMills.Construction.TorusMetric.torusSupNorm (x - y)) ∨
      (∀ x y, torusL1Norm (f x - f y) = torusL1Norm (x - y)) ∨
      (∀ x y, torusEuclidNorm (f x - f y) = torusEuclidNorm (x - y))) :
    Function.Bijective f ∧ ∃ (r : SignedFrame) (v : Fin 4 → ℝ),
      ∀ x, f (torusProj S x) = torusProj S (r.actOnVector x + v) := by
  rcases h with h | h | h
  · have hsupN : ∀ x : Torus4 S, _root_.YangMills.Construction.TorusMetric.torusSupNorm x = torusNormOf supNormSeminorm x := fun x => by
      have : TorusMetric.supNormVec = fun v => supNormSeminorm v := funext supNormVec_eq_norm
      rw [_root_.YangMills.Construction.TorusMetric.torusSupNorm, torusNormOf, this]
    have hk : PreservesTorusNorm supNormSeminorm f := fun x y => by rw [← hsupN, ← hsupN, h]
    have hN := supNormSeminorm_isMonotoneCoordNorm
    refine ⟨⟨hk.injective hN, hk.surjective hN⟩, ?_⟩
    obtain ⟨A, v, hb, hn, hl, hz⟩ := exists_affine_lift mazur hN hk
    choose a ha using hz
    obtain ⟨r, hr⟩ := exists_signedFrame_of_rows hb.2 ha (fun μ => by
      let x : Fin 4 → ℝ := fun ν => if 0 ≤ a ν μ then 1 else -1
      have h1 : A x μ = ((∑ ν, |a ν μ| : ℤ) : ℝ) := by
        rw [linearMap_apply_eq_sum A ha]
        push_cast
        refine Finset.sum_congr rfl fun ν _ => ?_
        by_cases h0 : 0 ≤ a ν μ
        · have h0' : (0 : ℝ) ≤ a ν μ := by exact_mod_cast h0
          simp [x, h0, abs_of_nonneg h0']
        · have h0' : (a ν μ : ℝ) < 0 := by exact_mod_cast not_le.1 h0
          simp [x, h0, abs_of_neg h0']
      have h2 : ‖x‖ ≤ 1 := (pi_norm_le_iff_of_nonneg zero_le_one).2 fun ν => by
        by_cases h0 : 0 ≤ a ν μ <;> simp [x, h0]
      have h3 : ‖A x‖ = ‖x‖ := hn x
      have h4 : ‖A x μ‖ ≤ ‖A x‖ := norm_le_pi_norm _ μ
      have h5 : A x μ ≤ 1 := by
        have := le_abs_self (A x μ)
        rw [Real.norm_eq_abs] at h4
        linarith
      rw [h1] at h5
      exact_mod_cast h5)
    exact ⟨r, v, fun x => by rw [hl, hr]⟩
  · have hk : PreservesTorusNorm l1NormSeminorm f := h
    have hN := l1NormSeminorm_isMonotoneCoordNorm
    refine ⟨⟨hk.injective hN, hk.surjective hN⟩, ?_⟩
    obtain ⟨A, v, hb, hn, hl, hz⟩ := exists_affine_lift mazur hN hk
    choose a ha using hz
    obtain ⟨r, hr⟩ := exists_signedFrame_of_columns hb.1 ha (fun ν => by
      have h1 : ∑ μ, |A (Pi.single ν 1) μ| = ∑ μ, |(Pi.single ν (1 : ℝ) : Fin 4 → ℝ) μ| :=
        hn (Pi.single ν 1)
      rw [sum_abs_pi_single] at h1
      simp only [ha] at h1
      have h2 : ((∑ μ, |a ν μ| : ℤ) : ℝ) = 1 := by
        push_cast
        exact h1
      exact le_of_eq (by exact_mod_cast h2))
    exact ⟨r, v, fun x => by rw [hl, hr]⟩
  · have hk : PreservesTorusNorm euclidNormSeminorm f := h
    have hN := euclidNormSeminorm_isMonotoneCoordNorm
    refine ⟨⟨hk.injective hN, hk.surjective hN⟩, ?_⟩
    obtain ⟨A, v, hb, hn, hl, hz⟩ := exists_affine_lift mazur hN hk
    choose a ha using hz
    obtain ⟨r, hr⟩ := exists_signedFrame_of_columns hb.1 ha (fun ν => by
      have h1 : Real.sqrt (∑ μ, A (Pi.single ν 1) μ ^ 2) =
          Real.sqrt (∑ μ, (Pi.single ν (1 : ℝ) : Fin 4 → ℝ) μ ^ 2) := hn (Pi.single ν 1)
      rw [sum_sq_pi_single, Real.sqrt_one] at h1
      simp only [ha] at h1
      have h2 : (∑ μ, (a ν μ : ℝ) ^ 2) = 1 := by
        have h3 : 0 ≤ ∑ μ, (a ν μ : ℝ) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
        rw [← Real.sq_sqrt h3, h1]
        norm_num
      have h4 : ∑ μ, a ν μ ^ 2 = 1 := by exact_mod_cast h2
      rw [← h4]
      refine Finset.sum_le_sum fun μ _ => ?_
      rw [← sq_abs (a ν μ)]
      rcases eq_or_ne (a ν μ) 0 with h0 | h0
      · simp [h0]
      · have : 1 ≤ |a ν μ| := Int.one_le_abs h0
        nlinarith)
    exact ⟨r, v, fun x => by rw [hl, hr]⟩
theorem torusProj_zero : torusProj S 0 = 0 := by apply _root_.YangMills.Construction.LimitSpaces.PeriodizeOnSmallSets.torusProj_zero <;> assumption
theorem actOnVector_zero (r : SignedFrame) : r.actOnVector 0 = 0 := by
  funext μ
  simp [SignedFrame.actOnVector]
theorem mem_meshVectors_of_torusProj_mem {L m : ℕ} (hL : 0 < L) {i : ℤ} (hi : -(m : ℤ) ≤ i)
    {v : Fin 4 → ℝ} (h : torusProj (torusSide L m) v ∈ sublattice L m i) : v ∈ meshVectors L i := by
  obtain ⟨d, hd⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ (m : ℤ) + i by omega)
  have hL' : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  have hside : torusSide L m = ((2 * (L : ℤ) ^ d : ℤ) : ℝ) * meshSize L i := by
    have hi' : i = (d : ℤ) - m := by omega
    simp only [torusSide, meshSize]
    push_cast
    rw [hi', neg_sub, zpow_sub₀ hL', zpow_natCast, zpow_natCast]
    field_simp
  obtain ⟨n, hn⟩ := h
  have key : ∀ μ, ∃ k : ℤ, v μ = (k : ℝ) * meshSize L i := fun μ => by
    have h1 : ((v μ - n μ * meshSize L i : ℝ) : AddCircle (torusSide L m)) = 0 := by
      rw [AddCircle.coe_sub, sub_eq_zero]
      exact hn μ
    obtain ⟨k, hk⟩ := (AddCircle.coe_eq_zero_iff _).1 h1
    refine ⟨n μ + k * (2 * (L : ℤ) ^ d), ?_⟩
    rw [zsmul_eq_mul, hside] at hk
    push_cast at hk ⊢
    linarith
  choose n' hn' using key
  exact ⟨n', hn'⟩
theorem toLevelUnits_le_toLevelUnits_iff {L K t : ℕ} (hL : 0 < L) {a b : ℝ} :
    toLevelUnits L K t a ≤ toLevelUnits L K t b ↔ a ≤ b := by
  have h : (0 : ℝ) < (L : ℝ) ^ levelDepth K t := zpow_pos (by exact_mod_cast hL) _
  exact ⟨fun h' => le_of_mul_le_mul_left h' h, fun h' => mul_le_mul_of_nonneg_left h' h.le⟩
theorem preservesPartitionCubes_of_mem (iso : LatticeIsometryGroupActionStatement) {L m : ℕ}
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) {i j : ℤ} (hi : -(m : ℤ) ≤ i)
    (hij : i ≤ j) {σ : FourTorus L m ≃ FourTorus L m} (hσ : σ ∈ latticeIsometries L m i) :
    PreservesPartitionCubes σ j := by
  obtain ⟨-, -, -, -, h⟩ := iso L m i hL hm hi
  obtain ⟨-, -, -, -, -, -, -, -, -, hp⟩ := (h σ hσ j hij).1
  intro Q hQ
  have : σ '' Q ∈ (fun Q => σ '' Q) '' standardCubePartition L m j := ⟨Q, hQ, rfl⟩
  rwa [hp] at this
theorem levelIsometryProperties_holds
    (mazur : LinearAlgebra.NormIsometry.BijectiveNormIsometryIsAffine)
    (ball : SupBallDeterminesCentre) (cov : LatticeIsometryCovariance) :
    LevelIsometryProperties := by
  intro L m K t u hL hm hK ht hu
  have hLpos : 0 < L := by
    have := hL.2
    omega
  have hLr : (0 : ℝ) < L := by exact_mod_cast hLpos
  have hL0 : (L : ℝ) ≠ 0 := hLr.ne'
  have : Fact (0 < torusSide L m) := ⟨by unfold torusSide; positivity⟩
  have iso := cov.1
  have hi : -(m : ℤ) ≤ scaledCubeIndex K t u := by
    simp only [scaledCubeIndex, levelDepth] at hu ⊢
    omega
  have hdepth : -(m : ℤ) ≤ levelDepth K t := by
    simp only [levelDepth]
    omega
  have hunit : toLevelUnits L K t (meshSize L (levelDepth K t)) = 1 := by
    simp only [toLevelUnits, meshSize]
    rw [← zpow_add₀ hL0, add_neg_cancel, zpow_zero]
  have hlevel : RegionChains.meshAtLevel L t t = 1 := by
    simp only [RegionChains.meshAtLevel, finestMeshInLevelUnits]
    rw [← zpow_natCast, ← zpow_add₀ hL0, add_neg_cancel, zpow_zero]
  have hcube : toLevelUnits L K t (meshSize L (scaledCubeIndex K t u)) = (L : ℝ) ^ u := by
    rw [meshSize_scaledCubeIndex hLpos.ne']
    simp only [toLevelUnits] at hunit ⊢
    rw [mul_left_comm, hunit, mul_one]
  refine ⟨by rw [hunit, hlevel], by rw [hcube, hlevel, mul_one], hi, ?_, fun σ hσ => ?_⟩
  · intro f hf hlat
    obtain ⟨hbij, r, v, hv⟩ := bijective_and_exists_signedFrame mazur hf
    have h0 : torusProj (torusSide L m) v = f 0 := by
      have h1 := hv 0
      rw [torusProj_zero, actOnVector_zero, zero_add] at h1
      exact h1.symm
    have hmem : f 0 ∈ (sublattice L m (levelDepth K t) : Set (FourTorus L m)) :=
      hlat ▸ mem_image_of_mem f (zero_mem _)
    exact ⟨Equiv.ofBijective f hbij,
      ⟨r, v, mem_meshVectors_of_torusProj_mem hLpos hdepth (h0 ▸ hmem), fun x => hv x⟩, rfl⟩
  · have hσ' := hσ
    obtain ⟨r, v, hv, hind⟩ := hσ
    have hfwd : PreservesPartitionCubes σ (scaledCubeIndex K t u) →
        σ ∈ latticeIsometries L m (scaledCubeIndex K t u) := by
      intro hmaps
      have hpres := ((iso L m _ hL hm hdepth).2.1 σ hσ').1.1
      obtain ⟨y, hy⟩ := hmaps _ (⟨0, rfl⟩ :
        cubeAround (0 : Site L m (scaledCubeIndex K t u)) ∈
          standardCubePartition L m (scaledCubeIndex K t u))
      have hball : ∀ x, x ∈ cubeAround y ↔
          _root_.YangMills.Construction.TorusMetric.torusSupNorm (x - σ 0) ≤ meshSize L (scaledCubeIndex K t u) / 2 := by
        intro x
        rw [hy]
        constructor
        · rintro ⟨z, hz, rfl⟩
          rw [hpres]
          simpa [cubeAround] using hz
        · intro hx
          refine ⟨σ.symm x, ?_, σ.apply_symm_apply x⟩
          have h1 := hpres (σ.symm x) 0
          rw [σ.apply_symm_apply] at h1
          rw [h1] at hx
          simpa [cubeAround] using hx
      have hhalf : toLevelUnits L K t (meshSize L (scaledCubeIndex K t u) / 2) =
          (L : ℝ) ^ u / 2 := by
        simp only [toLevelUnits] at hcube ⊢
        rw [← mul_div_assoc, hcube]
      have hρ : toLevelUnits L K t (meshSize L (scaledCubeIndex K t u) / 2) ≤
          sideInLevelUnits L m K t / 4 := by
        rw [hhalf]
        have h1 : (L : ℝ) ^ u ≤ (L : ℝ) ^ ((m : ℤ) + (K : ℤ) - (t : ℤ)) := by
          rw [← zpow_natCast]
          refine zpow_le_zpow_right₀ (by exact_mod_cast hLpos) ?_
          simp only [levelDepth] at hu
          omega
        simp only [sideInLevelUnits]
        linarith
      have hρ0 : 0 ≤ toLevelUnits L K t (meshSize L (scaledCubeIndex K t u) / 2) := by
        rw [hhalf]
        positivity
      have hcentre : (y : FourTorus L m) = σ 0 :=
        ball L m K hL hm hK t ht _ hρ0 hρ y (σ 0) (Set.ext fun x => by
          show toLevelUnits L K t _ ≤ _ ↔ toLevelUnits L K t _ ≤ _
          rw [toLevelUnits_le_toLevelUnits_iff hLpos, toLevelUnits_le_toLevelUnits_iff hLpos]
          exact hball x)
      have hcov : torusProj (torusSide L m) v = σ 0 := by
        have h1 := hind 0
        have h2 : toFourTorus L m 0 = 0 := torusProj_zero
        rw [h2, actOnVector_zero, zero_add] at h1
        exact h1.symm
      have hmem : torusProj (torusSide L m) v ∈ sublattice L m (scaledCubeIndex K t u) := by
        rw [hcov, ← hcentre]
        exact y.2
      exact ⟨r, v, mem_meshVectors_of_torusProj_mem hLpos hi hmem, hind⟩
    have hkey : σ ∈ latticeIsometries L m (scaledCubeIndex K t u) → ∀ n p : ℕ, n ≤ t →
        L ^ p ≤ L ^ u → PreservesPartitionCubes σ (scaledCubeIndex K n p) := by
      intro hmem n p hn hp
      have hpu : p ≤ u := (Nat.pow_le_pow_iff_right (by have := hL.2; omega)).1 hp
      refine preservesPartitionCubes_of_mem iso hL hm hi ?_ hmem
      simp only [scaledCubeIndex, levelDepth]
      omega
    exact ⟨⟨hfwd, fun h => preservesPartitionCubes_of_mem iso hL hm hi le_rfl h⟩,
      fun h => hkey (hfwd h)⟩
end YangMills.Construction.PeriodicLattice.LevelIsometryProof
