import YangMills.Construction.QuaternionicWilsonModel.TheFlowRepresentsTheMixedMomentProof
import YangMills.Construction.ClusterExpansionOfAStep.AnglesAlongOneDirection
import YangMills.Construction.ClusterExpansionOfAStep.CurvatureCovariantUnderIsometries
import YangMills.Construction.ClusterExpansionOfAStep.HessianOfAFamilyAtTheFlatField
import YangMills.Construction.ClusterExpansionOfAStep.OneNumberOfACarriedFamily
import YangMills.Construction.ClusterExpansionOfAStep.SecondOrderAtAbelianFields
import YangMills.Construction.ClusterExpansionOfAStep.WrittenFieldHasItsCurvature
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Topology
open Filter
namespace YangMills.Construction.TorusLumps
open BlockAverages TorusFields FlatHessian
variable {n : ℕ}
private def planeLow : Fin 6 → Fin 4 := ![0, 0, 0, 1, 1, 2]
private def planeHigh : Fin 6 → Fin 4 := ![1, 2, 3, 2, 3, 3]
private def unitPlaneInt (u : Fin 6) (i j : Fin 4) : ℤ :=
  (if i = planeLow u ∧ j = planeHigh u then 1 else 0) - (if i = planeHigh u ∧ j = planeLow u then 1 else 0)
private def unitPlane (u : Fin 6) (i j : Fin 4) : ℝ := (unitPlaneInt u i j : ℝ)
private theorem unitPlaneInt_antisymm : ∀ u i j, unitPlaneInt u i j = - unitPlaneInt u j i := by decide
private theorem unitPlaneInt_ends : ∀ u w, unitPlaneInt u (planeLow w) (planeHigh w) = if u = w then 1 else 0 := by decide
private theorem unitPlaneInt_diag : ∀ u i, unitPlaneInt u i i = 0 := by decide
private theorem index_pairs_cover : ∀ i j : Fin 4, i = j ∨ ∃ w, (i = planeLow w ∧ j = planeHigh w) ∨ (i = planeHigh w ∧ j = planeLow w) := by
  decide
private theorem sum_upper_eq_sum_planes (f : Fin 4 → Fin 4 → ℝ) :
    ∑ i, ∑ j, (if i < j then f i j else 0) = ∑ u, f (planeLow u) (planeHigh u) := by
  simp [Fin.sum_univ_four, Fin.sum_univ_six, planeLow, planeHigh]
  ring
private theorem antisymm_eq_sum_planes {M : Type} [AddCommGroup M] [Module ℝ M] (A : Fin 4 → Fin 4 → M)
    (hA : ∀ i j, A i j = - A j i) (i j : Fin 4) : A i j = ∑ u, unitPlane u i j • A (planeLow u) (planeHigh u) := by
  rcases index_pairs_cover i j with rfl | ⟨w, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
  · have h2 : (2 : ℝ) • A i i = 0 := by
      rw [two_smul]
      nth_rw 1 [hA i i]
      simp
    have h0 : A i i = 0 := (smul_eq_zero.mp h2).resolve_left two_ne_zero
    simp [unitPlane, unitPlaneInt_diag, h0]
  · rw [Finset.sum_eq_single w]
    · simp [unitPlane, unitPlaneInt_ends]
    · intro u _ hu
      simp [unitPlane, unitPlaneInt_ends, hu]
    · simp
  · rw [Finset.sum_eq_single w]
    · rw [hA]
      simp [unitPlane, unitPlaneInt_antisymm _ (planeHigh w) (planeLow w), unitPlaneInt_ends]
    · intro u _ hu
      simp [unitPlane, unitPlaneInt_antisymm _ (planeHigh w) (planeLow w), unitPlaneInt_ends, hu]
    · simp
private def realPotential (ω : Fin 4 → Fin 4 → ℝ) (c : (Fin 4 → ℤ) × Fin 4) : ℝ :=
  (1 / 2) * ∑ ν, ((c.1 ν : ℤ) : ℝ) * ω ν c.2
private theorem linearPotential_curvatureAlong (X : imaginaryQuaternions) (ω : Fin 4 → Fin 4 → ℝ) (c : (Fin 4 → ℤ) × Fin 4) :
    linearPotential (curvatureAlong X ω) c = realPotential ω c • X := by
  simp only [linearPotential, curvatureAlong, realPotential, Finset.sum_smul, Finset.smul_sum, mul_smul]
private theorem linearPotential_eq_sum_planes (A : Fin 4 → Fin 4 → imaginaryQuaternions) (hA : ∀ i j, A i j = - A j i)
    (c : (Fin 4 → ℤ) × Fin 4) :
    linearPotential A c = ∑ u, realPotential (unitPlane u) c • A (planeLow u) (planeHigh u) := by
  have e : ∀ ν, ((c.1 ν : ℤ) : ℝ) • A ν c.2 =
      ∑ u, (((c.1 ν : ℤ) : ℝ) * unitPlane u ν c.2) • A (planeLow u) (planeHigh u) := by
    intro ν
    conv_lhs => rw [antisymm_eq_sum_planes A hA ν c.2]
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun u _ => by rw [smul_smul]
  simp only [linearPotential, e]
  rw [Finset.sum_comm, Finset.smul_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  simp only [realPotential, Finset.sum_smul, Finset.smul_sum, mul_smul]
private theorem inner_quaternionI_self : inner ℝ (quaternionI : ℍ[ℝ]) (quaternionI : ℍ[ℝ]) = 1 := by apply _root_.YangMills.DeltaSharedProofs.p500886 <;> assumption
private theorem norm_quaternionI : ‖quaternionI‖ = 1 := by
  have h1 : ‖(quaternionI : ℍ[ℝ])‖ ^ 2 = 1 := by
    rw [← real_inner_self_eq_norm_sq, inner_quaternionI_self]
  have h2 : ‖quaternionI‖ = ‖(quaternionI : ℍ[ℝ])‖ := rfl
  rw [h2]
  nlinarith [norm_nonneg (quaternionI : ℍ[ℝ]), sq_nonneg (‖(quaternionI : ℍ[ℝ])‖ - 1)]
abbrev _root_.YangMills.SharedProofs.p83019 := @norm_quaternionI
private theorem abs_sum_sub_card_mul_le {ι : Type} [Fintype ι] (f : ι → ℝ) (a e : ℝ) (h : ∀ y, |f y - a| ≤ e) :
    |∑ y, f y - (Fintype.card ι : ℝ) * a| ≤ (Fintype.card ι : ℝ) * e := by
  have e1 : ∑ y, f y - (Fintype.card ι : ℝ) * a = ∑ y, (f y - a) := by
    simp [Finset.sum_sub_distrib, Finset.card_univ]
  rw [e1]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine (Finset.sum_le_sum fun y _ => h y).trans ?_
  simp [Finset.card_univ]
private theorem isCold_of_small_angles (X : imaginaryQuaternions) (hX : ‖X‖ = 1) (ω : Fin 4 → Fin 4 → ℝ) (γ s : ℝ) (V : TorusField n)
    (hV : IsAbelianWithCurvature X ω γ V) (hs : ∀ i j, (γ * ω i j) ^ 2 / 2 + |γ * ω i j| < s) :
    IsCold s V := by
  intro x μ ν hμν
  simp only [curvature]
  rw [hV.2 x μ ν hμν]
  exact (norm_coe_expUnit_smul_sub_one_le X hX _).trans_lt (hs μ ν)
private def reflectionSign (a x : Fin 4) : ℤ := if x = a then -1 else 1
private theorem reflectionSign_in_plane : ∀ (a : Fin 4) (u : Fin 6) (i j : Fin 4), (a = planeLow u ∨ a = planeHigh u) →
    reflectionSign a i * reflectionSign a j * unitPlaneInt u i j = - unitPlaneInt u i j := by decide
private theorem reflectionSign_off_plane : ∀ (a : Fin 4) (u : Fin 6) (i j : Fin 4), a ≠ planeLow u → a ≠ planeHigh u →
    reflectionSign a i * reflectionSign a j * unitPlaneInt u i j = unitPlaneInt u i j := by decide
private theorem exists_axis_separating : ∀ u v : Fin 6, u ≠ v → ∃ a, (a = planeLow u ∨ a = planeHigh u) ∧ a ≠ planeLow v ∧ a ≠ planeHigh v := by
  decide
private theorem exists_perm_to_plane (u : Fin 6) : ∃ p : Equiv.Perm (Fin 4), ∀ x y, unitPlaneInt 0 (p x) (p y) = unitPlaneInt u x y := by
  fin_cases u
  · exact ⟨1, by decide⟩
  · exact ⟨Equiv.swap 1 2, by decide⟩
  · exact ⟨Equiv.swap 1 3, by decide⟩
  · exact ⟨Equiv.swap 1 2 * Equiv.swap 0 1, by decide⟩
  · exact ⟨Equiv.swap 1 3 * Equiv.swap 0 1, by decide⟩
  · exact ⟨Equiv.swap 0 2 * Equiv.swap 1 3, by decide⟩
private theorem double_sum_delta (c : Fin 6 → Fin 6 → ℝ) (u v : Fin 6) (a b : ℝ) :
    ∑ w, ∑ w', (a * (if u = w then 1 else 0)) * (b * (if v = w' then 1 else 0)) * c w w' = a * b * c u v := by
  rw [Finset.sum_eq_single u, Finset.sum_eq_single v]
  · simp
  · intro w' _ hw
    simp [Ne.symm hw]
  · simp
  · intro w _ hw
    refine Finset.sum_eq_zero fun w' _ => ?_
    simp [Ne.symm hw]
  · simp
private theorem quadratic_two_planes (c : Fin 6 → Fin 6 → ℝ) (u v : Fin 6) (a b : ℝ) :
    ∑ w, ∑ w', ((a * (if u = w then 1 else 0)) + (b * (if v = w then 1 else 0))) *
        ((a * (if u = w' then 1 else 0)) + (b * (if v = w' then 1 else 0))) * c w w' =
      a * a * c u u + a * b * c u v + b * a * c v u + b * b * c v v := by
  simp only [add_mul, mul_add, Finset.sum_add_distrib, double_sum_delta]
  ring
private def unitFluxCurvature (n : ℕ) : ℝ := 2 * Real.pi * ((1 : ℕ) : ℝ) / (n : ℝ) ^ 2
private theorem invariantFamilyCurvatureForm_aux (hi : SecondOrderAtAbelianFields) (hH : HessianAtTrivialFieldStatement)
    (hIso : CurvatureUnderAnIsometry) (hW : AbelianFieldOfAnglesHasCurvature) :
    InvariantFamilyCurvatureForm := by
  intro ℓ hfit C h hh hcar
  obtain ⟨hT, -, -, -, hS, -, -, hV⟩ := hi ℓ hfit C h hh
  refine ⟨hT, ?_⟩
  have hev : ∀ᶠ n : ℕ in atTop, ℓ.n₀ ≤ n ∧ n ≠ 0 := by
    filter_upwards [eventually_ge_atTop (max ℓ.n₀ 1)] with n hn
    refine ⟨le_trans (le_max_left _ _) hn, ?_⟩
    have := le_trans (le_max_right ℓ.n₀ 1) hn
    omega
  set q : (Fin 4 → ℤ) × Fin 4 → (Fin 4 → ℤ) × Fin 4 → ℝ := fun c c' => secondDerivLimit h c c' quaternionI quaternionI with hq
  have hQ : ∀ c c' X X', secondDerivLimit h c c' X X' = inner ℝ (X : ℍ[ℝ]) (X' : ℍ[ℝ]) * q c c' := by
    intro c c' X X'
    refine tendsto_nhds_unique (hT c c' X X') (((hT c c' quaternionI quaternionI).const_mul _).congr' ?_)
    filter_upwards [hev] with n hn
    haveI : NeZero n := ⟨hn.2⟩
    exact ((hH ℓ hfit C h hh n hn.1 0 (bondFrom 0 c) (bondFrom 0 c')).1 X X').symm
  have hqs : ∀ c c', q c c' = q c' c := by
    intro c c'
    refine tendsto_nhds_unique (hT c c' quaternionI quaternionI) ((hT c' c quaternionI quaternionI).congr' ?_)
    filter_upwards [hev] with n hn
    haveI : NeZero n := ⟨hn.2⟩
    exact ((hH ℓ hfit C h hh n hn.1 0 (bondFrom 0 c) (bondFrom 0 c')).2).symm
  set T : Fin 6 → Fin 6 → ((Fin 4 → ℤ) × Fin 4) × ((Fin 4 → ℤ) × Fin 4) → ℝ :=
    fun u v cc => realPotential (unitPlane u) cc.1 * realPotential (unitPlane v) cc.2 * q cc.1 cc.2 with hTdef
  have hPlaneAnti : ∀ u i j, unitPlane u i j = - unitPlane u j i := by
    intro u i j
    simp only [unitPlane]
    rw [unitPlaneInt_antisymm u i j]
    simp
  have hAlong : ∀ ω : Fin 4 → Fin 4 → ℝ, (∀ i j, ω i j = - ω j i) → ∀ (X : imaginaryQuaternions) (μ ν : Fin 4),
      curvatureAlong X ω μ ν = - curvatureAlong X ω ν μ := by
    intro ω hω X μ ν
    simp only [curvatureAlong]
    rw [hω μ ν]
    exact neg_smul (ω ν μ) X
  have hTs : ∀ u v, Summable (T u v) := by
    intro u v
    have hsum := hS (curvatureAlong quaternionI (unitPlane u)) (curvatureAlong quaternionI (unitPlane v))
      (hAlong _ (hPlaneAnti u) _) (hAlong _ (hPlaneAnti v) _)
    refine hsum.congr fun cc => ?_
    rw [linearPotential_curvatureAlong, linearPotential_curvatureAlong, hQ]
    simp only [hTdef, Submodule.coe_smul, real_inner_smul_left, real_inner_smul_right, inner_quaternionI_self]
    ring
  set c : Fin 6 → Fin 6 → ℝ := fun u v => ∑' cc, T u v cc with hcdef
  have hc : ∀ u v, HasSum (T u v) (c u v) := fun u v => (hTs u v).hasSum
  have hcs : ∀ u v, c u v = c v u := by
    intro u v
    simp only [hcdef]
    rw [← (Equiv.prodComm _ _).tsum_eq (T v u)]
    refine tsum_congr fun cc => ?_
    simp only [hTdef, Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap]
    rw [hqs cc.2 cc.1]
    ring
  have hgen : ∀ A A' : Fin 4 → Fin 4 → imaginaryQuaternions, (∀ μ ν, A μ ν = - A ν μ) → (∀ μ ν, A' μ ν = - A' ν μ) →
      HasSum (fun cc : ((Fin 4 → ℤ) × Fin 4) × ((Fin 4 → ℤ) × Fin 4) =>
        secondDerivLimit h cc.1 cc.2 (linearPotential A cc.1) (linearPotential A' cc.2))
        (∑ u, ∑ v, inner ℝ (A (planeLow u) (planeHigh u) : ℍ[ℝ]) (A' (planeLow v) (planeHigh v) : ℍ[ℝ]) * c u v) := by
    intro A A' hA hA'
    have e : (fun cc : ((Fin 4 → ℤ) × Fin 4) × ((Fin 4 → ℤ) × Fin 4) =>
        secondDerivLimit h cc.1 cc.2 (linearPotential A cc.1) (linearPotential A' cc.2)) =
        fun cc => ∑ u, ∑ v, inner ℝ (A (planeLow u) (planeHigh u) : ℍ[ℝ]) (A' (planeLow v) (planeHigh v) : ℍ[ℝ]) * T u v cc := by
      funext cc
      rw [hQ, linearPotential_eq_sum_planes A hA, linearPotential_eq_sum_planes A' hA']
      simp only [Submodule.coe_sum, Submodule.coe_smul, sum_inner, inner_sum, real_inner_smul_left,
        real_inner_smul_right, Finset.sum_mul, hTdef]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
      ring
    rw [e]
    exact hasSum_sum fun u _ => hasSum_sum fun v _ => (hc u v).mul_left _
  set Qf : (Fin 4 → Fin 4 → ℝ) → ℝ :=
    fun ω => ∑ u, ∑ v, ω (planeLow u) (planeHigh u) * ω (planeLow v) (planeHigh v) * c u v with hQf
  have hval : ∀ ω : Fin 4 → Fin 4 → ℝ, (∀ i j, ω i j = - ω j i) →
      HasSum (fun cc : ((Fin 4 → ℤ) × Fin 4) × ((Fin 4 → ℤ) × Fin 4) =>
        secondDerivLimit h cc.1 cc.2 (linearPotential (curvatureAlong quaternionI ω) cc.1)
          (linearPotential (curvatureAlong quaternionI ω) cc.2)) (Qf ω) := by
    intro ω hω
    have hs := hgen _ _ (hAlong ω hω quaternionI) (hAlong ω hω quaternionI)
    have e : Qf ω = ∑ u, ∑ v, inner ℝ (curvatureAlong quaternionI ω (planeLow u) (planeHigh u) : ℍ[ℝ])
        (curvatureAlong quaternionI ω (planeLow v) (planeHigh v) : ℍ[ℝ]) * c u v := by
      refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
      simp only [curvatureAlong, Submodule.coe_smul, real_inner_smul_left, real_inner_smul_right, inner_quaternionI_self]
      ring
    rw [e]
    exact hs
  have hγ : Tendsto unitFluxCurvature atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop ((tendsto_pow_atTop (two_ne_zero)).comp tendsto_natCast_atTop_atTop)
  have hinv : ∀ (ω : Fin 4 → Fin 4 → ℝ) (p : Equiv.Perm (Fin 4)) (s : Fin 4 → ℤ) (hs : ∀ i, s i = 1 ∨ s i = -1),
      (∀ i j, ω i j = - ω j i) → (∀ i j, ∃ z : ℤ, ω i j = z) →
      Qf (fun a b => (s a : ℝ) * (s b : ℝ) * ω (p a) (p b)) = Qf ω := by
    intro ω p s hs hω hz
    set ω' : Fin 4 → Fin 4 → ℝ := fun a b => (s a : ℝ) * (s b : ℝ) * ω (p a) (p b) with hω'def
    have hω' : ∀ i j, ω' i j = - ω' j i := by
      intro i j
      simp only [hω'def]
      rw [hω (p i) (p j)]
      ring
    have hz1 : ∀ i j, ∃ z : ℤ, ((1 : ℕ) : ℝ) * ω i j = z := by
      intro i j
      obtain ⟨z, hz'⟩ := hz i j
      exact ⟨z, by simp [hz']⟩
    have hz1' : ∀ i j, ∃ z : ℤ, ((1 : ℕ) : ℝ) * ω' i j = z := by
      intro i j
      obtain ⟨z, hz'⟩ := hz (p i) (p j)
      exact ⟨s i * s j * z, by simp [hω'def, hz']⟩
    obtain ⟨v, hv, hb⟩ := hV ω 1 quaternionI hω one_pos hz1 norm_quaternionI
    obtain ⟨v', hv', hb'⟩ := hV ω' 1 quaternionI hω' one_pos hz1' norm_quaternionI
    rw [← hv.unique (hval ω hω), ← hv'.unique (hval ω' hω')]
    refine eq_of_abs_sub_le_all fun ε hε => ?_
    obtain ⟨n₁, hn₁⟩ := hb (ε / 4) (by positivity)
    obtain ⟨n₂, hn₂⟩ := hb' (ε / 4) (by positivity)
    have hsmall : ∀ w : ℝ, ∀ᶠ n : ℕ in atTop, (unitFluxCurvature n * w) ^ 2 / 2 + |unitFluxCurvature n * w| < ℓ.threshold := by
      intro w
      have h1 : Tendsto (fun n : ℕ => unitFluxCurvature n * w) atTop (𝓝 0) := by simpa using hγ.mul_const w
      have h2 : Tendsto (fun n : ℕ => (unitFluxCurvature n * w) ^ 2 / 2 + |unitFluxCurvature n * w|) atTop (𝓝 0) := by
        simpa using ((h1.pow 2).div_const 2).add h1.abs
      exact h2.eventually_lt_const hfit.σ_pos
    have hall : ∀ᶠ n : ℕ in atTop, (∀ i j, (unitFluxCurvature n * ω i j) ^ 2 / 2 + |unitFluxCurvature n * ω i j| < ℓ.threshold) ∧
        ∀ i j, (unitFluxCurvature n * ω' i j) ^ 2 / 2 + |unitFluxCurvature n * ω' i j| < ℓ.threshold :=
      (eventually_all.2 fun i => eventually_all.2 fun j => hsmall _).and
        (eventually_all.2 fun i => eventually_all.2 fun j => hsmall _)
    obtain ⟨n, hn, hsm, hsm'⟩ := ((eventually_ge_atTop (max (max n₁ n₂) (max ℓ.n₀ 1))).and hall).exists
    have hn1 : n₁ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
    have hn2 : n₂ ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
    have hn3 : ℓ.n₀ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn
    have hn4 : 1 ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn
    haveI : NeZero n := ⟨by omega⟩
    have hVa : IsAbelianWithCurvature quaternionI ω (unitFluxCurvature n)
        (abelianFieldOfAngles n quaternionI (unitFluxCurvature n) ω) :=
      hW n quaternionI ω 1 norm_quaternionI hω hz1
    obtain ⟨V', hcarry, hVa'⟩ := hIso n quaternionI ω (unitFluxCurvature n) _ p s hs hω hVa
    have hcold := isCold_of_small_angles quaternionI norm_quaternionI ω (unitFluxCurvature n) ℓ.threshold _ hVa hsm
    have hcold' := isCold_of_small_angles quaternionI norm_quaternionI ω' (unitFluxCurvature n) ℓ.threshold _ hVa' hsm'
    have hsum := hcar n hn3 _ _ _ hcold hcold' hcarry
    have b1 : ∀ Y, |centered h n Y (abelianFieldOfAngles n quaternionI (unitFluxCurvature n) ω) -
        unitFluxCurvature n ^ 2 / 2 * v| ≤ ε / 4 * unitFluxCurvature n ^ 2 :=
      fun Y => hn₁ n hn1 _ hVa Y
    have b2 : ∀ Y, |centered h n Y V' - unitFluxCurvature n ^ 2 / 2 * v'| ≤ ε / 4 * unitFluxCurvature n ^ 2 :=
      fun Y => hn₂ n hn2 _ hVa' Y
    have a1 := abs_sum_sub_card_mul_le _ _ _ b1
    have a2 := abs_sum_sub_card_mul_le _ _ _ b2
    rw [hsum] at a2
    have hg : 0 < unitFluxCurvature n := by
      have : (0 : ℝ) < n := by exact_mod_cast hn4
      simp only [unitFluxCurvature]
      positivity
    have hN : (0 : ℝ) < (Fintype.card (TorusSite n) : ℝ) := by
      exact_mod_cast Fintype.card_pos
    set N : ℝ := (Fintype.card (TorusSite n) : ℝ)
    obtain ⟨l1, u1⟩ := abs_le.mp a1
    obtain ⟨l2, u2⟩ := abs_le.mp a2
    have hK : 0 < N * unitFluxCurvature n ^ 2 / 2 := by positivity
    have c1 : (N * unitFluxCurvature n ^ 2 / 2) * (v' - v) ≤ (N * unitFluxCurvature n ^ 2 / 2) * ε := by nlinarith
    have c2 : (N * unitFluxCurvature n ^ 2 / 2) * (-ε) ≤ (N * unitFluxCurvature n ^ 2 / 2) * (v' - v) := by nlinarith
    exact abs_le.mpr ⟨le_of_mul_le_mul_left c2 hK, le_of_mul_le_mul_left c1 hK⟩
  have coef : ∀ u w, unitPlane u (planeLow w) (planeHigh w) = if u = w then 1 else 0 := by
    intro u w
    simp only [unitPlane, unitPlaneInt_ends]
    split_ifs <;> simp
  have hoff : ∀ u v, u ≠ v → c u v = 0 := by
    intro u v huv
    obtain ⟨a, ha, ha1, ha2⟩ := exists_axis_separating u v huv
    have hs : ∀ i, reflectionSign a i = 1 ∨ reflectionSign a i = -1 := by
      intro i
      simp only [reflectionSign]
      split_ifs <;> simp
    have hant : ∀ i j, (1 * unitPlane u i j + 1 * unitPlane v i j) = - (1 * unitPlane u j i + 1 * unitPlane v j i) := by
      intro i j
      rw [hPlaneAnti u i j, hPlaneAnti v i j]
      ring
    have hzz : ∀ i j, ∃ z : ℤ, 1 * unitPlane u i j + 1 * unitPlane v i j = z :=
      fun i j => ⟨unitPlaneInt u i j + unitPlaneInt v i j, by simp [unitPlane]⟩
    have h1 := hinv (fun i j => 1 * unitPlane u i j + 1 * unitPlane v i j) 1 (reflectionSign a) hs hant hzz
    have e1 : (fun x y => ((reflectionSign a x : ℤ) : ℝ) * ((reflectionSign a y : ℤ) : ℝ) *
        ((fun i j => 1 * unitPlane u i j + 1 * unitPlane v i j) ((1 : Equiv.Perm (Fin 4)) x) ((1 : Equiv.Perm (Fin 4)) y))) =
        fun i j => (-1) * unitPlane u i j + 1 * unitPlane v i j := by
      funext i j
      have g1 : ((reflectionSign a i : ℤ) : ℝ) * ((reflectionSign a j : ℤ) : ℝ) * unitPlane u i j = - unitPlane u i j := by
        simp only [unitPlane]
        exact_mod_cast reflectionSign_in_plane a u i j ha
      have g2 : ((reflectionSign a i : ℤ) : ℝ) * ((reflectionSign a j : ℤ) : ℝ) * unitPlane v i j = unitPlane v i j := by
        simp only [unitPlane]
        exact_mod_cast reflectionSign_off_plane a v i j ha1 ha2
      simp only [Equiv.Perm.coe_one, id]
      rw [one_mul, one_mul, mul_add, g1, g2]
      ring
    rw [e1] at h1
    simp only [hQf, coef] at h1
    rw [quadratic_two_planes, quadratic_two_planes] at h1
    have := hcs u v
    linarith
  have hdiag : ∀ u, c u u = c 0 0 := by
    intro u
    obtain ⟨p, hp⟩ := exists_perm_to_plane u
    have hant : ∀ i j, (1 * unitPlane 0 i j + 0 * unitPlane 0 i j) = - (1 * unitPlane 0 j i + 0 * unitPlane 0 j i) := by
      intro i j
      rw [hPlaneAnti 0 i j]
      ring
    have hzz : ∀ i j, ∃ z : ℤ, 1 * unitPlane 0 i j + 0 * unitPlane 0 i j = z :=
      fun i j => ⟨unitPlaneInt 0 i j, by simp [unitPlane]⟩
    have h1 := hinv (fun i j => 1 * unitPlane 0 i j + 0 * unitPlane 0 i j) p (fun _ => 1) (fun _ => Or.inl rfl) hant hzz
    have e1 : (fun x y => (((1 : ℤ)) : ℝ) * (((1 : ℤ)) : ℝ) *
        ((fun i j => 1 * unitPlane 0 i j + 0 * unitPlane 0 i j) (p x) (p y))) =
        fun i j => 1 * unitPlane u i j + 0 * unitPlane u i j := by
      funext i j
      have g1 : unitPlane 0 (p i) (p j) = unitPlane u i j := by
        simp only [unitPlane]
        rw [hp]
      simp only [g1]
      push_cast
      ring
    rw [e1] at h1
    simp only [hQf, coef] at h1
    rw [quadratic_two_planes, quadratic_two_planes] at h1
    linarith
  refine ⟨c 0 0, fun A A' hA hA' => ?_⟩
  have hs := hgen A A' hA hA'
  have e : c 0 0 * curvaturePairing A A' =
      ∑ u, ∑ v, inner ℝ (A (planeLow u) (planeHigh u) : ℍ[ℝ]) (A' (planeLow v) (planeHigh v) : ℍ[ℝ]) * c u v := by
    simp only [curvaturePairing]
    rw [sum_upper_eq_sum_planes (fun i j => inner ℝ (A i j : ℍ[ℝ]) (A' i j : ℍ[ℝ])), Finset.mul_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Finset.sum_eq_single u]
    · rw [hdiag u]
      ring
    · intro v _ hv
      rw [hoff u v (Ne.symm hv)]
      ring
    · simp
  rw [e]
  exact hs
theorem invariantFamilyCurvatureForm_of_secondOrder (hi : SecondOrderAtAbelianFields) (hH : HessianAtTrivialFieldStatement)
    (hIso : CurvatureUnderAnIsometry) (hW : AbelianFieldOfAnglesHasCurvature) :
    InvariantFamilyCurvatureForm :=
  invariantFamilyCurvatureForm_aux hi hH hIso hW
end YangMills.Construction.TorusLumps
end
