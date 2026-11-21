import YangMills.Construction.ResponseInTheExpansion.EnergyOfAPlaquetteAlongMoves
import YangMills.Construction.RunningCouplingSlope.CompositionKeepsTheCoefficientProof
import YangMills.Construction.RunningCouplingSlope.WilsonActionHasAChainForm
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Topology Quaternion
open YangMills.Construction.BlockAverages YangMills.Construction.TorusFields YangMills.Construction.TorusLumps YangMills.Construction.FlatLinearization
namespace YangMills.Construction.RunningCouplingSlope
variable {m : ℕ}
private def orientedSign (i : Fin 4) : ℝ := ![1, 1, -1, -1] i
private def edgeShift (m : ℕ) (μ ν i : Fin 4) : TorusSite m := ![0, TorusFields.unitStep m μ, TorusFields.unitStep m ν, 0] i
private def edgeAxis (μ ν i : Fin 4) : Fin 4 := ![μ, ν, μ, ν] i
private def latticeEdgeShift (μ ν i : Fin 4) : Fin 4 → ℤ := ![0, Pi.single μ 1, Pi.single ν 1, 0] i
private def curlKernel : BondKernel := fun m b c =>
  ∑ μ : Fin 4, ∑ ν : Fin 4, if μ < ν then ∑ i : Fin 4, ∑ j : Fin 4, orientedSign i * orientedSign j *
    (if edgeAxis μ ν i = b.2 ∧ edgeAxis μ ν j = c.2 ∧ b.1 - edgeShift m μ ν i = c.1 - edgeShift m μ ν j
      then 1 else 0) else 0
private def latticeCurlKernel (b c : LatticeBond) : ℝ :=
  ∑ μ : Fin 4, ∑ ν : Fin 4, if μ < ν then ∑ i : Fin 4, ∑ j : Fin 4, orientedSign i * orientedSign j *
    (if edgeAxis μ ν i = b.2 ∧ edgeAxis μ ν j = c.2 ∧ b.1 - latticeEdgeShift μ ν i = c.1 - latticeEdgeShift μ ν j
      then 1 else 0) else 0
private def plaquetteIncidence (x : TorusSite m) (μ ν : Fin 4) (b : TorusBond m) : ℝ :=
  ∑ i : Fin 4, orientedSign i * (if b = (x + edgeShift m μ ν i, edgeAxis μ ν i) then 1 else 0)
private def sumOverPlaquettes [NeZero m] (f : TorusSite m → Fin 4 → Fin 4 → ℝ) : ℝ :=
  ∑ x, ∑ μ : Fin 4, ∑ ν : Fin 4, if μ < ν then f x μ ν else 0
private theorem sumOverPlaquettes_finset_sum [NeZero m] {ι : Type} (s : Finset ι)
    (f : ι → TorusSite m → Fin 4 → Fin 4 → ℝ) :
    sumOverPlaquettes (fun x μ ν => ∑ i ∈ s, f i x μ ν) = ∑ i ∈ s, sumOverPlaquettes (f i) := by
  unfold sumOverPlaquettes
  have h : ∀ (x : TorusSite m) (μ ν : Fin 4), (if μ < ν then ∑ i ∈ s, f i x μ ν else 0) =
      ∑ i ∈ s, if μ < ν then f i x μ ν else 0 := by
    intro x μ ν
    split_ifs <;> simp
  simp only [h]
  symm
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [Finset.sum_comm]
private theorem sumOverPlaquettes_const_mul [NeZero m] (r : ℝ) (f : TorusSite m → Fin 4 → Fin 4 → ℝ) :
    sumOverPlaquettes (fun x μ ν => r * f x μ ν) = r * sumOverPlaquettes f := by
  unfold sumOverPlaquettes
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ => ?_
  split_ifs <;> simp
private theorem sum_indicator_mul_indicator [NeZero m] (o o' : TorusSite m) (d d' : Fin 4) (b c : TorusBond m) :
    ∑ x : TorusSite m, (if b = (x + o, d) then (1 : ℝ) else 0) * (if c = (x + o', d') then 1 else 0) =
      if d = b.2 ∧ d' = c.2 ∧ b.1 - o = c.1 - o' then 1 else 0 := by
  obtain ⟨y, β⟩ := b
  obtain ⟨z, γ⟩ := c
  rw [Finset.sum_eq_single (y - o)]
  · by_cases h1 : d = β
    · subst h1
      by_cases h2 : d' = γ
      · subst h2
        by_cases h3 : y - o = z - o'
        · have h4 : z = y - o + o' := by rw [h3]; abel
          subst h4
          simp
        · have h4 : z ≠ y - o + o' := fun h => h3 (by rw [h]; abel)
          simp [h3, h4]
      · simp [h2, Ne.symm h2]
    · simp [h1, Ne.symm h1]
  · intro x _ hx
    have : ¬ ((y, β) : TorusBond m) = (x + o, d) := by
      intro h
      apply hx
      have := congrArg Prod.fst h
      simp only at this
      rw [this]; abel
    simp [this]
  · simp
private theorem curlKernel_eq_sum [NeZero m] (b c : TorusBond m) :
    curlKernel m b c = sumOverPlaquettes fun x μ ν => plaquetteIncidence x μ ν b * plaquetteIncidence x μ ν c := by
  unfold curlKernel sumOverPlaquettes
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun μ _ => ?_
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ν _ => ?_
  by_cases h : μ < ν
  · simp only [h, if_true]
    simp only [plaquetteIncidence, Finset.sum_mul_sum]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← sum_indicator_mul_indicator, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    ring
  · simp [h]
private theorem plaquetteCurl_eq_sum [NeZero m] (ξ : RealOneForm m) (x : TorusSite m) (μ ν : Fin 4) :
    plaquetteCurl ξ x μ ν = ∑ b, plaquetteIncidence x μ ν b * ξ b := by
  simp only [plaquetteIncidence, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp only [mul_assoc, ← Finset.mul_sum, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp [Fin.sum_univ_four, plaquetteCurl, orientedSign, edgeShift, edgeAxis]
  ring
private theorem curlKernel_mulVec [NeZero m] (b : TorusBond m) (ζ : RealOneForm m) :
    ∑ c, curlKernel m b c * ζ c = sumOverPlaquettes fun x μ ν => plaquetteIncidence x μ ν b * plaquetteCurl ζ x μ ν := by
  simp only [curlKernel_eq_sum, plaquetteCurl_eq_sum, Finset.mul_sum, ← mul_assoc]
  rw [sumOverPlaquettes_finset_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [mul_comm, ← sumOverPlaquettes_const_mul]
  congr 1
  funext x μ ν
  ring
private theorem kernelPairing_curlKernel [NeZero m] (ξ ζ : RealOneForm m) :
    kernelPairing (curlKernel m) ξ ζ = sumOverPlaquettes fun x μ ν => plaquetteCurl ξ x μ ν * plaquetteCurl ζ x μ ν := by
  have h1 : kernelPairing (curlKernel m) ξ ζ = ∑ b, ξ b * ∑ c, curlKernel m b c * ζ c := by
    unfold kernelPairing
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    ring
  simp only [h1, curlKernel_mulVec, ← sumOverPlaquettes_const_mul]
  rw [← sumOverPlaquettes_finset_sum]
  congr 1
  funext x μ ν
  rw [plaquetteCurl_eq_sum ξ, Finset.sum_mul]
  refine Finset.sum_congr rfl fun b _ => ?_
  ring
private theorem curlKernel_symm [NeZero m] (b c : TorusBond m) : curlKernel m b c = curlKernel m c b := by
  rw [curlKernel_eq_sum, curlKernel_eq_sum]
  congr 1
  funext x μ ν
  ring
private theorem curlKernel_translate (u : TorusSite m) (b c : TorusBond m) :
    curlKernel m (b.1 + u, b.2) (c.1 + u, c.2) = curlKernel m b c := by
  have h : ∀ o o' : TorusSite m, (b.1 + u - o = c.1 + u - o') ↔ (b.1 - o = c.1 - o') := by
    intro o o'
    rw [add_sub_right_comm, add_sub_right_comm, add_left_inj]
  simp only [curlKernel, h]
private def oppositeEdge : Equiv.Perm (Fin 4) := ⟨![2, 3, 0, 1], ![2, 3, 0, 1], by decide, by decide⟩
private theorem edgeAxis_opposite (μ ν i : Fin 4) : edgeAxis μ ν (oppositeEdge i) = edgeAxis μ ν i := by
  fin_cases i <;> simp [edgeAxis, oppositeEdge]
private theorem orientedSign_opposite (i : Fin 4) : orientedSign (oppositeEdge i) = - orientedSign i := by
  fin_cases i <;> simp [orientedSign, oppositeEdge]
private theorem edgeShift_opposite (μ ν i : Fin 4) :
    TorusFields.unitStep m (edgeAxis μ ν i) + edgeShift m μ ν i + edgeShift m μ ν (oppositeEdge i) =
      TorusFields.unitStep m μ + TorusFields.unitStep m ν := by
  fin_cases i <;> simp [edgeAxis, edgeShift, oppositeEdge, add_comm]
private theorem curlKernel_reflect (b c : TorusBond m) :
    curlKernel m (reflectedBond b) (reflectedBond c) = curlKernel m b c := by
  obtain ⟨y, β⟩ := b
  obtain ⟨z, γ⟩ := c
  unfold curlKernel
  refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ => ?_
  split_ifs with hμν
  · conv_rhs => rw [← Equiv.sum_comp oppositeEdge]
    refine Finset.sum_congr rfl fun i _ => ?_
    conv_rhs => rw [← Equiv.sum_comp oppositeEdge]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [orientedSign_opposite, orientedSign_opposite]
    have hc : (edgeAxis μ ν i = β ∧ edgeAxis μ ν j = γ ∧
          -y - TorusFields.unitStep m β - edgeShift m μ ν i = -z - TorusFields.unitStep m γ - edgeShift m μ ν j) ↔
        (edgeAxis μ ν (oppositeEdge i) = β ∧ edgeAxis μ ν (oppositeEdge j) = γ ∧
          y - edgeShift m μ ν (oppositeEdge i) = z - edgeShift m μ ν (oppositeEdge j)) := by
      rw [edgeAxis_opposite, edgeAxis_opposite]
      have hi := edgeShift_opposite (m := m) μ ν i
      have hj := edgeShift_opposite (m := m) μ ν j
      constructor
      · rintro ⟨rfl, rfl, h⟩
        exact ⟨rfl, rfl, by linear_combination -h - hi + hj⟩
      · rintro ⟨rfl, rfl, h⟩
        exact ⟨rfl, rfl, by linear_combination -h - hi + hj⟩
    rw [neg_mul_neg]
    congr 1
    exact if_congr hc rfl rfl
  · rfl
private theorem abs_sum_fin_four_le (f : Fin 4 → ℝ) (r : ℝ) (h : ∀ i, |f i| ≤ r) : |∑ i, f i| ≤ 4 * r := by
  calc |∑ i, f i| ≤ ∑ i, |f i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin 4, r := Finset.sum_le_sum fun i _ => h i
    _ = 4 * r := by simp
private theorem edgeShift_apply_zero_or_one (μ ν i k : Fin 4) :
    edgeShift m μ ν i k = 0 ∨ edgeShift m μ ν i k = 1 := by
  fin_cases i
  · left; simp [edgeShift]
  · by_cases h : k = μ <;> simp [edgeShift, TorusFields.unitStep, Pi.single_apply, h]
  · by_cases h : k = ν <;> simp [edgeShift, TorusFields.unitStep, Pi.single_apply, h]
  · left; simp [edgeShift]
private theorem natAbs_valMinAbs_le_one [NeZero m] (a : ZMod m) (h : a = 0 ∨ a = 1 ∨ a = -1) :
    a.valMinAbs.natAbs ≤ 1 := by
  have h1 : ((1 : ZMod m)).valMinAbs.natAbs ≤ 1 := by
    rw [ZMod.valMinAbs_natAbs_eq_min]
    refine (min_le_left _ _).trans ?_
    rw [ZMod.val_one_eq_one_mod]
    exact Nat.mod_le _ _
  rcases h with rfl | rfl | rfl
  · simp
  · exact h1
  · rwa [ZMod.natAbs_valMinAbs_neg]
private theorem supDist_le_one_of_sub_eq [NeZero m] (y z o o' : TorusSite m) (ho : ∀ k, o k = 0 ∨ o k = 1)
    (ho' : ∀ k, o' k = 0 ∨ o' k = 1) (h : y - o = z - o') : supDist y z ≤ 1 := by
  unfold supDist
  refine Finset.sup_le fun k _ => natAbs_valMinAbs_le_one _ ?_
  have hk : y k - z k = o k - o' k := by
    have := congrFun h k
    simp only [Pi.sub_apply] at this
    linear_combination this
  rw [hk]
  rcases ho k with h1 | h1 <;> rcases ho' k with h2 | h2 <;> simp [h1, h2]
private theorem abs_orientedSign (i : Fin 4) : |orientedSign i| = 1 := by
  fin_cases i <;> simp [orientedSign]
private theorem abs_curlKernel_le [NeZero m] (b c : TorusBond m) :
    |curlKernel m b c| ≤ 4 * (4 * (4 * (4 * (if supDist b.1 c.1 ≤ 1 then 1 else 0)))) := by
  have hB0 : (0 : ℝ) ≤ if supDist b.1 c.1 ≤ 1 then 1 else 0 := by
    split_ifs <;> norm_num
  refine abs_sum_fin_four_le _ _ fun μ => abs_sum_fin_four_le _ _ fun ν => ?_
  by_cases h0 : μ < ν
  · rw [if_pos h0]
    refine abs_sum_fin_four_le _ _ fun i => abs_sum_fin_four_le _ _ fun j => ?_
    rw [abs_mul, abs_mul, abs_orientedSign, abs_orientedSign, one_mul, one_mul]
    by_cases h : edgeAxis μ ν i = b.2 ∧ edgeAxis μ ν j = c.2 ∧
        b.1 - edgeShift m μ ν i = c.1 - edgeShift m μ ν j
    · rw [if_pos h, if_pos (supDist_le_one_of_sub_eq _ _ _ _ (edgeShift_apply_zero_or_one μ ν i)
        (edgeShift_apply_zero_or_one μ ν j) h.2.2)]
      simp
    · rw [if_neg h, abs_zero]
      exact hB0
  · rw [if_neg h0, abs_zero]
    positivity
private theorem edgeShift_eq_siteOfInt (μ ν i : Fin 4) : edgeShift m μ ν i = siteOfInt (latticeEdgeShift μ ν i) := by
  funext k
  fin_cases i
  · simp [edgeShift, latticeEdgeShift, siteOfInt]
  · by_cases h : k = μ <;> simp [edgeShift, latticeEdgeShift, siteOfInt, TorusFields.unitStep, Pi.single_apply, h]
  · by_cases h : k = ν <;> simp [edgeShift, latticeEdgeShift, siteOfInt, TorusFields.unitStep, Pi.single_apply, h]
  · simp [edgeShift, latticeEdgeShift, siteOfInt]
private theorem siteOfInt_sub (z w : Fin 4 → ℤ) : (siteOfInt (z - w) : TorusSite m) = siteOfInt z - siteOfInt w := by apply _root_.YangMills.Construction.SlopeCoefficient.Pullback.siteOfInt_sub <;> assumption
private theorem eventually_siteOfInt_eq_iff (z w : Fin 4 → ℤ) :
    ∀ᶠ m : ℕ in Filter.atTop, ((siteOfInt z : TorusSite m) = siteOfInt w ↔ z = w) := by
  by_cases h : z = w
  · subst h
    simp
  · obtain ⟨k, hk⟩ := Function.ne_iff.mp h
    filter_upwards [Filter.eventually_gt_atTop (w k - z k).natAbs] with m hm
    refine ⟨fun e => ?_, fun e => absurd e h⟩
    exfalso
    have h1 : ((z k : ℤ) : ZMod m) = ((w k : ℤ) : ZMod m) := congrFun e k
    rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at h1
    have h2 := Int.eq_zero_of_abs_lt_dvd h1 (by rw [Int.abs_eq_natAbs]; exact_mod_cast hm)
    exact hk (by omega)
private theorem tendsto_curlKernel (b c : LatticeBond) :
    Filter.Tendsto (fun m => curlKernel m (bondFrom 0 b) (bondFrom 0 c)) Filter.atTop
      (𝓝 (latticeCurlKernel b c)) := by
  have h : ∀ᶠ m : ℕ in Filter.atTop, ∀ μ ν i j : Fin 4,
      ((siteOfInt (b.1 - latticeEdgeShift μ ν i) : TorusSite m) = siteOfInt (c.1 - latticeEdgeShift μ ν j) ↔
        b.1 - latticeEdgeShift μ ν i = c.1 - latticeEdgeShift μ ν j) := by
    simp only [Filter.eventually_all]
    exact fun μ ν i j => eventually_siteOfInt_eq_iff _ _
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [h] with m hm
  simp only [curlKernel, latticeCurlKernel, bondFrom, zero_add, edgeShift_eq_siteOfInt, ← siteOfInt_sub, hm]
private theorem plaquetteCurl_gradient (φ : TorusSite m → ℝ) (x : TorusSite m) (μ ν : Fin 4) :
    plaquetteCurl (fun c : TorusBond m => φ (c.1 + TorusFields.unitStep m c.2) - φ c.1) x μ ν = 0 := by
  simp only [plaquetteCurl]
  rw [add_right_comm x (TorusFields.unitStep m ν) (TorusFields.unitStep m μ)]
  ring
private theorem plaquetteCurl_constant (d : Fin 4) (x : TorusSite m) (μ ν : Fin 4) :
    plaquetteCurl (fun c : TorusBond m => if c.2 = d then (1 : ℝ) else 0) x μ ν = 0 := by
  simp only [plaquetteCurl]
  ring
private theorem sumOverPlaquettes_zero (m : ℕ) [NeZero m] :
    sumOverPlaquettes (fun (_ : TorusSite m) _ _ => (0 : ℝ)) = (0 : ℝ) := by
  simp [sumOverPlaquettes]
private theorem curlKernel_isFlowKernel : IsFlowKernel curlKernel where
  symm := by
    filter_upwards [Filter.eventually_gt_atTop 0] with m hm b c
    haveI : NeZero m := ⟨hm.ne'⟩
    exact curlKernel_symm b c
  decay := by
    refine ⟨256 * Real.exp 1, 1, one_pos, ?_⟩
    filter_upwards [Filter.eventually_gt_atTop 0] with m hm b c
    haveI : NeZero m := ⟨hm.ne'⟩
    have h := abs_curlKernel_le b c
    by_cases hd : supDist b.1 c.1 ≤ 1
    · rw [if_pos hd] at h
      have h1 : (supDist b.1 c.1 : ℝ) ≤ 1 := by exact_mod_cast hd
      have h2 : 1 ≤ Real.exp 1 * Real.exp (-(1 * (supDist b.1 c.1 : ℝ))) := by
        rw [← Real.exp_add]
        exact Real.one_le_exp (by linarith)
      nlinarith
    · rw [if_neg hd] at h
      have : 0 ≤ 256 * Real.exp 1 * Real.exp (-(1 * (supDist b.1 c.1 : ℝ))) := by positivity
      linarith
  translation_invariant := Filter.Eventually.of_forall fun _ u b c => curlKernel_translate u b c
  reflection_invariant := Filter.Eventually.of_forall fun _ b c => curlKernel_reflect b c
  annihilates_gradients := by
    refine Filter.Eventually.of_forall ?_
    intro m _ b φ
    rw [curlKernel_mulVec b (fun c => φ (c.1 + TorusFields.unitStep m c.2) - φ c.1)]
    simp only [plaquetteCurl_gradient, mul_zero]
    exact sumOverPlaquettes_zero m
  annihilates_constants := by
    refine Filter.Eventually.of_forall ?_
    intro m _ b d
    rw [curlKernel_mulVec b (fun c => if c.2 = d then (1 : ℝ) else 0)]
    simp only [plaquetteCurl_constant, mul_zero]
    exact sumOverPlaquettes_zero m
  tendsto := ⟨latticeCurlKernel, tendsto_curlKernel⟩
  curl_lower_bound := by
    refine ⟨1, one_pos, Filter.Eventually.of_forall ?_⟩
    intro m _ ξ
    rw [kernelPairing_curlKernel, one_mul]
    simp only [curlEnergy, sumOverPlaquettes, sq, le_refl]
private def SecondOrderJet (f : ℝ → ℍ[ℝ]) (a b : ℍ[ℝ]) : Prop :=
  ∃ f' : ℝ → ℍ[ℝ], (∀ t, HasDerivAt f (f' t) t) ∧ HasDerivAt f' b 0 ∧ f 0 = 1 ∧ f' 0 = a
private theorem secondOrderJet_exp (Y : ℍ[ℝ]) : SecondOrderJet (fun t => NormedSpace.exp (t • Y)) Y (Y * Y) := by
  refine ⟨fun t => NormedSpace.exp (t • Y) * Y, fun t => hasDerivAt_exp_smul_const Y t, ?_, by simp, by simp⟩
  simpa using (hasDerivAt_exp_smul_const Y (0 : ℝ)).mul_const Y
private def reCLM : ℍ[ℝ] →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun q => q.re, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => by simp }
private def starCLM : ℍ[ℝ] →L[ℝ] ℍ[ℝ] :=
  LinearMap.toContinuousLinearMap
    { toFun := star, map_add' := star_add, map_smul' := fun c q => by ext <;> simp }
private theorem secondOrderJet_star {f : ℝ → ℍ[ℝ]} {a b : ℍ[ℝ]} (h : SecondOrderJet f a b) :
    SecondOrderJet (fun t => star (f t)) (star a) (star b) := by
  obtain ⟨f', h1, h2, h3, h4⟩ := h
  exact ⟨fun t => star (f' t), fun t => starCLM.hasFDerivAt.comp_hasDerivAt t (h1 t),
    starCLM.hasFDerivAt.comp_hasDerivAt 0 h2, by simp [h3], by simp [h4]⟩
private theorem secondOrderJet_mul {f g : ℝ → ℍ[ℝ]} {a b c d : ℍ[ℝ]} (hf : SecondOrderJet f a b)
    (hg : SecondOrderJet g c d) :
    SecondOrderJet (fun t => f t * g t) (a + c) (b + a * c + a * c + d) := by
  obtain ⟨f', f1, f2, f3, f4⟩ := hf
  obtain ⟨g', g1, g2, g3, g4⟩ := hg
  refine ⟨fun t => f' t * g t + f t * g' t, fun t => (f1 t).mul (g1 t), ?_, by simp [f3, g3],
    by simp [f3, f4, g3, g4]⟩
  have h := (f2.mul (g1 0)).add ((f1 0).mul g2)
  have e : b * g 0 + f' 0 * g' 0 + (f' 0 * g' 0 + f 0 * d) = b + a * c + a * c + d := by
    rw [f3, f4, g3, g4]
    simp only [mul_one, one_mul]
    abel
  rw [e] at h
  exact h
private theorem re_neg_jet_eq_inner (y₀ y₁ y₂ y₃ : ℍ[ℝ]) (h₀ : y₀.re = 0) (h₁ : y₁.re = 0) (h₂ : y₂.re = 0)
    (h₃ : y₃.re = 0) :
    -(y₀ * y₀ + y₀ * y₁ + y₀ * y₁ + y₁ * y₁ + (y₀ + y₁) * star y₂ + (y₀ + y₁) * star y₂ + star (y₂ * y₂) +
        (y₀ + y₁ + star y₂) * star y₃ + (y₀ + y₁ + star y₂) * star y₃ + star (y₃ * y₃)).re =
      inner ℝ (y₀ + y₁ - y₂ - y₃) (y₀ + y₁ - y₂ - y₃) := by
  rw [Quaternion.inner_def]
  simp [h₀, h₁, h₂, h₃]
  ring
private theorem inner_smul_add_self (u v : ℝ) (X₀ X₁ : ℍ[ℝ]) :
    inner ℝ (u • X₀ + v • X₁) (u • X₀ + v • X₁) =
      u ^ 2 * inner ℝ X₀ X₀ + 2 * (u * v) * inner ℝ X₀ X₁ + v ^ 2 * inner ℝ X₁ X₁ := by
  simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right, real_inner_comm X₀ X₁]
  simp
  ring
private def lineDirection (c₀ c₁ : TorusBond m) (X₀ X₁ : imaginaryQuaternions) (w : Fin 2 → ℝ)
    (b : TorusBond m) : ℍ[ℝ] :=
  (if c₀ = b then w 0 • (X₀ : ℍ[ℝ]) else 0) + (if c₁ = b then w 1 • (X₁ : ℍ[ℝ]) else 0)
private theorem lineDirection_re (c₀ c₁ : TorusBond m) (X₀ X₁ : imaginaryQuaternions) (w : Fin 2 → ℝ)
    (b : TorusBond m) : (lineDirection c₀ c₁ X₀ X₁ w b).re = 0 := by
  have h₀ : (X₀ : ℍ[ℝ]).re = 0 := X₀.2
  have h₁ : (X₁ : ℍ[ℝ]).re = 0 := X₁.2
  unfold lineDirection
  split_ifs <;> simp [h₀, h₁]
private theorem coe_perturb_line (c₀ c₁ : TorusBond m) (X₀ X₁ : imaginaryQuaternions) (w : Fin 2 → ℝ) (t : ℝ)
    (x : TorusSite m) (i : Fin 4) :
    ((perturb ![c₀, c₁] ![X₀, X₁] (t • w) (trivialField m) x i : UnitQuaternion) : ℍ[ℝ]) =
      NormedSpace.exp (t • lineDirection c₀ c₁ X₀ X₁ w (x, i)) := by
  have h : perturb ![c₀, c₁] ![X₀, X₁] (t • w) (trivialField m) x i =
      expUnit (∑ l, if ![c₀, c₁] l = (x, i) then (t • w) l • ![X₀, X₁] l else 0) := by
    simp [perturb, trivialField]
  rw [h]
  show NormedSpace.exp _ = _
  congr 1
  simp only [Fin.sum_univ_two, lineDirection]
  by_cases h0 : c₀ = (x, i) <;> by_cases h1 : c₁ = (x, i) <;> simp [h0, h1, mul_smul, smul_add]
private theorem coe_inv_unitQuaternion (g : UnitQuaternion) : ((g⁻¹ : UnitQuaternion) : ℍ[ℝ]) = star (g : ℍ[ℝ]) := by
  rw [← Unitary.star_eq_inv, Unitary.coe_star]
private theorem plaquetteIncidence_eq (x : TorusSite m) (μ ν : Fin 4) (b : TorusBond m) :
    plaquetteIncidence x μ ν b = (if b = (x, μ) then 1 else 0) + (if b = (x + TorusFields.unitStep m μ, ν) then 1 else 0) -
      (if b = (x + TorusFields.unitStep m ν, μ) then 1 else 0) - (if b = (x, ν) then 1 else 0) := by
  have s₀ : orientedSign 0 = 1 := by simp [orientedSign]
  have s₁ : orientedSign 1 = 1 := by simp [orientedSign]
  have s₂ : orientedSign 2 = -1 := by simp [orientedSign]
  have s₃ : orientedSign 3 = -1 := by simp [orientedSign]
  have o₀ : x + edgeShift m μ ν 0 = x := by simp [edgeShift]
  have o₁ : edgeShift m μ ν 1 = TorusFields.unitStep m μ := by simp [edgeShift]
  have o₂ : edgeShift m μ ν 2 = TorusFields.unitStep m ν := by simp [edgeShift]
  have o₃ : x + edgeShift m μ ν 3 = x := by simp [edgeShift]
  have d₀ : edgeAxis μ ν 0 = μ := by simp [edgeAxis]
  have d₁ : edgeAxis μ ν 1 = ν := by simp [edgeAxis]
  have d₂ : edgeAxis μ ν 2 = μ := by simp [edgeAxis]
  have d₃ : edgeAxis μ ν 3 = ν := by simp [edgeAxis]
  simp only [plaquetteIncidence, Fin.sum_univ_four]
  rw [s₀, s₁, s₂, s₃, o₀, o₁, o₂, o₃, d₀, d₁, d₂, d₃]
  ring
private theorem lineDirection_curl (c₀ c₁ : TorusBond m) (X₀ X₁ : imaginaryQuaternions) (w : Fin 2 → ℝ)
    (x : TorusSite m) (μ ν : Fin 4) :
    lineDirection c₀ c₁ X₀ X₁ w (x, μ) + lineDirection c₀ c₁ X₀ X₁ w (x + TorusFields.unitStep m μ, ν) -
        lineDirection c₀ c₁ X₀ X₁ w (x + TorusFields.unitStep m ν, μ) - lineDirection c₀ c₁ X₀ X₁ w (x, ν) =
      (w 0 * plaquetteIncidence x μ ν c₀) • (X₀ : ℍ[ℝ]) + (w 1 * plaquetteIncidence x μ ν c₁) • (X₁ : ℍ[ℝ]) := by
  have e : ∀ (c b : TorusBond m) (v : ℍ[ℝ]), (if c = b then v else 0) = (if c = b then (1 : ℝ) else 0) • v := by
    intro c b v
    split_ifs <;> simp
  simp only [lineDirection, plaquetteIncidence_eq]
  simp only [e _ _ (w 0 • (X₀ : ℍ[ℝ])), e _ _ (w 1 • (X₁ : ℍ[ℝ]))]
  module
private def lineHessian (c₀ c₁ : TorusBond m) (X₀ X₁ : imaginaryQuaternions) (w : Fin 2 → ℝ) (x : TorusSite m)
    (μ ν : Fin 4) : ℝ :=
  (w 0 * plaquetteIncidence x μ ν c₀) ^ 2 * inner ℝ (X₀ : ℍ[ℝ]) (X₀ : ℍ[ℝ]) +
    2 * ((w 0 * plaquetteIncidence x μ ν c₀) * (w 1 * plaquetteIncidence x μ ν c₁)) *
      inner ℝ (X₀ : ℍ[ℝ]) (X₁ : ℍ[ℝ]) +
    (w 1 * plaquetteIncidence x μ ν c₁) ^ 2 * inner ℝ (X₁ : ℍ[ℝ]) (X₁ : ℍ[ℝ])
private theorem plaquetteEnergy_hasDerivAt_line (c₀ c₁ : TorusBond m) (X₀ X₁ : imaginaryQuaternions)
    (w : Fin 2 → ℝ) (x : TorusSite m) (μ ν : Fin 4) :
    ∃ f' : ℝ → ℝ,
      (∀ t, HasDerivAt (fun t : ℝ => plaquetteEnergy (perturb ![c₀, c₁] ![X₀, X₁] (t • w) (trivialField m)) x μ ν)
        (f' t) t) ∧
      HasDerivAt f' (lineHessian c₀ c₁ X₀ X₁ w x μ ν) 0 := by
  set y₀ := lineDirection c₀ c₁ X₀ X₁ w (x, μ) with hy₀
  set y₁ := lineDirection c₀ c₁ X₀ X₁ w (x + TorusFields.unitStep m μ, ν) with hy₁
  set y₂ := lineDirection c₀ c₁ X₀ X₁ w (x + TorusFields.unitStep m ν, μ) with hy₂
  set y₃ := lineDirection c₀ c₁ X₀ X₁ w (x, ν) with hy₃
  obtain ⟨f', h1, h2, -, -⟩ := secondOrderJet_mul (secondOrderJet_mul (secondOrderJet_mul (secondOrderJet_exp y₀)
    (secondOrderJet_exp y₁)) (secondOrderJet_star (secondOrderJet_exp y₂))) (secondOrderJet_star (secondOrderJet_exp y₃))
  have hf : (fun t : ℝ => plaquetteEnergy (perturb ![c₀, c₁] ![X₀, X₁] (t • w) (trivialField m)) x μ ν) = fun t =>
      1 - reCLM (NormedSpace.exp (t • y₀) * NormedSpace.exp (t • y₁) * star (NormedSpace.exp (t • y₂)) *
        star (NormedSpace.exp (t • y₃))) := by
    funext t
    unfold plaquetteEnergy holonomy
    simp only [Submonoid.coe_mul, coe_inv_unitQuaternion, coe_perturb_line]
    rfl
  rw [hf]
  refine ⟨fun t => - reCLM (f' t), fun t => ?_, ?_⟩
  · exact (reCLM.hasFDerivAt.comp_hasDerivAt t (h1 t)).const_sub 1
  · have h3 := (reCLM.hasFDerivAt.comp_hasDerivAt 0 h2).neg
    have e := re_neg_jet_eq_inner y₀ y₁ y₂ y₃ (lineDirection_re ..) (lineDirection_re ..) (lineDirection_re ..)
      (lineDirection_re ..)
    rw [hy₀, hy₁, hy₂, hy₃, lineDirection_curl, inner_smul_add_self, ← hy₀, ← hy₁, ← hy₂, ← hy₃] at e
    exact h3.congr_deriv e
private theorem fderiv_fderiv_apply_self_of_line {G : (Fin 2 → ℝ) → ℝ} (hG : ContDiff ℝ ⊤ G) (w : Fin 2 → ℝ)
    (f' : ℝ → ℝ) (r : ℝ) (h1 : ∀ t, HasDerivAt (fun t : ℝ => G (t • w)) (f' t) t) (h2 : HasDerivAt f' r 0) :
    fderiv ℝ (fderiv ℝ G) 0 w w = r := by
  have hd : Differentiable ℝ G := hG.differentiable (by simp)
  have hd2 : Differentiable ℝ (fderiv ℝ G) :=
    (hG.fderiv_right (m := ⊤) (by simp)).differentiable (by simp)
  have hline : ∀ t : ℝ, HasDerivAt (fun t : ℝ => t • w) w t := fun t => by
    simpa using (hasDerivAt_id t).smul_const w
  have h3 : ∀ t, f' t = fderiv ℝ G (t • w) w := fun t =>
    (h1 t).unique ((hd (t • w)).hasFDerivAt.comp_hasDerivAt t (hline t))
  have h4 : HasDerivAt (fun t : ℝ => fderiv ℝ G (t • w) w) (fderiv ℝ (fderiv ℝ G) 0 w w) 0 := by
    have a1 : HasDerivAt (fun t : ℝ => fderiv ℝ G (t • w)) (fderiv ℝ (fderiv ℝ G) 0 w) 0 := by
      have h0 : HasFDerivAt (fderiv ℝ G) (fderiv ℝ (fderiv ℝ G) ((0 : ℝ) • w)) ((0 : ℝ) • w) :=
        (hd2 _).hasFDerivAt
      have := h0.comp_hasDerivAt (0 : ℝ) (hline 0)
      rw [zero_smul] at this
      exact this
    simpa using a1.clm_apply (hasDerivAt_const (0 : ℝ) w)
  rw [show f' = fun t => fderiv ℝ G (t • w) w from funext h3] at h2
  exact h4.unique h2
private theorem fderiv_fderiv_apply_polarization {G : (Fin 2 → ℝ) → ℝ} (hG : ContDiff ℝ ⊤ G) (u v : Fin 2 → ℝ) :
    fderiv ℝ (fderiv ℝ G) 0 u v = (fderiv ℝ (fderiv ℝ G) 0 (u + v) (u + v) -
      fderiv ℝ (fderiv ℝ G) 0 u u - fderiv ℝ (fderiv ℝ G) 0 v v) / 2 := by
  have hs := (hG.contDiffAt (x := 0)).isSymmSndFDerivAt le_top
  have := hs u v
  simp only [map_add, ContinuousLinearMap.add_apply]
  rw [this]
  ring
private theorem minimalActionTotal_eq_sum [NeZero m] (a : ℝ) (L : ℕ) (V : TorusField m) :
    minimalActionTotal a L 0 m V = ∑ p ∈ plaquettesIn Finset.univ, plaquetteEnergy V p.1 p.2.1 p.2.2 := by
  unfold minimalActionTotal
  rw [dif_neg (NeZero.ne m)]
  rfl
private theorem sum_plaquettesIn_eq [NeZero m] (f : TorusPlaquette m → ℝ) :
    ∑ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite m)), f p = sumOverPlaquettes fun x μ ν => f (x, μ, ν) := by
  unfold plaquettesIn sumOverPlaquettes
  rw [Finset.sum_filter]
  simp only [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ => ?_
  simp
private theorem hasHessianAtTrivial_curlKernel [NeZero m] (hE : WeightedResponses.PlaquetteEnergySmoothBound)
    (a : ℝ) (L : ℕ) : HasHessianAtTrivial (minimalActionTotal a L 0) (curlKernel m) := by
  obtain ⟨M, -, hM⟩ := hE
  have hs : ∀ (k : ℕ) (c : Fin k → TorusBond m) (X : Fin k → imaginaryQuaternions),
      ContDiff ℝ ⊤ (fun σ : Fin k → ℝ => minimalActionTotal a L 0 m (perturb c X σ (trivialField m))) := by
    intro k c X
    simp only [minimalActionTotal_eq_sum]
    exact ContDiff.sum fun p _ => (hM m k (trivialField m) p.1 p.2.1 p.2.2 c X).1
  refine ⟨fun r k c X => ((hs k c X).of_le le_top).contDiffAt, fun c c' X X' => ?_⟩
  set G : (Fin 2 → ℝ) → ℝ := fun σ => minimalActionTotal a L 0 m (perturb ![c, c'] ![X, X'] σ (trivialField m))
    with hGdef
  have hG : ContDiff ℝ ⊤ G := hs 2 ![c, c'] ![X, X']
  have hw : ∀ w : Fin 2 → ℝ, fderiv ℝ (fderiv ℝ G) 0 w w =
      ∑ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite m)), lineHessian c c' X X' w p.1 p.2.1 p.2.2 := by
    intro w
    choose f' h1 h2 using fun p : TorusPlaquette m => plaquetteEnergy_hasDerivAt_line c c' X X' w p.1 p.2.1 p.2.2
    refine fderiv_fderiv_apply_self_of_line hG w
      (fun t => ∑ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite m)), f' p t) _ (fun t => ?_) ?_
    · simp only [hGdef, minimalActionTotal_eq_sum]
      exact HasDerivAt.fun_sum fun p _ => h1 p t
    · exact HasDerivAt.fun_sum fun p _ => h2 p
  have hK : curlKernel m c c' = ∑ p ∈ plaquettesIn (Finset.univ : Finset (TorusSite m)),
      plaquetteIncidence p.1 p.2.1 p.2.2 c * plaquetteIncidence p.1 p.2.1 p.2.2 c' := by
    rw [curlKernel_eq_sum, sum_plaquettesIn_eq]
  show iteratedFDeriv ℝ 2 G 0 (fun l => Pi.single l 1) = _
  rw [iteratedFDeriv_two_apply, fderiv_fderiv_apply_polarization hG, hw, hw, hw, hK, ← Finset.sum_sub_distrib,
    ← Finset.sum_sub_distrib, Finset.sum_div, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp [lineHessian]
  ring
theorem wilsonActionHasFlowKernel_of_plaquetteEnergySmoothBound
    (hE : WeightedResponses.PlaquetteEnergySmoothBound) : WilsonActionHasFlowKernel := by
  intro a _ L _
  refine ⟨curlKernel, curlKernel_isFlowKernel, ?_⟩
  filter_upwards [Filter.eventually_gt_atTop 0] with m hm
  have : NeZero m := ⟨hm.ne'⟩
  exact hasHessianAtTrivial_curlKernel hE a L
end YangMills.Construction.RunningCouplingSlope
end
