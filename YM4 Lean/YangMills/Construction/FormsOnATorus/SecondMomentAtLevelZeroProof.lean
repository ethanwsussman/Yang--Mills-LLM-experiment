import YangMills.Construction.ClusterExpansionOfAStep.ImageStateKeepsTranslationsProof
import YangMills.Construction.ClusterExpansionOfAStep.OffsetsOfABlock
import YangMills.Construction.FormsOnATorus.KernelOfTheCurlOnABoxProof
import YangMills.Construction.FormsOnATorus.SecondMomentAtLevelZero
import YangMills.Construction.RunningCouplingSlope.ContoursAtTheLeastFieldHaveKernelsProof
import Mathlib
set_option autoImplicit false
noncomputable section
open Filter Topology
open scoped Quaternion
namespace YangMills.Construction.LimitForms
open TorusFields TorusLumps ColdStepAtMirrorFrames ResponseInTheExpansion
open BlockAverages hiding unitStep wilsonAction
variable {n : ℕ}
private def incidence (e : TorusBond n) (x : TorusSite n) (μ ν : Fin 4) : ℝ :=
  (if e = (x, μ) then 1 else 0) + (if e = (x + unitStep n μ, ν) then 1 else 0) -
    (if e = (x + unitStep n ν, μ) then 1 else 0) - (if e = (x, ν) then 1 else 0)
private lemma norm_imaginaryUnitI : ‖BoxGaussian.imaginaryUnitI‖ = 1 := by apply _root_.YangMills.SharedProofs.p16675 <;> assumption
private lemma plaquetteEnergy_perturb (c : Fin 2 → TorusBond n) (s : Fin 2 → ℝ) (x : TorusSite n) (μ ν : Fin 4) :
    plaquetteEnergy (perturb c ![BoxGaussian.imaginaryUnitI, BoxGaussian.imaginaryUnitI] s (trivialField n)) x μ ν =
      1 - Real.cos (s 0 * incidence (c 0) x μ ν + s 1 * incidence (c 1) x μ ν) := by
  have hX := norm_imaginaryUnitI
  let θ : TorusBond n → ℝ := fun e => (if c 0 = e then s 0 else 0) + (if c 1 = e then s 1 else 0)
  have hb : ∀ (y : TorusSite n) (k : Fin 4),
      perturb c ![BoxGaussian.imaginaryUnitI, BoxGaussian.imaginaryUnitI] s (trivialField n) y k =
        expUnit (θ (y, k) • BoxGaussian.imaginaryUnitI) := by
    intro y k
    simp only [perturb, trivialField, mul_one, Fin.sum_univ_two, θ, add_smul, ite_smul, zero_smul]
    simp
  have hp : holonomy (perturb c ![BoxGaussian.imaginaryUnitI, BoxGaussian.imaginaryUnitI] s (trivialField n)) x μ ν =
      expUnit ((θ (x, μ) + θ (x + unitStep n μ, ν) + -θ (x + unitStep n ν, μ) + -θ (x, ν)) •
        BoxGaussian.imaginaryUnitI) := by
    unfold holonomy
    rw [hb, hb, hb, hb, inv_expUnit_smul hX, inv_expUnit_smul hX, expUnit_smul_mul hX, expUnit_smul_mul hX,
      expUnit_smul_mul hX]
  have he : θ (x, μ) + θ (x + unitStep n μ, ν) + -θ (x + unitStep n ν, μ) + -θ (x, ν) =
      s 0 * incidence (c 0) x μ ν + s 1 * incidence (c 1) x μ ν := by
    simp only [θ, incidence]
    split_ifs <;> ring
  unfold plaquetteEnergy
  rw [hp, he, coe_expUnit_smul hX]
  have hr : ((BoxGaussian.imaginaryUnitI : imaginaryQuaternions) : ℍ[ℝ]).re = 0 := BoxGaussian.imaginaryUnitI.2
  simp [hr]
private lemma iteratedFDeriv_one_sub_cos_linear (α β : ℝ) :
    iteratedFDeriv ℝ 2 (fun s : Fin 2 → ℝ => 1 - Real.cos (s 0 * α + s 1 * β)) 0 (fun l => Pi.single l 1) =
      α * β := by
  let Λ : (Fin 2 → ℝ) →L[ℝ] ℝ :=
    α • (ContinuousLinearMap.proj 0 : (Fin 2 → ℝ) →L[ℝ] ℝ) + β • (ContinuousLinearMap.proj 1 : (Fin 2 → ℝ) →L[ℝ] ℝ)
  have hφ : ContDiff ℝ 2 (fun t : ℝ => 1 - Real.cos t) := contDiff_const.sub Real.contDiff_cos
  have e : (fun s : Fin 2 → ℝ => 1 - Real.cos (s 0 * α + s 1 * β)) = (fun t : ℝ => 1 - Real.cos t) ∘ Λ := by
    funext s
    simp [Λ, mul_comm]
  rw [e, Λ.iteratedFDeriv_comp_right hφ 0 (by norm_num)]
  rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  rw [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod]
  have d1 : deriv (fun t : ℝ => 1 - Real.cos t) = Real.sin := by
    funext t
    simp
  have d2 : iteratedDeriv 2 (fun t : ℝ => 1 - Real.cos t) (Λ 0) = 1 := by
    rw [iteratedDeriv_succ, iteratedDeriv_one, d1]
    simp
  rw [d2]
  simp [Λ, Fin.prod_univ_two]
private lemma mixedDeriv_wilsonAction_eq [NeZero n] (S : Finset (TorusSite n)) (c : Fin 2 → TorusBond n) :
    mixedDeriv (wilsonAction S) (trivialField n) c ![BoxGaussian.imaginaryUnitI, BoxGaussian.imaginaryUnitI] =
      ∑ p ∈ plaquettesIn S, incidence (c 0) p.1 p.2.1 p.2.2 * incidence (c 1) p.1 p.2.1 p.2.2 := by
  unfold mixedDeriv wilsonAction
  simp only [plaquetteEnergy_perturb]
  rw [iteratedFDeriv_sum (fun p _ => by fun_prop)]
  simp only [Finset.sum_apply, sum_apply]
  exact Finset.sum_congr rfl fun p _ => iteratedFDeriv_one_sub_cos_linear _ _
private lemma natAbs_valMinAbs_intCast_le [NeZero n] (a : ℤ) : ((a : ZMod n).valMinAbs).natAbs ≤ a.natAbs := by apply _root_.YangMills.Construction.TorusFields.natAbs_valMinAbs_intCast_le <;> assumption
private lemma supDist_siteOfInt_le [NeZero n] (v : Fin 4 → ℤ) (N : ℕ) (h : ∀ l, (v l).natAbs ≤ N) :
    supDist (siteOfInt v : TorusSite n) 0 ≤ N :=
  Finset.sup_le fun l _ => by
    simpa [siteOfInt] using (natAbs_valMinAbs_intCast_le (n := n) (v l)).trans (h l)
private lemma siteOfInt_add_eq (a b : Fin 4 → ℤ) : (siteOfInt (a + b) : TorusSite n) = siteOfInt a + siteOfInt b := by apply _root_.YangMills.Construction.BlockOffsets.siteOfInt_add <;> assumption
private lemma siteOfInt_zero_eq : (siteOfInt 0 : TorusSite n) = 0 := by
  funext l; simp [siteOfInt]
private lemma siteOfInt_single (m : Fin 4) : (siteOfInt (Pi.single m 1) : TorusSite n) = unitStep n m := by apply _root_.YangMills.Construction.FrameTorusAction.siteOfInt_single <;> assumption
private lemma siteOfInt_neg (a : Fin 4 → ℤ) : (siteOfInt (-a) : TorusSite n) = - siteOfInt a := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.TranslationInvariance.siteOfInt_neg <;> assumption
private lemma natAbs_single_le (m l : Fin 4) : ((Pi.single m 1 : Fin 4 → ℤ) l).natAbs ≤ 1 := by apply _root_.YangMills.SharedProofs.p6300 <;> assumption
private lemma plaquetteVertices_mem_supBall [NeZero n] (N : ℕ) (hN : 3 ≤ N) (v : Fin 4 → ℤ)
    (hv : ∀ l, (v l).natAbs ≤ 1) (μ ν : Fin 4) :
    ∀ z ∈ plaquetteVertices (siteOfInt v : TorusSite n) μ ν, z ∈ supBall (0 : TorusSite n) N := by
  have key : ∀ w : Fin 4 → ℤ, (∀ l, (w l).natAbs ≤ 3) → (siteOfInt w : TorusSite n) ∈ supBall (0 : TorusSite n) N := by
    intro w hw
    simp only [supBall, Finset.mem_filter, Finset.mem_univ, true_and]
    have := supDist_siteOfInt_le (n := n) w 3 hw
    have h2 : (supDist (siteOfInt w : TorusSite n) 0 : ℝ) ≤ 3 := by exact_mod_cast this
    have h3 : (3 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  intro z hz
  simp only [plaquetteVertices, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl
  · exact key v fun l => (hv l).trans (by norm_num)
  · rw [← siteOfInt_single, ← siteOfInt_add_eq]
    refine key _ fun l => ?_
    have := Int.natAbs_add_le (v l) ((Pi.single μ 1 : Fin 4 → ℤ) l)
    have h1 := hv l
    have h2 := natAbs_single_le μ l
    simp only [Pi.add_apply]
    omega
  · rw [← siteOfInt_single, ← siteOfInt_add_eq]
    refine key _ fun l => ?_
    have := Int.natAbs_add_le (v l) ((Pi.single ν 1 : Fin 4 → ℤ) l)
    have h1 := hv l
    have h2 := natAbs_single_le ν l
    simp only [Pi.add_apply]
    omega
  · rw [← siteOfInt_single, ← siteOfInt_single, ← siteOfInt_add_eq, ← siteOfInt_add_eq]
    refine key _ fun l => ?_
    have a1 := Int.natAbs_add_le ((v + Pi.single μ 1 : Fin 4 → ℤ) l) ((Pi.single ν 1 : Fin 4 → ℤ) l)
    have a2 := Int.natAbs_add_le (v l) ((Pi.single μ 1 : Fin 4 → ℤ) l)
    have h1 := hv l
    have h2 := natAbs_single_le ν l
    have h3 := natAbs_single_le μ l
    simp only [Pi.add_apply] at a1 ⊢
    omega
private lemma incidence_eq (y x : TorusSite n) (i μ ν : Fin 4) (h : μ ≠ ν) :
    incidence (y, i) x μ ν =
      (if i = μ then ((if y = x then 1 else 0) - (if y = x + unitStep n ν then 1 else 0)) else 0) +
      (if i = ν then ((if y = x + unitStep n μ then 1 else 0) - (if y = x then 1 else 0)) else 0) := by
  unfold incidence
  simp only [Prod.mk.injEq]
  by_cases h1 : i = μ
  · subst h1
    simp [h]
  · by_cases h2 : i = ν
    · subst h2
      simp [h1]
    · simp [h1, h2]
open Classical in
private def planeProfile (y : TorusSite n) (m : Fin 4) : ℝ :=
  2 * (if y = 0 then 1 else 0) - (if y = unitStep n m then 1 else 0) - (if y = - unitStep n m then 1 else 0)
private lemma sum_indicator_sub_mul [NeZero n] (g : TorusSite n → ℝ) (e : TorusSite n) :
    ∑ x, ((if (0 : TorusSite n) = x then 1 else 0) - (if (0 : TorusSite n) = x + e then 1 else 0)) * g x =
      g 0 - g (-e) := by
  have h2 : ∀ x : TorusSite n, ((0 : TorusSite n) = x + e) ↔ x = -e := fun x => by
    rw [eq_comm, add_eq_zero_iff_eq_neg]
  simp only [sub_mul, ite_mul, one_mul, zero_mul, Finset.sum_sub_distrib, h2]
  simp
open Classical in
private lemma sum_incidence_mul_plane [NeZero n] (N : ℕ) (hN : 3 ≤ N) (y : TorusSite n) (i μ ν : Fin 4)
    (hμν : μ < ν) :
    ∑ x : TorusSite n, (if (∀ z ∈ plaquetteVertices x μ ν, z ∈ supBall (0 : TorusSite n) N) then
        incidence ((0 : TorusSite n), i) x μ ν * incidence (y, i) x μ ν else 0) =
      if μ = i then planeProfile y ν else if ν = i then planeProfile y μ else 0 := by
  have hne : μ ≠ ν := ne_of_lt hμν
  have ok0 : ∀ a b : Fin 4, ∀ z ∈ plaquetteVertices (0 : TorusSite n) a b, z ∈ supBall (0 : TorusSite n) N := by
    intro a b
    have := plaquetteVertices_mem_supBall (n := n) N hN 0 (by simp) a b
    rwa [siteOfInt_zero_eq] at this
  have ok1 : ∀ m a b : Fin 4, ∀ z ∈ plaquetteVertices (- unitStep n m : TorusSite n) a b,
      z ∈ supBall (0 : TorusSite n) N := by
    intro m a b
    have := plaquetteVertices_mem_supBall (n := n) N hN (- Pi.single m 1) (fun l => by
      simpa using natAbs_single_le m l) a b
    rwa [siteOfInt_neg, siteOfInt_single] at this
  by_cases h1 : μ = i
  · subst h1
    have e : ∀ x : TorusSite n, (if (∀ z ∈ plaquetteVertices x μ ν, z ∈ supBall (0 : TorusSite n) N) then
        incidence ((0 : TorusSite n), μ) x μ ν * incidence (y, μ) x μ ν else 0) =
        ((if (0 : TorusSite n) = x then 1 else 0) - (if (0 : TorusSite n) = x + unitStep n ν then 1 else 0)) *
          (if (∀ z ∈ plaquetteVertices x μ ν, z ∈ supBall (0 : TorusSite n) N) then
            ((if y = x then 1 else 0) - (if y = x + unitStep n ν then 1 else 0)) else 0) := by
      intro x
      rw [incidence_eq _ _ _ _ _ hne, incidence_eq _ _ _ _ _ hne]
      simp only [if_true, if_neg hne, add_zero, mul_ite, mul_zero]
    simp only [e]
    rw [sum_indicator_sub_mul, if_pos (ok0 μ ν), if_pos (ok1 ν μ ν)]
    unfold planeProfile
    simp only [if_true, zero_add, neg_add_cancel]
    split_ifs <;> ring
  · by_cases h2 : ν = i
    · subst h2
      have e : ∀ x : TorusSite n, (if (∀ z ∈ plaquetteVertices x μ ν, z ∈ supBall (0 : TorusSite n) N) then
          incidence ((0 : TorusSite n), ν) x μ ν * incidence (y, ν) x μ ν else 0) =
          ((if (0 : TorusSite n) = x then 1 else 0) - (if (0 : TorusSite n) = x + unitStep n μ then 1 else 0)) *
            (if (∀ z ∈ plaquetteVertices x μ ν, z ∈ supBall (0 : TorusSite n) N) then
              ((if y = x then 1 else 0) - (if y = x + unitStep n μ then 1 else 0)) else 0) := by
        intro x
        rw [incidence_eq _ _ _ _ _ hne, incidence_eq _ _ _ _ _ hne]
        simp only [if_true, if_neg (Ne.symm hne), zero_add, mul_ite, mul_zero]
        split_ifs <;> ring
      simp only [e]
      rw [sum_indicator_sub_mul, if_pos (ok0 μ ν), if_pos (ok1 μ μ ν), if_neg h1]
      unfold planeProfile
      simp only [if_true, zero_add, neg_add_cancel]
      split_ifs <;> ring
    · have e : ∀ x : TorusSite n, (if (∀ z ∈ plaquetteVertices x μ ν, z ∈ supBall (0 : TorusSite n) N) then
          incidence ((0 : TorusSite n), i) x μ ν * incidence (y, i) x μ ν else 0) = 0 := by
        intro x
        rw [incidence_eq _ _ _ _ _ hne]
        simp [Ne.symm h1, Ne.symm h2]
      simp [e, h1, h2]
private lemma sum_ordered_pairs (T : Fin 4 → ℝ) (i : Fin 4) :
    ∑ μ, ∑ ν, (if μ < ν then (if μ = i then T ν else if ν = i then T μ else 0) else 0) =
      ∑ m, (if m = i then 0 else T m) := by
  fin_cases i <;> simp [Fin.sum_univ_four] <;> ring
open Classical in
private lemma sum_incidence_supBall [NeZero n] (N : ℕ) (hN : 3 ≤ N) (y : TorusSite n) (i : Fin 4) :
    ∑ p ∈ plaquettesIn (supBall (0 : TorusSite n) N),
        incidence ((0 : TorusSite n), i) p.1 p.2.1 p.2.2 * incidence (y, i) p.1 p.2.1 p.2.2 =
      ∑ m, (if m = i then 0 else planeProfile y m) := by
  rw [← sum_ordered_pairs]
  unfold plaquettesIn
  rw [Finset.sum_filter, Fintype.sum_prod_type,
    Finset.sum_comm' (t' := Finset.univ) (s' := fun _ => Finset.univ) (by simp)]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ => ?_
  by_cases h : μ < ν
  · rw [if_pos h, ← sum_incidence_mul_plane N hN y i μ ν h]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [h, true_and]
  · rw [if_neg h]
    simp [h]
private lemma siteOfInt_eq_iff {z w : Fin 4 → ℤ} (hz : ∀ l, |z l - w l| < n) :
    (siteOfInt z : TorusSite n) = siteOfInt w ↔ z = w := by
  constructor
  · intro h
    funext l
    have h1 : ((z l : ℤ) : ZMod n) = (w l : ℤ) := congrFun h l
    have h2 := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1 h1
    have h3 : w l - z l = 0 := by
      refine Int.eq_zero_of_abs_lt_dvd h2 ?_
      rw [abs_sub_comm]
      exact hz l
    omega
  · rintro rfl; rfl
private def latticeComponent (i : Fin 4) (z : Fin 4 → ℤ) : ℝ :=
  ∑ m, (if m = i then 0 else
    2 * (if z = 0 then 1 else 0) - (if z = Pi.single m 1 then 1 else 0) - (if z = - Pi.single m 1 then 1 else 0))
private lemma cubeEntry_eq_latticeEntry (a : ℝ) (L N : ℕ) (i : Fin 4) (z : Fin 4 → ℤ) (hN : 3 ≤ N)
    (hz : ∀ l, (z l).natAbs ≤ N) : cubeEntry a L 0 N (0, i) (z, i) = latticeComponent i z := by
  haveI : NeZero (16 * (N + 1)) := ⟨by omega⟩
  have e1 : cubeEntry a L 0 N (0, i) (z, i) =
      mixedDeriv (wilsonAction (supBall (0 : TorusSite (16 * (N + 1))) N)) (trivialField (16 * (N + 1)))
        ![((0 : TorusSite (16 * (N + 1))), i), (siteOfInt z, i)]
        ![BoxGaussian.imaginaryUnitI, BoxGaussian.imaginaryUnitI] := by
    unfold cubeEntry
    have e2 : bondFrom (0 : TorusSite (16 * (N + 1))) ((0 : Fin 4 → ℤ), i) = ((0 : TorusSite (16 * (N + 1))), i) := by
      simp [bondFrom, siteOfInt_zero_eq]
    have e3 : bondFrom (0 : TorusSite (16 * (N + 1))) (z, i) = (siteOfInt z, i) := by
      simp [bondFrom]
    rw [e2, e3]
    rfl
  rw [e1, mixedDeriv_wilsonAction_eq]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [sum_incidence_supBall N hN]
  unfold latticeComponent planeProfile
  refine Finset.sum_congr rfl fun m _ => ?_
  by_cases hm : m = i
  · simp [hm]
  · simp only [if_neg hm]
    have hsmall : ∀ (w : Fin 4 → ℤ), (∀ l, (w l).natAbs ≤ 1) →
        ∀ l, |z l - w l| < ((16 * (N + 1) : ℕ) : ℤ) := by
      intro w hw l
      have h1 := hz l
      have h2 := hw l
      push_cast
      rw [abs_lt]
      omega
    have c1 : (siteOfInt z : TorusSite (16 * (N + 1))) = 0 ↔ z = 0 := by
      rw [← siteOfInt_zero_eq, siteOfInt_eq_iff (hsmall 0 (by simp))]
    have c2 : (siteOfInt z : TorusSite (16 * (N + 1))) = unitStep _ m ↔ z = Pi.single m 1 := by
      rw [← siteOfInt_single, siteOfInt_eq_iff (hsmall _ (natAbs_single_le m))]
    have c3 : (siteOfInt z : TorusSite (16 * (N + 1))) = - unitStep _ m ↔ z = - Pi.single m 1 := by
      rw [← siteOfInt_single, ← siteOfInt_neg,
        siteOfInt_eq_iff (hsmall _ (fun l => by simpa using natAbs_single_le m l))]
    simp only [c1, c2, c3]
private lemma hasSum_indicator_mul_sq (v : Fin 4 → ℤ) (l : Fin 4) :
    HasSum (fun z : Fin 4 → ℤ => (if z = v then (1 : ℝ) else 0) * (z l : ℝ) ^ 2) ((v l : ℝ) ^ 2) := by
  have := hasSum_single (f := fun z : Fin 4 → ℤ => (if z = v then (1 : ℝ) else 0) * (z l : ℝ) ^ 2) v
    (fun z hz => by simp [hz])
  simpa using this
theorem wilsonLimitFormSecondMoment : wilsonLimitFormSecondMomentStatement := by
  intro a cK c C L Q hc hQ i l hil
  have hK : ∀ z, Q (0, i) (z, i) = latticeComponent i z := by
    intro z
    refine tendsto_nhds_unique (hQ.tendsto (0, i) (z, i)) (tendsto_const_nhds.congr' ?_)
    filter_upwards [eventually_ge_atTop (3 + ∑ l, (z l).natAbs)] with N hN
    refine (cubeEntry_eq_latticeEntry a L N i z (by omega) fun l => ?_).symm
    have := Finset.single_le_sum (f := fun l => (z l).natAbs) (fun _ _ => Nat.zero_le _) (Finset.mem_univ l)
    omega
  have hm : ∀ m ∈ (Finset.univ : Finset (Fin 4)), HasSum (fun z : Fin 4 → ℤ =>
      (if m = i then 0 else 2 * (if z = 0 then 1 else 0) - (if z = Pi.single m 1 then 1 else 0) -
        (if z = - Pi.single m 1 then 1 else 0)) * (z l : ℝ) ^ 2)
      (if m = i then 0 else if m = l then -2 else 0) := by
    intro m _
    by_cases h : m = i
    · simp [h]
    · simp only [if_neg h]
      have h1 := (((hasSum_indicator_mul_sq 0 l).mul_left 2).sub
        (hasSum_indicator_mul_sq (Pi.single m 1) l)).sub (hasSum_indicator_mul_sq (- Pi.single m 1) l)
      refine (congrArg₂ (fun (f : (Fin 4 → ℤ) → ℝ) (v : ℝ) => HasSum f v) ?_ ?_).mp h1
      · funext z; ring
      · by_cases h2 : m = l
        · subst h2; simp; norm_num
        · simp [h2, Ne.symm h2]
  have h2 := hasSum_sum hm
  have e : ∑ m, (if m = i then (0 : ℝ) else if m = l then -2 else 0) = -2 := by
    rw [Finset.sum_eq_single l]
    · simp [Ne.symm hil]
    · intro b _ hb
      simp [hb]
    · simp
  rw [e] at h2
  refine (congrArg (fun f : (Fin 4 → ℤ) → ℝ => HasSum f _) ?_).mp h2
  funext z
  rw [hK, ← Finset.sum_mul]
  rfl
end YangMills.Construction.LimitForms
end
