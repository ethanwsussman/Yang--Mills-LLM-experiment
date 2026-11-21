import YangMills.Construction.HoleBesideASecondHole.MeanOfAProductOfGroupVariablesProof
import YangMills.Construction.HoleBesideASecondHole.MeanOfATurnedVariable
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
namespace TurnedMeans
open YangMills.Construction.BlockAverages (UnitQuaternion)
open YangMills.Construction.GroupMeans (polarPart meanDirection quatAverage average variance)
theorem norm_unit (g : UnitQuaternion) : ‖(g : ℍ[ℝ])‖ = 1 := by apply _root_.YangMills.Construction.BlockAverages.norm_coe_unitQuaternion <;> assumption
theorem unit_mul_inv (g : UnitQuaternion) : (g : ℍ[ℝ]) * ((g⁻¹ : UnitQuaternion) : ℍ[ℝ]) = 1 := by apply _root_.YangMills.Construction.GaugeFixing.coe_mul_coe_inv <;> assumption
theorem unit_mul (g g' : UnitQuaternion) :
    ((g * g' : UnitQuaternion) : ℍ[ℝ]) = (g : ℍ[ℝ]) * (g' : ℍ[ℝ]) := rfl
theorem norm_unit_mul_left (g : UnitQuaternion) (q : ℍ[ℝ]) : ‖(g : ℍ[ℝ]) * q‖ = ‖q‖ := by
  rw [norm_mul, norm_unit, one_mul]
theorem norm_smul_polarPart (q : ℍ[ℝ]) : (‖q‖ : ℝ) • ((polarPart q : UnitQuaternion) : ℍ[ℝ]) = q := by apply _root_.YangMills.Construction.GroupMeans.norm_smul_polarPart <;> assumption
variable {E : Type} (I : Finset E)
theorem card_pos_real (hI : I.Nonempty) : (0 : ℝ) < I.card := by exact_mod_cast hI.card_pos
theorem average_const (hI : I.Nonempty) (c : ℝ) : average I (fun _ => c) = c := by apply _root_.YangMills.Construction.GroupMeans.average_const <;> assumption
theorem average_add (f g : E → ℝ) : average I (fun e => f e + g e) = average I f + average I g := by
  simp only [average, Finset.sum_add_distrib, mul_add]
theorem quatAverage_add (f g : E → ℍ[ℝ]) :
    quatAverage I (fun e => f e + g e) = quatAverage I f + quatAverage I g := by
  simp only [quatAverage, Finset.sum_add_distrib, smul_add]
theorem quatAverage_mul_left (a : ℍ[ℝ]) (f : E → ℍ[ℝ]) :
    quatAverage I (fun e => a * f e) = a * quatAverage I f := by
  simp only [quatAverage, ← Finset.mul_sum, mul_smul_comm]
theorem quatAverage_mul_right (a : ℍ[ℝ]) (f : E → ℍ[ℝ]) :
    quatAverage I (fun e => f e * a) = quatAverage I f * a := by
  simp only [quatAverage, ← Finset.sum_mul, smul_mul_assoc]
theorem quatAverage_const (hI : I.Nonempty) (c : ℍ[ℝ]) : quatAverage I (fun _ => c) = c := by apply _root_.YangMills.Construction.GroupMeans.quatAverage_const <;> assumption
theorem norm_quatAverage_le (hI : I.Nonempty) (f : E → ℍ[ℝ]) :
    ‖quatAverage I f‖ ≤ average I fun e => ‖f e‖ := by apply _root_.YangMills.Construction.GroupMeans.norm_quatAverage_le <;> assumption
theorem quatAverage_rotated (g : E → UnitQuaternion) :
    quatAverage I (fun e => (((meanDirection I g)⁻¹ * g e : UnitQuaternion) : ℍ[ℝ])) =
      ((‖quatAverage I fun e => (g e : ℍ[ℝ])‖ : ℝ) : ℍ[ℝ]) := by apply _root_.YangMills.Construction.GroupMeans.quatAverage_rotated <;> assumption
theorem variance_eq (hI : I.Nonempty) (g : E → UnitQuaternion) :
    variance I g = 2 - 2 * ‖quatAverage I fun e => (g e : ℍ[ℝ])‖ := by apply _root_.YangMills.Construction.GroupMeans.variance_eq <;> assumption
theorem norm_quatAverage_unit_le (hI : I.Nonempty) (g : E → UnitQuaternion) :
    ‖quatAverage I fun e => (g e : ℍ[ℝ])‖ ≤ 1 := by apply _root_.YangMills.Construction.GroupMeans.norm_quatAverage_unit_le_one <;> assumption
theorem variance_le (hI : I.Nonempty) (g : E → UnitQuaternion) (T : UnitQuaternion) :
    variance I g ≤ average I fun e => ‖(g e : ℍ[ℝ]) - T‖ ^ 2 := by apply _root_.YangMills.Construction.GroupMeans.variance_le_average_sq_dist <;> assumption
theorem quatAverage_star (g : E → UnitQuaternion) :
    quatAverage I (fun e => (((g e)⁻¹ : UnitQuaternion) : ℍ[ℝ])) =
      star (quatAverage I fun e => (g e : ℍ[ℝ])) := by apply _root_.YangMills.Construction.GroupMeans.quatAverage_inv_eq_star <;> assumption
theorem norm_inv_sub_one (g : UnitQuaternion) :
    ‖((g⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1‖ = ‖(g : ℍ[ℝ]) - 1‖ := by apply _root_.YangMills.Construction.BlockAverages.norm_coe_inv_sub_one <;> assumption
variable {G : Finset E}
theorem quatAverage_sub (f g : E → ℍ[ℝ]) :
    quatAverage I (fun e => f e - g e) = quatAverage I f - quatAverage I g := by
  simp only [quatAverage, Finset.sum_sub_distrib, smul_sub]
theorem near_quatAverage (hI : I.Nonempty) (f : E → UnitQuaternion) (η : ℝ) (h : OscillationAtMost I f η) :
    ∀ e ∈ I, ‖(f e : ℍ[ℝ]) - quatAverage I fun e => (f e : ℍ[ℝ])‖ ≤ η := by
  intro e he
  have e1 : (f e : ℍ[ℝ]) - (quatAverage I fun e => (f e : ℍ[ℝ])) =
      quatAverage I (fun e' => (f e : ℍ[ℝ]) - (f e' : ℍ[ℝ])) := by
    rw [quatAverage_sub, quatAverage_const I hI]
  rw [e1]
  refine (norm_quatAverage_le I hI _).trans ?_
  unfold average
  calc (1 / (I.card : ℝ)) * ∑ e' ∈ I, ‖(f e : ℍ[ℝ]) - f e'‖
      ≤ (1 / (I.card : ℝ)) * ∑ _e' ∈ I, η :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun e' he' => h e he e' he') (by positivity)
    _ = η := by
        rw [Finset.sum_const, nsmul_eq_mul]
        field_simp
theorem rotated_near_one (hI : I.Nonempty) (f : E → UnitQuaternion) (η : ℝ) (hη : η ≤ 1 / 8)
    (h : OscillationAtMost I f η) :
    ∀ e ∈ I, ‖(((meanDirection I f)⁻¹ * f e : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ 2 * η := by
  intro e he
  set M := quatAverage I fun e => (f e : ℍ[ℝ]) with hM
  have h1 := near_quatAverage I hI f η h e he
  have h2 : (1 : ℝ) - η ≤ ‖M‖ := by
    have := norm_sub_norm_le (f e : ℍ[ℝ]) M
    rw [norm_unit] at this
    linarith
  have h3 : ‖M‖ ≤ 1 := norm_quatAverage_unit_le I hI f
  have hdir := norm_smul_polarPart M
  have h4 : ‖M - (polarPart M : ℍ[ℝ])‖ ≤ η := by
    have e1 : M - (polarPart M : ℍ[ℝ]) = (‖M‖ - 1 : ℝ) • (polarPart M : ℍ[ℝ]) := by
      rw [sub_smul, hdir, one_smul]
    rw [e1, norm_smul, norm_unit, mul_one, Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  have e2 : ‖(((meanDirection I f)⁻¹ * f e : UnitQuaternion) : ℍ[ℝ]) - 1‖ =
      ‖(f e : ℍ[ℝ]) - (polarPart M : ℍ[ℝ])‖ := by
    rw [← norm_unit_mul_left (meanDirection I f)]
    congr 1
    rw [mul_sub, unit_mul, ← mul_assoc, unit_mul_inv, one_mul, mul_one]
    rfl
  rw [e2]
  have e3 : (f e : ℍ[ℝ]) - (polarPart M : ℍ[ℝ]) =
      ((f e : ℍ[ℝ]) - M) + (M - (polarPart M : ℍ[ℝ])) := by abel
  rw [e3]
  have := norm_add_le ((f e : ℍ[ℝ]) - M) (M - (polarPart M : ℍ[ℝ]))
  linarith
theorem one_sub_norm_quatAverage_le (hI : I.Nonempty) (f : E → UnitQuaternion) (η : ℝ) (hη0 : 0 ≤ η)
    (hη : η ≤ 1 / 8) (h : OscillationAtMost I f η) :
    1 - ‖quatAverage I fun e => (f e : ℍ[ℝ])‖ ≤ 2 * η ^ 2 := by
  have h1 := variance_eq I hI f
  have h2 : variance I f ≤ 4 * η ^ 2 := by
    have : variance I f =
        average I fun e => ‖(((meanDirection I f)⁻¹ * f e : UnitQuaternion) : ℍ[ℝ]) - 1‖ ^ 2 := rfl
    rw [this]
    have c := card_pos_real I hI
    unfold average
    calc (1 / (I.card : ℝ)) * ∑ e ∈ I, ‖(((meanDirection I f)⁻¹ * f e : UnitQuaternion) : ℍ[ℝ]) - 1‖ ^ 2
        ≤ (1 / (I.card : ℝ)) * ∑ _e ∈ I, 4 * η ^ 2 := by
          refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun e he => ?_) (by positivity)
          have := rotated_near_one I hI f η hη h e he
          have h0 := norm_nonneg ((((meanDirection I f)⁻¹ * f e : UnitQuaternion) : ℍ[ℝ]) - 1)
          nlinarith
      _ = 4 * η ^ 2 := by
          rw [Finset.sum_const, nsmul_eq_mul]
          field_simp
  linarith
open Classical in
theorem subset_quatAverage_close (hIG : G ⊆ I) (hG : G.Nonempty) (D : E → ℍ[ℝ]) (m τ : ℝ) (hm : 0 ≤ m)
    (hD : ∀ e ∈ I, ‖D e‖ ≤ m) (hτ : ((I \ G).card : ℝ) ≤ τ * I.card) :
    ‖quatAverage G D - quatAverage I D‖ ≤ 2 * τ * m := by
  have hI : I.Nonempty := hG.mono hIG
  have cI := card_pos_real I hI
  have cG := card_pos_real G hG
  have hsplit : ∑ e ∈ I, D e = ∑ e ∈ G, D e + ∑ e ∈ I \ G, D e := by
    rw [add_comm, Finset.sum_sdiff hIG]
  have hcard : (I.card : ℝ) = G.card + (I \ G).card := by
    have := Finset.card_sdiff_add_card_eq_card hIG
    have h2 : ((I \ G).card + G.card : ℝ) = I.card := by exact_mod_cast this
    linarith
  have e1 : quatAverage G D - quatAverage I D =
      ((1 / (G.card : ℝ)) - 1 / (I.card : ℝ)) • ∑ e ∈ G, D e -
        (1 / (I.card : ℝ)) • ∑ e ∈ I \ G, D e := by
    simp only [quatAverage]
    rw [hsplit, smul_add, sub_smul]
    abel
  have n1 : ‖∑ e ∈ G, D e‖ ≤ G.card * m := by
    refine (norm_sum_le _ _).trans ?_
    refine (Finset.sum_le_sum fun e he => hD e (hIG he)).trans ?_
    simp
  have n2 : ‖∑ e ∈ I \ G, D e‖ ≤ (I \ G).card * m := by
    refine (norm_sum_le _ _).trans ?_
    refine (Finset.sum_le_sum fun e he => hD e (Finset.sdiff_subset he)).trans ?_
    simp
  rw [e1]
  refine (norm_sub_le _ _).trans ?_
  have hdiff : 0 ≤ (1 / (G.card : ℝ)) - 1 / (I.card : ℝ) := by
    have : (G.card : ℝ) ≤ I.card := by
      have : (0 : ℝ) ≤ (I \ G).card := by positivity
      linarith
    have := one_div_le_one_div_of_le cG this
    linarith
  rw [norm_smul, norm_smul, Real.norm_of_nonneg hdiff,
    Real.norm_of_nonneg (show 0 ≤ 1 / (I.card : ℝ) by positivity)]
  have t1 : ((1 / (G.card : ℝ)) - 1 / (I.card : ℝ)) * ‖∑ e ∈ G, D e‖ ≤
      ((I \ G).card : ℝ) / I.card * m := by
    calc ((1 / (G.card : ℝ)) - 1 / (I.card : ℝ)) * ‖∑ e ∈ G, D e‖
        ≤ ((1 / (G.card : ℝ)) - 1 / (I.card : ℝ)) * (G.card * m) :=
          mul_le_mul_of_nonneg_left n1 hdiff
      _ = ((I \ G).card : ℝ) / I.card * m := by
          rw [hcard]
          field_simp
          ring
  have t2 : (1 / (I.card : ℝ)) * ‖∑ e ∈ I \ G, D e‖ ≤ ((I \ G).card : ℝ) / I.card * m := by
    calc (1 / (I.card : ℝ)) * ‖∑ e ∈ I \ G, D e‖
        ≤ (1 / (I.card : ℝ)) * ((I \ G).card * m) := mul_le_mul_of_nonneg_left n2 (by positivity)
      _ = ((I \ G).card : ℝ) / I.card * m := by ring
  have t3 : ((I \ G).card : ℝ) / I.card ≤ τ := by
    rw [div_le_iff₀ cI]
    exact hτ
  have t4 : ((I \ G).card : ℝ) / I.card * m ≤ τ * m := mul_le_mul_of_nonneg_right t3 hm
  linarith
end TurnedMeans
open YangMills.Construction.BlockAverages (UnitQuaternion)
open YangMills.Construction.GroupMeans (polarPart meanDirection quatAverage average variance)
theorem TurnedMeans.turnedMeanEstimate_holds : TurnedMeans.TurnedMeanEstimate := by
  intro E I G A B P Pk η δ τ hIG hG hη0 hη hA hB hP hk hδ hτ
  open TurnedMeans in
  have hI : I.Nonempty := hG.mono hIG
  set g := meanDirection I A with hg
  set g' := meanDirection I B with hg'
  set p := quatAverage I (fun e => (P e : ℍ[ℝ])) with hp
  have hpn : ‖p‖ ≤ 1 := TurnedMeans.norm_quatAverage_unit_le I hI P
  let θ : E → UnitQuaternion := fun e => g⁻¹ * A e
  let ζ : E → UnitQuaternion := fun e => (B e)⁻¹ * g'
  let a : E → ℍ[ℝ] := fun e => (θ e : ℍ[ℝ]) - 1
  let b : E → ℍ[ℝ] := fun e => (ζ e : ℍ[ℝ]) - 1
  let ν : E → ℍ[ℝ] := fun e => (P e : ℍ[ℝ]) - p
  let κ : E → ℍ[ℝ] := fun e => (Pk e : ℍ[ℝ]) - P e
  let R : E → ℍ[ℝ] := fun e => (θ e : ℍ[ℝ]) * (Pk e : ℍ[ℝ]) * (ζ e : ℍ[ℝ])
  have ha : ∀ e ∈ I, ‖a e‖ ≤ 2 * η := TurnedMeans.rotated_near_one I hI A η hη hA
  have hb : ∀ e ∈ I, ‖b e‖ ≤ 2 * η := by
    intro e he
    have h1 := TurnedMeans.rotated_near_one I hI B η hη hB e he
    have h2 := TurnedMeans.norm_inv_sub_one (g'⁻¹ * B e)
    have e1 : (g'⁻¹ * B e)⁻¹ = ζ e := by
      simp only [ζ]
      group
    rw [e1] at h2
    simp only [b]
    rw [h2]
    exact h1
  have hν : ∀ e ∈ I, ‖ν e‖ ≤ η := TurnedMeans.near_quatAverage I hI P η hP
  have hκ : ∀ e ∈ I, ‖κ e‖ ≤ η := hk
  have hθn : ∀ e, ‖(θ e : ℍ[ℝ])‖ = 1 := fun e => TurnedMeans.norm_unit _
  have hζn : ∀ e, ‖(ζ e : ℍ[ℝ])‖ = 1 := fun e => TurnedMeans.norm_unit _
  let Err : E → ℍ[ℝ] := fun e => (θ e : ℍ[ℝ]) * κ e * (ζ e : ℍ[ℝ]) + a e * ν e +
    (θ e : ℍ[ℝ]) * ν e * b e + a e * p * b e
  have hid : ∀ e, R e = p + a e * p + p * b e + ν e + Err e := by
    intro e
    simp only [R, Err, a, b, ν, κ]
    noncomm_ring
  have hErr : ∀ e ∈ I, ‖Err e‖ ≤ ‖κ e‖ + 8 * η ^ 2 := by
    intro e he
    have n1 : ‖(θ e : ℍ[ℝ]) * κ e * (ζ e : ℍ[ℝ])‖ = ‖κ e‖ := by
      rw [norm_mul, norm_mul, hθn, hζn]
      ring
    have n2 : ‖a e * ν e‖ ≤ 2 * η * η := by
      rw [norm_mul]
      exact mul_le_mul (ha e he) (hν e he) (norm_nonneg _) (by positivity)
    have n3 : ‖(θ e : ℍ[ℝ]) * ν e * b e‖ ≤ η * (2 * η) := by
      rw [norm_mul, norm_mul, hθn, one_mul]
      exact mul_le_mul (hν e he) (hb e he) (norm_nonneg _) hη0
    have n4 : ‖a e * p * b e‖ ≤ 2 * η * 1 * (2 * η) := by
      rw [norm_mul, norm_mul]
      exact mul_le_mul (mul_le_mul (ha e he) hpn (norm_nonneg _) (by positivity)) (hb e he) (norm_nonneg _)
        (by positivity)
    simp only [Err]
    refine (norm_add_le _ _).trans ?_
    have m1 := norm_add_le ((θ e : ℍ[ℝ]) * κ e * (ζ e : ℍ[ℝ]) + a e * ν e) ((θ e : ℍ[ℝ]) * ν e * b e)
    have m2 := norm_add_le ((θ e : ℍ[ℝ]) * κ e * (ζ e : ℍ[ℝ])) (a e * ν e)
    nlinarith
  have hma : ‖quatAverage I a‖ ≤ 2 * η ^ 2 := by
    have e1 : quatAverage I a = (((‖quatAverage I fun e => (A e : ℍ[ℝ])‖ - 1 : ℝ)) : ℍ[ℝ]) := by
      have := TurnedMeans.quatAverage_rotated I A
      simp only [a, θ]
      rw [TurnedMeans.quatAverage_sub, this, TurnedMeans.quatAverage_const I hI]
      simp
    rw [e1, Quaternion.norm_coe, Real.norm_eq_abs, abs_le]
    have h1 := TurnedMeans.one_sub_norm_quatAverage_le I hI A η hη0 hη hA
    have h2 := TurnedMeans.norm_quatAverage_unit_le I hI A
    constructor <;> nlinarith
  have hmb : ‖quatAverage I b‖ ≤ 2 * η ^ 2 := by
    have e1 : quatAverage I b = (((‖quatAverage I fun e => (B e : ℍ[ℝ])‖ - 1 : ℝ)) : ℍ[ℝ]) := by
      have h0 := TurnedMeans.quatAverage_rotated I B
      have h1 := TurnedMeans.quatAverage_star I (fun e => g'⁻¹ * B e)
      have h2 : (fun e => (((g'⁻¹ * B e)⁻¹ : UnitQuaternion) : ℍ[ℝ])) = fun e => (ζ e : ℍ[ℝ]) := by
        funext e
        congr 1
        simp only [ζ]
        group
      rw [h2, h0] at h1
      simp only [b]
      rw [TurnedMeans.quatAverage_sub, h1, TurnedMeans.quatAverage_const I hI]
      simp
    rw [e1, Quaternion.norm_coe, Real.norm_eq_abs, abs_le]
    have h1 := TurnedMeans.one_sub_norm_quatAverage_le I hI B η hη0 hη hB
    have h2 := TurnedMeans.norm_quatAverage_unit_le I hI B
    constructor <;> nlinarith
  have hmν : quatAverage I ν = 0 := by
    simp only [ν]
    rw [TurnedMeans.quatAverage_sub, TurnedMeans.quatAverage_const I hI]
    simp [hp]
  have hmR : quatAverage I R = p + quatAverage I a * p + p * quatAverage I b + quatAverage I Err := by
    have e1 : R = fun e => p + a e * p + p * b e + ν e + Err e := funext hid
    rw [e1, TurnedMeans.quatAverage_add, TurnedMeans.quatAverage_add,
      TurnedMeans.quatAverage_add, TurnedMeans.quatAverage_add,
      TurnedMeans.quatAverage_const I hI, TurnedMeans.quatAverage_mul_right,
      TurnedMeans.quatAverage_mul_left]
    change p + quatAverage I a * p + p * quatAverage I b + quatAverage I ν + quatAverage I Err = _
    rw [hmν, add_zero]
  have hmErr : ‖quatAverage I Err‖ ≤ δ + 8 * η ^ 2 := by
    refine (TurnedMeans.norm_quatAverage_le I hI _).trans ?_
    have c := TurnedMeans.card_pos_real I hI
    have s1 : average I (fun e => ‖Err e‖) ≤ average I (fun e => ‖κ e‖ + 8 * η ^ 2) := by
      unfold average
      exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum hErr) (by positivity)
    rw [TurnedMeans.average_add, TurnedMeans.average_const I hI] at s1
    have : average I (fun e => ‖κ e‖) ≤ δ := hδ
    linarith
  have hall : ‖quatAverage I R - p‖ ≤ δ + 12 * η ^ 2 := by
    have e1 : quatAverage I R - p = quatAverage I a * p + p * quatAverage I b + quatAverage I Err := by
      rw [hmR]
      abel
    rw [e1]
    have n1 : ‖quatAverage I a * p‖ ≤ 2 * η ^ 2 * 1 := by
      rw [norm_mul]
      exact mul_le_mul hma hpn (norm_nonneg _) (by positivity)
    have n2 : ‖p * quatAverage I b‖ ≤ 1 * (2 * η ^ 2) := by
      rw [norm_mul]
      exact mul_le_mul hpn hmb (norm_nonneg _) (by norm_num)
    have m1 := norm_add_le (quatAverage I a * p + p * quatAverage I b) (quatAverage I Err)
    have m2 := norm_add_le (quatAverage I a * p) (p * quatAverage I b)
    linarith
  have hpt : ∀ e ∈ I, ‖R e - p‖ ≤ 7 * η := by
    intro e he
    have e1 : R e - p = a e * p + p * b e + ν e + Err e := by
      rw [hid]
      abel
    rw [e1]
    have n1 : ‖a e * p‖ ≤ 2 * η * 1 := by
      rw [norm_mul]
      exact mul_le_mul (ha e he) hpn (norm_nonneg _) (by positivity)
    have n2 : ‖p * b e‖ ≤ 1 * (2 * η) := by
      rw [norm_mul]
      exact mul_le_mul hpn (hb e he) (norm_nonneg _) (by norm_num)
    have m1 := norm_add_le (a e * p + p * b e + ν e) (Err e)
    have m2 := norm_add_le (a e * p + p * b e) (ν e)
    have m3 := norm_add_le (a e * p) (p * b e)
    have h4 := hErr e he
    have h5 := hκ e he
    have h6 := hν e he
    nlinarith
  have hgood : ‖quatAverage G R - quatAverage I R‖ ≤ 2 * τ * (7 * η) := by
    have h1 := TurnedMeans.subset_quatAverage_close I hIG hG (fun e => R e - p) (7 * η) τ
      (by positivity) hpt hτ
    rw [TurnedMeans.quatAverage_sub, TurnedMeans.quatAverage_sub,
      TurnedMeans.quatAverage_const I hI, TurnedMeans.quatAverage_const G hG] at h1
    simpa using h1
  have hconj : ((g⁻¹ : UnitQuaternion) : ℍ[ℝ]) *
      quatAverage G (fun e => ((A e * Pk e * (B e)⁻¹ : UnitQuaternion) : ℍ[ℝ])) * (g' : ℍ[ℝ]) =
      quatAverage G R := by
    rw [← TurnedMeans.quatAverage_mul_left, ← TurnedMeans.quatAverage_mul_right]
    congr 1
    funext e
    simp only [R, θ, ζ, TurnedMeans.unit_mul]
    noncomm_ring
  refine ⟨?_, ?_⟩
  · change ‖((g⁻¹ : UnitQuaternion) : ℍ[ℝ]) *
      quatAverage G (fun e => ((A e * Pk e * (B e)⁻¹ : UnitQuaternion) : ℍ[ℝ])) * (g' : ℍ[ℝ]) - p‖ ≤ _
    rw [hconj]
    have e1 : quatAverage G R - p = (quatAverage G R - quatAverage I R) + (quatAverage I R - p) := by abel
    rw [e1]
    have := norm_add_le (quatAverage G R - quatAverage I R) (quatAverage I R - p)
    nlinarith
  · obtain ⟨e0, he0⟩ := hI
    have h1 := TurnedMeans.variance_le I ⟨e0, he0⟩ P (P e0)
    have h2 := TurnedMeans.variance_eq I ⟨e0, he0⟩ P
    have c := TurnedMeans.card_pos_real I ⟨e0, he0⟩
    have h3 : average I (fun e => ‖(P e : ℍ[ℝ]) - P e0‖ ^ 2) ≤ η ^ 2 := by
      unfold average
      calc (1 / (I.card : ℝ)) * ∑ e ∈ I, ‖(P e : ℍ[ℝ]) - P e0‖ ^ 2
          ≤ (1 / (I.card : ℝ)) * ∑ _e ∈ I, η ^ 2 := by
            refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun e he => ?_) (by positivity)
            have := hP e he e0 he0
            have h0 := norm_nonneg ((P e : ℍ[ℝ]) - P e0)
            nlinarith
        _ = η ^ 2 := by
            rw [Finset.sum_const, nsmul_eq_mul]
            field_simp
    nlinarith
end YangMills.Construction
end
