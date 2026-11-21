import YangMills.Construction.Lattice.CubesOfTwoStandardPartitionsProof
import YangMills.Construction.Lattice.StandardPartitionCubeGeometry
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction
open Set TorusMetric
noncomputable section
namespace PeriodicLattice.StandardCubes
variable {L m : ℕ} {i : ℤ}
theorem torusSupNorm_eq_pi_norm {S : ℝ} (x : Torus4 S) : _root_.YangMills.Construction.TorusMetric.torusSupNorm x = ‖x‖ := by apply _root_.YangMills.Construction.PeriodicLattice.CubeRefinement.torusSupNorm_eq_norm <;> assumption
theorem norm_torusProj_le {S r : ℝ} (hr : 0 ≤ r) {v : Fin 4 → ℝ} (h : ∀ μ, |v μ| ≤ r) :
    ‖torusProj S v‖ ≤ r :=
  (pi_norm_le_iff_of_nonneg hr).2 fun μ => (addCircle_norm_coe_le_abs (v μ)).trans (h μ)
theorem exists_lift_abs_eq_norm {S : ℝ} (d : Torus4 S) :
    ∃ v, torusProj S v = d ∧ ∀ μ, |v μ| = ‖d μ‖ := by apply _root_.YangMills.Construction.PeriodicLattice.CubeRefinement.exists_torusProj_eq_abs_eq_norm <;> assumption
theorem torusProj_add_eq {S : ℝ} (u v : Fin 4 → ℝ) :
    torusProj S (u + v) = torusProj S u + torusProj S v := by apply _root_.YangMills.Construction.TestPairs.torusProj_map_add <;> assumption
theorem torusProj_sub_eq {S : ℝ} (u v : Fin 4 → ℝ) :
    torusProj S (u - v) = torusProj S u - torusProj S v := by apply _root_.YangMills.Construction.TestPairs.torusProj_map_sub <;> assumption
theorem exists_coord_norm_eq_norm {S : ℝ} (d : Torus4 S) : ∃ μ, ‖d μ‖ = ‖d‖ := by
  by_contra hne
  push Not at hne
  have hlt : ∀ μ, ‖d μ‖ < ‖d‖ := fun μ => lt_of_le_of_ne (norm_le_pi_norm d μ) (hne μ)
  have hpos : 0 < ‖d‖ := (norm_nonneg _).trans_lt (hlt 0)
  exact lt_irrefl _ ((pi_norm_lt_iff hpos).2 hlt)
theorem exists_clamped (v c : ℝ) (hc : 0 ≤ c) :
    ∃ t, (t = v ∨ t = c ∨ t = -c) ∧ |t| ≤ c ∧ |v - t| ≤ max 0 (|v| - c) := by
  rcases le_or_gt |v| c with h | h
  · exact ⟨v, Or.inl rfl, h, by simp⟩
  · rcases le_total 0 v with h0 | h0
    · rw [abs_of_nonneg h0] at h
      refine ⟨c, Or.inr (Or.inl rfl), by rw [abs_of_nonneg hc], ?_⟩
      rw [abs_of_nonneg h0, abs_of_pos (by linarith)]
      exact le_max_right _ _
    · rw [abs_of_nonpos h0] at h
      refine ⟨-c, Or.inr (Or.inr rfl), by rw [abs_neg, abs_of_nonneg hc], ?_⟩
      rw [abs_of_nonpos h0, abs_of_neg (by linarith)]
      refine le_trans (le_of_eq ?_) (le_max_right _ _)
      ring
theorem exists_int_mul_near {a b : ℤ} (hab : a ≤ b) {W t : ℝ} (hW : 0 < W)
    (h1 : (a : ℝ) * W - W / 2 ≤ t) (h2 : t ≤ (b : ℝ) * W + W / 2) :
    ∃ p : ℤ, a ≤ p ∧ p ≤ b ∧ |t - (p : ℝ) * W| ≤ W / 2 := by
  have hr := abs_sub_round (t / W)
  set r := round (t / W) with hrdef
  have hscale : ∀ p : ℤ, |t / W - (p : ℝ)| ≤ 1 / 2 → |t - (p : ℝ) * W| ≤ W / 2 := by
    intro p hp
    have : t - (p : ℝ) * W = (t / W - (p : ℝ)) * W := by field_simp
    rw [this, abs_mul, abs_of_pos hW]
    nlinarith
  have hlo : (a : ℝ) - 1 / 2 ≤ t / W := by
    rw [le_div_iff₀ hW]; nlinarith
  have hhi : t / W ≤ (b : ℝ) + 1 / 2 := by
    rw [div_le_iff₀ hW]; nlinarith
  rw [abs_le] at hr
  by_cases hra : r < a
  · refine ⟨a, le_rfl, hab, hscale a ?_⟩
    have : (r : ℝ) + 1 ≤ a := by exact_mod_cast hra
    rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  by_cases hrb : b < r
  · refine ⟨b, hab, le_rfl, hscale b ?_⟩
    have : (b : ℝ) + 1 ≤ r := by exact_mod_cast hrb
    rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  · exact ⟨r, not_lt.1 hra, not_lt.1 hrb, hscale r (abs_le.2 hr)⟩
def MeshDividesSide (L m : ℕ) (i : ℤ) : Prop :=
  0 < meshSize L i ∧ ∃ N : ℕ, 2 ≤ N ∧ torusSide L m = N * meshSize L i
theorem meshDividesSide_of (hL : 0 < L) (hi : -(m : ℤ) ≤ i) : MeshDividesSide L m i := by
  have hL' : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  have hd : (((m : ℤ) + i).toNat : ℤ) = m + i := Int.toNat_of_nonneg (by omega)
  refine ⟨zpow_pos (by exact_mod_cast hL) _, 2 * L ^ ((m : ℤ) + i).toNat, ?_, ?_⟩
  · have : 0 < L ^ ((m : ℤ) + i).toNat := pow_pos hL _
    omega
  · unfold torusSide meshSize
    push_cast
    rw [mul_assoc]
    congr 1
    rw [← zpow_natCast (L : ℝ) ((m : ℤ) + i).toNat, ← zpow_add₀ hL', ← zpow_natCast (L : ℝ) m]
    congr 1
    omega
theorem coe_add_int_mul_period (S v : ℝ) (k : ℤ) : ((v + k * S : ℝ) : AddCircle S) = v := by
  rw [AddCircle.coe_add]
  have h : (((k : ℝ) * S : ℝ) : AddCircle S) = 0 := by
    rw [AddCircle.coe_eq_zero_iff]
    exact ⟨k, by simp⟩
  rw [h, add_zero]
theorem exists_int_eq_add_mul_of_coe_eq {S a b : ℝ} (h : (a : AddCircle S) = b) :
    ∃ k : ℤ, a = b + k * S := by
  have h0 : ((a - b : ℝ) : AddCircle S) = 0 := by
    rw [AddCircle.coe_sub, h, sub_self]
  obtain ⟨k, hk⟩ := (AddCircle.coe_eq_zero_iff S).1 h0
  refine ⟨k, ?_⟩
  have : (k : ℝ) * S = a - b := by simpa using hk
  linarith
theorem exists_int_lift_of_multiple (h : MeshDividesSide L m i) (a : ℤ) :
    ∃ q : ℤ, (((q : ℝ) * meshSize L i : ℝ) : AddCircle (torusSide L m)) =
        (((a : ℝ) * meshSize L i : ℝ) : AddCircle (torusSide L m)) ∧
      |(q : ℝ)| * meshSize L i = ‖(((a : ℝ) * meshSize L i : ℝ) : AddCircle (torusSide L m))‖ := by
  obtain ⟨hW, N, -, hS⟩ := h
  set r := round ((torusSide L m)⁻¹ * ((a : ℝ) * meshSize L i)) with hr
  refine ⟨a - r * N, ?_, ?_⟩
  · have : (((a - r * N : ℤ) : ℝ) * meshSize L i) =
        (a : ℝ) * meshSize L i + ((-r : ℤ) : ℝ) * torusSide L m := by
      rw [hS]; push_cast; ring
    rw [this, coe_add_int_mul_period]
  · rw [AddCircle.norm_eq, ← hr]
    have : (a : ℝ) * meshSize L i - (r : ℝ) * torusSide L m =
        ((a - r * N : ℤ) : ℝ) * meshSize L i := by
      rw [hS]; push_cast; ring
    rw [this, abs_mul, abs_of_pos hW]
theorem exists_int_lift_of_mem_sublattice (h : MeshDividesSide L m i) {d : FourTorus L m}
    (hd : d ∈ sublattice L m i) :
    ∃ q : Fin 4 → ℤ, (∀ μ, d μ = (((q μ : ℝ) * meshSize L i : ℝ) : AddCircle (torusSide L m))) ∧
      ∀ μ, |(q μ : ℝ)| * meshSize L i = ‖d μ‖ := by
  obtain ⟨n, hn⟩ := hd
  choose q hq hq' using fun μ => exists_int_lift_of_multiple h (n μ)
  exact ⟨q, fun μ => by rw [hn μ, hq μ], fun μ => by rw [hq' μ, hn μ]⟩
theorem norm_eq_nat_mul_meshSize (h : MeshDividesSide L m i) {d : FourTorus L m}
    (hd : d ∈ sublattice L m i) : ∃ k : ℕ, ‖d‖ = (k : ℝ) * meshSize L i := by
  obtain ⟨q, -, hq⟩ := exists_int_lift_of_mem_sublattice h hd
  obtain ⟨μ, hμ⟩ := exists_coord_norm_eq_norm d
  refine ⟨(q μ).natAbs, ?_⟩
  rw [← hμ, ← hq μ, Nat.cast_natAbs, Int.cast_abs]
theorem exists_sublattice_clamp (h : MeshDividesSide L m i) {d : FourTorus L m}
    (hd : d ∈ sublattice L m i) (k : ℕ) :
    ∃ e ∈ sublattice L m i, ‖e‖ ≤ (k : ℝ) * meshSize L i ∧
      ‖d - e‖ ≤ max 0 (‖d‖ - (k : ℝ) * meshSize L i) := by
  obtain ⟨q, hq, hq'⟩ := exists_int_lift_of_mem_sublattice h hd
  have hW := h.1
  have hc : 0 ≤ (k : ℝ) * meshSize L i := by positivity
  choose t ht ht1 ht2 using fun μ => exists_clamped ((q μ : ℝ) * meshSize L i) _ hc
  have hmult : ∀ μ, ∃ n : ℤ, t μ = (n : ℝ) * meshSize L i := by
    intro μ
    rcases ht μ with h1 | h1 | h1
    · exact ⟨q μ, h1⟩
    · exact ⟨k, by rw [h1]; simp⟩
    · exact ⟨-k, by rw [h1]; simp⟩
  choose n hn using hmult
  have hd' : d = torusProj (torusSide L m) fun μ => (q μ : ℝ) * meshSize L i := funext hq
  refine ⟨torusProj (torusSide L m) t, ⟨n, fun μ => by rw [torusProj, hn μ]⟩,
    norm_torusProj_le hc ht1, ?_⟩
  have hsub : d - torusProj (torusSide L m) t =
      torusProj (torusSide L m) ((fun μ => (q μ : ℝ) * meshSize L i) - t) := by
    rw [torusProj_sub_eq, ← hd']
  rw [hsub]
  refine norm_torusProj_le (le_max_left _ _) fun μ => ?_
  refine (ht2 μ).trans (max_le_max le_rfl ?_)
  have : |(q μ : ℝ) * meshSize L i| = ‖d μ‖ := by rw [abs_mul, abs_of_pos hW, hq' μ]
  rw [this]
  linarith [norm_le_pi_norm d μ]
theorem exists_near_points_of_cubes {W : ℝ} (hW : 0 < W) {S : ℝ} (y y' : Torus4 S) :
    ∃ a b : Torus4 S, ‖a - y‖ ≤ W / 2 ∧ ‖b - y'‖ ≤ W / 2 ∧ ‖a - b‖ ≤ max 0 (‖y - y'‖ - W) := by
  obtain ⟨v, hv, hv'⟩ := exists_lift_abs_eq_norm (y - y')
  choose t ht ht1 ht2 using fun μ => exists_clamped (v μ) W hW.le
  have hs : ∀ μ, |t μ / 2| ≤ W / 2 := fun μ => by
    rw [abs_div, abs_of_pos (two_pos : (0 : ℝ) < 2)]
    linarith [ht1 μ]
  have hhalf : torusProj S (fun μ => t μ / 2) + torusProj S (fun μ => t μ / 2) = torusProj S t := by
    rw [← torusProj_add_eq]
    congr 1
    funext μ
    simp only [Pi.add_apply]
    ring
  refine ⟨y - torusProj S (fun μ => t μ / 2), y' + torusProj S (fun μ => t μ / 2), ?_, ?_, ?_⟩
  · have : y - torusProj S (fun μ => t μ / 2) - y = -torusProj S (fun μ => t μ / 2) := by abel
    rw [this, norm_neg]
    exact norm_torusProj_le (by positivity) hs
  · have : y' + torusProj S (fun μ => t μ / 2) - y' = torusProj S (fun μ => t μ / 2) := by abel
    rw [this]
    exact norm_torusProj_le (by positivity) hs
  · have : y - torusProj S (fun μ => t μ / 2) - (y' + torusProj S (fun μ => t μ / 2)) =
        torusProj S (v - t) := by
      rw [torusProj_sub_eq, hv, ← hhalf]
      abel
    rw [this]
    refine norm_torusProj_le (le_max_left _ _) fun μ => ?_
    refine (ht2 μ).trans (max_le_max le_rfl ?_)
    rw [hv' μ]
    have := norm_le_pi_norm (y - y') μ
    linarith
theorem mem_cubeAround_iff {y : Site L m i} {x : FourTorus L m} :
    x ∈ cubeAround y ↔ ‖x - (y : FourTorus L m)‖ ≤ meshSize L i / 2 := by apply _root_.YangMills.Construction.PeriodicLattice.CubeRefinement.mem_cubeAround <;> assumption
theorem centre_mem_cubeAround (h : MeshDividesSide L m i) (y : Site L m i) :
    (y : FourTorus L m) ∈ cubeAround y := by
  rw [mem_cubeAround_iff, sub_self, norm_zero]
  exact (half_pos h.1).le
theorem norm_centres_le {y y' : Site L m i} {x x' : FourTorus L m} (hx : x ∈ cubeAround y)
    (hx' : x' ∈ cubeAround y') : ‖(y : FourTorus L m) - y'‖ ≤ ‖x - x'‖ + meshSize L i := by
  rw [mem_cubeAround_iff] at hx hx'
  have e : (y : FourTorus L m) - y' = -(x - y) + (x - x') + (x' - y') := by abel
  calc ‖(y : FourTorus L m) - y'‖ = ‖-(x - y) + (x - x') + (x' - y')‖ := by rw [e]
    _ ≤ ‖-(x - (y : FourTorus L m))‖ + ‖x - x'‖ + ‖x' - (y' : FourTorus L m)‖ := norm_add₃_le
    _ ≤ ‖x - x'‖ + meshSize L i := by rw [norm_neg]; linarith
theorem setSupDist_le_norm {S : ℝ} {A B : Set (Torus4 S)} {a b : Torus4 S} (ha : a ∈ A)
    (hb : b ∈ B) : setSupDist A B ≤ ENNReal.ofReal ‖a - b‖ := by
  rw [← _root_.YangMills.Construction.PeriodicLattice.StandardCubes.torusSupNorm_eq_pi_norm]
  exact iInf₂_le_of_le a ha (iInf₂_le_of_le b hb le_rfl)
theorem le_setSupDist_of_forall {S : ℝ} {A B : Set (Torus4 S)} {r : ENNReal}
    (h : ∀ a ∈ A, ∀ b ∈ B, r ≤ ENNReal.ofReal ‖a - b‖) : r ≤ setSupDist A B := by
  refine le_iInf₂ fun a ha => le_iInf₂ fun b hb => ?_
  rw [_root_.YangMills.Construction.PeriodicLattice.StandardCubes.torusSupNorm_eq_pi_norm]
  exact h a ha b hb
theorem setSupDist_cubeAround (h : MeshDividesSide L m i) (y y' : Site L m i) :
    setSupDist (cubeAround y) (cubeAround y') =
      ENNReal.ofReal (max 0 (‖(y : FourTorus L m) - y'‖ - meshSize L i)) := by
  apply le_antisymm
  · obtain ⟨a, b, ha, hb, hab⟩ :=
      exists_near_points_of_cubes h.1 (y : FourTorus L m) (y' : FourTorus L m)
    exact (setSupDist_le_norm (mem_cubeAround_iff.2 ha) (mem_cubeAround_iff.2 hb)).trans
      (ENNReal.ofReal_le_ofReal hab)
  · refine le_setSupDist_of_forall fun a ha b hb => ENNReal.ofReal_le_ofReal ?_
    refine max_le (norm_nonneg _) ?_
    linarith [norm_centres_le ha hb]
theorem cubesMeet_cubeAround_iff (h : MeshDividesSide L m i) (y y' : Site L m i) :
    CubesMeet (cubeAround y) (cubeAround y') ↔ ‖(y : FourTorus L m) - y'‖ ≤ meshSize L i := by
  constructor
  · rintro ⟨x, hx, hx'⟩
    have := norm_centres_le hx hx'
    simpa using this
  · intro hn
    obtain ⟨a, b, ha, hb, hab⟩ :=
      exists_near_points_of_cubes h.1 (y : FourTorus L m) (y' : FourTorus L m)
    have h0 : ‖a - b‖ ≤ 0 := hab.trans (max_le le_rfl (by linarith))
    have hab' : a = b := sub_eq_zero.1 (norm_le_zero_iff.1 h0)
    subst hab'
    exact ⟨a, mem_cubeAround_iff.2 ha, mem_cubeAround_iff.2 hb⟩
theorem site_eq_of_norm_lt (h : MeshDividesSide L m i) {y y' : Site L m i}
    (hn : ‖(y : FourTorus L m) - y'‖ < meshSize L i) : y = y' := by
  obtain ⟨k, hk⟩ := norm_eq_nat_mul_meshSize h (sub_mem y.2 y'.2)
  have hW := h.1
  have hk0 : k = 0 := by
    by_contra hne
    have : (1 : ℝ) ≤ k := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hne
    rw [hk] at hn
    nlinarith
  subst hk0
  have : ‖(y : FourTorus L m) - y'‖ = 0 := by rw [hk]; simp
  exact Subtype.ext (sub_eq_zero.1 (norm_eq_zero.1 this))
theorem site_eq_of_near (h : MeshDividesSide L m i) {y y' : Site L m i} {x : FourTorus L m}
    (hx : ‖x - (y : FourTorus L m)‖ < meshSize L i / 2) (hx' : x ∈ cubeAround y') : y = y' := by
  refine site_eq_of_norm_lt h ?_
  have := norm_centres_le (mem_cubeAround_iff.2 hx.le) hx'
  rw [mem_cubeAround_iff] at hx'
  have e : (y : FourTorus L m) - y' = -(x - y) + (x - y') := by abel
  calc ‖(y : FourTorus L m) - y'‖ = ‖-(x - y) + (x - y')‖ := by rw [e]
    _ ≤ ‖-(x - (y : FourTorus L m))‖ + ‖x - (y' : FourTorus L m)‖ := norm_add_le _ _
    _ < meshSize L i := by rw [norm_neg]; linarith
theorem exists_cubeAround_mem (h : MeshDividesSide L m i) (x : FourTorus L m) :
    ∃ y : Site L m i, x ∈ cubeAround y := by
  obtain ⟨v, hv, -⟩ := exists_lift_abs_eq_norm x
  have hW := h.1
  have hex : ∀ μ, ∃ p : ℤ, |v μ - (p : ℝ) * meshSize L i| ≤ meshSize L i / 2 := by
    intro μ
    have hdiv : v μ / meshSize L i * meshSize L i = v μ := by field_simp
    have hr := abs_sub_round (v μ / meshSize L i)
    refine ⟨round (v μ / meshSize L i), ?_⟩
    have : v μ - (round (v μ / meshSize L i) : ℝ) * meshSize L i =
        (v μ / meshSize L i - (round (v μ / meshSize L i) : ℝ)) * meshSize L i := by
      rw [sub_mul, hdiv]
    rw [this, abs_mul, abs_of_pos hW]
    nlinarith
  choose p hp using hex
  refine ⟨⟨torusProj (torusSide L m) fun μ => (p μ : ℝ) * meshSize L i, p, fun μ => rfl⟩, ?_⟩
  rw [mem_cubeAround_iff]
  have : x - torusProj (torusSide L m) (fun μ => (p μ : ℝ) * meshSize L i) =
      torusProj (torusSide L m) (v - fun μ => (p μ : ℝ) * meshSize L i) := by
    rw [torusProj_sub_eq, hv]
  simp only [this]
  exact norm_torusProj_le (half_pos hW).le hp
theorem cube_mem_of_subset_sUnion (h : MeshDividesSide L m i) {C : Set (Set (FourTorus L m))}
    (hC : C ⊆ standardCubePartition L m i) {Q : Set (FourTorus L m)}
    (hQ : Q ∈ standardCubePartition L m i) (hsub : Q ⊆ ⋃₀ C) : Q ∈ C := by
  obtain ⟨y, rfl⟩ := hQ
  obtain ⟨Q', hQ', hy⟩ := hsub (centre_mem_cubeAround h y)
  obtain ⟨y', rfl⟩ := hC hQ'
  have : y = y' := site_eq_of_near h (by rw [sub_self, norm_zero]; exact half_pos h.1) hy
  rwa [this]
theorem cubeSupDistanceFacts_holds (h : MeshDividesSide L m i) : CubeSupDistanceFacts L m i := by
  refine ⟨fun y y' => ?_, fun y y' => ?_, fun y y' => ?_, ?_, ?_, ?_, ?_⟩
  · rw [_root_.YangMills.Construction.PeriodicLattice.StandardCubes.torusSupNorm_eq_pi_norm]
    exact norm_eq_nat_mul_meshSize h (sub_mem y.2 y'.2)
  · rw [_root_.YangMills.Construction.PeriodicLattice.StandardCubes.torusSupNorm_eq_pi_norm]
    exact setSupDist_cubeAround h y y'
  · rw [_root_.YangMills.Construction.PeriodicLattice.StandardCubes.torusSupNorm_eq_pi_norm]
    exact cubesMeet_cubeAround_iff h y y'
  · rintro _ ⟨y, rfl⟩ _ ⟨y', rfl⟩ hn
    rw [cubesMeet_cubeAround_iff h] at hn
    push Not at hn
    obtain ⟨k, hk⟩ := norm_eq_nat_mul_meshSize h (sub_mem y.2 y'.2)
    have hW := h.1
    have hk2 : (2 : ℝ) ≤ k := by
      have : 1 < k := by
        by_contra hle
        have : (k : ℝ) ≤ 1 := by exact_mod_cast not_lt.1 hle
        rw [hk] at hn
        nlinarith
      exact_mod_cast this
    rw [setSupDist_cubeAround h]
    refine ENNReal.ofReal_le_ofReal (le_max_of_le_right ?_)
    rw [hk]
    nlinarith
  · refine eq_univ_of_forall fun x => ?_
    obtain ⟨y, hy⟩ := exists_cubeAround_mem h x
    exact ⟨_, ⟨y, rfl⟩, hy⟩
  · rintro y x hx _ ⟨y', rfl⟩ hx'
    rw [_root_.YangMills.Construction.PeriodicLattice.StandardCubes.torusSupNorm_eq_pi_norm] at hx
    rw [site_eq_of_near h hx hx']
  · exact fun C hC Q hQ hsub => cube_mem_of_subset_sUnion h hC hQ hsub
theorem layerEnlargement_natCast (X : Set (FourTorus L m)) (a : ℕ) :
    layerEnlargement i X (a : ℤ) = (addCubeLayer i)^[a] X := rfl
theorem cube_mem_addCubeLayer_iff (h : MeshDividesSide L m i) (X : Set (FourTorus L m))
    (y'' : Site L m i) :
    cubeAround y'' ∈ partitionCubesIn i (addCubeLayer i X) ↔
      ∃ y' : Site L m i, cubeAround y' ∈ partitionCubesIn i X ∧
        ‖(y'' : FourTorus L m) - y'‖ ≤ meshSize L i := by
  constructor
  · rintro ⟨hp, hsub⟩
    obtain ⟨-, Q', hQ', ht⟩ := cube_mem_of_subset_sUnion h (fun Q hQ => hQ.1) hp hsub
    obtain ⟨y', rfl⟩ := hQ'.1
    exact ⟨y', hQ', (cubesMeet_cubeAround_iff h _ _).1 ht⟩
  · rintro ⟨y', hy', hn⟩
    exact ⟨⟨y'', rfl⟩, subset_sUnion_of_mem
      ⟨⟨y'', rfl⟩, _, hy', (cubesMeet_cubeAround_iff h _ _).2 hn⟩⟩
theorem cube_mem_iterate_addCubeLayer_iff (h : MeshDividesSide L m i) (X : Set (FourTorus L m))
    (a : ℕ) (y' : Site L m i) :
    cubeAround y' ∈ partitionCubesIn i ((addCubeLayer i)^[a] X) ↔
      ∃ y : Site L m i, cubeAround y ∈ partitionCubesIn i X ∧
        ‖(y' : FourTorus L m) - y‖ ≤ (a : ℝ) * meshSize L i := by
  induction a generalizing y' with
  | zero =>
    constructor
    · intro hy
      exact ⟨y', hy, by simp⟩
    · rintro ⟨y, hy, hn⟩
      have h0 : ‖(y' : FourTorus L m) - y‖ = 0 :=
        le_antisymm (by simpa using hn) (norm_nonneg _)
      have : y' = y := Subtype.ext (sub_eq_zero.1 (norm_eq_zero.1 h0))
      rw [this]
      exact hy
  | succ a ih =>
    have hW := h.1
    rw [Function.iterate_succ_apply', cube_mem_addCubeLayer_iff h]
    constructor
    · rintro ⟨y1, h1, hn1⟩
      obtain ⟨y, hy, hn⟩ := (ih y1).1 h1
      refine ⟨y, hy, ?_⟩
      have e : (y' : FourTorus L m) - y =
          ((y' : FourTorus L m) - y1) + ((y1 : FourTorus L m) - y) := by abel
      rw [e]
      push_cast
      refine (norm_add_le _ _).trans ?_
      linarith
    · rintro ⟨y, hy, hn⟩
      obtain ⟨e, he, he1, he2⟩ := exists_sublattice_clamp h (sub_mem y'.2 y.2) 1
      have he' : ‖(y' : FourTorus L m) - y - e‖ ≤ (a : ℝ) * meshSize L i := by
        refine he2.trans (max_le (by positivity) ?_)
        push_cast at hn
        push_cast
        linarith
      refine ⟨y' - ⟨e, he⟩, (ih _).2 ⟨y, hy, ?_⟩, ?_⟩
      · have : (((y' - ⟨e, he⟩ : Site L m i) : FourTorus L m)) - y =
            (y' : FourTorus L m) - y - e := by
          rw [AddSubgroupClass.coe_sub]
          abel
        rw [this]
        exact he'
      · have : (y' : FourTorus L m) - ((y' - ⟨e, he⟩ : Site L m i) : FourTorus L m) = e := by
          rw [AddSubgroupClass.coe_sub]
          abel
        rw [this]
        simpa using he1
theorem eq_sUnion_partitionCubesIn {X : Set (FourTorus L m)} (hX : IsPartitionRegion i X) :
    X = ⋃₀ partitionCubesIn i X := by
  obtain ⟨C, hC, rfl⟩ := hX
  apply subset_antisymm
  · rintro x ⟨Q, hQ, hx⟩
    exact ⟨Q, ⟨hC hQ, subset_sUnion_of_mem hQ⟩, hx⟩
  · exact sUnion_subset fun Q hQ => hQ.2
theorem isPartitionRegion_sUnion {D : Set (Set (FourTorus L m))}
    (hD : ∀ X ∈ D, IsPartitionRegion i X) : IsPartitionRegion i (⋃₀ D) := by
  refine ⟨⋃₀ (partitionCubesIn i '' D), ?_, ?_⟩
  · rintro Q ⟨_, ⟨X, -, rfl⟩, hQ⟩
    exact hQ.1
  · apply subset_antisymm
    · rintro x ⟨X, hXD, hx⟩
      rw [eq_sUnion_partitionCubesIn (hD X hXD)] at hx
      obtain ⟨Q, hQ, hxQ⟩ := hx
      exact ⟨Q, ⟨_, ⟨X, hXD, rfl⟩, hQ⟩, hxQ⟩
    · rintro x ⟨Q, ⟨_, ⟨X, hXD, rfl⟩, hQ⟩, hxQ⟩
      exact ⟨X, hXD, hQ.2 hxQ⟩
theorem isPartitionRegion_union {X Y : Set (FourTorus L m)} (hX : IsPartitionRegion i X)
    (hY : IsPartitionRegion i Y) : IsPartitionRegion i (X ∪ Y) := by
  rw [← sUnion_pair]
  refine isPartitionRegion_sUnion ?_
  rintro Z (rfl | rfl)
  · exact hX
  · exact hY
theorem isPartitionRegion_addCubeLayer (X : Set (FourTorus L m)) :
    IsPartitionRegion i (addCubeLayer i X) :=
  ⟨_, fun _ hQ => hQ.1, rfl⟩
theorem isPartitionRegion_iterate {X : Set (FourTorus L m)} (hX : IsPartitionRegion i X) (a : ℕ) :
    IsPartitionRegion i ((addCubeLayer i)^[a] X) := by
  cases a with
  | zero => exact hX
  | succ a =>
    rw [Function.iterate_succ_apply']
    exact isPartitionRegion_addCubeLayer _
theorem addCubeLayer_monotone : Monotone (addCubeLayer (L := L) (m := m) i) := by
  intro X₁ X₂ hX
  refine sUnion_subset_sUnion ?_
  rintro Q ⟨hQ, Q', hQ', ht⟩
  exact ⟨hQ, Q', ⟨hQ'.1, hQ'.2.trans hX⟩, ht⟩
theorem subset_iterate_addCubeLayer (h : MeshDividesSide L m i) {X : Set (FourTorus L m)}
    (hX : IsPartitionRegion i X) (a : ℕ) : X ⊆ (addCubeLayer i)^[a] X := by
  rw [eq_sUnion_partitionCubesIn hX]
  refine sUnion_subset fun Q hQ => ?_
  rw [← eq_sUnion_partitionCubesIn hX]
  obtain ⟨y, rfl⟩ := hQ.1
  refine ((cube_mem_iterate_addCubeLayer_iff h X a y).2 ⟨y, hQ, ?_⟩).2
  have hW := h.1
  rw [sub_self, norm_zero]
  positivity
theorem enlargementViaCentres_holds (h : MeshDividesSide L m i) : EnlargementViaCentres L m i := by
  refine ⟨fun X _ a y' => by
      simp only [_root_.YangMills.Construction.PeriodicLattice.StandardCubes.torusSupNorm_eq_pi_norm]
      exact cube_mem_iterate_addCubeLayer_iff h X a y',
    fun X hX a => subset_iterate_addCubeLayer h hX a,
    fun X₁ X₂ _ _ a hX => (addCubeLayer_monotone.iterate a) hX, ?_, ?_⟩
  · intro X₁ X₂ h₁ h₂ a
    simp only [layerEnlargement_natCast]
    apply subset_antisymm
    · intro x hx
      rw [eq_sUnion_partitionCubesIn
        (isPartitionRegion_iterate (isPartitionRegion_union h₁ h₂) a)] at hx
      obtain ⟨Q, hQ, hxQ⟩ := hx
      obtain ⟨y', rfl⟩ := hQ.1
      obtain ⟨y, hy, hn⟩ := (cube_mem_iterate_addCubeLayer_iff h _ a y').1 hQ
      obtain ⟨C₁, hC₁, rfl⟩ := id h₁
      obtain ⟨C₂, hC₂, rfl⟩ := id h₂
      have hmem : cubeAround y ∈ C₁ ∪ C₂ := by
        refine cube_mem_of_subset_sUnion h (union_subset hC₁ hC₂) hy.1 ?_
        rw [sUnion_union]
        exact hy.2
      rcases hmem with hm | hm
      · exact Or.inl (((cube_mem_iterate_addCubeLayer_iff h _ a y').2
          ⟨y, ⟨hy.1, subset_sUnion_of_mem hm⟩, hn⟩).2 hxQ)
      · exact Or.inr (((cube_mem_iterate_addCubeLayer_iff h _ a y').2
          ⟨y, ⟨hy.1, subset_sUnion_of_mem hm⟩, hn⟩).2 hxQ)
    · exact union_subset ((addCubeLayer_monotone.iterate a) subset_union_left)
        ((addCubeLayer_monotone.iterate a) subset_union_right)
  · intro X _ a b
    simp only [layerEnlargement_natCast]
    rw [add_comm a b, Function.iterate_add_apply]
theorem le_norm_of_not_mem_enlargement (h : MeshDividesSide L m i) {X : Set (FourTorus L m)}
    (hX : IsPartitionRegion i X) (a : ℕ) {y' : Site L m i}
    (hy' : cubeAround y' ∉ partitionCubesIn i ((addCubeLayer i)^[a] X)) {q x : FourTorus L m}
    (hq : q ∈ cubeAround y') (hx : x ∈ X) : (a : ℝ) * meshSize L i ≤ ‖q - x‖ := by
  have hW := h.1
  rw [eq_sUnion_partitionCubesIn hX] at hx
  obtain ⟨Q, hQ, hxQ⟩ := hx
  obtain ⟨y, rfl⟩ := hQ.1
  have hlt : (a : ℝ) * meshSize L i < ‖(y' : FourTorus L m) - y‖ := by
    by_contra hle
    exact hy' ((cube_mem_iterate_addCubeLayer_iff h X a y').2 ⟨y, hQ, not_lt.1 hle⟩)
  obtain ⟨k, hk⟩ := norm_eq_nat_mul_meshSize h (sub_mem y'.2 y.2)
  have hk' : ‖(y' : FourTorus L m) - y‖ = (k : ℝ) * meshSize L i := hk
  rw [hk'] at hlt
  have hak : a < k := by
    have : (a : ℝ) < k := lt_of_mul_lt_mul_right hlt hW.le
    exact_mod_cast this
  have hak' : (a : ℝ) + 1 ≤ k := by exact_mod_cast hak
  have := norm_centres_le hq hxQ
  rw [hk'] at this
  nlinarith
theorem enlargementSupDistanceFacts_holds (h : MeshDividesSide L m i) :
    EnlargementSupDistanceFacts L m i := by
  intro X hX a
  have hW := h.1
  simp only [layerEnlargement_natCast]
  have hnot : ∀ Q ∈ standardCubePartition L m i,
      Q ∉ partitionCubesIn i ((addCubeLayer i)^[a] X) →
      ∀ q ∈ Q, ∀ x ∈ X, (a : ℝ) * meshSize L i ≤ ‖q - x‖ := by
    rintro _ ⟨y', rfl⟩ hy' q hq x hx
    exact le_norm_of_not_mem_enlargement h hX a hy' hq hx
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx
    rw [eq_sUnion_partitionCubesIn (isPartitionRegion_iterate hX a)] at hx
    obtain ⟨Q, hQ, hxQ⟩ := hx
    obtain ⟨y', rfl⟩ := hQ.1
    obtain ⟨y, hy, hn⟩ := (cube_mem_iterate_addCubeLayer_iff h X a y').1 hQ
    have hxy : ‖x - (y : FourTorus L m)‖ ≤ (a : ℝ) * meshSize L i + meshSize L i / 2 := by
      have e : x - (y : FourTorus L m) = (x - y') + ((y' : FourTorus L m) - y) := by abel
      rw [e]
      refine (norm_add_le _ _).trans ?_
      linarith [mem_cubeAround_iff.1 hxQ]
    obtain ⟨v, hv, hv'⟩ := exists_lift_abs_eq_norm (x - (y : FourTorus L m))
    choose t ht ht1 ht2 using fun μ => exists_clamped (v μ) (meshSize L i / 2) (half_pos hW).le
    have hz : (y : FourTorus L m) + torusProj (torusSide L m) t ∈ cubeAround y := by
      rw [mem_cubeAround_iff, add_sub_cancel_left]
      exact norm_torusProj_le (half_pos hW).le ht1
    have hsub : x - ((y : FourTorus L m) + torusProj (torusSide L m) t) =
        torusProj (torusSide L m) (v - t) := by
      rw [torusProj_sub_eq, hv]
      abel
    refine (setSupDist_le_norm (mem_singleton x) (hy.2 hz)).trans (ENNReal.ofReal_le_ofReal ?_)
    rw [hsub]
    refine norm_torusProj_le (by positivity) fun μ => (ht2 μ).trans (max_le (by positivity) ?_)
    have := norm_le_pi_norm (x - (y : FourTorus L m)) μ
    rw [hv' μ]
    linarith
  · intro Q hQ hn
    exact le_setSupDist_of_forall fun q hq x hx => ENNReal.ofReal_le_ofReal (hnot Q hQ hn q hq x hx)
  · intro ha Q hQ
    obtain ⟨y', rfl⟩ := hQ.1
    obtain ⟨y, hy, hn⟩ := (cube_mem_iterate_addCubeLayer_iff h X a y').1 hQ
    obtain ⟨p, q, hp, hq, hpq⟩ :=
      exists_near_points_of_cubes hW (y' : FourTorus L m) (y : FourTorus L m)
    refine (setSupDist_le_norm (mem_cubeAround_iff.2 hp) (hy.2 (mem_cubeAround_iff.2 hq))).trans
      (ENNReal.ofReal_le_ofReal (hpq.trans (max_le ?_ ?_)))
    · have : (1 : ℝ) ≤ a := by exact_mod_cast ha
      exact mul_nonneg (by linarith) hW.le
    · linarith
  · intro x hx
    have hcontra : ∀ Q ∈ standardCubePartition L m i, x ∈ Q →
        Q ∈ partitionCubesIn i ((addCubeLayer i)^[a] X) := by
      intro Q hQ hxQ
      by_contra hn
      refine absurd hx (not_lt.2 ?_)
      exact le_setSupDist_of_forall fun x' hx' b hb => by
        rw [mem_singleton_iff.1 hx']
        exact ENNReal.ofReal_le_ofReal (hnot Q hQ hn x hxQ b hb)
    constructor
    · obtain ⟨y, hy⟩ := exists_cubeAround_mem h x
      exact (hcontra _ ⟨y, rfl⟩ hy).2 hy
    · intro Q hQ hxQ
      have hmem := cube_mem_of_subset_sUnion h (C := standardCubePartition L m i \
        partitionCubesIn i ((addCubeLayer i)^[a] X)) sdiff_subset hQ.1 hQ.2
      exact hmem.2 (hcontra Q hQ.1 hxQ)
theorem meshSize_eq_pow_mul (hL : 0 < L) (i : ℤ) (n : ℕ) :
    meshSize L i = (L : ℝ) ^ n * meshSize L (i + n) := by apply _root_.YangMills.Construction.PeriodicLattice.RefinedBlockCoordinatesProof.meshSize_eq_pow_mul <;> assumption
theorem abs_le_half_pred_of_odd {M : ℕ} (hM : Odd M) {k : ℤ} (h : 2 * |(k : ℝ)| ≤ M) :
    |(k : ℝ)| ≤ ((M : ℝ) - 1) / 2 := by
  obtain ⟨c, rfl⟩ := hM
  have h1 : 2 * |k| ≤ 2 * (c : ℤ) + 1 := by
    have : ((2 * |k| : ℤ) : ℝ) ≤ ((2 * (c : ℤ) + 1 : ℤ) : ℝ) := by
      push_cast at h ⊢
      exact h
    exact_mod_cast this
  have h2 : |k| ≤ c := by omega
  have h3 : ((|k| : ℤ) : ℝ) ≤ (c : ℝ) := by exact_mod_cast h2
  rw [Int.cast_abs] at h3
  push_cast
  linarith
theorem refinedBlock_eq_blockAsGrid (hL : Odd L) (hi : -(m : ℤ) ≤ i) (n : ℕ) (y : Site L m i) :
    refinedBlock n y = blockAsGrid n y := by
  have hL0 : 0 < L := hL.pos
  have h' : MeshDividesSide L m (i + n) := meshDividesSide_of hL0 (by omega)
  have hW' := h'.1
  have hW := meshSize_eq_pow_mul hL0 i n
  have hodd : Odd (L ^ n) := hL.pow
  have hy : (y : FourTorus L m) ∈ sublattice L m (i + n) := sublattice_mono hL0 m (by omega) y.2
  ext x
  constructor
  · rintro ⟨hxc, hxl⟩
    have hxc' := mem_cubeAround_iff.1 hxc
    have hd : x - (y : FourTorus L m) ∈ sublattice L m (i + n) := sub_mem hxl hy
    obtain ⟨q, hq, hq'⟩ := exists_int_lift_of_mem_sublattice h' hd
    refine ⟨q, fun μ => ?_, ?_⟩
    · have hle : |(q μ : ℝ)| * meshSize L (i + n) ≤ (L : ℝ) ^ n * meshSize L (i + n) / 2 := by
        rw [hq' μ, ← hW]
        exact (norm_le_pi_norm _ μ).trans hxc'
      have h2 : 2 * |(q μ : ℝ)| ≤ ((L ^ n : ℕ) : ℝ) := by
        push_cast
        have : (2 * |(q μ : ℝ)|) * meshSize L (i + n) ≤ (L : ℝ) ^ n * meshSize L (i + n) := by
          linarith
        exact le_of_mul_le_mul_right this hW'
      have := abs_le_half_pred_of_odd hodd h2
      push_cast at this
      exact this
    · have : x - (y : FourTorus L m) =
          torusProj (torusSide L m) (fun μ => meshSize L (i + n) * (q μ : ℝ)) := by
        funext μ
        rw [hq μ, torusProj, mul_comm]
      rw [← this]
      abel
  · rintro ⟨p, hp, rfl⟩
    refine ⟨?_, add_mem hy ⟨p, fun μ => ?_⟩⟩
    · rw [mem_cubeAround_iff, add_sub_cancel_left, hW]
      refine norm_torusProj_le (by positivity) fun μ => ?_
      rw [abs_mul, abs_of_pos hW']
      have := mul_le_mul_of_nonneg_left (hp μ) hW'.le
      nlinarith
    · rw [torusProj, mul_comm]
theorem cubeAround_eq_iUnion_refined (hL : Odd L) (hi : -(m : ℤ) ≤ i) (n : ℕ) (y : Site L m i) :
    cubeAround y = ⋃ y' : Site L m (i + n),
      ⋃ _ : (y' : FourTorus L m) ∈ refinedBlock n y, cubeAround y' := by
  have hL0 : 0 < L := hL.pos
  have h' : MeshDividesSide L m (i + n) := meshDividesSide_of hL0 (by omega)
  have hW' := h'.1
  have hW := meshSize_eq_pow_mul hL0 i n
  have hy : (y : FourTorus L m) ∈ sublattice L m (i + n) := sublattice_mono hL0 m (by omega) y.2
  obtain ⟨c, hc⟩ : Odd (L ^ n) := hL.pow
  have hcR : (L : ℝ) ^ n = 2 * c + 1 := by exact_mod_cast hc
  rw [hcR] at hW
  apply subset_antisymm
  · intro x hx
    have hx' := mem_cubeAround_iff.1 hx
    obtain ⟨v, hv, hv'⟩ := exists_lift_abs_eq_norm (x - (y : FourTorus L m))
    have hex : ∀ μ, ∃ p : ℤ, -(c : ℤ) ≤ p ∧ p ≤ c ∧
        |v μ - (p : ℝ) * meshSize L (i + n)| ≤ meshSize L (i + n) / 2 := by
      intro μ
      have hb : |v μ| ≤ (2 * (c : ℝ) + 1) * meshSize L (i + n) / 2 := by
        rw [hv' μ, ← hW]
        exact (norm_le_pi_norm _ μ).trans hx'
      obtain ⟨hb1, hb2⟩ := abs_le.1 hb
      refine exists_int_mul_near (by omega) hW' ?_ ?_
      · push_cast
        linarith
      · push_cast
        linarith
    choose p hp1 hp2 hp3 using hex
    have hmem : (y : FourTorus L m) +
        torusProj (torusSide L m) (fun μ => meshSize L (i + n) * (p μ : ℝ)) ∈
        sublattice L m (i + n) := add_mem hy ⟨p, fun μ => by rw [torusProj, mul_comm]⟩
    refine mem_iUnion₂.2 ⟨⟨_, hmem⟩, ?_, ?_⟩
    · rw [refinedBlock_eq_blockAsGrid hL hi]
      refine ⟨p, fun μ => ?_, rfl⟩
      have h1 : -(c : ℝ) ≤ (p μ : ℝ) := by exact_mod_cast hp1 μ
      have h2 : (p μ : ℝ) ≤ (c : ℝ) := by exact_mod_cast hp2 μ
      rw [hcR, abs_le]
      constructor <;> linarith
    · rw [mem_cubeAround_iff]
      have : x - ((y : FourTorus L m) +
            torusProj (torusSide L m) fun μ => meshSize L (i + n) * (p μ : ℝ)) =
          torusProj (torusSide L m) (v - fun μ => meshSize L (i + n) * (p μ : ℝ)) := by
        rw [torusProj_sub_eq, hv]
        abel
      simp only [this]
      refine norm_torusProj_le (half_pos hW').le fun μ => ?_
      simp only [Pi.sub_apply]
      rw [mul_comm]
      exact hp3 μ
  · refine iUnion₂_subset fun y' hy' x hx => ?_
    rw [refinedBlock_eq_blockAsGrid hL hi] at hy'
    obtain ⟨p, hp, hpe⟩ := hy'
    have hn : ‖(y' : FourTorus L m) - y‖ ≤ (c : ℝ) * meshSize L (i + n) := by
      rw [hpe, add_sub_cancel_left]
      refine norm_torusProj_le (by positivity) fun μ => ?_
      rw [abs_mul, abs_of_pos hW', mul_comm]
      have := hp μ
      rw [hcR] at this
      refine mul_le_mul_of_nonneg_right ?_ hW'.le
      linarith
    rw [mem_cubeAround_iff] at hx ⊢
    have e : x - (y : FourTorus L m) = (x - y') + ((y' : FourTorus L m) - y) := by abel
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [hW]
    linarith
theorem hyperplaneContainsFace_refine (hL : Odd L) (hi : -(m : ℤ) ≤ i) (n : ℕ) (μ : Fin 4)
    (c : AddCircle (torusSide L m)) (hc : HyperplaneContainsFace L m i μ c) :
    HyperplaneContainsFace L m (i + n) μ c := by
  have hL0 : 0 < L := hL.pos
  obtain ⟨hW0, N, hN, hS⟩ := meshDividesSide_of hL0 hi
  have hW := meshSize_eq_pow_mul hL0 i n
  have hy' : ∀ y : Site L m i, (y : FourTorus L m) ∈ sublattice L m (i + n) :=
    fun y => sublattice_mono hL0 m (by omega) y.2
  obtain ⟨c₀, hc₀⟩ : Odd (L ^ n) := hL.pow
  have hcR : (L : ℝ) ^ n = 2 * c₀ + 1 := by exact_mod_cast hc₀
  rw [hcR] at hW
  obtain ⟨F, Q, ⟨y, rfl, μ', ε, hε, rfl⟩, hF⟩ := hc
  have habs : |ε * meshSize L i / 2| ≤ meshSize L i / 2 := by
    rcases hε with rfl | rfl
    · rw [one_mul, abs_of_pos (half_pos hW0)]
    · rw [neg_one_mul, neg_div, abs_neg, abs_of_pos (half_pos hW0)]
  have hpt : ∀ v : Fin 4 → ℝ, (∀ ν, |v ν| ≤ meshSize L i / 2) → v μ' = ε * meshSize L i / 2 →
      (y : FourTorus L m) μ + (v μ : AddCircle (torusSide L m)) = c := by
    intro v hv hv'
    refine hF (a := (y : FourTorus L m) + torusProj (torusSide L m) v)
      ⟨mem_cubeAround_iff.2 ?_, ?_⟩
    · rw [add_sub_cancel_left]
      exact norm_torusProj_le (half_pos hW0).le hv
    · simp only [Pi.add_apply, torusProj, hv']
  have h1 := hpt (fun ν => if ν = μ' then ε * meshSize L i / 2 else 0)
    (fun ν => by
      by_cases hν : ν = μ'
      · simpa [hν] using habs
      · simpa [hν] using (half_pos hW0).le) (by simp)
  have hμ : μ' = μ := by
    by_contra hne
    have h2 := hpt (fun ν => if ν = μ' then ε * meshSize L i / 2 else meshSize L i / 2)
      (fun ν => by
        by_cases hν : ν = μ'
        · simpa [hν] using habs
        · simp only [hν, if_false]
          rw [abs_of_pos (half_pos hW0)]) (by simp)
    have hne' : μ ≠ μ' := fun h => hne h.symm
    simp only [hne', if_false] at h1 h2
    have h3 := add_left_cancel (h2.trans h1.symm)
    obtain ⟨k, hk⟩ := exists_int_eq_add_mul_of_coe_eq h3
    rw [hS] at hk
    have h4 : (1 : ℝ) = 2 * ((k * N : ℤ) : ℝ) := by
      push_cast
      have : meshSize L i * (1 - 2 * ((k : ℝ) * N)) = 0 := by linarith
      rcases mul_eq_zero.1 this with h0 | h0
      · exact absurd h0 hW0.ne'
      · linarith
    have h5 : (1 : ℤ) = 2 * (k * N) := by exact_mod_cast h4
    omega
  subst hμ
  simp only [if_true] at h1
  obtain ⟨e, he, hee⟩ : ∃ e : ℤ, ε = e ∧ (e = 1 ∨ e = -1) := by
    rcases hε with rfl | rfl
    · exact ⟨1, by simp, Or.inl rfl⟩
    · exact ⟨-1, by simp, Or.inr rfl⟩
  have hmem : (y : FourTorus L m) + torusProj (torusSide L m) (fun ν => if ν = μ' then
      ((e * c₀ : ℤ) : ℝ) * meshSize L (i + n) else ((0 : ℤ) : ℝ) * meshSize L (i + n)) ∈
      sublattice L m (i + n) := by
    refine add_mem (hy' y) ⟨fun ν => if ν = μ' then e * c₀ else 0, fun ν => ?_⟩
    by_cases hν : ν = μ'
    · simp only [torusProj, hν, if_true]
    · simp only [torusProj, hν, if_false]
  refine ⟨{x | x ∈ cubeAround (⟨_, hmem⟩ : Site L m (i + n)) ∧ x μ' =
      ((⟨_, hmem⟩ : Site L m (i + n)) : FourTorus L m) μ' +
        ((ε * meshSize L (i + n) / 2 : ℝ) : AddCircle (torusSide L m))}, _,
    ⟨⟨_, hmem⟩, rfl, μ', ε, hε, rfl⟩, ?_⟩
  rintro x ⟨-, hx⟩
  show x μ' = c
  rw [hx, ← h1]
  simp only [Pi.add_apply, torusProj, if_true]
  rw [add_assoc, ← AddCircle.coe_add]
  congr 2
  rw [hW, he]
  push_cast
  ring
theorem refinementCubeFacts_holds (hL : Odd L) (hi : -(m : ℤ) ≤ i) (n : ℕ) :
    RefinementCubeFacts L m i n := by
  have h := meshDividesSide_of hL.pos hi
  have hfiner : ∀ y' : Site L m (i + n), ∃ y : Site L m i, cubeAround y' ⊆ cubeAround y := by
    intro y'
    have h' : MeshDividesSide L m (i + n) := meshDividesSide_of hL.pos (by omega)
    obtain ⟨y, hy⟩ := exists_cubeAround_mem h (y' : FourTorus L m)
    refine ⟨y, ?_⟩
    rw [cubeAround_eq_iUnion_refined hL hi n y]
    exact subset_iUnion₂_of_subset y' ⟨hy, y'.2⟩ subset_rfl
  refine ⟨refinedBlock_eq_blockAsGrid hL hi n, cubeAround_eq_iUnion_refined hL hi n, ?_, ?_,
    fun μ c => hyperplaneContainsFace_refine hL hi n μ c⟩
  · rintro _ ⟨y', rfl⟩
    obtain ⟨y, hs⟩ := hfiner y'
    exact ⟨_, ⟨y, rfl⟩, hs⟩
  · rintro X ⟨C, hC, rfl⟩
    refine ⟨{Q' | Q' ∈ standardCubePartition L m (i + n) ∧ ∃ Q ∈ C, Q' ⊆ Q},
      fun Q hQ => hQ.1, ?_⟩
    apply subset_antisymm
    · rintro x ⟨Q, hQ, hx⟩
      obtain ⟨y, rfl⟩ := hC hQ
      rw [cubeAround_eq_iUnion_refined hL hi n y] at hx
      obtain ⟨y', hy', hxy⟩ := mem_iUnion₂.1 hx
      refine ⟨cubeAround y', ⟨⟨y', rfl⟩, cubeAround y, hQ, ?_⟩, hxy⟩
      rw [cubeAround_eq_iUnion_refined hL hi n y]
      exact subset_iUnion₂_of_subset y' hy' subset_rfl
    · rintro x ⟨Q', ⟨-, Q, hQ, hs⟩, hx⟩
      exact ⟨Q, hQ, hs hx⟩
theorem Icc_subset_of_periodic_translates {S y₀ r a b v : ℝ} (hr : r < S) (hS : 0 < S)
    (hv : v ∈ Icc a b) (hv' : v ∈ Icc y₀ (y₀ + r))
    (H : ∀ t ∈ Icc a b, ∃ k : ℤ, t + (k : ℝ) * S ∈ Icc y₀ (y₀ + r)) :
    Icc a b ⊆ Icc y₀ (y₀ + r) := by
  have hshift : ∀ t : ℝ, y₀ + r < t → t ≤ y₀ + r + (S - r) / 2 → ∀ k : ℤ,
      t + (k : ℝ) * S ∉ Icc y₀ (y₀ + r) := by
    intro t h1 h2 k ⟨h3, h4⟩
    rcases lt_trichotomy k 0 with hk | rfl | hk
    · have : (k : ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_of_lt hk
      nlinarith
    · simp at h4
      linarith
    · have : (1 : ℝ) ≤ k := by exact_mod_cast hk
      nlinarith
  have hshift' : ∀ t : ℝ, t < y₀ → y₀ - (S - r) / 2 ≤ t → ∀ k : ℤ,
      t + (k : ℝ) * S ∉ Icc y₀ (y₀ + r) := by
    intro t h1 h2 k ⟨h3, h4⟩
    rcases lt_trichotomy k 0 with hk | rfl | hk
    · have : (k : ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_of_lt hk
      nlinarith
    · simp at h3
      linarith
    · have : (1 : ℝ) ≤ k := by exact_mod_cast hk
      nlinarith
  intro t₀ ht₀
  by_contra hn
  rw [mem_Icc, not_and_or, not_le, not_le] at hn
  rcases hn with hn | hn
  · have hmem : max t₀ (y₀ - (S - r) / 2) ∈ Icc a b := by
      refine ⟨le_max_of_le_left ht₀.1, max_le ht₀.2 ?_⟩
      linarith [hv.2, hv'.1]
    obtain ⟨k, hk⟩ := H _ hmem
    refine hshift' _ (max_lt hn ?_) (le_max_right _ _) k hk
    linarith
  · have hmem : min t₀ (y₀ + r + (S - r) / 2) ∈ Icc a b := by
      refine ⟨le_min ht₀.1 ?_, min_le_of_left_le ht₀.2⟩
      linarith [hv.1, hv'.2]
    obtain ⟨k, hk⟩ := H _ hmem
    refine hshift _ (lt_min hn ?_) (min_le_right _ _) k hk
    linarith
def LiftOverCube (i : ℤ) (C : Set (FourTorus L m)) (μ : Fin 4) (v : Fin 4 → ℝ) (n : ℤ) : Prop :=
  ∃ y : Site L m i, cubeAround y ⊆ C ∧ torusProj (torusSide L m) v ∈ cubeAround y ∧
    (y : FourTorus L m) μ = (((n : ℝ) * meshSize L i : ℝ) : AddCircle (torusSide L m)) ∧
    |v μ - (n : ℝ) * meshSize L i| ≤ meshSize L i / 2
theorem exists_liftOverCube (h : MeshDividesSide L m i) {C : Set (FourTorus L m)}
    (hC : ∀ x ∈ C, ∃ y : Site L m i, cubeAround y ⊆ C ∧ x ∈ cubeAround y) {v : Fin 4 → ℝ}
    (hv : torusProj (torusSide L m) v ∈ C) (μ : Fin 4) : ∃ n : ℤ, LiftOverCube i C μ v n := by
  obtain ⟨-, N, -, hS⟩ := h
  obtain ⟨y, hs, hy⟩ := hC _ hv
  obtain ⟨a, ha⟩ := y.2
  have e : (torusProj (torusSide L m) v - (y : FourTorus L m)) μ =
      ((v μ - (a μ : ℝ) * meshSize L i : ℝ) : AddCircle (torusSide L m)) := by
    simp only [Pi.sub_apply, torusProj, ha μ, AddCircle.coe_sub]
  have hnorm : ‖((v μ - (a μ : ℝ) * meshSize L i : ℝ) : AddCircle (torusSide L m))‖ ≤
      meshSize L i / 2 := by
    rw [← e]
    exact (norm_le_pi_norm _ μ).trans (mem_cubeAround_iff.1 hy)
  obtain ⟨u, hu, hu'⟩ := exists_coe_eq_abs_eq_norm ((v μ - (a μ : ℝ) * meshSize L i : ℝ) :
    AddCircle (torusSide L m))
  obtain ⟨k, hk⟩ := exists_int_eq_add_mul_of_coe_eq hu
  refine ⟨a μ - k * N, y, hs, hy, ?_, ?_⟩
  · rw [ha μ]
    have : (((a μ - k * N : ℤ) : ℝ) * meshSize L i) =
        (a μ : ℝ) * meshSize L i + ((-k : ℤ) : ℝ) * torusSide L m := by
      rw [hS]
      push_cast
      ring
    rw [this, coe_add_int_mul_period]
  · have : v μ - ((a μ - k * N : ℤ) : ℝ) * meshSize L i = u := by
      rw [hk, hS]
      push_cast
      ring
    rw [this, hu']
    exact hnorm
theorem update_mem_liftToCornerCube (h : MeshDividesSide L m i) {C : Set (FourTorus L m)}
    {y₀ : Fin 4 → ℝ} (hy₀ : LiesInCornerCube L m i C y₀)
    (h100 : 100 * meshSize L i < torusSide L m) {v : Fin 4 → ℝ}
    (hv : v ∈ liftToCornerCube i C y₀) {μ : Fin 4} {n : ℤ} (hn : LiftOverCube i C μ v n) {t : ℝ}
    (ht : |t - (n : ℝ) * meshSize L i| ≤ meshSize L i / 2) :
    Function.update v μ t ∈ liftToCornerCube i C y₀ := by
  have hW := h.1
  obtain ⟨y, hs, hvy, hyμ, hvn⟩ := hn
  have hcov : ∀ t : ℝ, |t - (n : ℝ) * meshSize L i| ≤ meshSize L i / 2 →
      torusProj (torusSide L m) (Function.update v μ t) ∈ C := by
    intro t ht
    apply hs
    rw [mem_cubeAround_iff]
    refine (pi_norm_le_iff_of_nonneg (half_pos hW).le).2 fun ν => ?_
    by_cases hν : ν = μ
    · subst hν
      simp only [Pi.sub_apply, torusProj, Function.update_self, hyμ]
      rw [← AddCircle.coe_sub]
      exact (addCircle_norm_coe_le_abs _).trans ht
    · have : (torusProj (torusSide L m) (Function.update v μ t) - (y : FourTorus L m)) ν =
          (torusProj (torusSide L m) v - (y : FourTorus L m)) ν := by
        simp only [Pi.sub_apply, torusProj, Function.update_of_ne hν]
      rw [this]
      exact (norm_le_pi_norm _ ν).trans (mem_cubeAround_iff.1 hvy)
  have hSpos : 0 < torusSide L m := by linarith
  have hst := Icc_subset_of_periodic_translates (S := torusSide L m) (y₀ := y₀ μ)
    (r := 100 * meshSize L i)
    (a := (n : ℝ) * meshSize L i - meshSize L i / 2)
    (b := (n : ℝ) * meshSize L i + meshSize L i / 2) (v := v μ) h100 hSpos
    (by
      obtain ⟨h1, h2⟩ := abs_le.1 hvn
      exact ⟨by linarith, by linarith⟩)
    (hv.1 μ (mem_univ μ))
    (by
      intro s hs'
      have hs2 : |s - (n : ℝ) * meshSize L i| ≤ meshSize L i / 2 :=
        abs_le.2 ⟨by linarith [hs'.1], by linarith [hs'.2]⟩
      obtain ⟨u, hu, huc⟩ := hy₀ (hcov s hs2)
      have hcoord : (u μ : AddCircle (torusSide L m)) = (s : AddCircle (torusSide L m)) := by
        have := congrFun huc μ
        simpa only [torusProj, Function.update_self] using this
      obtain ⟨k, hk⟩ := exists_int_eq_add_mul_of_coe_eq hcoord
      refine ⟨k, ?_⟩
      rw [← hk]
      exact hu μ (mem_univ μ))
  refine ⟨fun ν _ => ?_, hcov t ht⟩
  by_cases hν : ν = μ
  · subst hν
    rw [Function.update_self]
    obtain ⟨h1, h2⟩ := abs_le.1 ht
    exact hst ⟨by linarith, by linarith⟩
  · rw [Function.update_of_ne hν]
    exact hv.1 ν (mem_univ ν)
theorem isPartitionRegion_image_boundingBox (h : MeshDividesSide L m i) {C : Set (FourTorus L m)}
    (hC : ∀ x ∈ C, ∃ y : Site L m i, cubeAround y ⊆ C ∧ x ∈ cubeAround y) (hne : C.Nonempty)
    {y₀ : Fin 4 → ℝ} (hy₀ : LiesInCornerCube L m i C y₀)
    (h100 : 100 * meshSize L i < torusSide L m) :
    IsPartitionRegion i (torusProj (torusSide L m) '' boundingBox (liftToCornerCube i C y₀)) := by
  have hW := h.1
  have hAne : (liftToCornerCube i C y₀).Nonempty := by
    obtain ⟨x, hx⟩ := hne
    obtain ⟨u, hu, huc⟩ := hy₀ hx
    exact ⟨u, hu, by rw [huc]; exact hx⟩
  have hidx : ∀ v ∈ liftToCornerCube i C y₀, ∀ μ, ∃ n : ℤ, LiftOverCube i C μ v n :=
    fun v hv μ => exists_liftOverCube h hC hv.2 μ
  let P : Fin 4 → ℤ → Prop := fun μ n => ∃ v ∈ liftToCornerCube i C y₀, LiftOverCube i C μ v n
  have hPne : ∀ μ, ∃ n, P μ n := by
    intro μ
    obtain ⟨v, hv⟩ := hAne
    obtain ⟨n, hn⟩ := hidx v hv μ
    exact ⟨n, v, hv, hn⟩
  have hPbound : ∀ μ n, P μ n → y₀ μ - meshSize L i / 2 ≤ (n : ℝ) * meshSize L i ∧
      (n : ℝ) * meshSize L i ≤ y₀ μ + 100 * meshSize L i + meshSize L i / 2 := by
    rintro μ n ⟨v, hv, -, -, -, -, hvn⟩
    obtain ⟨h1, h2⟩ := abs_le.1 hvn
    obtain ⟨h3, h4⟩ := hv.1 μ (mem_univ μ)
    exact ⟨by linarith, by linarith⟩
  have hbelow : ∀ μ, ∃ b : ℤ, ∀ z, P μ z → b ≤ z := by
    intro μ
    refine ⟨⌊(y₀ μ - meshSize L i / 2) / meshSize L i⌋, fun z hz => ?_⟩
    have h1 : (y₀ μ - meshSize L i / 2) / meshSize L i ≤ z := by
      rw [div_le_iff₀ hW]
      exact (hPbound μ z hz).1
    exact_mod_cast (Int.floor_le _).trans h1
  have habove : ∀ μ, ∃ b : ℤ, ∀ z, P μ z → z ≤ b := by
    intro μ
    refine ⟨⌈(y₀ μ + 100 * meshSize L i + meshSize L i / 2) / meshSize L i⌉, fun z hz => ?_⟩
    have h1 : (z : ℝ) ≤ (y₀ μ + 100 * meshSize L i + meshSize L i / 2) / meshSize L i := by
      rw [le_div_iff₀ hW]
      exact (hPbound μ z hz).2
    exact_mod_cast h1.trans (Int.le_ceil _)
  choose n₀ hn₀ hn₀' using fun μ => Int.exists_least_of_bdd (hbelow μ) (hPne μ)
  choose n₁ hn₁ hn₁' using fun μ => Int.exists_greatest_of_bdd (habove μ) (hPne μ)
  have hle : ∀ μ, n₀ μ ≤ n₁ μ := fun μ => hn₀' μ _ (hn₁ μ)
  have hsmall : boundingBox (liftToCornerCube i C y₀) = TorusBox.boxOfIntervals
      (fun μ => (n₀ μ : ℝ) * meshSize L i - meshSize L i / 2)
      (fun μ => (n₁ μ : ℝ) * meshSize L i + meshSize L i / 2) := by
    apply subset_antisymm
    · refine sInter_subset_of_mem ⟨?_, _, _, rfl⟩
      intro v hv μ _
      obtain ⟨n, hn⟩ := hidx v hv μ
      obtain ⟨h1, h2⟩ := abs_le.1 hn.choose_spec.2.2.2
      have h3 : (n₀ μ : ℝ) ≤ n := by exact_mod_cast hn₀' μ n ⟨v, hv, hn⟩
      have h4 : (n : ℝ) ≤ n₁ μ := by exact_mod_cast hn₁' μ n ⟨v, hv, hn⟩
      constructor
      · have := mul_le_mul_of_nonneg_right h3 hW.le
        simp only
        linarith
      · have := mul_le_mul_of_nonneg_right h4 hW.le
        simp only
        linarith
    · rintro w hw _ ⟨hAP, a, b, rfl⟩ μ _
      obtain ⟨v, hv, hvn⟩ := hn₀ μ
      obtain ⟨v', hv', hvn'⟩ := hn₁ μ
      have hlo := hAP (update_mem_liftToCornerCube h hy₀ h100 hv hvn
        (t := (n₀ μ : ℝ) * meshSize L i - meshSize L i / 2) (by
          rw [sub_sub_cancel_left, abs_neg, abs_of_pos (half_pos hW)]))
      have hhi := hAP (update_mem_liftToCornerCube h hy₀ h100 hv' hvn'
        (t := (n₁ μ : ℝ) * meshSize L i + meshSize L i / 2) (by
          rw [add_sub_cancel_left, abs_of_pos (half_pos hW)]))
      have h1 := (hlo μ (mem_univ μ)).1
      have h2 := (hhi μ (mem_univ μ)).2
      rw [Function.update_self] at h1 h2
      have h3 := hw μ (mem_univ μ)
      exact ⟨h1.trans h3.1, h3.2.trans h2⟩
  rw [hsmall]
  refine ⟨{Q | ∃ p : Fin 4 → ℤ, (∀ μ, n₀ μ ≤ p μ ∧ p μ ≤ n₁ μ) ∧ ∃ y : Site L m i,
    (y : FourTorus L m) = torusProj (torusSide L m) (fun μ => (p μ : ℝ) * meshSize L i) ∧
      Q = cubeAround y}, ?_, ?_⟩
  · rintro Q ⟨p, -, y, -, rfl⟩
    exact ⟨y, rfl⟩
  · apply subset_antisymm
    · rintro _ ⟨w, hw, rfl⟩
      have hex : ∀ μ, ∃ p : ℤ, n₀ μ ≤ p ∧ p ≤ n₁ μ ∧
          |w μ - (p : ℝ) * meshSize L i| ≤ meshSize L i / 2 := fun μ =>
        exists_int_mul_near (hle μ) hW (hw μ (mem_univ μ)).1 (hw μ (mem_univ μ)).2
      choose p hp1 hp2 hp3 using hex
      refine ⟨_, ⟨p, fun μ => ⟨hp1 μ, hp2 μ⟩, ⟨_, p, fun μ => rfl⟩, rfl, rfl⟩, ?_⟩
      rw [mem_cubeAround_iff]
      have : torusProj (torusSide L m) w -
            torusProj (torusSide L m) (fun μ => (p μ : ℝ) * meshSize L i) =
          torusProj (torusSide L m) (w - fun μ => (p μ : ℝ) * meshSize L i) :=
        (torusProj_sub_eq _ _).symm
      show ‖torusProj (torusSide L m) w -
        torusProj (torusSide L m) (fun μ => (p μ : ℝ) * meshSize L i)‖ ≤ _
      rw [this]
      exact norm_torusProj_le (half_pos hW).le hp3
    · rintro x ⟨_, ⟨p, hp, y, hy, rfl⟩, hx⟩
      have hx' := mem_cubeAround_iff.1 hx
      obtain ⟨v, hv, hv'⟩ := exists_lift_abs_eq_norm (x - (y : FourTorus L m))
      have hb : ∀ μ, |v μ| ≤ meshSize L i / 2 := fun μ => by
        rw [hv' μ]
        exact (norm_le_pi_norm _ μ).trans hx'
      refine ⟨(fun μ => (p μ : ℝ) * meshSize L i) + v, fun μ _ => ?_, ?_⟩
      · obtain ⟨h1, h2⟩ := abs_le.1 (hb μ)
        have h3 : (n₀ μ : ℝ) ≤ p μ := by exact_mod_cast (hp μ).1
        have h4 : (p μ : ℝ) ≤ n₁ μ := by exact_mod_cast (hp μ).2
        have h5 := mul_le_mul_of_nonneg_right h3 hW.le
        have h6 := mul_le_mul_of_nonneg_right h4 hW.le
        simp only [Pi.add_apply]
        exact ⟨by linarith, by linarith⟩
      · rw [torusProj_add_eq, hv, ← hy]
        abel
theorem isPartitionRegion_componentBox (h : MeshDividesSide L m i) {X C : Set (FourTorus L m)}
    (hC : IsSmallRegionComponent i X C) : IsPartitionRegion i (componentBox i C) := by
  obtain ⟨⟨Q, hQ, rfl⟩, h100, y₀, hy₀⟩ := hC
  have hjoined : ∀ Q', ChainConnectedIn i X Q Q' → Q' ∈ partitionCubesIn i X := by
    rintro Q' ⟨c, hc, -, hl⟩
    exact hc.1 Q' (List.mem_of_getLast? hl)
  have hself : ChainConnectedIn i X Q Q := ⟨[Q], ⟨by simpa using hQ, by simp⟩, rfl, rfl⟩
  obtain ⟨y, rfl⟩ := hQ.1
  have hne : (⋃₀ {Q' | ChainConnectedIn i X (cubeAround y) Q'}).Nonempty :=
    ⟨y, cubeAround y, hself, centre_mem_cubeAround h y⟩
  have hcubes : ∀ x ∈ ⋃₀ {Q' | ChainConnectedIn i X (cubeAround y) Q'}, ∃ y' : Site L m i,
      cubeAround y' ⊆ ⋃₀ {Q' | ChainConnectedIn i X (cubeAround y) Q'} ∧ x ∈ cubeAround y' := by
    rintro x ⟨Q', hQ', hx⟩
    obtain ⟨y', rfl⟩ := (hjoined Q' hQ').1
    exact ⟨y', subset_sUnion_of_mem hQ', hx⟩
  exact isPartitionRegion_image_boundingBox h hcubes hne (Classical.epsilon_spec ⟨y₀, hy₀⟩) h100
theorem componentBoxesAreRegions_holds (h : MeshDividesSide L m i) :
    ComponentBoxesAreRegions L m i := by
  intro X hX
  have hstep : ∀ Y, IsPartitionRegion i Y → IsPartitionRegion i (boxingOnce i Y) := fun Y hY =>
    isPartitionRegion_union hY (isPartitionRegion_sUnion (by
      rintro _ ⟨C, hC, rfl⟩
      exact isPartitionRegion_componentBox h hC))
  have hsub : ∀ Y : Set (FourTorus L m), Y ⊆ boxingOnce i Y := fun Y => subset_union_left
  have hit : ∀ n : ℕ, IsPartitionRegion i ((boxingOnce i)^[n] X) ∧ X ⊆ (boxingOnce i)^[n] X := by
    intro n
    induction n with
    | zero => exact ⟨hX, subset_rfl⟩
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact ⟨hstep _ ih.1, ih.2.trans (hsub _)⟩
  exact ⟨fun C hC => isPartitionRegion_componentBox h hC, hstep X hX, hsub X, (hit _).1, (hit _).2⟩
theorem standardPartitionCubeGeometry_holds : StandardPartitionCubeGeometry := by
  intro L m hL _ _ i hi
  have h := meshDividesSide_of hL.pos hi
  exact ⟨fun n => refinementCubeFacts_holds hL hi n, cubeSupDistanceFacts_holds h,
    enlargementViaCentres_holds h, enlargementSupDistanceFacts_holds h,
    componentBoxesAreRegions_holds h⟩
end PeriodicLattice.StandardCubes
end
end YangMills.Construction
