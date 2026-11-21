import YangMills.Construction.Lattice.BlockPartition
import YangMills.Construction.Lattice.BoxesOfOrderFromACornerProof
import YangMills.Construction.Lattice.GeometryOfASeparatedSequenceProof
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
open TorusMetric
namespace PeriodicLattice.CornerBoxes
variable {L m : ℕ} {j : ℤ}
theorem meshSize_pos (hL : 0 < L) (j : ℤ) : 0 < meshSize L j := by apply _root_.YangMills.SharedProofs.p6250 <;> assumption
theorem coe_unitStep_apply (μ ν : Fin 4) :
    ((unitStep L m j μ : Site L m j) : FourTorus L m) ν =
      (((if ν = μ then meshSize L j else 0 : ℝ)) : AddCircle (torusSide L m)) := by
  by_cases h : ν = μ
  · subst h
    simp [unitStep, pointOnAxis]
  · simp [unitStep, pointOnAxis, h]
theorem coe_offsetSite_apply (z : Site L m j) (t : Fin 4 → ℤ) (ν : Fin 4) :
    ((offsetSite z t : Site L m j) : FourTorus L m) ν =
      (z : FourTorus L m) ν + (((t ν : ℝ) * meshSize L j : ℝ) : AddCircle (torusSide L m)) := by apply _root_.YangMills.Construction.PeriodicLattice.OrderBoxes.offsetSite_apply <;> assumption
theorem offsetSite_offsetSite (z : Site L m j) (p t : Fin 4 → ℤ) :
    offsetSite (offsetSite z p) t = offsetSite z (p + t) := by
  simp only [offsetSite, Pi.add_apply, add_smul, Finset.sum_add_distrib, add_assoc]
theorem norm_apply_le_torusSupNorm {S : ℝ} (x : Torus4 S) (μ : Fin 4) :
    ‖x μ‖ ≤ _root_.YangMills.Construction.TorusMetric.torusSupNorm x := by apply _root_.YangMills.Construction.SequenceGeometryProof.norm_apply_le_torusSupNorm <;> assumption
theorem supNormVec_nonneg (v : Fin 4 → ℝ) : 0 ≤ supNormVec v :=
  (abs_nonneg (v 0)).trans (Finset.le_sup' (fun μ => |v μ|) (Finset.mem_univ 0))
theorem supNormVec_le {v : Fin 4 → ℝ} {r : ℝ} (h : ∀ μ, |v μ| ≤ r) : supNormVec v ≤ r :=
  Finset.sup'_le _ _ fun μ _ => h μ
theorem mem_cubeAround_iff (y : Site L m j) (c : Fin 4 → ℝ)
    (hc : torusProj (torusSide L m) c = (y : FourTorus L m)) (x : FourTorus L m) :
    x ∈ cubeAround y ↔ ∃ v : Fin 4 → ℝ, (∀ μ, |v μ - c μ| ≤ meshSize L j / 2) ∧
      torusProj (torusSide L m) v = x := by
  constructor
  · intro hx
    have hx' : _root_.YangMills.Construction.TorusMetric.torusSupNorm (x - (y : FourTorus L m)) ≤ meshSize L j / 2 := hx
    choose b hb hb' using fun μ => exists_coe_eq_abs_eq_norm ((x - (y : FourTorus L m)) μ)
    refine ⟨fun μ => c μ + b μ, fun μ => ?_, ?_⟩
    · simp only [add_sub_cancel_left]
      rw [hb' μ]
      exact (norm_apply_le_torusSupNorm _ μ).trans hx'
    · funext μ
      have hy : (c μ : AddCircle (torusSide L m)) = (y : FourTorus L m) μ := congrFun hc μ
      simp only [torusProj, AddCircle.coe_add, hb μ, hy, Pi.sub_apply]
      abel
  · rintro ⟨v, hv, rfl⟩
    have hlift : torusProj (torusSide L m) (v - c) =
        torusProj (torusSide L m) v - (y : FourTorus L m) := by
      rw [← hc]
      funext μ
      simp [torusProj]
    have hbdd : BddBelow (supNormVec ''
        (torusProj (torusSide L m) ⁻¹' {torusProj (torusSide L m) v - (y : FourTorus L m)})) :=
      ⟨0, by
        rintro _ ⟨w, -, rfl⟩
        exact supNormVec_nonneg w⟩
    exact (csInf_le hbdd ⟨v - c, hlift, rfl⟩).trans (supNormVec_le hv)
theorem eq_of_addCircle_coe_eq {S : ℝ} (hS : 0 < S) {x y : ℝ} (h : (x : AddCircle S) = y)
    (hxy : |x - y| < S) : x = y := by
  have h0 : ((x - y : ℝ) : AddCircle S) = 0 := by
    rw [AddCircle.coe_sub, h, sub_self]
  obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff S).mp h0
  rw [← hn, zsmul_eq_mul, abs_mul, abs_of_pos hS] at hxy
  have hn0 : n = 0 := by
    by_contra hne
    have h1 : (1 : ℝ) ≤ |(n : ℝ)| := by exact_mod_cast Int.one_le_abs hne
    nlinarith
  rw [hn0] at hn
  simp only [zero_smul] at hn
  linarith
theorem torusSide_eq_mul_meshSize (hL : 0 < L) {M : ℕ} (hM : (M : ℤ) = m + j) :
    torusSide L m = 2 * (L : ℝ) ^ M * meshSize L j := by
  have hL' : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  have h : (L : ℝ) ^ M = (L : ℝ) ^ m * (L : ℝ) ^ j := by
    rw [← zpow_natCast (L : ℝ) M, hM, zpow_add₀ hL', zpow_natCast]
  rw [torusSide, meshSize, h, zpow_neg]
  field_simp
theorem hasChartFaces_sitesFromCorner (hL : 0 < L) {M : ℕ} (hM : (M : ℤ) = m + j)
    (hj : -(m : ℤ) ≤ j) (z : Site L m j) (N : Fin 4 → ℤ)
    (hN : ∀ μ, 1 ≤ N μ ∧ N μ < (L : ℤ) ^ M) :
    ∃ lo hi, HasChartFaces j (sitesFromCorner z N) lo hi ∧
      ∀ μ, hi μ - lo μ = (N μ : ℝ) * meshSize L j := by
  obtain ⟨a, ha⟩ := z.2
  have hs : 0 < meshSize L j := meshSize_pos hL j
  have hS : torusSide L m = 2 * (L : ℝ) ^ M * meshSize L j := torusSide_eq_mul_meshSize hL hM
  have hSpos : 0 < torusSide L m := by rw [hS]; positivity
  have hN1 : ∀ μ, (1 : ℝ) ≤ (N μ : ℝ) := fun μ => by exact_mod_cast (hN μ).1
  have hN2 : ∀ μ, (N μ : ℝ) < (L : ℝ) ^ M := fun μ => by exact_mod_cast (hN μ).2
  have hlift : ∀ t : Fin 4 → ℤ,
      torusProj (torusSide L m) (fun μ => ((a μ + t μ : ℤ) : ℝ) * meshSize L j) =
      ((offsetSite z t : Site L m j) : FourTorus L m) := by
    intro t
    funext ν
    rw [coe_offsetSite_apply, ha ν, ← AddCircle.coe_add]
    simp only [torusProj]
    congr 1
    push_cast
    ring
  let lo : Fin 4 → ℝ := fun μ => ((a μ : ℝ) - 1 / 2) * meshSize L j
  let hi : Fin 4 → ℝ := fun μ => ((a μ : ℝ) - 1 / 2 + (N μ : ℝ)) * meshSize L j
  have hlohi : ∀ μ, hi μ - lo μ = (N μ : ℝ) * meshSize L j := fun μ => by
    simp only [lo, hi]
    ring
  have hsmall : ∀ μ, hi μ - lo μ < torusSide L m / 2 := fun μ => by
    rw [hlohi, hS]
    have := mul_lt_mul_of_pos_right (hN2 μ) hs
    linarith
  let X : Set (FourTorus L m) := torusProj (torusSide L m) '' TorusBox.boxOfIntervals lo hi
  let c : TorusBox.BoxChart (torusSide L m) X :=
    { lower := lo
      upper := hi
      lower_le_upper := fun μ => by
        have := hlohi μ
        have : 0 < (N μ : ℝ) * meshSize L j := mul_pos (by linarith [hN1 μ]) hs
        linarith
      injOn_proj := by
        intro v hv v' hv' hvv
        funext μ
        have h1 := hv μ (mem_univ μ)
        have h2 := hv' μ (mem_univ μ)
        refine eq_of_addCircle_coe_eq hSpos (congrFun hvv μ) ?_
        have := hsmall μ
        rw [abs_lt]
        constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
      image_proj := rfl }
  refine ⟨lo, hi, ⟨j, X, c, hj, le_rfl, ⟨?_, ⟨c⟩⟩, hsmall, ?_, rfl, rfl⟩, hlohi⟩
  · refine ⟨cubeAround '' sitesFromCorner z N, ?_, ?_⟩
    · rintro _ ⟨x, -, rfl⟩
      exact ⟨x, rfl⟩
    · ext p
      constructor
      · rintro ⟨v, hv, rfl⟩
        have hr : ∀ μ, ∃ t : ℤ, 0 ≤ t ∧ t < N μ ∧
            |v μ - ((a μ + t : ℤ) : ℝ) * meshSize L j| ≤ meshSize L j / 2 := by
          intro μ
          have h1 := hv μ (mem_univ μ)
          have h1a : lo μ ≤ v μ := h1.1
          have h1b : v μ ≤ hi μ := h1.2
          set r : ℝ := (v μ - lo μ) / meshSize L j with hr
          have hrv : v μ = lo μ + r * meshSize L j := by
            rw [hr]
            field_simp
            ring
          have hr0 : 0 ≤ r := div_nonneg (by linarith) hs.le
          have hrN : r ≤ (N μ : ℝ) := by
            rw [hr, div_le_iff₀ hs]
            linarith [hlohi μ]
          have hfl0 : 0 ≤ ⌊r⌋ := Int.floor_nonneg.mpr hr0
          have hfl1 : (⌊r⌋ : ℝ) ≤ r := Int.floor_le r
          have hfl2 : r < (⌊r⌋ : ℝ) + 1 := Int.lt_floor_add_one r
          refine ⟨min ⌊r⌋ (N μ - 1), le_min hfl0 (by linarith [(hN μ).1]), ?_, ?_⟩
          · have := min_le_right ⌊r⌋ (N μ - 1)
            omega
          · have hbd : ((min ⌊r⌋ (N μ - 1) : ℤ) : ℝ) ≤ r ∧
                r ≤ ((min ⌊r⌋ (N μ - 1) : ℤ) : ℝ) + 1 := by
              rcases le_total ⌊r⌋ (N μ - 1) with hle | hle
              · rw [min_eq_left hle]
                exact ⟨hfl1, hfl2.le⟩
              · rw [min_eq_right hle]
                have hle' : ((N μ : ℝ) - 1) ≤ (⌊r⌋ : ℝ) := by exact_mod_cast hle
                push_cast
                constructor <;> linarith
            generalize min ⌊r⌋ (N μ - 1) = t at hbd
            have heq : v μ - ((a μ + t : ℤ) : ℝ) * meshSize L j =
                (r - (t : ℝ) - 1 / 2) * meshSize L j := by
              rw [hrv]
              simp only [lo]
              push_cast
              ring
            rw [heq, abs_mul, abs_of_pos hs]
            have habs : |r - (t : ℝ) - 1 / 2| ≤ 1 / 2 := by
              rw [abs_le]
              constructor <;> linarith [hbd.1, hbd.2]
            nlinarith
        choose t ht0 ht1 ht2 using hr
        refine ⟨cubeAround (offsetSite z t), ⟨_, ⟨t, fun μ => ⟨ht0 μ, ht1 μ⟩, rfl⟩, rfl⟩, ?_⟩
        exact (mem_cubeAround_iff _ _ (hlift t) _).mpr ⟨v, ht2, rfl⟩
      · rintro ⟨_, ⟨_, ⟨t, ht, rfl⟩, rfl⟩, hp⟩
        obtain ⟨v, hv, rfl⟩ := (mem_cubeAround_iff _ _ (hlift t) _).mp hp
        refine ⟨v, fun μ _ => ?_, rfl⟩
        have h1 := abs_le.mp (hv μ)
        have ht0 : (0 : ℝ) ≤ (t μ : ℝ) := by exact_mod_cast (ht μ).1
        have ht1 : (t μ : ℝ) + 1 ≤ (N μ : ℝ) := by exact_mod_cast (ht μ).2
        have h2 := mul_le_mul_of_nonneg_right ht0 hs.le
        have h3 := mul_le_mul_of_nonneg_right ht1 hs.le
        push_cast at h1
        constructor
        · simp only [lo]
          nlinarith [h1.1]
        · simp only [hi]
          nlinarith [h1.2]
  · ext x
    constructor
    · rintro ⟨t, ht, rfl⟩
      refine ⟨fun μ => ((a μ + t μ : ℤ) : ℝ) * meshSize L j, fun μ _ => ?_, hlift t⟩
      have ht0 : (0 : ℝ) ≤ (t μ : ℝ) := by exact_mod_cast (ht μ).1
      have ht1 : (t μ : ℝ) + 1 ≤ (N μ : ℝ) := by exact_mod_cast (ht μ).2
      have h2 := mul_le_mul_of_nonneg_right ht0 hs.le
      have h3 := mul_le_mul_of_nonneg_right ht1 hs.le
      push_cast
      constructor
      · simp only [lo]
        nlinarith
      · simp only [hi]
        nlinarith
    · rintro ⟨v, hv, hvx⟩
      obtain ⟨b, hb⟩ := x.2
      have hc : ∀ μ, ∃ c : ℤ, v μ = (c : ℝ) * meshSize L j := by
        intro μ
        have h1 : (v μ : AddCircle (torusSide L m)) =
            (((b μ : ℝ) * meshSize L j : ℝ) : AddCircle _) :=
          (congrFun hvx μ).trans (hb μ)
        have h0 : ((v μ - (b μ : ℝ) * meshSize L j : ℝ) : AddCircle (torusSide L m)) = 0 := by
          rw [AddCircle.coe_sub, h1, sub_self]
        obtain ⟨q, hq⟩ := (AddCircle.coe_eq_zero_iff _).mp h0
        refine ⟨b μ + q * (2 * (L : ℤ) ^ M), ?_⟩
        rw [zsmul_eq_mul, hS] at hq
        push_cast
        linarith
      choose cc hcc using hc
      refine ⟨cc - a, fun μ => ?_, ?_⟩
      · have h1 := hv μ (mem_univ μ)
        have h1a : lo μ ≤ v μ := h1.1
        have h1b : v μ ≤ hi μ := h1.2
        simp only [lo, hi] at h1a h1b
        rw [hcc μ] at h1a h1b
        have h2 := le_of_mul_le_mul_right h1a hs
        have h3 := le_of_mul_le_mul_right h1b hs
        have h4 : 2 * (a μ) - 1 ≤ 2 * (cc μ) := by
          have : (2 * (a μ : ℝ) - 1) ≤ 2 * (cc μ : ℝ) := by linarith
          exact_mod_cast this
        have h5 : 2 * (cc μ) ≤ 2 * (a μ) - 1 + 2 * (N μ) := by
          have : 2 * (cc μ : ℝ) ≤ 2 * (a μ : ℝ) - 1 + 2 * (N μ : ℝ) := by linarith
          exact_mod_cast this
        simp only [Pi.sub_apply]
        omega
      · apply Subtype.ext
        rw [← hlift]
        rw [← hvx]
        funext μ
        simp only [torusProj, Pi.sub_apply, add_sub_cancel, hcc μ]
theorem coe_toSublattice (hL : 0 < L) {j' : ℤ} (h : j ≤ j') (y : Site L m j) :
    ((y.toSublattice j' : Site L m j') : FourTorus L m) = y :=
  Classical.epsilon_spec (p := fun x : Site L m j' => (x : FourTorus L m) = y)
    ⟨⟨y, sublattice_mono hL m h y.2⟩, rfl⟩
def translateBy (j' : ℤ) (y : Site L m j) (u : Fin 4 → ℤ) : FourTorus L m :=
  ((offsetSite (y.toSublattice j') u : Site L m j') : FourTorus L m)
theorem translateBy_apply (hL : 0 < L) {j' : ℤ} (h : j ≤ j') (y : Site L m j)
    (u : Fin 4 → ℤ) (ν : Fin 4) :
    translateBy j' y u ν =
      (y : FourTorus L m) ν + (((u ν : ℝ) * meshSize L j' : ℝ) : AddCircle (torusSide L m)) := by
  rw [translateBy, coe_offsetSite_apply, coe_toSublattice hL h]
theorem translateBy_shift (hL : 0 < L) {j' : ℤ} (h : j ≤ j') (y y₂ : Site L m j)
    (D : Fin 4 → ℤ)
    (hD : ∀ ν, (y₂ : FourTorus L m) ν = (y : FourTorus L m) ν +
      (((D ν : ℝ) * meshSize L j' : ℝ) : AddCircle (torusSide L m)))
    (p : Fin 4 → ℤ) : translateBy j' y₂ p = translateBy j' y (p + D) := by
  funext ν
  rw [translateBy_apply hL h, translateBy_apply hL h, hD ν, add_assoc, ← AddCircle.coe_add]
  congr 2
  simp only [Pi.add_apply]
  push_cast
  ring
theorem refinedBlock_eq_image (hP : BlockPartition.Properties)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) (hj : -(m : ℤ) ≤ j) (r : ℕ)
    {j' : ℤ} (h : j + r = j') (y : Site L m j) :
    refinedBlock r y = translateBy j' y '' blockOffsets L r := by
  subst h
  exact ((hP L m hL hm j r 0 hj).1 y).1
def integerBox (h : ℤ) (D : Fin 4 → ℤ) : Set (Fin 4 → ℤ) :=
  {u | ∀ ν, D ν - h ≤ u ν ∧ u ν ≤ D ν + h}
theorem mem_blockOffsets_iff {r : ℕ} {h : ℤ} (hh : (L : ℤ) ^ r = 2 * h + 1)
    (p : Fin 4 → ℤ) : p ∈ blockOffsets L r ↔ ∀ ν, -h ≤ p ν ∧ p ν ≤ h := by
  have key : ∀ ν, 2 * |p ν| ≤ (L : ℤ) ^ r - 1 ↔ -h ≤ p ν ∧ p ν ≤ h := by
    intro ν
    rw [hh, ← abs_le]
    constructor <;> intro _ <;> omega
  exact forall_congr' key
theorem refinedBlock_eq_image_integerBox (hP : BlockPartition.Properties)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) (hj : -(m : ℤ) ≤ j) (r : ℕ)
    {j' : ℤ} (hjj : j + r = j') {h : ℤ} (hh : (L : ℤ) ^ r = 2 * h + 1) (y y₂ : Site L m j)
    (D : Fin 4 → ℤ)
    (hD : ∀ ν, (y₂ : FourTorus L m) ν = (y : FourTorus L m) ν +
      (((D ν : ℝ) * meshSize L j' : ℝ) : AddCircle (torusSide L m))) :
    refinedBlock r y₂ = translateBy j' y '' integerBox h D := by
  have hL0 : 0 < L := by have := hL.2; omega
  have hle : j ≤ j' := by omega
  rw [refinedBlock_eq_image hP hL hm hj r hjj y₂]
  ext x
  constructor
  · rintro ⟨p, hp, rfl⟩
    refine ⟨p + D, fun ν => ?_, (translateBy_shift hL0 hle y y₂ D hD p).symm⟩
    have := ((mem_blockOffsets_iff hh p).mp hp) ν
    simp only [Pi.add_apply]
    omega
  · rintro ⟨u, hu, rfl⟩
    refine ⟨u - D, (mem_blockOffsets_iff hh _).mpr fun ν => ?_, ?_⟩
    · have := hu ν
      simp only [Pi.sub_apply]
      omega
    · rw [translateBy_shift hL0 hle y y₂ D hD, sub_add_cancel]
theorem siteImage_sitesFromCorner_blockCorner (y : Site L m j) {j' : ℤ} {N h : ℤ}
    (hN : N = 2 * h + 1) (C : Fin 4 → ℤ) :
    sitesAsTorusPoints (sitesFromCorner (blockCorner (j' := j') N y) C) =
      translateBy j' y '' {u | ∀ ν, -h ≤ u ν ∧ u ν < C ν - h} := by
  have hh : (N - 1) / 2 = h := by omega
  ext x
  constructor
  · rintro ⟨_, ⟨t, ht, rfl⟩, rfl⟩
    refine ⟨(fun _ => -h) + t, fun ν => ?_, ?_⟩
    · have := ht ν
      simp only [Pi.add_apply]
      omega
    · simp only [translateBy, blockCorner, hh, offsetSite_offsetSite]
  · rintro ⟨u, hu, rfl⟩
    refine ⟨_, ⟨u + fun _ => h, fun ν => ?_, rfl⟩, ?_⟩
    · have := hu ν
      simp only [Pi.add_apply]
      omega
    · simp only [translateBy, blockCorner, hh, offsetSite_offsetSite]
      congr 2
      funext ν
      simp only [Pi.add_apply]
      ring
theorem coe_unitStep_apply_of_meshSize_eq {j' N : ℤ}
    (hs : meshSize L j = (N : ℝ) * meshSize L j') (f ν : Fin 4) :
    ((unitStep L m j f : Site L m j) : FourTorus L m) ν =
      ((((if ν = f then N else 0 : ℤ) : ℝ) * meshSize L j' : ℝ) : AddCircle (torusSide L m)) := by
  rw [coe_unitStep_apply]
  split_ifs <;> simp [hs]
theorem meshSize_eq_mul (hL : 0 < L) (j : ℤ) (r : ℕ) :
    meshSize L j = (((L : ℤ) ^ r : ℤ) : ℝ) * meshSize L (j + r) := by
  have hL' : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  simp only [meshSize, neg_add, Int.cast_pow, Int.cast_natCast]
  rw [zpow_add₀ hL', zpow_neg (L : ℝ) (r : ℤ), zpow_natCast]
  field_simp
theorem blocksAreCornerBoxes (hP : BlockPartition.Properties)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) {K n k' : ℕ} (hnk : n ≤ k')
    (hk : k' ≤ K) :
    BlocksAreCornerBoxes L m K n k' := by
  have hL0 : 0 < L := by have := hL.2; omega
  have hj : -(m : ℤ) ≤ levelDepth K k' := by
    simp only [levelDepth]
    omega
  have hjj : levelDepth K k' + ((k' - n : ℕ) : ℤ) = levelDepth K n := by
    simp only [levelDepth]
    omega
  have hcount : 2 * (L : ℤ) ^ (k' - n) < (L : ℤ) ^ (m + K - n) := by
    have hsum : m + K - n = (k' - n) + (m + K - k') := by omega
    rw [hsum, pow_add]
    have hA : 0 < (L : ℤ) ^ (k' - n) := by positivity
    have hB : (13 : ℤ) ≤ (L : ℤ) ^ (m + K - k') := by
      have h13 : (13 : ℤ) ≤ (L : ℤ) := by exact_mod_cast hL.2
      calc (13 : ℤ) ≤ (L : ℤ) := h13
        _ = (L : ℤ) ^ 1 := (pow_one _).symm
        _ ≤ (L : ℤ) ^ (m + K - k') :=
          pow_le_pow_right₀ (by omega) (by omega)
    nlinarith
  obtain ⟨h, hh⟩ : ∃ h : ℤ, (L : ℤ) ^ (k' - n) = 2 * h + 1 := by
    obtain ⟨h, hh⟩ := hL.1.pow (n := k' - n)
    exact ⟨h, by exact_mod_cast hh⟩
  have hh0 : 0 ≤ h := by
    have : 0 < (L : ℤ) ^ (k' - n) := by positivity
    omega
  have hs : meshSize L (levelDepth K k') =
      (((L : ℤ) ^ (k' - n) : ℤ) : ℝ) * meshSize L (levelDepth K n) := by
    have := meshSize_eq_mul hL0 (levelDepth K k') (k' - n)
    rwa [hjj] at this
  intro y
  have hcounts : ∀ C : Fin 4 → ℤ, (∀ μ, C μ ≤ 2 * (L : ℤ) ^ (k' - n)) →
      CountsBoundedByDoubleBlock L m K n k' C := fun C hC => ⟨hC, hcount⟩
  have hblock := fun (y₂ : SiteAtLevel L m K k') (D : Fin 4 → ℤ) hD =>
    refinedBlock_eq_image_integerBox (y := y) (y₂ := y₂) hP hL hm hj (k' - n) hjj hh D hD
  have hzero : ∀ ν, (y : FourTorus L m) ν = (y : FourTorus L m) ν +
      (((((0 : Fin 4 → ℤ) ν : ℤ) : ℝ) * meshSize L (levelDepth K n) : ℝ) :
        AddCircle (torusSide L m)) := by
    intro ν
    simp
  have hone : ∀ μ ν,
      ((y + unitStep L m (levelDepth K k') μ : SiteAtLevel L m K k') : FourTorus L m) ν =
      (y : FourTorus L m) ν + ((((if ν = μ then (L : ℤ) ^ (k' - n) else 0 : ℤ) : ℝ) *
        meshSize L (levelDepth K n) : ℝ) : AddCircle (torusSide L m)) := by
    intro μ ν
    rw [AddSubgroup.coe_add, Pi.add_apply, coe_unitStep_apply_of_meshSize_eq hs]
  have hcorner := fun (C : Fin 4 → ℤ) =>
    siteImage_sitesFromCorner_blockCorner (j' := levelDepth K n) y hh C
  refine ⟨⟨?_, hcounts _ ?_⟩, fun μ => ⟨?_, hcounts _ ?_⟩, fun p hp => ⟨?_, hcounts _ ?_⟩⟩
  · rw [hcorner, hblock y 0 hzero]
    refine congrArg _ ?_
    ext u
    refine forall_congr' fun ν => ?_
    simp only [uniformCounts, Pi.zero_apply]
    omega
  · intro μ
    simp only [uniformCounts]
    omega
  · rw [hcorner]
    have h1 := hblock y 0 hzero
    have h2 := hblock _ _ (hone μ)
    simp only [Bond.forwardFrom]
    rw [h1, h2, ← image_union]
    refine congrArg _ ?_
    ext u
    simp only [integerBox, mem_union, mem_ofPred_eq, Pi.zero_apply]
    constructor
    · rintro (hu | hu) ν
      · have := hu ν
        by_cases hν : ν = μ
        · subst hν
          simp only [doubledCounts, Function.update_self]
          omega
        · simp only [doubledCounts, Function.update_of_ne hν, uniformCounts]
          omega
      · have := hu ν
        by_cases hν : ν = μ
        · subst hν
          simp only [doubledCounts, Function.update_self, if_true] at this ⊢
          omega
        · simp only [doubledCounts, Function.update_of_ne hν, uniformCounts, if_neg hν] at this ⊢
          omega
    · intro hu
      by_cases hμ : u μ ≤ h
      · left
        intro ν
        have := hu ν
        by_cases hν : ν = μ
        · subst hν
          simp only [doubledCounts, Function.update_self] at this
          omega
        · simp only [doubledCounts, Function.update_of_ne hν, uniformCounts] at this
          omega
      · right
        intro ν
        have := hu ν
        by_cases hν : ν = μ
        · subst hν
          simp only [doubledCounts, Function.update_self, if_true] at this ⊢
          omega
        · simp only [doubledCounts, Function.update_of_ne hν, uniformCounts, if_neg hν] at this ⊢
          omega
  · intro ν
    by_cases hν : ν = μ
    · subst hν
      simp only [doubledCounts, Function.update_self]
      omega
    · simp only [doubledCounts, Function.update_of_ne hν, uniformCounts]
      omega
  · subst hp
    have hfg : p.firstAxis ≠ p.secondAxis := p.firstAxis_lt_secondAxis.ne
    rw [hcorner]
    have h0 := hblock p.origin 0 hzero
    have h1 := hblock _ _ (hone p.firstAxis)
    have h3 := hblock _ _ (hone p.secondAxis)
    have h2 := hblock (p.origin + unitStep L m (levelDepth K k') p.firstAxis +
        unitStep L m (levelDepth K k') p.secondAxis)
      (fun ν => (if ν = p.firstAxis then (L : ℤ) ^ (k' - n) else 0) +
        (if ν = p.secondAxis then (L : ℤ) ^ (k' - n) else 0)) (fun ν => by
        rw [AddSubgroup.coe_add, Pi.add_apply, hone p.firstAxis ν,
          coe_unitStep_apply_of_meshSize_eq hs, add_assoc, ← AddCircle.coe_add]
        congr 2
        push_cast
        ring)
    simp only [Plaquette.vertices, biUnion_insert, biUnion_singleton]
    rw [h0, h1, h2, h3, ← image_union, ← image_union, ← image_union]
    refine congrArg _ ?_
    ext u
    simp only [integerBox, mem_union, mem_ofPred_eq, Pi.zero_apply]
    have hcnt : ∀ ν, plaquetteCounts (2 * h + 1) p.firstAxis p.secondAxis ν =
        (if ν = p.secondAxis then 2 * (2 * h + 1) else
          if ν = p.firstAxis then 2 * (2 * h + 1) else 2 * h + 1) := by
      intro ν
      simp only [plaquetteCounts, doubledCounts, uniformCounts, Function.update_apply]
    simp only [hh, hcnt]
    constructor
    · rintro (hu | hu | hu | hu) ν <;> have := hu ν <;>
        by_cases e1 : ν = p.firstAxis <;> by_cases e2 : ν = p.secondAxis <;>
        first
          | exact absurd (e1.symm.trans e2) hfg
          | (split_ifs at this ⊢; omega)
    · intro hu
      by_cases h1 : u p.firstAxis ≤ h <;> by_cases h2 : u p.secondAxis ≤ h
      · left
        intro ν
        have := hu ν
        by_cases e1 : ν = p.firstAxis
        · subst e1; omega
        · by_cases e2 : ν = p.secondAxis
          · subst e2; omega
          · simp only [if_neg e1, if_neg e2] at this
            omega
      · right; right; right
        intro ν
        have := hu ν
        by_cases e2 : ν = p.secondAxis
        · subst e2
          simp only [if_true] at this ⊢
          omega
        · by_cases e1 : ν = p.firstAxis
          · subst e1
            simp only [if_neg e2, if_true] at this ⊢
            omega
          · simp only [if_neg e1, if_neg e2] at this ⊢
            omega
      · right; left
        intro ν
        have := hu ν
        by_cases e1 : ν = p.firstAxis
        · subst e1
          simp only [if_neg hfg, if_true] at this ⊢
          omega
        · by_cases e2 : ν = p.secondAxis
          · subst e2
            simp only [if_neg e1, if_true] at this ⊢
            omega
          · simp only [if_neg e1, if_neg e2] at this ⊢
            omega
      · right; right; left
        intro ν
        have := hu ν
        by_cases e1 : ν = p.firstAxis
        · subst e1
          simp only [if_true, if_neg hfg] at this ⊢
          omega
        · by_cases e2 : ν = p.secondAxis
          · subst e2
            simp only [if_neg e1, if_true] at this ⊢
            omega
          · simp only [if_neg e1, if_neg e2] at this ⊢
            omega
  · intro ν
    simp only [plaquetteCounts, doubledCounts, uniformCounts, Function.update_apply]
    split_ifs <;> omega
end PeriodicLattice.CornerBoxes
namespace PeriodicLattice
theorem cornerBoxProperties_of_blockPartition (hP : BlockPartition.Properties) :
    CornerBoxProperties := by
  intro L m K hL hm _ n hn
  have hL0 : 0 < L := by have := hL.2; omega
  refine ⟨fun z N hN => ?_, fun k' hnk hk =>
    CornerBoxes.blocksAreCornerBoxes hP hL hm hnk hk⟩
  obtain ⟨lo, hi, hF, hd⟩ := CornerBoxes.hasChartFaces_sitesFromCorner hL0
    (M := m + K - n) (by simp only [levelDepth]; omega) (by simp only [levelDepth]; omega) z N hN
  exact ⟨isSiteBox_iff_hasChartFaces.mpr ⟨lo, hi, hF⟩, lo, hi, hF, hd⟩
end PeriodicLattice
end YangMills.Construction
