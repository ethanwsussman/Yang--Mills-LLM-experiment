import YangMills.Construction.SystemOfAdmissibleConstants.SizeOfAnObservableOnABall
import YangMills.Construction.SystemOfAdmissibleConstants.TentsOfASmallSideProof
import YangMills.Construction.Torus.CollinearQuadruplesProof
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.AdmissibleConstants
open TestFunctions Matrices
open InfiniteLattice (GaugeField AmbientSpace smearedEnergy)
private theorem re_trace_energy_mem {W : ComplexMatrix2} (hW : W ∈ ComplexMatrix2.specialUnitary) :
    0 ≤ 1 - (1 / 2) * (ComplexMatrix2.fullTrace W).re ∧
      1 - (1 / 2) * (ComplexMatrix2.fullTrace W).re ≤ 2 := by
  have hunit : W ∈ Matrix.unitaryGroup (Fin 2) ℂ := (Matrix.mem_specialUnitaryGroup_iff.mp hW).1
  have hb0 := entry_norm_bound_of_unitary hunit 0 0
  have hb1 := entry_norm_bound_of_unitary hunit 1 1
  have hr0 := Complex.abs_re_le_norm (W 0 0)
  have hr1 := Complex.abs_re_le_norm (W 1 1)
  have htr : (ComplexMatrix2.fullTrace W).re = (W 0 0).re + (W 1 1).re := by
    simp [ComplexMatrix2.fullTrace, Matrix.trace_fin_two]
  rw [htr]
  have k0 := abs_le.mp (hr0.trans hb0)
  have k1 := abs_le.mp (hr1.trans hb1)
  constructor <;> linarith [k0.1, k0.2, k1.1, k1.2]
private theorem abs_finsum_smul_le_of_planes {ι : Type*} (plane : ι → Fin 4 × Fin 4)
    (hplane : ∀ i, (plane i).1 < (plane i).2) (w g : ι → ℝ) (hw : ∀ i, 0 ≤ w i ∧ w i ≤ 2) (C N : ℝ)
    (hC0 : 0 ≤ C) (hC : ∀ i, |g i| ≤ C)
    (hfiber : ∀ q, {i | g i ≠ 0 ∧ plane i = q}.Finite ∧
      (({i | g i ≠ 0 ∧ plane i = q} : Set ι).ncard : ℝ) ≤ N) :
    |∑ᶠ i, w i • g i| ≤ 12 * N * C := by
  classical
  let pairs : Finset (Fin 4 × Fin 4) := Finset.univ.filter fun q => q.1 < q.2
  have hpairs : pairs.card = 6 := by decide
  let T : Finset ι := pairs.biUnion fun q => (hfiber q).1.toFinset
  have hsupp : Function.support (fun i => w i • g i) ⊆ (T : Set ι) := by
    intro i hi
    have hg : g i ≠ 0 := by
      intro h
      apply hi
      simp [h]
    simp only [T, Finset.coe_biUnion, Set.mem_iUnion, Finset.mem_coe, Set.Finite.mem_toFinset]
    exact ⟨plane i, by simp [pairs, hplane i], ⟨hg, rfl⟩⟩
  rw [finsum_eq_sum_of_support_subset _ hsupp]
  have hcardT : (T.card : ℝ) ≤ 6 * N := by
    have k1 : T.card ≤ ∑ q ∈ pairs, ((hfiber q).1.toFinset).card := Finset.card_biUnion_le
    have k2 : ((∑ q ∈ pairs, ((hfiber q).1.toFinset).card : ℕ) : ℝ) ≤ ∑ _q ∈ pairs, N := by
      rw [Nat.cast_sum]
      refine Finset.sum_le_sum fun q _ => ?_
      rw [← Set.ncard_eq_toFinset_card _ (hfiber q).1]
      exact (hfiber q).2
    have k3 : (T.card : ℝ) ≤ ((∑ q ∈ pairs, ((hfiber q).1.toFinset).card : ℕ) : ℝ) := by
      exact_mod_cast k1
    have k4 : ∑ _q ∈ pairs, N = 6 * N := by
      rw [Finset.sum_const, hpairs]
      simp
    linarith
  calc |∑ i ∈ T, w i • g i| ≤ ∑ i ∈ T, |w i • g i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ T, 2 * C := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [smul_eq_mul, abs_mul, abs_of_nonneg (hw i).1]
        exact mul_le_mul (hw i).2 (hC i) (abs_nonneg _) (by norm_num)
    _ = T.card * (2 * C) := by simp
    _ ≤ 6 * N * (2 * C) := mul_le_mul_of_nonneg_right hcardT (by positivity)
    _ = 12 * N * C := by ring
private theorem finite_ncard_le_pow_of_injOn {ι G : Type*} (e : ι → Fin 4 → G) (A : Set ι)
    (hinj : Set.InjOn e A) (D : Fin 4 → Set G) (hD : ∀ i ∈ A, ∀ κ, e i κ ∈ D κ)
    (hDfin : ∀ κ, (D κ).Finite) (B : ℝ)
    (hB : ∀ κ, ((D κ).ncard : ℝ) ≤ B) : A.Finite ∧ (A.ncard : ℝ) ≤ B ^ 4 := by
  classical
  let F : Fin 4 → Finset G := fun κ => (hDfin κ).toFinset
  let Y : Finset (Fin 4 → G) := Fintype.piFinset F
  have hmaps : Set.MapsTo e A (Y : Set (Fin 4 → G)) := by
    intro i hi
    simp only [Y, F, Finset.mem_coe, Fintype.mem_piFinset, Set.Finite.mem_toFinset]
    exact hD i hi
  have hAfin : A.Finite := Set.Finite.of_injOn hmaps hinj Y.finite_toSet
  refine ⟨hAfin, ?_⟩
  have k1 : A.ncard ≤ (Y : Set (Fin 4 → G)).ncard :=
    Set.ncard_le_ncard_of_injOn e (fun i hi => hmaps hi) hinj Y.finite_toSet
  rw [Set.ncard_coe_finset] at k1
  have k2 : (Y.card : ℝ) = ∏ κ, ((F κ).card : ℝ) := by
    simp only [Y, Fintype.card_piFinset, Nat.cast_prod]
  have k3 : ∏ κ : Fin 4, ((F κ).card : ℝ) ≤ ∏ _κ : Fin 4, B := by
    refine Finset.prod_le_prod (fun _ _ => Nat.cast_nonneg _) fun κ _ => ?_
    have := hB κ
    rwa [Set.ncard_eq_toFinset_card _ (hDfin κ)] at this
  have k4 : (A.ncard : ℝ) ≤ Y.card := by exact_mod_cast k1
  simpa using k4.trans (k2.le.trans k3)
private theorem coset_points_in_interval {a R : ℝ} (ha : 0 < a) (hR : 0 ≤ R) (x c : ℝ) :
    {t : ℝ | |t - x| ≤ R ∧ ∃ n : ℤ, t = n * a + c}.Finite ∧
      (({t : ℝ | |t - x| ≤ R ∧ ∃ n : ℤ, t = n * a + c} : Set ℝ).ncard : ℝ) ≤ 2 * R / a + 1 := by
  classical
  set lo : ℤ := ⌈(x - R - c) / a⌉ with hlo
  set hi : ℤ := ⌊(x + R - c) / a⌋ with hhi
  let I : Finset ℝ := (Finset.Icc lo hi).image fun n : ℤ => (n : ℝ) * a + c
  have hsub : {t : ℝ | |t - x| ≤ R ∧ ∃ n : ℤ, t = n * a + c} ⊆ (I : Set ℝ) := by
    rintro t ⟨ht, n, rfl⟩
    have h := abs_le.mp ht
    simp only [I, Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_Icc]
    refine ⟨n, ⟨?_, ?_⟩, rfl⟩
    · apply Int.ceil_le.mpr
      rw [div_le_iff₀ ha]
      linarith [h.1]
    · apply Int.le_floor.mpr
      rw [le_div_iff₀ ha]
      linarith [h.2]
  refine ⟨I.finite_toSet.subset hsub, ?_⟩
  have k1 := Set.ncard_le_ncard hsub I.finite_toSet
  rw [Set.ncard_coe_finset] at k1
  have k2 : I.card ≤ (hi + 1 - lo).toNat := by
    have := Finset.card_image_le (s := Finset.Icc lo hi) (f := fun n : ℤ => (n : ℝ) * a + c)
    rwa [Int.card_Icc] at this
  have hpos : 0 ≤ 2 * R / a + 1 := by positivity
  have k3 : (((hi + 1 - lo).toNat : ℕ) : ℝ) ≤ 2 * R / a + 1 := by
    by_cases hneg : 0 ≤ hi + 1 - lo
    · have e : (((hi + 1 - lo).toNat : ℕ) : ℝ) = (hi : ℝ) + 1 - lo := by
        have : (((hi + 1 - lo).toNat : ℕ) : ℤ) = hi + 1 - lo := Int.toNat_of_nonneg hneg
        exact_mod_cast this
      rw [e]
      have u1 : (hi : ℝ) ≤ (x + R - c) / a := Int.floor_le _
      have u2 : (x - R - c) / a ≤ (lo : ℝ) := Int.le_ceil _
      have u3 : (x + R - c) / a - (x - R - c) / a = 2 * R / a := by
        field_simp
        ring
      linarith
    · rw [Int.toNat_of_nonpos (by omega)]
      simpa using hpos
  have k4 : (({t : ℝ | |t - x| ≤ R ∧ ∃ n : ℤ, t = n * a + c} : Set ℝ).ncard : ℝ) ≤
      (((hi + 1 - lo).toNat : ℕ) : ℝ) := by exact_mod_cast k1.trans k2
  exact k4.trans k3
private theorem coset_points_on_circle {S a R : ℝ} {N : ℕ} (hN : 0 < N) (hS : S = N * a)
    (ha : 0 < a) (hR : 0 ≤ R) (x : AddCircle S) (c : ℝ) :
    {t : AddCircle S | ‖t - x‖ ≤ R ∧ ∃ n : ℤ, t = ((n * a + c : ℝ) : AddCircle S)}.Finite ∧
      (({t : AddCircle S | ‖t - x‖ ≤ R ∧ ∃ n : ℤ, t = ((n * a + c : ℝ) : AddCircle S)} :
        Set (AddCircle S)).ncard : ℝ) ≤ 2 * R / a + 1 ∧
      (({t : AddCircle S | ‖t - x‖ ≤ R ∧ ∃ n : ℤ, t = ((n * a + c : ℝ) : AddCircle S)} :
        Set (AddCircle S)).ncard : ℝ) ≤ N := by
  classical
  obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective x
  obtain ⟨hfin, hcount⟩ := coset_points_in_interval ha hR y c
  set E : Set ℝ := {t : ℝ | |t - y| ≤ R ∧ ∃ n : ℤ, t = n * a + c} with hE
  set T : Set (AddCircle S) :=
    {t : AddCircle S | ‖t - (y : AddCircle S)‖ ≤ R ∧
      ∃ n : ℤ, t = ((n * a + c : ℝ) : AddCircle S)} with hT
  have hsub : T ⊆ (fun u : ℝ => (u : AddCircle S)) '' E := by
    rintro t ⟨ht, n, hn⟩
    obtain ⟨v, hv, hv'⟩ := TorusMetric.exists_coe_eq_abs_eq_norm (t - (y : AddCircle S))
    refine ⟨y + v, ⟨?_, ?_⟩, ?_⟩
    · simpa [hv'] using ht
    · have hc : ((y + v : ℝ) : AddCircle S) = t := by
        rw [AddCircle.coe_add, hv]
        abel
      have hd : ((y + v - (n * a + c) : ℝ) : AddCircle S) = 0 := by
        rw [AddCircle.coe_sub, hc, hn, sub_self]
      obtain ⟨k, hk⟩ := (AddCircle.coe_eq_zero_iff S).mp hd
      refine ⟨n + k * N, ?_⟩
      have hk' : (k : ℝ) * S = y + v - (n * a + c) := by simpa using hk
      push_cast
      rw [hS] at hk'
      linarith
    · show ((y + v : ℝ) : AddCircle S) = t
      rw [AddCircle.coe_add, hv]
      abel
  have hTfin : T.Finite := (hfin.image _).subset hsub
  have k1 : (T.ncard : ℝ) ≤ 2 * R / a + 1 := by
    have h := Set.ncard_le_ncard hsub (hfin.image _)
    have h' := Set.ncard_image_le (f := fun u : ℝ => (u : AddCircle S)) hfin
    have : (T.ncard : ℝ) ≤ E.ncard := by exact_mod_cast h.trans h'
    exact this.trans hcount
  let J : Finset (AddCircle S) :=
    (Finset.range N).image fun i : ℕ => (((i : ℤ) * a + c : ℝ) : AddCircle S)
  have hsubJ : T ⊆ (J : Set (AddCircle S)) := by
    rintro t ⟨-, n, rfl⟩
    have hNz : (N : ℤ) ≠ 0 := by exact_mod_cast hN.ne'
    have hNp : (0 : ℤ) < N := by exact_mod_cast hN
    have h0 := Int.emod_nonneg n hNz
    have h1' := Int.emod_lt_of_pos n hNp
    simp only [J, Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_range]
    refine ⟨(n % N).toNat, by omega, ?_⟩
    have e : (((n % N).toNat : ℕ) : ℤ) = n % N := Int.toNat_of_nonneg h0
    rw [e]
    have hmod : n = n % N + N * (n / N) := (Int.emod_add_mul_ediv n N).symm
    have hre : ((n : ℝ) * a + c) =
        (((n % N : ℤ) : ℝ) * a + c) + (((n / N : ℤ) : ℝ) * S) := by
      have : (n : ℝ) = ((n % N : ℤ) : ℝ) + (N : ℝ) * ((n / N : ℤ) : ℝ) := by
        exact_mod_cast hmod
      rw [hS]
      nth_rewrite 1 [this]
      ring
    have hz : ((((n / N : ℤ) : ℝ) * S : ℝ) : AddCircle S) = 0 := by
      rw [AddCircle.coe_eq_zero_iff]
      exact ⟨n / N, by simp⟩
    rw [hre, AddCircle.coe_add S (((n % N : ℤ) : ℝ) * a + c), hz, add_zero]
  have k2 : (T.ncard : ℝ) ≤ N := by
    have h := Set.ncard_le_ncard hsubJ J.finite_toSet
    rw [Set.ncard_coe_finset] at h
    have h' : J.card ≤ N := Finset.card_image_le.trans (Finset.card_range N).le
    exact_mod_cast h.trans h'
  exact ⟨hTfin, k1, k2⟩
private theorem abs_le_uniformNorm {X : Type*} {g : X → ℝ} (hg : IsBoundedFun g) (x : X) :
    |g x| ≤ uniformNorm g := by apply _root_.YangMills.Construction.QuadrupleClasses.Collinear.abs_le_uniformNorm <;> assumption
private theorem uniformNorm_nonneg' {X : Type*} (g : X → ℝ) : 0 ≤ uniformNorm g :=
  Real.iSup_nonneg fun _ => norm_nonneg _
private theorem abs_apply_le_euclidNormVec (v : Fin 4 → ℝ) (κ : Fin 4) :
    |v κ| ≤ TorusMetric.euclidNormVec v := by apply _root_.YangMills.Construction.Parametrix.UnitKernelSupport.abs_apply_le_euclidNormVec <;> assumption
private theorem norm_apply_le_torusEuclidNorm {S : ℝ} (z : TorusMetric.Torus4 S) (κ : Fin 4) :
    ‖z κ‖ ≤ TorusMetric.torusEuclidNorm z := by apply _root_.YangMills.SharedProofs.p28925 <;> assumption
private theorem abs_smearedEnergy_le {a R : ℝ} (ha : 0 < a) (hR : 0 < R) {f : AmbientSpace → ℝ}
    (hf : IsBoundedFun f) {x : AmbientSpace} (hx : tsupport f ⊆ closedBallR4 x R)
    (U : GaugeField a) :
    |smearedEnergy f U| ≤ 12 * (2 * R / a + 1) ^ 4 * uniformNorm f := by
  refine abs_finsum_smul_le_of_planes
    (fun p : InfiniteLattice.ElementaryPlaquette a => (p.lowAxis, p.highAxis))
    (fun p => p.lowAxis_lt_highAxis) (fun p => InfiniteLattice.faceEnergy U p)
    (fun p => f p.center) (fun p => re_trace_energy_mem (InfiniteLattice.faceHolonomy U p).2) _ _
    (uniformNorm_nonneg' f) (fun p => abs_le_uniformNorm hf _) ?_
  rintro ⟨μ, ν⟩
  refine finite_ncard_le_pow_of_injOn (fun p : InfiniteLattice.ElementaryPlaquette a => p.center) _ ?_
    (fun κ => {t : ℝ | |t - x κ| ≤ R ∧ ∃ n : ℤ, t = n * a +
      ((if κ = μ then a / 2 else 0) + (if κ = ν then a / 2 else 0))})
    ?_ (fun κ => (coset_points_in_interval ha hR.le _ _).1) _
    (fun κ => (coset_points_in_interval ha hR.le _ _).2)
  · rintro p ⟨-, hp⟩ q ⟨-, hq⟩ h
    obtain ⟨hp1, hp2⟩ := Prod.mk.inj hp
    obtain ⟨hq1, hq2⟩ := Prod.mk.inj hq
    have hb : (p.corner : AmbientSpace) = q.corner := by
      simp only [InfiniteLattice.ElementaryPlaquette.center, hp1, hp2, hq1, hq2] at h
      exact add_right_cancel (add_right_cancel h)
    exact InfiniteLattice.ElementaryPlaquette.ext (Subtype.ext hb) (hp1.trans hq1.symm)
      (hp2.trans hq2.symm)
  · rintro p ⟨hne, hp⟩ κ
    obtain ⟨hp1, hp2⟩ := Prod.mk.inj hp
    have hball : p.center ∈ closedBallR4 x R := hx (subset_tsupport _ hne)
    refine ⟨(abs_apply_le_euclidNormVec (p.center - x) κ).trans hball, ?_⟩
    obtain ⟨n, hn⟩ := p.corner.2
    refine ⟨n κ, ?_⟩
    simp only [InfiniteLattice.ElementaryPlaquette.center, Pi.add_apply, hn κ, Pi.single_apply,
      hp1, hp2]
    ring
private theorem abs_smearedObservable_le {L m K : ℕ} (hL : 0 < L) {R : ℝ} (hR : 0 < R)
    {f : PeriodicLattice.FourTorus L m → ℝ} (hf : IsBoundedFun f) {x : PeriodicLattice.FourTorus L m}
    (hx : tsupport f ⊆ closedBallTorus x R)
    {U : PeriodicLattice.Bond L m (K : ℤ) → ComplexMatrix2}
    (hU : ∀ b, U b ∈ ComplexMatrix2.specialUnitary) :
    |PeriodicLattice.smearedObservable f U| ≤
      12 * min ((2 * R / PeriodicLattice.meshSize L (K : ℤ) + 1) ^ 4)
        ((PeriodicLattice.torusSide L m / PeriodicLattice.meshSize L (K : ℤ)) ^ 4) *
        uniformNorm f := by
  have hL' : (0 : ℝ) < L := by exact_mod_cast hL
  set a := PeriodicLattice.meshSize L (K : ℤ) with ha_def
  have ha : 0 < a := zpow_pos hL' _
  have hNpos : 0 < 2 * L ^ (m + K) := by positivity
  have hS : PeriodicLattice.torusSide L m = ((2 * L ^ (m + K) : ℕ) : ℝ) * a := by
    simp only [ha_def, PeriodicLattice.meshSize, PeriodicLattice.torusSide, zpow_neg,
      zpow_natCast, pow_add]
    push_cast
    field_simp
  have hq : PeriodicLattice.torusSide L m / a = ((2 * L ^ (m + K) : ℕ) : ℝ) := by
    rw [hS, mul_div_assoc, div_self ha.ne', mul_one]
  have hcost : ∀ p, 0 ≤ PeriodicLattice.plaquetteCost U p ∧
      PeriodicLattice.plaquetteCost U p ≤ 2 := by
    intro p
    refine re_trace_energy_mem ?_
    refine Submonoid.list_prod_mem _ ?_
    intro W hW
    obtain ⟨b, -, rfl⟩ := List.mem_map.mp hW
    exact hU b
  refine abs_finsum_smul_le_of_planes
    (fun p : PeriodicLattice.Plaquette L m (K : ℤ) => (p.firstAxis, p.secondAxis))
    (fun p => p.firstAxis_lt_secondAxis) (fun p => PeriodicLattice.plaquetteCost U p)
    (fun p => f p.barycenter) hcost _ _ (uniformNorm_nonneg' f)
    (fun p => abs_le_uniformNorm hf _) ?_
  rintro ⟨μ, ν⟩
  let c : Fin 4 → ℝ := fun κ => (if κ = μ then a / 2 else 0) + (if κ = ν then a / 2 else 0)
  let D : Fin 4 → Set (AddCircle (PeriodicLattice.torusSide L m)) := fun κ =>
    {t | ‖t - x κ‖ ≤ R ∧
      ∃ n : ℤ, t = ((n * a + c κ : ℝ) : AddCircle (PeriodicLattice.torusSide L m))}
  have hcount := fun κ => coset_points_on_circle hNpos hS ha hR.le (x κ) (c κ)
  have hinj : Set.InjOn (fun p : PeriodicLattice.Plaquette L m (K : ℤ) => p.barycenter)
      {p | f p.barycenter ≠ 0 ∧ (p.firstAxis, p.secondAxis) = (μ, ν)} := by
    rintro p ⟨-, hp⟩ q ⟨-, hq'⟩ h
    obtain ⟨hp1, hp2⟩ := Prod.mk.inj hp
    obtain ⟨hq1, hq2⟩ := Prod.mk.inj hq'
    have hb : (p.origin : PeriodicLattice.FourTorus L m) = q.origin := by
      simp only [PeriodicLattice.Plaquette.barycenter, hp1, hp2, hq1, hq2] at h
      exact add_right_cancel (add_right_cancel h)
    exact PeriodicLattice.Plaquette.ext (Subtype.ext hb) (hp1.trans hq1.symm) (hp2.trans hq2.symm)
  have hmem : ∀ p ∈ {p : PeriodicLattice.Plaquette L m (K : ℤ) |
      f p.barycenter ≠ 0 ∧ (p.firstAxis, p.secondAxis) = (μ, ν)}, ∀ κ, p.barycenter κ ∈ D κ := by
    rintro p ⟨hne, hp⟩ κ
    obtain ⟨hp1, hp2⟩ := Prod.mk.inj hp
    have hball : p.barycenter ∈ closedBallTorus x R := hx (subset_tsupport _ hne)
    refine ⟨(norm_apply_le_torusEuclidNorm (p.barycenter - x) κ).trans hball, ?_⟩
    obtain ⟨n, hn⟩ := p.origin.2
    refine ⟨n κ, ?_⟩
    have e1 : ∀ (μ' : Fin 4) (t : ℝ), PeriodicLattice.pointOnAxis L m μ' t κ =
        ((if κ = μ' then t else 0 : ℝ) : AddCircle (PeriodicLattice.torusSide L m)) := by
      intro μ' t
      simp only [PeriodicLattice.pointOnAxis, Pi.single_apply]
      split_ifs <;> simp
    simp only [PeriodicLattice.Plaquette.barycenter, Pi.add_apply, hn κ, e1, hp1, hp2]
    rw [← AddCircle.coe_add, ← AddCircle.coe_add]
    congr 1
    simp only [c, ha_def]
    ring
  have k1 := finite_ncard_le_pow_of_injOn _ _ hinj D hmem (fun κ => (hcount κ).1) _
    (fun κ => (hcount κ).2.1)
  have k2 := finite_ncard_le_pow_of_injOn _ _ hinj D hmem (fun κ => (hcount κ).1) _
    (fun κ => (hcount κ).2.2)
  rw [← hq] at k2
  exact ⟨k1.1, le_min k1.2 k2.2⟩
private theorem gaugeFieldOfPositive_mem {L m : ℕ} {j : ℤ}
    (v : PeriodicLattice.PositivelyOrientedBond L m j → ComplexMatrix2.specialUnitary)
    (b : PeriodicLattice.Bond L m j) :
    PeriodicLattice.gaugeFieldOfPositive v b ∈ ComplexMatrix2.specialUnitary := by
  unfold PeriodicLattice.gaugeFieldOfPositive
  split_ifs with h h'
  · exact (v ⟨b, h⟩).2
  · have e : ((v ⟨b.opposite, h'⟩ : ComplexMatrix2))⁻¹ =
        ((v ⟨b.opposite, h'⟩)⁻¹ : ComplexMatrix2.specialUnitary) :=
      Matrix.inv_eq_right_inv (by
        rw [← Submonoid.coe_mul, mul_inv_cancel]
        rfl)
    rw [e]
    exact Subtype.property _
  · exact one_mem _
abbrev _root_.YangMills.SharedProofs.p42206 := @gaugeFieldOfPositive_mem
private theorem ae_forall_mem_specialUnitary (L m K : ℕ) (β : ℝ) :
    ∀ᵐ U ∂PeriodicLattice.wilsonGibbsMeasure L m K β, ∀ b, U b ∈ ComplexMatrix2.specialUnitary := by
  have hclosed : IsClosed (ComplexMatrix2.specialUnitary : Set ComplexMatrix2) := by
    have h := (isCompact_range
      (continuous_subtype_val (p := fun W : ComplexMatrix2 => W ∈ ComplexMatrix2.specialUnitary)))
    rw [Subtype.range_coe] at h
    exact h.isClosed
  have hmeas : MeasurableSet {U : PeriodicLattice.Bond L m (K : ℤ) → ComplexMatrix2 |
      ∀ b, U b ∈ ComplexMatrix2.specialUnitary} := by
    have e : {U : PeriodicLattice.Bond L m (K : ℤ) → ComplexMatrix2 |
          ∀ b, U b ∈ ComplexMatrix2.specialUnitary} =
        ⋂ b, (fun U : PeriodicLattice.Bond L m (K : ℤ) → ComplexMatrix2 => U b) ⁻¹'
          (ComplexMatrix2.specialUnitary : Set ComplexMatrix2) := by
      ext U
      simp
    rw [e]
    exact MeasurableSet.iInter fun b => measurable_pi_apply b hclosed.measurableSet
  have hbase : ∀ᵐ U ∂PeriodicLattice.productHaarMeasure L m (K : ℤ),
      ∀ b, U b ∈ ComplexMatrix2.specialUnitary := by
    unfold PeriodicLattice.productHaarMeasure
    by_cases h : AEMeasurable PeriodicLattice.gaugeFieldOfPositive
        (PeriodicLattice.gaugeFieldHaar L m (K : ℤ))
    · rw [ae_map_iff h hmeas]
      exact Filter.Eventually.of_forall fun v b => gaugeFieldOfPositive_mem v b
    · rw [Measure.map_of_not_aemeasurable h]
      simp
  unfold PeriodicLattice.wilsonGibbsMeasure
  exact Measure.ae_smul_measure ((withDensity_absolutelyContinuous _ _).ae_le hbase) _
theorem smearedObservableBound_holds : SmearedObservableBound := by
  refine ⟨?_, ?_⟩
  · rintro a R ha hR f hf ⟨x, hx⟩ U
    exact abs_smearedEnergy_le ha hR hf hx U
  · rintro L m K β R hL - hR f hf ⟨x, hx⟩
    filter_upwards [ae_forall_mem_specialUnitary L m K β] with U hU
    exact abs_smearedObservable_le (by omega) hR hf hx hU
end YangMills.Construction.AdmissibleConstants
end
