import YangMills.Construction.Lattice.OneStepObjectsReadInTheChartProof
import YangMills.Construction.Lattice.SiteCoordinatesProof
import YangMills.Construction.Lattice.CountingSitesBondsPlaquettes
import YangMills.Construction.Lattice.LatticesCubesOfAStandardPartitionAndEnlargements
import YangMills.Construction.Lattice.SupDistanceLatticesCubesBlocksAndComplementsProof
import YangMills.Construction.Lattice.WeightedDistanceOfASeparatedSequence
import Mathlib
set_option autoImplicit false
open Set Filter Topology
open YangMills.Construction.TorusMetric YangMills.Construction.PeriodicLattice
open YangMills.Construction.SupDistance
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.CubePartitions
variable {L m : ℕ} {i : ℤ}
theorem torusSupNorm_eq_norm {S : ℝ} (x : Torus4 S) : torusSupNorm x = ‖x‖ := by apply _root_.YangMills.Construction.PeriodicLattice.CubeRefinement.torusSupNorm_eq_norm <;> assumption
theorem supDistScaled_eq (c : ℝ) (x y : FourTorus L m) : supDistScaled c x y = c * dist x y := by
  rw [supDistScaled, torusSupNorm_eq_norm, dist_eq_norm]
theorem isSupOpen_iff {c : ℝ} (hc : 0 < c) (U : Set (FourTorus L m)) :
    IsSupOpen c U ↔ IsOpen U := by apply _root_.YangMills.Construction.SupDistance.isSupOpen_iff_isOpen <;> assumption
theorem supInterior_eq {c : ℝ} (hc : 0 < c) (A : Set (FourTorus L m)) :
    supInterior c A = interior A := by
  simp only [supInterior, interior, isSupOpen_iff hc]
theorem supClosure_eq {c : ℝ} (hc : 0 < c) (A : Set (FourTorus L m)) :
    supClosure c A = closure A := by
  simp only [supClosure, closure, isSupOpen_iff hc, isOpen_compl_iff]
theorem supTendsto_of_tendsto (c : ℝ) {u : ℕ → FourTorus L m} {p : FourTorus L m}
    (h : Tendsto u atTop (𝓝 p)) : SupTendsto c u p := by
  have h₀ := tendsto_iff_dist_tendsto_zero.1 h
  have h₁ := h₀.const_mul c
  rw [mul_zero] at h₁
  simpa only [SupTendsto, supDistScaled_eq] using h₁
theorem exists_seq_contract_tendsto (z x : FourTorus L m) :
    ∃ u : ℕ → FourTorus L m, (∀ n : ℕ, ‖u n - z‖ ≤ (1 - 1 / ((n : ℝ) + 1)) * ‖x - z‖) ∧
      Tendsto u atTop (𝓝 x) := by
  choose v hv hv' using fun μ => exists_coe_eq_abs_eq_norm ((x - z) μ)
  have hproj : torusProj (torusSide L m) v = x - z := funext hv
  have hpos : ∀ n : ℕ, 0 < (n : ℝ) + 1 := fun n => by positivity
  have hle_one : ∀ n : ℕ, 1 / ((n : ℝ) + 1) ≤ 1 := fun n => by
    rw [div_le_one (hpos n)]
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hcoord : ∀ μ, |v μ| ≤ ‖x - z‖ := fun μ => by
    rw [hv' μ]
    exact norm_le_pi_norm (x - z) μ
  let w : ℕ → Fin 4 → ℝ := fun n μ => (1 - 1 / ((n : ℝ) + 1)) * v μ
  have hfac : ∀ n : ℕ, 0 ≤ 1 - 1 / ((n : ℝ) + 1) := fun n => by linarith [hle_one n]
  refine ⟨fun n => z + torusProj (torusSide L m) (w n), fun n => ?_, ?_⟩
  · rw [add_sub_cancel_left]
    refine (pi_norm_le_iff_of_nonneg (mul_nonneg (hfac n) (norm_nonneg _))).2 fun μ => ?_
    refine (addCircle_norm_coe_le_abs _).trans ?_
    rw [abs_mul, abs_of_nonneg (hfac n)]
    exact mul_le_mul_of_nonneg_left (hcoord μ) (hfac n)
  · rw [tendsto_iff_norm_sub_tendsto_zero]
    have hlim : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1) * ‖x - z‖) atTop (𝓝 0) := by
      simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).mul_const ‖x - z‖
    refine squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_) hlim
    have hx : x = z + torusProj (torusSide L m) v := by rw [hproj]; abel
    have hsub : z + torusProj (torusSide L m) (w n) - x = fun μ =>
        (((-(1 / ((n : ℝ) + 1)) * v μ : ℝ)) : AddCircle (torusSide L m)) := by
      rw [hx]
      funext μ
      simp only [Pi.add_apply, Pi.sub_apply, torusProj, w, add_sub_add_left_eq_sub]
      rw [← AddCircle.coe_sub]
      congr 1
      ring
    rw [hsub]
    refine (pi_norm_le_iff_of_nonneg (by have := hpos n; positivity)).2 fun μ => ?_
    refine (addCircle_norm_coe_le_abs _).trans ?_
    rw [abs_mul, abs_neg, abs_of_pos (by have := hpos n; positivity)]
    exact mul_le_mul_of_nonneg_left (hcoord μ) (by have := hpos n; positivity)
theorem meshSize_pos (hL : 0 < L) (j : ℤ) : 0 < meshSize L j := by apply _root_.YangMills.SharedProofs.p6250 <;> assumption
theorem cubeAround_eq_closedBall (y : Site L m i) :
    cubeAround y = Metric.closedBall (y : FourTorus L m) (meshSize L i / 2) := by apply _root_.YangMills.Construction.SupDistance.cubeAround_eq_closedBall <;> assumption
theorem isClosed_cubeAround (y : Site L m i) : IsClosed (cubeAround y) := by apply _root_.YangMills.Construction.SeparatedSequence.isClosed_cubeAround <;> assumption
theorem center_mem_cubeAround (hL : 0 < L) (y : Site L m i) :
    (y : FourTorus L m) ∈ cubeAround y := by
  rw [cubeAround_eq_closedBall]
  exact Metric.mem_closedBall_self (by have := meshSize_pos hL i; positivity)
theorem eq_cubeAround_of_norm_lt (hS : CubeSupDistanceFacts L m i) {y : Site L m i}
    {x : FourTorus L m} (hx : ‖x - (y : FourTorus L m)‖ < meshSize L i / 2)
    {Q : Set (FourTorus L m)} (hQ : Q ∈ standardCubePartition L m i) (hxQ : x ∈ Q) :
    Q = cubeAround y :=
  hS.2.2.2.2.2.1 y x (by rwa [torusSupNorm_eq_norm]) Q hQ hxQ
theorem exists_seq_near_center_tendsto (hL : 0 < L) {y : Site L m i} {p : FourTorus L m}
    (hp : p ∈ cubeAround y) : ∃ u : ℕ → FourTorus L m,
      (∀ n, ‖u n - (y : FourTorus L m)‖ < meshSize L i / 2) ∧ Tendsto u atTop (𝓝 p) := by
  obtain ⟨u, hu, hlim⟩ := exists_seq_contract_tendsto (y : FourTorus L m) p
  refine ⟨u, fun n => ?_, hlim⟩
  have ha := meshSize_pos hL i
  have hpos : 0 < (n : ℝ) + 1 := by positivity
  have hp' : ‖p - (y : FourTorus L m)‖ ≤ meshSize L i / 2 := by
    rw [cubeAround_eq_closedBall, Metric.mem_closedBall, dist_eq_norm] at hp
    exact hp
  have hq : 0 < 1 / ((n : ℝ) + 1) := by positivity
  have hq₁ : 1 / ((n : ℝ) + 1) ≤ 1 := by
    rw [div_le_one hpos]
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  calc ‖u n - (y : FourTorus L m)‖ ≤ (1 - 1 / ((n : ℝ) + 1)) * ‖p - (y : FourTorus L m)‖ := hu n
    _ ≤ (1 - 1 / ((n : ℝ) + 1)) * (meshSize L i / 2) :=
        mul_le_mul_of_nonneg_left hp' (by linarith)
    _ < meshSize L i / 2 := by nlinarith
def axisCount (L m : ℕ) (i : ℤ) : ℕ := 2 * L ^ ((m : ℤ) + i).toNat
theorem axisCount_pos (hL : 0 < L) : 0 < axisCount L m i := by apply _root_.YangMills.Construction.PeriodicLattice.Counting.sitesPerAxis_pos <;> assumption
theorem axisCount_cast (hi : -(m : ℤ) ≤ i) :
    (axisCount L m i : ℝ) = sitesPerAxis L m i := by
  have h : (((m : ℤ) + i).toNat : ℤ) = (m : ℤ) + i := Int.toNat_of_nonneg (by omega)
  simp only [axisCount, sitesPerAxis]
  push_cast
  rw [← zpow_natCast, h]
theorem torusSide_eq (hL : 0 < L) (hi : -(m : ℤ) ≤ i) :
    torusSide L m = (axisCount L m i : ℝ) * meshSize L i := by apply _root_.YangMills.DeltaSharedProofs.p501486 <;> assumption
theorem coe_mul_meshSize_eq_zero_iff (hL : 0 < L) (hi : -(m : ℤ) ≤ i) (k : ℤ) :
    (((k : ℝ) * meshSize L i : ℝ) : AddCircle (torusSide L m)) = 0 ↔
      (axisCount L m i : ℤ) ∣ k := by apply _root_.YangMills.DeltaSharedProofs.p501788 <;> assumption
theorem coe_mul_meshSize_eq_iff (hL : 0 < L) (hi : -(m : ℤ) ≤ i) (k k' : ℤ) :
    (((k : ℝ) * meshSize L i : ℝ) : AddCircle (torusSide L m)) =
        (((k' : ℝ) * meshSize L i : ℝ)) ↔
      (axisCount L m i : ℤ) ∣ k - k' := by
  rw [← coe_mul_meshSize_eq_zero_iff hL hi, ← sub_eq_zero, ← AddCircle.coe_sub]
  push_cast
  rw [sub_mul]
def siteOfCoords (L m : ℕ) (i : ℤ) (n : Fin 4 → Fin (axisCount L m i)) : Site L m i :=
  ⟨fun μ => ((((n μ : ℕ) : ℤ) : ℝ) * meshSize L i : ℝ), ⟨fun μ => ((n μ : ℕ) : ℤ), fun _ => rfl⟩⟩
theorem fin_eq_of_natCast_dvd_sub {N : ℕ} {a b : Fin N}
    (h : (N : ℤ) ∣ ((a : ℕ) : ℤ) - ((b : ℕ) : ℤ)) : a = b := by
  have ha := a.isLt
  have hb := b.isLt
  have h₀ : ((a : ℕ) : ℤ) - ((b : ℕ) : ℤ) = 0 :=
    Int.eq_zero_of_abs_lt_dvd h (abs_lt.2 ⟨by omega, by omega⟩)
  exact Fin.ext (by omega)
theorem site_finite (hL : 0 < L) (hi : -(m : ℤ) ≤ i) : Finite (Site L m i) := by apply _root_.YangMills.Construction.PeriodicLattice.Counting.site_finite <;> assumption
theorem nat_card_site (hL : 0 < L) (hi : -(m : ℤ) ≤ i) :
    Nat.card (Site L m i) = axisCount L m i ^ 4 := by apply _root_.YangMills.Construction.PeriodicLattice.Counting.card_site_eq <;> assumption
theorem coe_zsmul_unitStep (k : ℤ) (μ : Fin 4) :
    ((k • unitStep L m i μ : Site L m i) : FourTorus L m) =
      Pi.single μ (((k : ℝ) * meshSize L i : ℝ) : AddCircle (torusSide L m)) := by apply _root_.YangMills.Construction.PeriodicLattice.ChartInvariance.coe_zsmul_unitStep <;> assumption
theorem zsmul_unitStep_eq_zero_iff (hL : 0 < L) (hi : -(m : ℤ) ≤ i) (k : ℤ) (μ : Fin 4) :
    k • unitStep L m i μ = 0 ↔ (axisCount L m i : ℤ) ∣ k := by
  rw [← coe_mul_meshSize_eq_zero_iff hL hi, ← Subtype.coe_inj, coe_zsmul_unitStep]
  constructor
  · intro h
    simpa using congrFun h μ
  · intro h
    rw [h]
    simp
theorem ncard_range_add_zsmul (hL : 0 < L) (hi : -(m : ℤ) ≤ i) (y : Site L m i) (μ : Fin 4) :
    (range fun k : ℤ => y + k • unitStep L m i μ).ncard = axisCount L m i := by
  have hN : 0 < (axisCount L m i : ℤ) := by exact_mod_cast axisCount_pos (m := m) (i := i) hL
  let f : Fin (axisCount L m i) → Site L m i := fun k => y + ((k : ℕ) : ℤ) • unitStep L m i μ
  have hf : Function.Injective f := by
    intro a b h
    have h₁ : (((a : ℕ) : ℤ) - ((b : ℕ) : ℤ)) • unitStep L m i μ = 0 := by
      have h₂ : ((a : ℕ) : ℤ) • unitStep L m i μ = ((b : ℕ) : ℤ) • unitStep L m i μ :=
        add_left_cancel h
      rw [sub_smul, h₂, sub_self]
    exact fin_eq_of_natCast_dvd_sub ((zsmul_unitStep_eq_zero_iff hL hi _ μ).1 h₁)
  have hrange : (range fun k : ℤ => y + k • unitStep L m i μ) = f '' univ := by
    ext z
    constructor
    · rintro ⟨k, rfl⟩
      have hnn : 0 ≤ k % (axisCount L m i : ℤ) := Int.emod_nonneg _ hN.ne'
      have hlt : k % (axisCount L m i : ℤ) < axisCount L m i := Int.emod_lt_of_pos _ hN
      refine ⟨⟨(k % (axisCount L m i : ℤ)).toNat, by omega⟩, mem_univ _, ?_⟩
      have h₀ : (k - k % (axisCount L m i : ℤ)) • unitStep L m i μ = 0 := by
        rw [zsmul_unitStep_eq_zero_iff hL hi, Int.emod_def]
        exact ⟨k / (axisCount L m i : ℤ), by ring⟩
      show y + (((k % (axisCount L m i : ℤ)).toNat : ℕ) : ℤ) • unitStep L m i μ = _
      rw [Int.toNat_of_nonneg hnn]
      rw [sub_smul, sub_eq_zero] at h₀
      show _ = y + k • unitStep L m i μ
      rw [h₀]
    · rintro ⟨k, -, rfl⟩
      exact ⟨((k : ℕ) : ℤ), rfl⟩
  rw [hrange, ncard_image_of_injective _ hf, ncard_univ, Nat.card_fin]
theorem cubeAround_injective (hL : 0 < L) (hS : CubeSupDistanceFacts L m i) :
    Function.Injective (cubeAround : Site L m i → Set (FourTorus L m)) := by
  intro y y' h
  have ha := meshSize_pos hL i
  have hy : (y : FourTorus L m) ∈ cubeAround y' := h ▸ center_mem_cubeAround hL y
  obtain ⟨n, hn⟩ := hS.1 y y'
  have hle : torusSupNorm ((y : FourTorus L m) - (y' : FourTorus L m)) ≤ meshSize L i / 2 := hy
  rw [hn] at hle
  have hn₀ : n = 0 := by
    by_contra hne
    have h₁ : (1 : ℝ) ≤ n := by exact_mod_cast Nat.pos_of_ne_zero hne
    nlinarith
  rw [hn₀, Nat.cast_zero, zero_mul, torusSupNorm_eq_norm, norm_eq_zero, sub_eq_zero] at hn
  exact Subtype.ext hn
theorem finite_standardCubePartition (hL : 0 < L) (hi : -(m : ℤ) ≤ i) :
    (standardCubePartition L m i).Finite := by
  have := site_finite (m := m) (i := i) hL hi
  exact finite_range _
theorem isClosed_sUnion_of_subset_partition (hL : 0 < L) (hi : -(m : ℤ) ≤ i)
    {C : Set (Set (FourTorus L m))} (hC : C ⊆ standardCubePartition L m i) : IsClosed (⋃₀ C) := by
  rw [sUnion_eq_biUnion]
  refine ((finite_standardCubePartition hL hi).subset hC).isClosed_biUnion fun Q hQ => ?_
  obtain ⟨y, rfl⟩ := hC hQ
  exact isClosed_cubeAround y
theorem latticeAndCubeCounts (hL : 0 < L) (hi : -(m : ℤ) ≤ i) (hS : CubeSupDistanceFacts L m i)
    (c : ℝ) : LatticeAndCubeCounts L m c i := by
  have := site_finite (m := m) (i := i) hL hi
  have hinj := cubeAround_injective hL hS
  refine ⟨?_, fun y μ => ?_, ?_, ?_, ?_, finite_standardCubePartition hL hi, fun y μ => ?_, ?_⟩
  · rw [nat_card_site hL hi, ← axisCount_cast hi]
    push_cast
    rfl
  · rw [ncard_range_add_zsmul hL hi, axisCount_cast hi]
  · exact Finite.of_injective (fun b : Bond L m i => (b.source, b.target)) fun b b' h =>
      Bond.ext (congrArg Prod.fst h) (congrArg Prod.snd h)
  · exact Finite.of_injective
      (fun p : Plaquette L m i => (p.origin, p.firstAxis, p.secondAxis)) fun p p' h =>
      Plaquette.ext (congrArg Prod.fst h) (congrArg (fun q => q.2.1) h)
        (congrArg (fun q => q.2.2) h)
  · refine ⟨fun _ _ => ⟨_, rfl⟩, hinj.injOn, ?_⟩
    rintro _ ⟨y, rfl⟩
    exact ⟨y, mem_univ _, rfl⟩
  · have himg : (range fun k : ℤ => cubeAround (y + k • unitStep L m i μ)) =
        (cubeAround : Site L m i → Set (FourTorus L m)) ''
          range fun k : ℤ => y + k • unitStep L m i μ := by
      rw [← range_comp]
      rfl
    rw [himg, ncard_image_of_injective _ hinj, ncard_range_add_zsmul hL hi, axisCount_cast hi]
  · rw [torusSide_eq hL hi, axisCount_cast hi]
    ring
theorem not_mem_cube_of_mem_interior_sUnion (hL : 0 < L) (hS : CubeSupDistanceFacts L m i)
    {C : Set (Set (FourTorus L m))} {x : FourTorus L m} (hx : x ∈ interior (⋃₀ C))
    (hC : C ⊆ standardCubePartition L m i) {Q : Set (FourTorus L m)}
    (hQ : Q ∈ standardCubePartition L m i) (hQC : Q ∉ C) : x ∉ Q := by
  obtain ⟨y, rfl⟩ := hQ
  intro hxQ
  obtain ⟨u, hnear, hlim⟩ := exists_seq_near_center_tendsto hL hxQ
  obtain ⟨n, hn⟩ := (hlim.eventually (isOpen_interior.mem_nhds hx)).exists
  obtain ⟨Q', hQ', hu⟩ := interior_subset hn
  exact hQC (eq_cubeAround_of_norm_lt hS (hnear n) (hC hQ') hu ▸ hQ')
theorem cubePointsAndInteriors (hL : 0 < L) (hS : CubeSupDistanceFacts L m i) {c : ℝ}
    (hc : 0 < c) : CubePointsAndInteriors L m c i := by
  refine ⟨fun y p hp => ?_, fun C hC x hx Q hQ hQC => ?_, fun C hC C' hC' hdisj => ?_⟩
  · obtain ⟨u, hnear, hlim⟩ := exists_seq_near_center_tendsto hL hp
    refine ⟨u, fun n => ?_, supTendsto_of_tendsto c hlim⟩
    rw [supDistScaled_eq, dist_eq_norm]
    have := mul_lt_mul_of_pos_left (hnear n) hc
    linarith
  · rw [supInterior_eq hc] at hx
    exact not_mem_cube_of_mem_interior_sUnion hL hS hx hC hQ hQC
  · rw [supInterior_eq hc, supInterior_eq hc, Set.disjoint_left]
    intro x hx hx'
    obtain ⟨Q, hQ, hxQ⟩ := interior_subset hx
    exact not_mem_cube_of_mem_interior_sUnion hL hS hx' hC' (hC hQ)
      (fun hQ' => Set.disjoint_left.1 hdisj hQ hQ') hxQ
theorem subsetInteriorOfMeetingCubes (hL : 0 < L) (hi : -(m : ℤ) ≤ i)
    (hS : CubeSupDistanceFacts L m i) {c : ℝ} (hc : 0 < c) :
    SubsetInteriorOfMeetingCubes L m c i := by
  intro X
  rw [supInterior_eq hc]
  set C : Set (Set (FourTorus L m)) :=
    {Q | Q ∈ standardCubePartition L m i ∧ CubeIntersects Q X} with hCdef
  have hclosed : IsClosed (⋃₀ (standardCubePartition L m i \ C)) :=
    isClosed_sUnion_of_subset_partition hL hi sdiff_subset
  have hsub : (⋃₀ (standardCubePartition L m i \ C))ᶜ ⊆ ⋃₀ C := by
    intro x hx
    have hcov : x ∈ ⋃₀ standardCubePartition L m i := by
      rw [hS.2.2.2.2.1]
      exact mem_univ x
    obtain ⟨Q, hQ, hxQ⟩ := hcov
    by_contra hnot
    exact hx ⟨Q, ⟨hQ, fun hQC => hnot ⟨Q, hQC, hxQ⟩⟩, hxQ⟩
  refine fun x hx => interior_mono hsub ?_
  rw [hclosed.isOpen_compl.interior_eq]
  rintro ⟨Q, ⟨hQ, hQC⟩, hxQ⟩
  exact hQC ⟨hQ, x, hxQ, hx⟩
theorem finerCubeSubsetOfUnion (hL : 0 < L) (hS : CubeSupDistanceFacts L m i)
    (hR : ∀ n : ℕ, RefinementCubeFacts L m i n) : FinerCubeSubsetOfUnion L m i := by
  intro i' hii' C hC y' hy'
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, i' = i + n := ⟨(i' - i).toNat, by omega⟩
  have hRn := hR n
  obtain ⟨Q', ⟨y, rfl⟩, hsub⟩ := hRn.2.2.1 (cubeAround y') ⟨y', rfl⟩
  have hblock : (y' : FourTorus L m) ∈ refinedBlock n y :=
    ⟨hsub (center_mem_cubeAround hL y'), y'.2⟩
  rw [hRn.1 y] at hblock
  obtain ⟨p, hp, hx⟩ := hblock
  have hL' : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  have ha' := meshSize_pos hL (i + n)
  have hscale : meshSize L (i + n) * (L : ℝ) ^ n = meshSize L i := by
    simp only [meshSize]
    rw [neg_add, zpow_add₀ hL', zpow_neg _ (n : ℤ), zpow_natCast]
    field_simp
  have hnear : ‖(y' : FourTorus L m) - (y : FourTorus L m)‖ < meshSize L i / 2 := by
    rw [hx, add_sub_cancel_left]
    have hb : (0 : ℝ) ≤ meshSize L (i + n) * (((L : ℝ) ^ n - 1) / 2) := by
      have h₁ : 0 ≤ ((L : ℝ) ^ n - 1) / 2 := (abs_nonneg _).trans (hp 0)
      positivity
    refine lt_of_le_of_lt ((pi_norm_le_iff_of_nonneg hb).2 fun μ => ?_) ?_
    · refine (addCircle_norm_coe_le_abs _).trans ?_
      rw [abs_mul, abs_of_pos ha']
      exact mul_le_mul_of_nonneg_left (hp μ) ha'.le
    · nlinarith
  obtain ⟨Q, hQC, hyQ⟩ := hy'
  have hQ := eq_cubeAround_of_norm_lt hS hnear (hC hQC) hyQ
  exact ⟨Q, hQC, hQ ▸ hsub⟩
theorem isClosed_layerEnlargement (hL : 0 < L) (hi : -(m : ℤ) ≤ i) (X : Set (FourTorus L m))
    (k : ℕ) : IsClosed (layerEnlargement i X ((k + 1 : ℕ) : ℤ)) := by
  have h : layerEnlargement i X ((k + 1 : ℕ) : ℤ) = addCubeLayer i ((addCubeLayer i)^[k] X) :=
    Function.iterate_succ_apply' (addCubeLayer i) k X
  rw [h]
  exact isClosed_sUnion_of_subset_partition hL hi fun Q hQ => hQ.1
theorem mem_layerEnlargement_of_setSupDist_le (hL : 0 < L) (hi : -(m : ℤ) ≤ i)
    (hE : EnlargementSupDistanceFacts L m i) {X : Set (FourTorus L m)}
    (hX : IsPartitionRegion i X) (n : ℕ) {x : FourTorus L m}
    (hx : setSupDist ({x} : Set (FourTorus L m)) X ≤ ENNReal.ofReal ((n : ℝ) * meshSize L i)) :
    x ∈ layerEnlargement i X (n : ℤ) := by
  have ha := meshSize_pos hL i
  have : Fact (0 < torusSide L m) :=
    ⟨by rw [torusSide]; have : (0 : ℝ) < L := by exact_mod_cast hL
        positivity⟩
  have hsingle : ∀ w : FourTorus L m, setSupDist ({w} : Set (FourTorus L m)) X =
      ⨅ b ∈ X, ENNReal.ofReal ‖w - b‖ := by
    intro w
    simp [setSupDist, torusSupNorm_eq_norm]
  rcases X.eq_empty_or_nonempty with rfl | hne
  · have htop : setSupDist ({x} : Set (FourTorus L m)) ∅ = ⊤ := by simp [hsingle]
    rw [htop] at hx
    exact (ENNReal.ofReal_ne_top (top_le_iff.1 hx)).elim
  obtain ⟨C, hC, rfl⟩ := hX
  have hcpt : IsCompact (⋃₀ C) := (isClosed_sUnion_of_subset_partition hL hi hC).isCompact
  have hcont : ContinuousOn (fun z : FourTorus L m => ‖x - z‖) (⋃₀ C) := by fun_prop
  obtain ⟨z, hz, hmin⟩ := hcpt.exists_isMinOn hne hcont
  have hle : ENNReal.ofReal ‖x - z‖ ≤ ENNReal.ofReal ((n : ℝ) * meshSize L i) := by
    refine le_trans ?_ hx
    rw [hsingle]
    exact le_iInf₂ fun b hb => ENNReal.ofReal_le_ofReal (hmin hb)
  have hnn : (0 : ℝ) ≤ (n : ℝ) * meshSize L i := by positivity
  rw [ENNReal.ofReal_le_ofReal_iff hnn] at hle
  rcases n with _ | k
  · have hxz : x = z := by
      have h₀ : ‖x - z‖ ≤ 0 := by simpa using hle
      exact sub_eq_zero.1 (norm_le_zero_iff.1 h₀)
    rw [hxz]
    exact hz
  · have hr : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) * meshSize L i := by positivity
    obtain ⟨u, hu, hlim⟩ := exists_seq_contract_tendsto z x
    refine (isClosed_layerEnlargement hL hi _ k).mem_of_tendsto hlim
      (Eventually.of_forall fun t => ?_)
    have hpos : 0 < (t : ℝ) + 1 := by positivity
    have hq : 0 < 1 / ((t : ℝ) + 1) := by positivity
    have hq₁ : 1 / ((t : ℝ) + 1) ≤ 1 := by
      rw [div_le_one hpos]
      have : (0 : ℝ) ≤ t := Nat.cast_nonneg t
      linarith
    have hlt : ‖u t - z‖ < ((k + 1 : ℕ) : ℝ) * meshSize L i := by
      calc ‖u t - z‖ ≤ (1 - 1 / ((t : ℝ) + 1)) * ‖x - z‖ := hu t
        _ ≤ (1 - 1 / ((t : ℝ) + 1)) * (((k + 1 : ℕ) : ℝ) * meshSize L i) :=
            mul_le_mul_of_nonneg_left hle (by linarith)
        _ < ((k + 1 : ℕ) : ℝ) * meshSize L i := by nlinarith
    have hd : setSupDist ({u t} : Set (FourTorus L m)) (⋃₀ C) <
        ENNReal.ofReal (((k + 1 : ℕ) : ℝ) * meshSize L i) := by
      rw [hsingle]
      refine lt_of_le_of_lt (iInf₂_le z hz) ?_
      exact (ENNReal.ofReal_lt_ofReal_iff hr).2 hlt
    exact ((hE _ ⟨C, hC, rfl⟩ (k + 1)).2.2.2 _ hd).1
theorem enlargementEqNeighborhood (hL : 0 < L) (hi : -(m : ℤ) ≤ i)
    (hE : EnlargementSupDistanceFacts L m i) {c : ℝ} (hc : 0 < c) :
    EnlargementEqNeighborhood L m c i := by
  intro X hX n
  have hiff : ∀ x : FourTorus L m, infSupDist c x X ≤
      ENNReal.ofReal ((n : ℝ) * (c * meshSize L i)) ↔
        setSupDist ({x} : Set (FourTorus L m)) X ≤ ENNReal.ofReal ((n : ℝ) * meshSize L i) := by
    intro x
    have h₁ : (n : ℝ) * (c * meshSize L i) = c * ((n : ℝ) * meshSize L i) := by ring
    rw [infSupDist, h₁, ENNReal.ofReal_mul hc.le]
    exact ENNReal.mul_le_mul_iff_right (by simpa using hc) ENNReal.ofReal_ne_top
  ext x
  show infSupDist c x X ≤ _ ↔ _
  rw [hiff x]
  exact ⟨mem_layerEnlargement_of_setSupDist_le hL hi hE hX n, (hE X hX n).1 x⟩
theorem closureDiffRegions (hL : 0 < L) (hi : -(m : ℤ) ≤ i) (hS : CubeSupDistanceFacts L m i)
    {c : ℝ} (hc : 0 < c) : ClosureDiffRegions L m c i := by
  intro X X' hX hX'
  rw [supClosure_eq hc]
  apply subset_antisymm
  · refine closure_minimal ?_ (isClosed_sUnion_of_subset_partition hL hi fun Q hQ => hQ.1.1)
    rintro x ⟨hxX, hxX'⟩
    obtain ⟨C, hC, rfl⟩ := hX
    obtain ⟨Q, hQ, hxQ⟩ := hxX
    exact ⟨Q, ⟨⟨hC hQ, subset_sUnion_of_mem hQ⟩, fun hQ' => hxX' (hQ'.2 hxQ)⟩, hxQ⟩
  · rintro p ⟨Q, ⟨⟨⟨y, rfl⟩, hQX⟩, hQX'⟩, hp⟩
    obtain ⟨u, hnear, hlim⟩ := exists_seq_near_center_tendsto hL hp
    refine mem_closure_of_tendsto hlim (Eventually.of_forall fun n => ⟨?_, ?_⟩)
    · refine hQX ?_
      rw [cubeAround_eq_closedBall, Metric.mem_closedBall, dist_eq_norm]
      exact (hnear n).le
    · intro hu
      obtain ⟨C', hC', rfl⟩ := hX'
      obtain ⟨Q', hQ', huQ'⟩ := hu
      have hEq := eq_cubeAround_of_norm_lt hS (hnear n) (hC' hQ') huQ'
      exact hQX' ⟨⟨y, rfl⟩, hEq ▸ subset_sUnion_of_mem hQ'⟩
theorem cubePartitionFacts (hcubes : PeriodicLattice.StandardPartitionCubeGeometry) :
    CubePartitionFacts := by
  intro s i hi c hunit
  have hadm := s.isAdmissible
  have hL : 0 < s.L := by
    have := hadm.2
    omega
  have hc : 0 < c := by
    rcases hunit with rfl | ⟨k, -, rfl⟩
    · exact one_pos
    · have hL' : (0 : ℝ) < s.L := by exact_mod_cast hL
      simpa [toLevelUnits] using zpow_pos hL' _
  obtain ⟨hR, hS, -, hE, -⟩ := hcubes s.L s.m hadm.1 hadm.2 s.m.pos i hi
  exact ⟨latticeAndCubeCounts hL hi hS c, cubePointsAndInteriors hL hS hc,
    subsetInteriorOfMeetingCubes hL hi hS hc, finerCubeSubsetOfUnion hL hS hR,
    enlargementEqNeighborhood hL hi hE hc, closureDiffRegions hL hi hS hc⟩
end YangMills.Construction.CubePartitions
end
