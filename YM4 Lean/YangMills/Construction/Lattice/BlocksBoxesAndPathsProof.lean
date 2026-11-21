import YangMills.Construction.Lattice.BlockPartition
import YangMills.Construction.Lattice.BlocksBoxesAndPaths
import YangMills.Construction.Lattice.PathsOfBlocksAndDoubleBlocksProof
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.PeriodicLattice.BlocksBoxesPaths
variable {L m : ℕ} {j j' : ℤ}
private theorem two_halfSideSteps_add_one (hO : Odd L) (i : ℕ) :
    2 * halfSideSteps L i + 1 = (L : ℤ) ^ i := by
  have h : Odd ((L : ℤ) ^ i) := (by exact_mod_cast hO : Odd (L : ℤ)).pow
  obtain ⟨r, hr⟩ := h
  unfold halfSideSteps
  rw [hr]
  omega
private theorem blockOffsets_eq_blockCubeOffsets (hO : Odd L) (i : ℕ) :
    blockOffsets L i = blockCubeOffsets L i := by
  have h := two_halfSideSteps_add_one hO i
  ext p
  simp only [blockOffsets, blockCubeOffsets, mem_ofPred_eq]
  constructor
  · intro hp μ
    have := hp μ
    omega
  · intro hp μ
    have := hp μ
    omega
private theorem coe_toSublattice (hL : 0 < L) (h : j ≤ j') (y : Site L m j) :
    ((y.toSublattice j' : Site L m j') : FourTorus L m) = y := by apply _root_.YangMills.Construction.SeparatedSequences.BlockAverages.coe_toSublattice <;> assumption
private theorem coe_unitStep_eq_pow_smul (hL : 0 < L) (j : ℤ) (i : ℕ) (μ : Fin 4) :
    ((unitStep L m j μ : Site L m j) : FourTorus L m) =
      ((L : ℤ) ^ i) • ((unitStep L m (j + i) μ : Site L m (j + i)) : FourTorus L m) := by
  have hL' : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  have hs : meshSize L j = ((L : ℤ) ^ i) • meshSize L (j + i) := by
    unfold meshSize
    rw [zsmul_eq_mul, neg_add, zpow_add₀ hL', zpow_neg _ (i : ℤ), zpow_natCast]
    push_cast
    field_simp
  show pointOnAxis L m μ (meshSize L j) = ((L : ℤ) ^ i) • pointOnAxis L m μ (meshSize L (j + i))
  funext ν
  by_cases h : ν = μ
  · subst h
    simp only [pointOnAxis, Pi.smul_apply, Pi.single_eq_same]
    rw [hs, AddCircle.coe_zsmul]
  · simp [pointOnAxis, Pi.single_eq_of_ne h]
private theorem coe_offsetSite (y : Site L m j) (n : Fin 4 → ℤ) :
    ((offsetSite y n : Site L m j) : FourTorus L m) =
      (y : FourTorus L m) + ∑ μ, n μ • ((unitStep L m j μ : Site L m j) : FourTorus L m) := by
  simp [offsetSite]
private theorem offsetSite_offsetSite (w : Site L m j) (a b : Fin 4 → ℤ) :
    offsetSite (offsetSite w a) b = offsetSite w (a + b) := by
  simp only [offsetSite, Pi.add_apply, add_smul, Finset.sum_add_distrib, add_assoc]
private theorem coe_offsetSite_refine (hL : 0 < L) (y : Site L m j) (i : ℕ) (p n : Fin 4 → ℤ) :
    ((offsetSite ((offsetSite y p).toSublattice (j + i)) n :
        Site L m (j + i)) : FourTorus L m) =
      (offsetSite (y.toSublattice (j + i)) (fun μ => p μ * (L : ℤ) ^ i + n μ) :
        Site L m (j + i)) := by
  have hle : j ≤ j + i := by omega
  rw [coe_offsetSite, coe_toSublattice hL hle, coe_offsetSite, coe_offsetSite,
    coe_toSublattice hL hle]
  simp only [coe_unitStep_eq_pow_smul (m := m) hL j i, add_smul, mul_smul,
    Finset.sum_add_distrib, add_assoc]
private theorem mem_refinedBlock_iff (hO : Odd L) {i : ℕ} (hB : RefinedBlockCoordinates L m j i)
    (hj : j' = j + i) (y : Site L m j) (x : Site L m j') :
    (x : FourTorus L m) ∈ refinedBlock i y ↔
      ∃ p ∈ blockCubeOffsets L i, x = offsetSite (y.toSublattice j') p := by
  subst hj
  rw [(hB y).2.1, ← blockOffsets_eq_blockCubeOffsets hO]
  constructor
  · rintro ⟨p, hp, h⟩
    exact ⟨p, hp, Subtype.ext h.symm⟩
  · rintro ⟨p, hp, rfl⟩
    exact ⟨p, hp, rfl⟩
private theorem refinedBlock_parametrized (hO : Odd L) {i : ℕ}
    (hB : RefinedBlockCoordinates L m j i) (hj : j' = j + i) (y : Site L m j) :
    IsParametrizedBy (y.toSublattice j') (blockCubeOffsets L i) (refinedBlock i y) := by
  subst hj
  rw [← blockOffsets_eq_blockCubeOffsets hO]
  exact ⟨(hB y).2.2.1, (hB y).2.1.symm⟩
private theorem refinedBlockUnion_siteGrid (hO : Odd L) {i : ℕ}
    (hB : RefinedBlockCoordinates L m j i) (y : Site L m j) (q : Fin 4 → ℕ) :
    refinedBlockUnion i (siteGrid y q) =
      (fun t => (offsetSite (y.toSublattice (j + i)) t : FourTorus L m)) ''
        gridBlockOffsets L i q := by
  have hL : 0 < L := hO.pos
  have hh := two_halfSideSteps_add_one hO i
  have hP : 0 < (L : ℤ) ^ i := pow_pos (by exact_mod_cast hL) i
  ext x
  constructor
  · intro hx
    simp only [refinedBlockUnion, mem_iUnion, exists_prop] at hx
    obtain ⟨z, ⟨p, hp, rfl⟩, hx⟩ := hx
    rw [(hB _).2.1] at hx
    obtain ⟨n, hn, rfl⟩ := hx
    refine ⟨fun μ => p μ * (L : ℤ) ^ i + n μ, ?_, (coe_offsetSite_refine hL y i p n).symm⟩
    intro μ
    have h1 : 0 ≤ p μ * (L : ℤ) ^ i := mul_nonneg (hp μ).1 hP.le
    have h2 : p μ * (L : ℤ) ^ i ≤ (q μ : ℤ) * (L : ℤ) ^ i :=
      mul_le_mul_of_nonneg_right (hp μ).2 hP.le
    have h3 := hn μ
    have h4 := abs_le.1 (show |n μ| ≤ halfSideSteps L i by omega)
    constructor
    · show -halfSideSteps L i ≤ p μ * (L : ℤ) ^ i + n μ
      linarith [h4.1]
    · show p μ * (L : ℤ) ^ i + n μ ≤ (q μ : ℤ) * (L : ℤ) ^ i + halfSideSteps L i
      linarith [h4.2]
  · rintro ⟨t, ht, rfl⟩
    set h := halfSideSteps L i with hdef
    let p : Fin 4 → ℤ := fun μ => (t μ + h) / (L : ℤ) ^ i
    let n : Fin 4 → ℤ := fun μ => (t μ + h) % (L : ℤ) ^ i - h
    have hdecomp : ∀ μ, (L : ℤ) ^ i * p μ + ((t μ + h) % (L : ℤ) ^ i) = t μ + h :=
      fun μ => Int.mul_ediv_add_emod _ _
    have hr0 : ∀ μ, 0 ≤ (t μ + h) % (L : ℤ) ^ i := fun μ => Int.emod_nonneg _ hP.ne'
    have hr1 : ∀ μ, (t μ + h) % (L : ℤ) ^ i < (L : ℤ) ^ i := fun μ => Int.emod_lt_of_pos _ hP
    have hp0 : ∀ μ, 0 ≤ p μ := by
      intro μ
      by_contra hc
      have h1 : p μ + 1 ≤ 0 := by omega
      have h2 := mul_le_mul_of_nonneg_left h1 hP.le
      have h3 := hdecomp μ
      have h4 := hr1 μ
      have h5 := (ht μ).1
      nlinarith
    have hpq : ∀ μ, p μ ≤ (q μ : ℤ) := by
      intro μ
      by_contra hc
      have h1 : (q μ : ℤ) + 1 ≤ p μ := by omega
      have h2 := mul_le_mul_of_nonneg_left h1 hP.le
      have h3 := hdecomp μ
      have h4 := hr0 μ
      have h5 := (ht μ).2
      nlinarith
    have htpn : (fun μ => p μ * (L : ℤ) ^ i + n μ) = t := by
      funext μ
      have h3 := hdecomp μ
      show p μ * (L : ℤ) ^ i + ((t μ + h) % (L : ℤ) ^ i - h) = t μ
      linarith [mul_comm (p μ) ((L : ℤ) ^ i)]
    simp only [refinedBlockUnion, mem_iUnion, exists_prop]
    refine ⟨offsetSite y p, ⟨p, fun μ => ⟨hp0 μ, hpq μ⟩, rfl⟩, ?_⟩
    rw [(hB _).2.1]
    refine ⟨n, ?_, ?_⟩
    · intro μ
      have h4 := hr0 μ
      have h5 := hr1 μ
      have : |n μ| ≤ h := abs_le.2 ⟨by show -h ≤ _ - h; omega, by show _ - h ≤ h; omega⟩
      omega
    · have := coe_offsetSite_refine hL y i p n
      rw [htpn] at this
      exact this
private theorem offsetSite_injOn_grid (hO : Odd L) {i M : ℕ}
    (hLat : SublatticeCoordinates L m (j + i)) (hM : (m : ℤ) + j = M) (q : Fin 4 → ℕ)
    (hq : ∀ μ, (q μ : ℤ) + 1 < (L : ℤ) ^ M) (w : Site L m (j + i)) :
    InjOn (offsetSite w) (gridBlockOffsets L i q) := by
  have hL : 0 < L := hO.pos
  have hh := two_halfSideSteps_add_one hO i
  have hP : 0 < (L : ℤ) ^ i := pow_pos (by exact_mod_cast hL) i
  have hhalf : (halfPeriod L m (j + i) : ℤ) = (L : ℤ) ^ M * (L : ℤ) ^ i := by
    have : ((m : ℤ) + (j + i)).toNat = M + i := by omega
    simp [halfPeriod, this, pow_add]
  intro t ht t' ht' e
  have hc := (hLat.2.2.2.2.1 w t t').1 e
  funext μ
  have hd := Int.modEq_iff_dvd.1 (hc μ)
  have hmul : ((q μ : ℤ) + 1) * (L : ℤ) ^ i < (L : ℤ) ^ M * (L : ℤ) ^ i :=
    mul_lt_mul_of_pos_right (hq μ) hP
  have h1 := ht μ
  have h2 := ht' μ
  have hlt : |t' μ - t μ| < ((2 * halfPeriod L m (j + i) : ℕ) : ℤ) := by
    push_cast
    rw [hhalf, abs_lt]
    constructor <;> nlinarith [h1.1, h1.2, h2.1, h2.2]
  have := Int.eq_zero_of_abs_lt_dvd hd hlt
  omega
private theorem sitesFromCorner_points (hO : Odd L) (i : ℕ) (w : Site L m j') (q : Fin 4 → ℕ) :
    sitesAsTorusPoints (sitesFromCorner (offsetSite w fun _ => -halfSideSteps L i)
        fun μ => ((q μ : ℤ) + 1) * (L : ℤ) ^ i) =
      (fun t => (offsetSite w t : FourTorus L m)) '' gridBlockOffsets L i q := by
  have hh := two_halfSideSteps_add_one hO i
  ext x
  constructor
  · rintro ⟨_, ⟨t, ht, rfl⟩, rfl⟩
    refine ⟨(fun _ => -halfSideSteps L i) + t, fun μ => ?_, by simp only [offsetSite_offsetSite]⟩
    have h1 := ht μ
    simp only [Pi.add_apply]
    constructor
    · linarith [h1.1]
    · nlinarith [h1.2]
  · rintro ⟨t, ht, rfl⟩
    refine ⟨_, ⟨(fun _ => halfSideSteps L i) + t, fun μ => ?_, rfl⟩, ?_⟩
    · have h1 := ht μ
      simp only [Pi.add_apply]
      constructor
      · linarith [h1.1]
      · nlinarith [h1.2]
    · simp only [offsetSite_offsetSite]
      congr 2
      funext μ
      simp
private theorem sitesIn_sitesAsTorusPoints (P : Set (Site L m j)) :
    sitesIn (sitesAsTorusPoints P) = P := by apply _root_.YangMills.Construction.PeriodicLattice.DoubleBlockCorner.sitesIn_siteImage <;> assumption
private theorem siteGrid_facts (hO : Odd L) {i M : ℕ} (hLat : SublatticeCoordinates L m (j + i))
    (hB : RefinedBlockCoordinates L m j i) (hM : (m : ℤ) + j = M) (hj : j' = j + i)
    (y : Site L m j) (q : Fin 4 → ℕ) (hq : ∀ μ, (q μ : ℤ) + 1 < (L : ℤ) ^ M) :
    refinedBlockUnion i (siteGrid y q) =
        sitesAsTorusPoints (sitesFromCorner
          (offsetSite (y.toSublattice j') fun _ => -halfSideSteps L i)
          fun μ => ((q μ : ℤ) + 1) * (L : ℤ) ^ i) ∧
      IsParametrizedBy (y.toSublattice j') (gridBlockOffsets L i q)
        (refinedBlockUnion i (siteGrid y q)) := by
  subst hj
  rw [sitesFromCorner_points hO, refinedBlockUnion_siteGrid hO hB]
  exact ⟨rfl, offsetSite_injOn_grid hO hLat hM q hq _, rfl⟩
private def bondPathEnd (x : Site L m j) (Γ : List (Bond L m j)) : Site L m j :=
  Γ.foldl (fun _ b => b.target) x
private theorem bondPathEnd_append (x : Site L m j) (Γ₁ Γ₂ : List (Bond L m j)) :
    bondPathEnd x (Γ₁ ++ Γ₂) = bondPathEnd (bondPathEnd x Γ₁) Γ₂ := by
  simp [bondPathEnd, List.foldl_append]
private theorem target_getLast_eq_bondPathEnd (Γ : List (Bond L m j)) (x : Site L m j) :
    ∀ b ∈ Γ.getLast?, b.target = bondPathEnd x Γ := by
  induction Γ generalizing x with
  | nil => simp
  | cons a l ih =>
    cases l with
    | nil =>
      intro b hb
      simp only [List.getLast?_singleton, Option.mem_def, Option.some.injEq] at hb
      subst hb
      rfl
    | cons c l' =>
      intro b hb
      rw [List.getLast?_cons_cons] at hb
      exact ih a.target b hb
private theorem eq_bondPathEnd {Γ : List (Bond L m j)} {x z : Site L m j}
    (h : IsBondPathFromTo Γ x z) : z = bondPathEnd x Γ := by
  cases Γ with
  | nil => exact (h.2.1 rfl).symm
  | cons a l =>
    cases hl : (a :: l).getLast? with
    | none => simp at hl
    | some b =>
      have h1 : b.target = z := h.2.2.2 b hl
      rw [← h1]
      exact target_getLast_eq_bondPathEnd _ x b hl
private theorem bondPathEnd_forwardFlow (x : Site L m j) (μ : Fin 4) (n : ℕ) :
    bondPathEnd x (forwardAxisPath x μ n) = x + (n : ℤ) • unitStep L m j μ := by
  induction n generalizing x with
  | zero => simp [forwardAxisPath, bondPathEnd]
  | succ n ih =>
    show bondPathEnd (x + unitStep L m j μ) (forwardAxisPath (x + unitStep L m j μ) μ n) = _
    rw [ih]
    push_cast
    rw [add_smul, one_smul]
    abel
private theorem isBondPath_forwardFlow (x : Site L m j) (μ : Fin 4) (n : ℕ) :
    IsBondPath (forwardAxisPath x μ n) := by
  induction n generalizing x with
  | zero => simp [IsBondPath, forwardAxisPath]
  | succ n ih =>
    cases n with
    | zero => simp [IsBondPath, forwardAxisPath]
    | succ n =>
      have h := ih (x + unitStep L m j μ)
      simp only [IsBondPath, forwardAxisPath, List.isChain_cons_cons] at h ⊢
      exact ⟨rfl, h⟩
private theorem isBondPathFromTo_forwardFlow (x : Site L m j) (μ : Fin 4) (n : ℕ) :
    IsBondPathFromTo (forwardAxisPath x μ n) x (x + (n : ℤ) • unitStep L m j μ) := by
  refine ⟨isBondPath_forwardFlow x μ n, ?_, ?_, ?_⟩
  · intro h
    cases n with
    | zero => simp
    | succ n => simp [forwardAxisPath] at h
  · intro b hb
    cases n with
    | zero => simp [forwardAxisPath] at hb
    | succ n =>
      simp only [forwardAxisPath, List.head?_cons, Option.mem_def, Option.some.injEq] at hb
      subst hb
      rfl
  · intro b hb
    rw [target_getLast_eq_bondPathEnd _ x b hb, bondPathEnd_forwardFlow]
abbrev _root_.YangMills.SharedProofs.p2140 := @isBondPathFromTo_forwardFlow
private theorem length_forwardFlow (x : Site L m j) (μ : Fin 4) (n : ℕ) :
    (forwardAxisPath x μ n).length = n := by apply _root_.YangMills.SharedProofs.p1058 <;> assumption
private theorem target_sub_source_forwardFlow (x : Site L m j) (μ : Fin 4) (n : ℕ) :
    ∀ b ∈ forwardAxisPath x μ n, b.target - b.source = unitStep L m j μ := by apply _root_.YangMills.Construction.PeriodicLattice.BlockPaths.target_sub_source_of_mem_forwardFlow <;> assumption
private theorem sitesOfPath_forwardFlow (x : Site L m j) (μ : Fin 4) (n : ℕ) :
    ∀ z ∈ sitesOfPath x (forwardAxisPath x μ n),
      ∃ t : ℕ, t ≤ n ∧ z = x + (t : ℤ) • unitStep L m j μ := by
  induction n generalizing x with
  | zero =>
    intro z hz
    simp only [sitesOfPath, forwardAxisPath, List.map_nil, List.mem_singleton] at hz
    exact ⟨0, le_rfl, by simp [hz]⟩
  | succ n ih =>
    intro z hz
    simp only [sitesOfPath, forwardAxisPath, List.map_cons, List.mem_cons] at hz
    rcases hz with rfl | hz
    · exact ⟨0, by omega, by simp⟩
    · obtain ⟨t, ht, rfl⟩ := ih (x + unitStep L m j μ) z (by
        simp only [sitesOfPath, List.mem_cons]
        exact hz)
      refine ⟨t + 1, by omega, ?_⟩
      push_cast
      rw [add_smul, one_smul]
      abel
private theorem offsetSite_single (x : Site L m j) (ν : Fin 4) (n : ℤ) :
    offsetSite x (Pi.single ν n) = x + n • unitStep L m j ν := by apply _root_.YangMills.Construction.PeriodicLattice.DoubleBlockCorner.offsetSite_single <;> assumption
private theorem halfPeriod_eq_pow {M : ℕ} (hM : (m : ℤ) + j = M) :
    (halfPeriod L m j : ℤ) = (L : ℤ) ^ M := by
  simp [halfPeriod, hM]
private theorem axialPath_eq_forwardFlow (hLat : SublatticeCoordinates L m j) {M : ℕ}
    (hM : (m : ℤ) + j = M) (x : Site L m j) (μ : Fin 4) (a : ℕ) (ha0 : 0 < a)
    (ha : (a : ℤ) < (L : ℤ) ^ M) :
    axialPath x (x + (a : ℤ) • unitStep L m j μ) = forwardAxisPath x μ a := by
  have hhalf := halfPeriod_eq_pow (L := L) hM
  have hdisp : IsAxialDisplacement x (x + (a : ℤ) • unitStep L m j μ) μ (a : ℤ) := by
    refine ⟨by simp, ?_⟩
    rw [hM, zpow_natCast, abs_of_nonneg (by omega)]
    exact_mod_cast ha
  have hex : ∃ q : Fin 4 × ℤ, IsAxialDisplacement x (x + (a : ℤ) • unitStep L m j μ) q.1 q.2 :=
    ⟨(μ, (a : ℤ)), hdisp⟩
  unfold axialPath
  rw [dif_pos hex]
  obtain ⟨h1, h2⟩ := hex.choose_spec
  have key : hex.choose.1 = μ ∧ hex.choose.2 = (a : ℤ) := by
    generalize hex.choose = r at h1 h2
    obtain ⟨ν, n⟩ := r
    simp only at h1 h2 ⊢
    have he : offsetSite x (Pi.single ν n) = offsetSite x (Pi.single μ (a : ℤ)) := by
      rw [offsetSite_single, offsetSite_single, ← h1]
      abel
    have hc := (hLat.2.2.2.2.1 x _ _).1 he μ
    have hn : |n| < (L : ℤ) ^ M := by
      rw [hM, zpow_natCast] at h2
      exact_mod_cast h2
    have hd := Int.modEq_iff_dvd.1 hc
    have hcast : ((2 * halfPeriod L m j : ℕ) : ℤ) = 2 * (L : ℤ) ^ M := by
      push_cast
      rw [hhalf]
    rw [hcast] at hd
    by_cases hνμ : ν = μ
    · subst hνμ
      simp only [Pi.single_eq_same] at hd
      have hlt : |(a : ℤ) - n| < 2 * (L : ℤ) ^ M := by
        have := abs_lt.1 hn
        rw [abs_lt]
        constructor <;> linarith [this.1, this.2]
      have := Int.eq_zero_of_abs_lt_dvd hd hlt
      exact ⟨rfl, by omega⟩
    · exfalso
      simp only [Pi.single_eq_same, Pi.single_eq_of_ne (Ne.symm hνμ)] at hd
      have hlt : |(a : ℤ) - 0| < 2 * (L : ℤ) ^ M := by
        rw [sub_zero, abs_of_nonneg (by omega)]
        omega
      have := Int.eq_zero_of_abs_lt_dvd hd hlt
      omega
  rw [key.1, key.2]
  unfold flowAlong
  rw [if_pos (by omega)]
  simp
private theorem shiftByBlock_across_bond (hO : Odd L) {i M : ℕ}
    (hB : RefinedBlockCoordinates L m j i)
    (hLat : SublatticeCoordinates L m j') (hj : j' = j + i) (hM : (m : ℤ) + j' = M)
    (hi : (L : ℤ) ^ i < (L : ℤ) ^ M) (b : Bond L m j) (μ : Fin 4)
    (hb : b.target - b.source = unitStep L m j μ) :
    BijOn (shiftByBlock i μ) (sitesIn (refinedBlock i b.source) : Set (Site L m j'))
      (sitesIn (refinedBlock i b.target)) ∧
    ∀ x ∈ (sitesIn (refinedBlock i b.source) : Set (Site L m j')),
      IsAxialDisplacement x (shiftByBlock i μ x) μ ((L : ℤ) ^ i) ∧
      IsBondPathFromTo (axialPath x (shiftByBlock i μ x)) x (shiftByBlock i μ x) ∧
      (axialPath x (shiftByBlock i μ x)).length = L ^ i ∧
      (∀ b' ∈ axialPath x (shiftByBlock i μ x), b'.IsPositivelyOriented) ∧
      ∀ z ∈ sitesOfPath x (axialPath x (shiftByBlock i μ x)),
        (z : FourTorus L m) ∈ refinedBlock i b.source ∪ refinedBlock i b.target := by
  subst hj
  have hL : 0 < L := hO.pos
  have hh := two_halfSideSteps_add_one hO i
  have hle : j ≤ j + i := by omega
  have hmem : ∀ (y : Site L m j) (x : Site L m (j + i)),
      x ∈ (sitesIn (refinedBlock i y) : Set (Site L m (j + i))) ↔
        ∃ p ∈ blockCubeOffsets L i, x = offsetSite (y.toSublattice (j + i)) p :=
    fun y x => mem_refinedBlock_iff hO hB rfl y x
  set T := b.source.toSublattice (j + i) with hT
  set H := b.target.toSublattice (j + i) with hH
  have hHT : H = T + ((L : ℤ) ^ i) • unitStep L m (j + i) μ := by
    apply Subtype.ext
    have h1 : b.target = b.source + unitStep L m j μ := by rw [← hb]; abel
    have h2 : ((b.target : Site L m j) : FourTorus L m) =
        (b.source : FourTorus L m) + ((unitStep L m j μ : Site L m j) : FourTorus L m) := by
      rw [h1]; rfl
    simp only [hH, hT, AddSubgroup.coe_add, AddSubgroup.coe_zsmul, coe_toSublattice hL hle]
    rw [h2, coe_unitStep_eq_pow_smul hL j i μ]
  have hacross : ∀ p : Fin 4 → ℤ,
      shiftByBlock i μ (offsetSite T p) = offsetSite H p := by
    intro p
    simp only [shiftByBlock, offsetSite, hHT]
    abel
  have hsa : ∀ x : Site L m (j + i),
      shiftByBlock i μ x = x + ((L ^ i : ℕ) : ℤ) • unitStep L m (j + i) μ := by
    intro x
    simp [shiftByBlock]
  have hLi : (((L ^ i : ℕ) : ℤ)) < (L : ℤ) ^ M := by
    push_cast
    exact hi
  have hpos : 0 < L ^ i := pow_pos hL i
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · intro x hx
    obtain ⟨p, hp, rfl⟩ := (hmem _ _).1 hx
    exact (hmem _ _).2 ⟨p, hp, hacross p⟩
  · intro x _ x' _ h
    simp only [shiftByBlock] at h
    exact add_right_cancel h
  · intro z hz
    obtain ⟨p, hp, rfl⟩ := (hmem _ _).1 hz
    exact ⟨offsetSite T p, (hmem _ _).2 ⟨p, hp, rfl⟩, hacross p⟩
  · intro x hx
    obtain ⟨p, hp, rfl⟩ := (hmem _ _).1 hx
    have hsp := axialPath_eq_forwardFlow hLat hM (offsetSite T p) μ (L ^ i) hpos hLi
    rw [← hsa] at hsp
    rw [hsp]
    refine ⟨⟨by simp [shiftByBlock], ?_⟩, ?_, length_forwardFlow _ _ _, ?_, ?_⟩
    · rw [hM, zpow_natCast, abs_of_nonneg (by positivity)]
      exact_mod_cast hi
    · rw [hsa]
      exact isBondPathFromTo_forwardFlow _ _ _
    · intro b' hb'
      exact ⟨μ, target_sub_source_forwardFlow _ _ _ b' hb'⟩
    · intro z hz
      obtain ⟨t, ht, rfl⟩ := sitesOfPath_forwardFlow _ _ _ z hz
      have htL : (t : ℤ) ≤ (L : ℤ) ^ i := by exact_mod_cast ht
      have hpμ := abs_le.1 (hp μ)
      have hq : ∀ (s : ℤ), -halfSideSteps L i ≤ p μ + s → p μ + s ≤ halfSideSteps L i →
          p + Pi.single μ s ∈ blockCubeOffsets L i := by
        intro s h1 h2 ρ
        by_cases hρ : ρ = μ
        · subst hρ
          simp only [Pi.add_apply, Pi.single_eq_same]
          exact abs_le.2 ⟨h1, h2⟩
        · simp only [Pi.add_apply, Pi.single_eq_of_ne hρ, add_zero]
          exact hp ρ
      by_cases hc : p μ + (t : ℤ) ≤ halfSideSteps L i
      · left
        refine (hmem _ _).2 ⟨p + Pi.single μ (t : ℤ), hq _ (by omega) hc, ?_⟩
        rw [← offsetSite_offsetSite, offsetSite_single]
      · right
        refine (hmem _ _).2
          ⟨p + Pi.single μ ((t : ℤ) - (L : ℤ) ^ i), hq _ (by omega) (by omega), ?_⟩
        rw [← offsetSite_offsetSite, offsetSite_single, ← hH, ← hacross p, shiftByBlock, sub_smul]
        abel
private theorem refinedBlock_add_eq_iUnion {a b : ℕ}
    (hPart : ∀ y : Site L m j, RefinedBlockOfSumOrder L m j a b y)
    (hj : j' = j + a) (y : Site L m j) :
    refinedBlock (a + b) y =
      ⋃ x : Site L m j', ⋃ _ : (x : FourTorus L m) ∈ refinedBlock a y, refinedBlock b x := by
  subst hj
  exact hPart y
private theorem blockUnionsOverSites_holds (hPart : BlockPartition.Properties)
    (hLat : CoordinateDescription) {K : ℕ}
    (hO : Odd L) (h13 : 13 ≤ L) (hm : 0 < m) {k : ℕ} (hk : k ≤ K) :
    BlockUnionsOverSites L m K k := by
  intro Z
  have hpart := hPart L m ⟨hO, h13⟩ hm
  have hjk : -(m : ℤ) ≤ levelDepth K k := by
    simp only [levelDepth]
    omega
  have h0 : ∀ y : SiteAtLevel L m K k, refinedBlock 0 y = {(y : FourTorus L m)} :=
    fun y => ((hLat L m hO h13 hm).2.2.1 _ 0 hjk y).2.2.2.2
  have hstep : ∀ n : ℕ, n < k → blockUnionAtLevel n Z =
      ⋃ z ∈ (sitesIn (blockUnionAtLevel (n + 1) Z) : Set (SiteAtLevel L m K (n + 1))),
        unitBlock z := by
    intro n hn
    have hsplit : ∀ y : SiteAtLevel L m K k, refinedBlock (k - n) y =
        ⋃ x : SiteAtLevel L m K (n + 1),
          ⋃ _ : (x : FourTorus L m) ∈ refinedBlock (k - (n + 1)) y, refinedBlock 1 x := by
      intro y
      have e : k - n = (k - (n + 1)) + 1 := by omega
      rw [e]
      exact refinedBlock_add_eq_iUnion
        (fun y => (hpart (levelDepth K k) (k - (n + 1)) 1 hjk).2.2.1 y)
        (by simp only [levelDepth]; omega) y
    ext x
    simp only [blockUnionAtLevel, refinedBlockUnion, mem_iUnion, exists_prop, hsplit]
    constructor
    · rintro ⟨y, hy, z, hz, hx⟩
      refine ⟨z, ?_, hx⟩
      simp only [sitesIn, mem_iUnion, exists_prop]
      exact ⟨y, hy, hz⟩
    · rintro ⟨z, hz, hx⟩
      simp only [sitesIn, mem_iUnion, exists_prop] at hz
      obtain ⟨y, hy, hz⟩ := hz
      exact ⟨y, hy, z, hz, hx⟩
  refine ⟨?_, hstep, ?_, ?_⟩
  · ext x
    simp only [blockUnionAtLevel, refinedBlockUnion, Nat.sub_self, mem_iUnion, exists_prop,
      sitesAsTorusPoints, mem_image, h0, mem_singleton_iff]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y, hy, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y, hy, rfl⟩
  · intro n hn c ht hh
    rw [hstep n hn]
    unfold bondDoubleBlock
    apply union_subset
    · intro x hx
      simp only [mem_iUnion, exists_prop]
      exact ⟨c.source, ht, hx⟩
    · intro x hx
      simp only [mem_iUnion, exists_prop]
      exact ⟨c.target, hh, hx⟩
  · intro n hn x hx w hw
    simp only [blockUnionAtLevel, refinedBlockUnion, mem_iUnion, exists_prop, Nat.sub_zero]
      at hx ⊢
    obtain ⟨y, hy, hxy⟩ := hx
    refine ⟨y, hy, ?_⟩
    have hs := refinedBlock_add_eq_iUnion (a := k - n) (b := n) (j' := levelDepth K n)
      (fun y => (hpart (levelDepth K k) (k - n) n hjk).2.2.1 y)
      (by simp only [levelDepth]; omega) y
    rw [Nat.sub_add_cancel hn] at hs
    rw [hs]
    simp only [mem_iUnion, exists_prop]
    exact ⟨x, hxy, hw⟩
private theorem flowAlong_of_nonneg (x : Site L m j) (μ : Fin 4) {a : ℤ} (ha : 0 ≤ a) :
    flowAlong x μ a = forwardAxisPath x μ a.toNat := if_pos ha
private theorem stepsThroughAxes_congr (l : List (Fin 4)) (n n' : Fin 4 → ℤ) (x : Site L m j)
    (h : ∀ ν ∈ l, n ν = n' ν) : stepsThroughAxes n x l = stepsThroughAxes n' x l := by
  induction l generalizing x with
  | nil => rfl
  | cons μ l ih =>
    simp only [stepsThroughAxes]
    rw [h μ (by simp), ih _ (fun ν hν => h ν (by simp [hν]))]
private theorem stepsThroughAxes_of_zero (l : List (Fin 4)) (n : Fin 4 → ℤ) (x : Site L m j)
    (h : ∀ ν ∈ l, n ν = 0) : stepsThroughAxes n x l = [] := by
  induction l generalizing x with
  | nil => rfl
  | cons μ l ih =>
    simp only [stepsThroughAxes]
    rw [h μ (by simp), ih _ (fun ν hν => h ν (by simp [hν]))]
    simp [flowAlong, forwardAxisPath]
private theorem forwardFlow_prefix (x : Site L m j) (μ : Fin 4) (a : ℕ)
    (Γ₁ Γ₂ : List (Bond L m j)) (h : forwardAxisPath x μ a = Γ₁ ++ Γ₂) :
    ∃ b, b ≤ a ∧ Γ₁ = forwardAxisPath x μ b := by
  induction a generalizing x Γ₁ with
  | zero =>
    simp only [forwardAxisPath] at h
    exact ⟨0, le_rfl, by simpa [forwardAxisPath] using (List.append_eq_nil_iff.1 h.symm).1⟩
  | succ a ih =>
    cases Γ₁ with
    | nil => exact ⟨0, by omega, rfl⟩
    | cons g Γ' =>
      simp only [forwardAxisPath, List.cons_append, List.cons.injEq] at h
      obtain ⟨b, hb, rfl⟩ := ih _ Γ' h.2
      exact ⟨b + 1, by omega, by simp [forwardAxisPath, h.1]⟩
private theorem stepsThroughAxes_prefix (l : List (Fin 4)) (hl : l.Nodup) (n : Fin 4 → ℤ)
    (hn : ∀ μ, 0 ≤ n μ) (x : Site L m j) (Γ₁ Γ₂ : List (Bond L m j))
    (h : stepsThroughAxes n x l = Γ₁ ++ Γ₂) :
    ∃ n' : Fin 4 → ℤ, (∀ μ, 0 ≤ n' μ ∧ n' μ ≤ n μ) ∧ (∀ μ, μ ∉ l → n' μ = 0) ∧
      Γ₁ = stepsThroughAxes n' x l := by
  induction l generalizing x Γ₁ with
  | nil =>
    simp only [stepsThroughAxes] at h
    refine ⟨0, fun μ => ⟨le_rfl, hn μ⟩, fun _ _ => rfl, ?_⟩
    simpa [stepsThroughAxes] using (List.append_eq_nil_iff.1 h.symm).1
  | cons μ l ih =>
    obtain ⟨hμl, hnd⟩ := List.nodup_cons.1 hl
    simp only [stepsThroughAxes] at h
    rw [flowAlong_of_nonneg x μ (hn μ)] at h
    rcases List.append_eq_append_iff.1 h with ⟨R₁, hΓ, hR⟩ | ⟨c, hc, _⟩
    · obtain ⟨n'', h1, h2, h3⟩ := ih hnd _ R₁ hR
      refine ⟨Function.update n'' μ (n μ), fun ν => ?_, fun ν hν => ?_, ?_⟩
      · by_cases hν : ν = μ
        · subst hν
          simp [hn ν]
        · simp only [Function.update_of_ne hν]
          exact h1 ν
      · have hνμ : ν ≠ μ := fun e => hν (by simp [e])
        simp only [Function.update_of_ne hνμ]
        exact h2 ν (fun e => hν (by simp [e]))
      · simp only [stepsThroughAxes, Function.update_self]
        rw [flowAlong_of_nonneg x μ (hn μ), hΓ, h3]
        congr 1
        apply stepsThroughAxes_congr
        intro ν hν
        have hνμ : ν ≠ μ := fun e => hμl (e ▸ hν)
        simp only [Function.update_of_ne hνμ]
    · obtain ⟨b, hb, rfl⟩ := forwardFlow_prefix x μ _ Γ₁ c hc
      refine ⟨Pi.single μ (b : ℤ), fun ν => ?_, fun ν hν => ?_, ?_⟩
      · by_cases hν : ν = μ
        · subst hν
          simp only [Pi.single_eq_same]
          have := hn ν
          omega
        · simp only [Pi.single_eq_of_ne hν]
          exact ⟨le_rfl, hn ν⟩
      · have hνμ : ν ≠ μ := fun e => hν (by simp [e])
        simp only [Pi.single_eq_of_ne hνμ]
      · simp only [stepsThroughAxes, Pi.single_eq_same]
        rw [flowAlong_of_nonneg x μ (by omega), stepsThroughAxes_of_zero l _ _ (fun ν hν => ?_)]
        · simp
        · have hνμ : ν ≠ μ := fun e => hμl (e ▸ hν)
          simp only [Pi.single_eq_of_ne hνμ]
private theorem bondPathEnd_stepsThroughAxes (l : List (Fin 4)) (n : Fin 4 → ℤ)
    (hn : ∀ μ, 0 ≤ n μ) (x : Site L m j) :
    bondPathEnd x (stepsThroughAxes n x l) = x + (l.map fun μ => n μ • unitStep L m j μ).sum := by
  induction l generalizing x with
  | nil => simp [stepsThroughAxes, bondPathEnd]
  | cons μ l ih =>
    simp only [stepsThroughAxes, bondPathEnd_append]
    rw [flowAlong_of_nonneg x μ (hn μ), bondPathEnd_forwardFlow, Int.toNat_of_nonneg (hn μ), ih]
    simp [add_assoc]
private theorem meshSize_pos (hL : 0 < L) (j : ℤ) : 0 < meshSize L j := by apply _root_.YangMills.SharedProofs.p6250 <;> assumption
private theorem chartOffset_eq (hL : 0 < L) (hLat : SublatticeCoordinates L m j)
    {y x : Site L m j} {d : Fin 4 → ℤ} (h : IsChartOffset y x d) :
    chartOffset y x = d := by
  have h' : IsChartOffset y x (chartOffset y x) :=
    Classical.epsilon_spec (p := IsChartOffset y x) ⟨d, h⟩
  have hsp := meshSize_pos hL j
  have hbound : ∀ e : Fin 4 → ℤ, IsChartOffset y x e → ∀ μ,
      |e μ| < (halfPeriod L m j : ℤ) := by
    intro e he μ
    have h1 := he.2 μ
    have h2 : torusSide L m = (2 * (halfPeriod L m j : ℝ)) * meshSize L j := by
      have := hLat.1
      rw [div_eq_iff hsp.ne'] at this
      rw [this]
      push_cast
      ring
    rw [h2] at h1
    have h3 : ((|e μ| : ℤ) : ℝ) < (halfPeriod L m j : ℝ) := by
      have : ((|e μ| : ℤ) : ℝ) * meshSize L j < (halfPeriod L m j : ℝ) * meshSize L j := by
        linarith
      exact lt_of_mul_lt_mul_right this hsp.le
    exact_mod_cast h3
  have heq : offsetSite y d = offsetSite y (chartOffset y x) := by
    simp only [offsetSite, ← h.1, ← h'.1]
  have hc := (hLat.2.2.2.2.1 y _ _).1 heq
  funext μ
  have hd := Int.modEq_iff_dvd.1 (hc μ)
  have h1 := abs_lt.1 (hbound _ h' μ)
  have h2 := abs_lt.1 (hbound _ h μ)
  have hlt : |chartOffset y x μ - d μ| < ((2 * halfPeriod L m j : ℕ) : ℤ) := by
    push_cast
    rw [abs_lt]
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  have := Int.eq_zero_of_abs_lt_dvd hd hlt
  omega
private theorem coordinateComb_prefix (hL : 0 < L) (hLat : SublatticeCoordinates L m j)
    {o x z : Site L m j} {d : Fin 4 → ℤ} (hd : IsChartOffset o x d) (hnn : ∀ ν, 0 ≤ d ν)
    (Γ₁ Γ₂ : List (Bond L m j)) (h : coordinateComb o x = Γ₁ ++ Γ₂)
    (hp : IsBondPathFromTo Γ₁ o z) :
    coordinateComb o z = Γ₁ := by
  unfold coordinateComb at h
  rw [chartOffset_eq hL hLat hd] at h
  obtain ⟨n', hn', _, rfl⟩ := stepsThroughAxes_prefix [3, 2, 1, 0] (by decide) d hnn o Γ₁ Γ₂ h
  have hz := eq_bondPathEnd hp
  rw [bondPathEnd_stepsThroughAxes _ _ (fun μ => (hn' μ).1)] at hz
  have hsp := meshSize_pos hL j
  have hcd : IsChartOffset o z n' := by
    refine ⟨?_, fun μ => ?_⟩
    · rw [hz]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Fin.sum_univ_four]
      abel
    · have h1 := hd.2 μ
      have h2 : |n' μ| ≤ |d μ| := by
        rw [abs_of_nonneg (hn' μ).1, abs_of_nonneg (hnn μ)]
        exact (hn' μ).2
      have h3 : ((|n' μ| : ℤ) : ℝ) ≤ ((|d μ| : ℤ) : ℝ) := by exact_mod_cast h2
      have h4 := mul_le_mul_of_nonneg_right h3 hsp.le
      linarith
  unfold coordinateComb
  rw [chartOffset_eq hL hLat hcd]
open Classical in
private theorem length_le_sum_countP (Γ : List (Bond L m j)) (P : Fin 4 → Bond L m j → Prop)
    (h : ∀ b ∈ Γ, ∃ ν, P ν b) : Γ.length ≤ ∑ ν, Γ.countP fun b => decide (P ν b) := by
  induction Γ with
  | nil => simp
  | cons a l ih =>
    have h1 := ih (fun b hb => h b (by simp [hb]))
    obtain ⟨ν, hν⟩ := h a (by simp)
    simp only [List.countP_cons, Finset.sum_add_distrib, List.length_cons]
    have h2 : 1 ≤ ∑ x : Fin 4, (if decide (P x a) = true then 1 else 0) := by
      refine le_trans ?_ (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ ν))
      simp [hν]
    omega
open Classical in
private theorem contour_length_le (hO : Odd L) {y : Site L m j} {x : Site L m j'}
    {p : Fin 4 → ℤ} (hC : ContourCoordinates y x p) :
    ∀ Γ ∈ contourSet y x, Γ.length ≤ 2 * (L - 1) := by
  intro Γ hΓ
  obtain ⟨_, hcnt, hb, _, _⟩ := hC Γ hΓ
  have hO' := hO
  obtain ⟨r, hr⟩ := hO'
  have hhalf : centreToFaceSteps L = (r : ℤ) := by
    unfold centreToFaceSteps
    omega
  let P : Fin 4 → Bond L m j' → Prop :=
    fun ν b => p ν ≠ 0 ∧ b.target - b.source = (p ν).sign • unitStep L m j' ν
  have h1 := length_le_sum_countP Γ P (fun b hb' => by
    obtain ⟨ν, h1, h2⟩ := hb b hb'
    exact ⟨ν, h1, h2⟩)
  have h2 : ∀ ν, (Γ.countP fun b => @decide (P ν b) (Classical.propDecidable _)) ≤ r := by
    intro ν
    by_cases h0 : p ν = 0
    · have : (Γ.countP fun b => @decide (P ν b) (Classical.propDecidable _)) = 0 := by
        rw [List.countP_eq_zero]
        intro b _
        simp [P, h0]
      omega
    · have h3 := hcnt ν h0
      have h4 : (Γ.countP fun b => @decide (P ν b) (Classical.propDecidable _)) ≤
          countSteps Γ ((p ν).sign • unitStep L m j' ν) := by
        unfold countSteps
        apply List.countP_mono_left
        intro b _ hb'
        simp only [P, decide_eq_true_eq] at hb' ⊢
        exact hb'.2
      have h5 := h3.2
      rw [hhalf] at h5
      have h6 := h3.1
      have h7 : |p ν| = ((p ν).natAbs : ℤ) := Int.abs_eq_natAbs _
      omega
  simp only [Fin.sum_univ_four] at h1
  have := h2 0
  have := h2 1
  have := h2 2
  have := h2 3
  omega
private theorem stepSetsAreBoxes_holds (hBox : CornerBoxProperties) {K n : ℕ}
    (hO : Odd L) (h13 : 13 ≤ L) (hm : 0 < m) (hK : 0 < K) (hn : n < K) :
    StepSetsAreBoxes L m K n := by
  have hb := hBox L m K ⟨hO, h13⟩ hm hK n hn.le
  have hcorner := hb.2 (n + 1) (by omega) (by omega)
  have key : ∀ (P : Set (FourTorus L m)) (z : SiteAtLevel L m K n) (C : Fin 4 → ℤ),
      P = sitesAsTorusPoints (sitesFromCorner z C) →
      CountsBoundedByDoubleBlock L m K n (n + 1) C →
      (∀ μ, C μ = (L : ℤ) ∨ C μ = 2 * (L : ℤ)) →
      IsBoxOfBlockWidth (levelDepth K n) (sitesIn P) := by
    intro P z C hP hC hLL
    have hs : (sitesIn P : Set (SiteAtLevel L m K n)) = sitesFromCorner z C := by
      rw [hP, sitesIn_sitesAsTorusPoints]
    have hbound : ∀ μ, 1 ≤ C μ ∧ C μ < (L : ℤ) ^ (m + K - n) := by
      intro μ
      have h1 := hC.1 μ
      have h2 := hC.2
      refine ⟨?_, by omega⟩
      rcases hLL μ with h | h <;> omega
    have := hb.1 z C hbound
    rw [hs]
    exact ⟨this.1, C, this.2, hLL⟩
  unfold BlocksAreCornerBoxes at hcorner
  simp only [Nat.add_sub_cancel_left, pow_one] at hcorner
  refine ⟨fun y => ?_, fun c => ?_, fun p => ?_⟩
  · obtain ⟨e, hC⟩ := (hcorner y).1
    exact key _ _ _ e hC
      (fun _ => Or.inl rfl)
  · have hdb : ∀ μ ν, doubledCounts (L : ℤ) μ ν = (L : ℤ) ∨
        doubledCounts (L : ℤ) μ ν = 2 * (L : ℤ) := by
      intro μ ν
      by_cases h : ν = μ
      · subst h
        simp [doubledCounts]
      · simp [doubledCounts, uniformCounts, Function.update_of_ne h]
    obtain ⟨μ, h | h⟩ := c.isNeighbour
    · have hh : c.target = c.source + unitStep L m (levelDepth K (n + 1)) μ := by
        rw [← h]; abel
      obtain ⟨e, hC⟩ := (hcorner c.source).2.1 μ
      refine key _ (blockCorner (j' := levelDepth K n) (L : ℤ) c.source) _ ?_ hC (hdb μ)
      unfold bondDoubleBlock
      rw [hh]
      exact e
    · have hh : c.source = c.target + unitStep L m (levelDepth K (n + 1)) μ := by
        have : c.target - c.source + unitStep L m (levelDepth K (n + 1)) μ = 0 := by
          rw [h]; abel
        have h2 : c.target + unitStep L m (levelDepth K (n + 1)) μ - c.source = 0 := by
          rw [← this]; abel
        exact (sub_eq_zero.1 h2).symm
      obtain ⟨e, hC⟩ := (hcorner c.target).2.1 μ
      refine key _ (blockCorner (j' := levelDepth K n) (L : ℤ) c.target) _ ?_ hC (hdb μ)
      unfold bondDoubleBlock
      rw [union_comm, hh]
      exact e
  · obtain ⟨e, hC⟩ := (hcorner p.origin).2.2 p rfl
    refine key _ _ _ e hC ?_
    intro ν
    by_cases h1 : ν = p.secondAxis
    · subst h1
      simp [plaquetteCounts]
    · by_cases h2 : ν = p.firstAxis
      · subst h2
        simp [plaquetteCounts, doubledCounts, Function.update_of_ne h1]
      · simp [plaquetteCounts, doubledCounts, uniformCounts, Function.update_of_ne h1,
          Function.update_of_ne h2]
private theorem doubleBlockCrossings_holds (hPaths : BlockPaths.Statement) {K n : ℕ}
    (hO : Odd L) (h13 : 13 ≤ L) (hm : 0 < m) (hn : n < K) :
    DoubleBlockCrossings L m K n := by
  have hP := hPaths L m K hO h13 hm n hn
  rintro c ⟨μ, hμ⟩
  obtain ⟨hD, _, _, hS, hPb⟩ := hP.2 c μ hμ
  obtain ⟨_, _, _, himg, htr, _⟩ := hD
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · intro x hx
    show shiftAcross c x ∈ _
    rw [htr x hx, ← himg]
    exact ⟨x, hx, rfl⟩
  · intro x hx x' hx' h
    rw [htr x hx, htr x' hx'] at h
    exact add_right_cancel h
  · intro z hz
    rw [← himg] at hz
    obtain ⟨x, hx, rfl⟩ := hz
    exact ⟨x, hx, htr x hx⟩
  · intro x hx
    have hc := (hS.1 x hx).2.1
    refine ⟨?_, ?_, fun b hb => ?_⟩
    · rw [hc, htr x hx]
      exact isBondPathFromTo_forwardFlow x μ L
    · rw [hc]
      exact length_forwardFlow x μ L
    · rw [hc] at hb
      refine ⟨⟨μ, target_sub_source_forwardFlow x μ L b hb⟩, hPb.2 x hx b ?_⟩
      rw [hc]
      exact hb
private theorem contoursCombs_holds (hLat : CoordinateDescription)
    (hPaths : BlockPaths.Statement) {K n : ℕ}
    (hO : Odd L) (h13 : 13 ≤ L) (hm : 0 < m) (hn : n < K) :
    BlockContoursCombsAndBaseSites L m K n := by
  have hP := hPaths L m K hO h13 hm n hn
  have hL : 0 < L := hO.pos
  have hLn : SublatticeCoordinates L m (levelDepth K n) :=
    (hLat L m hO h13 hm).1 _ (by simp only [levelDepth]; omega)
  have hin : ∀ (y : SiteAtLevel L m K (n + 1)) (x : SiteAtLevel L m K n),
      x ∈ sitesInBlock (levelDepth K n) y →
        ∃ p ∈ blockIndexBox L, x = offsetSite (y.toSublattice (levelDepth K n)) p := by
    intro y x hx
    have himg := (hP.1 y).1.1.2
    have hx' : (x : FourTorus L m) ∈ unitBlock y := hx
    rw [← himg] at hx'
    obtain ⟨p, hp, h⟩ := hx'
    exact ⟨p, hp, Subtype.ext h.symm⟩
  have hhalf0 : 0 ≤ centreToFaceSteps L := by
    have hO' := hO
    obtain ⟨r, hr⟩ := hO'
    unfold centreToFaceSteps
    omega
  refine ⟨?_, ?_⟩
  · intro y x hx
    obtain ⟨p, hp, rfl⟩ := hin y x hx
    obtain ⟨hblk, _, hcc⟩ := hP.1 y
    obtain ⟨hCon, hCmb⟩ := hcc p hp
    obtain ⟨_, hdisp, _, hcnt, hpos, hsites, _⟩ := hCmb
    refine ⟨fun Γ hΓ => ⟨contour_length_le hO hCon Γ hΓ, ?_⟩, hblk.2.2, ?_, ?_, ?_, ?_⟩
    · intro z hz
      exact (hCon Γ hΓ).2.2.2.1 z hz
    · exact hpos
    · intro ν
      have h1 := (hcnt ν).1
      have h2 := (hcnt ν).2
      rw [h1]
      have : L ≠ 0 := hL.ne'
      omega
    · exact hsites
    · intro Γ₁ Γ₂ z h hp'
      exact coordinateComb_prefix hL hLn hdisp (fun ν => by have := (hp ν).1; omega) Γ₁ Γ₂ h hp'
  · rintro c s ⟨μ, hμ⟩
    obtain ⟨_, _, _, hS, _⟩ := hP.2 c μ hμ
    cases s with
    | centred =>
      refine ⟨?_, hS.2.1⟩
      have himg := (hP.1 c.source).1.1.2
      show ((c.source.toSublattice (levelDepth K n) : SiteAtLevel L m K n) : FourTorus L m) ∈
        unitBlock c.source
      rw [← himg]
      refine ⟨0, fun ν => ?_, ?_⟩
      · simpa using hhalf0
      · simp [offsetSite]
    | cornered => exact ⟨(hP.1 c.source).1.2.2, hS.2.2⟩
private theorem siteGrid_box (hLat : CoordinateDescription)
    (hBox : CornerBoxProperties) {K n k i : ℕ} (hO : Odd L) (h13 : 13 ≤ L)
    (hm : 0 < m) (hK : 0 < K) (hk : k ≤ K) (hnk : n + i = k) (y : SiteAtLevel L m K k)
    (q : Fin 4 → ℕ) (hq : ∀ μ, q μ + 1 < L ^ (m + K - k)) :
    IsSiteBox (levelDepth K n) (sitesIn (refinedBlockUnion i (siteGrid y q))) ∧
    IsParametrizedBy (y.toSublattice (levelDepth K n)) (gridBlockOffsets L i q)
      (refinedBlockUnion i (siteGrid y q)) ∧
    HasSiteCounts (levelDepth K n) (sitesIn (refinedBlockUnion i (siteGrid y q)))
      fun μ => ((q μ : ℤ) + 1) * (L : ℤ) ^ i := by
  have hjk : -(m : ℤ) ≤ levelDepth K k := by
    simp only [levelDepth]
    omega
  have hdep : levelDepth K n = levelDepth K k + i := by
    simp only [levelDepth]
    omega
  have hB := (hLat L m hO h13 hm).2.2.1 (levelDepth K k) i hjk
  have hLat' : SublatticeCoordinates L m (levelDepth K k + i) :=
    (hLat L m hO h13 hm).1 _ (by omega)
  have hM : (m : ℤ) + levelDepth K k = ((m + K - k : ℕ) : ℤ) := by
    simp only [levelDepth]
    omega
  have hq' : ∀ μ, (q μ : ℤ) + 1 < (L : ℤ) ^ (m + K - k) := fun μ => by exact_mod_cast hq μ
  obtain ⟨e1, e2⟩ := siteGrid_facts hO hLat' hB hM hdep y q hq'
  have hP : (0 : ℤ) < (L : ℤ) ^ i := pow_pos (by exact_mod_cast hO.pos) i
  have hbound : ∀ μ, 1 ≤ ((q μ : ℤ) + 1) * (L : ℤ) ^ i ∧
      ((q μ : ℤ) + 1) * (L : ℤ) ^ i < (L : ℤ) ^ (m + K - n) := by
    intro μ
    refine ⟨?_, ?_⟩
    · have : (0 : ℤ) < ((q μ : ℤ) + 1) * (L : ℤ) ^ i := mul_pos (by omega) hP
      omega
    · have e : m + K - n = (m + K - k) + i := by omega
      rw [e, pow_add]
      exact mul_lt_mul_of_pos_right (hq' μ) hP
  have hbox := (hBox L m K ⟨hO, h13⟩ hm hK n (by omega)).1
    (offsetSite (y.toSublattice (levelDepth K n)) fun _ => -halfSideSteps L i) _ hbound
  have hs : (sitesIn (refinedBlockUnion i (siteGrid y q)) : Set (SiteAtLevel L m K n)) =
      sitesFromCorner (offsetSite (y.toSublattice (levelDepth K n))
        fun _ => -halfSideSteps L i) (fun μ => ((q μ : ℤ) + 1) * (L : ℤ) ^ i) := by
    rw [e1, sitesIn_sitesAsTorusPoints]
  rw [hs]
  exact ⟨hbox.1, e2, hbox.2⟩
private theorem siteSegment_eq_siteGrid (y : Site L m j) (μ : Fin 4) (r : ℕ) (hr : 1 ≤ r) :
    siteSegment y μ r = siteGrid y (Pi.single μ (r - 1)) := by
  ext z
  constructor
  · rintro ⟨t, ht, rfl⟩
    refine ⟨Pi.single μ (t : ℤ), fun ρ => ?_, ?_⟩
    · by_cases hρ : ρ = μ
      · subst hρ
        simp only [Pi.single_eq_same]
        omega
      · simp [Pi.single_eq_of_ne hρ]
    · rw [offsetSite_single]
      simp
  · rintro ⟨p, hp, rfl⟩
    have hμ := hp μ
    simp only [Pi.single_eq_same] at hμ
    refine ⟨(p μ).toNat, by omega, ?_⟩
    have hps : p = Pi.single μ (p μ) := by
      funext ρ
      by_cases hρ : ρ = μ
      · subst hρ
        simp
      · have := hp ρ
        simp only [Pi.single_eq_of_ne hρ] at this ⊢
        push_cast at this
        omega
    rw [hps, offsetSite_single]
    simp only [Pi.single_eq_same]
    rw [← natCast_zsmul, Int.toNat_of_nonneg hμ.1]
theorem holds (hLat : CoordinateDescription)
    (hBox : CornerBoxProperties)
    (hPaths : BlockPaths.Statement)
    (hPart : BlockPartition.Properties) : BlocksBoxesPaths.Statement := by
  intro L K m hD
  have hO := hD.odd_L
  have h13 := hD.thirteen_le_L
  have hK := hD.K_pos
  have hm := hD.m_pos
  have hL : 0 < L := hO.pos
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [halfSideSteps, centreToFaceSteps]
  · have h := two_halfSideSteps_add_one hO 1
    have h' : 2 * ((halfSideSteps L 1 : ℤ) : ℝ) + 1 = (L : ℝ) := by
      rw [pow_one] at h
      exact_mod_cast h
    unfold Averaging.OneStep.halfBlockingFactor
    linarith
  · intro i k hik hkK
    have hjk : -(m : ℤ) ≤ levelDepth K k := by
      simp only [levelDepth]
      omega
    have hB := (hLat L m hO h13 hm).2.2.1 (levelDepth K k) i hjk
    have hdep : levelDepth K (k - i) = levelDepth K k + i := by
      simp only [levelDepth]
      omega
    refine ⟨⟨?_, two_halfSideSteps_add_one hO i⟩, fun y => ?_, ?_, fun y q hq => ?_, ?_⟩
    · have hL' : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
      rw [hdep]
      unfold meshSize
      rw [neg_add, zpow_add₀ hL', zpow_neg _ (i : ℤ), zpow_natCast]
      field_simp
    · exact ⟨refinedBlock_parametrized hO hB hdep y, (hB y).2.2.2.1, (hB y).2.2.2.2⟩
    · have hp := (hPart L m ⟨hO, h13⟩ hm (levelDepth K k) i 0 hjk).2.1
      refine ⟨fun a _ b _ hab => hp.2.2.1 hab, ?_⟩
      rw [hdep]
      exact hp.2.2.2
    · exact siteGrid_box hLat hBox hO h13 hm hK hkK (by omega) y q hq
    · intro b μ hb
      have hLat' : SublatticeCoordinates L m (levelDepth K (k - i)) :=
        (hLat L m hO h13 hm).1 _ (by omega)
      have hM : (m : ℤ) + levelDepth K (k - i) = ((m + K - k + i : ℕ) : ℤ) := by
        simp only [levelDepth]
        omega
      have hi : (L : ℤ) ^ i < (L : ℤ) ^ (m + K - k + i) := by
        apply pow_lt_pow_right₀ (by exact_mod_cast (by omega : 1 < L))
        omega
      exact shiftByBlock_across_bond hO hB hLat' hdep hM hi b μ hb
  · intro i j k hji hik hkK
    exact (hLat L m hO h13 hm).2.2.2 K k i j hK hji hik hkK
  · intro k hk
    exact blockUnionsOverSites_holds hPart hLat hO h13 hm hk
  · intro k _ hkK y μ r hr1 hr3
    rw [siteSegment_eq_siteGrid y μ r hr1]
    have hq : ∀ ρ, (Pi.single μ (r - 1) : Fin 4 → ℕ) ρ ≤ 2 := by
      intro ρ
      by_cases hρ : ρ = μ
      · subst hρ
        simp only [Pi.single_eq_same]
        omega
      · simp [Pi.single_eq_of_ne hρ]
    have hbig : 3 < L ^ (m + K - k) := by
      have h1 : L ≤ L ^ (m + K - k) := Nat.le_self_pow (by omega) L
      omega
    obtain ⟨h1, _, h3⟩ := siteGrid_box (n := 0) (i := k) hLat hBox hO h13 hm hK hkK (by omega) y
      (Pi.single μ (r - 1)) (fun ρ => by have := hq ρ; omega)
    refine ⟨h1, _, h3, fun ν => ?_⟩
    have hP : (0 : ℤ) ≤ (L : ℤ) ^ k := by positivity
    have hqν : ((Pi.single μ (r - 1) : Fin 4 → ℕ) ν : ℤ) + 1 ≤ 3 := by
      have := hq ν
      omega
    exact mul_le_mul_of_nonneg_right hqν hP
  · intro n hn
    exact ⟨stepSetsAreBoxes_holds hBox hO h13 hm hK hn, doubleBlockCrossings_holds hPaths hO h13 hm hn,
      contoursCombs_holds hLat hPaths hO h13 hm hn⟩
end YangMills.Construction.PeriodicLattice.BlocksBoxesPaths
