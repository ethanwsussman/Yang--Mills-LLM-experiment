import YangMills.Construction.Lattice.BlockPartition
import YangMills.Construction.Towers.BondsOfADoubleBlockAndTheirImageInATorus
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.DoubleCubeImage
open YangMills.Construction.InfiniteLattice (AmbientSpace)
variable {L k j n : ℕ}
theorem meshAt_eq_mul_pred (hL : 0 < L) (hj : 1 ≤ j) :
    meshAt L k j = (L : ℝ) * meshAt L k (j - 1) := by
  have hL' : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  have e : (j : ℤ) - (k : ℤ) = 1 + (((j - 1 : ℕ) : ℤ) - (k : ℤ)) := by omega
  unfold meshAt
  rw [e, zpow_add₀ hL', zpow_one]
theorem meshAt_ne_zero (hL : 0 < L) (i : ℕ) : meshAt L k i ≠ 0 := by
  have hL' : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  exact zpow_ne_zero _ hL'
theorem torusSide_eq_mul_meshAt (hL : 0 < L) (hj : 1 ≤ j) (hjk : j ≤ k) :
    PeriodicLattice.torusSide L n =
      ((2 * (L : ℤ) ^ (n + (k + 1 - j)) : ℤ) : ℝ) * meshAt L k (j - 1) := by
  have e : ((j - 1 : ℕ) : ℤ) - (k : ℤ) = -((k + 1 - j : ℕ) : ℤ) := by omega
  unfold PeriodicLattice.torusSide meshAt
  rw [e, zpow_neg, zpow_natCast]
  push_cast
  rw [pow_add]
  field_simp
theorem int_eq_zero_of_coe_eq_zero {M a : ℝ} {Q d : ℤ} (ha : a ≠ 0) (hM : M = (Q : ℝ) * a)
    (hd : |d| < Q) (h : (((d : ℝ) * a : ℝ) : AddCircle M) = 0) : d = 0 := by
  obtain ⟨m, hm⟩ := (AddCircle.coe_eq_zero_iff M).1 h
  have h1 : (m : ℝ) * (Q : ℝ) = (d : ℝ) := by
    have h2 : ((m : ℝ) * (Q : ℝ)) * a = (d : ℝ) * a := by
      rw [← hm, hM, zsmul_eq_mul]
      ring
    exact mul_right_cancel₀ ha h2
  have h3 : m * Q = d := by exact_mod_cast h1
  exact Int.eq_zero_of_abs_lt_dvd ⟨m, by rw [← h3]; ring⟩ hd
theorem exists_coords_of_mem (hL : 0 < L) (hj : 1 ≤ j) {c : Edge L k j}
    (hc : c.IsPositivelyOriented)
    {x : AmbientSpace} (hx : x ∈ doubleCube L (meshAt L k (j - 1)) c) :
    ∃ w : Fin 4 → ℤ, (∀ μ, 2 * |w μ| ≤ 3 * (L : ℤ) - 1) ∧
      ∀ μ, x μ = (c.initial : AmbientSpace) μ + (w μ : ℝ) * meshAt L k (j - 1) := by
  obtain ⟨ν₀, hν₀⟩ := hc
  have hterm : ∀ μ, (c.terminal : AmbientSpace) μ =
      (c.initial : AmbientSpace) μ + (Pi.single ν₀ (meshAt L k j) : AmbientSpace) μ := by
    intro μ
    have h := congrArg (fun s : Vertex L k j => (s : AmbientSpace) μ) hν₀
    simp only [InfiniteLattice.axisStep, AddSubgroupClass.coe_sub, Pi.sub_apply] at h
    linarith
  have hLz : (0 : ℤ) < (L : ℤ) := by exact_mod_cast hL
  rcases hx with hx | hx
  · obtain ⟨ν, hν, rfl⟩ := hx
    refine ⟨ν, fun μ => ?_, fun μ => ?_⟩
    · have h := hν μ
      rw [pow_one] at h
      linarith
    · rw [Finset.univ_sum_single]
      rfl
  · obtain ⟨ν, hν, rfl⟩ := hx
    refine ⟨fun μ => ν μ + (Pi.single ν₀ (L : ℤ) : Fin 4 → ℤ) μ, fun μ => ?_, fun μ => ?_⟩
    · have h := hν μ
      rw [pow_one] at h
      by_cases hμ : μ = ν₀
      · subst hμ
        have h2 := abs_add_le (ν μ) (L : ℤ)
        rw [abs_of_pos hLz] at h2
        simp only [Pi.single_eq_same]
        linarith
      · simp only [Pi.single_eq_of_ne hμ, add_zero]
        linarith
    · have hsp := meshAt_eq_mul_pred (k := k) hL hj
      rw [Finset.univ_sum_single, Pi.add_apply, hterm μ]
      by_cases hμ : μ = ν₀
      · subst hμ
        simp only [Pi.single_eq_same]
        push_cast
        linear_combination hsp
      · simp only [Pi.single_eq_of_ne hμ]
        push_cast
        ring
theorem mem_latticeSubgroup_of_mem (hL : 0 < L) (hj : 1 ≤ j) {c : Edge L k j}
    (hc : c.IsPositivelyOriented)
    {x : AmbientSpace} (hx : x ∈ doubleCube L (meshAt L k (j - 1)) c) :
    x ∈ InfiniteLattice.latticeSubgroup (meshAt L k (j - 1)) := by
  obtain ⟨w, -, hw⟩ := exists_coords_of_mem hL hj hc hx
  obtain ⟨t, ht⟩ := c.initial.2
  refine ⟨fun μ => t μ * (L : ℤ) + w μ, fun μ => ?_⟩
  rw [hw μ, ht μ, meshAt_eq_mul_pred hL hj]
  push_cast
  ring
theorem sub_eq_of_torusProj_sub_eq (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n)
    (hj : 1 ≤ j) (hjk : j ≤ k) {c : Edge L k j} (hc : c.IsPositivelyOriented)
    {x x' : AmbientSpace}
    (hx : x ∈ doubleCube L (meshAt L k (j - 1)) c)
    (hx' : x' ∈ doubleCube L (meshAt L k (j - 1)) c) (s : Fin 4 → ℤ)
    (hs : ∀ μ, |s μ| ≤ 1)
    (h : TorusMetric.torusProj (PeriodicLattice.torusSide L n) x' -
        TorusMetric.torusProj (PeriodicLattice.torusSide L n) x =
      TorusMetric.torusProj (PeriodicLattice.torusSide L n)
        (fun μ => (s μ : ℝ) * meshAt L k (j - 1))) :
    ∀ μ, x' μ - x μ = (s μ : ℝ) * meshAt L k (j - 1) := by
  have hL13 : 13 ≤ L := hL.2
  have hL0 : 0 < L := by omega
  obtain ⟨w, hwb, hw⟩ := exists_coords_of_mem hL0 hj hc hx
  obtain ⟨w', hwb', hw'⟩ := exists_coords_of_mem hL0 hj hc hx'
  intro μ
  have hpow : (L : ℤ) ^ 2 ≤ (L : ℤ) ^ (n + (k + 1 - j)) :=
    pow_le_pow_right₀ (by omega) (by omega)
  have hbig : 3 * (L : ℤ) < 2 * (L : ℤ) ^ (n + (k + 1 - j)) := by nlinarith
  have hd : |w' μ - w μ - s μ| < 2 * (L : ℤ) ^ (n + (k + 1 - j)) := by
    have h1 := abs_le.1 (show |w μ| ≤ |w μ| from le_rfl)
    have h2 := abs_le.1 (show |w' μ| ≤ |w' μ| from le_rfl)
    have h3 := abs_le.1 (hs μ)
    have h4 := hwb μ
    have h5 := hwb' μ
    rw [abs_lt]
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]
  have hval : ((w' μ - w μ - s μ : ℤ) : ℝ) * meshAt L k (j - 1) =
      x' μ - x μ - (s μ : ℝ) * meshAt L k (j - 1) := by
    rw [hw μ, hw' μ]
    push_cast
    ring
  have hz : (((((w' μ - w μ - s μ : ℤ) : ℝ) * meshAt L k (j - 1) : ℝ)) :
      AddCircle (PeriodicLattice.torusSide L n)) = 0 := by
    have h0 := congrFun h μ
    simp only [TorusMetric.torusProj, Pi.sub_apply] at h0
    rw [hval, AddCircle.coe_sub, AddCircle.coe_sub, h0, sub_self]
  have hd0 := int_eq_zero_of_coe_eq_zero (meshAt_ne_zero hL0 (j - 1))
    (torusSide_eq_mul_meshAt hL0 hj hjk) hd hz
  rw [hd0] at hval
  simp only [Int.cast_zero, zero_mul] at hval
  linarith
theorem torusProj_single (μ : Fin 4) (e : ℤ) (a : ℝ) :
    TorusMetric.torusProj (PeriodicLattice.torusSide L n)
        (fun ν => ((Pi.single μ e : Fin 4 → ℤ) ν : ℝ) * a) =
      PeriodicLattice.pointOnAxis L n μ ((e : ℝ) * a) := by
  funext ν
  by_cases h : ν = μ
  · subst h
    simp [TorusMetric.torusProj, PeriodicLattice.pointOnAxis]
  · simp [TorusMetric.torusProj, PeriodicLattice.pointOnAxis, Pi.single_eq_of_ne h]
theorem torusProj_image_cube (hb : PeriodicLattice.BlockPartition.Properties)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) (hj : 1 ≤ j) (hjk : j ≤ k)
    (y : Vertex L k j) :
    TorusMetric.torusProj (PeriodicLattice.torusSide L n) '' cube L (meshAt L k (j - 1)) y =
      PeriodicLattice.unitBlock (projVertex L n k j y) := by
  have hL0 : 0 < L := by have := hL.2; omega
  have hJ : -(n : ℤ) ≤ PeriodicLattice.levelDepth k j := by
    simp only [PeriodicLattice.levelDepth]
    omega
  have h := ((hb L n hL hn (PeriodicLattice.levelDepth k j) 1 0 hJ).1 (projVertex L n k j y)).1
  have hs : PeriodicLattice.meshSize L (PeriodicLattice.levelDepth k j + ((1 : ℕ) : ℤ)) =
      meshAt L k (j - 1) := by
    rw [← meshSize_levelDepth L k (j - 1)]
    congr 1
    simp only [PeriodicLattice.levelDepth]
    omega
  have hcoe : (((projVertex L n k j y).toSublattice
        (PeriodicLattice.levelDepth k j + ((1 : ℕ) : ℤ)) :
      PeriodicLattice.Site L n (PeriodicLattice.levelDepth k j + ((1 : ℕ) : ℤ))) :
        PeriodicLattice.FourTorus L n) =
      (projVertex L n k j y : PeriodicLattice.FourTorus L n) :=
    Classical.epsilon_spec
      (p := fun x : PeriodicLattice.Site L n (PeriodicLattice.levelDepth k j + ((1 : ℕ) : ℤ)) =>
        (x : PeriodicLattice.FourTorus L n) = (projVertex L n k j y : PeriodicLattice.FourTorus L n))
      ⟨⟨_, PeriodicLattice.sublattice_mono hL0 n (by omega) (projVertex L n k j y).2⟩, rfl⟩
  have hpt : ∀ p : Fin 4 → ℤ,
      ((PeriodicLattice.refinedOffsetSite 1 (projVertex L n k j y) p :
        PeriodicLattice.Site L n (PeriodicLattice.levelDepth k j + ((1 : ℕ) : ℤ))) :
          PeriodicLattice.FourTorus L n) =
        TorusMetric.torusProj (PeriodicLattice.torusSide L n)
          ((y : AmbientSpace) + fun μ => (p μ : ℝ) * meshAt L k (j - 1)) := by
    intro p
    funext ν
    simp only [PeriodicLattice.refinedOffsetSite, PeriodicLattice.offsetSite,
      AddSubgroup.coe_add, hcoe, AddSubmonoidClass.coe_finsetSum, AddSubgroupClass.coe_zsmul,
      Pi.add_apply, Finset.sum_apply, Pi.smul_apply, PeriodicLattice.unitStep,
      PeriodicLattice.pointOnAxis,
      hs, Pi.single_apply, smul_ite, smul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    simp only [projVertex, TorusMetric.torusProj, Pi.add_apply, AddCircle.coe_add]
    congr 1
    rw [← AddCircle.coe_zsmul, zsmul_eq_mul]
  show _ = PeriodicLattice.refinedBlock 1 _
  rw [h]
  ext z
  constructor
  · rintro ⟨x, ⟨ν, hν, rfl⟩, rfl⟩
    refine ⟨ν, hν, ?_⟩
    show _ = _
    rw [Finset.univ_sum_single]
    exact hpt ν
  · rintro ⟨p, hp, rfl⟩
    refine ⟨_, ⟨p, hp, rfl⟩, ?_⟩
    rw [Finset.univ_sum_single]
    exact (hpt p).symm
theorem doubleCubeLinksAndTorusImage (hq : Tower.EdgeProjectionProperties)
    (hb : PeriodicLattice.BlockPartition.Properties) :
    DoubleCubeLinksAndTorusImage := by
  intro L k j hL hj hjk c hc
  refine ⟨⟨rfl, fun b hb' => ⟨hb'.2, hb'.1⟩⟩, fun n hn => ?_⟩
  have hL0 : 0 < L := by have := hL.2; omega
  have hqj := (hq L n k j hL hn hjk).1 c
  have hq' := (hq L n k (j - 1) hL hn (by omega)).1
  have himi := torusProj_image_cube hb hL hn hj hjk c.initial
  have himt := torusProj_image_cube hb hL hn hj hjk c.terminal
  have hDC : TorusMetric.torusProj (PeriodicLattice.torusSide L n) ''
      doubleCube L (meshAt L k (j - 1)) c =
      PeriodicLattice.bondDoubleBlock (projEdge L n k j c) := by
    unfold doubleCube PeriodicLattice.bondDoubleBlock
    rw [image_union, himi, himt, hqj.1, hqj.2.1]
  have hinj : InjOn (TorusMetric.torusProj (PeriodicLattice.torusSide L n))
      (doubleCube L (meshAt L k (j - 1)) c) := by
    intro x hx y hy hxy
    have h := sub_eq_of_torusProj_sub_eq hL hn hj hjk hc hx hy (fun _ => 0) (by simp)
      (by rw [hxy, sub_self]; funext μ; simp [TorusMetric.torusProj])
    funext μ
    have h' := h μ
    simp only [Int.cast_zero, zero_mul] at h'
    linarith
  refine ⟨hqj.1, hqj.2.1, hqj.2.2.1 hc, hinj, himi, himt, ?_, ?_, ?_⟩
  · intro b hb'
    show ((projEdge L n k (j - 1) b).source : PeriodicLattice.FourTorus L n) ∈ _ ∧
      ((projEdge L n k (j - 1) b).target : PeriodicLattice.FourTorus L n) ∈ _
    rw [(hq' b).1, (hq' b).2.1, ← hDC]
    exact ⟨⟨_, hb'.1, rfl⟩, ⟨_, hb'.2, rfl⟩⟩
  · intro b hb' b' hb'' h
    have hi : (b.initial : AmbientSpace) = b'.initial := by
      refine hinj hb'.1 hb''.1 ?_
      have h1 := congrArg (fun d : Tower.Edge L n k (j - 1) => d.source) h
      simp only [(hq' b).1, (hq' b').1] at h1
      exact congrArg Subtype.val h1
    have ht : (b.terminal : AmbientSpace) = b'.terminal := by
      refine hinj hb'.2 hb''.2 ?_
      have h1 := congrArg (fun d : Tower.Edge L n k (j - 1) => d.target) h
      simp only [(hq' b).2.1, (hq' b').2.1] at h1
      exact congrArg Subtype.val h1
    exact InfiniteLattice.Link.ext (Subtype.ext hi) (Subtype.ext ht)
  · intro b' hb'
    obtain ⟨hb1, hb2⟩ := hb'
    rw [← hDC] at hb1 hb2
    obtain ⟨x, hx, hxe⟩ := hb1
    obtain ⟨x', hx', hxe'⟩ := hb2
    have hxs := mem_latticeSubgroup_of_mem hL0 hj hc hx
    have hxs' := mem_latticeSubgroup_of_mem hL0 hj hc hx'
    have hsp := meshSize_levelDepth L k (j - 1)
    have lift : ∀ (μ : Fin 4) (e : ℤ), (e = 1 ∨ e = -1) →
        (b'.target : PeriodicLattice.FourTorus L n) - (b'.source : PeriodicLattice.FourTorus L n) =
          PeriodicLattice.pointOnAxis L n μ ((e : ℝ) * meshAt L k (j - 1)) →
        ∃ b ∈ doubleCubeLinks L (meshAt L k (j - 1)) c,
          projEdge L n k (j - 1) b = b' := by
      intro μ e he h
      have hd := sub_eq_of_torusProj_sub_eq hL hn hj hjk hc hx hx' (Pi.single μ e)
        (fun ν => by
          by_cases hν : ν = μ
          · subst hν
            rcases he with rfl | rfl <;> simp
          · simp [Pi.single_eq_of_ne hν])
        (by rw [hxe, hxe', torusProj_single]; exact h)
      have hadj : ∃ μ : Fin 4,
          (⟨x', hxs'⟩ - ⟨x, hxs⟩ : Vertex L k (j - 1)) =
              InfiniteLattice.axisStep (meshAt L k (j - 1)) μ ∨
            (⟨x', hxs'⟩ - ⟨x, hxs⟩ : Vertex L k (j - 1)) =
              -InfiniteLattice.axisStep (meshAt L k (j - 1)) μ := by
        refine ⟨μ, ?_⟩
        rcases he with rfl | rfl
        · refine Or.inl (Subtype.ext (funext fun ν => ?_))
          have h' := hd ν
          by_cases hν : ν = μ
          · subst hν
            simpa [InfiniteLattice.axisStep] using h'
          · simpa [InfiniteLattice.axisStep, Pi.single_eq_of_ne hν] using h'
        · refine Or.inr (Subtype.ext (funext fun ν => ?_))
          have h' := hd ν
          by_cases hν : ν = μ
          · subst hν
            simpa [InfiniteLattice.axisStep] using h'
          · simpa [InfiniteLattice.axisStep, Pi.single_eq_of_ne hν] using h'
      refine ⟨⟨⟨x, hxs⟩, ⟨x', hxs'⟩, hadj⟩, ⟨hx, hx'⟩, ?_⟩
      refine PeriodicLattice.Bond.ext ?_ ?_
      · rw [(hq' _).1]
        exact Subtype.ext hxe
      · rw [(hq' _).2.1]
        exact Subtype.ext hxe'
    obtain ⟨μ, h | h⟩ := b'.isNeighbour
    · refine lift μ 1 (Or.inl rfl) ?_
      have h1 := congrArg (fun s : Tower.Vertex L n k (j - 1) =>
        (s : PeriodicLattice.FourTorus L n)) h
      simp only [AddSubgroupClass.coe_sub, PeriodicLattice.unitStep, hsp] at h1
      simpa using h1
    · refine lift μ (-1) (Or.inr rfl) ?_
      have h1 := congrArg (fun s : Tower.Vertex L n k (j - 1) =>
        (s : PeriodicLattice.FourTorus L n)) h
      simp only [AddSubgroupClass.coe_sub, NegMemClass.coe_neg, PeriodicLattice.unitStep,
        hsp] at h1
      rw [h1]
      funext ν
      by_cases hν : ν = μ
      · subst hν
        simp [PeriodicLattice.pointOnAxis]
      · simp [PeriodicLattice.pointOnAxis, Pi.single_eq_of_ne hν]
end YangMills.Construction.Tower.FullSpace.DoubleCubeImage
end
