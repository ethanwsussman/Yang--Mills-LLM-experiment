import YangMills.Construction.Lattice.BlocksAndLinearSizesUnderIsometriesProof
import YangMills.Construction.Lattice.SitesBondsAndPlaquettesOfSetsUnderIsometriesProof
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.PeriodicLattice.IsometryImages
variable {L m : ℕ} {j : ℤ}
theorem meshSize_pos (hL : 0 < L) (j : ℤ) : 0 < meshSize L j := by apply _root_.YangMills.SharedProofs.p6250 <;> assumption
theorem meshSize_eq_mul_succ (hL : 0 < L) (j : ℤ) :
    meshSize L j = (L : ℝ) * meshSize L (j + 1) := by
  have hL' : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  rw [meshSize, meshSize, neg_add, zpow_add₀ hL', zpow_neg_one]
  field_simp
theorem torusSide_eq_pow_mul (hL : 0 < L) (hj : -(m : ℤ) ≤ j) :
    ∃ d : ℕ, torusSide L m = (2 * (L : ℝ) ^ d) * meshSize L j := by
  obtain ⟨d, hd⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ (m : ℤ) + j by omega)
  have hL' : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  refine ⟨d, ?_⟩
  have hm : (m : ℤ) = (d : ℤ) + -j := by omega
  rw [torusSide, meshSize, ← zpow_natCast (L : ℝ) m, hm, zpow_add₀ hL', zpow_natCast]
  ring
theorem exists_int_mul_meshSize (hL : 0 < L) (hj : -(m : ℤ) ≤ j) {s : ℝ} {n : ℤ}
    (h : (s : AddCircle (torusSide L m)) =
      (((n : ℝ) * meshSize L j : ℝ) : AddCircle (torusSide L m))) :
    ∃ N : ℤ, s = (N : ℝ) * meshSize L j := by apply _root_.YangMills.Construction.PeriodicLattice.IsometryCells.exists_int_mul_meshSize_of_coe_eq <;> assumption
theorem coe_meshSize_ne_zero (hL : 0 < L) (hj : -(m : ℤ) ≤ j) :
    ((meshSize L j : ℝ) : AddCircle (torusSide L m)) ≠ 0 := by
  intro h
  obtain ⟨k, hk⟩ := (AddCircle.coe_eq_zero_iff _).1 h
  obtain ⟨d, hs⟩ := torusSide_eq_pow_mul (m := m) hL hj
  rw [zsmul_eq_mul, hs] at hk
  have e : (k : ℝ) * (2 * (L : ℝ) ^ d) = 1 :=
    mul_right_cancel₀ (meshSize_pos hL j).ne' (by rw [one_mul, mul_assoc]; exact hk)
  have e' : k * (2 * (L : ℤ) ^ d) = 1 := by exact_mod_cast e
  have e'' : 2 * (k * (L : ℤ) ^ d) = 1 := by linarith
  omega
theorem coe_mul_ne_coe_add_half (hL : 0 < L) (hj : -(m : ℤ) ≤ j) (a b : ℤ) :
    (((a : ℝ) * meshSize L j : ℝ) : AddCircle (torusSide L m)) ≠
      (((b : ℝ) * meshSize L j + meshSize L j / 2 : ℝ) : AddCircle (torusSide L m)) := by
  intro h
  obtain ⟨N, hN⟩ := exists_int_mul_meshSize hL hj h.symm
  have hs := (meshSize_pos hL j).ne'
  have e₁ : ((b : ℝ) + 1 / 2) * meshSize L j = (N : ℝ) * meshSize L j := by linarith
  have e₂ := mul_right_cancel₀ hs e₁
  have e₃ : (2 * b + 1 : ℝ) = 2 * (N : ℝ) := by linarith
  have e₄ : 2 * b + 1 = 2 * N := by exact_mod_cast e₃
  omega
theorem pointOnAxis_same (μ : Fin 4) (t : ℝ) :
    pointOnAxis L m μ t μ = (t : AddCircle (torusSide L m)) := by
  simp [pointOnAxis]
theorem pointOnAxis_of_ne {μ ν : Fin 4} (h : ν ≠ μ) (t : ℝ) : pointOnAxis L m μ t ν = 0 := by
  simp [pointOnAxis, Pi.single_eq_of_ne h]
theorem coe_unitStep (μ : Fin 4) :
    ((unitStep L m j μ : Site L m j) : FourTorus L m) = pointOnAxis L m μ (meshSize L j) := rfl
theorem coe_zsmul_unitStep_succ (hL : 0 < L) (μ : Fin 4) :
    (((L : ℤ) • unitStep L m (j + 1) μ : Site L m (j + 1)) : FourTorus L m) =
      ((unitStep L m j μ : Site L m j) : FourTorus L m) := by
  funext ν
  have e : (((L : ℤ) • unitStep L m (j + 1) μ : Site L m (j + 1)) : FourTorus L m) ν =
      (L : ℤ) • pointOnAxis L m μ (meshSize L (j + 1)) ν := by
    simp [unitStep]
  rw [e, coe_unitStep]
  by_cases h : ν = μ
  · subst h
    rw [pointOnAxis_same, pointOnAxis_same, ← AddCircle.coe_zsmul, zsmul_eq_mul,
      meshSize_eq_mul_succ hL j]
    simp
  · rw [pointOnAxis_of_ne h, pointOnAxis_of_ne h, smul_zero]
theorem abs_cast_lt_zpow (hL : 1 < L) (hm : 0 < m) (hj : 0 ≤ j) :
    (((|(L : ℤ)| : ℤ)) : ℝ) < (L : ℝ) ^ ((m : ℤ) + (j + 1)) := by
  obtain ⟨d, hd⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ (m : ℤ) + (j + 1) - 2 by omega)
  have e : (m : ℤ) + (j + 1) = ((d + 2 : ℕ) : ℤ) := by push_cast; omega
  have h1 : (1 : ℝ) ≤ (L : ℝ) ^ d := one_le_pow₀ (by exact_mod_cast hL.le)
  have h2 : (1 : ℝ) < L := by exact_mod_cast hL
  rw [e, zpow_natCast, pow_add, Nat.abs_cast, Int.cast_natCast]
  nlinarith
theorem image_coe_vertices (hL : 0 < L) (hj : -(m : ℤ) ≤ j) (p : Plaquette L m j) :
    (fun x : Site L m j => (x : FourTorus L m)) '' p.vertices =
      p.face ∩ (sublattice L m j : Set (FourTorus L m)) := by apply _root_.YangMills.Construction.PeriodicLattice.IsometryCells.coe_vertices_eq <;> assumption
theorem barycenter_apply_spec (p : Plaquette L m j) (ν : Fin 4) :
    ∃ n : ℤ, (p.origin : FourTorus L m) ν =
        (((n : ℝ) * meshSize L j : ℝ) : AddCircle (torusSide L m)) ∧
      ((ν = p.firstAxis ∨ ν = p.secondAxis) → p.barycenter ν =
        (((n : ℝ) * meshSize L j + meshSize L j / 2 : ℝ) : AddCircle (torusSide L m))) ∧
      ((ν ≠ p.firstAxis ∧ ν ≠ p.secondAxis) → p.barycenter ν =
        (((n : ℝ) * meshSize L j : ℝ) : AddCircle (torusSide L m))) := by
  obtain ⟨n, hn⟩ := p.origin.2
  refine ⟨n ν, hn ν, ?_, ?_⟩
  · have hne : p.firstAxis ≠ p.secondAxis := p.firstAxis_lt_secondAxis.ne
    rintro (rfl | rfl)
    · simp only [Plaquette.barycenter, Pi.add_apply, pointOnAxis_same, pointOnAxis_of_ne hne,
        add_zero]
      rw [hn, AddCircle.coe_add]
    · simp only [Plaquette.barycenter, Pi.add_apply, pointOnAxis_same,
        pointOnAxis_of_ne hne.symm, add_zero]
      rw [hn, AddCircle.coe_add]
  · rintro ⟨h₁, h₂⟩
    simp only [Plaquette.barycenter, Pi.add_apply, pointOnAxis_of_ne h₁, pointOnAxis_of_ne h₂,
      add_zero]
    exact hn ν
theorem eq_of_barycenter_eq (hL : 0 < L) (hj : -(m : ℤ) ≤ j) {p q : Plaquette L m j}
    (h : p.barycenter = q.barycenter) : p = q := by
  have key : ∀ {p q : Plaquette L m j}, p.barycenter = q.barycenter → ∀ ν : Fin 4,
      (ν = p.firstAxis ∨ ν = p.secondAxis) → ν = q.firstAxis ∨ ν = q.secondAxis := by
    intro p q h ν hν
    by_contra hc
    push Not at hc
    obtain ⟨a, -, ha, -⟩ := barycenter_apply_spec p ν
    obtain ⟨b, -, -, hb⟩ := barycenter_apply_spec q ν
    have e := (hb hc).symm.trans ((congrFun h ν).symm.trans (ha hν))
    exact coe_mul_ne_coe_add_half hL hj b a e
  have hf := key h p.firstAxis (Or.inl rfl)
  have hg := key h p.secondAxis (Or.inr rfl)
  have h₁ := p.firstAxis_lt_secondAxis
  have h₂ := q.firstAxis_lt_secondAxis
  have hd : p.firstAxis = q.firstAxis ∧ p.secondAxis = q.secondAxis := by
    rcases hf with hf | hf <;> rcases hg with hg | hg
    · exact absurd (hf.trans hg.symm) h₁.ne
    · exact ⟨hf, hg⟩
    · exfalso
      rw [hf, hg] at h₁
      exact lt_asymm h₁ h₂
    · exact absurd (hf.trans hg.symm) h₁.ne
  have hb : (p.origin : FourTorus L m) = q.origin := by
    have e : (p.origin : FourTorus L m) + pointOnAxis L m p.firstAxis (meshSize L j / 2) +
        pointOnAxis L m p.secondAxis (meshSize L j / 2) = (q.origin : FourTorus L m) +
        pointOnAxis L m p.firstAxis (meshSize L j / 2) +
        pointOnAxis L m p.secondAxis (meshSize L j / 2) := by
      rw [hd.1, hd.2]
      rw [← hd.1, ← hd.2]
      have := h
      simp only [Plaquette.barycenter] at this
      rwa [← hd.1, ← hd.2] at this
    exact add_right_cancel (add_right_cancel e)
  exact Plaquette.ext (Subtype.ext hb) hd.1 hd.2
theorem flowAlong_eq_cons (z : Site L m j) (μ : Fin 4) {a : ℤ} (ha : a ≠ 0) :
    ∃ b t, flowAlong z μ a = b :: t ∧
      (b.target = z + unitStep L m j μ ∨ b.target = z - unitStep L m j μ) := by
  unfold flowAlong
  split_ifs with h
  · obtain ⟨k, hk⟩ : ∃ k, a.toNat = k + 1 := ⟨a.toNat - 1, by omega⟩
    rw [hk]
    exact ⟨_, _, rfl, Or.inl rfl⟩
  · obtain ⟨k, hk⟩ : ∃ k, (-a).toNat = k + 1 := ⟨(-a).toNat - 1, by omega⟩
    rw [hk]
    exact ⟨_, _, rfl, Or.inr rfl⟩
theorem axis_eq_of_neighbour (hL : 0 < L) (hj : -(m : ℤ) ≤ j) {z w : Site L m j}
    {μ μ' : Fin 4}
    (h₁ : w = z + unitStep L m j μ ∨ w = z - unitStep L m j μ)
    (h₂ : w = z + unitStep L m j μ' ∨ w = z - unitStep L m j μ') : μ = μ' := by
  by_contra hne
  have hξ := coe_meshSize_ne_zero (m := m) hL hj
  have c₂ : (w : FourTorus L m) μ = (z : FourTorus L m) μ := by
    rcases h₂ with rfl | rfl
    · simp [coe_unitStep, pointOnAxis_of_ne hne]
    · simp [coe_unitStep, pointOnAxis_of_ne hne]
  rcases h₁ with rfl | rfl
  · apply hξ
    simpa [coe_unitStep, pointOnAxis_same] using c₂
  · apply hξ
    simpa [coe_unitStep, pointOnAxis_same] using c₂
theorem stepsThroughAxes_inj (hL : 0 < L) (hj : -(m : ℤ) ≤ j) (n : Fin 4 → ℤ) :
    ∀ (l l' : List (Fin 4)) (z : Site L m j), l.length = l'.length → (∀ μ ∈ l, n μ ≠ 0) →
      (∀ μ ∈ l', n μ ≠ 0) → stepsThroughAxes n z l = stepsThroughAxes n z l' → l = l' := by
  intro l
  induction l with
  | nil =>
    intro l' z hl _ _ _
    cases l' with
    | nil => rfl
    | cons _ _ => simp at hl
  | cons μ l ih =>
    intro l' z hl h₁ h₂ e
    cases l' with
    | nil => simp at hl
    | cons μ' l' =>
      simp only [stepsThroughAxes] at e
      obtain ⟨b, t, e₁, hb⟩ := flowAlong_eq_cons z μ (h₁ μ (by simp))
      obtain ⟨b', t', e₂, hb'⟩ := flowAlong_eq_cons z μ' (h₂ μ' (by simp))
      have hbb : b = b' := by
        have e' := e
        rw [e₁, e₂] at e'
        exact (List.cons.inj e').1
      have hμ : μ = μ' := axis_eq_of_neighbour hL hj hb (hbb ▸ hb')
      subst hμ
      have e₃ := List.append_cancel_left e
      rw [ih l' _ (by simpa using hl) (fun ν hν => h₁ ν (by simp [hν]))
        (fun ν hν => h₂ ν (by simp [hν])) e₃]
theorem orderedContour_injective {j' : ℤ} (hL : 0 < L) (hj : -(m : ℤ) ≤ j') (y : Site L m j)
    (x : Site L m j') : Function.Injective (orderedContour y x) := by
  intro s s' e
  have hm : ∀ (s : AxisOrdering y x), ∀ μ ∈ (List.finRange _).map
      (fun i => ((s i : offsetAxes y x) : Fin 4)), blockOffset y x μ ≠ 0 := by
    intro s μ hμ
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hμ
    exact (Finset.mem_filter.1 (s i).2).2
  have hl := stepsThroughAxes_inj hL hj (blockOffset y x) _ _ (y.toSublattice j')
    (by simp) (hm s) (hm s') e
  exact Equiv.ext fun i => Subtype.ext (List.map_inj_left.1 hl i (List.mem_finRange i))
section Images
variable {σ : FourTorus L m ≃ FourTorus L m}
theorem coe_sitePreimage_symm
    (hl : σ '' (sublattice L m j : Set (FourTorus L m)) = sublattice L m j)
    (y : Site L m j) : ((sitePreimage σ.symm y : Site L m j) : FourTorus L m) = σ y := by apply _root_.YangMills.Construction.PeriodicLattice.IsometryCells.coe_siteImage <;> assumption
theorem coe_toSublattice {j' : ℤ} (hL : 0 < L) (h : j ≤ j') (y : Site L m j) :
    ((y.toSublattice j' : Site L m j') : FourTorus L m) = y := by apply _root_.YangMills.Construction.SeparatedSequences.BlockAverages.coe_toSublattice <;> assumption
theorem bondImage_source (hc : MapsCellsAndCubes σ j) (b : Bond L m j) :
    (bondImage σ b).source = sitePreimage σ.symm b.source :=
  Subtype.ext (by rw [(hc.2.2.2.1 b).1, coe_sitePreimage_symm hc.1])
theorem bondImage_target (hc : MapsCellsAndCubes σ j) (b : Bond L m j) :
    (bondImage σ b).target = sitePreimage σ.symm b.target :=
  Subtype.ext (by rw [(hc.2.2.2.1 b).2, coe_sitePreimage_symm hc.1])
theorem bondImage_injective (hc : MapsCellsAndCubes σ j) (hs : MapsCellsAndCubes σ.symm j) :
    Function.Injective (bondImage σ : Bond L m j → Bond L m j) := by apply _root_.YangMills.Construction.PeriodicLattice.IsometryInvariance.bondImage_injective <;> assumption
theorem apply_coord {r : SignedFrame} {v : Fin 4 → ℝ} (h : IsInducedByAffine σ r v)
    (x : FourTorus L m) (μ : Fin 4) :
    σ x μ = ((r.2 μ : ℤˣ) : ℤ) • x (r.1 μ) + (v μ : AddCircle (torusSide L m)) := by apply _root_.YangMills.Construction.PeriodicLattice.IsometryInvariance.isInducedByAffine_apply <;> assumption
theorem map_add_add {r : SignedFrame} {v : Fin 4 → ℝ} (h : IsInducedByAffine σ r v)
    (a b w : FourTorus L m) : σ (a + w) + σ b = σ a + σ (b + w) := by
  funext μ
  simp only [Pi.add_apply, apply_coord h, smul_add]
  abel
end Images
section Objects
variable {σ : FourTorus L m ≃ FourTorus L m}
theorem mapsBlockSites (hc : MapsCellsAndCubes σ (j + 1))
    (hs : MapsCellsAndCubes σ.symm (j + 1))
    (hb : IsometryInvariance.MapsBlocks σ j) (y : Site L m j) :
    MapsBlockSites σ (j + 1) y := by
  have hbl := hb 1 y
  unfold MapsBlockSites
  refine BijOn.mk (fun x hx => ?_) (fun x _ x' _ e => ?_) (fun x hx => ?_)
  · show ((sitePreimage σ.symm x : Site L m (j + 1)) : FourTorus L m) ∈
      refinedBlock 1 (sitePreimage σ.symm y)
    rw [coe_sitePreimage_symm hc.1, ← hbl]
    exact mem_image_of_mem σ hx
  · apply Subtype.ext
    have e' := congrArg (fun s : Site L m (j + 1) => (s : FourTorus L m)) e
    simp only [coe_sitePreimage_symm hc.1] at e'
    exact σ.injective e'
  · have h₁ : (x : FourTorus L m) ∈ σ '' refinedBlock 1 y := by
      rw [hbl]
      exact hx
    obtain ⟨a, ha, e⟩ := h₁
    refine ⟨sitePreimage σ.symm.symm x, ?_, ?_⟩
    · show ((sitePreimage σ.symm.symm x : Site L m (j + 1)) : FourTorus L m) ∈ refinedBlock 1 y
      rw [coe_sitePreimage_symm hs.1, ← e]
      simpa using ha
    · apply Subtype.ext
      rw [coe_sitePreimage_symm hc.1, coe_sitePreimage_symm hs.1]
      simp
theorem mapsContourIndices {y : Site L m j} {x : Site L m (j + 1)}
    (hfam : pathImage σ '' contourSet y x =
      contourSet (sitePreimage σ.symm y) (sitePreimage σ.symm x))
    (h₁ : Function.Injective (orderedContour y x))
    (h₂ : Function.Injective
      (orderedContour (sitePreimage σ.symm y) (sitePreimage σ.symm x)))
    (hI : Function.Injective (bondImage σ : Bond L m (j + 1) → Bond L m (j + 1))) :
    MapsContourIndices σ y x := by
  have hP : Function.Injective (pathImage σ : List (Bond L m (j + 1)) → _) :=
    fun Γ Γ' e => List.map_injective_iff.2 hI e
  have hex : ∀ s, ∃ s', orderedContour (sitePreimage σ.symm y) (sitePreimage σ.symm x) s' =
      pathImage σ (orderedContour y x s) := by
    intro s
    exact show pathImage σ (orderedContour y x s) ∈
        contourSet (sitePreimage σ.symm y) (sitePreimage σ.symm x) from by
      rw [← hfam]
      exact mem_image_of_mem _ (mem_range_self s)
  choose f hf using hex
  have hbij : Function.Bijective f := by
    refine ⟨fun s s' e => h₁ (hP ?_), fun s' => ?_⟩
    · rw [← hf, ← hf, e]
    · have h : orderedContour (sitePreimage σ.symm y) (sitePreimage σ.symm x) s' ∈
          pathImage σ '' contourSet y x := by
        rw [hfam]
        exact mem_range_self s'
      obtain ⟨_, ⟨s, rfl⟩, e⟩ := h
      exact ⟨s, h₂ ((hf s).trans e)⟩
  exact ⟨Equiv.ofBijective f hbij, fun s => hf s⟩
theorem coe_shiftAcross (hL : 0 < L) (c : Bond L m j) (x : Site L m (j + 1)) :
    ((shiftAcross c x : Site L m (j + 1)) : FourTorus L m) =
      x + ((c.target : FourTorus L m) - c.source) := by
  show (x : FourTorus L m) +
    (((c.target - c.source).toSublattice (j + 1) : Site L m (j + 1)) : FourTorus L m) = _
  rw [coe_toSublattice hL (by omega)]
  rfl
theorem exists_axialDisplacement (hL : 1 < L) (hm : 0 < m) (hj : 0 ≤ j) (c : Bond L m j)
    {a b : Site L m (j + 1)}
    (hab : (b : FourTorus L m) - a = (c.target : FourTorus L m) - c.source) :
    ∃ μ n, IsAxialDisplacement a b μ n := by
  have hL0 : 0 < L := by omega
  obtain ⟨μ, h | h⟩ := c.isNeighbour
  · refine ⟨μ, (L : ℤ), Subtype.ext ?_, abs_cast_lt_zpow hL hm hj⟩
    rw [coe_zsmul_unitStep_succ hL0]
    exact hab.trans (congrArg (fun s : Site L m j => (s : FourTorus L m)) h)
  · refine ⟨μ, -(L : ℤ), Subtype.ext ?_, by rw [abs_neg]; exact abs_cast_lt_zpow hL hm hj⟩
    have e : ((-(L : ℤ) • unitStep L m (j + 1) μ : Site L m (j + 1)) : FourTorus L m) =
        -(((L : ℤ) • unitStep L m (j + 1) μ : Site L m (j + 1)) : FourTorus L m) := by
      rw [neg_smul]
      rfl
    rw [e, coe_zsmul_unitStep_succ hL0]
    exact hab.trans (congrArg (fun s : Site L m j => (s : FourTorus L m)) h)
theorem mapsCrossing {r : SignedFrame} {v : Fin 4 → ℝ} (hL : 1 < L) (hm : 0 < m) (hj : 0 ≤ j)
    (h : IsInducedByAffine σ r v) (hcj : MapsCellsAndCubes σ j)
    (hc : MapsCellsAndCubes σ (j + 1))
    (hp : IsometryInvariance.MapsAxialPaths σ (j + 1)) (c : Bond L m j)
    (x : Site L m (j + 1)) : MapsCrossing σ c x := by
  have hL0 : 0 < L := by omega
  have e₁ : sitePreimage σ.symm (shiftAcross c x) =
      shiftAcross (bondImage σ c) (sitePreimage σ.symm x) := by
    apply Subtype.ext
    rw [coe_sitePreimage_symm hc.1, coe_shiftAcross hL0, coe_shiftAcross hL0,
      coe_sitePreimage_symm hc.1, (hcj.2.2.2.1 c).1, (hcj.2.2.2.1 c).2]
    have e := map_add_add h (x : FourTorus L m) (c.source : FourTorus L m)
      ((c.target : FourTorus L m) - c.source)
    rw [add_sub_cancel] at e
    rw [eq_sub_of_add_eq e]
    abel
  refine ⟨e₁, ?_⟩
  unfold crossingPath
  rw [← e₁]
  refine (hp x (shiftAcross c x) (exists_axialDisplacement hL hm hj c ?_)).2
  rw [coe_shiftAcross hL0]
  abel
theorem mapsTransportPath (hL : 1 < L) (hm : 0 < m) (hj : 0 ≤ j)
    (hcj : MapsCellsAndCubes σ j) (hc : MapsCellsAndCubes σ (j + 1))
    (hp : IsometryInvariance.MapsAxialPaths σ (j + 1)) (c : Bond L m j) :
    MapsTransportPath σ (j + 1) c := by
  have hL0 : 0 < L := by omega
  have hle : j ≤ j + 1 := by omega
  have e : ∀ y : Site L m j, (sitePreimage σ.symm y : Site L m j).toSublattice (j + 1) =
      sitePreimage σ.symm (y.toSublattice (j + 1)) := fun y =>
    Subtype.ext (by
      rw [coe_toSublattice hL0 hle, coe_sitePreimage_symm hcj.1, coe_sitePreimage_symm hc.1,
        coe_toSublattice hL0 hle])
  unfold MapsTransportPath
  rw [bondImage_source hcj, bondImage_target hcj, e, e]
  refine (hp _ _ (exists_axialDisplacement hL hm hj c ?_)).2
  rw [coe_toSublattice hL0 hle, coe_toSublattice hL0 hle]
theorem plaquetteImage_mem_plaquettesInside (hL : 0 < L) (hj : -(m : ℤ) ≤ j)
    (hc : MapsCellsAndCubes σ j)
    (hl : σ.symm '' (sublattice L m j : Set (FourTorus L m)) = sublattice L m j)
    (X : Set (FourTorus L m))
    {p : Plaquette L m j} (hp : p ∈ (plaquettesInside X : Set (Plaquette L m j))) :
    plaquetteImage σ p ∈ (plaquettesInside (σ '' X) : Set (Plaquette L m j)) := by
  intro c hc'
  have h₁ : (c : FourTorus L m) ∈ (plaquetteImage σ p).face := by
    have h := image_coe_vertices hL hj (plaquetteImage σ p)
    exact (h ▸ mem_image_of_mem (fun x : Site L m j => (x : FourTorus L m)) hc' :
      (c : FourTorus L m) ∈
        (plaquetteImage σ p).face ∩ (sublattice L m j : Set (FourTorus L m))).1
  rw [hc.2.2.2.2.2.1 p] at h₁
  obtain ⟨q, hq, e⟩ := h₁
  have hql : q ∈ (sublattice L m j : Set (FourTorus L m)) := by
    rw [← hl]
    exact ⟨c, c.2, by rw [← e]; simp⟩
  have h₂ : q ∈ (fun x : Site L m j => (x : FourTorus L m)) '' p.vertices := by
    rw [image_coe_vertices hL hj]
    exact ⟨hq, hql⟩
  obtain ⟨d, hd, rfl⟩ := h₂
  exact ⟨d, hp d hd, e⟩
theorem image_plaquettesInside (hL : 0 < L) (hj : -(m : ℤ) ≤ j)
    (hc : MapsCellsAndCubes σ j) (hs : MapsCellsAndCubes σ.symm j)
    (X : Set (FourTorus L m)) :
    plaquetteImage σ '' (plaquettesInside X : Set (Plaquette L m j)) =
      plaquettesInside (σ '' X) := by
  apply Subset.antisymm
  · rintro _ ⟨p, hp, rfl⟩
    exact plaquetteImage_mem_plaquettesInside hL hj hc hs.1 X hp
  · intro p' hp'
    refine ⟨plaquetteImage σ.symm p', ?_, eq_of_barycenter_eq hL hj ?_⟩
    · have h := plaquetteImage_mem_plaquettesInside hL hj hs (by simpa using hc.1) (σ '' X) hp'
      rwa [Equiv.symm_image_image] at h
    · rw [hc.2.2.2.2.2.2.2.1, hs.2.2.2.2.2.2.2.1]
      simp
theorem image_bondDoubleBlock (hb : IsometryInvariance.MapsBlocks σ j)
    (hc : MapsCellsAndCubes σ j) (c : Bond L m j) :
    σ '' bondDoubleBlock c = bondDoubleBlock (bondImage σ c) := by apply _root_.YangMills.Construction.PeriodicLattice.IsometryInvariance.image_bondDoubleBlock <;> assumption
end Objects
theorem statement_holds (hG : LatticeIsometryGroupActionStatement)
    (hB : IsometryInvariance.InvariantUnderIsometries) : Statement := by
  intro L m hLs hm i hi σ hσ j j' hij hj hj'
  subst hj'
  have hL : 1 < L := by
    have := hLs.2
    omega
  have hL0 : 0 < L := by omega
  obtain ⟨⟨⟨H, hH⟩, -⟩, -, -, -, hall⟩ := hG L m i hLs hm hi
  have hτ : σ.symm ∈ latticeIsometries L m i := by
    have h₁ : σ ∈ H := by
      rw [← SetLike.mem_coe, hH]
      exact hσ
    have h₂ : σ⁻¹ ∈ H := H.inv_mem h₁
    rw [← hH]
    exact h₂
  have hij' : i ≤ j + 1 := by omega
  have hm' : -(m : ℤ) ≤ j + 1 := by omega
  have hcj := (hall σ hσ j hij).1
  have hc := (hall σ hσ (j + 1) hij').1
  have hs := (hall σ.symm hτ (j + 1) hij').1
  obtain ⟨hblocks, -, hfam⟩ := (hB L m hLs hm i hi σ hσ).1 j hij
  obtain ⟨-, hpaths, -⟩ := (hB L m hLs hm i hi σ hσ).1 (j + 1) hij'
  obtain ⟨r, v, -, hr⟩ := hσ
  have hI := bondImage_injective hc hs
  refine ⟨fun y => ⟨mapsBlockSites hc hs hblocks y, fun x hx => ?_⟩, fun c =>
    ⟨fun x => mapsCrossing hL hm hj hr hcj hc hpaths c x,
      mapsTransportPath hL hm hj hcj hc hpaths c, ?_⟩⟩
  · exact mapsContourIndices (hfam y x hx) (orderedContour_injective hL0 hm' y x)
      (orderedContour_injective hL0 hm' _ _) hI
  · unfold MapsDoubleBlockPlaquettes doubleBlockPlaquettes
    rw [image_plaquettesInside hL0 hm' hc hs, image_bondDoubleBlock hblocks hcj]
end YangMills.Construction.PeriodicLattice.IsometryImages
