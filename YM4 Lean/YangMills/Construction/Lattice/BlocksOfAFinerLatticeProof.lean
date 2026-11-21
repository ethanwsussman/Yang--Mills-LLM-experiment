import YangMills.Construction.Lattice.CoarseBlockCentres
import YangMills.Construction.Lattice.LiftsClassesAndSitesInLevelUnits
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.PeriodicLattice.CoarseBlocks
variable {L m K : ℕ}
def LevelFacts (L m K j k : ℕ) : Prop :=
  LevelSideFacts L m K j k ∧ LiftCosetFacts L m K j ∧ SitesAndBondsRescaled L m K j k ∧
    SupNormAndCubesRescaled L m K j k ∧ HalfWidthProperties L (k - j)
def castVec (r : Fin 4 → ℤ) : Fin 4 → ℝ := fun μ => (r μ : ℝ)
theorem supNormVec_le_iff {v : Fin 4 → ℝ} {c : ℝ} : supNormVec v ≤ c ↔ ∀ μ, |v μ| ≤ c := by
  unfold supNormVec
  rw [Finset.sup'_le_iff]
  simp
theorem exists_centered_residue {a : ℤ} (ha : 0 ≤ a) (t : ℤ) :
    ∃ r, |r| ≤ a ∧ (2 * a + 1) ∣ t - r := by
  have hP : (0 : ℤ) < 2 * a + 1 := by omega
  refine ⟨(t + a) % (2 * a + 1) - a, ?_, ?_⟩
  · have h0 := Int.emod_nonneg (t + a) hP.ne'
    have h1 := Int.emod_lt_of_pos (t + a) hP
    rw [abs_le]
    constructor <;> omega
  · have h := Int.emod_add_mul_ediv (t + a) (2 * a + 1)
    refine ⟨(t + a) / (2 * a + 1), ?_⟩
    linarith
theorem centered_residue_unique {a r r' : ℤ} (hr : |r| ≤ a) (hr' : |r'| ≤ a)
    (h : (2 * a + 1) ∣ r - r') : r = r' := by
  have hz : r - r' = 0 := by
    refine Int.eq_zero_of_abs_lt_dvd h ?_
    rw [abs_le] at hr hr'
    rw [abs_lt]
    constructor <;> omega
  omega
section Lifts
variable {j k : ℕ}
theorem sub_mem_of_isLevelLift (hF : LevelFacts L m K j k) {x : FourTorus L m} {w w' : Fin 4 → ℝ}
    (h : IsLevelLift L m K j x w) (h' : IsLevelLift L m K j x w') :
    w' - w ∈ scaledIntLattice (sideInLevelUnits L m K j) := by
  obtain ⟨w₀, h₀⟩ := hF.2.1.1 x
  have a : w ∈ cosetMod (sideInLevelUnits L m K j) w₀ := by rw [← h₀]; exact h
  have a' : w' ∈ cosetMod (sideInLevelUnits L m K j) w₀ := by rw [← h₀]; exact h'
  obtain ⟨z, hz⟩ := a
  obtain ⟨z', hz'⟩ := a'
  refine ⟨z' - z, fun μ => ?_⟩
  have e := hz μ
  have e' := hz' μ
  simp only [Pi.sub_apply, Int.cast_sub] at *
  rw [mul_sub, ← e, ← e']
  ring
theorem isLevelLift_of_sub_mem (hF : LevelFacts L m K j k) {x : FourTorus L m} {w w' : Fin 4 → ℝ}
    (h : IsLevelLift L m K j x w) (hd : w' - w ∈ scaledIntLattice (sideInLevelUnits L m K j)) :
    IsLevelLift L m K j x w' := by
  obtain ⟨w₀, h₀⟩ := hF.2.1.1 x
  have a : w ∈ cosetMod (sideInLevelUnits L m K j) w₀ := by rw [← h₀]; exact h
  obtain ⟨z, hz⟩ := a
  obtain ⟨z', hz'⟩ := hd
  have : w' ∈ cosetMod (sideInLevelUnits L m K j) w₀ := by
    refine ⟨z' + z, fun μ => ?_⟩
    have e := hz μ
    have e' := hz' μ
    simp only [Pi.sub_apply, Pi.add_apply, Int.cast_add] at *
    rw [mul_add, ← e, ← e']
    ring
  rw [← h₀] at this
  exact this
theorem exists_isLevelLift (hF : LevelFacts L m K j k) (x : FourTorus L m) :
    ∃ w, IsLevelLift L m K j x w := by
  obtain ⟨w₀, h₀⟩ := hF.2.1.1 x
  refine ⟨w₀, ?_⟩
  have : w₀ ∈ cosetMod (sideInLevelUnits L m K j) w₀ :=
    ⟨0, fun μ => by simp⟩
  rw [← h₀] at this
  exact this
theorem eq_of_isLevelLift (hF : LevelFacts L m K j k) {x x' : FourTorus L m} {w : Fin 4 → ℝ}
    (h : IsLevelLift L m K j x w) (h' : IsLevelLift L m K j x' w) : x = x' := by
  have a := (hF.2.1.2.2.1 w x).1 h
  have a' := (hF.2.1.2.2.1 w x').1 h'
  rw [a, a']
theorem isLevelLift_shiftBy (hF : LevelFacts L m K j k) {x : FourTorus L m} {w : Fin 4 → ℝ}
    (h : IsLevelLift L m K j x w) (r : Fin 4 → ℝ) :
    IsLevelLift L m K j (shiftBy L m K j x r) (w + r) :=
  (hF.2.1.2.2.1 _ _).2 (hF.2.1.2.2.2.2 x r w h)
theorem eq_shiftBy_of_isLevelLift (hF : LevelFacts L m K j k) {x x' : FourTorus L m}
    {w : Fin 4 → ℝ} {r : Fin 4 → ℝ}
    (h : IsLevelLift L m K j x w) (h' : IsLevelLift L m K j x' (w + r)) :
    x' = shiftBy L m K j x r :=
  eq_of_isLevelLift hF h' (isLevelLift_shiftBy hF h r)
theorem isLevelLift_sub (hF : LevelFacts L m K j k) {x x' : FourTorus L m} {w w' : Fin 4 → ℝ}
    (h : IsLevelLift L m K j x w) (h' : IsLevelLift L m K j x' w') :
    IsLevelLift L m K j (x - x') (w - w') :=
  (hF.2.1.2.2.2.1 x x' w w' h h').2
theorem exists_int_lift (hF : LevelFacts L m K j k) (x : SiteAtLevel L m K j) :
    ∃ z : Fin 4 → ℤ, IsLevelLift L m K j (x : FourTorus L m) (castVec z) := by
  have hx : (x : FourTorus L m) ∈ torusClassOf L m K j '' scaledIntLattice 1 := by
    rw [← hF.2.2.1.1]
    exact x.2
  obtain ⟨w, ⟨z, hz⟩, hw⟩ := hx
  refine ⟨z, ?_⟩
  have e : castVec z = w := by
    funext μ
    rw [hz μ]
    simp [castVec]
  rw [e]
  exact (hF.2.1.2.2.1 _ _).2 hw.symm
theorem mem_sublattice_of_int_lift (hF : LevelFacts L m K j k) {x : FourTorus L m}
    {z : Fin 4 → ℤ} (h : IsLevelLift L m K j x (castVec z)) :
    x ∈ sublattice L m (levelDepth K j) := by
  have hx : x ∈ torusClassOf L m K j '' scaledIntLattice 1 :=
    ⟨castVec z, ⟨z, fun μ => by simp [castVec]⟩, ((hF.2.1.2.2.1 _ _).1 h).symm⟩
  rw [← hF.2.2.1.1] at hx
  exact hx
theorem coarse_lift_mem (hF : LevelFacts L m K j k) (y : SiteAtLevel L m K k) {w : Fin 4 → ℝ}
    (h : IsLevelLift L m K j (y : FourTorus L m) w) :
    ∃ u : Fin 4 → ℤ, ∀ μ, w μ = (L : ℝ) ^ (k - j) * (u μ : ℝ) :=
  hF.2.2.1.2.2.1 y w h
theorem exists_coarse_site_of_lift (hF : LevelFacts L m K j k) {u : Fin 4 → ℤ} {w : Fin 4 → ℝ}
    (hw : ∀ μ, w μ = (L : ℝ) ^ (k - j) * (u μ : ℝ)) :
    ∃ y : SiteAtLevel L m K k, IsLevelLift L m K j (y : FourTorus L m) w := by
  have hx : torusClassOf L m K j w ∈
      torusClassOf L m K j '' scaledIntLattice ((L : ℝ) ^ (k - j)) :=
    ⟨w, ⟨u, hw⟩, rfl⟩
  rw [← hF.2.2.1.2.1] at hx
  exact ⟨⟨_, hx⟩, (hF.2.1.2.2.1 _ _).2 rfl⟩
theorem side_eq_pow_mul (hF : LevelFacts L m K j k) :
    ∃ a : ℤ, 6 ≤ a ∧ sideInLevelUnits L m K j = (L : ℝ) ^ (k - j) * (a : ℝ) := by
  obtain ⟨-, ⟨a, ha⟩, -, e, -, h2, h6⟩ := hF.1
  refine ⟨a, ?_, by rw [e, ha]⟩
  have : (6 : ℝ) ≤ (a : ℝ) := by rw [← ha]; linarith
  exact_mod_cast this
theorem halfWidth_int (hF : LevelFacts L m K j k) :
    ∃ a : ℤ, 0 ≤ a ∧ halfWidth L (k - j) = (a : ℝ) ∧ 2 * a + 1 = (L : ℤ) ^ (k - j) := by
  obtain ⟨⟨a, ha⟩, h0, h1, -⟩ := hF.2.2.2.2
  refine ⟨a, ?_, ha, ?_⟩
  · rw [ha] at h0
    exact_mod_cast h0
  · rw [ha] at h1
    exact_mod_cast h1
theorem supNormVec_int_le_iff {a : ℤ} (ha : halfWidth L (k - j) = (a : ℝ)) {r : Fin 4 → ℤ} :
    supNormVec (fun μ => (r μ : ℝ)) ≤ halfWidth L (k - j) ↔ ∀ μ, |r μ| ≤ a := by
  rw [supNormVec_le_iff, ha]
  refine forall_congr' fun μ => ?_
  rw [← Int.cast_abs]
  exact_mod_cast Iff.rfl
theorem isLevelLift_of_displacement (hF : LevelFacts L m K j k) {x : SiteAtLevel L m K j}
    {y : SiteAtLevel L m K k} {r : Fin 4 → ℤ} (h : IsBlockDisplacement j k x y r)
    {w : Fin 4 → ℝ} (hw : IsLevelLift L m K j (y : FourTorus L m) w) :
    IsLevelLift L m K j (x : FourTorus L m) (w + castVec r) := by
  have := isLevelLift_shiftBy hF hw (castVec r)
  have e : shiftBy L m K j (y : FourTorus L m) (castVec r) = (x : FourTorus L m) := h.2.symm
  rwa [e] at this
theorem displacement_unique (hF : LevelFacts L m K j k) {x : SiteAtLevel L m K j}
    {y y' : SiteAtLevel L m K k} {r r' : Fin 4 → ℤ} (h : IsBlockDisplacement j k x y r)
    (h' : IsBlockDisplacement j k x y' r') : y = y' ∧ r = r' := by
  obtain ⟨a, -, ha, hP⟩ := halfWidth_int hF
  obtain ⟨c, -, hc⟩ := side_eq_pow_mul hF
  have hb := (supNormVec_int_le_iff ha).1 h.1
  have hb' := (supNormVec_int_le_iff ha).1 h'.1
  obtain ⟨w, hw⟩ := exists_isLevelLift hF (y : FourTorus L m)
  obtain ⟨w', hw'⟩ := exists_isLevelLift hF (y' : FourTorus L m)
  obtain ⟨u, hu⟩ := coarse_lift_mem hF y hw
  obtain ⟨u', hu'⟩ := coarse_lift_mem hF y' hw'
  have l := isLevelLift_of_displacement hF h hw
  have l' := isLevelLift_of_displacement hF h' hw'
  obtain ⟨z, hz⟩ := sub_mem_of_isLevelLift hF l l'
  have hrr : r = r' := by
    funext μ
    refine centered_residue_unique (hb μ) (hb' μ) ?_
    rw [hP]
    refine ⟨u' μ - u μ - c * z μ, ?_⟩
    have e := hz μ
    simp only [Pi.sub_apply, Pi.add_apply, castVec, hu μ, hu' μ, hc] at e
    have : ((r μ - r' μ : ℤ) : ℝ) =
        (((L : ℤ) ^ (k - j) * (u' μ - u μ - c * z μ) : ℤ) : ℝ) := by
      push_cast
      linarith
    exact_mod_cast this
  subst hrr
  refine ⟨?_, rfl⟩
  have hd : w' - w ∈ scaledIntLattice (sideInLevelUnits L m K j) := by
    refine ⟨z, fun μ => ?_⟩
    have e := hz μ
    simp only [Pi.sub_apply, Pi.add_apply] at e ⊢
    linarith
  exact Subtype.ext (eq_of_isLevelLift hF (isLevelLift_of_sub_mem hF hw hd) hw')
theorem exists_displacement (hF : LevelFacts L m K j k) (x : SiteAtLevel L m K j) :
    ∃ (y : SiteAtLevel L m K k) (r : Fin 4 → ℤ), IsBlockDisplacement j k x y r := by
  obtain ⟨a, ha0, ha, hP⟩ := halfWidth_int hF
  obtain ⟨z, hz⟩ := exists_int_lift hF x
  choose r hr hd using fun μ => exists_centered_residue ha0 (z μ)
  rw [hP] at hd
  choose u hu using hd
  have hw : ∀ μ, (castVec z - castVec r) μ = (L : ℝ) ^ (k - j) * (u μ : ℝ) := by
    intro μ
    have e : ((z μ - r μ : ℤ) : ℝ) = (((L : ℤ) ^ (k - j) * u μ : ℤ) : ℝ) := by rw [hu μ]
    push_cast at e
    simpa [castVec] using e
  obtain ⟨y, hy⟩ := exists_coarse_site_of_lift hF hw
  refine ⟨y, r, (supNormVec_int_le_iff ha).2 hr, ?_⟩
  refine eq_shiftBy_of_isLevelLift hF hy ?_
  have e : castVec z - castVec r + castVec r = castVec z := by abel
  change IsLevelLift L m K j (x : FourTorus L m) (castVec z - castVec r + castVec r)
  rw [e]
  exact hz
theorem coarseCentre_spec (hF : LevelFacts L m K j k) (x : SiteAtLevel L m K j) :
    ∃ r, IsBlockDisplacement j k x (coarseCentre j k x : SiteAtLevel L m K k) r :=
  Classical.epsilon_spec (p := fun y : SiteAtLevel L m K k => ∃ r, IsBlockDisplacement j k x y r)
    (exists_displacement hF x)
theorem coarseCentre_eq (hF : LevelFacts L m K j k) {x : SiteAtLevel L m K j}
    {y : SiteAtLevel L m K k} {r : Fin 4 → ℤ} (h : IsBlockDisplacement j k x y r) :
    coarseCentre j k x = y := by
  obtain ⟨r', hr'⟩ := coarseCentre_spec hF x
  exact (displacement_unique hF hr' h).1
theorem mem_cubeAtLevel_iff (hF : LevelFacts L m K j k) (y : SiteAtLevel L m K k)
    (z : FourTorus L m) :
    z ∈ cubeAtLevel y ↔
      toLevelUnits L K j (TorusMetric.torusSupNorm (z - (y : FourTorus L m))) ≤
        (L : ℝ) ^ (k - j) / 2 := by
  have e : cubeAtLevel y = _ := hF.2.2.2.1.2 y
  rw [e]
  rfl
theorem self_mem_cubeAtLevel (hF : LevelFacts L m K j k) (y : SiteAtLevel L m K k) :
    (y : FourTorus L m) ∈ cubeAtLevel y := by
  rw [mem_cubeAtLevel_iff hF]
  obtain ⟨w, hw⟩ := exists_isLevelLift hF (y : FourTorus L m)
  have l := isLevelLift_sub hF hw hw
  have := (hF.2.2.2.1.1 ((y : FourTorus L m) - y)).2 ⟨w - w, l, rfl⟩
  refine this.trans ?_
  rw [supNormVec_le_iff]
  intro μ
  simp
  positivity
theorem mem_cubeAtLevel_iff_eq_coarseCentre (hF : LevelFacts L m K j k)
    (x : SiteAtLevel L m K j) (y' : SiteAtLevel L m K k) :
    (x : FourTorus L m) ∈ cubeAtLevel y' ↔ y' = coarseCentre j k x := by
  obtain ⟨a, ha0, ha, hP⟩ := halfWidth_int hF
  obtain ⟨c, -, hc⟩ := side_eq_pow_mul hF
  obtain ⟨r, hr⟩ := coarseCentre_spec hF x
  have hb := (supNormVec_int_le_iff ha).1 hr.1
  have hPR : (L : ℝ) ^ (k - j) = 2 * (a : ℝ) + 1 := by
    have : (((L : ℤ) ^ (k - j) : ℤ) : ℝ) = ((2 * a + 1 : ℤ) : ℝ) := by rw [hP]
    push_cast at this
    exact this
  obtain ⟨w, hw⟩ :=
    exists_isLevelLift hF ((coarseCentre j k x : SiteAtLevel L m K k) : FourTorus L m)
  have l := isLevelLift_of_displacement hF hr hw
  constructor
  · intro hx
    rw [mem_cubeAtLevel_iff hF] at hx
    obtain ⟨⟨v, hv, hvn⟩, -⟩ := hF.2.2.2.1.1 ((x : FourTorus L m) - (y' : FourTorus L m))
    obtain ⟨w', hw'⟩ := exists_isLevelLift hF (y' : FourTorus L m)
    have l2 := isLevelLift_sub hF l hw'
    obtain ⟨z, hz⟩ := sub_mem_of_isLevelLift hF hv l2
    obtain ⟨u, hu⟩ := coarse_lift_mem hF _ hw
    obtain ⟨u', hu'⟩ := coarse_lift_mem hF _ hw'
    have hvb : ∀ μ, |v μ| ≤ (L : ℝ) ^ (k - j) / 2 := by
      rw [← supNormVec_le_iff, hvn]
      exact hx
    have hvr : ∀ μ, v μ = (r μ : ℝ) := by
      intro μ
      have e := hz μ
      simp only [Pi.sub_apply, Pi.add_apply, castVec, hu μ, hu' μ, hc] at e
      set t : ℤ := c * z μ - u μ + u' μ with ht
      have et : v μ - (r μ : ℝ) = (L : ℝ) ^ (k - j) * (-(t : ℝ)) := by
        rw [ht]
        push_cast
        linarith
      have hrμ : |(r μ : ℝ)| ≤ (a : ℝ) := by
        rw [← Int.cast_abs]
        exact_mod_cast hb μ
      have hvμ := hvb μ
      have hlt : |v μ - (r μ : ℝ)| < (L : ℝ) ^ (k - j) := by
        have := abs_sub (v μ) (r μ : ℝ)
        rw [hPR] at hvμ ⊢
        linarith
      have hPpos : (0 : ℝ) < (L : ℝ) ^ (k - j) := by
        rw [hPR]
        have : (0 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha0
        linarith
      rw [et, abs_mul, abs_of_pos hPpos] at hlt
      have h1 : |(-(t : ℝ))| < 1 := by
        by_contra hcon
        have hcon' := not_lt.mp hcon
        nlinarith
      have ht0 : t = 0 := by
        have : |t| < 1 := by
          rw [abs_neg, ← Int.cast_abs] at h1
          exact_mod_cast h1
        exact Int.abs_lt_one_iff.mp this
      rw [ht0] at et
      simp at et
      linarith
    have hd : w' - w ∈ scaledIntLattice (sideInLevelUnits L m K j) := by
      refine ⟨-z, fun μ => ?_⟩
      have e := hz μ
      simp only [Pi.sub_apply, Pi.add_apply, Pi.neg_apply, castVec, hvr μ, Int.cast_neg] at e ⊢
      linarith
    exact Subtype.ext (eq_of_isLevelLift hF hw' (isLevelLift_of_sub_mem hF hw hd))
  · rintro rfl
    rw [mem_cubeAtLevel_iff hF]
    have l2 := isLevelLift_sub hF l hw
    have hmin := (hF.2.2.2.1.1 ((x : FourTorus L m) -
      ((coarseCentre j k x : SiteAtLevel L m K k) : FourTorus L m))).2 ⟨_, l2, rfl⟩
    refine hmin.trans ?_
    rw [supNormVec_le_iff]
    intro μ
    simp only [Pi.sub_apply, Pi.add_apply, castVec, add_sub_cancel_left]
    have hrμ : |(r μ : ℝ)| ≤ (a : ℝ) := by
      rw [← Int.cast_abs]
      exact_mod_cast hb μ
    rw [hPR]
    linarith
theorem levelDepth_add (hjk : j ≤ k) : levelDepth K k + ((k - j : ℕ) : ℤ) = levelDepth K j := by
  simp only [levelDepth]
  omega
theorem mem_blockAtLevel_iff (hF : LevelFacts L m K j k) (hjk : j ≤ k) (y : SiteAtLevel L m K k)
    (z : FourTorus L m) :
    z ∈ blockAtLevel j y ↔
      ∃ x : SiteAtLevel L m K j, (x : FourTorus L m) = z ∧ coarseCentre j k x = y := by
  constructor
  · rintro ⟨hc, hl⟩
    have hl' : z ∈ sublattice L m (levelDepth K j) := by
      have : z ∈ (sublattice L m (levelDepth K k + ((k - j : ℕ) : ℤ)) : Set (FourTorus L m)) := hl
      rw [levelDepth_add hjk] at this
      exact this
    exact ⟨⟨z, hl'⟩, rfl, ((mem_cubeAtLevel_iff_eq_coarseCentre hF ⟨z, hl'⟩ y).1 hc).symm⟩
  · rintro ⟨x, rfl, hx⟩
    refine ⟨(mem_cubeAtLevel_iff_eq_coarseCentre hF x y).2 hx.symm, ?_⟩
    rw [levelDepth_add hjk]
    exact x.2
theorem blockAtLevel_eq_shifts (hF : LevelFacts L m K j k) (hjk : j ≤ k)
    (y : SiteAtLevel L m K k) :
    blockAtLevel j y =
      {z | ∃ r : Fin 4 → ℤ, supNormVec (fun μ => (r μ : ℝ)) ≤ halfWidth L (k - j) ∧
        z = shiftBy L m K j y fun μ => (r μ : ℝ)} := by
  ext z
  rw [mem_blockAtLevel_iff hF hjk]
  constructor
  · rintro ⟨x, rfl, rfl⟩
    obtain ⟨r, hr⟩ := coarseCentre_spec hF x
    exact ⟨r, hr⟩
  · rintro ⟨r, hn, rfl⟩
    obtain ⟨w, hw⟩ := exists_isLevelLift hF (y : FourTorus L m)
    obtain ⟨u, hu⟩ := coarse_lift_mem hF y hw
    have l := isLevelLift_shiftBy hF hw (castVec r)
    have e : w + castVec r = castVec (fun μ => (L : ℤ) ^ (k - j) * u μ + r μ) := by
      funext μ
      simp [castVec, hu μ]
    rw [e] at l
    have hmem := mem_sublattice_of_int_lift hF l
    have hx : IsBlockDisplacement j k ⟨_, hmem⟩ y r := ⟨hn, rfl⟩
    exact ⟨⟨_, hmem⟩, rfl, coarseCentre_eq hF hx⟩
end Lifts
theorem isLevelLift_of_coarser (hL : L ≠ 0) {j i : ℕ} (hji : j ≤ i) {x : FourTorus L m}
    {w : Fin 4 → ℝ} (h : IsLevelLift L m K i x w) :
    IsLevelLift L m K j x (fun μ => (L : ℝ) ^ (i - j) * w μ) := by
  obtain ⟨v, hv, hw⟩ := h
  refine ⟨v, hv, fun μ => ?_⟩
  have hL' : (L : ℝ) ≠ 0 := by exact_mod_cast hL
  change (L : ℝ) ^ (i - j) * w μ = _
  rw [hw μ]
  simp only [toLevelUnits]
  rw [← mul_assoc, ← zpow_natCast, ← zpow_add₀ hL']
  congr 2
  simp only [levelDepth]
  omega
theorem coarseCentre_coarseCentre (hL : L ≠ 0) {j i k : ℕ} (hji : j ≤ i) (hik : i ≤ k)
    (hji' : LevelFacts L m K j i) (hik' : LevelFacts L m K i k) (hjk' : LevelFacts L m K j k)
    (x : SiteAtLevel L m K j) :
    coarseCentre i k (coarseCentre j i x : SiteAtLevel L m K i) =
      (coarseCentre j k x : SiteAtLevel L m K k) := by
  set y' : SiteAtLevel L m K i := coarseCentre j i x with hy'
  set y : SiteAtLevel L m K k := coarseCentre i k y' with hy
  obtain ⟨r₁, hr₁⟩ := coarseCentre_spec hji' x
  obtain ⟨r₂, hr₂⟩ := coarseCentre_spec hik' y'
  obtain ⟨a₁, h0₁, ha₁, hP₁⟩ := halfWidth_int hji'
  obtain ⟨a₂, -, ha₂, hP₂⟩ := halfWidth_int hik'
  obtain ⟨a, -, ha, hP⟩ := halfWidth_int hjk'
  have hb₁ := (supNormVec_int_le_iff ha₁).1 hr₁.1
  have hb₂ := (supNormVec_int_le_iff ha₂).1 hr₂.1
  obtain ⟨w, hw⟩ := exists_isLevelLift hik' (y : FourTorus L m)
  have l₂ := isLevelLift_of_displacement hik' hr₂ hw
  have hyl := isLevelLift_of_coarser hL hji hw
  have hyl' := isLevelLift_of_coarser hL hji l₂
  have hxl := isLevelLift_of_displacement hji' hr₁ hyl'
  have hPP : (L : ℤ) ^ (k - j) = (L : ℤ) ^ (i - j) * (L : ℤ) ^ (k - i) := by
    rw [← pow_add]
    congr 1
    omega
  set Q : ℤ := (L : ℤ) ^ (i - j) with hQ
  have hQpos : 0 ≤ Q := by omega
  have hoff : IsBlockDisplacement j k x y (fun μ => Q * r₂ μ + r₁ μ) := by
    refine ⟨(supNormVec_int_le_iff ha).2 fun μ => ?_, ?_⟩
    · have t₂ := mul_le_mul_of_nonneg_left (hb₂ μ) hQpos
      have t₃ : |Q * r₂ μ + r₁ μ| ≤ |Q * r₂ μ| + |r₁ μ| := abs_add_le _ _
      rw [abs_mul, abs_of_nonneg hQpos] at t₃
      have t₁ := hb₁ μ
      rw [hPP, ← hP₂] at hP
      have ea : a = Q * a₂ + a₁ := by linarith
      rw [ea]
      linarith
    · refine eq_shiftBy_of_isLevelLift hjk' hyl ?_
      have e : (fun μ => (L : ℝ) ^ (i - j) * (w + castVec r₂) μ) + castVec r₁ =
          (fun μ => (L : ℝ) ^ (i - j) * w μ) + fun μ => ((Q * r₂ μ + r₁ μ : ℤ) : ℝ) := by
        funext μ
        simp [castVec, hQ]
        ring
      rw [← e]
      exact hxl
  exact (coarseCentre_eq hjk' hoff).symm
section Bonds
variable {j k : ℕ}
theorem not_mem_scaledIntLattice {N a : ℝ} (ha : 0 < a) (hN : 6 * a ≤ N) (μ ν : Fin 4) :
    a • coordVec ν + a • coordVec μ ∉ scaledIntLattice N := by
  rintro ⟨z, hz⟩
  have e := hz μ
  have hv : 0 < (a • coordVec ν + a • coordVec μ) μ ∧
      (a • coordVec ν + a • coordVec μ) μ ≤ 2 * a := by
    by_cases h : μ = ν
    · subst h
      simp only [coordVec, Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul]
      constructor <;> linarith
    · simp only [coordVec, Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul,
        Pi.single_eq_of_ne h]
      constructor <;> linarith
  rw [e] at hv
  have z1 : (0 : ℝ) < (z μ : ℝ) := by
    by_contra hc
    have := not_lt.mp hc
    nlinarith [hv.1]
  have z2 : ((z μ : ℝ)) < 1 := by
    by_contra hc
    have := not_lt.mp hc
    nlinarith [hv.2]
  have i1 : 0 < z μ := by exact_mod_cast z1
  have i2 : z μ < 1 := by exact_mod_cast z2
  omega
theorem shiftBy_neg_ne (hF : LevelFacts L m K j k) (x : FourTorus L m) {a : ℝ} (ha : 0 < a)
    (hN : 6 * a ≤ sideInLevelUnits L m K j) (μ ν : Fin 4) :
    shiftBy L m K j x ((-a) • coordVec μ) ≠ shiftBy L m K j x (a • coordVec ν) := by
  intro e
  obtain ⟨w, hw⟩ := exists_isLevelLift hF x
  have l₁ := isLevelLift_shiftBy hF hw ((-a) • coordVec μ)
  have l₂ := isLevelLift_shiftBy hF hw (a • coordVec ν)
  rw [e] at l₁
  have hd := sub_mem_of_isLevelLift hF l₁ l₂
  have e' : w + a • coordVec ν - (w + (-a) • coordVec μ) =
      a • coordVec ν + a • coordVec μ := by
    funext ρ
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [e'] at hd
  exact not_mem_scaledIntLattice ha hN μ ν hd
theorem bond_coarse (hF : LevelFacts L m K j k) (hF₀ : LevelFacts L m K j j) (hjk : j ≤ k)
    (b : BondAtLevel L m K j) (σ : ℝ) (μ : Fin 4) (hσ : σ = 1 ∨ σ = -1)
    (hb : (b.target : FourTorus L m) = shiftBy L m K j b.source (σ • coordVec μ)) :
    (coarseCentre j k b.target : SiteAtLevel L m K k) = coarseCentre j k b.source ∨
      (((coarseCentre j k b.target : SiteAtLevel L m K k) : FourTorus L m) =
          shiftBy L m K j (coarseCentre j k b.source : SiteAtLevel L m K k)
            ((σ * (L : ℝ) ^ (k - j)) • coordVec μ) ∧
        (coarseCentre j k b.target : SiteAtLevel L m K k) ≠ coarseCentre j k b.source ∧
        ∃ c : BondAtLevel L m K k, c.source = coarseCentre j k b.source ∧
          c.target = coarseCentre j k b.target ∧
          (c.IsPositivelyOriented ↔ b.IsPositivelyOriented) ∧
          ∀ c' : BondAtLevel L m K k, (b.source : FourTorus L m) ∈ blockAtLevel j c'.source →
            (b.target : FourTorus L m) ∈ blockAtLevel j c'.target → c' = c) := by
  obtain ⟨s, hs, rfl⟩ : ∃ s : ℤ, (s = 1 ∨ s = -1) ∧ σ = (s : ℝ) := by
    rcases hσ with rfl | rfl
    · exact ⟨1, Or.inl rfl, by simp⟩
    · exact ⟨-1, Or.inr rfl, by simp⟩
  obtain ⟨a, ha0, ha, hP⟩ := halfWidth_int hF
  obtain ⟨c₀, hc₀, hside⟩ := side_eq_pow_mul hF
  obtain ⟨r, hr⟩ := coarseCentre_spec hF b.source
  have hbd := (supNormVec_int_le_iff ha).1 hr.1
  obtain ⟨w, hw⟩ := exists_isLevelLift hF
    ((coarseCentre j k b.source : SiteAtLevel L m K k) : FourTorus L m)
  obtain ⟨u, hu⟩ := coarse_lift_mem hF _ hw
  have lt := isLevelLift_of_displacement hF hr hw
  have lh : IsLevelLift L m K j (b.target : FourTorus L m)
      (w + castVec r + (s : ℝ) • coordVec μ) := by
    rw [hb]
    exact isLevelLift_shiftBy hF lt _
  set r₁ : Fin 4 → ℤ := r + Pi.single μ s with hr₁
  have h1 : r₁ μ = r μ + s := by simp [hr₁]
  have hne : ∀ ν, ν ≠ μ → r₁ ν = r ν := by
    intro ν h
    simp [hr₁, Pi.single_eq_of_ne h]
  by_cases hc : |r₁ μ| ≤ a
  · left
    have hoff : IsBlockDisplacement j k b.target
        (coarseCentre j k b.source : SiteAtLevel L m K k) r₁ := by
      refine ⟨(supNormVec_int_le_iff ha).2 fun ν => ?_, eq_shiftBy_of_isLevelLift hF hw ?_⟩
      · by_cases h : ν = μ
        · rw [h]
          exact hc
        · rw [hne ν h]
          exact hbd ν
      · have e : w + (fun ν => (r₁ ν : ℝ)) = w + castVec r + (s : ℝ) • coordVec μ := by
          funext ν
          by_cases h : ν = μ
          · subst h
            simp [castVec, h1, coordVec, add_assoc]
          · simp [castVec, hne ν h, coordVec, Pi.single_eq_of_ne h]
        rw [e]
        exact lh
    exact coarseCentre_eq hF hoff
  · right
    have hrμ : r μ = s * a := by
      rw [h1, abs_le, not_and_or, not_le, not_le] at hc
      have := abs_le.mp (hbd μ)
      rcases hs with rfl | rfl <;> omega
    set r₂ : Fin 4 → ℤ := r₁ - Pi.single μ (s * (L : ℤ) ^ (k - j)) with hr₂
    have h2 : r₂ μ = r μ + s - s * (2 * a + 1) := by simp [hr₂, h1, hP]
    have hne₂ : ∀ ν, ν ≠ μ → r₂ ν = r ν := by
      intro ν h
      simp [hr₂, hne ν h, Pi.single_eq_of_ne h]
    set wN : Fin 4 → ℝ := w + ((s : ℝ) * (L : ℝ) ^ (k - j)) • coordVec μ with hwN
    set u₂ : Fin 4 → ℤ := u + Pi.single μ s with hu₂
    have hwc : ∀ ν, wN ν = (L : ℝ) ^ (k - j) * (u₂ ν : ℝ) := by
      intro ν
      by_cases h : ν = μ
      · subst h
        simp [hwN, hu₂, hu ν, coordVec]
        ring
      · simp [hwN, hu₂, hu ν, coordVec, Pi.single_eq_of_ne h]
    obtain ⟨y', hy'⟩ := exists_coarse_site_of_lift hF hwc
    have hoff : IsBlockDisplacement j k b.target y' r₂ := by
      refine ⟨(supNormVec_int_le_iff ha).2 fun ν => ?_, eq_shiftBy_of_isLevelLift hF hy' ?_⟩
      · by_cases h : ν = μ
        · rw [h, h2, hrμ, abs_le]
          rcases hs with rfl | rfl <;> constructor <;> omega
        · rw [hne₂ ν h]
          exact hbd ν
      · have e : wN + (fun ν => (r₂ ν : ℝ)) = w + castVec r + (s : ℝ) • coordVec μ := by
          funext ν
          by_cases h : ν = μ
          · subst h
            simp [hwN, castVec, hr₂, hr₁, coordVec]
            ring
          · simp [hwN, castVec, hne₂ ν h, coordVec, Pi.single_eq_of_ne h]
        rw [e]
        exact lh
    have hcent : (coarseCentre j k b.target : SiteAtLevel L m K k) = y' := coarseCentre_eq hF hoff
    have hPR : (L : ℝ) ^ (k - j) = 2 * (a : ℝ) + 1 := by
      have : (((L : ℤ) ^ (k - j) : ℤ) : ℝ) = ((2 * a + 1 : ℤ) : ℝ) := by rw [hP]
      push_cast at this
      exact this
    have ha0R : (0 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha0
    have hPpos : (0 : ℝ) < (L : ℝ) ^ (k - j) := by rw [hPR]; linarith
    have hP1 : (1 : ℝ) ≤ (L : ℝ) ^ (k - j) := by rw [hPR]; linarith
    have hc6 : (6 : ℝ) ≤ (c₀ : ℝ) := by exact_mod_cast hc₀
    have teq : (y' : FourTorus L m) = shiftBy L m K j
        (coarseCentre j k b.source : SiteAtLevel L m K k)
        (((s : ℝ) * (L : ℝ) ^ (k - j)) • coordVec μ) := eq_shiftBy_of_isLevelLift hF hw hy'
    rw [hcent]
    refine ⟨teq, ?_, ?_⟩
    · intro he
      rw [he] at hy'
      obtain ⟨z, hz⟩ := sub_mem_of_isLevelLift hF hw hy'
      have e := hz μ
      simp only [hwN, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, coordVec,
        Pi.single_eq_same, add_sub_cancel_left, mul_one, hside] at e
      have e' : (s : ℝ) = (c₀ : ℝ) * (z μ : ℝ) := by
        apply mul_left_cancel₀ hPpos.ne'
        linarith
      have e'' : s = c₀ * z μ := by exact_mod_cast e'
      have hd : c₀ ∣ 1 := by
        rcases hs with rfl | rfl
        · exact ⟨z μ, e''⟩
        · exact ⟨-z μ, by linarith⟩
      have := Int.le_of_dvd one_pos hd
      omega
    · obtain ⟨c, hct, hch⟩ := (hF.2.2.1.2.2.2.2.2.2.1 _ y').2
        ⟨(s : ℝ), μ, by rcases hs with rfl | rfl <;> simp, teq⟩
      refine ⟨c, hct, hch, ?_, fun c' h₁ h₂ => ?_⟩
      · have posC := hF.2.2.1.2.2.2.2.2.2.2 c
        have posB := hF₀.2.2.1.2.2.2.2.2.2.2 b
        simp only [Nat.sub_self, pow_zero] at posB
        rcases hs with rfl | rfl
        · refine iff_of_true (posC.2 ⟨μ, ?_⟩) (posB.2 ⟨μ, ?_⟩)
          · rw [hct, hch]
            simpa using teq
          · simpa using hb
        · refine iff_of_false ?_ ?_
          · rw [posC]
            rintro ⟨ν, hν⟩
            rw [hct, hch] at hν
            refine shiftBy_neg_ne hF
              ((coarseCentre j k b.source : SiteAtLevel L m K k) : FourTorus L m) hPpos ?_ μ ν ?_
            · rw [hside]
              nlinarith
            · rw [← hν, teq]
              simp
          · rw [posB]
            rintro ⟨ν, hν⟩
            refine shiftBy_neg_ne hF (b.source : FourTorus L m) one_pos (a := 1) ?_ μ ν ?_
            · rw [hside]
              nlinarith
            · rw [← hν, hb]
              simp
      · obtain ⟨x₁, e₁, e₂⟩ := (mem_blockAtLevel_iff hF hjk _ _).1 h₁
        obtain ⟨x₂, e₃, e₄⟩ := (mem_blockAtLevel_iff hF hjk _ _).1 h₂
        have t₁ : x₁ = b.source := Subtype.ext e₁
        have t₂ : x₂ = b.target := Subtype.ext e₃
        subst t₁ t₂
        refine Bond.ext ?_ ?_
        · rw [hct, e₂]
        · rw [hch, ← hcent, e₄]
end Bonds
theorem coarseCentreProperties_of_rescaled (h : RescaledLatticeStatement) :
    CoarseCentreProperties := by
  intro L m K hL hm hK j k hjk hkK
  have F : ∀ a b, a ≤ b → b ≤ K → LevelFacts L m K a b :=
    fun a b hab hb => h L m K hL hm hK a b hab hb
  have hF := F j k hjk hkK
  have hF₀ := F j j le_rfl (hjk.trans hkK)
  have hLne : L ≠ 0 := by
    have := hL.2
    omega
  refine ⟨fun x => ⟨?_, fun y' => mem_cubeAtLevel_iff_eq_coarseCentre hF x y'⟩,
    fun y => ⟨?_, blockAtLevel_eq_shifts hF hjk y⟩, fun x => ?_,
    fun i hji hik => ⟨fun x => ?_, fun y' => ?_⟩,
    fun b σ μ hσ hb => bond_coarse hF hF₀ hjk b σ μ hσ hb, fun X hX x hx => ?_⟩
  · obtain ⟨y, r, hyr⟩ := exists_displacement hF x
    refine ⟨(y, r), hyr, fun p hp => ?_⟩
    obtain ⟨e₁, e₂⟩ := displacement_unique hF hp hyr
    exact Prod.ext e₁ e₂
  · ext z
    exact mem_blockAtLevel_iff hF hjk y z
  · refine ⟨coarseCentre j k x, (mem_blockAtLevel_iff hF hjk _ _).2 ⟨x, rfl, rfl⟩,
      fun y' hy' => ?_⟩
    obtain ⟨x', e, e'⟩ := (mem_blockAtLevel_iff hF hjk _ _).1 hy'
    have t : x' = x := Subtype.ext e
    rw [← e', t]
  · exact coarseCentre_coarseCentre hLne hji hik (F j i hji (hik.trans hkK)) (F i k hik hkK) hF x
  · intro z hz
    obtain ⟨x, rfl, hx⟩ := (mem_blockAtLevel_iff (F j i hji (hik.trans hkK)) hji y' z).1 hz
    refine (mem_blockAtLevel_iff hF hjk _ _).2 ⟨x, rfl, ?_⟩
    rw [← coarseCentre_coarseCentre hLne hji hik (F j i hji (hik.trans hkK)) (F i k hik hkK) hF x,
      hx]
  · obtain ⟨C, hC, rfl⟩ := hX
    obtain ⟨Q, hQ, hxQ⟩ := hx
    obtain ⟨y', rfl⟩ := hC hQ
    have e := (mem_cubeAtLevel_iff_eq_coarseCentre hF x y').1 hxQ
    rw [← e]
    have hs := subset_sUnion_of_mem hQ
    exact ⟨hs, hs (self_mem_cubeAtLevel hF y'), fun z hz => hs hz.1⟩
end YangMills.Construction.PeriodicLattice.CoarseBlocks
