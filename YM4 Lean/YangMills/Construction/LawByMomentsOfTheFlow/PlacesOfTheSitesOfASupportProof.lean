import YangMills.Construction.LawByMomentsOfTheFlow.CoordinatesOnACircle
import YangMills.Construction.LawByMomentsOfTheFlow.PlacesOfTheSitesOfASupport
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.LevelTestFunctions
open TorusFields TorusLumps WeightedResponses ResponseInTheExpansion TestFunctions
private theorem parentBlock_offset (L n : ℕ) [NeZero L] [NeZero n] (hL : Odd L) (x : ZMod (n * L)) (Y : ZMod n)
    (h : (((((x.cast : ℤ) + ((L : ℤ) - 1) / 2) / (L : ℤ)) : ℤ) : ZMod n) = Y) :
    ∃ e w : ℤ, 2 * |e| + 1 ≤ (L : ℤ) ∧ (x.cast : ℤ) = L * (Y.cast : ℤ) + e + ((n * L : ℕ) : ℤ) * w := by
  obtain ⟨g, hg⟩ := hL
  have hLpos : (0 : ℤ) < L := by
    have := NeZero.ne L
    omega
  have hdiv : ((L : ℤ) - 1) / 2 = g := by omega
  rw [hdiv] at h
  have hq : (x.cast : ℤ) + g = L * (((x.cast : ℤ) + g) / L) + ((x.cast : ℤ) + g) % L :=
    (Int.mul_ediv_add_emod _ _).symm
  have hr0 : 0 ≤ ((x.cast : ℤ) + g) % L := Int.emod_nonneg _ (ne_of_gt hLpos)
  have hr1 : ((x.cast : ℤ) + g) % L < L := Int.emod_lt_of_pos _ hLpos
  generalize ((x.cast : ℤ) + g) / L = q at hq h
  generalize ((x.cast : ℤ) + g) % L = r at hq hr0 hr1
  have hY : ((q : ℤ) : ZMod n) = (((Y.cast : ℤ)) : ZMod n) := by
    rw [h]
    simp
  obtain ⟨w, hw⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp hY
  refine ⟨r - g, -w, ?_, ?_⟩
  · have : |r - g| ≤ g := abs_le.mpr ⟨by omega, by omega⟩
    omega
  · push_cast
    have hq' : q = (Y.cast : ℤ) - n * w := by linarith
    rw [hq'] at hq
    have : (x.cast : ℤ) = L * ((Y.cast : ℤ) - n * w) + r - g := by linarith
    rw [this]
    ring
private theorem intCast_eq_of_eq_add_mul (M : ℕ) (a b w : ℤ) (h : a = b + M * w) :
    (a : ZMod M) = (b : ZMod M) := by
  rw [h]
  simp
private theorem two_mul_supDist_fineCentre_add_one_le (L : ℕ) [NeZero L] (hL : Odd L) :
    ∀ (t n : ℕ) [NeZero n] (y : TorusSite n) (c : TorusSite (fineSide L t n)),
      c ∈ fineBlock L t n y → 2 * supDist c (fineCentre L t y) + 1 ≤ L ^ t := by
  intro t
  induction t with
  | zero =>
    intro n _ y c hc
    have h1 : c = y := by
      have h : c ∈ ({y} : Finset (TorusSite n)) := hc
      exact Finset.mem_singleton.mp h
    have h2 : (fineCentre L 0 y : TorusSite n) = y := by
      funext a
      show (((L : ℤ) ^ 0 * ((y a).cast : ℤ) : ℤ) : ZMod n) = y a
      rw [pow_zero, one_mul]
      exact ZMod.intCast_zmod_cast _
    have h3 : supDist (n := n) c (fineCentre L 0 y) = 0 := by
      rw [h2, h1]
      exact supDist_self _
    have h4 : supDist c (fineCentre L 0 y) = 0 := h3
    simp [h4]
  | succ t ih =>
    intro n _ Y c hc
    rw [fineBlock] at hc
    obtain ⟨y, hy, hc⟩ := Finset.mem_biUnion.mp hc
    have hy' : parentBlock L y = Y := by simpa [sitesInBlocks] using hy
    have h1 := ih (n * L) y c hc
    have hoff : ∀ a, ∃ e w : ℤ, 2 * |e| + 1 ≤ (L : ℤ) ∧
        ((y a).cast : ℤ) = L * ((Y a).cast : ℤ) + e + ((n * L : ℕ) : ℤ) * w := fun a =>
      parentBlock_offset L n hL (y a) (Y a) (by rw [← hy']; rfl)
    choose e w he hw using hoff
    have hM : fineSide L t (n * L) = n * L * L ^ t := fineSide_eq L t (n * L)
    have hcentre : (fineCentre L t y : TorusSite (fineSide L t (n * L))) =
        (fineCentre L (t + 1) Y : TorusSite (fineSide L t (n * L))) +
          siteOfInt (fun a => (L : ℤ) ^ t * e a) := by
      funext a
      have hint : (L : ℤ) ^ t * ((y a).cast : ℤ) =
          ((L : ℤ) ^ (t + 1) * ((Y a).cast : ℤ) + (L : ℤ) ^ t * e a) +
            ((fineSide L t (n * L) : ℕ) : ℤ) * w a := by
        rw [hw a, hM]
        push_cast
        ring
      have h2 := intCast_eq_of_eq_add_mul _ _ _ _ hint
      simp only [fineCentre, siteOfInt, Pi.add_apply]
      rw [h2, Int.cast_add]
      rfl
    obtain ⟨g, hg⟩ := hL
    have hsize : supDist (n := fineSide L t (n * L)) (fineCentre L (t + 1) Y) (fineCentre L t y) ≤
        L ^ t * g := by
      rw [hcentre]
      refine supDist_add_siteOfInt_le _ _ _ fun a => ?_
      rw [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast]
      refine Nat.mul_le_mul_left _ ?_
      have := he a
      rw [Int.abs_eq_natAbs] at this
      omega
    have htri := supDist_triangle (n := fineSide L t (n * L)) c (fineCentre L t y) (fineCentre L (t + 1) Y)
    have hcomm := supDist_comm (n := fineSide L t (n * L)) (fineCentre L t y) (fineCentre L (t + 1) Y)
    have hpow : L ^ (t + 1) = L ^ t + 2 * (L ^ t * g) := by
      calc L ^ (t + 1) = L ^ t * L := pow_succ _ _
        _ = L ^ t * (2 * g + 1) := congrArg (fun v => L ^ t * v) hg
        _ = L ^ t + 2 * (L ^ t * g) := by ring
    exact show 2 * supDist (n := fineSide L t (n * L)) c (fineCentre L (t + 1) Y) + 1 ≤ L ^ (t + 1) from by
      rw [hpow]
      omega
abbrev _root_.YangMills.SharedProofs.p17606 := @two_mul_supDist_fineCentre_add_one_le
private theorem exists_mem_fineBlock (L : ℕ) [NeZero L] : ∀ (t n : ℕ) [NeZero n]
    (c : TorusSite (fineSide L t n)), ∃ y : TorusSite n, c ∈ fineBlock L t n y := by
  intro t
  induction t with
  | zero =>
    intro n _ c
    refine ⟨c, ?_⟩
    show c ∈ ({c} : Finset (TorusSite n))
    exact Finset.mem_singleton_self _
  | succ t ih =>
    intro n _ c
    obtain ⟨y, hy⟩ := ih (n * L) c
    refine ⟨parentBlock L y, ?_⟩
    rw [fineBlock]
    exact Finset.mem_biUnion.mpr ⟨y, by simp [sitesInBlocks], hy⟩
abbrev _root_.YangMills.SharedProofs.p68008 := @exists_mem_fineBlock
private theorem exists_val_intCast_eq {m : ℕ} [NeZero m] (v : ℤ) :
    ∃ w : ℤ, (((v : ZMod m).val : ℕ) : ℤ) = v + m * w := by
  refine ⟨-(v / m), ?_⟩
  rw [ZMod.val_intCast, Int.emod_def]
  ring
private theorem abs_circleRep_vertex_sub_barycenter_le {m : ℕ} [NeZero m]
    (hper : ∀ (c : ℝ), 0 < c → ∀ (v : ℝ) (e : ℤ), circleRep c (v + c * e) = circleRep c v)
    (hsh : ∀ (c : ℝ), 0 < c → ∀ v : ℝ, |circleRep c v| ≤ |v|) (p : TorusPlaquette m) (hp : p.2.1 < p.2.2)
    (c : TorusSite m) (hc : c ∈ plaquetteVertices p.1 p.2.1 p.2.2) (a : Fin 4) :
    |circleRep m (((c a).val : ℝ) - barycenterCoord p a)| ≤ 1 / 2 := by
  obtain ⟨x, μ, ν⟩ := p
  have hm : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m)
  have hne : μ ≠ ν := ne_of_lt hp
  have key : ∀ ε₁ ε₂ : ℤ, (ε₁ = 0 ∨ ε₁ = 1) → (ε₂ = 0 ∨ ε₂ = 1) →
      c a = (((((x a).val : ℤ) + ((if a = μ then ε₁ else 0) + (if a = ν then ε₂ else 0)) : ℤ)) : ZMod m) →
      |circleRep m (((c a).val : ℝ) - barycenterCoord (x, μ, ν) a)| ≤ 1 / 2 := by
    intro ε₁ ε₂ h1 h2 hca
    obtain ⟨w, hw⟩ := exists_val_intCast_eq (m := m)
      (((x a).val : ℤ) + ((if a = μ then ε₁ else 0) + (if a = ν then ε₂ else 0)))
    rw [← hca] at hw
    have hreal : ((c a).val : ℝ) = ((x a).val : ℝ) +
        (((if a = μ then ε₁ else 0) + (if a = ν then ε₂ else 0) : ℤ) : ℝ) + (m : ℝ) * (w : ℝ) := by
      exact_mod_cast hw
    have hd : ((c a).val : ℝ) - barycenterCoord (x, μ, ν) a =
        ((((if a = μ then ε₁ else 0) + (if a = ν then ε₂ else 0) : ℤ) : ℝ) -
          ((if a = μ then 1 / 2 else 0) + (if a = ν then 1 / 2 else 0))) + (m : ℝ) * (w : ℝ) := by
      rw [hreal]
      simp only [barycenterCoord]
      ring
    rw [hd, hper _ hm]
    refine (hsh _ hm _).trans ?_
    by_cases ha : a = μ
    · have hb : a ≠ ν := fun h => hne (ha.symm.trans h)
      simp only [ha, if_true, hne, if_false]
      rcases h1 with h | h <;> subst h <;> norm_num [abs_le]
    · by_cases hb : a = ν
      · simp only [ha, if_false, hb, if_true, show ν ≠ μ from fun h => hne h.symm]
        rcases h2 with h | h <;> subst h <;> norm_num [abs_le]
      · simp [ha, hb]
  have hx : ((((x a).val : ℤ) : ZMod m)) = x a := by simp
  simp only [plaquetteVertices, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  · refine key 0 0 (Or.inl rfl) (Or.inl rfl) ?_
    simp [hx]
  · refine key 1 0 (Or.inr rfl) (Or.inl rfl) ?_
    by_cases ha : a = μ
    · subst ha
      simp [unitStep, hx, hne]
    · simp [unitStep, hx, ha, Pi.single_apply]
  · refine key 0 1 (Or.inl rfl) (Or.inr rfl) ?_
    by_cases ha : a = ν
    · subst ha
      simp [unitStep, hx, hne.symm]
    · simp [unitStep, hx, ha, Pi.single_apply]
  · refine key 1 1 (Or.inr rfl) (Or.inr rfl) ?_
    by_cases ha : a = μ
    · subst ha
      simp [unitStep, hx, hne, Pi.single_apply]
    · by_cases hb : a = ν
      · subst hb
        simp [unitStep, hx, ha, Pi.single_apply]
      · simp [unitStep, hx, ha, hb, Pi.single_apply]
abbrev _root_.YangMills.DeltaSharedProofs.p502487 := @abs_circleRep_vertex_sub_barycenter_le
private theorem exists_testWeight_ne_zero_of_eq {k : ℕ} (P : LevelData k) (L : ℕ) (i : Fin k) (m₁ m₂ : ℕ)
    (h : m₁ = m₂) (hl : ∃ p : OrientedPlaquette m₁, P.testWeight L i m₁ p.1 ≠ 0) :
    ∃ p : OrientedPlaquette m₂, P.testWeight L i m₂ p.1 ≠ 0 := by
  subst h
  exact hl
theorem supportSitesLocationStatement_holds (hC : CircleRepProperties) :
    supportSitesLocationStatement := by
  obtain ⟨hper, hsh, hsub, -, -, hsc, hsite⟩ := hC
  intro L _ hL k P t ht i
  have hLpos : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hm : fineSide L t (P.sideAt L t) = P.period L * L ^ P.windowLevel := by
    rw [fineSide_eq, LevelData.sideAt, mul_assoc, ← pow_add, Nat.sub_add_cancel ht]
  refine ⟨fun y hy => ?_, fun hlive => ?_⟩
  · simp only [LevelData.supportSites, weightSupportSites, Finset.mem_filter, Finset.mem_univ,
      true_and] at hy
    obtain ⟨p, ⟨hlt, c, hc, hcb⟩, hne⟩ := hy
    refine ⟨WithLp.toLp 2 fun a => (L : ℝ) ^ P.windowLevel / (L : ℝ) ^ P.scaleLevel *
      circleRep (P.period L) (barycenterCoord p a / (L : ℝ) ^ P.windowLevel - P.center a), hne, fun a => ?_⟩
    have hT : (0 : ℝ) < (P.period L : ℝ) := by
      have : 0 < P.period L :=
        Nat.pos_of_ne_zero (mul_ne_zero two_ne_zero (pow_ne_zero _ (NeZero.ne L)))
      exact_mod_cast this
    have hM : (0 : ℝ) < (L : ℝ) ^ P.windowLevel := by positivity
    have hS : (0 : ℝ) < (L : ℝ) ^ P.scaleLevel := by positivity
    have hmr : ((fineSide L t (P.sideAt L t) : ℕ) : ℝ) = (P.period L : ℝ) * (L : ℝ) ^ P.windowLevel := by
      rw [hm]
      push_cast
      ring
    have hmpos : (0 : ℝ) < ((fineSide L t (P.sideAt L t) : ℕ) : ℝ) := by rw [hmr]; positivity
    obtain ⟨w₁, hw₁⟩ := exists_val_intCast_eq (m := fineSide L t (P.sideAt L t))
      ((L : ℤ) ^ t * ((y a).cast : ℤ))
    have hcast : ((y a).cast : ℤ) = ((y a).val : ℤ) := by simp
    have hCa : (fineCentre L t y) a =
        (((L : ℤ) ^ t * ((y a).cast : ℤ) : ℤ) : ZMod (fineSide L t (P.sideAt L t))) := rfl
    rw [← hCa, hcast] at hw₁
    have hwr : (((fineCentre L t y) a).val : ℝ) = (L : ℝ) ^ t * ((y a).val : ℝ) +
        ((fineSide L t (P.sideAt L t) : ℕ) : ℝ) * (w₁ : ℝ) := by
      exact_mod_cast hw₁
    have hnear : |circleRep ((fineSide L t (P.sideAt L t) : ℕ) : ℝ)
        (((y a).val : ℝ) * (L : ℝ) ^ t - barycenterCoord p a)| ≤ (L : ℝ) ^ t / 2 := by
      have hsplit : ((y a).val : ℝ) * (L : ℝ) ^ t - barycenterCoord p a =
          (((((fineCentre L t y) a).val : ℝ) - ((c a).val : ℝ)) + (((c a).val : ℝ) - barycenterCoord p a)) +
            ((fineSide L t (P.sideAt L t) : ℕ) : ℝ) * ((-w₁ : ℤ) : ℝ) := by
        rw [hwr]
        push_cast
        ring
      rw [hsplit, hper _ hmpos]
      refine (hsub _ hmpos _ _).trans ?_
      have h1 := hsite (fineSide L t (P.sideAt L t)) ((fineCentre L t y) a) (c a)
      have h2 := abs_circleRep_vertex_sub_barycenter_le hper hsh p hlt c hc a
      have h3 := two_mul_supDist_fineCentre_add_one_le L hL t (P.sideAt L t) y c hcb
      have h4 : (((fineCentre L t y) a - c a).valMinAbs).natAbs ≤ supDist (fineCentre L t y) c :=
        (supDist_le_iff _ _ _).mp le_rfl a
      rw [supDist_comm] at h4
      have h5 : (2 : ℝ) * (supDist c (fineCentre L t y) : ℝ) + 1 ≤ (L : ℝ) ^ t := by exact_mod_cast h3
      have h6 : ((((fineCentre L t y) a - c a).valMinAbs).natAbs : ℝ) ≤ (supDist c (fineCentre L t y) : ℝ) := by
        exact_mod_cast h4
      rw [h1]
      linarith
    have hro : circleRep (P.period L) (barycenterCoord p a / (L : ℝ) ^ P.windowLevel - P.center a) =
        (barycenterCoord p a / (L : ℝ) ^ P.windowLevel - P.center a) -
          (P.period L : ℝ) *
            (round ((barycenterCoord p a / (L : ℝ) ^ P.windowLevel - P.center a) / (P.period L : ℝ)) : ℝ) := rfl
    have harg : ((y a).val : ℝ) * (L : ℝ) ^ t / (L : ℝ) ^ P.windowLevel - P.center a -
        (L : ℝ) ^ P.scaleLevel / (L : ℝ) ^ P.windowLevel *
          (WithLp.toLp 2 fun a => (L : ℝ) ^ P.windowLevel / (L : ℝ) ^ P.scaleLevel *
            circleRep (P.period L) (barycenterCoord p a / (L : ℝ) ^ P.windowLevel - P.center a) :
              EuclideanFourSpace) a =
        (((y a).val : ℝ) * (L : ℝ) ^ t - barycenterCoord p a) / (L : ℝ) ^ P.windowLevel +
          (P.period L : ℝ) *
            (round ((barycenterCoord p a / (L : ℝ) ^ P.windowLevel - P.center a) / (P.period L : ℝ)) : ℝ) := by
      simp only [hro]
      field_simp
      ring
    rw [harg, hper _ hT]
    have hscale := hsc (P.period L) ((L : ℝ) ^ P.windowLevel) hT hM
      ((((y a).val : ℝ) * (L : ℝ) ^ t - barycenterCoord p a) / (L : ℝ) ^ P.windowLevel)
    rw [div_mul_cancel₀ _ (ne_of_gt hM), ← hmr] at hscale
    rw [hscale, abs_mul, abs_of_pos hM] at hnear
    rw [le_div_iff₀ (by positivity)]
    linarith
  · obtain ⟨p, hp⟩ := exists_testWeight_ne_zero_of_eq P L i _ _ hm.symm hlive
    obtain ⟨y, hy⟩ := exists_mem_fineBlock L t (P.sideAt L t) p.1.1
    refine ⟨y, ?_⟩
    simp only [LevelData.supportSites, weightSupportSites, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨p.1, ⟨p.2, p.1.1, ?_, hy⟩, hp⟩
    simp [plaquetteVertices]
end YangMills.Construction.LevelTestFunctions
end
