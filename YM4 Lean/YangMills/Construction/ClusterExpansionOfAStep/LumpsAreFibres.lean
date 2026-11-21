import YangMills.Construction.ClusterExpansionOfAStep.DistancesAndClasses
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
namespace TorusLumps
open BlockAverages LumpContours TorusFields
section Corners
variable {n : ℕ}
def stripStart {L : ℕ} (g : LumpGrid L) (c : ℤ) : ℤ := c - offsetFromCentre L c + g.lower (offsetFromCentre L c)
def lumpCorner (ℓ : StepParameters) (z : TorusSite n) : TorusSite n :=
  fun i => ((stripStart ℓ.grid ((z i).cast : ℤ) : ℤ) : ZMod n)
open Classical in
def torusLumpOf (ℓ : StepParameters) [NeZero n] (z : TorusSite n) : Finset (TorusSite n) :=
  Finset.univ.filter fun x => lumpCorner ℓ x = lumpCorner ℓ z
end Corners
section IntCast
variable {m n : ℕ}
theorem castInt_add (hm : m = n) [NeZero m] (a b : ZMod m) :
    (((a + b : ZMod m).cast : ℤ) : ZMod n) = ((a.cast : ℤ) : ZMod n) + ((b.cast : ℤ) : ZMod n) := by
  subst hm
  simp
theorem castInt_intCast (hm : m = n) [NeZero m] (z : ℤ) :
    ((((z : ZMod m)).cast : ℤ) : ZMod n) = (z : ZMod n) := by
  subst hm
  simp
theorem castInt_neg (hm : m = n) [NeZero m] (a : ZMod m) :
    (((- a : ZMod m).cast : ℤ) : ZMod n) = - ((a.cast : ℤ) : ZMod n) := by
  subst hm
  simp
theorem castInt_surjective (hm : m = n) [NeZero m] (b : ZMod n) :
    ∃ a : ZMod m, ((a.cast : ℤ) : ZMod n) = b := by
  subst hm
  exact ⟨b, by simp⟩
theorem castInt_injective (hm : m = n) [NeZero m] (a b : ZMod m)
    (h : ((a.cast : ℤ) : ZMod n) = ((b.cast : ℤ) : ZMod n)) : a = b := by
  subst hm
  simpa using h
end IntCast
variable {L : ℕ}
theorem offsetFromCentre_spec (hL : 0 < L) (hodd : Odd L) (c : ℤ) :
    (L : ℤ) ∣ c - offsetFromCentre L c ∧ |offsetFromCentre L c| ≤ ((L : ℤ) - 1) / 2 := by
  obtain ⟨k, rfl⟩ := hodd
  have hL' : (0 : ℤ) < ((2 * k + 1 : ℕ) : ℤ) := by exact_mod_cast hL
  have hh : (((2 * k + 1 : ℕ) : ℤ) - 1) / 2 = k := by
    push_cast
    omega
  unfold offsetFromCentre
  rw [hh]
  have h1 := Int.emod_nonneg (c + k) hL'.ne'
  have h2 := Int.emod_lt_of_pos (c + k) hL'
  have h3 := Int.emod_add_mul_ediv (c + k) ((2 * k + 1 : ℕ) : ℤ)
  constructor
  · refine ⟨(c + k) / ((2 * k + 1 : ℕ) : ℤ), ?_⟩
    linarith
  · rw [abs_le]
    push_cast at h1 h2 ⊢
    constructor <;> omega
theorem offsetFromCentre_add_of_dvd (hL : 0 < L) (hodd : Odd L) (b o : ℤ) (hb : (L : ℤ) ∣ b)
    (ho : |o| ≤ ((L : ℤ) - 1) / 2) :
    offsetFromCentre L (b + o) = o := by
  obtain ⟨k, rfl⟩ := hodd
  obtain ⟨q, rfl⟩ := hb
  have hh : (((2 * k + 1 : ℕ) : ℤ) - 1) / 2 = k := by
    push_cast
    omega
  unfold offsetFromCentre
  rw [hh] at ho ⊢
  rw [abs_le] at ho
  have : (((2 * k + 1 : ℕ) : ℤ) * q + o + k) % ((2 * k + 1 : ℕ) : ℤ) = o + k := by
    rw [show ((2 * k + 1 : ℕ) : ℤ) * q + o + k = (o + k) + ((2 * k + 1 : ℕ) : ℤ) * q by ring,
      Int.add_mul_emod_self_left]
    refine Int.emod_eq_of_lt (by omega) ?_
    push_cast
    omega
  rw [this]
  ring
theorem offsetFromCentre_add_dvd (hL : 0 < L) (hodd : Odd L) (c b : ℤ) (hb : (L : ℤ) ∣ b) :
    offsetFromCentre L (c + b) = offsetFromCentre L c := by
  obtain ⟨h1, h2⟩ := offsetFromCentre_spec hL hodd c
  have : c + b = ((c - offsetFromCentre L c) + b) + offsetFromCentre L c := by ring
  rw [this]
  exact offsetFromCentre_add_of_dvd hL hodd _ _ (dvd_add h1 hb) h2
theorem stripStart_add_dvd (hL : 0 < L) (hodd : Odd L) (g : LumpGrid L) (c b : ℤ) (hb : (L : ℤ) ∣ b) :
    stripStart g (c + b) = stripStart g c + b := by
  unfold stripStart
  rw [offsetFromCentre_add_dvd hL hodd c b hb]
  ring
theorem stripStart_eq_of_mem (hL : 0 < L) (hodd : Odd L) (g : LumpGrid L) (c h : ℤ)
    (h1 : c - offsetFromCentre L c + g.lower (offsetFromCentre L c) ≤ h)
    (h2 : h ≤ c - offsetFromCentre L c + g.upper (offsetFromCentre L c)) : stripStart g h = stripStart g c := by
  obtain ⟨hb, ho⟩ := offsetFromCentre_spec hL hodd c
  obtain ⟨b1, b2, b3, b4⟩ := g.mem_interval _ ho
  have ho' : |h - (c - offsetFromCentre L c)| ≤ ((L : ℤ) - 1) / 2 := by
    rw [abs_le]
    constructor <;> linarith
  have hoff : offsetFromCentre L h = h - (c - offsetFromCentre L c) := by
    have := offsetFromCentre_add_of_dvd hL hodd (c - offsetFromCentre L c) (h - (c - offsetFromCentre L c)) hb ho'
    rwa [show c - offsetFromCentre L c + (h - (c - offsetFromCentre L c)) = h by ring] at this
  have hs := (g.interval_eq (offsetFromCentre L c) (h - (c - offsetFromCentre L c)) ho (by linarith) (by linarith)).1
  unfold stripStart
  rw [hoff, hs]
  ring
theorem mem_of_stripStart_eq (hL : 0 < L) (hodd : Odd L) (g : LumpGrid L) (c h : ℤ)
    (hs : stripStart g h = stripStart g c) :
    c - offsetFromCentre L c + g.lower (offsetFromCentre L c) ≤ h ∧
      h ≤ c - offsetFromCentre L c + g.upper (offsetFromCentre L c) := by
  obtain ⟨hb, ho⟩ := offsetFromCentre_spec hL hodd c
  obtain ⟨hb', ho'⟩ := offsetFromCentre_spec hL hodd h
  obtain ⟨b1, b2, b3, b4⟩ := g.mem_interval _ ho
  obtain ⟨b1', b2', b3', b4'⟩ := g.mem_interval _ ho'
  unfold stripStart at hs
  obtain ⟨u, hu⟩ := hb
  obtain ⟨u', hu'⟩ := hb'
  have hLpos : (0 : ℤ) < L := by exact_mod_cast hL
  have hhalf : 2 * (((L : ℤ) - 1) / 2) ≤ (L : ℤ) - 1 := by omega
  have huu : u' = u := by
    have e : (L : ℤ) * (u' - u) = g.lower (offsetFromCentre L c) - g.lower (offsetFromCentre L h) := by
      rw [mul_sub, ← hu, ← hu']
      linarith
    have hlt : |(L : ℤ) * (u' - u)| < L := by
      rw [e, abs_lt]
      constructor <;> linarith
    by_contra hne
    have h1 : 1 ≤ |u' - u| := Int.one_le_abs (sub_ne_zero.mpr hne)
    rw [abs_mul, abs_of_pos hLpos] at hlt
    nlinarith
  have hbase : h - offsetFromCentre L h = c - offsetFromCentre L c := by rw [hu, hu', huu]
  set f := g.lower (offsetFromCentre L c) with hfdef
  have s1 := g.interval_eq (offsetFromCentre L c) f ho le_rfl (by linarith)
  have s2 := g.interval_eq (offsetFromCentre L h) f ho' (by linarith) (by linarith)
  constructor <;> linarith
theorem stripStart_cast_intCast (ℓ : StepParameters) (hfit : ℓ.Admissible) {n : ℕ} [NeZero n]
    (hLn : ℓ.side ∣ n) (c : ℤ) :
    ((stripStart ℓ.grid (((c : ZMod n)).cast : ℤ) : ℤ) : ZMod n) = (stripStart ℓ.grid c : ZMod n) := by
  have hLpos : 0 < ℓ.side := by have := hfit.L_ge; omega
  have h1 : (((c : ZMod n)).cast : ℤ) = c + (-(c / n) * n) := by
    rw [ZMod.coe_intCast]
    have := Int.emod_add_mul_ediv c n
    linarith
  have hd : (ℓ.side : ℤ) ∣ -(c / n) * n := Dvd.dvd.mul_left (by exact_mod_cast hLn) _
  rw [h1, stripStart_add_dvd hLpos hfit.L_odd _ _ _ hd]
  simp
section Projection
variable {ℓ : StepParameters} {n : ℕ}
theorem period_stepBlockFrame (hLn : ℓ.side ∣ n) (i : Fin 4) :
    (stepBlockFrame ℓ.side (n / ℓ.side)).period 0 i = n := by
  simp only [stepBlockFrame, BlockFrame.period, BlockFrame.top]
  simp [Nat.div_mul_cancel hLn]
theorem neZero_div_side [NeZero n] (hLn : ℓ.side ∣ n) : NeZero (n / ℓ.side) :=
  ⟨by
    intro h
    have := Nat.div_mul_cancel hLn
    rw [h, zero_mul] at this
    exact NeZero.ne n this.symm⟩
theorem toTorusSite_add [NeZero n] (hLn : ℓ.side ∣ n) (x y : (stepBlockFrame ℓ.side (n / ℓ.side)).Site 0) :
    toTorusSite n (x + y) = toTorusSite n x + toTorusSite n y := by
  have := neZero_div_side (ℓ := ℓ) hLn
  funext k
  exact castInt_add (period_stepBlockFrame hLn k) (x k) (y k)
theorem toTorusSite_siteOfCoords [NeZero n] (hLn : ℓ.side ∣ n) (h : Fin 4 → ℤ) :
    toTorusSite n (siteOfCoords 0 h : (stepBlockFrame ℓ.side (n / ℓ.side)).Site 0) = siteOfInt h := by
  have := neZero_div_side (ℓ := ℓ) hLn
  funext k
  exact castInt_intCast (period_stepBlockFrame hLn k) (h k)
theorem toTorusSite_unitStep [NeZero n] (hLn : ℓ.side ∣ n) (i : Fin 4) :
    toTorusSite n (BlockAverages.unitStep 0 i : (stepBlockFrame ℓ.side (n / ℓ.side)).Site 0) =
      TorusFields.unitStep n i := by
  unfold BlockAverages.unitStep
  rw [toTorusSite_siteOfCoords hLn]
  funext k
  by_cases hk : k = i
  · subst hk
    simp [siteOfInt, TorusFields.unitStep]
  · simp [siteOfInt, TorusFields.unitStep, Pi.single_apply, hk]
theorem toTorusSite_surjective [NeZero n] (hLn : ℓ.side ∣ n) (z : TorusSite n) :
    ∃ x : (stepBlockFrame ℓ.side (n / ℓ.side)).Site 0, toTorusSite n x = z := by
  have := neZero_div_side (ℓ := ℓ) hLn
  have h := fun k => castInt_surjective (period_stepBlockFrame hLn k) (z k)
  choose x hx using h
  exact ⟨x, funext hx⟩
theorem plaquetteDefect_readAtLevel [NeZero n] (hLn : ℓ.side ∣ n) (W : TorusField n)
    (x : (stepBlockFrame ℓ.side (n / ℓ.side)).Site 0) (μ ν : Fin 4) :
    plaquetteDefect (readAtLevel (stepBlockFrame ℓ.side (n / ℓ.side)) 0 W) (x, μ, ν) =
      TorusFields.curvature W (toTorusSite n x) μ ν := by
  unfold plaquetteDefect TorusFields.curvature TorusFields.holonomy
  have hv : plaquetteHolonomy (readAtLevel (stepBlockFrame ℓ.side (n / ℓ.side)) 0 W) (x, μ, ν) =
      W (toTorusSite n x) μ * W (toTorusSite n x + TorusFields.unitStep n μ) ν *
        (W (toTorusSite n x + TorusFields.unitStep n ν) μ)⁻¹ * (W (toTorusSite n x) ν)⁻¹ := by
    have a1 : x + BlockAverages.unitStep 0 μ + BlockAverages.unitStep 0 ν - BlockAverages.unitStep 0 μ =
        x + BlockAverages.unitStep 0 ν := by abel
    have a2 : x + BlockAverages.unitStep 0 μ + BlockAverages.unitStep 0 ν + -BlockAverages.unitStep 0 μ -
        BlockAverages.unitStep 0 ν = x := by abel
    have hr : ∀ (z : (stepBlockFrame ℓ.side (n / ℓ.side)).Site 0) (i : Fin 4),
        readAtLevel (stepBlockFrame ℓ.side (n / ℓ.side)) 0 W z i = W (toTorusSite n z) i := fun _ _ => rfl
    simp only [plaquetteHolonomy, pathHolonomy, linkValue, stepDisplacement, if_true, Bool.false_eq_true,
      if_false, mul_one, a1, a2, hr, toTorusSite_add hLn, toTorusSite_unitStep hLn, mul_assoc]
  rw [hv]
theorem mem_levelSites [NeZero n] (hLn : ℓ.side ∣ n) (x : (stepBlockFrame ℓ.side (n / ℓ.side)).Site 0) :
    x ∈ levelSites (stepBlockFrame ℓ.side (n / ℓ.side)) 0 := by
  have := neZero_div_side (ℓ := ℓ) hLn
  unfold levelSites boxSites
  refine Finset.mem_image.mpr ⟨siteCoords x, ?_, ?_⟩
  · refine Fintype.mem_piFinset.mpr fun i => Finset.mem_Icc.mpr ?_
    have h1 : siteCoords x i = (((x i).val : ℕ) : ℤ) := ZMod.cast_eq_val _
    have h2 := ZMod.val_lt (x i)
    rw [h1]
    simp only [Pi.zero_apply]
    omega
  · funext k
    simp [siteOfCoords, siteCoords]
theorem image_lumpOf (hfit : ℓ.Admissible) [NeZero n] (hLn : ℓ.side ∣ n)
    (x : (stepBlockFrame ℓ.side (n / ℓ.side)).Site 0) :
    open Classical in (lumpOf ℓ.grid x).image (toTorusSite n) = torusLumpOf ℓ (toTorusSite n x) := by
  classical
  have hLpos : 0 < ℓ.side := by have := hfit.L_ge; omega
  have hodd := hfit.L_odd
  have hkey : ∀ h : Fin 4 → ℤ, lumpCorner ℓ (siteOfInt h : TorusSite n) =
      fun i => (stripStart ℓ.grid (h i) : ZMod n) := by
    intro h
    funext i
    exact stripStart_cast_intCast ℓ hfit hLn (h i)
  have hx : toTorusSite n x = siteOfInt (siteCoords x) := rfl
  ext z
  simp only [Finset.mem_image, torusLumpOf, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨h, hh, rfl⟩ := Finset.mem_image.mp hy
    rw [toTorusSite_siteOfCoords hLn, hx, hkey, hkey]
    funext i
    have hi := Finset.mem_Icc.mp (Fintype.mem_piFinset.mp hh i)
    rw [stripStart_eq_of_mem hLpos hodd ℓ.grid (siteCoords x i) (h i) hi.1 hi.2]
  · intro hz
    have hz2 : ∀ i, ∃ k : ℤ, stripStart ℓ.grid ((z i).cast : ℤ) =
        stripStart ℓ.grid (siteCoords x i) + n * k := by
      intro i
      have h1 := congrFun hz i
      rw [hx, hkey] at h1
      have h2 : ((stripStart ℓ.grid ((z i).cast : ℤ) : ℤ) : ZMod n) =
          (stripStart ℓ.grid (siteCoords x i) : ZMod n) := h1
      rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at h2
      obtain ⟨k, hk⟩ := h2
      exact ⟨-k, by linarith⟩
    choose k hk using hz2
    have hdv : ∀ i, (ℓ.side : ℤ) ∣ -(n : ℤ) * k i := fun i =>
      Dvd.dvd.mul_right (Dvd.dvd.neg_right (by exact_mod_cast hLn)) _
    have hstrip : ∀ i, stripStart ℓ.grid (((z i).cast : ℤ) + -(n : ℤ) * k i) =
        stripStart ℓ.grid (siteCoords x i) := by
      intro i
      rw [stripStart_add_dvd hLpos hodd _ _ _ (hdv i), hk]
      ring
    refine ⟨siteOfCoords 0 fun i => ((z i).cast : ℤ) + -(n : ℤ) * k i, ?_, ?_⟩
    · refine Finset.mem_image.mpr ⟨_, Fintype.mem_piFinset.mpr fun i => Finset.mem_Icc.mpr ?_, rfl⟩
      exact mem_of_stripStart_eq hLpos hodd ℓ.grid (siteCoords x i) _ (hstrip i)
    · rw [toTorusSite_siteOfCoords hLn]
      funext i
      simp [siteOfInt]
theorem mem_plaquetteVertices_iff [NeZero n] (hLn : ℓ.side ∣ n)
    (x : (stepBlockFrame ℓ.side (n / ℓ.side)).Site 0) (μ ν : Fin 4) (z : TorusSite n) :
    z ∈ plaquetteVertices (toTorusSite n x) μ ν ↔
      ∃ y ∈ plaquetteCorners ((x, μ, ν) : (stepBlockFrame ℓ.side (n / ℓ.side)).Site 0 × Fin 4 × Fin 4),
        toTorusSite n y = z := by
  simp only [plaquetteVertices, plaquetteCorners, List.mem_cons, List.not_mem_nil, or_false,
    Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro (h | h | h | h)
    · exact ⟨x, Or.inl rfl, h.symm⟩
    · exact ⟨x + BlockAverages.unitStep 0 μ, Or.inr (Or.inl rfl),
        by rw [h, toTorusSite_add hLn, toTorusSite_unitStep hLn]⟩
    · exact ⟨x + BlockAverages.unitStep 0 ν, Or.inr (Or.inr (Or.inl rfl)),
        by rw [h, toTorusSite_add hLn, toTorusSite_unitStep hLn]⟩
    · exact ⟨x + BlockAverages.unitStep 0 μ + BlockAverages.unitStep 0 ν, Or.inr (Or.inr (Or.inr rfl)),
        by rw [h, toTorusSite_add hLn, toTorusSite_add hLn, toTorusSite_unitStep hLn,
          toTorusSite_unitStep hLn]⟩
  · rintro ⟨y, (rfl | rfl | rfl | rfl), rfl⟩ <;> simp [toTorusSite_add hLn, toTorusSite_unitStep hLn]
end Projection
theorem mem_torusHotLumps_iff (ℓ : StepParameters) (hfit : ℓ.Admissible) {n : ℕ} [NeZero n]
    (hLn : ℓ.side ∣ n) (W : TorusField n) (l : Finset (TorusSite n)) :
    l ∈ torusHotLumps ℓ W ↔ ∃ x μ ν, μ < ν ∧ ℓ.threshold ≤ TorusFields.curvature W x μ ν ∧
      ∃ z ∈ plaquetteVertices x μ ν, l = torusLumpOf ℓ z := by
  classical
  unfold torusHotLumps hotLumps
  simp only [Finset.mem_image, Finset.mem_biUnion, Finset.mem_filter]
  constructor
  · rintro ⟨l₀, ⟨⟨x, μ, ν⟩, ⟨hp, hs⟩, hl⟩, rfl⟩
    obtain ⟨z₀, hz₀, rfl⟩ := hl
    have hlt : μ < ν := (Finset.mem_filter.mp hp).2.1
    refine ⟨toTorusSite n x, μ, ν, hlt, ?_, toTorusSite n z₀,
      (mem_plaquetteVertices_iff hLn x μ ν _).mpr ⟨z₀, hz₀, rfl⟩, ?_⟩
    · rw [← plaquetteDefect_readAtLevel hLn]
      exact hs
    · exact image_lumpOf hfit hLn z₀
  · rintro ⟨x', μ, ν, hlt, hs, z', hz', rfl⟩
    obtain ⟨x, rfl⟩ := toTorusSite_surjective (ℓ := ℓ) hLn x'
    obtain ⟨z₀, hz₀, rfl⟩ := (mem_plaquetteVertices_iff hLn x μ ν _).mp hz'
    refine ⟨lumpOf ℓ.grid z₀, ⟨(x, μ, ν), ⟨?_, ?_⟩, z₀, hz₀, rfl⟩, image_lumpOf hfit hLn z₀⟩
    · unfold cutPlaquettes
      refine Finset.mem_filter.mpr ⟨?_, hlt, fun y _ => mem_levelSites hLn y⟩
      simp [mem_levelSites hLn x]
    · rw [plaquetteDefect_readAtLevel hLn]
      exact hs
section Diameter
variable {ℓ : StepParameters} {n : ℕ} [NeZero n]
theorem mem_torusLumpOf_self (z : TorusSite n) : z ∈ torusLumpOf ℓ z := by
  classical
  simp [torusLumpOf]
theorem lumpCorner_siteOfInt (hfit : ℓ.Admissible) (hLn : ℓ.side ∣ n) (h : Fin 4 → ℤ) :
    lumpCorner ℓ (siteOfInt h : TorusSite n) = fun i => (stripStart ℓ.grid (h i) : ZMod n) := by
  funext i
  exact stripStart_cast_intCast ℓ hfit hLn (h i)
theorem eq_siteOfInt_cast (z : TorusSite n) : z = siteOfInt fun i => ((z i).cast : ℤ) := by
  funext i
  simp [siteOfInt]
theorem lumpCorner_add_side_mul (hfit : ℓ.Admissible) (hLn : ℓ.side ∣ n) (x : TorusSite n) (v : Fin 4 → ℤ) :
    lumpCorner ℓ (x + siteOfInt fun i => (ℓ.side : ℤ) * v i) =
      lumpCorner ℓ x + siteOfInt fun i => (ℓ.side : ℤ) * v i := by
  have hLpos : 0 < ℓ.side := by have := hfit.L_ge; omega
  conv_lhs => rw [eq_siteOfInt_cast x, ← siteOfInt_add, lumpCorner_siteOfInt hfit hLn]
  conv_rhs => rw [eq_siteOfInt_cast x, lumpCorner_siteOfInt hfit hLn]
  funext i
  simp only [Pi.add_apply, siteOfInt]
  rw [stripStart_add_dvd hLpos hfit.L_odd _ _ _ (Dvd.intro _ rfl)]
  simp
theorem supDist_lt_of_lumpCorner_eq (hfit : ℓ.Admissible) (hLn : ℓ.side ∣ n) {x z : TorusSite n}
    (h : lumpCorner ℓ z = lumpCorner ℓ x) :
    supDist x z < 2 ^ 15 := by
  have hLpos : 0 < ℓ.side := by have := hfit.L_ge; omega
  have hbound : supDist x z ≤ 2 ^ 15 - 1 := by
    rw [supDist_comm, supDist_le_iff]
    intro i
    set c : ℤ := ((x i).cast : ℤ) with hc
    set c' : ℤ := ((z i).cast : ℤ) with hc'
    have h1 := congrFun h i
    have h2 : ((stripStart ℓ.grid c' : ℤ) : ZMod n) = (stripStart ℓ.grid c : ZMod n) := h1
    rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at h2
    obtain ⟨k, hk⟩ := h2
    have hdv : (ℓ.side : ℤ) ∣ (n : ℤ) * k := Dvd.dvd.mul_right (by exact_mod_cast hLn) _
    have hs : stripStart ℓ.grid (c' + (n : ℤ) * k) = stripStart ℓ.grid c := by
      rw [stripStart_add_dvd hLpos hfit.L_odd _ _ _ hdv]
      linarith
    obtain ⟨m1, m2⟩ := mem_of_stripStart_eq hLpos hfit.L_odd ℓ.grid c _ hs
    obtain ⟨_, ho⟩ := offsetFromCentre_spec hLpos hfit.L_odd c
    have hsides := ℓ.grid.interval_length _ ho
    obtain ⟨b1, b2, b3, b4⟩ := ℓ.grid.mem_interval _ ho
    have hdiff : z i - x i = (((c' + (n : ℤ) * k) - c : ℤ) : ZMod n) := by
      simp [hc, hc']
    rw [hdiff]
    refine (natAbs_valMinAbs_intCast_le _).trans ?_
    have : |(c' + (n : ℤ) * k) - c| ≤ 2 ^ 15 - 1 := by
      rw [abs_le]
      constructor <;> linarith
    omega
  have : (2 : ℕ) ^ 15 - 1 < 2 ^ 15 := by norm_num
  omega
theorem exists_centre_of_torusLumpOf (hfit : ℓ.Admissible) (hLn : ℓ.side ∣ n) (z : TorusSite n) :
    ∃ m : TorusSite n, ∀ x ∈ torusLumpOf ℓ z, supDist x m ≤ 2 ^ 14 := by
  classical
  have hLpos : 0 < ℓ.side := by have := hfit.L_ge; omega
  let c : Fin 4 → ℤ := fun i => ((z i).cast : ℤ)
  let lo : Fin 4 → ℤ := fun i =>
    c i - offsetFromCentre ℓ.side (c i) + ℓ.grid.lower (offsetFromCentre ℓ.side (c i))
  let hi : Fin 4 → ℤ := fun i =>
    c i - offsetFromCentre ℓ.side (c i) + ℓ.grid.upper (offsetFromCentre ℓ.side (c i))
  refine ⟨siteOfInt fun i => (lo i + hi i) / 2, fun x hx => ?_⟩
  have hkey := (Finset.mem_filter.mp hx).2
  rw [supDist_le_iff]
  intro i
  set c' : ℤ := ((x i).cast : ℤ) with hc'
  have h2 : ((stripStart ℓ.grid c' : ℤ) : ZMod n) = (stripStart ℓ.grid (c i) : ZMod n) := congrFun hkey i
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at h2
  obtain ⟨k, hk⟩ := h2
  have hdv : (ℓ.side : ℤ) ∣ (n : ℤ) * k := Dvd.dvd.mul_right (by exact_mod_cast hLn) _
  have hs : stripStart ℓ.grid (c' + (n : ℤ) * k) = stripStart ℓ.grid (c i) := by
    rw [stripStart_add_dvd hLpos hfit.L_odd _ _ _ hdv]
    linarith
  obtain ⟨m1, m2⟩ := mem_of_stripStart_eq hLpos hfit.L_odd ℓ.grid (c i) _ hs
  obtain ⟨_, ho⟩ := offsetFromCentre_spec hLpos hfit.L_odd (c i)
  have hsides := ℓ.grid.interval_length _ ho
  have hdiff : x i - (siteOfInt fun i => (lo i + hi i) / 2 : TorusSite n) i =
      (((c' + (n : ℤ) * k) - (lo i + hi i) / 2 : ℤ) : ZMod n) := by
    simp [hc', siteOfInt]
  rw [hdiff]
  refine (natAbs_valMinAbs_intCast_le _).trans ?_
  have hlo : lo i ≤ c' + (n : ℤ) * k := m1
  have hhi : c' + (n : ℤ) * k ≤ hi i := m2
  have hw : hi i - lo i + 1 < 2 ^ 15 := by
    have : hi i - lo i =
        ℓ.grid.upper (offsetFromCentre ℓ.side (c i)) - ℓ.grid.lower (offsetFromCentre ℓ.side (c i)) := by
      simp only [hi, lo]
      ring
    linarith [hsides.2]
  omega
end Diameter
end TorusLumps
end YangMills.Construction
end
