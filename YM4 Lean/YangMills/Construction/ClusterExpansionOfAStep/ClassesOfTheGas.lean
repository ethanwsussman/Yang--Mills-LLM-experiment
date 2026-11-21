import YangMills.Construction.ClusterExpansionOfAStep.GasOfASetting
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion ENNReal
open MeasureTheory
namespace YangMills.Construction
open BlockAverages TorusFields TorusLumps StepGas StepSettings StepCosts LumpContours ColdStepAtMirrorFrames Dobrushin
variable {R : StepSetup} {n : ℕ}
theorem TorusLumps.supDist_le_of_parentBlock_eq [NeZero n] (L : ℕ) [NeZero L] {p q : TorusSite (n * L)}
    (h : parentBlock L p = parentBlock L q) : supDist p q ≤ L := by
  have hL : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  have hL' : (0 : ℤ) < L := by exact_mod_cast hL
  rw [supDist_le_iff]
  intro i
  have hi := congrFun h i
  set cp : ℤ := ((p i).cast : ℤ) with hcp
  set cq : ℤ := ((q i).cast : ℤ) with hcq
  set e : ℤ := ((L : ℤ) - 1) / 2
  have hi' : (((cp + e) / (L : ℤ) : ℤ) : ZMod n) = (((cq + e) / (L : ℤ) : ℤ) : ZMod n) := hi
  obtain ⟨k, hk⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp hi'
  have h1 := Int.emod_add_mul_ediv (cp + e) L
  have h2 := Int.emod_add_mul_ediv (cq + e) L
  have h3 := Int.emod_nonneg (cp + e) hL'.ne'
  have h4 := Int.emod_lt_of_pos (cp + e) hL'
  have h5 := Int.emod_nonneg (cq + e) hL'.ne'
  have h6 := Int.emod_lt_of_pos (cq + e) hL'
  set a := (cp + e) / (L : ℤ)
  set a' := (cq + e) / (L : ℤ)
  set r := (cp + e) % (L : ℤ)
  set r' := (cq + e) % (L : ℤ)
  have hdiff : p i - q i = ((r - r' : ℤ) : ZMod (n * L)) := by
    have hcpz : ((cp : ℤ) : ZMod (n * L)) = p i := ZMod.intCast_zmod_cast _
    have hcqz : ((cq : ℤ) : ZMod (n * L)) = q i := ZMod.intCast_zmod_cast _
    rw [← hcpz, ← hcqz, ← Int.cast_sub]
    have : cp - cq = (r - r') + ((n * L : ℕ) : ℤ) * (-k) := by
      push_cast
      have e1 : cp - cq = (r - r') + (L : ℤ) * (a - a') := by linarith [mul_sub (L : ℤ) a a']
      have e2 : a - a' = -((n : ℤ) * k) := by linarith
      rw [e1, e2]
      ring
    rw [this, Int.cast_add, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self]
    simp
  rw [hdiff]
  refine (natAbs_valMinAbs_intCast_le _).trans ?_
  omega
section GasFamilies
variable [NeZero n]
theorem StepGas.GasSupport.mem_core {θ : GasSupport R n} {y : TorusSite n} :
    y ∈ θ.core ↔ ∃ p : TorusSite (n * R.params.side), parentBlock R.params.side p = y ∧
      ∃ z ∈ θ.sites, supDist p z ≤ 4 * R.range := by
  classical
  unfold GasSupport.core supportCore coreBlocks
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨p, hp⟩
    obtain ⟨h1, h2⟩ := Finset.mem_inter.mp hp
    obtain ⟨z, hz, hpz⟩ := (mem_thickening _ _ _).mp h2
    exact ⟨p, by simpa [sitesInBlocks] using h1, z, hz, hpz⟩
  · rintro ⟨p, hp, z, hz, hpz⟩
    exact ⟨p, Finset.mem_inter.mpr ⟨by simpa [sitesInBlocks] using hp, (mem_thickening _ _ _).mpr ⟨z, hz, hpz⟩⟩⟩
theorem StepGas.GasSupport.parentBlock_mem_core {θ : GasSupport R n} {z : TorusSite (n * R.params.side)}
    (hz : z ∈ θ.sites) : parentBlock R.params.side z ∈ θ.core :=
  GasSupport.mem_core.mpr ⟨z, rfl, z, hz, by simp [supDist_self]⟩
theorem StepGas.GasSupport.FarApart.false_of_mem_cores {θ θ' : GasSupport R n} (h : θ.FarApart θ')
    (hr : R.params.side ≤ 2 * R.range) {y : TorusSite n}
    (hy : y ∈ θ.core) (hy' : y ∈ θ'.core) : False := by
  obtain ⟨p, hp, z, hz, hpz⟩ := GasSupport.mem_core.mp hy
  obtain ⟨p', hp', z', hz', hpz'⟩ := GasSupport.mem_core.mp hy'
  have h1 := h z hz z' hz'
  have h2 : supDist p p' ≤ R.params.side := supDist_le_of_parentBlock_eq _ (hp.trans hp'.symm)
  have h3 := supDist_triangle z p z'
  have h4 := supDist_triangle p p' z'
  rw [supDist_comm z p] at h3
  omega
def StepGas.GasFamily.CoresDisjoint (γ : GasFamily R n) : Prop :=
  ∀ θ θ', γ.Occupies θ → γ.Occupies θ' → ∀ y, y ∈ θ.core → y ∈ θ'.core → θ = θ'
open Classical in
def StepGas.GasFamily.insertClass (γ : GasFamily R n) (θ : GasSupport R n) (s : SupportState θ) :
    GasFamily R n :=
  Function.update γ θ (Sum.inr s)
variable {γ : GasFamily R n} {θ : GasSupport R n} {s : SupportState θ}
theorem StepGas.GasFamily.occupies_insertClass {θ' : GasSupport R n} :
    (γ.insertClass θ s).Occupies θ' ↔ θ' = θ ∨ γ.Occupies θ' := by
  classical
  by_cases h : θ' = θ
  · subst h
    simp [GasFamily.insertClass, GasFamily.Occupies]
  · simp [GasFamily.insertClass, GasFamily.Occupies, h]
theorem StepGas.GasFamily.insertClass_apply_of_ne {θ' : GasSupport R n} (h : θ' ≠ θ) :
    (γ.insertClass θ s) θ' = γ θ' := by
  classical
  simp [GasFamily.insertClass, Function.update_of_ne h]
theorem StepGas.GasFamily.state_insertClass_self (h : (γ.insertClass θ s).Occupies θ) :
    (γ.insertClass θ s).state h = s := by
  classical
  simp [GasFamily.state, GasFamily.insertClass]
theorem StepGas.GasFamily.state_insertClass_of_ne {θ' : GasSupport R n} (hne : θ' ≠ θ)
    (h : (γ.insertClass θ s).Occupies θ') (h' : γ.Occupies θ') :
    (γ.insertClass θ s).state h = γ.state h' := by
  classical
  simp only [GasFamily.state]
  congr 1
  exact GasFamily.insertClass_apply_of_ne hne
theorem StepGas.GasFamily.state_link_congr (γ' : GasFamily R n) {θ₁ θ₂ : GasSupport R n} (e : θ₁ = θ₂)
    (h₁ : γ'.Occupies θ₁) (h₂ : γ'.Occupies θ₂) {b : TorusBond (n * R.params.side)}
    (hb₁ : b ∈ θ₁.coreBonds) (hb₂ : b ∈ θ₂.coreBonds) :
    (γ'.state h₁).1 ⟨b, hb₁⟩ = (γ'.state h₂).1 ⟨b, hb₂⟩ := by
  subst e
  rfl
theorem StepGas.GasFamily.state_label_congr (γ' : GasFamily R n) {θ₁ θ₂ : GasSupport R n} (e : θ₁ = θ₂)
    (h₁ : γ'.Occupies θ₁) (h₂ : γ'.Occupies θ₂) {z : TorusSite (n * R.params.side)}
    (hb₁ : z ∈ θ₁.2) (hb₂ : z ∈ θ₂.2) :
    (γ'.state h₁).2.1 ⟨z, hb₁⟩ = (γ'.state h₂).2.1 ⟨z, hb₂⟩ := by
  subst e
  rfl
theorem StepGas.GasFamily.state_base_congr (γ' : GasFamily R n) {θ₁ θ₂ : GasSupport R n} (e : θ₁ = θ₂)
    (h₁ : γ'.Occupies θ₁) (h₂ : γ'.Occupies θ₂) {y : TorusSite n} (hb₁ : y ∈ θ₁.core) (hb₂ : y ∈ θ₂.core) :
    (γ'.state h₁).2.2 ⟨y, hb₁⟩ = (γ'.state h₂).2.2 ⟨y, hb₂⟩ := by
  subst e
  rfl
theorem StepGas.GasSupport.parentBlock_mem_core_of_mem_coreBonds {θ' : GasSupport R n}
    {b : TorusBond (n * R.params.side)} (hb : b ∈ θ'.coreBonds) :
    parentBlock R.params.side b.1 ∈ θ'.core := by
  classical
  exact (Finset.mem_filter.mp hb).2.1
theorem StepGas.GasSupport.parentBlock_mem_core_of_mem_sites {θ' : GasSupport R n}
    {z : TorusSite (n * R.params.side)} (hz : z ∈ θ'.2) :
    parentBlock R.params.side z ∈ θ'.core :=
  GasSupport.parentBlock_mem_core (Finset.mem_union_right _ hz)
theorem StepGas.GasFamily.CoresDisjoint.insertClass (hs : γ.CoresDisjoint)
    (hc : ∀ θ', γ.Occupies θ' → ∀ y, y ∈ θ.core → y ∈ θ'.core → False) :
    (γ.insertClass θ s).CoresDisjoint := by
  intro θ₁ θ₂ h₁ h₂ y hy₁ hy₂
  rcases GasFamily.occupies_insertClass.mp h₁ with e₁ | g₁
  · rcases GasFamily.occupies_insertClass.mp h₂ with e₂ | g₂
    · rw [e₁, e₂]
    · exact (hc _ g₂ y (e₁ ▸ hy₁) hy₂).elim
  · rcases GasFamily.occupies_insertClass.mp h₂ with e₂ | g₂
    · exact (hc _ g₁ y (e₂ ▸ hy₂) hy₁).elim
    · exact hs _ _ g₁ g₂ y hy₁ hy₂
open Classical in
theorem StepGas.GasFamily.fieldAt_insertClass (hs : γ.CoresDisjoint)
    (hc : ∀ θ', γ.Occupies θ' → ∀ y, y ∈ θ.core → y ∈ θ'.core → False) (b : TorusBond (n * R.params.side)) :
    (γ.insertClass θ s).fieldAt b =
      if h : b ∈ θ.coreBonds then Sum.inr (s.1 ⟨b, h⟩) else γ.fieldAt b := by
  have hs' : (γ.insertClass θ s).CoresDisjoint := hs.insertClass hc
  have hself : (γ.insertClass θ s).Occupies θ := GasFamily.occupies_insertClass.mpr (Or.inl rfl)
  unfold GasFamily.fieldAt
  by_cases hb : b ∈ θ.coreBonds
  · have hex : ∃ θ', (γ.insertClass θ s).Occupies θ' ∧ b ∈ θ'.coreBonds := ⟨θ, hself, hb⟩
    rw [dif_pos hex, dif_pos hb]
    have he : hex.choose = θ := hs' _ _ hex.choose_spec.1 hself _
      (GasSupport.parentBlock_mem_core_of_mem_coreBonds hex.choose_spec.2)
      (GasSupport.parentBlock_mem_core_of_mem_coreBonds hb)
    have := GasFamily.state_link_congr (γ.insertClass θ s) he hex.choose_spec.1 hself hex.choose_spec.2 hb
    rw [this, GasFamily.state_insertClass_self]
  · rw [dif_neg hb]
    by_cases hex : ∃ θ', γ.Occupies θ' ∧ b ∈ θ'.coreBonds
    · have hex' : ∃ θ', (γ.insertClass θ s).Occupies θ' ∧ b ∈ θ'.coreBonds := by
        obtain ⟨θ', h1, h2⟩ := hex
        exact ⟨θ', GasFamily.occupies_insertClass.mpr (Or.inr h1), h2⟩
      rw [dif_pos hex', dif_pos hex]
      have hne : hex'.choose ≠ θ := fun e => hb (e ▸ hex'.choose_spec.2)
      have hold : γ.Occupies hex'.choose :=
        (GasFamily.occupies_insertClass.mp hex'.choose_spec.1).resolve_left hne
      have he : hex'.choose = hex.choose := hs _ _ hold hex.choose_spec.1 _
        (GasSupport.parentBlock_mem_core_of_mem_coreBonds hex'.choose_spec.2)
        (GasSupport.parentBlock_mem_core_of_mem_coreBonds hex.choose_spec.2)
      rw [GasFamily.state_insertClass_of_ne hne hex'.choose_spec.1 hold]
      rw [GasFamily.state_link_congr γ he hold hex.choose_spec.1 hex'.choose_spec.2 hex.choose_spec.2]
    · have hex' : ¬ ∃ θ', (γ.insertClass θ s).Occupies θ' ∧ b ∈ θ'.coreBonds := by
        rintro ⟨θ', h1, h2⟩
        rcases GasFamily.occupies_insertClass.mp h1 with rfl | h1
        · exact hb h2
        · exact hex ⟨θ', h1, h2⟩
      rw [dif_neg hex', dif_neg hex]
open Classical in
theorem StepGas.GasFamily.sites_insertClass : (γ.insertClass θ s).sites = γ.sites ∪ θ.2 := by
  ext z
  unfold GasFamily.sites
  simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
  constructor
  · rintro ⟨θ', h, hz⟩
    rcases GasFamily.occupies_insertClass.mp h with rfl | h
    · exact Or.inr hz
    · exact Or.inl ⟨θ', h, hz⟩
  · rintro (⟨θ', h, hz⟩ | hz)
    · exact ⟨θ', GasFamily.occupies_insertClass.mpr (Or.inr h), hz⟩
    · exact ⟨θ, GasFamily.occupies_insertClass.mpr (Or.inl rfl), hz⟩
theorem StepGas.GasFamily.labelAt_eq_of_mem (γ' : GasFamily R n) (hs : γ'.CoresDisjoint)
    {z : TorusSite (n * R.params.side)} (h : z ∈ γ'.sites)
    {θ' : GasSupport R n} (hθ : γ'.Occupies θ') (hz : z ∈ θ'.2) :
    γ'.labelAt h = (γ'.state hθ).2.1 ⟨z, hz⟩ := by
  unfold GasFamily.labelAt
  exact GasFamily.state_label_congr γ' (hs _ _ (GasFamily.exists_of_mem_sites h).choose_spec.1 hθ _
    (GasSupport.parentBlock_mem_core_of_mem_sites (GasFamily.exists_of_mem_sites h).choose_spec.2)
    (GasSupport.parentBlock_mem_core_of_mem_sites hz)) _ hθ _ hz
open Classical in
theorem StepGas.GasFamily.baseAt_insertClass (hs : γ.CoresDisjoint)
    (hc : ∀ θ', γ.Occupies θ' → ∀ y, y ∈ θ.core → y ∈ θ'.core → False) (y : TorusSite n) :
    (γ.insertClass θ s).baseAt y = if h : y ∈ θ.core then Sum.inr (s.2.2 ⟨y, h⟩) else γ.baseAt y := by
  have hs' : (γ.insertClass θ s).CoresDisjoint := hs.insertClass hc
  have hself : (γ.insertClass θ s).Occupies θ := GasFamily.occupies_insertClass.mpr (Or.inl rfl)
  unfold GasFamily.baseAt
  by_cases hb : y ∈ θ.core
  · have hex : ∃ θ', (γ.insertClass θ s).Occupies θ' ∧ y ∈ θ'.core := ⟨θ, hself, hb⟩
    rw [dif_pos hex, dif_pos hb]
    have he : hex.choose = θ := hs' _ _ hex.choose_spec.1 hself _ hex.choose_spec.2 hb
    rw [GasFamily.state_base_congr (γ.insertClass θ s) he hex.choose_spec.1 hself hex.choose_spec.2 hb,
      GasFamily.state_insertClass_self]
  · rw [dif_neg hb]
    by_cases hex : ∃ θ', γ.Occupies θ' ∧ y ∈ θ'.core
    · have hex' : ∃ θ', (γ.insertClass θ s).Occupies θ' ∧ y ∈ θ'.core := by
        obtain ⟨θ', h1, h2⟩ := hex
        exact ⟨θ', GasFamily.occupies_insertClass.mpr (Or.inr h1), h2⟩
      rw [dif_pos hex', dif_pos hex]
      have hne : hex'.choose ≠ θ := fun e => hb (e ▸ hex'.choose_spec.2)
      have hold : γ.Occupies hex'.choose :=
        (GasFamily.occupies_insertClass.mp hex'.choose_spec.1).resolve_left hne
      have he : hex'.choose = hex.choose := hs _ _ hold hex.choose_spec.1 _
        hex'.choose_spec.2 hex.choose_spec.2
      rw [GasFamily.state_insertClass_of_ne hne hex'.choose_spec.1 hold]
      rw [GasFamily.state_base_congr γ he hold hex.choose_spec.1 hex'.choose_spec.2 hex.choose_spec.2]
    · have hex' : ¬ ∃ θ', (γ.insertClass θ s).Occupies θ' ∧ y ∈ θ'.core := by
        rintro ⟨θ', h1, h2⟩
        rcases GasFamily.occupies_insertClass.mp h1 with rfl | h1
        · exact hb h2
        · exact hex ⟨θ', h1, h2⟩
      rw [dif_neg hex', dif_neg hex]
end GasFamilies
section FrameField
variable [NeZero n]
def StepSettings.frameField (R : StepSetup) (free : Finset (TorusBond (n * R.params.side)))
    (V : TorusField n) (B : TorusField (n * R.params.side)) : TorusField (n * R.params.side) :=
  open Classical in fun x i =>
    if (x, i) ∈ free then
      (gaugeAt (R := R) B x)⁻¹ *
        (if IsCrossingBond (F := stepBlockFrame R.params.side n)
            (torusSiteInFrame (stepBlockFrame R.params.side n) 0 x, i)
          then expUnit (frameCoord R.params R.anchorRadius R.depth R.frameReach V (x, i) + toImaginary 0) *
            V (parentBlock R.params.side x) i
          else expUnit (frameCoord R.params R.anchorRadius R.depth R.frameReach V (x, i) + toImaginary 0)) *
        gaugeAt (R := R) B (x + TorusFields.unitStep (n * R.params.side) i)
    else B x i
omit [NeZero n] in
theorem StepSettings.ChartSetting.field_zero (c : ChartSetting R n) :
    c.field 0 = frameField R c.free c.coarse c.fine := by
  classical
  funext x i
  unfold ChartSetting.field frameField
  by_cases h : (x, i) ∈ c.free
  · simp only [dif_pos h, if_pos h]
    rfl
  · simp only [dif_neg h, if_neg h]
omit [NeZero n] in
theorem BlockAverages.continuous_pathHolonomy_readAtLevel (F : BlockFrame) (j : ℕ) (steps : List PathStep) :
    ∀ x : F.Site j, Continuous fun W : TorusField n => pathHolonomy (readAtLevel F j W) x steps := by
  induction steps with
  | nil => intro x; exact continuous_const
  | cons st rest ih =>
    intro x
    have h1 : Continuous fun W : TorusField n => linkValue (readAtLevel F j W) x st := by
      unfold linkValue readAtLevel
      by_cases hst : st.2 = true
      · simp only [hst, if_true]
        exact continuous_apply_apply _ _
      · simp only [hst]
        exact (continuous_apply_apply _ _).inv
    exact h1.mul (ih _)
omit [NeZero n] in
theorem StepSettings.continuous_gaugeAt (x : TorusSite (n * R.params.side)) :
    Continuous fun B : TorusField (n * R.params.side) => gaugeAt (R := R) B x := by
  unfold gaugeAt axialGauge
  exact continuous_pathHolonomy_readAtLevel _ _ _ _
omit [NeZero n] in
theorem StepSettings.continuous_frameField (free : Finset (TorusBond (n * R.params.side))) (V : TorusField n) :
    Continuous (frameField R free V) := by
  classical
  refine continuous_pi fun x => continuous_pi fun i => ?_
  unfold frameField
  by_cases h : (x, i) ∈ free
  · simp only [if_pos h]
    exact ((continuous_gaugeAt x).inv.mul continuous_const).mul (continuous_gaugeAt _)
  · simp only [if_neg h]
    exact continuous_apply_apply _ _
end FrameField
section FamilySettings
variable [NeZero n] (G : GasGround R n) {γ : GasFamily R n} {θ : GasSupport R n}
open Classical in
def StepGas.GasGround.baseWithClass (G : GasGround R n) (γ : GasFamily R n) (θ : GasSupport R n)
    (a : θ.coreBonds → UnitQuaternion) : TorusField (n * R.params.side) :=
  fun x i => if h : (x, i) ∈ θ.coreBonds then a ⟨(x, i), h⟩ else (G.settingWithFamily γ).fine x i
theorem StepGas.continuous_baseWithClass : Continuous (G.baseWithClass γ θ) := by
  classical
  refine continuous_pi fun x => continuous_pi fun i => ?_
  unfold GasGround.baseWithClass
  by_cases h : (x, i) ∈ θ.coreBonds
  · simp only [dif_pos h]
    exact continuous_apply _
  · simp only [dif_neg h]
    exact continuous_const
variable (s : SupportState θ)
theorem StepGas.GasGround.settingWithFamily_fine_insertClass (hs : γ.CoresDisjoint)
    (hc : ∀ θ', γ.Occupies θ' → ∀ y, y ∈ θ.core → y ∈ θ'.core → False) :
    (G.settingWithFamily (γ.insertClass θ s)).fine = G.baseWithClass γ θ s.1 := by
  classical
  funext x i
  unfold GasGround.baseWithClass
  have h := GasFamily.fieldAt_insertClass (s := s) hs hc (x, i)
  show (match (γ.insertClass θ s).fieldAt (x, i) with
    | Sum.inr g => g
    | Sum.inl _ => G.state.fieldWithStoredLinks (trivialField _) x i) = _
  rw [h]
  by_cases hb : (x, i) ∈ θ.coreBonds
  · simp only [dif_pos hb]
  · simp only [dif_neg hb]
    rfl
open Classical in
theorem StepGas.GasGround.settingWithFamily_free_insertClass (hs : γ.CoresDisjoint)
    (hc : ∀ θ', γ.Occupies θ' → ∀ y, y ∈ θ.core → y ∈ θ'.core → False) :
    (G.settingWithFamily (γ.insertClass θ s)).free =
      (G.settingWithFamily γ).free.filter fun b => b ∉ θ.coreBonds := by
  ext b
  have h := GasFamily.fieldAt_insertClass (s := s) hs hc b
  show b ∈ G.freeBonds.filter (fun b => (γ.insertClass θ s).fieldAt b = Sum.inl ()) ↔
    b ∈ (G.freeBonds.filter fun b => γ.fieldAt b = Sum.inl ()).filter fun b => b ∉ θ.coreBonds
  simp only [Finset.mem_filter, h]
  by_cases hb : b ∈ θ.coreBonds
  · simp [hb]
  · simp [hb]
theorem StepGas.GasGround.field_zero_insertClass (hs : γ.CoresDisjoint)
    (hc : ∀ θ', γ.Occupies θ' → ∀ y, y ∈ θ.core → y ∈ θ'.core → False) :
    (G.settingOf (γ.insertClass θ s)).field 0 =
      StepSettings.frameField R (G.settingWithFamily (γ.insertClass θ s)).free G.coarse
        (StepSettings.frameField R (G.settingWithFamily (γ.insertClass θ s)).free G.coarse
          (G.baseWithClass γ θ s.1)) := by
  rw [ChartSetting.field_zero]
  show StepSettings.frameField R (G.settingWithFamily (γ.insertClass θ s)).free G.coarse
    ((G.settingWithFamily (γ.insertClass θ s)).field 0) = _
  rw [ChartSetting.field_zero]
  show _ = StepSettings.frameField R _ G.coarse (StepSettings.frameField R _ G.coarse _)
  congr 2
  exact G.settingWithFamily_fine_insertClass s hs hc
end FamilySettings
section Neighbourhoods
variable [NeZero n]
open Classical in
def TorusFields.sitesNear (r : ℕ) (X : Finset (TorusSite n)) : Finset (TorusSite n) :=
  Finset.univ.filter fun y => ∃ z ∈ X, (supDist y z : ℝ) < (r : ℝ) / 4
def StepSettings.ChartSetting.densityNear (c : ChartSetting R n) (X : Finset (TorusSite (n * R.params.side))) : ℝ :=
  ∑ y ∈ sitesNear R.range X, R.siteDensity (n * R.params.side) y (c.field 0) c.support c.labelling
open Classical in
def TorusLumps.hotLumpsWithin (ℓ : StepParameters) (W : TorusField (n * ℓ.side))
    (X : Finset (TorusSite (n * ℓ.side))) : Finset (Finset (TorusSite (n * ℓ.side))) :=
  (torusHotLumps ℓ W).filter (· ⊆ X)
variable (G : GasGround R n)
open Classical in
theorem StepGas.GasGround.familyOf_update (σ : G.Config) (i : G.GasSpin) (v : G.SpinState i) :
    G.familyOf (Function.update σ i (Sum.inr v)) = (G.familyOf σ).insertClass i.1 v.1 := by
  funext θ
  by_cases h : θ = i.1
  · subst h
    have : (⟨i.1, i.2⟩ : G.GasSpin) = i := rfl
    simp [GasGround.familyOf, GasFamily.insertClass, i.2]
  · have hne := GasFamily.insertClass_apply_of_ne (γ := G.familyOf σ) (s := v.1) h
    rw [hne]
    unfold GasGround.familyOf
    by_cases hθ : G.IsGasSupport θ
    · have hi : (⟨θ, hθ⟩ : G.GasSpin) ≠ i := fun e => h (congrArg Subtype.val e)
      simp only [dif_pos hθ, Function.update_of_ne hi]
    · simp only [dif_neg hθ]
open Classical in
theorem StepGas.GasGround.exists_spin_of_occupies {σ : G.Config} {θ : GasSupport R n}
    (h : (G.familyOf σ).Occupies θ) : ∃ j : G.GasSpin, j.1 = θ ∧ σ j ≠ Sum.inl () := by
  unfold GasFamily.Occupies GasGround.familyOf at h
  by_cases hθ : G.IsGasSupport θ
  · rw [dif_pos hθ] at h
    refine ⟨⟨θ, hθ⟩, rfl, fun e => ?_⟩
    rw [e] at h
    simp at h
  · rw [dif_neg hθ] at h
    simp at h
theorem StepGas.GasGround.coresDisjoint_familyOf {σ : G.Config} (hadm : G.pairConstraint.IsAdmissible σ)
    (hr : R.params.side ≤ 2 * R.range) : (G.familyOf σ).CoresDisjoint := by
  intro θ θ' h h' y hy hy'
  obtain ⟨j, rfl, hj⟩ := G.exists_spin_of_occupies h
  obtain ⟨j', rfl, hj'⟩ := G.exists_spin_of_occupies h'
  by_contra hne
  have hjj : j ≠ j' := fun e => hne (congrArg Subtype.val e)
  rcases hadm j j' hjj with e | e | e
  · exact hj e
  · exact hj' e
  · exact e.false_of_mem_cores hr hy hy'
end Neighbourhoods
end YangMills.Construction
end
