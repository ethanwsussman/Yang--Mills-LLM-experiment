import YangMills.Construction.ClusterExpansionOfAStep.InnerSupportsWithTheirCoresProof
import YangMills.Construction.ClusterExpansionOfAStep.StatesOfSharedCores
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.ClusterExpansionOfAStep
open BlockAverages TorusFields TorusLumps StepSettings StepGas BlockOffsets
namespace SharedCores
theorem exists_equiv_subtype_of_rel {α β : Type} {P : α → Prop} {Q : β → Prop} (r : α → β → Prop)
    (hex : ∀ a, P a → ∃ b, Q b ∧ r a b) (hex' : ∀ b, Q b → ∃ a, P a ∧ r a b)
    (huniq : ∀ a b b', P a → Q b → Q b' → r a b → r a b' → b = b')
    (huniq' : ∀ a a' b, P a → P a' → Q b → r a b → r a' b → a = a') :
    ∃ e : {a // P a} ≃ {b // Q b}, ∀ a, r a.1 (e a).1 := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.InnerSupports.exists_equiv_of_bijective_relation <;> assumption
theorem measurePreserving_count_of_measurableEquiv {α β : Type} [MeasurableSpace α] [MeasurableSpace β]
    (g : α ≃ᵐ β) : MeasurePreserving g Measure.count Measure.count := by
  refine ⟨g.measurable, ?_⟩
  ext t ht
  have e : (g ⁻¹' t) = g.symm '' t := by
    ext x
    constructor
    · intro hx
      exact ⟨g x, hx, by simp⟩
    · rintro ⟨b, hb, rfl⟩
      simpa using hb
  rw [Measure.map_apply g.measurable ht, Measure.count_apply ht, Measure.count_apply (g.measurable ht), e,
    g.symm.injective.encard_image]
variable {L : ℕ} [NeZero L]
theorem exists_parentBlock_fineSite_add_unitStep (hodd : Odd L) (h o : Fin 4 → ℤ) (ho : o ∈ centredCube L)
    (i : Fin 4) :
    ∃ h₂ : Fin 4 → ℤ, (∀ l, |h₂ l - h l| ≤ 1) ∧ ∀ (k : ℕ) [NeZero k] (Z : TorusSite k),
      parentBlock L (fineSite L Z h o + TorusFields.unitStep (k * L) i) = Z + siteOfInt h₂ := by apply _root_.YangMills.Construction.InBoxTransfer.exists_parentBlock_add_unitStep <;> assumption
end SharedCores
open SharedCores in
theorem sharedCoreStatesEquiv_holds : SharedCoreStatesEquiv := by
  classical
  intro R n n' _ _ θ θ' Y Y' N hodd hn hn' hs hc
  have box_eq : ∀ {k : ℕ} [NeZero k] (Z : TorusSite k) {a b : Fin 4 → ℤ}, 2 * N + 2 < k → OffsetInBox N a →
      OffsetInBox N b → Z + siteOfInt a = Z + siteOfInt b → a = b := by
    intro k _ Z a b hk ha hb e
    exact SettingShifts.eq_of_siteOfInt_eq hk ha hb (add_left_cancel e)
  obtain ⟨e3, he3⟩ := exists_equiv_subtype_of_rel (P := fun y => y ∈ θ.core) (Q := fun y' => y' ∈ θ'.core)
    (fun y y' => ∃ h, OffsetInBox N h ∧ y = Y + siteOfInt h ∧ y' = Y' + siteOfInt h)
    (fun y hy => by
      obtain ⟨h, hh, rfl⟩ := hs.core_mem y hy
      exact ⟨_, (hc h hh).1 hy, h, hh, rfl, rfl⟩)
    (fun y' hy => by
      obtain ⟨h, hh, rfl⟩ := hs.core_mem' y' hy
      exact ⟨_, (hc h hh).2 hy, h, hh, rfl, rfl⟩)
    (by
      rintro _ _ _ _ _ _ ⟨h, hh, rfl, rfl⟩ ⟨h', hh', e, rfl⟩
      rw [box_eq Y hn hh hh' e])
    (by
      rintro _ _ _ _ _ _ ⟨h, hh, rfl, rfl⟩ ⟨h', hh', rfl, e⟩
      rw [box_eq Y' hn' hh hh' e])
  have near_eq : ∀ {k : ℕ} [NeZero k] (Z : TorusSite k), 2 * N + 2 < k → ∀ {a b o o' : Fin 4 → ℤ},
      OffsetInBox N a → OffsetInBox N b → o ∈ centredCube R.params.side → o' ∈ centredCube R.params.side →
      (fineSite R.params.side Z a o : TorusSite (k * R.params.side)) = fineSite R.params.side Z b o' →
        a = b ∧ o = o' := by
    intro k _ Z hk a b o o' ha hb ho ho' e
    have e1 := congrArg (parentBlock R.params.side) e
    rw [parentBlock_fineSite hodd Z a o ho, parentBlock_fineSite hodd Z b o' ho'] at e1
    have hab := box_eq Z hk ha hb e1
    subst hab
    exact ⟨rfl, fineSite_injective Z a hodd ho ho' e⟩
  have fine_of : ∀ {k : ℕ} [NeZero k] (Z : TorusSite k) (z : TorusSite (k * R.params.side)) (h : Fin 4 → ℤ),
      parentBlock R.params.side z = Z + siteOfInt h →
        ∃ o ∈ centredCube R.params.side, z = fineSite R.params.side Z h o := by
    intro k _ Z z h e
    obtain ⟨o, ho, hz⟩ := exists_fineSite_of_parentBlock hodd _ z e
    refine ⟨o, ho, ?_⟩
    rw [hz, SettingShifts.fineSite_add_siteOfInt, add_zero]
  obtain ⟨e2, he2⟩ := exists_equiv_subtype_of_rel (P := fun z => z ∈ θ.2) (Q := fun z' => z' ∈ θ'.2)
    (fun z z' => ∃ h o, OffsetInBox N h ∧ o ∈ centredCube R.params.side ∧ z = fineSite R.params.side Y h o ∧
      z' = fineSite R.params.side Y' h o)
    (fun z hz => by
      obtain ⟨h, hh, e⟩ := hs.core_mem _ (GasSupport.parentBlock_mem_core_of_mem_sites hz)
      obtain ⟨o, ho, rfl⟩ := fine_of Y z h e
      exact ⟨_, (hs.sites_iff h o hh ho).1 hz, h, o, hh, ho, rfl, rfl⟩)
    (fun z' hz => by
      obtain ⟨h, hh, e⟩ := hs.core_mem' _ (GasSupport.parentBlock_mem_core_of_mem_sites hz)
      obtain ⟨o, ho, rfl⟩ := fine_of Y' z' h e
      exact ⟨_, (hs.sites_iff h o hh ho).2 hz, h, o, hh, ho, rfl, rfl⟩)
    (by
      rintro _ _ _ _ _ _ ⟨h, o, hh, ho, rfl, rfl⟩ ⟨h', o', hh', ho', e, rfl⟩
      obtain ⟨rfl, rfl⟩ := near_eq Y hn hh hh' ho ho' e
      rfl)
    (by
      rintro _ _ _ _ _ _ ⟨h, o, hh, ho, rfl, rfl⟩ ⟨h', o', hh', ho', rfl, e⟩
      obtain ⟨rfl, rfl⟩ := near_eq Y' hn' hh hh' ho ho' e
      rfl)
  have bonds_iff : ∀ q, IsNearIndex R.params.side N q →
      (nearBond R.params.side Y q ∈ θ.coreBonds ↔ nearBond R.params.side Y' q ∈ θ'.coreBonds) := by
    rintro ⟨h, o, i⟩ ⟨hh, ho⟩
    obtain ⟨h₂, hd, hb⟩ := exists_parentBlock_fineSite_add_unitStep hodd h o ho i
    have hh₂ : ∀ {k : ℕ} [NeZero k] (Z : TorusSite k) {a : Fin 4 → ℤ}, 2 * N + 2 < k → OffsetInBox N a →
        Z + siteOfInt h₂ = Z + siteOfInt a → h₂ = a := by
      intro k _ Z a hk ha e
      refine TorusLumps.eq_of_siteOfInt_eq (n := k) (add_left_cancel e) fun l => ?_
      have a1 := abs_le.1 (hd l)
      have a2 := abs_le.1 ((show OffsetInBox N h from hh) l)
      have a3 := abs_le.1 (ha l)
      rw [abs_lt]
      constructor <;> omega
    have hmem : ∀ {k : ℕ} [NeZero k] (ϑ : GasSupport R k) (b : TorusBond (k * R.params.side)),
        b ∈ ϑ.coreBonds ↔ parentBlock R.params.side b.1 ∈ ϑ.core ∧
          parentBlock R.params.side (b.1 + TorusFields.unitStep (k * R.params.side) b.2) ∈ ϑ.core := by
      intro k _ ϑ b
      unfold GasSupport.coreBonds
      simp
    rw [hmem θ, hmem θ']
    simp only [nearBond]
    rw [parentBlock_fineSite hodd Y h o ho, parentBlock_fineSite hodd Y' h o ho, hb n Y, hb n' Y', hc h hh]
    refine and_congr_right fun _ => ⟨fun hy => ?_, fun hy => ?_⟩
    · obtain ⟨a, ha, e⟩ := hs.core_mem _ hy
      have := hh₂ Y hn ha e
      subst this
      exact (hc _ ha).1 hy
    · obtain ⟨a, ha, e⟩ := hs.core_mem' _ hy
      have := hh₂ Y' hn' ha e
      subst this
      exact (hc _ ha).2 hy
  obtain ⟨e1, he1⟩ := exists_equiv_subtype_of_rel (P := fun b => b ∈ θ.coreBonds)
    (Q := fun b' => b' ∈ θ'.coreBonds)
    (fun b b' => ∃ q, IsNearIndex R.params.side N q ∧ b = nearBond R.params.side Y q ∧
      b' = nearBond R.params.side Y' q)
    (fun b hb => by
      obtain ⟨h, hh, e⟩ := hs.core_mem _ (GasSupport.parentBlock_mem_core_of_mem_coreBonds hb)
      obtain ⟨o, ho, hz⟩ := fine_of Y b.1 h e
      have hq : b = nearBond R.params.side Y (h, o, b.2) := Prod.ext hz rfl
      exact ⟨_, (bonds_iff (h, o, b.2) ⟨hh, ho⟩).1 (hq ▸ hb), (h, o, b.2), ⟨hh, ho⟩, hq, rfl⟩)
    (fun b' hb => by
      obtain ⟨h, hh, e⟩ := hs.core_mem' _ (GasSupport.parentBlock_mem_core_of_mem_coreBonds hb)
      obtain ⟨o, ho, hz⟩ := fine_of Y' b'.1 h e
      have hq : b' = nearBond R.params.side Y' (h, o, b'.2) := Prod.ext hz rfl
      exact ⟨_, (bonds_iff (h, o, b'.2) ⟨hh, ho⟩).2 (hq ▸ hb), (h, o, b'.2), ⟨hh, ho⟩, rfl, hq⟩)
    (by
      rintro _ _ _ _ _ _ ⟨⟨h, o, i⟩, ⟨hh, ho⟩, rfl, rfl⟩ ⟨⟨h', o', i'⟩, ⟨hh', ho'⟩, e, rfl⟩
      have e1 : fineSite R.params.side Y h o = fineSite R.params.side Y h' o' := congrArg Prod.fst e
      have e2 : i = i' := congrArg Prod.snd e
      obtain ⟨rfl, rfl⟩ := near_eq Y hn hh hh' ho ho' e1
      rw [e2])
    (by
      rintro _ _ _ _ _ _ ⟨⟨h, o, i⟩, ⟨hh, ho⟩, rfl, rfl⟩ ⟨⟨h', o', i'⟩, ⟨hh', ho'⟩, rfl, e⟩
      have e1 : fineSite R.params.side Y' h o = fineSite R.params.side Y' h' o' := congrArg Prod.fst e
      have e2 : i = i' := congrArg Prod.snd e
      obtain ⟨rfl, rfl⟩ := near_eq Y' hn' hh hh' ho ho' e1
      rw [e2])
  let f₁ := MeasurableEquiv.piCongrLeft (fun _ : θ'.coreBonds => UnitQuaternion) e1
  let f₂ := MeasurableEquiv.piCongrLeft (fun _ : θ'.2 => R.labels.Ω) e2
  let f₃ := MeasurableEquiv.piCongrLeft (fun _ : θ'.core => BlockOffset R.params.side) e3
  have hf₁ : ∀ (a : θ.coreBonds → UnitQuaternion) (b : θ.coreBonds), f₁ a (e1 b) = a b := fun a b =>
    Equiv.piCongrLeft_apply_apply (fun _ : θ'.coreBonds => UnitQuaternion) e1 a b
  have hf₂ : ∀ (a : θ.2 → R.labels.Ω) (b : θ.2), f₂ a (e2 b) = a b := fun a b =>
    Equiv.piCongrLeft_apply_apply (fun _ : θ'.2 => R.labels.Ω) e2 a b
  have hf₃ : ∀ (a : θ.core → BlockOffset R.params.side) (b : θ.core), f₃ a (e3 b) = a b := fun a b =>
    Equiv.piCongrLeft_apply_apply (fun _ : θ'.core => BlockOffset R.params.side) e3 a b
  refine ⟨f₁.prodCongr (f₂.prodCongr f₃), ?_, fun s => ?_⟩
  · have p₁ : MeasurePreserving f₁ (Measure.pi fun _ : θ.coreBonds => haarUnit)
        (Measure.pi fun _ : θ'.coreBonds => haarUnit) :=
      measurePreserving_piCongrLeft (fun _ : θ'.coreBonds => haarUnit) e1
    have p₂ : MeasurePreserving f₂ (Measure.pi fun _ : θ.2 => R.labels.μ)
        (Measure.pi fun _ : θ'.2 => R.labels.μ) :=
      measurePreserving_piCongrLeft (fun _ : θ'.2 => R.labels.μ) e2
    exact p₁.prod (p₂.prod (measurePreserving_count_of_measurableEquiv f₃))
  have hs₁ : (f₁.prodCongr (f₂.prodCongr f₃) s).1 = f₁ s.1 := rfl
  have hs₂ : (f₁.prodCongr (f₂.prodCongr f₃) s).2.1 = f₂ s.2.1 := rfl
  have hs₃ : (f₁.prodCongr (f₂.prodCongr f₃) s).2.2 = f₃ s.2.2 := rfl
  refine ⟨fun q hb hb' hq => ?_, fun h o hz hz' hh ho => ?_, fun h hy hy' hh => ?_⟩
  · have he : e1 ⟨_, hb⟩ = ⟨_, hb'⟩ := by
      obtain ⟨q', hq', e, e'⟩ := he1 ⟨_, hb⟩
      have e5 : q = q' := by
        obtain ⟨a, o, i⟩ := q
        obtain ⟨a', o', i'⟩ := q'
        have e6 : fineSite R.params.side Y a o = fineSite R.params.side Y a' o' := congrArg Prod.fst e
        have e7 : i = i' := congrArg Prod.snd e
        obtain ⟨rfl, rfl⟩ := near_eq Y hn hq.1 hq'.1 hq.2 hq'.2 e6
        rw [e7]
      subst e5
      exact Subtype.ext e'
    rw [hs₁, ← he, hf₁]
  · have he : e2 ⟨_, hz⟩ = ⟨_, hz'⟩ := by
      obtain ⟨a, o', ha, ho', e, e'⟩ := he2 ⟨_, hz⟩
      obtain ⟨rfl, rfl⟩ := near_eq Y hn hh ha ho ho' e
      exact Subtype.ext e'
    rw [hs₂, ← he, hf₂]
  · have he : e3 ⟨_, hy⟩ = ⟨_, hy'⟩ := by
      obtain ⟨a, ha, e, e'⟩ := he3 ⟨_, hy⟩
      have := box_eq Y hn hh ha e
      subst this
      exact Subtype.ext e'
    rw [hs₃, ← he, hf₃]
end YangMills.Construction.ClusterExpansionOfAStep
end
