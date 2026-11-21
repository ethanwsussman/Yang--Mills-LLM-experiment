import YangMills.Construction.ClusterExpansionOfAStep.HotLumpsOnACut
import YangMills.Construction.ClusterExpansionOfAStep.MatchingClasses
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace YangMills.Construction.CongruentBoxes
open TorusFields TorusLumps StepSettings
variable {n n' : ℕ} [NeZero n] [NeZero n'] {y : TorusSite n} {y' : TorusSite n'} {m : ℕ}
section Sets
variable {A B : Finset (TorusSite n)} {A' B' : Finset (TorusSite n')}
theorem congruentInBoxes_symm (h : CongruentInBoxes A A' y y' m) : CongruentInBoxes A' A y' y m :=
  ⟨h.2.1, h.1, fun a ha => (h.2.2 a ha).symm⟩
theorem eq_of_congruentInBoxes_of_congruentInBoxes {C : Finset (TorusSite n')}
    (h1 : CongruentInBoxes A B' y y' m) (h2 : CongruentInBoxes A C y y' m) : B' = C := by
  ext z
  constructor
  · intro hz
    obtain ⟨a, ha, rfl⟩ := h1.2.1 z hz
    exact (h2.2.2 a ha).mp ((h1.2.2 a ha).mpr hz)
  · intro hz
    obtain ⟨a, ha, rfl⟩ := h2.2.1 z hz
    exact (h1.2.2 a ha).mp ((h2.2.2 a ha).mpr hz)
theorem subset_of_congruentInBoxes (hA : CongruentInBoxes A A' y y' m) (hB : CongruentInBoxes B B' y y' m)
    (h : A ⊆ B) : A' ⊆ B' := by
  intro z hz
  obtain ⟨a, ha, rfl⟩ := hA.2.1 z hz
  exact (hB.2.2 a ha).mp (h ((hA.2.2 a ha).mpr hz))
theorem eq_of_congruentInBoxes_of_eq (hA : CongruentInBoxes A A' y y' m) (hB : CongruentInBoxes B B' y y' m)
    (h : A = B) : A' = B' :=
  eq_of_congruentInBoxes_of_congruentInBoxes hA (h ▸ hB)
theorem congruentInBoxes_union [DecidableEq (TorusSite n)] [DecidableEq (TorusSite n')]
    (hA : CongruentInBoxes A A' y y' m) (hB : CongruentInBoxes B B' y y' m) :
    CongruentInBoxes (A ∪ B) (A' ∪ B') y y' m := by
  refine ⟨fun z hz => ?_, fun z hz => ?_, fun a ha => ?_⟩
  · rcases Finset.mem_union.mp hz with h | h
    · exact hA.1 z h
    · exact hB.1 z h
  · rcases Finset.mem_union.mp hz with h | h
    · exact hA.2.1 z h
    · exact hB.2.1 z h
  · rw [Finset.mem_union, Finset.mem_union, hA.2.2 a ha, hB.2.2 a ha]
end Sets
theorem sameBlockPosition_symm {ℓ : StepParameters} (h : SameBlockPosition ℓ y y') :
    SameBlockPosition ℓ y' y := fun i => by
  have h2 : (ℓ.side : ℤ) ∣ ((y i).cast : ℤ) - ((y' i).cast : ℤ) := Int.dvd_of_emod_eq_zero (h i)
  have h3 := dvd_neg.mpr h2
  rw [neg_sub] at h3
  exact Int.emod_eq_zero_of_dvd h3
theorem fieldsAgreeOnSet_symm {W : TorusField n} {W' : TorusField n'} {X : Finset (TorusSite n)}
    {X' : Finset (TorusSite n')} (hb : CongruentInBoxes X X' y y' m) (hf : FieldsAgreeOnSet W W' y y' m X) :
    FieldsAgreeOnSet W' W y' y m X' := fun b hbb h1 h2 => by
  have e1 : (bondFrom y b).1 ∈ X := (hb.2.2 b.1 hbb.1).mpr h1
  have e2 : (bondFrom y b).1 + unitStep n b.2 ∈ X := by
    rw [bondFrom_fst_add_unitStep] at h2 ⊢
    exact (hb.2.2 _ hbb.2).mpr h2
  exact (hf b hbb e1 e2).symm
section Distance
theorem eq_of_add_siteOfInt_eq (hn : 2 * m + 2 < n) {a b : Fin 4 → ℤ} (ha : OffsetInBox m a)
    (hb : OffsetInBox m b) (h : y + siteOfInt a = y + siteOfInt b) : a = b := by
  refine eq_of_siteOfInt_eq (add_left_cancel h) fun i => ?_
  have h1 := ha i
  have h2 := hb i
  rw [abs_le] at h1 h2
  rw [abs_lt]
  constructor <;> omega
theorem natAbs_le_of_abs_le_natCast {a : ℤ} {k : ℕ} (h : |a| ≤ (k : ℤ)) : a.natAbs ≤ k := by
  rw [abs_le] at h
  omega
theorem abs_le_natCast_of_natAbs_le {a : ℤ} {k : ℕ} (h : a.natAbs ≤ k) : |a| ≤ (k : ℤ) := by
  rw [abs_le]
  omega
def BallInBox (m ρ : ℕ) (a : Fin 4 → ℤ) : Prop :=
  ∀ e : Fin 4 → ℤ, (∀ i, |e i| ≤ (ρ : ℤ)) → OffsetInBox m (a + e)
def BallsInBox (y : TorusSite n) (m : ℕ) (S : Finset (TorusSite n)) (ρ : ℕ) : Prop :=
  ∀ a, OffsetInBox m a → y + siteOfInt a ∈ S → BallInBox m ρ a
theorem BallsInBox.mono {S S₁ : Finset (TorusSite n)} {ρ ρ₁ : ℕ} (h : BallsInBox y m S ρ) (hs : S₁ ⊆ S)
    (hρ : ρ₁ ≤ ρ) : BallsInBox y m S₁ ρ₁ := fun a ha hx e he =>
  h a ha (hs hx) e fun i => (he i).trans (by exact_mod_cast hρ)
theorem BallsInBox.of_congruent {S : Finset (TorusSite n)} {S' : Finset (TorusSite n')} {ρ : ℕ}
    (h : BallsInBox y m S ρ) (hS : CongruentInBoxes S S' y y' m) : BallsInBox y' m S' ρ := fun a ha hx =>
  h a ha ((hS.2.2 a ha).mpr hx)
theorem abs_sub_le_of_supDist_le (hn : 2 * m + 2 < n) {a b : Fin 4 → ℤ} {ρ : ℕ} (ha : BallInBox m ρ a)
    (hb : OffsetInBox m b) (h : supDist (y + siteOfInt a) (y + siteOfInt b) ≤ ρ) :
    ∀ i, |b i - a i| ≤ (ρ : ℤ) := by
  obtain ⟨e, he, hb'⟩ := exists_offset_of_supDist (y + siteOfInt a) (y + siteOfInt b)
  have hρ : ∀ i, |e i| ≤ (ρ : ℤ) := fun i => abs_le_natCast_of_natAbs_le ((hb' i).trans h)
  have : b = a + e := eq_of_add_siteOfInt_eq hn hb (ha e hρ) (by rw [he, add_siteOfInt_add])
  intro i
  rw [this]
  simpa using hρ i
theorem supDist_le_of_abs_sub_le {a b : Fin 4 → ℤ} {ρ : ℕ} (h : ∀ i, |b i - a i| ≤ (ρ : ℤ)) :
    supDist (y + siteOfInt a) (y + siteOfInt b) ≤ ρ := by
  have e : y + siteOfInt b = y + siteOfInt a + siteOfInt (b - a) := by
    rw [← add_siteOfInt_add]
    simp
  rw [e]
  exact supDist_add_siteOfInt_le _ _ _ fun i => natAbs_le_of_abs_le_natCast (h i)
theorem supDist_le_transfer (hn : 2 * m + 2 < n) {a b : Fin 4 → ℤ} {ρ : ℕ} (ha : BallInBox m ρ a)
    (hb : OffsetInBox m b) (h : supDist (y + siteOfInt a) (y + siteOfInt b) ≤ ρ) :
    supDist (y' + siteOfInt a) (y' + siteOfInt b) ≤ ρ :=
  supDist_le_of_abs_sub_le (abs_sub_le_of_supDist_le hn ha hb h)
theorem exists_offset_of_mem_thickening {S : Finset (TorusSite n)} {ρ : ℕ}
    (hS : ∀ z ∈ S, ∃ a, OffsetInBox m a ∧ z = y + siteOfInt a) (hd : BallsInBox y m S ρ) {z : TorusSite n}
    (hz : z ∈ thickening ρ S) : ∃ b, OffsetInBox m b ∧ z = y + siteOfInt b := by
  obtain ⟨x, hx, hzx⟩ := (mem_thickening _ _ _).mp hz
  obtain ⟨a, ha, rfl⟩ := hS x hx
  obtain ⟨e, he, hb⟩ := exists_offset_of_supDist (y + siteOfInt a) z
  refine ⟨a + e, hd a ha hx e fun i => ?_, by rw [he, add_siteOfInt_add]⟩
  rw [supDist_comm] at hzx
  exact abs_le_natCast_of_natAbs_le ((hb i).trans hzx)
theorem mem_thickening_transfer {S : Finset (TorusSite n)} {S' : Finset (TorusSite n')} {ρ : ℕ}
    (hn : 2 * m + 2 < n) (hS : CongruentInBoxes S S' y y' m) (hd : BallsInBox y m S ρ) {b : Fin 4 → ℤ}
    (hb : OffsetInBox m b) (hz : y + siteOfInt b ∈ thickening ρ S) : y' + siteOfInt b ∈ thickening ρ S' := by
  obtain ⟨x, hx, hzx⟩ := (mem_thickening _ _ _).mp hz
  obtain ⟨a, ha, rfl⟩ := hS.1 x hx
  refine (mem_thickening _ _ _).mpr ⟨_, (hS.2.2 a ha).mp hx, ?_⟩
  rw [supDist_comm] at hzx ⊢
  exact supDist_le_transfer hn (hd a ha hx) hb hzx
theorem congruentInBoxes_thickening {S : Finset (TorusSite n)} {S' : Finset (TorusSite n')} {ρ : ℕ}
    (hn : 2 * m + 2 < n) (hn' : 2 * m + 2 < n') (hS : CongruentInBoxes S S' y y' m)
    (hd : BallsInBox y m S ρ) : CongruentInBoxes (thickening ρ S) (thickening ρ S') y y' m :=
  ⟨fun _ hz => exists_offset_of_mem_thickening hS.1 hd hz,
    fun _ hz => exists_offset_of_mem_thickening hS.2.1 (hd.of_congruent hS) hz, fun _ hb =>
    ⟨mem_thickening_transfer hn hS hd hb,
      mem_thickening_transfer hn' (congruentInBoxes_symm hS) (hd.of_congruent hS) hb⟩⟩
end Distance
section Components
variable {S : Finset (TorusSite n)} {S' : Finset (TorusSite n')} {ρ : ℕ}
theorem chainConnected_transfer (hn : 2 * m + 2 < n) (hS : CongruentInBoxes S S' y y' m)
    (hd : BallsInBox y m S ρ) {a b : Fin 4 → ℤ} (ha : OffsetInBox m a) (hb : OffsetInBox m b)
    (hax : y + siteOfInt a ∈ S) (hj : ChainConnected ρ S (y + siteOfInt a) (y + siteOfInt b)) :
    ChainConnected ρ S' (y' + siteOfInt a) (y' + siteOfInt b) := by
  have key : ∀ z, Relation.ReflTransGen (fun u v => u ∈ S ∧ v ∈ S ∧ supDist u v ≤ ρ) (y + siteOfInt a) z →
      ∃ c, OffsetInBox m c ∧ z = y + siteOfInt c ∧ z ∈ S ∧
        ChainConnected ρ S' (y' + siteOfInt a) (y' + siteOfInt c) := by
    intro z hz
    induction hz with
    | refl => exact ⟨a, ha, rfl, hax, Relation.ReflTransGen.refl⟩
    | @tail u v _ hs ih =>
      obtain ⟨c, hc, rfl, hu, hJ⟩ := ih
      obtain ⟨hu₁, hv, hdist⟩ := hs
      obtain ⟨c', hc', rfl⟩ := hS.1 v hv
      refine ⟨c', hc', rfl, hv,
        hJ.trans (chainConnected_of_supDist_le ((hS.2.2 c hc).mp hu) ((hS.2.2 c' hc').mp hv) ?_)⟩
      exact supDist_le_transfer hn (hd c hc hu) hc' hdist
  obtain ⟨c, hc, he, -, hJ⟩ := key _ hj
  rw [eq_of_add_siteOfInt_eq hn hb hc he]
  exact hJ
theorem exists_congruent_component (hn : 2 * m + 2 < n) (hn' : 2 * m + 2 < n')
    (hS : CongruentInBoxes S S' y y' m) (hd : BallsInBox y m S ρ) {K : Finset (TorusSite n)}
    (hK : K ∈ chainComponents ρ S) : ∃ K' ∈ chainComponents ρ S', CongruentInBoxes K K' y y' m := by
  classical
  obtain ⟨x, hx, rfl⟩ := mem_chainComponents.mp hK
  obtain ⟨a, ha, rfl⟩ := hS.1 x hx
  have hx' := (hS.2.2 a ha).mp hx
  refine ⟨S'.filter (ChainConnected ρ S' (y' + siteOfInt a)), mem_chainComponents.mpr ⟨_, hx', rfl⟩,
    fun z hz => hS.1 z (Finset.mem_filter.mp hz).1, fun z hz => hS.2.1 z (Finset.mem_filter.mp hz).1,
    fun b hb => ?_⟩
  rw [Finset.mem_filter, Finset.mem_filter, hS.2.2 b hb]
  refine and_congr_right fun _ => ⟨chainConnected_transfer hn hS hd ha hb hx, ?_⟩
  exact chainConnected_transfer hn' (congruentInBoxes_symm hS) (hd.of_congruent hS) ha hb hx'
theorem exists_congruent_component_symm (hn : 2 * m + 2 < n) (hn' : 2 * m + 2 < n')
    (hS : CongruentInBoxes S S' y y' m) (hd : BallsInBox y m S ρ) {K' : Finset (TorusSite n')}
    (hK : K' ∈ chainComponents ρ S') : ∃ K ∈ chainComponents ρ S, CongruentInBoxes K K' y y' m := by
  obtain ⟨K, h1, h2⟩ :=
    exists_congruent_component hn' hn (congruentInBoxes_symm hS) (hd.of_congruent hS) hK
  exact ⟨K, h1, congruentInBoxes_symm h2⟩
end Components
theorem prod_eq_prod_of_rel {α β : Type} {A : Finset α} {B : Finset β} (r : α → β → Prop) (f : α → ℝ)
    (g : β → ℝ) (h1 : ∀ a ∈ A, ∃ b ∈ B, r a b) (h2 : ∀ b ∈ B, ∃ a ∈ A, r a b)
    (hu : ∀ a ∈ A, ∀ b ∈ B, ∀ b' ∈ B, r a b → r a b' → b = b')
    (hu' : ∀ a ∈ A, ∀ a' ∈ A, ∀ b ∈ B, r a b → r a' b → a = a')
    (hf : ∀ a ∈ A, ∀ b ∈ B, r a b → f a = g b) : ∏ a ∈ A, f a = ∏ b ∈ B, g b := by
  classical
  choose φ hφ hφr using h1
  refine Finset.prod_bij (fun a ha => φ a ha) (fun a ha => hφ a ha) (fun a ha a' ha' he => ?_)
    (fun b hb => ?_) (fun a ha => hf a ha _ (hφ a ha) (hφr a ha))
  · exact hu' a ha a' ha' _ (hφ a ha) (hφr a ha) (he ▸ hφr a' ha')
  · obtain ⟨a, ha, hr⟩ := h2 b hb
    exact ⟨a, ha, hu a ha _ (hφ a ha) b hb (hφr a ha) hr⟩
section Lumps
variable {ℓ : StepParameters} {S : Finset (TorusSite n)} {S' : Finset (TorusSite n')}
  {W : TorusField n} {W' : TorusField n'}
theorem curvature_eq_of_fieldsAgreeOnSet (hf : FieldsAgreeOnSet W W' y y' m S) (a : Fin 4 → ℤ) (μ ν : Fin 4)
    (h : ∀ d ∈ plaquetteOffsets μ ν, OffsetInBox m (a + d) ∧ y + siteOfInt (a + d) ∈ S) :
    curvature W (y + siteOfInt a) μ ν = curvature W' (y' + siteOfInt a) μ ν := by
  have d0 := h 0 (by simp [plaquetteOffsets])
  have d1 := h (Pi.single μ 1) (by simp [plaquetteOffsets])
  have d2 := h (Pi.single ν 1) (by simp [plaquetteOffsets])
  have d3 := h (Pi.single μ 1 + Pi.single ν 1) (by simp [plaquetteOffsets])
  rw [add_zero] at d0
  have hv : ∀ (c : Fin 4 → ℤ) (i : Fin 4), OffsetInBox m c → OffsetInBox m (c + Pi.single i 1) →
      y + siteOfInt c ∈ S → y + siteOfInt (c + Pi.single i 1) ∈ S →
      W (y + siteOfInt c) i = W' (y' + siteOfInt c) i := by
    intro c i h1 h2 h3 h4
    refine hf (c, i) ⟨h1, h2⟩ h3 ?_
    rw [bondFrom_fst_add_unitStep]
    exact h4
  have a3 : a + (Pi.single μ 1 + Pi.single ν 1) = (a + Pi.single μ 1) + Pi.single ν 1 := by
    rw [add_assoc]
  have a4 : a + (Pi.single μ 1 + Pi.single ν 1) = (a + Pi.single ν 1) + Pi.single μ 1 := by
    rw [add_assoc, add_comm (Pi.single μ 1)]
  have e1 := hv a μ d0.1 d1.1 d0.2 d1.2
  have e2 := hv (a + Pi.single μ 1) ν d1.1 (a3 ▸ d3.1) d1.2 (a3 ▸ d3.2)
  have e3 := hv (a + Pi.single ν 1) μ d2.1 (a4 ▸ d3.1) d2.2 (a4 ▸ d3.2)
  have e4 := hv a ν d0.1 d2.1 d0.2 d2.2
  unfold curvature holonomy
  simp only [unitStep_eq_siteOfInt]
  rw [add_siteOfInt_add, add_siteOfInt_add] at e2 e3
  rw [e1, e2, e3, e4]
theorem plaquette_offsets_mem (hn : 2 * m + 2 < n) (hS : ∀ z ∈ S, ∃ a, OffsetInBox m a ∧ z = y + siteOfInt a)
    {a : Fin 4 → ℤ} {μ ν : Fin 4} (ha : OffsetInBox m a)
    (hc : ∀ z ∈ plaquetteVertices (y + siteOfInt a) μ ν, z ∈ S) :
    ∀ d ∈ plaquetteOffsets μ ν, OffsetInBox m (a + d) ∧ y + siteOfInt (a + d) ∈ S := by
  intro d hd
  have hin : y + siteOfInt (a + d) ∈ S := by
    rw [add_siteOfInt_add]
    exact hc _ ((mem_plaquetteVertices_iff_offset _ _ _ _).mpr ⟨d, hd, rfl⟩)
  obtain ⟨b, hb, he⟩ := hS _ hin
  have hab : a + d = b := by
    refine eq_of_siteOfInt_eq (add_left_cancel he) fun i => ?_
    have h1 := ha i
    have h2 := hb i
    have h3 := abs_le_two_of_mem_plaquetteOffsets hd i
    rw [abs_le] at h1 h2 h3
    rw [abs_lt]
    simp only [Pi.add_apply]
    constructor <;> omega
  rw [hab] at hin ⊢
  exact ⟨hb, hin⟩
theorem exists_hot_lump_transfer (hfit : ℓ.Admissible) (hL : ℓ.side ∣ n) (hL' : ℓ.side ∣ n')
    (hn : 2 * m + 2 < n) (hn' : 2 * m + 2 < n') (hS : CongruentInBoxes S S' y y' m)
    (hf : FieldsAgreeOnSet W W' y y' m S) {l : Finset (TorusSite n)} (hl : l ∈ hotLumpsOn ℓ S W) :
    ∃ a, OffsetInBox m a ∧ y + siteOfInt a ∈ S ∧ l = torusLumpOf ℓ (y + siteOfInt a) ∧
      torusLumpOf ℓ (y' + siteOfInt a) ∈ hotLumpsOn ℓ S' W' := by
  obtain ⟨x, μ, ν, hlt, hcur, hall, z, hz, rfl⟩ := (mem_hotLumpsOn_iff ℓ hfit hL S W l).mp hl
  have hx : x ∈ S := hall x (by simp [plaquetteVertices])
  obtain ⟨a, ha, rfl⟩ := hS.1 x hx
  have hco := plaquette_offsets_mem hn hS.1 ha hall
  obtain ⟨d, hd, rfl⟩ := (mem_plaquetteVertices_iff_offset _ _ _ _).mp hz
  rw [← add_siteOfInt_add]
  obtain ⟨h1, h2⟩ := hco d hd
  refine ⟨a + d, h1, h2, rfl, (mem_hotLumpsOn_iff ℓ hfit hL' S' W' _).mpr
    ⟨y' + siteOfInt a, μ, ν, hlt, ?_, ?_, y' + siteOfInt (a + d), ?_, rfl⟩⟩
  · rw [← curvature_eq_of_fieldsAgreeOnSet hf a μ ν hco]
    exact hcur
  · intro w hw
    obtain ⟨d', hd', rfl⟩ := (mem_plaquetteVertices_iff_offset _ _ _ _).mp hw
    rw [← add_siteOfInt_add]
    exact (hS.2.2 _ (hco d' hd').1).mp (hco d' hd').2
  · rw [add_siteOfInt_add]
    exact (mem_plaquetteVertices_iff_offset _ _ _ _).mpr ⟨d, hd, rfl⟩
theorem mem_torusLumpOf_transfer (hfit : ℓ.Admissible) (hL : ℓ.side ∣ n) (hL' : ℓ.side ∣ n')
    (hbig : 2 ^ 17 < n) (hb : SameBlockPosition ℓ y y') {a e : Fin 4 → ℤ} (he : ∀ i, |e i| ≤ 2 ^ 15)
    (h : y + siteOfInt (a + e) ∈ torusLumpOf ℓ (y + siteOfInt a)) :
    y' + siteOfInt (a + e) ∈ torusLumpOf ℓ (y' + siteOfInt a) := by
  classical
  have hk := (Finset.mem_filter.mp h).2
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
    (lumpCorner_eq_of_sameBlockPosition hfit hL hL' hbig hb a e he hk.symm).symm⟩
theorem exists_offset_of_mem_torusLumpOf (hfit : ℓ.Admissible) (hL : ℓ.side ∣ n) {x z : TorusSite n}
    (h : z ∈ torusLumpOf ℓ x) : ∃ e : Fin 4 → ℤ, (∀ i, |e i| ≤ (2 ^ 15 : ℕ)) ∧ z = x + siteOfInt e := by
  classical
  have hk := (Finset.mem_filter.mp h).2
  have hd : supDist z x < 2 ^ 15 := supDist_lt_of_lumpCorner_eq hfit hL hk.symm
  obtain ⟨e, he, hb⟩ := exists_offset_of_supDist x z
  refine ⟨e, fun i => abs_le_natCast_of_natAbs_le ?_, he⟩
  have := hb i
  rw [supDist_comm] at this
  omega
theorem congruentInBoxes_hotLumps (hfit : ℓ.Admissible) (hL : ℓ.side ∣ n) (hL' : ℓ.side ∣ n')
    (hbig : 2 ^ 17 < n) (hbig' : 2 ^ 17 < n') (hn : 2 * m + 2 < n) (hn' : 2 * m + 2 < n')
    (hb : SameBlockPosition ℓ y y') (hS : CongruentInBoxes S S' y y' m)
    (hf : FieldsAgreeOnSet W W' y y' m S)
    (hd : ∀ l ∈ hotLumpsOn ℓ S W, ∀ a, OffsetInBox m a → y + siteOfInt a ∈ l → BallInBox m (2 ^ 15) a) :
    CongruentInBoxes ((hotLumpsOn ℓ S W).biUnion id) ((hotLumpsOn ℓ S' W').biUnion id) y y' m := by
  classical
  have hf' := fieldsAgreeOnSet_symm hS hf
  have hS' := congruentInBoxes_symm hS
  have hb' := sameBlockPosition_symm hb
  refine ⟨fun z hz => ?_, fun z hz => ?_, fun c hc => ⟨fun hz => ?_, fun hz => ?_⟩⟩
  · obtain ⟨l, hl, hzl⟩ := Finset.mem_biUnion.mp hz
    obtain ⟨a, ha, -, rfl, -⟩ := exists_hot_lump_transfer hfit hL hL' hn hn' hS hf hl
    obtain ⟨e, he, rfl⟩ := exists_offset_of_mem_torusLumpOf hfit hL hzl
    exact ⟨a + e, hd _ hl a ha (mem_torusLumpOf_self _) e he, by rw [add_siteOfInt_add]⟩
  · obtain ⟨l', hl', hzl⟩ := Finset.mem_biUnion.mp hz
    obtain ⟨a, ha, -, rfl, hl⟩ := exists_hot_lump_transfer hfit hL' hL hn' hn hS' hf' hl'
    obtain ⟨e, he, rfl⟩ := exists_offset_of_mem_torusLumpOf hfit hL' hzl
    exact ⟨a + e, hd _ hl a ha (mem_torusLumpOf_self _) e he, by rw [add_siteOfInt_add]⟩
  · obtain ⟨l, hl, hzl⟩ := Finset.mem_biUnion.mp hz
    obtain ⟨a, ha, -, rfl, hl'⟩ := exists_hot_lump_transfer hfit hL hL' hn hn' hS hf hl
    obtain ⟨e, he, hze⟩ := exists_offset_of_mem_torusLumpOf hfit hL hzl
    have hin := hd _ hl a ha (mem_torusLumpOf_self _) e he
    have hce : c = a + e := eq_of_add_siteOfInt_eq hn hc hin (by rw [hze, add_siteOfInt_add])
    subst hce
    refine Finset.mem_biUnion.mpr ⟨_, hl', ?_⟩
    exact mem_torusLumpOf_transfer hfit hL hL' hbig hb (fun i => by simpa using he i) hzl
  · obtain ⟨l', hl', hzl⟩ := Finset.mem_biUnion.mp hz
    obtain ⟨a, ha, -, rfl, hl⟩ := exists_hot_lump_transfer hfit hL' hL hn' hn hS' hf' hl'
    obtain ⟨e, he, hze⟩ := exists_offset_of_mem_torusLumpOf hfit hL' hzl
    have hin := hd _ hl a ha (mem_torusLumpOf_self _) e he
    have hce : c = a + e := eq_of_add_siteOfInt_eq hn' hc hin (by rw [hze, add_siteOfInt_add])
    subst hce
    refine Finset.mem_biUnion.mpr ⟨_, hl, ?_⟩
    exact mem_torusLumpOf_transfer hfit hL' hL hbig' hb' (fun i => by simpa using he i) hzl
end Lumps
end YangMills.Construction.CongruentBoxes
end
