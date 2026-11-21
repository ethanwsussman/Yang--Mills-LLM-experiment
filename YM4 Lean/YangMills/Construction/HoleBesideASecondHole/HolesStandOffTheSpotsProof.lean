import YangMills.Construction.HoleBesideASecondHole.ComplementOfEnlargedLumpsIsRegularProofForm
import YangMills.Construction.HoleBesideASecondHole.EachHoleIsFilledProof
import YangMills.Construction.HoleBesideASecondHole.HolesOffTheSpotsProof
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
open YangMills.Construction.BlockAverages YangMills.Construction.LumpContours YangMills.Construction.Holes YangMills.Construction.HoleSavings
namespace HoleFilling
namespace HoleFamilyProof
theorem card_bound_of_reachable {α : Type*} [DecidableEq α] (Q : α → α → Prop) (f : α → ℕ) (c : ℕ)
    (B : Finset α) (a : α)
    (ha : a ∈ B) (hstep : ∀ x y, Q x y → y ∈ B ∧ f y ≤ f x + c)
    (hreach : ∀ b ∈ B, Relation.ReflTransGen Q a b) : ∀ b ∈ B, f b + c ≤ f a + c * B.card := by
  have exit : ∀ (C : Finset α) (b : α), a ∈ C → b ∉ C → Relation.ReflTransGen Q a b →
      ∃ x y, Q x y ∧ x ∈ C ∧ y ∉ C ∧ Relation.ReflTransGen Q a y := by
    intro C b hC hb hr
    induction hr with
    | refl => exact absurd hC hb
    | @tail c d h1 h2 ih =>
      by_cases hc : c ∈ C
      · exact ⟨c, d, h2, hc, hb, h1.tail h2⟩
      · exact ih hc
  have main : ∀ (m : ℕ) (C : Finset α), C ⊆ B → a ∈ C → (∀ b ∈ C, f b + c ≤ f a + c * C.card) →
      B.card - C.card = m → ∀ b ∈ B, f b + c ≤ f a + c * B.card := by
    intro m
    induction m with
    | zero =>
      intro C hCB _ hb hcard b hbB
      have e : C = B := Finset.eq_of_subset_of_card_le hCB (by omega)
      subst e
      exact hb b hbB
    | succ m ih =>
      intro C hCB haC hb hcard
      obtain ⟨b0, hb0, hb0'⟩ : ∃ b0 ∈ B, b0 ∉ C := by
        by_contra hcon
        push_neg at hcon
        have := Finset.card_le_card (show B ⊆ C from hcon)
        omega
      obtain ⟨x, y, hq, hx, hy, _⟩ := exit C b0 haC hb0' (hreach b0 hb0)
      obtain ⟨hyB, hfy⟩ := hstep x y hq
      refine ih (insert y C) (Finset.insert_subset hyB hCB) (Finset.mem_insert_of_mem haC) ?_ ?_
      · intro b hbm
        rw [Finset.card_insert_of_notMem hy, mul_add, mul_one]
        rcases Finset.mem_insert.1 hbm with rfl | hbC
        · have := hb x hx
          omega
        · have := hb b hbC
          omega
      · rw [Finset.card_insert_of_notMem hy]
        omega
  exact main _ {a} (by simpa using ha) (by simp) (by simp) rfl
theorem reflTransGen_restrict {α : Type*} (Q : α → α → Prop) (B : α → Prop) (a : α)
    (hB : ∀ c, Relation.ReflTransGen Q a c → B c) {b : α} (hr : Relation.ReflTransGen Q a b) :
    Relation.ReflTransGen (fun x y => Q x y ∧ B x ∧ B y) a b := by
  induction hr with
  | refl => exact Relation.ReflTransGen.refl
  | @tail c d h1 h2 ih => exact ih.tail ⟨h2, hB c h1, hB d (h1.tail h2)⟩
variable {F : BlockFrame}
structure SiteGeometry (F : BlockFrame) : Prop where
  symm : ∀ {j : ℕ} (x y : F.Site j), _root_.YangMills.Construction.LumpContours.supDist x y = _root_.YangMills.Construction.LumpContours.supDist y x
  triangle : ∀ {j : ℕ} (x y z : F.Site j), _root_.YangMills.Construction.LumpContours.supDist x z ≤ _root_.YangMills.Construction.LumpContours.supDist x y + _root_.YangMills.Construction.LumpContours.supDist y z
  thicken_iff : ∀ {j : ℕ} (m : ℕ) (X : Finset (F.Site j)) (x : F.Site j),
    x ∈ thicken m X ↔ ∃ y ∈ X, _root_.YangMills.Construction.LumpContours.supDist y x ≤ m
  below_iff : ∀ (x : F.Site F.depth) (y : F.Cell), x ∈ sitesBelow F.depth y ↔ enclosingCell x = y
  cell_le : ∀ (m : ℕ) (x x' : F.Site F.depth), _root_.YangMills.Construction.LumpContours.supDist x x' ≤ m * F.blockSide →
    cellSupDist (enclosingCell x) (enclosingCell x') ≤ m
  cell_triangle : ∀ (x y z : F.Cell), cellSupDist x z ≤ cellSupDist x y + cellSupDist y z
  cell_symm : ∀ (x y : F.Cell), cellSupDist x y = cellSupDist y x
  ball_iff : ∀ (x : F.Cell) (r : ℕ) (y : F.Cell), y ∈ cellBall x r ↔ cellSupDist x y ≤ r
  lump_spec : ∀ (g : LumpGrid F.blockSide) (x : F.Site F.depth), x ∈ lumpOf g x ∧
    lumpOf g x ⊆ sitesBelow F.depth (enclosingCell x) ∧
    ∀ u ∈ lumpOf g x, ∀ v ∈ lumpOf g x, _root_.YangMills.Construction.LumpContours.supDist u v < 2 ^ 15
theorem siteGeometry_of (hd : TorusDistanceBlockLumpFacts) (hL : Odd F.blockSide)
    (hs : ∀ i, 0 < F.extent i) : SiteGeometry F := by
  obtain ⟨a, b, c, d, e, f, g, h, i⟩ := hd F hL.pos hs
  exact ⟨fun x y => a _ x y, fun x y z => b _ x y z, fun m X x => c _ m X x, d hL, e hL, f, g, h, i hL⟩
theorem supDist_self {j : ℕ} (x : F.Site j) : _root_.YangMills.Construction.LumpContours.supDist x x = 0 := by apply _root_.YangMills.Construction.HoleFilling.supDist_self <;> assumption
theorem cellSupDist_self (x : F.Cell) : cellSupDist x x = 0 := _root_.YangMills.Construction.HoleFilling.HoleFamilyProof.supDist_self x
variable (G : SiteGeometry F)
include G
theorem isLump_spec {g : LumpGrid F.blockSide} {l : Finset (F.Site F.depth)} (hl : IsLump g l) :
    l.Nonempty ∧ (∀ u ∈ l, ∀ v ∈ l, _root_.YangMills.Construction.LumpContours.supDist u v < 2 ^ 15) ∧
      ∀ u ∈ l, l ⊆ sitesBelow F.depth (enclosingCell u) := by
  obtain ⟨x, rfl⟩ := hl
  obtain ⟨h1, h2, h3⟩ := G.lump_spec g x
  refine ⟨⟨x, h1⟩, h3, fun u hu => ?_⟩
  have : enclosingCell u = enclosingCell x := (G.below_iff u _).1 (h2 hu)
  rw [this]
  exact h2
theorem mem_lumpNeighbourhood {l : Finset (F.Site F.depth)} {p : F.Site F.depth} :
    p ∈ lumpNeighbourhood l ↔ ∃ v ∈ l, _root_.YangMills.Construction.LumpContours.supDist v p ≤ 2 ^ 12 :=
  G.thicken_iff _ _ _
theorem mem_lumpCollar {l : Finset (F.Site F.depth)} {p : F.Site F.depth} :
    p ∈ lumpCollar l ↔ ∃ v ∈ l, _root_.YangMills.Construction.LumpContours.supDist v p ≤ 2 ^ 12 + 2 :=
  G.thicken_iff _ _ _
def lumpSpread (x₀ : F.Site F.depth) (l : Finset (F.Site F.depth)) : ℕ := l.sup (_root_.YangMills.Construction.LumpContours.supDist x₀)
omit G in
theorem le_lumpSpread {x₀ u : F.Site F.depth} {l : Finset (F.Site F.depth)} (hu : u ∈ l) :
    _root_.YangMills.Construction.LumpContours.supDist x₀ u ≤ lumpSpread x₀ l :=
  Finset.le_sup hu
theorem lumpSpread_le_of_within {g : LumpGrid F.blockSide} (x₀ : F.Site F.depth)
    {l l' : Finset (F.Site F.depth)} {r : ℕ}
    (hl' : IsLump g l') (hw : AreWithin r (lumpNeighbourhood l) (lumpNeighbourhood l')) :
    lumpSpread x₀ l' ≤ lumpSpread x₀ l + (r + 2 ^ 13 + 2 ^ 15) := by
  obtain ⟨p, hp, p', hp', hd⟩ := hw
  obtain ⟨v, hv, hvp⟩ := (mem_lumpNeighbourhood G).1 hp
  obtain ⟨v', hv', hvp'⟩ := (mem_lumpNeighbourhood G).1 hp'
  refine Finset.sup_le fun u hu => ?_
  have a1 := le_lumpSpread (x₀ := x₀) hv
  have a2 := (isLump_spec G hl').2.1 v' hv' u hu
  have t1 := G.triangle x₀ v u
  have t2 := G.triangle v p u
  have t3 := G.triangle p p' u
  have t4 := G.triangle p' v' u
  rw [G.symm p' v'] at t4
  omega
omit G in
theorem le_holeScale {J₀ : ℕ} (hJ : 1 ≤ J₀) (i : ℕ) : 2 ^ 16 ≤ holeScale J₀ i := by
  unfold holeScale lumpRange
  have : 1 ≤ (40 * J₀) ^ i := Nat.one_le_pow _ _ (by omega)
  nlinarith
omit G in
theorem holeScale_succ (J₀ i : ℕ) : holeScale J₀ (i + 1) = 10 * holeRadius J₀ i := by
  simp only [holeScale, holeRadius, pow_succ]
  ring
omit G in
theorem holeScale_mono {J₀ : ℕ} (hJ : 1 ≤ J₀) {i j : ℕ} (hij : i ≤ j) :
    holeScale J₀ i ≤ holeScale J₀ j := by apply _root_.YangMills.Construction.Holes.LinkComponentFacts.holeScale_mono <;> assumption
omit G in
theorem topScaleIndex_facts {J₀ L : ℕ} (hJ : 1 ≤ J₀) (hL : holeScale J₀ (2 * J₀) ^ 2 ≤ L) :
    2 * J₀ ≤ topScaleIndex J₀ L ∧ holeScale J₀ (topScaleIndex J₀ L) ^ 2 ≤ L ∧
      16 * J₀ * holeScale J₀ (topScaleIndex J₀ L) ≤ L := by
  have h1 : 2 * J₀ < (40 * J₀) ^ (2 * J₀) := by
    exact Nat.lt_pow_self (by omega : 1 < 40 * J₀)
  have h2 : 2 * J₀ ≤ holeScale J₀ (2 * J₀) := by
    unfold holeScale lumpRange
    nlinarith
  have h3 : holeScale J₀ (2 * J₀) ≤ holeScale J₀ (2 * J₀) ^ 2 := by
    have := le_holeScale hJ (2 * J₀)
    nlinarith
  have h4 : 2 * J₀ ≤ L := by omega
  have a1 : 2 * J₀ ≤ topScaleIndex J₀ L := Nat.le_findGreatest h4 hL
  have a2 : holeScale J₀ (topScaleIndex J₀ L) ^ 2 ≤ L :=
    Nat.findGreatest_spec (P := fun i => holeScale J₀ i ^ 2 ≤ L) h4 hL
  refine ⟨a1, a2, ?_⟩
  have a3 : 16 * J₀ ≤ holeScale J₀ (topScaleIndex J₀ L) := by
    have h5 : holeScale J₀ 1 ≤ holeScale J₀ (topScaleIndex J₀ L) := holeScale_mono hJ (by omega)
    have h6 : holeScale J₀ 1 = 16 * lumpRange * (40 * J₀) := by simp [holeScale]
    unfold lumpRange at h6
    omega
  nlinarith
structure ComponentFacts (h : Finset (Finset (F.Site F.depth))) : Prop where
  mem_self : ∀ (r : ℕ) (l : Finset (F.Site F.depth)), l ∈ h → l ∈ linkComponent r h l
  eq_of_mem : ∀ (r : ℕ) (l l' : Finset (F.Site F.depth)), l' ∈ linkComponent r h l →
    linkComponent r h l' = linkComponent r h l
  mono : ∀ (r r' : ℕ) (l : Finset (F.Site F.depth)), r ≤ r' → linkComponent r h l ⊆ linkComponent r' h l
omit G in
theorem mem_of_reflTransGen {h : Finset (Finset (F.Site F.depth))} {r : ℕ} {a b : Finset (F.Site F.depth)}
    (ha : a ∈ h) (hr : Relation.ReflTransGen (LumpsLinked r h) a b) : b ∈ h := by
  cases hr.cases_tail with
  | inl e => rw [e]; exact ha
  | inr e =>
    obtain ⟨c, _, hc⟩ := e
    exact hc.2.1
omit G in
theorem mem_linkComponent {h : Finset (Finset (F.Site F.depth))} {r : ℕ} {l l' : Finset (F.Site F.depth)} :
    l' ∈ linkComponent r h l ↔ l' ∈ h ∧ Relation.ReflTransGen (LumpsLinked r h) l l' := by apply _root_.YangMills.Construction.Holes.LinkComponentFacts.mem_linkComponent <;> assumption
omit G in
theorem mem_cutBelow {i j : ℕ} {X : Finset (F.Site j)} {z : F.Site i} :
    z ∈ cutBelow i X ↔ ∃ x ∈ X, z ∈ sitesBelow i x := by apply _root_.YangMills.Construction.HoleFilling.AwayFromBadCells.mem_cutBelow <;> assumption
omit G in
theorem subset_cutBelow {l : Finset (F.Site F.depth)} {y : F.Cell} {X : Finset F.Cell}
    (hy : l ⊆ sitesBelow F.depth y) (hX : y ∈ X) :
    l ⊆ cutBelow F.depth X := fun _ hu => mem_cutBelow.2 ⟨y, hX, hy hu⟩
theorem exists_cell_near {g : LumpGrid F.blockSide} {l : Finset (F.Site F.depth)} (hl : IsLump g l)
    {x₀ : F.Site F.depth} {y : F.Cell}
    (hx : enclosingCell x₀ = y) (hm : lumpSpread x₀ l ≤ 1 * F.blockSide) :
    ∃ z, cellSupDist y z ≤ 1 ∧ l ⊆ sitesBelow F.depth z := by
  obtain ⟨⟨u, hu⟩, _, h3⟩ := isLump_spec G hl
  have hd := G.cell_le 1 x₀ u ((le_lumpSpread hu).trans hm)
  rw [hx] at hd
  exact ⟨enclosingCell u, hd, h3 u hu⟩
theorem subset_cutBelow_cellBall {g : LumpGrid F.blockSide} {l : Finset (F.Site F.depth)} (hl : IsLump g l)
    {x₀ : F.Site F.depth} {y : F.Cell}
    (hx : enclosingCell x₀ = y) {m : ℕ} (hm : lumpSpread x₀ l ≤ m * F.blockSide) :
    l ⊆ cutBelow F.depth (cellBall y m) := by
  obtain ⟨⟨u, hu⟩, _, h3⟩ := isLump_spec G hl
  have hd := G.cell_le m x₀ u ((le_lumpSpread hu).trans hm)
  rw [hx] at hd
  intro v hv
  exact mem_cutBelow.2 ⟨enclosingCell u, (G.ball_iff y m _).2 hd, h3 u hu hv⟩
theorem cutBelow_cellBall_mono {y : F.Cell} {m m' : ℕ} (hm : m ≤ m') :
    cutBelow F.depth (cellBall y m) ⊆ cutBelow F.depth (cellBall y m') := by
  intro z hz
  obtain ⟨x, hx, hzx⟩ := mem_cutBelow.1 hz
  refine mem_cutBelow.2 ⟨x, ?_, hzx⟩
  rw [G.ball_iff] at hx ⊢
  omega
theorem lumpSpread_le {g : LumpGrid F.blockSide} {l : Finset (F.Site F.depth)} (hl : IsLump g l)
    {x₀ : F.Site F.depth} (hx : x₀ ∈ l) :
    lumpSpread x₀ l ≤ 2 ^ 15 :=
  Finset.sup_le fun u hu => ((isLump_spec G hl).2.1 x₀ hx u hu).le
section HoleDataFacts
variable {a s θ : ℝ} {J₀ : ℕ} {g : LumpGrid F.blockSide} (D : HoleData F g a s θ J₀)
theorem hot_spec {l : Finset (F.Site F.depth)} (hl : l ∈ D.hotFineLumps) :
    IsLump g l ∧ ∃ y ∈ D.cells, l ⊆ sitesBelow F.depth y := by
  unfold HoleData.hotFineLumps hotLumps at hl
  simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_image] at hl
  obtain ⟨p, ⟨hp, _⟩, x, hx, rfl⟩ := hl
  have hxX : x ∈ cutBelow F.depth D.cells := (Finset.mem_filter.1 hp).2.2 hx
  obtain ⟨y, hy, hxy⟩ := Finset.mem_biUnion.1 hxX
  have e := (G.below_iff x y).1 hxy
  refine ⟨⟨x, rfl⟩, y, hy, ?_⟩
  rw [← e]
  exact (G.lump_spec g x).2.1
omit G in
theorem mem_nearbyLumps {h : Finset (Finset (F.Site F.depth))} {y : F.Cell} {l : Finset (F.Site F.depth)} :
    l ∈ nearbyLumps h y ↔ l ∈ h ∧ l ⊆ cutBelow F.depth (cellBall y 2) := by
  classical
  simp [nearbyLumps]
def LinkedWithin (r : ℕ) (h A : Finset (Finset (F.Site F.depth))) (x y : Finset (F.Site F.depth)) : Prop :=
  LumpsLinked r h x y ∧ x ∈ A ∧ y ∈ A
theorem component_small (hJ : 1 ≤ J₀) {r : ℕ} (hr : 2 ^ 16 ≤ r) (hbig : 16 * J₀ * r ≤ F.blockSide)
    {y : F.Cell}
    {h : Finset (Finset (F.Site F.depth))} (hlump : ∀ l ∈ h, IsLump g l)
    (hnc : ¬ IsCrowded J₀ h y) {l₀ : Finset (F.Site F.depth)} (hl₀ : l₀ ∈ h)
    (hy : l₀ ⊆ sitesBelow F.depth y) :
    (linkComponent r h l₀).card < J₀ ∧
      ∀ l' ∈ linkComponent r h l₀, ∃ z, cellSupDist y z ≤ 1 ∧ l' ⊆ sitesBelow F.depth z := by
  classical
  obtain ⟨⟨x₀, hx₀⟩, _, _⟩ := isLump_spec G (hlump l₀ hl₀)
  have hcell : enclosingCell x₀ = y := (G.below_iff x₀ y).1 (hy hx₀)
  obtain ⟨A, hA⟩ : ∃ A, A = nearbyLumps h y := ⟨_, rfl⟩
  have hAc : A.card < J₀ := by
    have : ¬ J₀ ≤ (nearbyLumps h y).card := hnc
    rw [hA]
    omega
  have hyb : y ∈ cellBall y 2 := (G.ball_iff y 2 y).2 (by rw [cellSupDist_self]; norm_num)
  have hsubb : l₀ ⊆ cutBelow F.depth (cellBall y 2) := subset_cutBelow hy hyb
  have hl₀A : l₀ ∈ A := by
    rw [hA]
    exact mem_nearbyLumps.2 ⟨hl₀, hsubb⟩
  have hAh : ∀ l ∈ A, l ∈ h := fun l hl => by
    rw [hA] at hl
    exact (mem_nearbyLumps.1 hl).1
  obtain ⟨B, hB⟩ : ∃ B, B = A.filter (Relation.ReflTransGen (LinkedWithin r h A) l₀) := ⟨_, rfl⟩
  have hinA : ∀ c, Relation.ReflTransGen (LinkedWithin r h A) l₀ c → c ∈ B := by
    intro c hc
    rw [hB]
    refine Finset.mem_filter.2 ⟨?_, hc⟩
    cases hc.cases_tail with
    | inl e => rw [e]; exact hl₀A
    | inr e =>
      obtain ⟨d, _, hd⟩ := e
      exact hd.2.2
  have hBA : ∀ b ∈ B, b ∈ A ∧ Relation.ReflTransGen (LinkedWithin r h A) l₀ b := fun b hb => by
    rw [hB] at hb
    exact Finset.mem_filter.1 hb
  have hl₀B : l₀ ∈ B := hinA _ Relation.ReflTransGen.refl
  obtain ⟨c, hc⟩ : ∃ c, c = r + 2 ^ 13 + 2 ^ 15 := ⟨_, rfl⟩
  have bound := card_bound_of_reachable (fun x y' => LinkedWithin r h A x y' ∧ x ∈ B ∧ y' ∈ B)
    (lumpSpread x₀) c B l₀ hl₀B
    (fun x y' hq => ⟨hq.2.2, by
      rw [hc]
      exact lumpSpread_le_of_within G x₀ (hlump y' (hAh y' (hBA y' hq.2.2).1)) hq.1.1.2.2⟩)
    (fun b hb => reflTransGen_restrict (LinkedWithin r h A) (· ∈ B) l₀ hinA (hBA b hb).2)
  have hBc : B.card ≤ J₀ - 1 := by
    have h1 : B ⊆ A := fun b hb => (hBA b hb).1
    have := Finset.card_le_card h1
    omega
  have hs0 := lumpSpread_le G (hlump l₀ hl₀) hx₀
  have hc2 : c ≤ 2 * r := by omega
  have hcB : c * B.card ≤ 2 * r * (J₀ - 1) := Nat.mul_le_mul hc2 hBc
  have hL1 : 2 ^ 15 + 2 * r * (J₀ - 1) ≤ 1 * F.blockSide := by
    obtain ⟨m, rfl⟩ : ∃ m, J₀ = m + 1 := ⟨J₀ - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    nlinarith
  have hbd : ∀ b ∈ B, lumpSpread x₀ b + c ≤ 1 * F.blockSide := fun b hb => by
    have := bound b hb
    omega
  have hkB : ∀ l, Relation.ReflTransGen (LumpsLinked r h) l₀ l → l ∈ B := by
    intro l hl
    induction hl with
    | refl => exact hl₀B
    | @tail b d h1 h2 ih =>
      have hdl := hlump d h2.2.1
      have hsp := lumpSpread_le_of_within G x₀ hdl h2.2.2
      rw [← hc] at hsp
      have hle : lumpSpread x₀ d ≤ 1 * F.blockSide := by
        have := hbd b ih
        omega
      have hball := subset_cutBelow_cellBall G hdl hcell hle
      have hdA : d ∈ A := by
        rw [hA]
        exact mem_nearbyLumps.2 ⟨h2.2.1, hball.trans (cutBelow_cellBall_mono G (by norm_num))⟩
      exact hinA d ((hBA b ih).2.tail ⟨h2, (hBA b ih).1, hdA⟩)
  have hsub : linkComponent r h l₀ ⊆ B := fun l hl => hkB l (mem_linkComponent.1 hl).2
  refine ⟨lt_of_le_of_lt (Finset.card_le_card hsub) (by omega), fun l' hl' => ?_⟩
  have hlB := hsub hl'
  have hle : lumpSpread x₀ l' ≤ 1 * F.blockSide := by
    have := hbd l' hlB
    omega
  exact exists_cell_near G (hlump l' (mem_linkComponent.1 hl').1) hcell hle
theorem component_spread (hJ : 1 ≤ J₀) {r : ℕ} (hr : 2 ^ 16 ≤ r) {h : Finset (Finset (F.Site F.depth))}
    (hlump : ∀ l ∈ h, IsLump g l) {l₀ : Finset (F.Site F.depth)} (hl₀ : l₀ ∈ h)
    (hcard : (linkComponent r h l₀).card < J₀)
    {x₀ : F.Site F.depth} (hx₀ : x₀ ∈ l₀) :
    ∀ l ∈ linkComponent r h l₀, ∀ u ∈ lumpCollar l, _root_.YangMills.Construction.LumpContours.supDist x₀ u ≤ 2 * J₀ * r := by
  classical
  intro l hl u hu
  obtain ⟨c, hc⟩ : ∃ c, c = r + 2 ^ 13 + 2 ^ 15 := ⟨_, rfl⟩
  have hin : ∀ d, Relation.ReflTransGen (LumpsLinked r h) l₀ d → d ∈ linkComponent r h l₀ := fun d hd =>
    mem_linkComponent.2 ⟨mem_of_reflTransGen hl₀ hd, hd⟩
  have hself : l₀ ∈ linkComponent r h l₀ := hin _ Relation.ReflTransGen.refl
  have bound := card_bound_of_reachable
    (fun x y' => LumpsLinked r h x y' ∧ x ∈ linkComponent r h l₀ ∧ y' ∈ linkComponent r h l₀)
    (lumpSpread x₀) c (linkComponent r h l₀) l₀ hself
    (fun x y' hq => ⟨hq.2.2, by
      rw [hc]
      exact lumpSpread_le_of_within G x₀ (hlump y' hq.1.2.1) hq.1.2.2⟩)
    (fun b hb => reflTransGen_restrict (LumpsLinked r h) (· ∈ linkComponent r h l₀) l₀ hin
      (mem_linkComponent.1 hb).2) l hl
  obtain ⟨v, hv, hvu⟩ := (mem_lumpCollar G).1 hu
  have a1 := le_lumpSpread (x₀ := x₀) hv
  have a2 := G.triangle x₀ v u
  have hs0 := lumpSpread_le G (hlump l₀ hl₀) hx₀
  have hpos : 1 ≤ (linkComponent r h l₀).card := Finset.card_pos.2 ⟨_, hself⟩
  obtain ⟨m, hm⟩ : ∃ m, (linkComponent r h l₀).card = m + 1 := ⟨_, (Nat.sub_add_cancel hpos).symm⟩
  rw [hm] at bound hcard
  have hc2 : c ≤ 2 * r := by omega
  have hcm : c * m ≤ 2 * r * m := Nat.mul_le_mul_right _ hc2
  have hJm : 2 * (m + 2) * r ≤ 2 * J₀ * r := by
    apply Nat.mul_le_mul_right
    omega
  have e1 : c * (m + 1) = c * m + c := by ring
  have e2 : 2 * (m + 2) * r = 2 * r * m + 4 * r := by ring
  omega
structure HoleSetting (D : HoleData F g a s θ J₀) (o : Finset (Finset (F.Site F.depth)) → F.Site F.depth) :
    Prop where
  one_le : 1 ≤ J₀
  odd_side : Odd F.blockSide
  extent_ge : ∀ i, 64 ≤ F.extent i
  top_ge : 2 * J₀ ≤ topScaleIndex J₀ F.blockSide
  top_sq_le : holeScale J₀ (topScaleIndex J₀ F.blockSide) ^ 2 ≤ F.blockSide
  top_mul_le : 16 * J₀ * holeScale J₀ (topScaleIndex J₀ F.blockSide) ≤ F.blockSide
  components : ComponentFacts D.hotFineLumps
  anchor_mem : ∀ k', (∃ l ∈ k', l ∈ D.hotFineLumps) → ∃ l ∈ k', o k' ∈ l
variable {D} {o : Finset (Finset (F.Site F.depth)) → F.Site F.depth}
omit G in
theorem exists_of_mem_linkComponents {r : ℕ} {h k : Finset (Finset (F.Site F.depth))}
    (hk : k ∈ linkComponents r h) :
    ∃ l ∈ h, k = linkComponent r h l := by
  classical
  obtain ⟨l, hl, rfl⟩ := Finset.mem_image.1 hk
  exact ⟨l, hl, rfl⟩
omit G in
theorem mem_componentsWithin {r : ℕ} {h k k' : Finset (Finset (F.Site F.depth))} :
    k' ∈ componentsWithin r h k ↔ k' ∈ linkComponents r h ∧ k' ⊆ k := by
  classical
  simp [componentsWithin]
theorem part_facts (X : HoleSetting D o) {k : Finset (Finset (F.Site F.depth))} (hkc : k.card < J₀) {i : ℕ}
    (hf : IsStableIndex J₀ D.hotFineLumps k i) {k' : Finset (Finset (F.Site F.depth))}
    (hk' : k' ∈ componentsWithin (holeScale J₀ i) D.hotFineLumps k) :
    ∃ l₀ ∈ k', l₀ ∈ D.hotFineLumps ∧ o k' ∈ l₀ ∧ k' = linkComponent (holeScale J₀ i) D.hotFineLumps l₀ ∧
      k' = linkComponent (holeScale J₀ (i + 1)) D.hotFineLumps l₀ ∧
      ∀ l ∈ k', ∀ u ∈ lumpCollar l, _root_.YangMills.Construction.LumpContours.supDist (o k') u ≤ 2 * J₀ * holeScale J₀ i := by
  have hlump : ∀ l ∈ D.hotFineLumps, IsLump g l := fun l hl => (hot_spec G D hl).1
  obtain ⟨h1, h2⟩ := mem_componentsWithin.1 hk'
  obtain ⟨l₁, hl₁, e₁⟩ := exists_of_mem_linkComponents h1
  have hm : l₁ ∈ k' := by
    rw [e₁]
    exact X.components.mem_self _ _ hl₁
  obtain ⟨l₀, hl₀, hol⟩ := X.anchor_mem k' ⟨l₁, hm, hl₁⟩
  have hl₀h : l₀ ∈ D.hotFineLumps := by
    rw [e₁] at hl₀
    exact (mem_linkComponent.1 hl₀).1
  have e0 : k' = linkComponent (holeScale J₀ i) D.hotFineLumps l₀ := by
    rw [e₁] at hl₀ ⊢
    exact (X.components.eq_of_mem _ _ _ hl₀).symm
  have hk'2 : k' ∈ componentsWithin (holeScale J₀ (i + 1)) D.hotFineLumps k := by
    rw [← hf]
    exact hk'
  obtain ⟨l₂, _, e₂⟩ := exists_of_mem_linkComponents (mem_componentsWithin.1 hk'2).1
  have e3 : k' = linkComponent (holeScale J₀ (i + 1)) D.hotFineLumps l₀ := by
    rw [e₂] at hl₀ ⊢
    exact (X.components.eq_of_mem _ _ _ hl₀).symm
  refine ⟨l₀, hl₀, hl₀h, hol, e0, e3, ?_⟩
  have hcard : (linkComponent (holeScale J₀ i) D.hotFineLumps l₀).card < J₀ := by
    rw [← e0]
    exact lt_of_le_of_lt (Finset.card_le_card h2) hkc
  intro l hl u hu
  rw [e0] at hl
  rw [← e0] at hcard
  have := component_spread G X.one_le (le_holeScale X.one_le i) hlump hl₀h (by rw [← e0]; exact hcard)
    hol l hl u hu
  exact this
omit G in
theorem zmod_cast_bounds {p : ℕ} (hp : 0 < p) (x : ZMod p) :
    0 ≤ (ZMod.cast x : ℤ) ∧ (ZMod.cast x : ℤ) ≤ (p : ℤ) - 1 := by apply _root_.YangMills.Construction.LumpContours.ThickenedComplement.zmodCast_bounds <;> assumption
omit G in
theorem mem_torusCells (hL : 0 < F.blockSide) (hs : ∀ i, 0 < F.extent i) (x : F.Cell) : x ∈ torusCells F := by
  have tc : siteOfCoords F.top (siteCoords x) = x := by
    funext k
    simp [siteOfCoords, siteCoords]
  unfold torusCells boxSites
  refine Finset.mem_image.2 ⟨siteCoords x, ?_, tc⟩
  simp only [Fintype.mem_piFinset, Finset.mem_Icc, Pi.zero_apply]
  intro i
  have per_top : F.period F.top i = F.extent i := by simp [BlockFrame.period]
  have hp : 0 < F.period F.top i := by rw [per_top]; exact hs i
  have h0 := zmod_cast_bounds hp (x i)
  have hv : ((F.period F.top i : ℕ) : ℤ) = F.extent i := by rw [per_top]
  have h2 : siteCoords x i ≤ ((F.period F.top i : ℕ) : ℤ) - 1 := h0.2
  rw [hv] at h2
  exact ⟨h0.1, h2⟩
theorem mem_outerBox (H : Hole F) (p : F.Site F.depth) : p ∈ H.outerBox ↔ _root_.YangMills.Construction.LumpContours.supDist H.centre p ≤ 2 * H.radius := by
  unfold Hole.outerBox
  rw [G.thicken_iff]
  simp
theorem mem_innerBox (H : Hole F) (p : F.Site F.depth) : p ∈ H.innerBox ↔ _root_.YangMills.Construction.LumpContours.supDist H.centre p ≤ H.radius := by
  unfold Hole.innerBox
  rw [G.thicken_iff]
  simp
omit G in
theorem mem_annulus (H : Hole F) (p : F.Site F.depth) : p ∈ H.annulus ↔ p ∈ H.outerBox ∧ p ∉ H.innerBox := by
  unfold Hole.annulus
  exact Finset.mem_sdiff
def partHole (o : Finset (Finset (F.Site F.depth)) → F.Site F.depth) (J₀ i : ℕ)
    (k' : Finset (Finset (F.Site F.depth))) : Hole F :=
  ⟨k', o k', holeRadius J₀ i⟩
omit G in
theorem holeRadius_facts (X : HoleSetting D o) {i : ℕ} (hi : i < topScaleIndex J₀ F.blockSide) :
    99 ≤ holeRadius J₀ i ∧ 100 * holeRadius J₀ i ^ 2 ≤ F.blockSide ∧
      10 * holeRadius J₀ i ≤ holeScale J₀ (topScaleIndex J₀ F.blockSide) ∧
      holeRadius J₀ i = 4 * J₀ * holeScale J₀ i ∧ 2 ^ 16 ≤ holeScale J₀ i := by
  have hJ := X.one_le
  have h1 := le_holeScale hJ i
  have h2 := holeScale_succ J₀ i
  have h3 : holeScale J₀ (i + 1) ≤ holeScale J₀ (topScaleIndex J₀ F.blockSide) := holeScale_mono hJ hi
  have h4 : holeRadius J₀ i = 4 * J₀ * holeScale J₀ i := rfl
  have h5 : 4 * holeScale J₀ i ≤ holeRadius J₀ i := by
    rw [h4]
    nlinarith
  refine ⟨by omega, ?_, by omega, h4, h1⟩
  have h6 : (10 * holeRadius J₀ i) ^ 2 ≤ holeScale J₀ (topScaleIndex J₀ F.blockSide) ^ 2 :=
    Nat.pow_le_pow_left (by omega) 2
  have h7 := X.top_sq_le
  nlinarith
theorem mem_lumpNeighbourhood_self {l : Finset (F.Site F.depth)} {x : F.Site F.depth} (hx : x ∈ l) :
    x ∈ lumpNeighbourhood l :=
  (mem_lumpNeighbourhood G).2 ⟨x, hx, by rw [_root_.YangMills.Construction.HoleFilling.HoleFamilyProof.supDist_self]; norm_num⟩
theorem lumpCollar_of_neighbourhood {l : Finset (F.Site F.depth)} {x : F.Site F.depth}
    (hx : x ∈ lumpNeighbourhood l) : x ∈ lumpCollar l := by
  obtain ⟨v, hv, d⟩ := (mem_lumpNeighbourhood G).1 hx
  exact (mem_lumpCollar G).2 ⟨v, hv, by omega⟩
theorem outer_not_within (X : HoleSetting D o) {k : Finset (Finset (F.Site F.depth))} (hkc : k.card < J₀) {i : ℕ}
    (hf : IsStableIndex J₀ D.hotFineLumps k i) {k' : Finset (Finset (F.Site F.depth))}
    (hk' : k' ∈ componentsWithin (holeScale J₀ i) D.hotFineLumps k) (hi : i < topScaleIndex J₀ F.blockSide)
    {l : Finset (F.Site F.depth)} (hl : l ∈ D.hotFineLumps) (hl' : l ∉ k') :
    ¬ AreWithin 1 (partHole o J₀ i k').outerBox (lumpNeighbourhood l) := by
  rintro ⟨p, hp, q, hq, d⟩
  obtain ⟨l₀, hl₀, hl₀h, hol, _, e3, _⟩ := part_facts G X hkc hf hk'
  obtain ⟨_, _, _, _, h5⟩ := holeRadius_facts X hi
  have h1 := (mem_outerBox G _ p).1 hp
  simp only [partHole] at h1
  have h2 := G.triangle (o k') p q
  have hR := holeScale_succ J₀ i
  have hw : AreWithin (holeScale J₀ (i + 1)) (lumpNeighbourhood l₀) (lumpNeighbourhood l) :=
    ⟨o k', mem_lumpNeighbourhood_self G hol, q, hq, by omega⟩
  apply hl'
  rw [e3]
  exact mem_linkComponent.2 ⟨hl, Relation.ReflTransGen.single ⟨hl₀h, hl, hw⟩⟩
theorem annulus_not_within (X : HoleSetting D o) {k : Finset (Finset (F.Site F.depth))} (hkc : k.card < J₀)
    {i : ℕ}
    (hf : IsStableIndex J₀ D.hotFineLumps k i) {k' : Finset (Finset (F.Site F.depth))}
    (hk' : k' ∈ componentsWithin (holeScale J₀ i) D.hotFineLumps k) (hi : i < topScaleIndex J₀ F.blockSide)
    {l : Finset (F.Site F.depth)} (hl : l ∈ D.hotFineLumps) :
    ¬ AreWithin 1 (partHole o J₀ i k').annulus (lumpNeighbourhood l) := by
  rintro ⟨p, hp, q, hq, d⟩
  obtain ⟨hp1, hp2⟩ := (mem_annulus _ p).1 hp
  by_cases hl' : l ∈ k'
  · obtain ⟨l₀, hl₀, hl₀h, hol, _, _, hb⟩ := part_facts G X hkc hf hk'
    have h1 := hb l hl' q (lumpCollar_of_neighbourhood G hq)
    rw [mem_innerBox G] at hp2
    simp only [partHole] at hp2
    obtain ⟨_, _, _, h4, h5⟩ := holeRadius_facts X hi
    have h2 := G.triangle (o k') q p
    rw [G.symm q p] at h2
    have h6 : 2 * J₀ * holeScale J₀ i + 1 ≤ holeRadius J₀ i := by
      rw [h4]
      nlinarith [X.one_le]
    omega
  · exact outer_not_within G X hkc hf hk' hi hl hl' ⟨p, hp1, q, hq, d⟩
theorem thicken_outer_walls (X : HoleSetting D o) {k : Finset (Finset (F.Site F.depth))} (hkc : k.card < J₀)
    {i : ℕ}
    (hf : IsStableIndex J₀ D.hotFineLumps k i) {k' : Finset (Finset (F.Site F.depth))}
    (hk' : k' ∈ componentsWithin (holeScale J₀ i) D.hotFineLumps k) (hi : i < topScaleIndex J₀ F.blockSide)
    {x : F.Site F.depth} (hx : x ∈ thicken (F.blockSide / 2) (partHole o J₀ i k').outerBox) :
    enclosingCell x ∈ D.cells ∧ ∀ z ∈ torusCells F \ D.cells, 2 ≤ cellSupDist (enclosingCell x) z := by
  obtain ⟨l₀, hl₀, hl₀h, hol, _, _, _⟩ := part_facts G X hkc hf hk'
  obtain ⟨p, hp, dpx⟩ := (G.thicken_iff _ _ _).1 hx
  have h1 := (mem_outerBox G _ p).1 hp
  simp only [partHole] at h1
  obtain ⟨_, h2, _, _, _⟩ := holeRadius_facts X hi
  have h3 := G.triangle (o k') p x
  have hR : 2 * holeRadius J₀ i ≤ F.blockSide / 2 := by
    have : 4 * holeRadius J₀ i ≤ F.blockSide := by nlinarith
    omega
  have hd : _root_.YangMills.Construction.LumpContours.supDist (o k') x ≤ 1 * F.blockSide := by omega
  obtain ⟨y₀, hy₀, hsub⟩ := (hot_spec G D hl₀h).2
  have hc : enclosingCell (o k') = y₀ := (G.below_iff _ _).1 (hsub hol)
  have hcd := G.cell_le 1 _ _ hd
  rw [hc] at hcd
  have hw := D.wall_free
  have hw' : ∀ z ∈ torusCells F \ D.cells, 2 < cellSupDist y₀ z := fun z hz => hw l₀ hl₀h y₀ hy₀ hsub z hz
  have hs' : ∀ i, 0 < F.extent i := fun i => by have := X.extent_ge i; omega
  refine ⟨?_, fun z hz => ?_⟩
  · by_contra hn
    have := hw' (enclosingCell x) (Finset.mem_sdiff.2 ⟨mem_torusCells X.odd_side.pos hs' _, hn⟩)
    omega
  · have a1 := hw' z hz
    have a2 := G.cell_triangle y₀ (enclosingCell x) z
    omega
theorem outer_apart (X : HoleSetting D o) {k : Finset (Finset (F.Site F.depth))} (hkc : k.card < J₀) {i : ℕ}
    (hf : IsStableIndex J₀ D.hotFineLumps k i) {k₁ k₂ : Finset (Finset (F.Site F.depth))}
    (h₁ : k₁ ∈ componentsWithin (holeScale J₀ i) D.hotFineLumps k)
    (h₂ : k₂ ∈ componentsWithin (holeScale J₀ i) D.hotFineLumps k)
    (hne : k₁ ≠ k₂) :
    ¬ AreWithin (5 * holeRadius J₀ i) (partHole o J₀ i k₁).outerBox (partHole o J₀ i k₂).outerBox := by
  rintro ⟨p, hp, q, hq, d⟩
  obtain ⟨l₁, m₁, hl₁, ho₁, e₁, e₁', _⟩ := part_facts G X hkc hf h₁
  obtain ⟨l₂, m₂, hl₂, ho₂, e₂, _, _⟩ := part_facts G X hkc hf h₂
  have a1 := (mem_outerBox G _ p).1 hp
  have a2 := (mem_outerBox G _ q).1 hq
  simp only [partHole] at a1 a2
  have t1 := G.triangle (o k₁) p (o k₂)
  have t2 := G.triangle p q (o k₂)
  rw [G.symm q (o k₂)] at t2
  have hR := holeScale_succ J₀ i
  have hw : AreWithin (holeScale J₀ (i + 1)) (lumpNeighbourhood l₁) (lumpNeighbourhood l₂) :=
    ⟨o k₁, mem_lumpNeighbourhood_self G ho₁, o k₂, mem_lumpNeighbourhood_self G ho₂, by omega⟩
  have hm : l₂ ∈ k₁ := by
    rw [e₁']
    exact mem_linkComponent.2 ⟨hl₂, Relation.ReflTransGen.single ⟨hl₁, hl₂, hw⟩⟩
  apply hne
  rw [e₁] at hm
  rw [e₁, e₂]
  exact (X.components.eq_of_mem _ _ _ hm).symm
theorem holeRadius_lt (hJ : 1 ≤ J₀) {i i' : ℕ} (hi : i < i') : 40 * holeRadius J₀ i ≤ holeRadius J₀ i' := by
  have h1 : holeScale J₀ (i + 1) ≤ holeScale J₀ i' := holeScale_mono hJ hi
  have h2 := holeScale_succ J₀ i
  have h3 : holeRadius J₀ i' = 4 * J₀ * holeScale J₀ i' := rfl
  rw [h3]
  nlinarith
theorem annulus_disjoint_of_lt (X : HoleSetting D o) {k : Finset (Finset (F.Site F.depth))} (hkc : k.card < J₀)
    {i i' : ℕ}
    (hf : IsStableIndex J₀ D.hotFineLumps k i) (hf' : IsStableIndex J₀ D.hotFineLumps k i') (hii : i < i')
    (hi' : i' < topScaleIndex J₀ F.blockSide)
    {k₁ k₂ : Finset (Finset (F.Site F.depth))}
    (h₁ : k₁ ∈ componentsWithin (holeScale J₀ i) D.hotFineLumps k)
    (h₂ : k₂ ∈ componentsWithin (holeScale J₀ i') D.hotFineLumps k)
    {x : F.Site F.depth} (hx₁ : x ∈ (partHole o J₀ i k₁).annulus) (hx₂ : x ∈ (partHole o J₀ i' k₂).annulus) :
    False := by
  obtain ⟨l₁, m₁, hl₁, ho₁, _, _, _⟩ := part_facts G X hkc hf h₁
  obtain ⟨l₂, m₂, hl₂, ho₂, _, e₂', hb₂⟩ := part_facts G X hkc hf' h₂
  obtain ⟨a1, _⟩ := (mem_annulus _ x).1 hx₁
  obtain ⟨a2, a3⟩ := (mem_annulus _ x).1 hx₂
  rw [mem_outerBox G] at a1 a2
  rw [mem_innerBox G] at a3
  simp only [partHole] at a1 a2 a3
  have hR := holeRadius_lt G X.one_le hii
  have hR' := holeScale_succ J₀ i'
  have t1 := G.triangle (o k₂) x (o k₁)
  rw [G.symm x (o k₁)] at t1
  have hw : AreWithin (holeScale J₀ (i' + 1)) (lumpNeighbourhood l₂) (lumpNeighbourhood l₁) :=
    ⟨o k₂, mem_lumpNeighbourhood_self G ho₂, o k₁, mem_lumpNeighbourhood_self G ho₁, by omega⟩
  have hm : l₁ ∈ k₂ := by
    rw [e₂']
    exact mem_linkComponent.2 ⟨hl₁, Relation.ReflTransGen.single ⟨hl₂, hl₁, hw⟩⟩
  have h3 := hb₂ l₁ hm (o k₁) (lumpCollar_of_neighbourhood G (mem_lumpNeighbourhood_self G ho₁))
  have t2 := G.triangle (o k₂) (o k₁) x
  have h4 : holeRadius J₀ i' = 4 * J₀ * holeScale J₀ i' := rfl
  have h5 : 2 * (2 * J₀ * holeScale J₀ i') = holeRadius J₀ i' := by rw [h4]; ring
  omega
omit G in
theorem mem_cutPlaquettes {j : ℕ} {X : Finset (F.Site j)} {p : F.Site j × Fin 4 × Fin 4} :
    p ∈ cutPlaquettes X ↔ p.1 ∈ X ∧ p.2.1 < p.2.2 ∧ plaquetteCorners p ⊆ X := by apply _root_.YangMills.Construction.HoleFilling.AwayFromBadCells.mem_cutPlaquettes <;> assumption
omit G in
theorem fst_mem_plaquetteCorners {j : ℕ} (p : F.Site j × Fin 4 × Fin 4) : p.1 ∈ plaquetteCorners p := by
  simp [plaquetteCorners]
omit G in
theorem cutBelow_mono {i j : ℕ} {X Y : Finset (F.Site j)} (h : X ⊆ Y) : cutBelow i X ⊆ cutBelow i Y := by apply _root_.YangMills.Construction.HoleSavings.QuietCell.cutBelow_subset_cutBelow <;> assumption
omit G in
theorem cutPlaquettes_mono {j : ℕ} {X Y : Finset (F.Site j)} (h : X ⊆ Y) {p : F.Site j × Fin 4 × Fin 4}
    (hp : p ∈ cutPlaquettes X) : p ∈ cutPlaquettes Y := by apply _root_.YangMills.Construction.CoreBondMeans.cutPlaquettes_mono <;> assumption
theorem annulus_subset_chainSites (X : HoleSetting D o) {k : Finset (Finset (F.Site F.depth))}
    (hkc : k.card < J₀) {i : ℕ}
    (hf : IsStableIndex J₀ D.hotFineLumps k i) {k' : Finset (Finset (F.Site F.depth))}
    (hk' : k' ∈ componentsWithin (holeScale J₀ i) D.hotFineLumps k) (hi : i < topScaleIndex J₀ F.blockSide) :
    (partHole o J₀ i k').annulus ⊆ D.chainSites := by
  classical
  intro x hx
  obtain ⟨h1, _⟩ := (mem_annulus _ x).1 hx
  have h2 : x ∈ thicken (F.blockSide / 2) (partHole o J₀ i k').outerBox :=
    (G.thicken_iff _ _ _).2 ⟨x, h1, by rw [_root_.YangMills.Construction.HoleFilling.HoleFamilyProof.supDist_self]; omega⟩
  have h3 := (thicken_outer_walls G X hkc hf hk' hi h2).1
  refine Finset.mem_sdiff.2 ⟨mem_cutBelow.2 ⟨_, h3, (G.below_iff x _).2 rfl⟩, fun hn => ?_⟩
  obtain ⟨l, hl, hxl⟩ := Finset.mem_biUnion.1 hn
  exact annulus_not_within G X hkc hf hk' hi hl ⟨x, hx, x, hxl, by rw [_root_.YangMills.Construction.HoleFilling.HoleFamilyProof.supDist_self]; norm_num⟩
omit G in
theorem mem_componentHoles {h k : Finset (Finset (F.Site F.depth))} {i : ℕ} {H : Hole F} :
    H ∈ componentHoles J₀ h k i o ↔ ∃ k' ∈ componentsWithin (holeScale J₀ i) h k, H = partHole o J₀ i k' := by
  classical
  simp only [componentHoles, Finset.mem_image, partHole]
  constructor
  · rintro ⟨k', hk', rfl⟩
    exact ⟨k', hk', rfl⟩
  · rintro ⟨k', hk', rfl⟩
    exact ⟨k', hk', rfl⟩
open Classical in
theorem annulusEnergy_sum_le (X : HoleSetting D o)
    (trans : ∀ (i j m : ℕ), i ≤ j → j ≤ m → m ≤ F.top → ∀ (x : F.Site m) (w : F.Site j) (z : F.Site i),
      w ∈ sitesBelow j x → z ∈ sitesBelow i w → z ∈ sitesBelow i x)
    (uniq : ∀ (i j : ℕ), i ≤ j → j ≤ F.top → ∀ (x x' : F.Site j) (z : F.Site i),
      z ∈ sitesBelow i x → z ∈ sitesBelow i x' → x = x')
    (eln : ∀ (U : F.GaugeField 0) (p : F.Site 0 × Fin 4 × Fin 4), 0 ≤ plaquetteEnergy U p)
    (ren : ∀ (q : ℍ[ℝ]) (g : UnitQuaternion), 0 ≤ ‖q‖ - (q * (g⁻¹ : UnitQuaternion)).re) (ha : 0 ≤ a)
    {k : Finset (Finset (F.Site F.depth))} (hkc : k.card < J₀) {y₁ : F.Cell} {B₃ : Finset F.Cell}
    (hB : ∀ z, cellSupDist y₁ z ≤ 2 → z ∈ B₃)
    (hball : ∀ l ∈ k, ∃ z, cellSupDist y₁ z ≤ 1 ∧ l ⊆ sitesBelow F.depth z) (Fr : Finset ℕ)
    (hFr : ∀ i ∈ Fr, i < topScaleIndex J₀ F.blockSide ∧ IsStableIndex J₀ D.hotFineLumps k i) :
    ∑ i ∈ Fr, ∑ H ∈ componentHoles J₀ D.hotFineLumps k i o, H.annulusEnergy (D.chain 0) ≤
      D.energyOver B₃ := by
  have hJ := X.one_le
  have pw1 : (Fr : Set ℕ).PairwiseDisjoint (fun i => componentHoles J₀ D.hotFineLumps k i o) := by
    intro i hi i' hi' hne
    refine Finset.disjoint_left.2 fun H h1 h2 => ?_
    obtain ⟨k₁, _, rfl⟩ := mem_componentHoles.1 h1
    obtain ⟨k₂, _, e⟩ := mem_componentHoles.1 h2
    have er : holeRadius J₀ i = holeRadius J₀ i' := congrArg Hole.radius e
    have p1 := (holeRadius_facts X (hFr i hi).1).1
    have p2 := (holeRadius_facts X (hFr i' hi').1).1
    rcases lt_or_gt_of_ne hne with h | h
    · have := holeRadius_lt G hJ h
      omega
    · have := holeRadius_lt G hJ h
      omega
  rw [← Finset.sum_biUnion pw1]
  have pw2 : ((Fr.biUnion fun i => componentHoles J₀ D.hotFineLumps k i o : Finset (Hole F)) :
      Set (Hole F)).PairwiseDisjoint
      (fun H => cutPlaquettes (cutBelow 0 H.annulus)) := by
    intro H hH H' hH' hne
    refine Finset.disjoint_left.2 fun p h1 h2 => ?_
    obtain ⟨i, hi, hHi⟩ := Finset.mem_biUnion.1 (Finset.mem_coe.1 hH)
    obtain ⟨i', hi', hHi'⟩ := Finset.mem_biUnion.1 (Finset.mem_coe.1 hH')
    obtain ⟨k₁, hk₁, rfl⟩ := mem_componentHoles.1 hHi
    obtain ⟨k₂, hk₂, rfl⟩ := mem_componentHoles.1 hHi'
    obtain ⟨f, hf, hz⟩ := mem_cutBelow.1 (mem_cutPlaquettes.1 h1).1
    obtain ⟨f', hf', hz'⟩ := mem_cutBelow.1 (mem_cutPlaquettes.1 h2).1
    have e := uniq 0 F.depth (Nat.zero_le _) (by simp [BlockFrame.top]) f f' p.1 hz hz'
    subst e
    rcases lt_trichotomy i i' with h | h | h
    · exact annulus_disjoint_of_lt G X hkc (hFr i hi).2 (hFr i' hi').2 h (hFr i' hi').1 hk₁ hk₂ hf hf'
    · subst h
      have hkne : k₁ ≠ k₂ := fun e => hne (by rw [e])
      exact outer_apart G X hkc (hFr i hi).2 hk₁ hk₂ hkne
        ⟨f, ((mem_annulus _ f).1 hf).1, f, ((mem_annulus _ f).1 hf').1, by rw [_root_.YangMills.Construction.HoleFilling.HoleFamilyProof.supDist_self]; omega⟩
    · exact annulus_disjoint_of_lt G X hkc (hFr i' hi').2 (hFr i hi).2 h (hFr i hi).1 hk₂ hk₁ hf' hf
  unfold Hole.annulusEnergy
  rw [← Finset.sum_biUnion pw2]
  have hp : ∀ p ∈ (Fr.biUnion fun i => componentHoles J₀ D.hotFineLumps k i o).biUnion
      (fun H => cutPlaquettes (cutBelow 0 H.annulus)),
      p ∈ cutPlaquettes (cutBelow 0 D.chainSites) ∧ ∃ x ∈ plaquetteCorners p, x ∈ cutBelow 0 B₃ := by
    intro p hp
    obtain ⟨H, hH, hpH'⟩ := Finset.mem_biUnion.1 hp
    have hpH : p ∈ cutPlaquettes (cutBelow 0 H.annulus) := hpH'
    obtain ⟨f, hf, hz⟩ := mem_cutBelow.1 (mem_cutPlaquettes.1 hpH).1
    obtain ⟨i, hi, hHi⟩ := Finset.mem_biUnion.1 hH
    obtain ⟨k₁, hk₁, rfl⟩ := mem_componentHoles.1 hHi
    have hfree := hFr i hi
    refine ⟨cutPlaquettes_mono (cutBelow_mono (annulus_subset_chainSites G X hkc hfree.2 hk₁ hfree.1)) hpH,
      p.1, fst_mem_plaquetteCorners p, ?_⟩
    obtain ⟨l₀, m₀, _, ho₀, _, _, _⟩ := part_facts G X hkc hfree.2 hk₁
    have hsub := (mem_componentsWithin.1 hk₁).2
    obtain ⟨z, hzb, hoz'⟩ := hball l₀ (hsub m₀)
    have hoz := hoz' ho₀
    have hcz : enclosingCell (o k₁) = z := (G.below_iff _ _).1 hoz
    have hf1 := (mem_outerBox G _ f).1 ((mem_annulus _ f).1 hf).1
    simp only [partHole] at hf1
    obtain ⟨r1, r2, _, _, _⟩ := holeRadius_facts X hfree.1
    have hd : _root_.YangMills.Construction.LumpContours.supDist (o k₁) f ≤ 1 * F.blockSide := by nlinarith
    have hcd := G.cell_le 1 _ _ hd
    rw [hcz] at hcd
    have h3 := G.cell_triangle y₁ z (enclosingCell f)
    exact mem_cutBelow.2 ⟨enclosingCell f, hB _ (by omega),
      trans 0 F.depth F.top (Nat.zero_le _) (by simp [BlockFrame.top]) le_rfl _ f p.1
      ((G.below_iff _ _).2 rfl) hz⟩
  have s1 : ∑ p ∈ (Fr.biUnion fun i => componentHoles J₀ D.hotFineLumps k i o).biUnion
      (fun H => cutPlaquettes (cutBelow 0 H.annulus)),
      plaquetteEnergy (D.chain 0) p ≤ ∑ p ∈ cutPlaquettes (cutBelow 0 D.chainSites),
        (if ∃ x ∈ plaquetteCorners p, x ∈ cutBelow 0 B₃ then plaquetteEnergy (D.chain 0) p else 0) := by
    calc _ = ∑ p ∈ (Fr.biUnion fun i => componentHoles J₀ D.hotFineLumps k i o).biUnion
          (fun H => cutPlaquettes (cutBelow 0 H.annulus)),
          (if ∃ x ∈ plaquetteCorners p, x ∈ cutBelow 0 B₃ then plaquetteEnergy (D.chain 0) p else 0) :=
          Finset.sum_congr rfl fun p h => (if_pos (hp p h).2).symm
      _ ≤ _ := by
          refine Finset.sum_le_sum_of_subset_of_nonneg (fun p h => (hp p h).1) fun p _ _ => ?_
          split_ifs
          · exact eln _ _
          · exact le_rfl
  unfold HoleData.energyOver
  have s2 : 0 ≤ a * ∑ i ∈ Finset.range F.depth, ∑ c ∈ cutBonds (cutBelow (i + 1) D.chainSites),
      (if c.1 ∈ cutBelow (i + 1) B₃ ∨ c.1 + unitStep (i + 1) c.2 ∈ cutBelow (i + 1) B₃
        then blockFit (D.chain i) (D.chain (i + 1)) c else 0) := by
    refine mul_nonneg ha (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun c _ => ?_)
    split_ifs
    · exact ren _ _
    · exact le_rfl
  have s3 : 0 ≤ a * ∑ c ∈ cutBonds D.cells, (if c.1 ∈ B₃ ∨ c.1 + unitStep F.top c.2 ∈ B₃
      then D.topBondFit c else 0) := by
    refine mul_nonneg ha (Finset.sum_nonneg fun c _ => ?_)
    split_ifs
    · exact ren _ _
    · exact le_rfl
  linarith
variable {C : ℝ}
omit G in
theorem mem_coreCells {m : ℕ} {y : F.Cell} :
    y ∈ D.coreCells C m ↔ y ∈ D.cells ∧ ∀ z ∈ D.badCells C, m ≤ cellSupDist y z := by
  classical
  simp [HoleData.coreCells]
omit G in
theorem not_crowded_of_core {m : ℕ} (hm : 1 ≤ m) {y : F.Cell} (hy : y ∈ D.coreCells C m) :
    ¬ IsCrowded J₀ D.hotFineLumps y := by
  classical
  intro hc
  obtain ⟨h1, h2⟩ := mem_coreCells.1 hy
  have : y ∈ D.badCells C := Finset.mem_union_right _ (Finset.mem_filter.2 ⟨h1, hc⟩)
  have := h2 y this
  rw [cellSupDist_self] at this
  omega
omit G in
theorem energyOver_lt_of_core {m : ℕ} (hm : 1 ≤ m) {y : F.Cell} (hy : y ∈ D.coreCells C m) :
    D.energyOver (cellBall y 3) < C * s ^ 2 := by
  classical
  by_contra hc
  push_neg at hc
  obtain ⟨h1, h2⟩ := mem_coreCells.1 hy
  have : y ∈ D.badCells C := Finset.mem_union_left _ (Finset.mem_filter.2 ⟨h1, hc⟩)
  have := h2 y this
  rw [cellSupDist_self] at this
  omega
omit G in
theorem mem_componentsAtCore {k : Finset (Finset (F.Site F.depth))} :
    k ∈ D.componentsAtCore C ↔
      k ∈ linkComponents (holeScale J₀ (topScaleIndex J₀ F.blockSide)) D.hotFineLumps ∧
      ∃ l ∈ k, ∃ y ∈ D.coreCells C 3, l ⊆ sitesBelow F.depth y := by
  classical
  simp [HoleData.componentsAtCore, componentsNearCells]
omit G in
theorem eq_linkComponent_of_mem (X : HoleSetting D o) {r : ℕ} {k : Finset (Finset (F.Site F.depth))}
    (hk : k ∈ linkComponents r D.hotFineLumps)
    {l : Finset (F.Site F.depth)} (hl : l ∈ k) : k = linkComponent r D.hotFineLumps l ∧ l ∈ D.hotFineLumps := by
  obtain ⟨l₁, _, e⟩ := exists_of_mem_linkComponents hk
  rw [e] at hl
  refine ⟨?_, (mem_linkComponent.1 hl).1⟩
  rw [e]
  exact (X.components.eq_of_mem _ _ _ hl).symm
omit G in
theorem mem_holesAt {idx : Finset (Finset (F.Site F.depth)) → ℕ} {H : Hole F} :
    H ∈ D.holesAt C idx o ↔ ∃ k ∈ D.componentsAtCore C,
      ∃ k' ∈ componentsWithin (holeScale J₀ (idx k)) D.hotFineLumps k, H = partHole o J₀ (idx k) k' := by
  classical
  unfold HoleData.holesAt allHoles
  rw [Finset.mem_biUnion]
  constructor
  · rintro ⟨k, hk, h⟩
    exact ⟨k, hk, mem_componentHoles.1 h⟩
  · rintro ⟨k, hk, h⟩
    exact ⟨k, hk, mem_componentHoles.2 h⟩
theorem mem_cellBall_step {y c z : F.Cell} {m m' : ℕ} (hm : m + 1 ≤ m') (hc : c ∈ cellBall y m)
    (hz : cellSupDist c z ≤ 1) :
    z ∈ cellBall y m' := by
  have h1 := (G.ball_iff y m c).1 hc
  have h2 := G.cell_triangle y c z
  exact (G.ball_iff y m' z).2 (by omega)
theorem card_holes_le (X : HoleSetting D o) {idx : Finset (Finset (F.Site F.depth)) → ℕ}
    (hidx : ∀ k ∈ D.componentsAtCore C, idx k < topScaleIndex J₀ F.blockSide ∧
      IsStableIndex J₀ D.hotFineLumps k (idx k))
    (hcard : ∀ k ∈ D.componentsAtCore C, k.card < J₀) {B : Finset F.Cell} {B₂ : Finset F.Cell}
    (hB : ∀ c ∈ B, ∀ z, cellSupDist c z ≤ 1 → z ∈ B₂) :
    ∀ (A : Finset (Finset (F.Site F.depth))), (∀ l ∈ D.hotFineLumps, l ⊆ cutBelow F.depth B₂ → l ∈ A) →
    (∀ l ∈ A, l ∈ D.hotFineLumps) →
    ∀ (T : Finset (Hole F)), (∀ H ∈ T, H ∈ D.holesAt C idx o ∧ ∃ x ∈ H.outerBox, x ∈ cutBelow F.depth B) →
      T.card ≤ A.card := by
  classical
  intro A hA _ T hT
  have hphi : ∀ H : Hole F, ∃ l, H ∈ T → l ∈ H.lumps ∧ l ∈ D.hotFineLumps := by
    intro H
    by_cases hH : H ∈ T
    · obtain ⟨k, hk, k', hk', rfl⟩ := mem_holesAt.1 (hT H hH).1
      obtain ⟨l₀, m₀, hl₀, _⟩ := part_facts G X (hcard k hk) (hidx k hk).2 hk'
      exact ⟨l₀, fun _ => ⟨m₀, hl₀⟩⟩
    · exact ⟨∅, fun h => absurd h hH⟩
  choose φ hφ using hphi
  refine Finset.card_le_card_of_injOn φ ?_ ?_
  · intro H hH
    have hH' : H ∈ T := hH
    obtain ⟨h1, x, hx, hxB⟩ := hT H hH'
    obtain ⟨m₁, m₂⟩ := hφ H hH'
    obtain ⟨k, hk, k', hk', rfl⟩ := mem_holesAt.1 h1
    obtain ⟨l₀, m₀, hl₀, ho₀, _, _, hb⟩ := part_facts G X (hcard k hk) (hidx k hk).2 hk'
    refine hA _ m₂ ?_
    have hlp := isLump_spec G (hot_spec G D m₂).1
    obtain ⟨⟨u, hu⟩, _, h3⟩ := hlp
    have hdu := hb _ m₁ u (lumpCollar_of_neighbourhood G (mem_lumpNeighbourhood_self G hu))
    have hdx := (mem_outerBox G _ x).1 hx
    simp only [partHole] at hdx
    obtain ⟨r1, r2, _, r4, _⟩ := holeRadius_facts X (hidx k hk).1
    have t := G.triangle u (o k') x
    rw [G.symm u (o k')] at t
    have hle : _root_.YangMills.Construction.LumpContours.supDist u x ≤ 1 * F.blockSide := by
      have : 2 * J₀ * holeScale J₀ (idx k) ≤ holeRadius J₀ (idx k) := by
        rw [r4]
        nlinarith [Nat.zero_le (J₀ * holeScale J₀ (idx k))]
      nlinarith
    have hcd := G.cell_le 1 _ _ hle
    obtain ⟨c, hc, hxc⟩ := mem_cutBelow.1 hxB
    have hcx : enclosingCell x = c := (G.below_iff _ _).1 hxc
    rw [hcx, G.cell_symm] at hcd
    exact subset_cutBelow (h3 u hu) (hB c hc _ hcd)
  · intro H hH H' hH' e
    have a := hT H hH
    have b := hT H' hH'
    obtain ⟨m₁, m₂⟩ := hφ H hH
    obtain ⟨m₃, m₄⟩ := hφ H' hH'
    obtain ⟨k, hk, k', hk', rfl⟩ := mem_holesAt.1 a.1
    obtain ⟨k₂, hk₂, k'', hk'', rfl⟩ := mem_holesAt.1 b.1
    rw [← e] at m₃
    have s1 := (mem_componentsWithin.1 hk').2 m₁
    have s2 := (mem_componentsWithin.1 hk'').2 m₃
    have e1 := (eq_linkComponent_of_mem X (mem_componentsAtCore.1 hk).1 s1).1
    have e2 := (eq_linkComponent_of_mem X (mem_componentsAtCore.1 hk₂).1 s2).1
    have ek : k = k₂ := e1.trans e2.symm
    subst ek
    have e3 := (eq_linkComponent_of_mem X (mem_componentsWithin.1 hk').1 m₁).1
    have e4 := (eq_linkComponent_of_mem X (mem_componentsWithin.1 hk'').1 m₃).1
    rw [e3.trans e4.symm]
omit G in
theorem hot_of_mem_part (X : HoleSetting D o) {k' k : Finset (Finset (F.Site F.depth))} {r : ℕ}
    (hk' : k' ∈ componentsWithin r D.hotFineLumps k) :
    ∀ {l}, l ∈ k' → l ∈ D.hotFineLumps := by
  intro l hl
  obtain ⟨l₁, _, e⟩ := exists_of_mem_linkComponents (mem_componentsWithin.1 hk').1
  rw [e] at hl
  exact (mem_linkComponent.1 hl).1
theorem exists_hole_of_core (X : HoleSetting D o) {idx : Finset (Finset (F.Site F.depth)) → ℕ}
    (hfree : ∀ k ∈ D.componentsAtCore C, idx k < topScaleIndex J₀ F.blockSide ∧
      IsStableIndex J₀ D.hotFineLumps k (idx k))
    {l : Finset (F.Site F.depth)} (hl : l ∈ D.hotFineLumps) {y : F.Cell} (hy : y ∈ D.coreCells C 3)
    (hsub : l ⊆ sitesBelow F.depth y) :
    ∃ H ∈ D.holesAt C idx o, l ∈ H.lumps := by
  classical
  have hJ := X.one_le
  have hk : linkComponent (holeScale J₀ (topScaleIndex J₀ F.blockSide)) D.hotFineLumps l ∈ D.componentsAtCore C :=
    mem_componentsAtCore.2 ⟨Finset.mem_image_of_mem _ hl, l, X.components.mem_self _ _ hl, y, hy, hsub⟩
  have hle := (hfree _ hk).1
  refine ⟨partHole o J₀ (idx (linkComponent (holeScale J₀ (topScaleIndex J₀ F.blockSide)) D.hotFineLumps l))
    (linkComponent (holeScale J₀ (idx (linkComponent (holeScale J₀ (topScaleIndex J₀ F.blockSide))
      D.hotFineLumps l))) D.hotFineLumps l),
    mem_holesAt.2 ⟨_, hk, _, ?_, rfl⟩, X.components.mem_self _ _ hl⟩
  exact mem_componentsWithin.2 ⟨Finset.mem_image_of_mem _ hl, X.components.mono _ _ _ (holeScale_mono hJ hle.le)⟩
open Classical in
theorem annulusEnergy_sum_le_ball (X : HoleSetting D o)
    (trans : ∀ (i j m : ℕ), i ≤ j → j ≤ m → m ≤ F.top → ∀ (x : F.Site m) (w : F.Site j) (z : F.Site i),
      w ∈ sitesBelow j x → z ∈ sitesBelow i w → z ∈ sitesBelow i x)
    (uniq : ∀ (i j : ℕ), i ≤ j → j ≤ F.top → ∀ (x x' : F.Site j) (z : F.Site i),
      z ∈ sitesBelow i x → z ∈ sitesBelow i x' → x = x')
    (eln : ∀ (U : F.GaugeField 0) (p : F.Site 0 × Fin 4 × Fin 4), 0 ≤ plaquetteEnergy U p)
    (ren : ∀ (q : ℍ[ℝ]) (g : UnitQuaternion), 0 ≤ ‖q‖ - (q * (g⁻¹ : UnitQuaternion)).re) (ha : 0 ≤ a)
    {k : Finset (Finset (F.Site F.depth))} (hkc : k.card < J₀) {y : F.Cell} {m' : ℕ} (hm : 2 ≤ m')
    (hball : ∀ l ∈ k, ∃ z, cellSupDist y z ≤ 1 ∧ l ⊆ sitesBelow F.depth z) (Fr : Finset ℕ)
    (hFr : ∀ i ∈ Fr, i < topScaleIndex J₀ F.blockSide ∧ IsStableIndex J₀ D.hotFineLumps k i) :
    ∑ i ∈ Fr, ∑ H ∈ componentHoles J₀ D.hotFineLumps k i o, H.annulusEnergy (D.chain 0) ≤
      D.energyOver (cellBall y m') :=
  annulusEnergy_sum_le G X trans uniq eln ren ha hkc (fun z hz => (G.ball_iff y m' z).2 (by omega)) hball Fr hFr
open Classical in
theorem exists_good_index (X : HoleSetting D o)
    (trans : ∀ (i j m : ℕ), i ≤ j → j ≤ m → m ≤ F.top → ∀ (x : F.Site m) (w : F.Site j) (z : F.Site i),
      w ∈ sitesBelow j x → z ∈ sitesBelow i w → z ∈ sitesBelow i x)
    (uniq : ∀ (i j : ℕ), i ≤ j → j ≤ F.top → ∀ (x x' : F.Site j) (z : F.Site i),
      z ∈ sitesBelow i x → z ∈ sitesBelow i x' → x = x')
    (eln : ∀ (U : F.GaugeField 0) (p : F.Site 0 × Fin 4 × Fin 4), 0 ≤ plaquetteEnergy U p)
    (ren : ∀ (q : ℍ[ℝ]) (g : UnitQuaternion), 0 ≤ ‖q‖ - (q * (g⁻¹ : UnitQuaternion)).re) (ha : 0 ≤ a)
    {k : Finset (Finset (F.Site F.depth))}
    (c5 : k ∈ linkComponents (holeScale J₀ (topScaleIndex J₀ F.blockSide)) D.hotFineLumps →
      topScaleIndex J₀ F.blockSide + 1 ≤
        ((Finset.range (topScaleIndex J₀ F.blockSide)).filter (IsStableIndex J₀ D.hotFineLumps k)).card + k.card)
    (hk : k ∈ D.componentsAtCore C) :
    ∃ i, i < topScaleIndex J₀ F.blockSide ∧ IsStableIndex J₀ D.hotFineLumps k i ∧
      (∑ H ∈ componentHoles J₀ D.hotFineLumps k i o, H.annulusEnergy (D.chain 0)) *
        ((topScaleIndex J₀ F.blockSide : ℝ) - J₀) ≤ C * s ^ 2 := by
  have hJ := X.one_le
  have hlump : ∀ l ∈ D.hotFineLumps, IsLump g l := fun l hl => (hot_spec G D hl).1
  have hrI := le_holeScale hJ (topScaleIndex J₀ F.blockSide)
  obtain ⟨hc, l, hl, y, hy, hsub⟩ := mem_componentsAtCore.1 hk
  obtain ⟨e, hlh⟩ := eq_linkComponent_of_mem X hc hl
  have hsm := component_small G hJ hrI X.top_mul_le hlump (not_crowded_of_core (by norm_num) hy) hlh hsub
  rw [← e] at hsm
  obtain ⟨hkc, hball⟩ := hsm
  have hcount := c5 hc
  have t1 := X.top_ge
  have hFr : ∀ i ∈ (Finset.range (topScaleIndex J₀ F.blockSide)).filter (IsStableIndex J₀ D.hotFineLumps k),
      i < topScaleIndex J₀ F.blockSide ∧ IsStableIndex J₀ D.hotFineLumps k i := fun i hi => by
    obtain ⟨a1, a2⟩ := Finset.mem_filter.1 hi
    exact ⟨Finset.mem_range.1 a1, a2⟩
  have hsum := annulusEnergy_sum_le_ball G X trans uniq eln ren ha hkc (m' := 3) (by norm_num) hball _ hFr
  have hexc := energyOver_lt_of_core (C := C) (by norm_num) hy
  have hne : ((Finset.range (topScaleIndex J₀ F.blockSide)).filter
      (IsStableIndex J₀ D.hotFineLumps k)).Nonempty := by
    rw [← Finset.card_pos]
    omega
  obtain ⟨i, hi, hmin⟩ := Finset.exists_min_image _
    (fun i => ∑ H ∈ componentHoles J₀ D.hotFineLumps k i o, H.annulusEnergy (D.chain 0)) hne
  refine ⟨i, (hFr i hi).1, (hFr i hi).2, ?_⟩
  have h1 := Finset.card_nsmul_le_sum _ _ _ hmin
  rw [nsmul_eq_mul] at h1
  have hT : 0 ≤ ∑ H ∈ componentHoles J₀ D.hotFineLumps k i o, H.annulusEnergy (D.chain 0) :=
    Finset.sum_nonneg fun H _ => Finset.sum_nonneg fun p _ => eln _ _
  have hcc : (topScaleIndex J₀ F.blockSide : ℝ) - J₀ ≤
      (((Finset.range (topScaleIndex J₀ F.blockSide)).filter (IsStableIndex J₀ D.hotFineLumps k)).card : ℝ) := by
    have : topScaleIndex J₀ F.blockSide ≤
        ((Finset.range (topScaleIndex J₀ F.blockSide)).filter (IsStableIndex J₀ D.hotFineLumps k)).card + J₀ := by
      omega
    have h2 : (topScaleIndex J₀ F.blockSide : ℝ) ≤
        (((Finset.range (topScaleIndex J₀ F.blockSide)).filter (IsStableIndex J₀ D.hotFineLumps k)).card : ℝ) +
          J₀ := by
      exact_mod_cast this
    linarith
  have h3 := mul_le_mul_of_nonneg_left hcc hT
  nlinarith
open Classical in
theorem card_holes_meeting_le (X : HoleSetting D o) {idx : Finset (Finset (F.Site F.depth)) → ℕ}
    (hidx : ∀ k ∈ D.componentsAtCore C, idx k < topScaleIndex J₀ F.blockSide ∧
      IsStableIndex J₀ D.hotFineLumps k (idx k))
    (hcard : ∀ k ∈ D.componentsAtCore C, k.card < J₀) {m m' : ℕ} (hm : m + 1 ≤ m') (y : F.Cell) :
    ((D.holesAt C idx o).filter fun H => (H.outerBox ∩ cutBelow F.depth (cellBall y m)).Nonempty).card ≤
      (D.hotFineLumps.filter fun l => l ⊆ cutBelow F.depth (cellBall y m')).card := by
  refine card_holes_le G X hidx hcard (B := cellBall y m) (B₂ := cellBall y m')
    (fun c hc z hz => mem_cellBall_step G hm hc hz) _ (fun l hl hs => Finset.mem_filter.2 ⟨hl, hs⟩)
    (fun l hl => (Finset.mem_filter.1 hl).1) _ fun H hH => ?_
  obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hH
  obtain ⟨x, hx⟩ := h2
  exact ⟨h1, x, (Finset.mem_inter.1 hx).1, (Finset.mem_inter.1 hx).2⟩
open Classical in
theorem isHoleFamily_of (X : HoleSetting D o) {idx : Finset (Finset (F.Site F.depth)) → ℕ}
    (hidx : ∀ k ∈ D.componentsAtCore C, idx k < topScaleIndex J₀ F.blockSide ∧
      IsStableIndex J₀ D.hotFineLumps k (idx k) ∧
      (∑ H ∈ componentHoles J₀ D.hotFineLumps k (idx k) o, H.annulusEnergy (D.chain 0)) *
        ((topScaleIndex J₀ F.blockSide : ℝ) - J₀) ≤ C * s ^ 2) :
    D.IsHoleFamily C idx o := by
  have hJ := X.one_le
  have hlump : ∀ l ∈ D.hotFineLumps, IsLump g l := fun l hl => (hot_spec G D hl).1
  have t3 := X.top_mul_le
  have hrI := le_holeScale hJ (topScaleIndex J₀ F.blockSide)
  have hcard : ∀ k ∈ D.componentsAtCore C, k.card < J₀ := by
    intro k hk
    obtain ⟨hc, l, hl, y, hy, hsub⟩ := mem_componentsAtCore.1 hk
    obtain ⟨e, hlh⟩ := eq_linkComponent_of_mem X hc hl
    rw [e]
    exact (component_small G hJ hrI t3 hlump (not_crowded_of_core (by norm_num) hy) hlh hsub).1
  have hfree := fun k hk => (⟨(hidx k hk).1, (hidx k hk).2.1⟩ :
    idx k < topScaleIndex J₀ F.blockSide ∧ IsStableIndex J₀ D.hotFineLumps k (idx k))
  have hdouble : ∀ i, 2 * J₀ * holeScale J₀ i ≤ holeRadius J₀ i := fun i => by
    have h4 : holeRadius J₀ i = 4 * J₀ * holeScale J₀ i := rfl
    rw [h4]
    nlinarith [Nat.zero_le (J₀ * holeScale J₀ i)]
  refine ⟨hfree, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun k hk => (hidx k hk).2.2⟩
  · intro k hk y hy l hl hsub
    obtain ⟨e, hlh⟩ := eq_linkComponent_of_mem X (mem_componentsAtCore.1 hk).1 hl
    rw [e]
    obtain ⟨s1, s2⟩ := component_small G hJ hrI t3 hlump (not_crowded_of_core (by norm_num) hy) hlh hsub
    refine ⟨s1, fun l' hl' => ?_⟩
    obtain ⟨z, hz, hs⟩ := s2 l' hl'
    exact subset_cutBelow hs ((G.ball_iff y 1 z).2 hz)
  · intro H hH
    obtain ⟨k, hk, k', hk', rfl⟩ := mem_holesAt.1 hH
    have r := holeRadius_facts X (hfree k hk).1
    exact ⟨r.1, r.2.1⟩
  · intro H hH l hl u hu
    obtain ⟨k, hk, k', hk', rfl⟩ := mem_holesAt.1 hH
    obtain ⟨_, _, _, _, _, _, hb⟩ := part_facts G X (hcard k hk) (hfree k hk).2 hk'
    refine (mem_innerBox G _ u).2 ?_
    exact (hb l hl u hu).trans (hdouble _)
  · intro H hH l hl p hp
    obtain ⟨k, hk, k', hk', rfl⟩ := mem_holesAt.1 hH
    obtain ⟨_, _, _, _, _, _, hb⟩ := part_facts G X (hcard k hk) (hfree k hk).2 hk'
    obtain ⟨⟨u, hu⟩, _, _⟩ := isLump_spec G (hlump l ((hot_of_mem_part X hk') hl))
    refine (G.thicken_iff _ _ _).2 ⟨u, hu, ?_⟩
    have h1 := hb l hl u (lumpCollar_of_neighbourhood G (mem_lumpNeighbourhood_self G hu))
    have h2 := (mem_outerBox G _ p).1 hp
    simp only [partHole] at h2 ⊢
    have t := G.triangle u (o k') p
    rw [G.symm u (o k')] at t
    have := hdouble (idx k)
    omega
  · intro H hH l hl hl'
    obtain ⟨k, hk, k', hk', rfl⟩ := mem_holesAt.1 hH
    exact outer_not_within G X (hcard k hk) (hfree k hk).2 hk' (hfree k hk).1 hl hl'
  · intro H hH l hl
    obtain ⟨k, hk, k', hk', rfl⟩ := mem_holesAt.1 hH
    exact annulus_not_within G X (hcard k hk) (hfree k hk).2 hk' (hfree k hk).1 hl
  · intro H hH x hx
    obtain ⟨k, hk, k', hk', rfl⟩ := mem_holesAt.1 hH
    exact thicken_outer_walls G X (hcard k hk) (hfree k hk).2 hk' (hfree k hk).1 hx
  · intro H hH H' hH' hne hw
    obtain ⟨ka, hka, k₁, hk₁, rfl⟩ := mem_holesAt.1 hH
    obtain ⟨kb, hkb, k₂, hk₂, rfl⟩ := mem_holesAt.1 hH'
    by_cases hab : ka = kb
    · subst hab
      have hk12 : k₁ ≠ k₂ := fun e => hne (by rw [e])
      refine outer_apart G X (hcard ka hka) (hfree ka hka).2 hk₁ hk₂ hk12 ?_
      obtain ⟨p, hp, q, hq, d⟩ := hw
      refine ⟨p, hp, q, hq, ?_⟩
      simpa [partHole] using d
    · obtain ⟨p, hp, q, hq, d⟩ := hw
      obtain ⟨l₁, m₁, hl₁, ho₁, _, _, _⟩ := part_facts G X (hcard ka hka) (hfree ka hka).2 hk₁
      obtain ⟨l₂, m₂, hl₂, ho₂, _, _, _⟩ := part_facts G X (hcard kb hkb) (hfree kb hkb).2 hk₂
      have a1 := (mem_outerBox G _ p).1 hp
      have a2 := (mem_outerBox G _ q).1 hq
      simp only [partHole] at a1 a2 d
      obtain ⟨_, _, b1, _, _⟩ := holeRadius_facts X (hfree ka hka).1
      obtain ⟨_, _, b2, _, _⟩ := holeRadius_facts X (hfree kb hkb).1
      have hM : 10 * max (holeRadius J₀ (idx ka)) (holeRadius J₀ (idx kb)) ≤
          holeScale J₀ (topScaleIndex J₀ F.blockSide) := by
        rcases le_total (holeRadius J₀ (idx ka)) (holeRadius J₀ (idx kb)) with h | h
        · rw [max_eq_right h]; exact b2
        · rw [max_eq_left h]; exact b1
      have c1 := le_max_left (holeRadius J₀ (idx ka)) (holeRadius J₀ (idx kb))
      have c2 := le_max_right (holeRadius J₀ (idx ka)) (holeRadius J₀ (idx kb))
      have t1 := G.triangle (o k₁) p (o k₂)
      have t2 := G.triangle p q (o k₂)
      rw [G.symm q (o k₂)] at t2
      have hw' : AreWithin (holeScale J₀ (topScaleIndex J₀ F.blockSide)) (lumpNeighbourhood l₁)
          (lumpNeighbourhood l₂) :=
        ⟨o k₁, mem_lumpNeighbourhood_self G ho₁, o k₂, mem_lumpNeighbourhood_self G ho₂, by omega⟩
      have s1 := (mem_componentsWithin.1 hk₁).2 m₁
      have s2 := (mem_componentsWithin.1 hk₂).2 m₂
      obtain ⟨e1, _⟩ := eq_linkComponent_of_mem X (mem_componentsAtCore.1 hka).1 s1
      obtain ⟨e2, _⟩ := eq_linkComponent_of_mem X (mem_componentsAtCore.1 hkb).1 s2
      have hm : l₂ ∈ linkComponent (holeScale J₀ (topScaleIndex J₀ F.blockSide)) D.hotFineLumps l₁ :=
        mem_linkComponent.2 ⟨hl₂, Relation.ReflTransGen.single ⟨hl₁, hl₂, hw'⟩⟩
      apply hab
      rw [e1, e2]
      exact (X.components.eq_of_mem _ _ _ hm).symm
  · intro l hl y hy hsub
    exact exists_hole_of_core G X hfree hl hy hsub
  · intro l hl y hy hne
    obtain ⟨x, hx⟩ := hne
    obtain ⟨hx1, hx2⟩ := Finset.mem_inter.1 hx
    obtain ⟨v, hv, hvx⟩ := (mem_lumpNeighbourhood G).1 hx1
    have hcx : enclosingCell x = y := (G.below_iff _ _).1 hx2
    have hd : _root_.YangMills.Construction.LumpContours.supDist v x ≤ 1 * F.blockSide := by
      have : 2 ^ 12 ≤ F.blockSide := by nlinarith
      omega
    have hcd := G.cell_le 1 _ _ hd
    rw [hcx] at hcd
    obtain ⟨_, _, h3⟩ := isLump_spec G (hlump l hl)
    obtain ⟨y', hy', hsub'⟩ := (hot_spec G D hl).2
    have hcv : enclosingCell v = y' := (G.below_iff _ _).1 (hsub' hv)
    refine exists_hole_of_core G X hfree hl (y := enclosingCell v)
      (mem_coreCells.2 ⟨by rw [hcv]; exact hy', fun z hz => ?_⟩) (h3 v hv)
    have a1 := (mem_coreCells.1 hy).2 z hz
    have a2 := G.cell_triangle y (enclosingCell v) z
    rw [G.cell_symm y (enclosingCell v)] at a2
    omega
  · intro H hH l hl l' hl' hw
    obtain ⟨k, hk, k', hk', rfl⟩ := mem_holesAt.1 hH
    obtain ⟨l₀, _, _, _, _, e3, _⟩ := part_facts G X (hcard k hk) (hfree k hk).2 hk'
    have hl2 : l ∈ k' := hl
    rw [e3] at hl2
    have e4 := X.components.eq_of_mem _ _ _ hl2
    have hlh := (mem_linkComponent.1 hl2).1
    obtain ⟨x, hx, z, hz, d⟩ := hw
    have hmono : holeScale J₀ 1 ≤ holeScale J₀ (idx k + 1) := holeScale_mono hJ (by omega)
    have hm : l' ∈ linkComponent (holeScale J₀ (idx k + 1)) D.hotFineLumps l :=
      mem_linkComponent.2 ⟨hl', Relation.ReflTransGen.single ⟨hlh, hl', ⟨x, hx, z, hz, d.trans hmono⟩⟩⟩
    show l' ∈ k'
    rw [e3, ← e4]
    exact hm
  · intro y hnc
    have hAc : (nearbyLumps D.hotFineLumps y).card < J₀ := by
      have : ¬ J₀ ≤ (nearbyLumps D.hotFineLumps y).card := hnc
      omega
    exact lt_of_le_of_lt (card_holes_meeting_le G X hfree hcard (m := 1) (m' := 2) (by norm_num) y) hAc
end HoleDataFacts
end HoleFamilyProof
open HoleFamilyProof in
theorem holeFamilyExists (hd : TorusDistanceBlockLumpFacts) (hcp : LinkComponentProperties)
    (hsu : NestedSiteFacts) : holeFamilyExistsStatement := by
  intro J₀ hJ
  refine ⟨holeScale J₀ (2 * J₀) ^ 2, fun L hLo hLf => ?_⟩
  obtain ⟨t1, t2, t3⟩ := topScaleIndex_facts hJ hLf
  refine ⟨t1, ?_⟩
  intro g a C s θ F D ha hFL hs
  subst hFL
  classical
  have hs' : ∀ i, 0 < F.extent i := fun i => by have := hs i; omega
  have G : SiteGeometry F := siteGeometry_of hd hLo hs'
  obtain ⟨su1, ren⟩ := hsu
  obtain ⟨trans, uniq, eln⟩ := su1 F hLo hs'
  obtain ⟨c1, c2, c3, _, c5⟩ := hcp F D.hotFineLumps
  have hlump : ∀ l ∈ D.hotFineLumps, IsLump g l := fun l hl => (hot_spec G D hl).1
  have hex : ∀ k' : Finset (Finset (F.Site F.depth)), ∃ x : F.Site F.depth,
      (∃ l ∈ k', l ∈ D.hotFineLumps) → ∃ l ∈ k', x ∈ l := by
    intro k'
    by_cases h : ∃ l ∈ k', l ∈ D.hotFineLumps
    · obtain ⟨l, hl, hlh⟩ := h
      obtain ⟨⟨u, hu⟩, _, _⟩ := isLump_spec G (hlump l hlh)
      exact ⟨u, fun _ => ⟨l, hl, hu⟩⟩
    · exact ⟨0, fun h' => absurd h' h⟩
  choose o ho using hex
  have X : HoleSetting D o := ⟨hJ, hLo, hs, t1, t2, t3, ⟨c1, c2, c3⟩, ho⟩
  have hrI := le_holeScale hJ (topScaleIndex J₀ F.blockSide)
  have pick : ∀ k : Finset (Finset (F.Site F.depth)), ∃ i, k ∈ D.componentsAtCore C →
      i < topScaleIndex J₀ F.blockSide ∧
      IsStableIndex J₀ D.hotFineLumps k i ∧
      (∑ H ∈ componentHoles J₀ D.hotFineLumps k i o, H.annulusEnergy (D.chain 0)) *
        ((topScaleIndex J₀ F.blockSide : ℝ) - J₀) ≤ C * s ^ 2 := by
    intro k
    by_cases hk : k ∈ D.componentsAtCore C
    · obtain ⟨i, hi⟩ := exists_good_index G X trans uniq eln ren (by linarith)
        (c5 J₀ (topScaleIndex J₀ F.blockSide) k hJ) hk
      exact ⟨i, fun _ => hi⟩
    · exact ⟨0, fun h => absurd h hk⟩
  choose idx hidx using pick
  exact ⟨idx, o, isHoleFamily_of G X hidx⟩
end HoleFilling
end YangMills.Construction
end
