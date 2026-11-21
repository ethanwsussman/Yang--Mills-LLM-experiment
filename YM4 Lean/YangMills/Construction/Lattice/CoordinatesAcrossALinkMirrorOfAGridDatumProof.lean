import YangMills.Construction.Lattice.ActionAcrossALinkMirrorOfAGridDatumProof
import YangMills.Construction.Lattice.CoordinatesAcrossALinkMirrorOfAGridDatum
import YangMills.Construction.Matrices.RelabellingOfProductsOfHaarMeasures
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.GridMirror.CoordinateSplit
open MeasureTheory YangMills.Construction.BoxTorus
open YangMills.Construction.GridMirror YangMills.Construction.TorusDescent
open YangMills.Construction.MirrorLayers
open YangMills.Construction.Matrices.ComplexMatrix2.HaarRelabel
variable {L : ℕ} {κ : ℤ} {d : YangMills.Construction.CellGrid L κ}
theorem lt_two_mul_mod_cases {n m : ℕ} (hn : n < 2 * m) :
    (n < m ∧ n % m = n) ∨ (m ≤ n ∧ n % m = n - m) := by
  rcases lt_or_ge n m with hlt | hge
  · exact Or.inl ⟨hlt, Nat.mod_eq_of_lt hlt⟩
  · refine Or.inr ⟨hge, ?_⟩
    rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt (by omega)]
theorem zmod_val_one {h : ℕ} (h2 : 2 ≤ h) : (1 : ZMod (2 * h)).val = 1 := by
  rw [ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt (by omega)]
theorem val_mem_Icc_iff_one_sub_not {h : ℕ} (h2 : 2 ≤ h) (a : ZMod (2 * h)) :
    a.val ∈ Finset.Icc 1 h ↔ (1 - a).val ∉ Finset.Icc 1 h := by
  have : NeZero (2 * h) := ⟨by omega⟩
  have e := ZMod.val_add a (1 - a)
  rw [add_sub_cancel, zmod_val_one h2] at e
  have ha := ZMod.val_lt a
  have hb := ZMod.val_lt (1 - a)
  have hc := lt_two_mul_mod_cases (n := a.val + (1 - a).val) (m := 2 * h) (by omega)
  simp only [Finset.mem_Icc]
  omega
theorem eq_top_of_add_one_exit {h : ℕ} (h2 : 2 ≤ h) {a : ZMod (2 * h)}
    (ha : a.val ∈ Finset.Icc 1 h) (hb : (a + 1).val ∉ Finset.Icc 1 h) :
    a = (h : ZMod (2 * h)) := by apply _root_.YangMills.Construction.MirrorActionSplit.eq_half_of_exit <;> assumption
theorem add_one_eq_one_of_not_mem_of_add_one_mem {h : ℕ} (h2 : 2 ≤ h) {a : ZMod (2 * h)}
    (ha : a.val ∉ Finset.Icc 1 h) (hb : (a + 1).val ∈ Finset.Icc 1 h) : a + 1 = 1 := by apply _root_.YangMills.Construction.MirrorActionSplit.add_one_eq_one_of_not_mem_of_add_one_mem <;> assumption
def forwardPart (b : d.DirectedEdge) : d.ForwardEdge :=
  open Classical in
  if hf : b.IsForward then ⟨b, hf⟩ else ⟨b.flip, DirectedEdge.flip_isForward hf⟩
theorem ends_forwardPart (b : d.DirectedEdge) : (forwardPart b).1.ends = b.ends := by
  by_cases hf : b.IsForward
  · rw [forwardPart, dif_pos hf]
  · rw [forwardPart, dif_neg hf]
    exact Set.pair_comm _ _
abbrev CoordIndex (g : d.GridSymmetry) (H : Set d.Space) : Type :=
  HalfEdge d H ⊕ HalfEdge d H ⊕ MirrorPairedPoint g H
def edgeAt (g : d.GridSymmetry) (H : Set d.Space) :
    CoordIndex g H → d.DirectedEdge
  | .inl b => b.1.1
  | .inr (.inl b) => g.edgeImage b.1.1
  | .inr (.inr y) => mirrorEdge y
def forwardEdgeEquiv {g : d.GridSymmetry} {H : Set d.Space}
    (hb : Function.Bijective fun t => forwardPart (edgeAt g H t)) :
    d.ForwardEdge ≃ CoordIndex g H :=
  (Equiv.ofBijective _ hb).symm
def flipFlag {g : d.GridSymmetry} {H : Set d.Space}
    (hb : Function.Bijective fun t => forwardPart (edgeAt g H t)) (p : d.ForwardEdge) : Bool :=
  open Classical in decide (¬ (edgeAt g H (forwardEdgeEquiv hb p)).IsForward)
theorem edgeVariable_relabel {g : d.GridSymmetry} {H : Set d.Space}
    (hb : Function.Bijective fun t => forwardPart (edgeAt g H t))
    (x : (HalfEdge d H → YangMills.Construction.Matrices.ComplexMatrix2.specialUnitary) ×
      (HalfEdge d H → YangMills.Construction.Matrices.ComplexMatrix2.specialUnitary) ×
      (MirrorPairedPoint g H → YangMills.Construction.Matrices.ComplexMatrix2.specialUnitary))
    (t : CoordIndex g H) :
    edgeVariable (relabel (forwardEdgeEquiv hb) (flipFlag hb) x) (edgeAt g H t) =
      Sum.elim x.1 (Sum.elim x.2.1 x.2.2) t := by
  have hep : forwardEdgeEquiv hb (forwardPart (edgeAt g H t)) = t :=
    (Equiv.ofBijective _ hb).symm_apply_apply t
  by_cases hp : (edgeAt g H t).IsForward
  · have e : forwardPart (edgeAt g H t) = ⟨edgeAt g H t, hp⟩ := dif_pos hp
    have hf : flipFlag hb (forwardPart (edgeAt g H t)) = false := by
      simp [flipFlag, hep, hp]
    rw [edgeVariable, dif_pos hp, ← e, relabel, hf, hep]
    rfl
  · have e : forwardPart (edgeAt g H t) =
        ⟨(edgeAt g H t).flip, DirectedEdge.flip_isForward hp⟩ := dif_neg hp
    have hf : flipFlag hb (forwardPart (edgeAt g H t)) = true := by
      simp [flipFlag, hep, hp]
    rw [edgeVariable, dif_neg hp, ← e, relabel, hf, hep]
    simp
theorem ends_edgeImage (hLD : YangMills.Construction.GridLattice.EdgesByDistance d)
    (g : d.GridSymmetry) (b : d.DirectedEdge) :
    (g.edgeImage b).ends = {g.pointImage b.source, g.pointImage b.target} := by
  obtain ⟨h₁, h₂⟩ := g.edgeImage_endpoints hLD b
  rw [DirectedEdge.ends, h₁, h₂]
theorem mem_posHalf_iff_not_image {g : d.GridSymmetry} {μ : Fin 4} {c : ℝ} {h : ℕ}
    (h2 : 2 ≤ h) {layer : d.GridPoint → ZMod (2 * h)} (hl : IsMirrorLayering g μ c h layer)
    (x : d.GridPoint) :
    (x : d.Space) ∈ posHalf d μ c ↔ ¬ ((g.pointImage x : d.GridPoint) : d.Space) ∈ posHalf d μ c := by
  obtain ⟨-, -, hg, -, -, -, hup, -⟩ := hl
  rw [hup, hup, hg]
  exact val_mem_Icc_iff_one_sub_not h2 (layer x)
theorem bijective_forwardPart_edgeAt (hLP : YangMills.Construction.GridLattice.EdgesAndFaces d)
    (hLD : YangMills.Construction.GridLattice.EdgesByDistance d) {g : d.GridSymmetry} {μ : Fin 4}
    {c : ℝ} {h : ℕ} (h2 : 2 ≤ h) {layer : d.GridPoint → ZMod (2 * h)}
    (hl : IsMirrorLayering g μ c h layer) :
    Function.Bijective fun t => forwardPart (edgeAt g (posHalf d μ c) t) := by
  have hswap := mem_posHalf_iff_not_image h2 hl
  obtain ⟨hstep, hother, -, -, -, hinv, hup, -, h1, hh, hcont, -⟩ := hl
  have hpos : ∀ b b' : d.DirectedEdge, b.IsForward → b'.IsForward →
      b.ends = b'.ends → b = b' := hLP.2.2.2.1
  have hinj : Function.Injective g.pointImage := Function.LeftInverse.injective hinv
  have hin : ∀ (b : HalfEdge d (posHalf d μ c)),
      (b.1.1.source : d.Space) ∈ posHalf d μ c ∧ (b.1.1.target : d.Space) ∈ posHalf d μ c :=
    fun b => (hcont b.1.1).1 b.2
  constructor
  · intro t t' e
    have he : (edgeAt g (posHalf d μ c) t).ends =
        (edgeAt g (posHalf d μ c) t').ends := by
      rw [← ends_forwardPart, ← ends_forwardPart (edgeAt g (posHalf d μ c) t')]
      exact congrArg (fun p : d.ForwardEdge => p.1.ends) e
    rcases t with b | b | y <;> rcases t' with b' | b' | y'
    · exact congrArg Sum.inl (Subtype.ext (Subtype.ext (hpos _ _ b.1.2 b'.1.2 he)))
    · exfalso
      have he' : ({b.1.1.source, b.1.1.target} : Set d.GridPoint) =
          {g.pointImage b'.1.1.source, g.pointImage b'.1.1.target} := by
        rw [← ends_edgeImage hLD]
        exact he
      rcases Set.pair_eq_pair_iff.mp he' with ⟨e₁, -⟩ | ⟨e₁, -⟩
      · exact (hswap _).mp (hin b').1 (e₁ ▸ (hin b).1)
      · exact (hswap _).mp (hin b').2 (e₁ ▸ (hin b).1)
    · exfalso
      have he' : ({b.1.1.source, b.1.1.target} : Set d.GridPoint) =
          {g.pointImage y'.1, y'.1} := he
      rcases Set.pair_eq_pair_iff.mp he' with ⟨e₁, -⟩ | ⟨-, e₁⟩
      · exact (hswap _).mp y'.2.1 (e₁ ▸ (hin b).1)
      · exact (hswap _).mp y'.2.1 (e₁ ▸ (hin b).2)
    · exfalso
      have he' : ({g.pointImage b.1.1.source, g.pointImage b.1.1.target} : Set d.GridPoint) =
          {b'.1.1.source, b'.1.1.target} := by
        rw [← ends_edgeImage hLD]
        exact he
      rcases Set.pair_eq_pair_iff.mp he' with ⟨e₁, -⟩ | ⟨e₁, -⟩
      · exact (hswap _).mp (hin b).1 (e₁ ▸ (hin b').1)
      · exact (hswap _).mp (hin b).1 (e₁ ▸ (hin b').2)
    · have he' : ({g.pointImage b.1.1.source, g.pointImage b.1.1.target} : Set d.GridPoint) =
          {g.pointImage b'.1.1.source, g.pointImage b'.1.1.target} := by
        rw [← ends_edgeImage hLD, ← ends_edgeImage hLD]
        exact he
      have hends : b.1.1.ends = b'.1.1.ends := by
        rcases Set.pair_eq_pair_iff.mp he' with ⟨e₁, e₂⟩ | ⟨e₁, e₂⟩
        · rw [DirectedEdge.ends, DirectedEdge.ends, hinj e₁, hinj e₂]
        · rw [DirectedEdge.ends, DirectedEdge.ends, hinj e₁, hinj e₂]
          exact Set.pair_comm _ _
      exact congrArg (fun u => Sum.inr (Sum.inl u))
        (Subtype.ext (Subtype.ext (hpos _ _ b.1.2 b'.1.2 hends)))
    · exfalso
      have he' : ({g.pointImage b.1.1.source, g.pointImage b.1.1.target} : Set d.GridPoint) =
          {g.pointImage y'.1, y'.1} := by
        rw [← ends_edgeImage hLD]
        exact he
      rcases Set.pair_eq_pair_iff.mp he' with ⟨-, e₁⟩ | ⟨e₁, -⟩
      · exact (hswap _).mp (hin b).2 (e₁ ▸ y'.2.1)
      · exact (hswap _).mp (hin b).1 (e₁ ▸ y'.2.1)
    · exfalso
      have he' : ({g.pointImage y.1, y.1} : Set d.GridPoint) = {b'.1.1.source, b'.1.1.target} := he
      rcases Set.pair_eq_pair_iff.mp he' with ⟨e₁, -⟩ | ⟨e₁, -⟩
      · exact (hswap _).mp y.2.1 (e₁ ▸ (hin b').1)
      · exact (hswap _).mp y.2.1 (e₁ ▸ (hin b').2)
    · exfalso
      have he' : ({g.pointImage y.1, y.1} : Set d.GridPoint) =
          {g.pointImage b'.1.1.source, g.pointImage b'.1.1.target} := by
        rw [← ends_edgeImage hLD]
        exact he
      rcases Set.pair_eq_pair_iff.mp he' with ⟨-, e₁⟩ | ⟨-, e₁⟩
      · exact (hswap _).mp (hin b').2 (e₁ ▸ y.2.1)
      · exact (hswap _).mp (hin b').1 (e₁ ▸ y.2.1)
    · have he' : ({g.pointImage y.1, y.1} : Set d.GridPoint) = {g.pointImage y'.1, y'.1} := he
      rcases Set.pair_eq_pair_iff.mp he' with ⟨-, e₁⟩ | ⟨-, e₁⟩
      · exact congrArg (fun u => Sum.inr (Sum.inr u)) (Subtype.ext e₁)
      · exact ((hswap _).mp y'.2.1 (e₁ ▸ y.2.1)).elim
  · intro p
    suffices hs : ∃ t, (edgeAt g (posHalf d μ c) t).ends = p.1.ends by
      obtain ⟨t, ht⟩ := hs
      exact ⟨t, Subtype.ext (hpos _ _ (forwardPart _).2 p.2 (by rw [ends_forwardPart, ht]))⟩
    obtain ⟨ν, hν⟩ := p.2
    have htarget : p.1.target = p.1.source + gridStep L κ d.sideLengths ν :=
      Subtype.ext (by rw [hν.2, one_mul]; rfl)
    have hcross : ((p.1.source : d.Space) ∈ posHalf d μ c ↔
        ¬ (p.1.target : d.Space) ∈ posHalf d μ c) →
        layer p.1.target = layer p.1.source + 1 ∧
          p.1.target = p.1.source + gridStep L κ d.sideLengths μ := by
      intro hx
      have hνμ : ν = μ := by
        by_contra hne
        have hk := hother p.1.source ν hne
        rw [← htarget] at hk
        have : (p.1.source : d.Space) ∈ posHalf d μ c ↔
            (p.1.target : d.Space) ∈ posHalf d μ c := by
          rw [hup, hup, hk]
        tauto
      subst hνμ
      exact ⟨by rw [htarget]; exact hstep _, htarget⟩
    by_cases a : (p.1.source : d.Space) ∈ posHalf d μ c <;>
      by_cases b : (p.1.target : d.Space) ∈ posHalf d μ c
    · exact ⟨.inl ⟨p, (hcont p.1).2 ⟨a, b⟩⟩, rfl⟩
    · obtain ⟨hk, hs⟩ := hcross (by tauto)
      have hx : layer p.1.source = (h : ZMod (2 * h)) := by
        refine eq_top_of_add_one_exit h2 ((hup _).mp a) ?_
        rw [← hk]
        exact fun m => b ((hup _).mpr m)
      have hgx : g.pointImage p.1.source = p.1.target := by rw [hh _ hx, ← hs]
      refine ⟨.inr (.inr ⟨p.1.source, (⟨a, p.1.flip, hgx.symm, rfl⟩ :
        (p.1.source : d.Space) ∈ posHalf d μ c ∧ ∃ b : d.DirectedEdge,
          b.source = g.pointImage p.1.source ∧ b.target = p.1.source)⟩), ?_⟩
      show ({g.pointImage p.1.source, p.1.source} : Set d.GridPoint) = {p.1.source, p.1.target}
      rw [hgx]
      exact Set.pair_comm _ _
    · obtain ⟨hk, hs⟩ := hcross (by tauto)
      have hx : layer p.1.target = 1 := by
        rw [hk]
        refine add_one_eq_one_of_not_mem_of_add_one_mem h2 (fun m => a ((hup _).mpr m)) ?_
        rw [← hk]
        exact (hup _).mp b
      have hgx : g.pointImage p.1.target = p.1.source := by
        rw [h1 _ hx, hs, add_sub_cancel_right]
      refine ⟨.inr (.inr ⟨p.1.target, (⟨b, p.1, hgx.symm, rfl⟩ :
        (p.1.target : d.Space) ∈ posHalf d μ c ∧ ∃ b : d.DirectedEdge,
          b.source = g.pointImage p.1.target ∧ b.target = p.1.target)⟩), ?_⟩
      show ({g.pointImage p.1.target, p.1.target} : Set d.GridPoint) = {p.1.source, p.1.target}
      rw [hgx]
    · have hga : ((g.pointImage p.1.source : d.GridPoint) : d.Space) ∈ posHalf d μ c :=
        by_contra fun n => a ((hswap _).mpr n)
      have hgb : ((g.pointImage p.1.target : d.GridPoint) : d.Space) ∈ posHalf d μ c :=
        by_contra fun n => b ((hswap _).mpr n)
      have hq : (forwardPart (g.edgeImage p.1)).1.ends =
          {g.pointImage p.1.source, g.pointImage p.1.target} := by
        rw [ends_forwardPart, ends_edgeImage hLD]
      have hqin : ∀ z ∈ (forwardPart (g.edgeImage p.1)).1.ends,
          (z : d.Space) ∈ posHalf d μ c := by
        intro z hz
        rw [hq] at hz
        rcases hz with rfl | hz
        · exact hga
        · rw [Set.mem_singleton_iff.mp hz]
          exact hgb
      refine ⟨.inr (.inl ⟨forwardPart (g.edgeImage p.1),
        (hcont _).2 ⟨hqin _ (Or.inl rfl), hqin _ (Or.inr rfl)⟩⟩), ?_⟩
      show (g.edgeImage (forwardPart (g.edgeImage p.1)).1).ends = _
      rw [ends_edgeImage hLD]
      rw [DirectedEdge.ends] at hq
      rcases Set.pair_eq_pair_iff.mp hq with ⟨e₁, e₂⟩ | ⟨e₁, e₂⟩
      · rw [e₁, e₂, hinv, hinv]
        rfl
      · rw [e₁, e₂, hinv, hinv]
        exact Set.pair_comm _ _
theorem mirrorCoordinates_holds (hLay : YangMills.Construction.MirrorLayers.LayeringTheorem)
    (hRel : YangMills.Construction.Matrices.ComplexMatrix2.HaarRelabel.Statement)
    (hLat : YangMills.Construction.GridLattice.Properties) :
    YangMills.Construction.GridMirror.MirrorCoordinates := by
  intro L κ d g μ c hg
  obtain ⟨h, h2, layer, hl⟩ := hLay L κ d g μ c hg
  obtain ⟨-, hLP, -, hLD, -⟩ := hLat L κ d
  have hb := bijective_forwardPart_edgeAt hLP hLD h2 hl
  obtain ⟨hm, hmap⟩ := hRel _ _ _ (forwardEdgeEquiv hb) (flipFlag hb)
  refine ⟨relabel (forwardEdgeEquiv hb) (flipFlag hb), hm, hmap,
    fun x => ⟨fun b => ?_, fun b => ?_, fun y => ?_⟩⟩
  · exact edgeVariable_relabel hb x (.inl b)
  · exact edgeVariable_relabel hb x (.inr (.inl b))
  · exact edgeVariable_relabel hb x (.inr (.inr y))
end YangMills.Construction.GridMirror.CoordinateSplit
end
