import YangMills.Construction.Lattice.BareBaseSitesOfTheSchemesProof
import YangMills.Construction.Lattice.WeightedDistanceOfASeparatedSequence
import YangMills.Construction.RunningCouplingSlope.CellsOfNeighbouringFineSites
import YangMills.Construction.RunningCouplingSlope.FewIndicesLieNearACell
import YangMills.Construction.SystemOfAdmissibleConstants.TentsOfASmallSideProof
import Mathlib
set_option autoImplicit false
open Filter
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope.IndicesNearCell
private abbrev IntegerBox (M : ℕ) : Type := Fin 4 → Set.Icc (-(M : ℤ)) (M : ℤ)
private theorem norm_apply_le_torusEuclidNorm {S : ℝ} (x : TorusMetric.Torus4 S) (μ : Fin 4) :
    ‖x μ‖ ≤ TorusMetric.torusEuclidNorm x := by apply _root_.YangMills.SharedProofs.p28925 <;> assumption
private theorem exists_int_mul_eq_of_norm_le {S a : ℝ} (q : ℤ) (hS : S = (q : ℝ) * a) (ha : 0 < a) (m : ℤ)
    {R : ℝ} (h : ‖(((m : ℝ) * a : ℝ) : AddCircle S)‖ ≤ R) :
    ∃ m' : ℤ, (((m' : ℝ) * a : ℝ) : AddCircle S) = (((m : ℝ) * a : ℝ) : AddCircle S) ∧
      |(m' : ℝ)| * a ≤ R := by
  subst hS
  rw [AddCircle.norm_eq] at h
  set t : ℤ := round (((q : ℝ) * a)⁻¹ * ((m : ℝ) * a)) with ht
  refine ⟨m - t * q, ?_, ?_⟩
  · rw [← sub_eq_zero, ← AddCircle.coe_sub, AddCircle.coe_eq_zero_iff]
    refine ⟨-t, ?_⟩
    simp only [zsmul_eq_mul]
    push_cast
    ring
  · have e : |((m - t * q : ℤ) : ℝ)| * a = |(m : ℝ) * a - (t : ℝ) * ((q : ℝ) * a)| := by
      have : (m : ℝ) * a - (t : ℝ) * ((q : ℝ) * a) = ((m - t * q : ℤ) : ℝ) * a := by
        push_cast
        ring
      rw [this, abs_mul, abs_of_pos ha]
    rw [e]
    exact h
variable {L n k : ℕ}
private theorem meshSize_top (L k : ℕ) :
    PeriodicLattice.meshSize L (PeriodicLattice.levelDepth k k) = 1 := by
  simp [PeriodicLattice.meshSize, PeriodicLattice.levelDepth]
private theorem meshSize_finest (L k : ℕ) :
    PeriodicLattice.meshSize L (PeriodicLattice.levelDepth k 0) = ((L : ℝ) ^ k)⁻¹ := by
  simp [PeriodicLattice.meshSize, PeriodicLattice.levelDepth]
private theorem coe_toSublattice (hL : 0 < L) {d d' : ℤ} (h : d ≤ d') (x : PeriodicLattice.Site L n d) :
    ((x.toSublattice d' : PeriodicLattice.Site L n d') : PeriodicLattice.FourTorus L n) = x := by apply _root_.YangMills.SharedProofs.p9023 <;> assumption
private theorem exists_injective_site_code (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hC : NeighbouringFineVertexCells) (y : Tower.Vertex L n k k) (r : ℝ) (M : ℕ)
    (hM : (|r| + 1) * (L : ℝ) ^ k ≤ M) :
    ∃ f : {x : PeriodicLattice.Site L n (PeriodicLattice.levelDepth k 0) //
        cellDist y (fineVertexCell (L := L) (n := n) (k := k) x) ≤ r} → IntegerBox M,
      Function.Injective f := by
  have hL0 : 0 < L := by
    have := hL.2
    omega
  have hLk : (0 : ℝ) < (L : ℝ) ^ k := by positivity
  obtain ⟨a, ha⟩ : ∃ a, a = PeriodicLattice.meshSize L (PeriodicLattice.levelDepth k 0) := ⟨_, rfl⟩
  have haL : a = ((L : ℝ) ^ k)⁻¹ := ha.trans (meshSize_finest L k)
  have ha0 : 0 < a := by
    rw [haL]
    positivity
  have hY : (y : PeriodicLattice.FourTorus L n) ∈ PeriodicLattice.sublattice L n (PeriodicLattice.levelDepth k 0) :=
    PeriodicLattice.sublattice_mono hL0 n (by simp [PeriodicLattice.levelDepth]) y.2
  have hside : PeriodicLattice.torusSide L n = ((2 * (L : ℤ) ^ (n + k) : ℤ) : ℝ) * a := by
    rw [haL, PeriodicLattice.torusSide]
    push_cast
    rw [pow_add]
    field_simp
  have key : ∀ x : {x : PeriodicLattice.Site L n (PeriodicLattice.levelDepth k 0) //
      cellDist y (fineVertexCell (L := L) (n := n) (k := k) x) ≤ r}, ∃ w : IntegerBox M, ∀ μ,
      ((x.1 : PeriodicLattice.FourTorus L n) - (y : PeriodicLattice.FourTorus L n)) μ =
        ((((w μ : ℤ) : ℝ) * a : ℝ) : AddCircle (PeriodicLattice.torusSide L n)) := by
    rintro ⟨x, hx⟩
    obtain ⟨m, hm⟩ := (PeriodicLattice.sublattice L n (PeriodicLattice.levelDepth k 0)).sub_mem x.2 hY
    rw [← ha] at hm
    have near : ∀ μ, ‖((x : PeriodicLattice.FourTorus L n) - (y : PeriodicLattice.FourTorus L n)) μ‖ ≤ |r| + 1 := by
      intro μ
      obtain ⟨c, hc⟩ : ∃ c, c = fineVertexCell (L := L) (n := n) (k := k) x := ⟨_, rfl⟩
      rw [← hc] at hx
      have h₁ : ‖((x : PeriodicLattice.FourTorus L n) - (c : PeriodicLattice.FourTorus L n)) μ‖ ≤ 1 / 2 := by
        have h := ((hC L hL n k).2.2.1 x).1
        rw [← hc] at h
        change TorusMetric.torusSupNorm _ ≤ _ at h
        rw [SeparatedSequence.torusSupNorm_le_iff, meshSize_top] at h
        exact h μ
      have h₂ : ‖((y : PeriodicLattice.FourTorus L n) - (c : PeriodicLattice.FourTorus L n)) μ‖ ≤ r :=
        (norm_apply_le_torusEuclidNorm _ μ).trans hx
      have e : ((x : PeriodicLattice.FourTorus L n) - (y : PeriodicLattice.FourTorus L n)) μ =
          ((x : PeriodicLattice.FourTorus L n) - (c : PeriodicLattice.FourTorus L n)) μ -
            ((y : PeriodicLattice.FourTorus L n) - (c : PeriodicLattice.FourTorus L n)) μ := by
        simp
      rw [e]
      refine (norm_sub_le _ _).trans ?_
      linarith [le_abs_self r]
    have short : ∀ μ, ∃ m' : ℤ,
        ((x : PeriodicLattice.FourTorus L n) - (y : PeriodicLattice.FourTorus L n)) μ =
          (((m' : ℝ) * a : ℝ) : AddCircle (PeriodicLattice.torusSide L n)) ∧ |(m' : ℝ)| * a ≤ |r| + 1 := by
      intro μ
      obtain ⟨m', e₁, e₂⟩ := exists_int_mul_eq_of_norm_le _ hside ha0 (m μ) (R := |r| + 1)
        (by rw [← hm μ]; exact near μ)
      exact ⟨m', by rw [hm μ, e₁], e₂⟩
    choose m' hm₁ hm₂ using short
    have hi : ∀ μ, |m' μ| ≤ (M : ℤ) := by
      intro μ
      have h : |(m' μ : ℝ)| ≤ M := by
        calc |(m' μ : ℝ)| = (|(m' μ : ℝ)| * a) * (L : ℝ) ^ k := by
              rw [haL]
              field_simp
          _ ≤ (|r| + 1) * (L : ℝ) ^ k := mul_le_mul_of_nonneg_right (hm₂ μ) hLk.le
          _ ≤ M := hM
      exact_mod_cast h
    exact ⟨fun μ => ⟨m' μ, abs_le.mp (hi μ)⟩, hm₁⟩
  choose f hf using key
  refine ⟨f, fun x x' e => Subtype.ext (Subtype.ext ?_)⟩
  have : (x.1 : PeriodicLattice.FourTorus L n) - (y : PeriodicLattice.FourTorus L n) =
      (x'.1 : PeriodicLattice.FourTorus L n) - (y : PeriodicLattice.FourTorus L n) :=
    funext fun μ => by rw [hf x μ, hf x' μ, e]
  exact sub_left_injective this
private theorem exists_injective_bond_code (hL : Conventions.IsAdmissibleBlockingFactor L)
    (hC : NeighbouringFineVertexCells) (y : Tower.Vertex L n k k) (r : ℝ) (M : ℕ)
    (hM : (|r| + 1) * (L : ℝ) ^ k ≤ M) {d : ℤ} (hd : d ≤ PeriodicLattice.levelDepth k 0) :
    ∃ f : {b : PeriodicLattice.PositivelyOrientedBond L n d // cellDist y
        (fineVertexCell (L := L) (n := n) (k := k) (b.1.source.toSublattice (PeriodicLattice.levelDepth k 0))) ≤ r} →
        Fin 4 × IntegerBox M, Function.Injective f := by
  have hL0 : 0 < L := by
    have := hL.2
    omega
  obtain ⟨g, hg⟩ := exists_injective_site_code hL hC y r M hM
  have hdir : ∀ b : PeriodicLattice.PositivelyOrientedBond L n d, ∃ μ : Fin 4,
      b.1.target - b.1.source = PeriodicLattice.unitStep L n d μ := fun b => b.2
  choose dir hdir using hdir
  refine ⟨fun b => (dir b.1, g ⟨b.1.1.source.toSublattice _, b.2⟩), fun b b' e => ?_⟩
  obtain ⟨e₁, e₂⟩ := Prod.mk.inj e
  have e₃ := congrArg Subtype.val (hg e₂)
  have sources : b.1.1.source = b'.1.1.source := by
    refine Subtype.ext ?_
    rw [← coe_toSublattice hL0 hd b.1.1.source, ← coe_toSublattice hL0 hd b'.1.1.source]
    exact congrArg Subtype.val e₃
  have targets : b.1.1.target = b'.1.1.target := by
    have h₁ := hdir b.1
    have h₂ := hdir b'.1
    rw [e₁, ← h₂, sources] at h₁
    exact sub_left_injective h₁
  exact Subtype.ext (Subtype.ext (PeriodicLattice.Bond.ext sources targets))
theorem fewIndicesNearCell_of_neighbouringFineVertexCells (hC : NeighbouringFineVertexCells) :
    FewIndicesNearCell := by
  intro L hL k _ r
  obtain ⟨M, hM⟩ := exists_nat_ge ((|r| + 1) * (L : ℝ) ^ k)
  refine ⟨Nat.card (Fin 3 × Option (Fin k) × Fin 4 × IntegerBox M), Eventually.of_forall fun n y => ?_⟩
  have hd : ∀ j : ℕ, PeriodicLattice.levelDepth k j ≤ PeriodicLattice.levelDepth k 0 := fun j => by
    simp [PeriodicLattice.levelDepth]
  choose f hf using fun j : ℕ => exists_injective_bond_code (n := n) (k := k) hL hC y r M hM (hd j)
  constructor
  · let g : {q : LevelFormIndex L n k // cellDist y (levelFormIndexCell q) ≤ r} →
        Fin 3 × Option (Fin k) × Fin 4 × IntegerBox M := fun q =>
      match q with
      | ⟨.inl p, h⟩ => (p.1, none, f 0 ⟨p.2, h⟩)
      | ⟨.inr ⟨i, p⟩, h⟩ => (p.1, some i, f (i + 1) ⟨p.2, h⟩)
    refine Nat.card_le_card_of_injective g ?_
    rintro ⟨⟨c, b⟩ | ⟨i, c, b⟩, h⟩ ⟨⟨c', b'⟩ | ⟨i', c', b'⟩, h'⟩ e
    · obtain ⟨e₁, e₂⟩ := Prod.mk.inj e
      obtain ⟨-, e₃⟩ := Prod.mk.inj e₂
      have e₄ := congrArg Subtype.val (hf 0 e₃)
      subst e₁
      cases (show b = b' from e₄)
      rfl
    · simp [g] at e
    · simp [g] at e
    · obtain ⟨e₁, e₂⟩ := Prod.mk.inj e
      obtain ⟨e₃, e₄⟩ := Prod.mk.inj e₂
      obtain rfl : i = i' := Option.some.inj e₃
      have e₅ := congrArg Subtype.val (hf (i + 1) e₄)
      subst e₁
      cases (show b = b' from e₅)
      rfl
  · refine Nat.card_le_card_of_injective (β := Fin 3 × Option (Fin k) × Fin 4 × IntegerBox M)
      (fun p => (p.1.1, none, f k ⟨p.1.2, p.2⟩)) ?_
    rintro ⟨⟨c, b⟩, h⟩ ⟨⟨c', b'⟩, h'⟩ e
    obtain ⟨e₁, e₂⟩ := Prod.mk.inj e
    obtain ⟨-, e₃⟩ := Prod.mk.inj e₂
    have e₄ := congrArg Subtype.val (hf k e₃)
    subst e₁
    cases (show b = b' from e₄)
    rfl
end YangMills.Construction.RunningCouplingSlope.IndicesNearCell
end
