import YangMills.Construction.InfiniteLattice.ReconstructionAtALatticeMirrorProof
import YangMills.Construction.InfiniteLattice.CoveringOfTheTorusLatticeAtOneSpacingProof
import YangMills.Construction.OneLoopLaw.PlaneWavesUnderMotionsOfTheLattice
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.OneLoopLaw.PlaneWaveSymmetries
open Tower PeriodicOperators PeriodicOperators.Tempered UnitLatticeMotions Matrices
open InfiniteLattice (AmbientSpace)
open TorusMetric (torusProj)
open PeriodicLattice (FourTorus torusSide pointOnAxis sublattice levelDepth meshSize unitStep)
variable {L n : ℕ}
abbrev basisShift (L n : ℕ) (μ : Fin 4) : FourTorus L n := pointOnAxis L n μ 1
theorem addCircle_coe_ne_zero_of_le_two {S t : ℝ} (hS : 2 < S) (h0 : 0 < t) (h1 : t ≤ 2) :
    (t : AddCircle S) ≠ 0 := by
  intro h
  obtain ⟨k, hk⟩ := (AddCircle.coe_eq_zero_iff S).1 h
  rw [zsmul_eq_mul] at hk
  rcases le_or_gt k 0 with hk0 | hk0
  · have : (k : ℝ) ≤ 0 := by exact_mod_cast hk0
    nlinarith
  · have : (1 : ℝ) ≤ k := by exact_mod_cast hk0
    nlinarith
theorem two_lt_torusSide (hL : Conventions.IsAdmissibleBlockingFactor L) (hn : 0 < n) :
    2 < torusSide L n := by
  have h1 : (13 : ℝ) ≤ L := by exact_mod_cast hL.2
  have h2 : (L : ℝ) ≤ (L : ℝ) ^ n := le_self_pow₀ (by linarith) hn.ne'
  unfold torusSide
  linarith
theorem basisShift_apply_self (μ : Fin 4) :
    basisShift L n μ μ = ((1 : ℝ) : AddCircle (torusSide L n)) := by
  simp [pointOnAxis]
theorem basisShift_apply_of_ne {μ ν : Fin 4} (h : ν ≠ μ) : basisShift L n μ ν = 0 := by
  simp [pointOnAxis, Pi.single_eq_of_ne h]
theorem basisShift_add_basisShift_ne_zero (hS : 2 < torusSide L n) (μ ν : Fin 4) :
    basisShift L n μ + basisShift L n ν ≠ 0 := by
  intro h
  have h1 := congrFun h μ
  rw [Pi.add_apply, basisShift_apply_self] at h1
  by_cases hμν : ν = μ
  · subst hμν
    rw [basisShift_apply_self, ← AddCircle.coe_add] at h1
    exact addCircle_coe_ne_zero_of_le_two hS (by norm_num) (by norm_num) h1
  · rw [basisShift_apply_of_ne (Ne.symm hμν), add_zero] at h1
    exact addCircle_coe_ne_zero_of_le_two hS (by norm_num) (by norm_num) h1
theorem basisShift_inj (hS : 2 < torusSide L n) {μ ν : Fin 4} :
    basisShift L n ν = basisShift L n μ ↔ ν = μ := by
  constructor
  · intro h
    by_contra hne
    have h1 := congrFun h ν
    rw [basisShift_apply_self, basisShift_apply_of_ne hne] at h1
    exact addCircle_coe_ne_zero_of_le_two hS (by norm_num) (by norm_num) h1
  · rintro rfl
    rfl
theorem neg_basisShift_ne (hS : 2 < torusSide L n) (μ ν : Fin 4) :
    -basisShift L n ν ≠ basisShift L n μ := by
  intro h
  apply basisShift_add_basisShift_ne_zero hS ν μ
  rw [← h]
  simp
theorem coe_unitStep_levelDepth (μ : Fin 4) :
    ((unitStep L n (levelDepth 0 0) μ : PeriodicLattice.Site L n _) : FourTorus L n) =
      basisShift L n μ := by
  show pointOnAxis L n μ (meshSize L _) = _
  congr 1
theorem sub_eq_unitStep_iff (x y : Vertex L n 0 0) (μ : Fin 4) :
    x - y = unitStep L n (levelDepth 0 0) μ ↔
      (x : FourTorus L n) - y = basisShift L n μ := by
  rw [Subtype.ext_iff, AddSubgroup.coe_sub, coe_unitStep_levelDepth]
theorem isPositivelyOriented_iff (c : UnitEdge L n) :
    c.IsPositivelyOriented ↔ ∃ ν, (c.target : FourTorus L n) - c.source = basisShift L n ν :=
  exists_congr fun ν => sub_eq_unitStep_iff _ _ ν
theorem isPositivelyOriented_or_opposite (c : UnitEdge L n) :
    c.IsPositivelyOriented ∨ c.opposite.IsPositivelyOriented := by
  obtain ⟨μ, h | h⟩ := c.isNeighbour
  · exact Or.inl ⟨μ, h⟩
  · refine Or.inr ⟨μ, ?_⟩
    show c.source - c.target = _
    rw [← neg_sub, h, neg_neg]
theorem not_opposite_isPositivelyOriented (hS : 2 < torusSide L n) (c : UnitEdge L n)
    (h : c.IsPositivelyOriented) : ¬ c.opposite.IsPositivelyOriented := by
  intro h'
  obtain ⟨μ, hμ⟩ := (isPositivelyOriented_iff c).1 h
  obtain ⟨ν, hν⟩ := (isPositivelyOriented_iff c.opposite).1 h'
  have hν' : (c.source : FourTorus L n) - c.target = basisShift L n ν := hν
  apply basisShift_add_basisShift_ne_zero hS μ ν
  rw [← hμ, ← hν']
  abel
theorem extendOddly_eq (F B' : UnitEdge L n → ComplexMatrix2)
    (hB' : ∀ c : UnitEdge L n, B' c.opposite = -B' c)
    (h : ∀ b : UnitEdge L n, b.IsPositivelyOriented → F b = B' b) :
    extendOddly (k := 0) (j := 0) F = B' := by
  funext b
  unfold extendOddly
  by_cases hb : b.IsPositivelyOriented
  · rw [if_pos hb]
    exact h b hb
  · rw [if_neg hb, h _ ((isPositivelyOriented_or_opposite b).resolve_left hb), hB', neg_neg]
def euclidDot (a b : AmbientSpace) : ℝ := ∑ μ, a μ * b μ
theorem bilinDot_toComplexVec (a b : AmbientSpace) :
    bilinDot (toComplexVec a) (toComplexVec b) = ((euclidDot a b : ℝ) : ℂ) := by
  simp [bilinDot, toComplexVec, euclidDot]
def expPhase (p y : AmbientSpace) : ℂ := Complex.exp (Complex.I * ((euclidDot p y : ℝ) : ℂ))
theorem euclidDot_add (p y y' : AmbientSpace) :
    euclidDot p (y + y') = euclidDot p y + euclidDot p y' := by apply _root_.YangMills.Construction.LatticeConventions.MirrorReconstructionProof.euclidDot_add <;> assumption
theorem expPhase_add (p y y' : AmbientSpace) :
    expPhase p (y + y') = expPhase p y * expPhase p y' := by
  unfold expPhase
  rw [← Complex.exp_add, euclidDot_add]
  congr 1
  push_cast
  ring
theorem torusProj_surjective (x : FourTorus L n) :
    ∃ y : AmbientSpace, torusProj (torusSide L n) y = x := by
  have h := fun μ => QuotientAddGroup.mk_surjective (x μ)
  choose y hy using h
  exact ⟨y, funext hy⟩
theorem torusProj_add_eq (y y' : AmbientSpace) :
    torusProj (torusSide L n) (y + y') =
      torusProj (torusSide L n) y + torusProj (torusSide L n) y' := by apply _root_.YangMills.Construction.InfiniteLattice.TorusCovering.torusProj_add <;> assumption
theorem natCast_two_mul_pow_eq_torusSide : (((2 * L ^ n : ℕ)) : ℝ) = torusSide L n := by
  simp [torusSide]
theorem mem_dualLattice_iff {p : AmbientSpace} :
    p ∈ dualLattice (2 * L ^ n) ↔
      ∃ m : Fin 4 → ℤ, ∀ μ, p μ = (m μ : ℝ) * (2 * Real.pi / torusSide L n) := by
  rw [← natCast_two_mul_pow_eq_torusSide]
  rfl
theorem expPhase_eq_of_torusProj_eq (hS : 2 < torusSide L n) {p y y' : AmbientSpace}
    (hp : p ∈ dualLattice (2 * L ^ n))
    (h : torusProj (torusSide L n) y' = torusProj (torusSide L n) y) :
    expPhase p y' = expPhase p y := by
  obtain ⟨m, hm⟩ := mem_dualLattice_iff.1 hp
  have hk : ∀ μ, ∃ k : ℤ, y' μ - y μ = (k : ℝ) * torusSide L n := by
    intro μ
    have h1 : (y' μ : AddCircle (torusSide L n)) = y μ := congrFun h μ
    have h0 : ((y' μ - y μ : ℝ) : AddCircle (torusSide L n)) = 0 := by
      rw [AddCircle.coe_sub, h1, sub_self]
    obtain ⟨k, hk⟩ := (AddCircle.coe_eq_zero_iff _).1 h0
    exact ⟨k, by rw [← hk, zsmul_eq_mul]⟩
  choose k hk using hk
  have hS0 : torusSide L n ≠ 0 := by linarith
  have hterm : ∀ μ, p μ * y' μ =
      p μ * y μ + ((m μ : ℝ) * (k μ : ℝ)) * (2 * Real.pi) := by
    intro μ
    have h1 : y' μ = y μ + (k μ : ℝ) * torusSide L n := by linarith [hk μ]
    rw [h1, hm μ]
    field_simp
  have hr : euclidDot p y' = euclidDot p y + ((∑ μ, m μ * k μ : ℤ) : ℝ) * (2 * Real.pi) := by
    unfold euclidDot
    simp_rw [hterm]
    rw [Finset.sum_add_distrib, ← Finset.sum_mul]
    push_cast
    rfl
  unfold expPhase
  rw [Complex.exp_eq_exp_iff_exists_int]
  refine ⟨∑ μ, m μ * k μ, ?_⟩
  rw [hr]
  push_cast
  ring
theorem phase_torusProj_eq_expPhase (hS : 2 < torusSide L n) {p : AmbientSpace}
    (hp : p ∈ dualLattice (2 * L ^ n)) (y : AmbientSpace) :
    phase (L := L) (n := n) p (torusProj (torusSide L n) y) = expPhase p y := by
  unfold phase
  have hex : ∃ z : ℂ, ∀ y' : AmbientSpace,
      (fun μ => (y' μ : AddCircle (torusSide L n))) = torusProj (torusSide L n) y →
        Complex.exp (Complex.I * bilinDot (toComplexVec p) (toComplexVec y')) = z := by
    refine ⟨expPhase p y, fun y' h => ?_⟩
    rw [bilinDot_toComplexVec]
    exact expPhase_eq_of_torusProj_eq hS hp h
  have h := Classical.epsilon_spec hex y rfl
  rw [← h, bilinDot_toComplexVec]
  rfl
theorem phase_add_torusProj_eq (hS : 2 < torusSide L n) {p : AmbientSpace}
    (hp : p ∈ dualLattice (2 * L ^ n)) (x : FourTorus L n) (v : AmbientSpace) :
    phase p (x + torusProj (torusSide L n) v) = phase p x * expPhase p v := by
  obtain ⟨y, rfl⟩ := torusProj_surjective x
  rw [← torusProj_add_eq, phase_torusProj_eq_expPhase hS hp, phase_torusProj_eq_expPhase hS hp,
    expPhase_add]
theorem basisShift_eq_torusProj (μ : Fin 4) :
    basisShift L n μ = torusProj (torusSide L n) (Pi.single μ 1) := by
  funext ν
  by_cases h : ν = μ
  · subst h
    simp [pointOnAxis, torusProj]
  · simp [pointOnAxis, torusProj, Pi.single_eq_of_ne h]
theorem phase_add_basisShift (hS : 2 < torusSide L n) {p : AmbientSpace}
    (hp : p ∈ dualLattice (2 * L ^ n)) (x : FourTorus L n) (μ : Fin 4) :
    phase p (x + basisShift L n μ) = phase p x * Complex.exp (Complex.I * (p μ : ℂ)) := by
  rw [basisShift_eq_torusProj, phase_add_torusProj_eq hS hp]
  simp [expPhase, euclidDot, Pi.single_apply]
theorem phase_sub_basisShift (hS : 2 < torusSide L n) {p : AmbientSpace}
    (hp : p ∈ dualLattice (2 * L ^ n)) (x : FourTorus L n) (μ : Fin 4) :
    phase p (x - basisShift L n μ) = phase p x * Complex.exp (-(Complex.I * (p μ : ℂ))) := by
  have h := phase_add_basisShift hS hp (x - basisShift L n μ) μ
  rw [sub_add_cancel] at h
  rw [h, mul_assoc, ← Complex.exp_add]
  simp
theorem pauliFamily_mem_traceless (a : Fin 3) :
    ComplexMatrix2.pauliFamily a ∈ ComplexMatrix2.traceless := by
  obtain ⟨h0, h1, h2⟩ := ComplexMatrix2.pauliFamily_apply
  show Matrix.trace (ComplexMatrix2.pauliFamily a) = 0
  fin_cases a
  · show Matrix.trace (ComplexMatrix2.pauliFamily 0) = 0
    rw [h0, Matrix.trace_fin_two]
    simp
  · show Matrix.trace (ComplexMatrix2.pauliFamily 1) = 0
    rw [h1, Matrix.trace_fin_two]
    simp
  · show Matrix.trace (ComplexMatrix2.pauliFamily 2) = 0
    rw [h2, Matrix.trace_fin_two]
    simp
open Classical in
def edgeMode (a : Fin 3) (p : AmbientSpace) (μ : Fin 4) (t h : FourTorus L n) : ComplexMatrix2 :=
  if h - t = basisShift L n μ then phase p t • ComplexMatrix2.pauliFamily a
  else if t - h = basisShift L n μ then -(phase p h • ComplexMatrix2.pauliFamily a)
  else 0
theorem fourierModeForm_apply (hS : 2 < torusSide L n) (a : Fin 3) (p : AmbientSpace)
    (μ : Fin 4) (c : UnitEdge L n) :
    fourierModeForm L n a p μ c = edgeMode a p μ (c.source : FourTorus L n) c.target := by
  unfold fourierModeForm extendOddly edgeMode
  beta_reduce
  by_cases h1 : (c.target : FourTorus L n) - c.source = basisShift L n μ
  · have hp : c.IsPositivelyOriented := (isPositivelyOriented_iff c).2 ⟨μ, h1⟩
    rw [if_pos hp, if_pos ((sub_eq_unitStep_iff _ _ _).2 h1), if_pos h1]
  · rw [if_neg h1]
    by_cases h2 : (c.source : FourTorus L n) - c.target = basisShift L n μ
    · have hp : c.opposite.IsPositivelyOriented := (isPositivelyOriented_iff _).2 ⟨μ, h2⟩
      have hn : ¬ c.IsPositivelyOriented := fun h => not_opposite_isPositivelyOriented hS c h hp
      have h3 : c.opposite.target - c.opposite.source = unitStep L n (levelDepth 0 0) μ :=
        (sub_eq_unitStep_iff _ _ _).2 h2
      rw [if_neg hn, if_pos h2, if_pos h3]
      rfl
    · rw [if_neg h2]
      have h3 : ¬ (c.target - c.source = unitStep L n (levelDepth 0 0) μ) :=
        fun h => h1 ((sub_eq_unitStep_iff _ _ _).1 h)
      have h4 : ¬ (c.opposite.target - c.opposite.source = unitStep L n (levelDepth 0 0) μ) :=
        fun h => h2 ((sub_eq_unitStep_iff _ _ _).1 h)
      by_cases hp : c.IsPositivelyOriented
      · rw [if_pos hp, if_neg h3]
      · rw [if_neg hp, if_neg h4, neg_zero]
theorem edgeMode_swap (hS : 2 < torusSide L n) (a : Fin 3) (p : AmbientSpace) (μ : Fin 4)
    (t h : FourTorus L n) : edgeMode a p μ h t = -edgeMode a p μ t h := by
  unfold edgeMode
  by_cases h1 : h - t = basisShift L n μ
  · have h2 : ¬ (t - h = basisShift L n μ) := by
      intro h2
      apply neg_basisShift_ne hS μ μ
      calc -basisShift L n μ = -(h - t) := by rw [h1]
        _ = t - h := by abel
        _ = basisShift L n μ := h2
    rw [if_pos h1, if_neg h2, if_pos h1]
  · by_cases h2 : t - h = basisShift L n μ
    · rw [if_pos h2, if_neg h1, if_pos h2, neg_neg]
    · rw [if_neg h1, if_neg h2, if_neg h1, if_neg h2, neg_zero]
theorem fourierModeForm_opposite (hS : 2 < torusSide L n) (a : Fin 3) (p : AmbientSpace)
    (μ : Fin 4) (c : UnitEdge L n) :
    fourierModeForm L n a p μ c.opposite = -fourierModeForm L n a p μ c := by
  rw [fourierModeForm_apply hS, fourierModeForm_apply hS]
  exact edgeMode_swap hS a p μ _ _
theorem edgeMode_add_basisShift (hS : 2 < torusSide L n) (a : Fin 3) (p : AmbientSpace)
    (μ ν : Fin 4) (t : FourTorus L n) :
    edgeMode a p μ t (t + basisShift L n ν) =
      if ν = μ then phase p t • ComplexMatrix2.pauliFamily a else 0 := by
  unfold edgeMode
  by_cases h : ν = μ
  · subst h
    simp
  · have h1 : ¬ (t + basisShift L n ν - t = basisShift L n μ) := by
      rw [add_sub_cancel_left]
      exact (basisShift_inj hS).not.2 h
    have h2 : ¬ (t - (t + basisShift L n ν) = basisShift L n μ) := by
      rw [sub_add_cancel_left]
      exact neg_basisShift_ne hS μ ν
    rw [if_neg h1, if_neg h2, if_neg h]
theorem edgeMode_sub_basisShift (hS : 2 < torusSide L n) (a : Fin 3) (p : AmbientSpace)
    (μ ν : Fin 4) (t : FourTorus L n) :
    edgeMode a p μ t (t - basisShift L n ν) =
      if ν = μ then -(phase p (t - basisShift L n ν) • ComplexMatrix2.pauliFamily a) else 0 := by
  have h := edgeMode_swap hS a p μ (t - basisShift L n ν) t
  have h' := edgeMode_add_basisShift hS a p μ ν (t - basisShift L n ν)
  rw [sub_add_cancel] at h'
  rw [h, h']
  split_ifs <;> simp
theorem edgePreimage_coe (f g : FourTorus L n → FourTorus L n)
    (hfg : ∀ x, f (g x) = x) (hgf : ∀ x, g (f x) = x)
    (hlat : ∀ x : Vertex L n 0 0, g x ∈ sublattice L n (levelDepth 0 0))
    (hstep : ∀ (t : FourTorus L n) (ν : Fin 4), ∃ ν' : Fin 4,
      g (t + basisShift L n ν) - g t = basisShift L n ν' ∨
        g (t + basisShift L n ν) - g t = -basisShift L n ν')
    (b : UnitEdge L n) :
    ((edgePreimage (k := 0) (j := 0) f b).source : FourTorus L n) = g b.source ∧
      ((edgePreimage (k := 0) (j := 0) f b).target : FourTorus L n) = g b.target := by
  have hsite : ∀ x : Vertex L n 0 0,
      (vertexPreimage (k := 0) (j := 0) f x : FourTorus L n) = g x := by
    intro x
    have hex : ∃ x' : Vertex L n 0 0, f x' = x := ⟨⟨g x, hlat x⟩, hfg x⟩
    have h : f (vertexPreimage (k := 0) (j := 0) f x) = x := Classical.epsilon_spec hex
    rw [← h, hgf]
  have hadj : ∃ μ : Fin 4, (⟨g b.target, hlat _⟩ : Vertex L n 0 0) - ⟨g b.source, hlat _⟩ =
        unitStep L n (levelDepth 0 0) μ ∨
      (⟨g b.target, hlat _⟩ : Vertex L n 0 0) - ⟨g b.source, hlat _⟩ =
        -unitStep L n (levelDepth 0 0) μ := by
    have key : ∃ μ : Fin 4, g b.target - g b.source = basisShift L n μ ∨
        g b.target - g b.source = -basisShift L n μ := by
      obtain ⟨ν, hν | hν⟩ := b.isNeighbour
      · have h1 := (sub_eq_unitStep_iff _ _ _).1 hν
        have h2 : (b.target : FourTorus L n) = b.source + basisShift L n ν :=
          eq_add_of_sub_eq' h1
        rw [h2]
        exact hstep _ ν
      · have h1 : b.source - b.target = unitStep L n (levelDepth 0 0) ν := by
          rw [← neg_sub, hν, neg_neg]
        have h2 := (sub_eq_unitStep_iff _ _ _).1 h1
        have h3 : (b.source : FourTorus L n) = b.target + basisShift L n ν :=
          eq_add_of_sub_eq' h2
        obtain ⟨ν', h4⟩ := hstep (b.target : FourTorus L n) ν
        rw [← h3] at h4
        refine ⟨ν', ?_⟩
        rcases h4 with h4 | h4
        · right
          rw [← h4]
          abel
        · left
          rw [← neg_eq_iff_eq_neg.mpr h4]
          abel
    obtain ⟨μ, h | h⟩ := key
    · exact ⟨μ, Or.inl (by rw [Subtype.ext_iff, AddSubgroup.coe_sub, coe_unitStep_levelDepth]; exact h)⟩
    · exact ⟨μ, Or.inr (by
        rw [Subtype.ext_iff, AddSubgroup.coe_sub, AddSubgroup.coe_neg, coe_unitStep_levelDepth]
        exact h)⟩
  have hex : ∃ c : UnitEdge L n, c.source = vertexPreimage (k := 0) (j := 0) f b.source ∧
      c.target = vertexPreimage (k := 0) (j := 0) f b.target := by
    have ht : vertexPreimage (k := 0) (j := 0) f b.source = ⟨g b.source, hlat _⟩ :=
      Subtype.ext (hsite _)
    have hh : vertexPreimage (k := 0) (j := 0) f b.target = ⟨g b.target, hlat _⟩ :=
      Subtype.ext (hsite _)
    exact ⟨⟨_, _, hadj⟩, ht.symm, hh.symm⟩
  have h := Classical.epsilon_spec hex
  have h' : (edgePreimage (k := 0) (j := 0) f b).source =
        vertexPreimage (k := 0) (j := 0) f b.source ∧
      (edgePreimage (k := 0) (j := 0) f b).target =
        vertexPreimage (k := 0) (j := 0) f b.target := h
  rw [h'.1, h'.2]
  exact ⟨hsite _, hsite _⟩
theorem tangentEdgeValue_identityField (B : UnitEdge L n → ComplexMatrix2)
    (hB : ∀ c : UnitEdge L n, B c.opposite = -B c) (c : UnitEdge L n) :
    tangentEdgeValue (identityField L n) B c = B c := by
  unfold tangentEdgeValue
  by_cases h : c.IsPositivelyOriented
  · rw [if_pos h]
  · rw [if_neg h]
    have h1 : c.opposite.opposite = c := rfl
    have h2 := hB c.opposite
    rw [h1] at h2
    simp [identityField, ComplexMatrix2.conjugateBy, h2]
theorem tangentPushforward_eq (f g : FourTorus L n → FourTorus L n)
    (hfg : ∀ x, f (g x) = x) (hgf : ∀ x, g (f x) = x)
    (hlat : ∀ x : Vertex L n 0 0, g x ∈ sublattice L n (levelDepth 0 0))
    (hstep : ∀ (t : FourTorus L n) (ν : Fin 4), ∃ ν' : Fin 4,
      g (t + basisShift L n ν) - g t = basisShift L n ν' ∨
        g (t + basisShift L n ν) - g t = -basisShift L n ν')
    (B B' : UnitEdge L n → ComplexMatrix2) (hB : ∀ c : UnitEdge L n, B c.opposite = -B c)
    (hB' : ∀ c : UnitEdge L n, B' c.opposite = -B' c)
    (h : ∀ (b c : UnitEdge L n), b.IsPositivelyOriented →
      (c.source : FourTorus L n) = g b.source →
      (c.target : FourTorus L n) = g b.target → B c = B' b) :
    tangentPushforward f B = B' := by
  unfold tangentPushforward isometryOnTangent
  refine extendOddly_eq _ _ hB' fun b hb => ?_
  rw [tangentEdgeValue_identityField B hB]
  obtain ⟨h1, h2⟩ := edgePreimage_coe f g hfg hgf hlat hstep b
  exact h b _ hb h1 h2
theorem mem_sublattice_levelDepth_iff (x : FourTorus L n) :
    x ∈ sublattice L n (levelDepth 0 0) ↔
      ∃ z : Fin 4 → ℤ, x = torusProj (torusSide L n) (castVec z) := by
  have hsp : meshSize L (levelDepth 0 0) = 1 := by
    simp [meshSize]
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨z, funext fun μ => ?_⟩
    rw [hz μ, hsp, mul_one]
    rfl
  · rintro ⟨z, rfl⟩
    refine ⟨z, fun μ => ?_⟩
    rw [hsp, mul_one]
    rfl
theorem add_two_pi_smul_mem_dualLattice (hS : 2 < torusSide L n) {p : AmbientSpace}
    (hp : p ∈ dualLattice (2 * L ^ n)) (e : Fin 4 → ℤ) :
    p + (2 * Real.pi) • castVec e ∈ dualLattice (2 * L ^ n) := by
  obtain ⟨m, hm⟩ := mem_dualLattice_iff.1 hp
  refine mem_dualLattice_iff.2 ⟨fun μ => m μ + e μ * (2 * (L : ℤ) ^ n), fun μ => ?_⟩
  have hS0 : torusSide L n ≠ 0 := by linarith
  have hs : torusSide L n = 2 * (L : ℝ) ^ n := rfl
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, castVec, hm μ]
  push_cast
  rw [← hs]
  field_simp
theorem phase_add_two_pi_smul (hS : 2 < torusSide L n) {p : AmbientSpace}
    (hp : p ∈ dualLattice (2 * L ^ n)) (e : Fin 4 → ℤ) (x : FourTorus L n)
    (hx : x ∈ sublattice L n (levelDepth 0 0)) :
    phase (p + (2 * Real.pi) • castVec e) x = phase p x := by
  obtain ⟨z, rfl⟩ := (mem_sublattice_levelDepth_iff x).1 hx
  rw [phase_torusProj_eq_expPhase hS (add_two_pi_smul_mem_dualLattice hS hp e),
    phase_torusProj_eq_expPhase hS hp]
  have hr : euclidDot (p + (2 * Real.pi) • castVec e) (castVec z) =
      euclidDot p (castVec z) + ((∑ μ, e μ * z μ : ℤ) : ℝ) * (2 * Real.pi) := by
    unfold euclidDot
    push_cast
    rw [Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun μ _ => ?_
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, castVec]
    ring
  unfold expPhase
  rw [Complex.exp_eq_exp_iff_exists_int]
  refine ⟨∑ μ, e μ * z μ, ?_⟩
  rw [hr]
  push_cast
  ring
theorem comp_symm_mem_dualLattice {p : AmbientSpace} (hp : p ∈ dualLattice (2 * L ^ n))
    (σ : Equiv.Perm (Fin 4)) : p ∘ σ.symm ∈ dualLattice (2 * L ^ n) := by
  obtain ⟨m, hm⟩ := mem_dualLattice_iff.1 hp
  exact mem_dualLattice_iff.2 ⟨m ∘ σ.symm, fun μ => hm (σ.symm μ)⟩
theorem flipCoord_mem_dualLattice {p : AmbientSpace} (hp : p ∈ dualLattice (2 * L ^ n))
    (ρ : Fin 4) : flipCoord ρ p ∈ dualLattice (2 * L ^ n) := by
  obtain ⟨m, hm⟩ := mem_dualLattice_iff.1 hp
  refine mem_dualLattice_iff.2 ⟨Function.update m ρ (-m ρ), fun μ => ?_⟩
  by_cases h : μ = ρ
  · subst h
    simp [flipCoord, hm μ]
  · simp [flipCoord, Function.update_of_ne h, hm μ]
theorem tangentPushforward_translation (hS : 2 < torusSide L n)
    (f : FourTorus L n → FourTorus L n) (m : Fin 4 → ℤ)
    (hind : IsInducedByMotion f 1 m) (a : Fin 3) (μ : Fin 4) (p : AmbientSpace)
    (hp : p ∈ dualLattice (2 * L ^ n)) :
    tangentPushforward f (fourierModeForm L n a p μ) =
      Complex.exp (-(Complex.I * bilinDot (toComplexVec p) (toComplexVec (castVec m)))) •
        fourierModeForm L n a p μ := by
  set v : FourTorus L n := torusProj (torusSide L n) (castVec m) with hv
  have hf : ∀ x, f x = x + v := by
    intro x
    obtain ⟨y, rfl⟩ := torusProj_surjective x
    rw [hind y, Matrix.one_mulVec, torusProj_add_eq]
  refine tangentPushforward_eq f (fun x => x - v) (fun x => by simp [hf]) (fun x => by simp [hf])
    (fun x => AddSubgroup.sub_mem _ x.2 ((mem_sublattice_levelDepth_iff v).2 ⟨m, rfl⟩))
    (fun t ν => ⟨ν, Or.inl (by abel)⟩) _ _ (fourierModeForm_opposite hS a p μ)
    (fun c => by simp [fourierModeForm_opposite hS]) ?_
  intro b c hb ht hh
  obtain ⟨ν, hν⟩ := (isPositivelyOriented_iff b).1 hb
  have hhead : (b.target : FourTorus L n) = b.source + basisShift L n ν := eq_add_of_sub_eq' hν
  have hsh : (b.source : FourTorus L n) + basisShift L n ν - v =
      ((b.source : FourTorus L n) - v) + basisShift L n ν := by abel
  have hph : phase p ((b.source : FourTorus L n) - v) =
      Complex.exp (-(Complex.I * bilinDot (toComplexVec p) (toComplexVec (castVec m)))) *
        phase p (b.source : FourTorus L n) := by
    have h1 : (b.source : FourTorus L n) =
        ((b.source : FourTorus L n) - v) + torusProj (torusSide L n) (castVec m) := by
      rw [← hv]
      abel
    have h2 := phase_add_torusProj_eq hS hp ((b.source : FourTorus L n) - v) (castVec m)
    rw [← h1] at h2
    rw [h2, bilinDot_toComplexVec, mul_comm _ (expPhase _ _), ← mul_assoc]
    unfold expPhase
    rw [← Complex.exp_add]
    simp
  rw [Pi.smul_apply, fourierModeForm_apply hS, fourierModeForm_apply hS, ht, hh, hhead, hsh,
    edgeMode_add_basisShift hS, edgeMode_add_basisShift hS]
  by_cases h : ν = μ
  · rw [if_pos h, if_pos h, hph, smul_smul]
  · rw [if_neg h, if_neg h, smul_zero]
theorem permMatrix_mulVec_eq_comp (σ : Equiv.Perm (Fin 4)) (y : AmbientSpace) :
    (permMatrix σ).mulVec y = y ∘ σ.symm := by
  funext ν
  simp only [Matrix.mulVec, dotProduct, permMatrix, Matrix.of_apply, Function.comp]
  rw [Finset.sum_eq_single (σ.symm ν)]
  · simp
  · intro μ _ h
    have : ν ≠ σ μ := by
      rintro rfl
      exact h (by simp)
    simp [this]
  · simp
theorem basisShift_comp (σ : Equiv.Perm (Fin 4)) (ν : Fin 4) :
    basisShift L n ν ∘ σ = basisShift L n (σ.symm ν) := by
  funext κ
  by_cases h : κ = σ.symm ν
  · subst h
    simp only [Function.comp, Equiv.apply_symm_apply]
    rw [basisShift_apply_self, basisShift_apply_self]
  · have h' : σ κ ≠ ν := fun e => h (by rw [← e]; simp)
    simp only [Function.comp]
    rw [basisShift_apply_of_ne h', basisShift_apply_of_ne h]
theorem phase_comp_perm (hS : 2 < torusSide L n) {p : AmbientSpace}
    (hp : p ∈ dualLattice (2 * L ^ n)) (σ : Equiv.Perm (Fin 4)) (x : FourTorus L n) :
    phase p (x ∘ σ) = phase (p ∘ σ.symm) x := by
  obtain ⟨y, rfl⟩ := torusProj_surjective x
  have h : (torusProj (torusSide L n) y) ∘ σ = torusProj (torusSide L n) (y ∘ σ) := rfl
  rw [h, phase_torusProj_eq_expPhase hS hp,
    phase_torusProj_eq_expPhase hS (comp_symm_mem_dualLattice hp σ)]
  have hr : euclidDot p (y ∘ σ) = euclidDot (p ∘ σ.symm) y := by
    unfold euclidDot
    rw [← Equiv.sum_comp σ (fun μ => (p ∘ σ.symm) μ * y μ)]
    simp
  unfold expPhase
  rw [hr]
theorem tangentPushforward_permutation (hS : 2 < torusSide L n)
    (f : FourTorus L n → FourTorus L n) (σ : Equiv.Perm (Fin 4))
    (hind : IsInducedByMotion f (permMatrix σ) 0) (a : Fin 3) (μ : Fin 4) (p : AmbientSpace)
    (hp : p ∈ dualLattice (2 * L ^ n)) :
    tangentPushforward f (fourierModeForm L n a p μ) =
      fourierModeForm L n a (p ∘ σ.symm) (σ μ) := by
  have hf : ∀ x, f x = x ∘ σ.symm := by
    intro x
    obtain ⟨y, rfl⟩ := torusProj_surjective x
    rw [hind y, permMatrix_mulVec_eq_comp]
    have h0 : castVec (0 : Fin 4 → ℤ) = 0 := by
      funext μ
      simp [castVec]
    rw [h0, add_zero]
    rfl
  have hadd : ∀ (t : FourTorus L n) (ν : Fin 4),
      (t + basisShift L n ν) ∘ σ = t ∘ σ + basisShift L n (σ.symm ν) := by
    intro t ν
    rw [← basisShift_comp]
    rfl
  refine tangentPushforward_eq f (fun x => x ∘ σ) (fun x => ?_) (fun x => ?_) (fun x => ?_)
    (fun t ν => ⟨σ.symm ν, Or.inl ?_⟩) _ _ (fourierModeForm_opposite hS a p μ)
    (fourierModeForm_opposite hS a _ _) ?_
  · rw [hf]
    funext κ
    simp
  · rw [hf]
    funext κ
    simp
  · obtain ⟨z, hz⟩ := (mem_sublattice_levelDepth_iff (x : FourTorus L n)).1 x.2
    refine (mem_sublattice_levelDepth_iff _).2 ⟨z ∘ σ, ?_⟩
    rw [hz]
    rfl
  · show (t + basisShift L n ν) ∘ σ - t ∘ σ = _
    rw [hadd, add_sub_cancel_left]
  intro b c hb ht hh
  obtain ⟨ν, hν⟩ := (isPositivelyOriented_iff b).1 hb
  have hhead : (b.target : FourTorus L n) = b.source + basisShift L n ν := eq_add_of_sub_eq' hν
  have hhh : (c.target : FourTorus L n) =
      (b.source : FourTorus L n) ∘ σ + basisShift L n (σ.symm ν) := by
    rw [hh, hhead]
    exact hadd _ ν
  have htt : (c.source : FourTorus L n) = (b.source : FourTorus L n) ∘ σ := ht
  rw [fourierModeForm_apply hS, fourierModeForm_apply hS, htt, hhh, hhead,
    edgeMode_add_basisShift hS, edgeMode_add_basisShift hS, phase_comp_perm hS hp]
  by_cases h : ν = σ μ
  · rw [if_pos h, if_pos (by rw [h]; simp)]
  · rw [if_neg h, if_neg (fun e => h (by rw [← e]; simp))]
def flipAxis (ρ : Fin 4) (x : FourTorus L n) : FourTorus L n :=
  Function.update x ρ (-x ρ)
theorem flipAxis_flipAxis (ρ : Fin 4) (x : FourTorus L n) : flipAxis ρ (flipAxis ρ x) = x := by
  funext κ
  by_cases h : κ = ρ
  · subst h
    simp [flipAxis]
  · simp [flipAxis, Function.update_of_ne h]
theorem flipAxis_add (ρ : Fin 4) (x y : FourTorus L n) :
    flipAxis ρ (x + y) = flipAxis ρ x + flipAxis ρ y := by
  funext κ
  by_cases h : κ = ρ
  · subst h
    simp [flipAxis, add_comm]
  · simp [flipAxis, Function.update_of_ne h]
theorem flipAxis_basisShift_self (ρ : Fin 4) :
    flipAxis ρ (basisShift L n ρ) = -basisShift L n ρ := by
  funext κ
  by_cases h : κ = ρ
  · subst h
    simp [flipAxis]
  · simp [flipAxis, Function.update_of_ne h, basisShift_apply_of_ne h]
theorem flipAxis_basisShift_of_ne {ρ ν : Fin 4} (h : ν ≠ ρ) :
    flipAxis ρ (basisShift L n ν) = basisShift L n ν := by
  funext κ
  by_cases hκ : κ = ρ
  · subst hκ
    simp [flipAxis, basisShift_apply_of_ne (Ne.symm h)]
  · simp [flipAxis, Function.update_of_ne hκ]
theorem axisReflectionMatrix_mulVec_eq_update (ρ : Fin 4) (y : AmbientSpace) :
    (axisReflectionMatrix ρ).mulVec y = Function.update y ρ (-y ρ) := by
  funext κ
  rw [axisReflectionMatrix, Matrix.mulVec_diagonal]
  by_cases h : κ = ρ
  · subst h
    simp
  · simp [h]
theorem phase_flipAxis (hS : 2 < torusSide L n) {p : AmbientSpace}
    (hp : p ∈ dualLattice (2 * L ^ n)) (ρ : Fin 4) (x : FourTorus L n) :
    phase p (flipAxis ρ x) = phase (flipCoord ρ p) x := by
  obtain ⟨y, rfl⟩ := torusProj_surjective x
  have h : flipAxis ρ (torusProj (torusSide L n) y) =
      torusProj (torusSide L n) (Function.update y ρ (-y ρ)) := by
    funext κ
    by_cases hκ : κ = ρ
    · subst hκ
      simp [flipAxis, torusProj]
    · simp [flipAxis, torusProj, Function.update_of_ne hκ]
  rw [h, phase_torusProj_eq_expPhase hS hp,
    phase_torusProj_eq_expPhase hS (flipCoord_mem_dualLattice hp ρ)]
  have hr : euclidDot p (Function.update y ρ (-y ρ)) = euclidDot (flipCoord ρ p) y := by
    unfold euclidDot
    refine Finset.sum_congr rfl fun κ _ => ?_
    by_cases hκ : κ = ρ
    · subst hκ
      simp [flipCoord]
    · simp [flipCoord, Function.update_of_ne hκ]
  unfold expPhase
  rw [hr]
theorem eq_flipAxis_of_isInducedByMotion (f : FourTorus L n → FourTorus L n) (ρ : Fin 4)
    (hind : IsInducedByMotion f (axisReflectionMatrix ρ) 0) (x : FourTorus L n) :
    f x = flipAxis ρ x := by
  obtain ⟨y, rfl⟩ := torusProj_surjective x
  rw [hind y, axisReflectionMatrix_mulVec_eq_update]
  have h0 : castVec (0 : Fin 4 → ℤ) = 0 := by
    funext μ
    simp [castVec]
  rw [h0, add_zero]
  funext κ
  by_cases hκ : κ = ρ
  · subst hκ
    simp [flipAxis, torusProj]
  · simp [flipAxis, torusProj, Function.update_of_ne hκ]
theorem flipAxis_mem_sublattice (ρ : Fin 4) (x : Vertex L n 0 0) :
    flipAxis ρ (x : FourTorus L n) ∈ sublattice L n (levelDepth 0 0) := by
  obtain ⟨z, hz⟩ := (mem_sublattice_levelDepth_iff (x : FourTorus L n)).1 x.2
  refine (mem_sublattice_levelDepth_iff _).2 ⟨Function.update z ρ (-z ρ), ?_⟩
  rw [hz]
  funext κ
  by_cases hκ : κ = ρ
  · subst hκ
    simp [flipAxis, torusProj, castVec]
  · simp [flipAxis, torusProj, castVec, Function.update_of_ne hκ]
theorem flipAxis_add_basisShift (ρ : Fin 4) (t : FourTorus L n) (ν : Fin 4) :
    ∃ ν' : Fin 4, flipAxis ρ (t + basisShift L n ν) - flipAxis ρ t = basisShift L n ν' ∨
      flipAxis ρ (t + basisShift L n ν) - flipAxis ρ t = -basisShift L n ν' := by
  rw [flipAxis_add, add_sub_cancel_left]
  by_cases h : ν = ρ
  · subst h
    exact ⟨ν, Or.inr (flipAxis_basisShift_self ν)⟩
  · exact ⟨ν, Or.inl (flipAxis_basisShift_of_ne h)⟩
theorem tangentPushforward_reflection_of_ne (hS : 2 < torusSide L n)
    (f : FourTorus L n → FourTorus L n) (ρ : Fin 4)
    (hind : IsInducedByMotion f (axisReflectionMatrix ρ) 0) (a : Fin 3) (μ : Fin 4) (hμ : μ ≠ ρ)
    (p : AmbientSpace) (hp : p ∈ dualLattice (2 * L ^ n)) :
    tangentPushforward f (fourierModeForm L n a p μ) = fourierModeForm L n a (flipCoord ρ p) μ := by
  have hf := eq_flipAxis_of_isInducedByMotion f ρ hind
  refine tangentPushforward_eq f (flipAxis ρ) (fun x => by rw [hf, flipAxis_flipAxis])
    (fun x => by rw [hf, flipAxis_flipAxis]) (flipAxis_mem_sublattice ρ) (flipAxis_add_basisShift ρ)
    _ _ (fourierModeForm_opposite hS a p μ) (fourierModeForm_opposite hS a _ _) ?_
  intro b c hb ht hh
  obtain ⟨ν, hν⟩ := (isPositivelyOriented_iff b).1 hb
  have hhead : (b.target : FourTorus L n) = b.source + basisShift L n ν := eq_add_of_sub_eq' hν
  rw [fourierModeForm_apply hS, fourierModeForm_apply hS, ht, hh, hhead, flipAxis_add]
  by_cases h : ν = ρ
  · subst h
    rw [flipAxis_basisShift_self, ← sub_eq_add_neg, edgeMode_sub_basisShift hS,
      edgeMode_add_basisShift hS, if_neg (Ne.symm hμ), if_neg (Ne.symm hμ)]
  · rw [flipAxis_basisShift_of_ne h, edgeMode_add_basisShift hS, edgeMode_add_basisShift hS,
      phase_flipAxis hS hp]
theorem tangentPushforward_reflection_self (hS : 2 < torusSide L n)
    (f : FourTorus L n → FourTorus L n) (ρ : Fin 4)
    (hind : IsInducedByMotion f (axisReflectionMatrix ρ) 0) (a : Fin 3) (p : AmbientSpace)
    (hp : p ∈ dualLattice (2 * L ^ n)) :
    tangentPushforward f (fourierModeForm L n a p ρ) =
      (-Complex.exp (-(Complex.I * (p ρ : ℂ)))) • fourierModeForm L n a (flipCoord ρ p) ρ := by
  have hf := eq_flipAxis_of_isInducedByMotion f ρ hind
  refine tangentPushforward_eq f (flipAxis ρ) (fun x => by rw [hf, flipAxis_flipAxis])
    (fun x => by rw [hf, flipAxis_flipAxis]) (flipAxis_mem_sublattice ρ) (flipAxis_add_basisShift ρ)
    _ _ (fourierModeForm_opposite hS a p ρ) (fun c => by simp [fourierModeForm_opposite hS]) ?_
  intro b c hb ht hh
  obtain ⟨ν, hν⟩ := (isPositivelyOriented_iff b).1 hb
  have hhead : (b.target : FourTorus L n) = b.source + basisShift L n ν := eq_add_of_sub_eq' hν
  rw [Pi.smul_apply, fourierModeForm_apply hS, fourierModeForm_apply hS, ht, hh, hhead,
    flipAxis_add]
  by_cases h : ν = ρ
  · subst h
    rw [flipAxis_basisShift_self, ← sub_eq_add_neg, edgeMode_sub_basisShift hS,
      edgeMode_add_basisShift hS, if_pos rfl, if_pos rfl, phase_sub_basisShift hS hp,
      phase_flipAxis hS hp, smul_smul, ← neg_smul, neg_mul, mul_comm]
  · rw [flipAxis_basisShift_of_ne h, edgeMode_add_basisShift hS, edgeMode_add_basisShift hS,
      if_neg h, if_neg h, smul_zero]
theorem covDiff_phaseSite (hS : 2 < torusSide L n) (a : Fin 3) (p : AmbientSpace)
    (hp : p ∈ dualLattice (2 * L ^ n)) :
    covDiff (k := 0) (j := 0) (identityField L n) (phaseSite L n a p) =
      ∑ μ, (Complex.exp (Complex.I * (p μ : ℂ)) - 1) • fourierModeForm L n a p μ := by
  unfold covDiff
  refine extendOddly_eq _ _ (fun c => ?_) fun b hb => ?_
  · simp only [Finset.sum_apply, Pi.smul_apply, fourierModeForm_opposite hS, smul_neg,
      Finset.sum_neg_distrib]
  · obtain ⟨ν, hν⟩ := (isPositivelyOriented_iff b).1 hb
    have hhead : (b.target : FourTorus L n) = b.source + basisShift L n ν :=
      eq_add_of_sub_eq' hν
    simp only [Finset.sum_apply, Pi.smul_apply, fourierModeForm_apply hS, hhead,
      edgeMode_add_basisShift hS]
    simp only [smul_ite, smul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    simp only [identityField, ComplexMatrix2.conjugateBy, phaseSite, hhead,
      phase_add_basisShift hS hp]
    simp only [inv_one, mul_one, one_mul, smul_smul, ← sub_smul]
    congr 1
    ring
theorem plane_wave_laws_hold : PlaneWaveLawsHold := by
  intro L n hL hn
  have hS : 2 < torusSide L n := two_lt_torusSide hL hn
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a μ p _
    refine ⟨fun b _ => ?_, fourierModeForm_opposite hS a p μ⟩
    rw [fourierModeForm_apply hS]
    unfold edgeMode
    split_ifs
    · exact ComplexMatrix2.traceless.smul_mem _ (pauliFamily_mem_traceless a)
    · exact ComplexMatrix2.traceless.neg_mem
        (ComplexMatrix2.traceless.smul_mem _ (pauliFamily_mem_traceless a))
    · exact ComplexMatrix2.traceless.zero_mem
  · intro a μ p hp e
    funext c
    rw [fourierModeForm_apply hS, fourierModeForm_apply hS]
    unfold edgeMode
    rw [phase_add_two_pi_smul hS hp e _ c.source.2, phase_add_two_pi_smul hS hp e _ c.target.2]
  · intro f m _ _ hind a μ p hp
    exact tangentPushforward_translation hS f m hind a μ p hp
  · intro f σ _ _ hind a μ p hp
    exact tangentPushforward_permutation hS f σ hind a μ p hp
  · intro f ρ _ _ hind a μ hμ p hp
    exact tangentPushforward_reflection_of_ne hS f ρ hind a μ hμ p hp
  · intro f ρ _ _ hind a p hp
    exact tangentPushforward_reflection_self hS f ρ hind a p hp
  · intro a p _ x
    exact ComplexMatrix2.traceless.smul_mem _ (pauliFamily_mem_traceless a)
  · intro a p hp
    exact covDiff_phaseSite hS a p hp
end YangMills.Construction.OneLoopLaw.PlaneWaveSymmetries
end
