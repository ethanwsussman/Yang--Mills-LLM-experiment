import YangMills.Construction.Lattice.KernelsOnPositiveBondFamilies
import YangMills.Construction.Lattice.LinearAveragesRoundACoarsePlaquette
import YangMills.Construction.Lattice.PathsOfBlocksAndDoubleBlocks
import Mathlib
set_option autoImplicit false
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.PeriodicLattice
variable {L m K n : ℕ}
private theorem sum_cell_boundaries_eq_sides {M : Type*} [AddCommGroup M] (h v : ℕ → ℕ → M)
    (N : ℕ) :
    ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, (h i j + v (i + 1) j - h i (j + 1) - v i j) =
      ∑ i ∈ Finset.range N, h i 0 + ∑ j ∈ Finset.range N, v N j -
        ∑ i ∈ Finset.range N, h i N - ∑ j ∈ Finset.range N, v 0 j := by
  have hsplit : ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
      (h i j + v (i + 1) j - h i (j + 1) - v i j) =
      ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, (h i j - h i (j + 1)) +
        ∑ j ∈ Finset.range N, ∑ i ∈ Finset.range N, (v (i + 1) j - v i j) := by
    rw [Finset.sum_comm (s := Finset.range N) (t := Finset.range N)
      (f := fun j i => v (i + 1) j - v i j), ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    abel
  have hh : ∀ i, ∑ j ∈ Finset.range N, (h i j - h i (j + 1)) = h i 0 - h i N :=
    fun i => Finset.sum_range_sub' (h i) N
  have hv : ∀ j, ∑ i ∈ Finset.range N, (v (i + 1) j - v i j) = v N j - v 0 j :=
    fun j => Finset.sum_range_sub (fun i => v i j) N
  rw [hsplit]
  simp only [hh, hv, Finset.sum_sub_distrib]
  abel
private theorem bondFormSumAlong_forwardFlow {j : ℤ} (A : Bond L m j → Matrices.ComplexMatrix2)
    (μ : Fin 4) (N : ℕ) (x : Site L m j) :
    bondFormSumAlong A (forwardAxisPath x μ N) =
      ∑ i ∈ Finset.range N, A (Bond.forwardFrom (x + (i : ℤ) • unitStep L m j μ) μ) := by
  induction N generalizing x with
  | zero => simp [bondFormSumAlong, forwardAxisPath]
  | succ N ih =>
    have hstep : bondFormSumAlong A (forwardAxisPath x μ (N + 1)) =
        A (Bond.forwardFrom x μ) + bondFormSumAlong A (forwardAxisPath (x + unitStep L m j μ) μ N) := by
      simp [bondFormSumAlong, forwardAxisPath]
    rw [hstep, ih, Finset.sum_range_succ', add_comm]
    congr 1
    · refine Finset.sum_congr rfl fun i _ => ?_
      congr 2
      push_cast
      rw [add_smul, one_smul]
      abel
    · simp
private theorem bondFormSumAlong_congr {j : ℤ} {A A' : Bond L m j → Matrices.ComplexMatrix2}
    {Γ : List (Bond L m j)} (h : ∀ b ∈ Γ, A' b = A b) :
    bondFormSumAlong A' Γ = bondFormSumAlong A Γ := by
  unfold bondFormSumAlong
  rw [List.map_congr_left h]
private theorem forwardFrom_isPositivelyOriented {j : ℤ} (x : Site L m j) (μ : Fin 4) :
    (Bond.forwardFrom x μ).IsPositivelyOriented :=
  ⟨μ, by simp [Bond.forwardFrom]⟩
private theorem bondFormSumAlong_boundaryBonds {j : ℤ} {A : Bond L m j → Matrices.ComplexMatrix2}
    (hA : ∀ b : Bond L m j, b.IsPositivelyOriented → A b.opposite = -A b) (q : Plaquette L m j) :
    bondFormSumAlong A q.boundaryBonds = A (Bond.forwardFrom q.origin q.firstAxis) +
      A (Bond.forwardFrom (q.origin + unitStep L m j q.firstAxis) q.secondAxis) -
      A (Bond.forwardFrom (q.origin + unitStep L m j q.secondAxis) q.firstAxis) -
      A (Bond.forwardFrom q.origin q.secondAxis) := by
  simp only [bondFormSumAlong, Plaquette.boundaryBonds, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, hA _ (forwardFrom_isPositivelyOriented _ _)]
  abel
private theorem eval_opposite_of_isPositivelyOriented {P : SymmetricBondSet L m K n}
    (a : LieBondField P) (hL : 1 < L) (hj : -(m : ℤ) < levelDepth K n) {b : BondAtLevel L m K n}
    (h : b.IsPositivelyOriented) :
    a.eval b.opposite = -a.eval b := by
  have nr : ¬ b.opposite.IsPositivelyOriented := Bond.opposite_not_isPositivelyOriented hL hj h
  by_cases hb : b ∈ P.bonds
  · rw [LieBondField.eval_opposite a ⟨b, hb, h⟩ nr, LieBondField.eval_of_positive a ⟨b, hb, h⟩]
  · have hr : b.opposite ∉ P.bonds := fun hr => hb (P.opposite_mem _ hr)
    have h₁ : a.eval b = 0 := by
      rw [LieBondField.eval, dif_neg (fun x => hb x.1), dif_neg (fun x => hr x.1)]
    have h₂ : a.eval b.opposite = 0 := by
      rw [LieBondField.eval, dif_neg (fun x => nr x.2), dif_neg (fun x => hb x.1)]
    rw [h₁, h₂, neg_zero]
private theorem matrixValues_restrictToDoubleBlock {Z : Set (SiteAtLevel L m K n)}
    (a : LieBondFieldWithin Z) (c : BondAtLevel L m K (n + 1))
    (hZ : ∀ b ∈ (bondsInDoubleBlock c : Set (BondAtLevel L m K n)), b.LiesIn Z)
    {b : BondAtLevel L m K n} (hb : b ∈ (bondsInDoubleBlock c : Set (BondAtLevel L m K n))) :
    LieBondField.matrixValues (LieBondField.restrictToDoubleBlock c a) b =
      LieBondField.matrixValues a b := by
  unfold LieBondField.matrixValues
  by_cases hp : b.IsPositivelyOriented
  · have h₁ : b ∈ (doubleBlockSymmetricSet c).bonds ∧ b.IsPositivelyOriented := ⟨hb, hp⟩
    have he := LieBondField.eval_of_positive (LieBondField.restrictToDoubleBlock c a) ⟨b, h₁⟩
    rw [show (LieBondField.restrictToDoubleBlock c a).eval b = a.eval b from he]
  · have hr := Bond.opposite_isPositivelyOriented hp
    have hbr : b.opposite ∈ (doubleBlockSymmetricSet c).bonds :=
      (doubleBlockSymmetricSet c).opposite_mem b hb
    have h₁ : ¬ (b ∈ (doubleBlockSymmetricSet c).bonds ∧ b.IsPositivelyOriented) :=
      fun h => hp h.2
    have h₂ : b.opposite ∈ (doubleBlockSymmetricSet c).bonds ∧
        b.opposite.IsPositivelyOriented := ⟨hbr, hr⟩
    have h₃ : ¬ (b ∈ (bondsWithin Z).bonds ∧ b.IsPositivelyOriented) := fun h => hp h.2
    have h₄ : b.opposite ∈ (bondsWithin Z).bonds ∧ b.opposite.IsPositivelyOriented :=
      ⟨hZ _ hbr, hr⟩
    have e₁ : (LieBondField.restrictToDoubleBlock c a).eval b = -a.eval b.opposite := by
      rw [LieBondField.eval, dif_neg h₁, dif_pos h₂]
      rfl
    have e₂ : a.eval b = -a ⟨b.opposite, h₄⟩ := by
      rw [LieBondField.eval, dif_neg h₃, dif_pos h₄]
    have e₃ := LieBondField.eval_of_positive a ⟨b.opposite, h₄⟩
    rw [e₁, e₂, show a.eval b.opposite = a ⟨b.opposite, h₄⟩ from e₃]
private def blockContourTotal (s : AveragingScheme)
    (A : BondAtLevel L m K n → Matrices.ComplexMatrix2) (y : SiteAtLevel L m K (n + 1)) :
    Matrices.ComplexMatrix2 :=
  ∑ᶠ x ∈ sitesInBlock (levelDepth K n) y, contourFormMean s A y x
private def crossingPathTotal (A : BondAtLevel L m K n → Matrices.ComplexMatrix2)
    (c : BondAtLevel L m K (n + 1)) : Matrices.ComplexMatrix2 :=
  ∑ᶠ x ∈ sitesInBlock (levelDepth K n) c.source, bondFormSumAlong A (crossingPath c x)
private theorem sitesInBlock_card (hP : BlockPaths.Statement)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) (hn : n < K)
    (y : SiteAtLevel L m K (n + 1)) :
    ∃ hf : (sitesInBlock (levelDepth K n) y : Set (SiteAtLevel L m K n)).Finite,
      hf.toFinset.card = L ^ 4 := by
  obtain ⟨⟨⟨_, hIm⟩, hcard, _⟩, _⟩ := (hP L m K hL.1 hL.2 hm n hn).1 y
  have hLpos : 0 < L := by have := hL.2; omega
  have himg : (fun x : SiteAtLevel L m K n => (x : FourTorus L m)) ''
      sitesInBlock (levelDepth K n) y = unitBlock y := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro hz
      have hz' := hz
      rw [← hIm] at hz'
      obtain ⟨q, hq, rfl⟩ := hz'
      exact ⟨_, hz, rfl⟩
  have hfinB : (unitBlock y).Finite :=
    Set.finite_of_ncard_pos (by rw [hcard]; positivity)
  have hf : (sitesInBlock (levelDepth K n) y : Set (SiteAtLevel L m K n)).Finite :=
    Set.Finite.of_finite_image (by rw [himg]; exact hfinB) Subtype.val_injective.injOn
  refine ⟨hf, ?_⟩
  rw [← Set.ncard_eq_toFinset_card _ hf, ← hcard, ← himg,
    Set.ncard_image_of_injective _ Subtype.val_injective]
private theorem linearSchemeAverage_eq (hP : BlockPaths.Statement)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) (hn : n < K) (s : AveragingScheme)
    (c : BondAtLevel L m K (n + 1)) (μ : Fin 4)
    (hc : c.target - c.source = unitStep L m (levelDepth K (n + 1)) μ)
    {A A' : BondAtLevel L m K n → Matrices.ComplexMatrix2}
    (hA : ∀ b ∈ (bondsInDoubleBlock c : Set (BondAtLevel L m K n)), A' b = A b) :
    linearSchemeAverage s A' c =
      inverseFourthPowerWeight L • (blockContourTotal s A c.source + crossingPathTotal A c -
        blockContourTotal s A c.target) := by
  obtain ⟨⟨_, _, _, himg, htr, _⟩, _, _, _, ⟨hpaths, hcross⟩⟩ :=
    (hP L m K hL.1 hL.2 hm n hn).2 c μ hc
  obtain ⟨hf₁, _⟩ := sitesInBlock_card hP hL hm hn c.source
  have hloc : ∀ y : SiteAtLevel L m K (n + 1), (y = c.source ∨ y = c.target) →
      ∀ x ∈ sitesInBlock (levelDepth K n) y, contourFormMean s A' y x = contourFormMean s A y x := by
    intro y hy x hx
    obtain ⟨h₁, h₂⟩ := hpaths y hy x hx
    cases s with
    | centred =>
      simp only [contourFormMean, contourFormAverage]
      congr 1
      refine Finset.sum_congr rfl fun σ _ => ?_
      exact bondFormSumAlong_congr fun b hb => hA b (h₁ _ ⟨σ, rfl⟩ b hb)
    | cornered =>
      simp only [contourFormMean]
      exact bondFormSumAlong_congr fun b hb => hA b (h₂ b hb)
  have hmaps : ∀ x ∈ sitesInBlock (levelDepth K n) c.source,
      x + blockTranslation L m (levelDepth K n) μ ∈ sitesInBlock (levelDepth K n) c.target :=
    fun x hx => by
      rw [← himg]
      exact ⟨x, hx, rfl⟩
  have hterm : ∀ x ∈ sitesInBlock (levelDepth K n) c.source,
      contourFormMean s A' c.source x + bondFormSumAlong A' (crossingPath c x) -
          contourFormMean s A' c.target (shiftAcross c x) =
        contourFormMean s A c.source x + bondFormSumAlong A (crossingPath c x) -
          contourFormMean s A c.target (x + blockTranslation L m (levelDepth K n) μ) := by
    intro x hx
    rw [htr x hx, hloc _ (Or.inl rfl) x hx, hloc _ (Or.inr rfl) _ (hmaps x hx),
      bondFormSumAlong_congr fun b hb => hA b (hcross x hx b hb)]
  have htarget : blockContourTotal s A c.target = ∑ᶠ x ∈ sitesInBlock (levelDepth K n) c.source,
      contourFormMean s A c.target (x + blockTranslation L m (levelDepth K n) μ) := by
    rw [blockContourTotal, ← himg, finsum_mem_image (add_left_injective _).injOn]
  unfold linearSchemeAverage
  rw [finsum_mem_congr rfl hterm, htarget, blockContourTotal, crossingPathTotal]
  simp only [finsum_mem_eq_finite_toFinset_sum _ hf₁, Finset.sum_sub_distrib,
    Finset.sum_add_distrib]
private theorem crossingPathTotal_eq (hP : BlockPaths.Statement)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) (hn : n < K)
    (A : BondAtLevel L m K n → Matrices.ComplexMatrix2) (c : BondAtLevel L m K (n + 1)) (μ : Fin 4)
    (hc : c.target - c.source = unitStep L m (levelDepth K (n + 1)) μ)
    {y : SiteAtLevel L m K (n + 1)} (hy : c.source = y)
    (hf : (sitesInBlock (levelDepth K n) y : Set (SiteAtLevel L m K n)).Finite) :
    crossingPathTotal A c = ∑ x ∈ hf.toFinset, bondFormSumAlong A (forwardAxisPath x μ L) := by
  subst hy
  obtain ⟨_, _, _, ⟨hst, _⟩, _⟩ := (hP L m K hL.1 hL.2 hm n hn).2 c μ hc
  unfold crossingPathTotal
  rw [finsum_mem_congr rfl fun x hx => by rw [(hst x hx).2.1],
    finsum_mem_eq_finite_toFinset_sum _ hf]
private theorem crossingPathTotal_translated (hP : BlockPaths.Statement)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) (hn : n < K)
    (A : BondAtLevel L m K n → Matrices.ComplexMatrix2) (c c' : BondAtLevel L m K (n + 1))
    (μ ν : Fin 4) (hc : c.target - c.source = unitStep L m (levelDepth K (n + 1)) μ)
    (hc' : c'.target - c'.source = unitStep L m (levelDepth K (n + 1)) ν)
    (ht : c'.source = c.target) {y : SiteAtLevel L m K (n + 1)} (hy : c.source = y)
    (hf : (sitesInBlock (levelDepth K n) y : Set (SiteAtLevel L m K n)).Finite) :
    crossingPathTotal A c' = ∑ x ∈ hf.toFinset,
      bondFormSumAlong A (forwardAxisPath (x + blockTranslation L m (levelDepth K n) μ) ν L) := by
  subst hy
  obtain ⟨⟨_, _, _, himg, _, _⟩, _⟩ := (hP L m K hL.1 hL.2 hm n hn).2 c μ hc
  obtain ⟨_, _, _, ⟨hst, _⟩, _⟩ := (hP L m K hL.1 hL.2 hm n hn).2 c' ν hc'
  unfold crossingPathTotal
  rw [finsum_mem_congr rfl fun x hx => by rw [(hst x hx).2.1], ht, ← himg,
    finsum_mem_image (add_left_injective _).injOn, finsum_mem_eq_finite_toFinset_sum _ hf]
private def gridSite {j : ℤ} (x : Site L m j) (μ ν : Fin 4) (i k : ℕ) : Site L m j :=
  x + (i : ℤ) • unitStep L m j μ + (k : ℤ) • unitStep L m j ν
private theorem gridSite_add_first {j : ℤ} (x : Site L m j) (μ ν : Fin 4) (i k : ℕ) :
    gridSite x μ ν i k + unitStep L m j μ = gridSite x μ ν (i + 1) k := by
  simp only [gridSite]
  push_cast
  rw [add_smul, one_smul]
  abel
private theorem gridSite_add_second {j : ℤ} (x : Site L m j) (μ ν : Fin 4) (i k : ℕ) :
    gridSite x μ ν i k + unitStep L m j ν = gridSite x μ ν i (k + 1) := by
  simp only [gridSite]
  push_cast
  rw [add_smul, one_smul]
  abel
private theorem sum_around_square {j : ℤ} {A : Bond L m j → Matrices.ComplexMatrix2}
    (hA : ∀ b : Bond L m j, b.IsPositivelyOriented → A b.opposite = -A b) (x : Site L m j)
    (μ ν : Fin 4) (h : μ < ν) (N : ℕ) :
    bondFormSumAlong A (forwardAxisPath x μ N) +
        bondFormSumAlong A (forwardAxisPath (x + (N : ℤ) • unitStep L m j μ) ν N) -
        bondFormSumAlong A (forwardAxisPath (x + (N : ℤ) • unitStep L m j ν) μ N) -
        bondFormSumAlong A (forwardAxisPath x ν N) =
      ∑ i ∈ Finset.range N, ∑ k ∈ Finset.range N,
        bondFormSumAlong A (Plaquette.boundaryBonds ⟨gridSite x μ ν i k, μ, ν, h⟩) := by
  have hb : ∀ i k, bondFormSumAlong A (Plaquette.boundaryBonds ⟨gridSite x μ ν i k, μ, ν, h⟩) =
      A (Bond.forwardFrom (gridSite x μ ν i k) μ) +
        A (Bond.forwardFrom (gridSite x μ ν (i + 1) k) ν) -
        A (Bond.forwardFrom (gridSite x μ ν i (k + 1)) μ) -
        A (Bond.forwardFrom (gridSite x μ ν i k) ν) := by
    intro i k
    rw [bondFormSumAlong_boundaryBonds hA]
    simp only [gridSite_add_first, gridSite_add_second]
  rw [Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => hb i k,
    sum_cell_boundaries_eq_sides (fun i k => A (Bond.forwardFrom (gridSite x μ ν i k) μ))
      (fun i k => A (Bond.forwardFrom (gridSite x μ ν i k) ν)) N]
  simp only [bondFormSumAlong_forwardFlow]
  congr 1
  · congr 1
    · congr 1
      · refine Finset.sum_congr rfl fun i _ => ?_
        simp [gridSite]
    · refine Finset.sum_congr rfl fun i _ => ?_
      simp only [gridSite]
      rw [add_right_comm]
  · refine Finset.sum_congr rfl fun i _ => ?_
    simp [gridSite]
private theorem mem_fourCornerBlockSites {p : PlaquetteAtLevel L m K (n + 1)}
    {y : SiteAtLevel L m K (n + 1)} (hy : y ∈ p.vertices) {z : SiteAtLevel L m K n}
    (hz : (z : FourTorus L m) ∈ unitBlock y) : z ∈ fourCornerBlockSites p :=
  Set.mem_iUnion₂.mpr ⟨y, hy, hz⟩
private theorem liesIn_of_endpoints {p : PlaquetteAtLevel L m K (n + 1)}
    {c : BondAtLevel L m K (n + 1)} (ht : c.source ∈ p.vertices) (hh : c.target ∈ p.vertices) :
    ∀ b ∈ (bondsInDoubleBlock c : Set (BondAtLevel L m K n)),
      b.LiesIn (fourCornerBlockSites p) := by
  intro b hb
  constructor
  · rcases hb.1 with h | h
    · exact mem_fourCornerBlockSites ht h
    · exact mem_fourCornerBlockSites hh h
  · rcases hb.2 with h | h
    · exact mem_fourCornerBlockSites ht h
    · exact mem_fourCornerBlockSites hh h
private theorem origin_mem_vertices (p : PlaquetteAtLevel L m K (n + 1)) :
    p.origin ∈ p.vertices := by
  simp [Plaquette.vertices]
private theorem first_mem_vertices (p : PlaquetteAtLevel L m K (n + 1)) :
    p.origin + unitStep L m (levelDepth K (n + 1)) p.firstAxis ∈ p.vertices := by
  simp [Plaquette.vertices]
private theorem far_mem_vertices (p : PlaquetteAtLevel L m K (n + 1)) :
    p.origin + unitStep L m (levelDepth K (n + 1)) p.firstAxis +
      unitStep L m (levelDepth K (n + 1)) p.secondAxis ∈ p.vertices := by
  simp [Plaquette.vertices]
private theorem second_mem_vertices (p : PlaquetteAtLevel L m K (n + 1)) :
    p.origin + unitStep L m (levelDepth K (n + 1)) p.secondAxis ∈ p.vertices := by
  simp [Plaquette.vertices]
private theorem gridSite_mem (hP : BlockPaths.Statement)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) (hn : n < K)
    (p : PlaquetteAtLevel L m K (n + 1)) {x : SiteAtLevel L m K n}
    (hx : x ∈ sitesInBlock (levelDepth K n) p.origin) {i k : ℕ} (hi : i ≤ L) (hk : k ≤ L) :
    gridSite x p.firstAxis p.secondAxis i k ∈ fourCornerBlockSites p := by
  have hs : ∀ (c : BondAtLevel L m K (n + 1)) (μ : Fin 4),
      c.target - c.source = unitStep L m (levelDepth K (n + 1)) μ →
      ∀ w ∈ sitesInBlock (levelDepth K n) c.source, ∀ t : ℕ, t ≤ L →
        ((w + (t : ℤ) • unitStep L m (levelDepth K n) μ : SiteAtLevel L m K n) : FourTorus L m) ∈
          bondDoubleBlock c := by
    intro c μ hc w hw t ht
    obtain ⟨_, _, _, ⟨hst, _⟩, _⟩ := (hP L m K hL.1 hL.2 hm n hn).2 c μ hc
    exact (hst w hw).2.2.2 t ht
  have d₁ : (firstEdge p).target - (firstEdge p).source =
      unitStep L m (levelDepth K (n + 1)) p.firstAxis := by simp [firstEdge, Bond.forwardFrom]
  have d₂ : (secondEdge p).target - (secondEdge p).source =
      unitStep L m (levelDepth K (n + 1)) p.secondAxis := by simp [secondEdge, Bond.forwardFrom]
  have d₄ : (fourthEdge p).target - (fourthEdge p).source =
      unitStep L m (levelDepth K (n + 1)) p.secondAxis := by simp [fourthEdge, Bond.forwardFrom]
  set w : SiteAtLevel L m K n := x + (i : ℤ) • unitStep L m (levelDepth K n) p.firstAxis with hw
  rcases hs _ _ d₁ x hx i hi with h | h
  · rcases hs _ _ d₄ w h k hk with h' | h'
    · exact mem_fourCornerBlockSites (origin_mem_vertices p) h'
    · exact mem_fourCornerBlockSites (second_mem_vertices p) h'
  · rcases hs _ _ d₂ w h k hk with h' | h'
    · exact mem_fourCornerBlockSites (first_mem_vertices p) h'
    · exact mem_fourCornerBlockSites (far_mem_vertices p) h'
private theorem gridPlaquette_liesIn (hP : BlockPaths.Statement)
    (hL : Conventions.IsAdmissibleBlockingFactor L) (hm : 0 < m) (hn : n < K)
    (p : PlaquetteAtLevel L m K (n + 1)) {x : SiteAtLevel L m K n}
    (hx : x ∈ sitesInBlock (levelDepth K n) p.origin) {i k : ℕ} (hi : i < L) (hk : k < L) :
    (⟨gridSite x p.firstAxis p.secondAxis i k, p.firstAxis, p.secondAxis,
      p.firstAxis_lt_secondAxis⟩ : PlaquetteAtLevel L m K n).LiesIn (fourCornerBlockSites p) := by
  intro w hw
  simp only [Plaquette.vertices, Set.mem_insert_iff, Set.mem_singleton_iff] at hw
  rcases hw with rfl | rfl | rfl | rfl
  · exact gridSite_mem hP hL hm hn p hx hi.le hk.le
  · rw [gridSite_add_first]
    exact gridSite_mem hP hL hm hn p hx hi hk.le
  · rw [gridSite_add_first, gridSite_add_second]
    exact gridSite_mem hP hL hm hn p hx hi hk
  · rw [gridSite_add_second]
    exact gridSite_mem hP hL hm hn p hx hi.le hk
theorem CoarsePlaquetteLinearAverageBound.holds (hP : BlockPaths.Statement) :
    CoarsePlaquetteLinearAverageBound.Statement := by
  intro L hL m K n hm hn s p a D hD
  have hL13 := hL.2
  have hL1 : 1 < L := by omega
  have hj : -(m : ℤ) < levelDepth K n := by
    simp only [levelDepth]
    omega
  have hAr : ∀ b : BondAtLevel L m K n, b.IsPositivelyOriented →
      LieBondField.matrixValues a b.opposite = -LieBondField.matrixValues a b := by
    intro b hb
    simp only [LieBondField.matrixValues]
    rw [eval_opposite_of_isPositivelyOriented a hL1 hj hb]
    rfl
  have d₁ : (firstEdge p).target - (firstEdge p).source =
      unitStep L m (levelDepth K (n + 1)) p.firstAxis := by simp [firstEdge, Bond.forwardFrom]
  have d₂ : (secondEdge p).target - (secondEdge p).source =
      unitStep L m (levelDepth K (n + 1)) p.secondAxis := by simp [secondEdge, Bond.forwardFrom]
  have d₃ : (thirdEdge p).target - (thirdEdge p).source =
      unitStep L m (levelDepth K (n + 1)) p.firstAxis := by simp [thirdEdge, Bond.forwardFrom]
  have d₄ : (fourthEdge p).target - (fourthEdge p).source =
      unitStep L m (levelDepth K (n + 1)) p.secondAxis := by simp [fourthEdge, Bond.forwardFrom]
  have e₂₃ : (secondEdge p).target = (thirdEdge p).target :=
    add_right_comm p.origin _ _
  have c₃ : (thirdEdge p).target ∈ p.vertices := e₂₃ ▸ far_mem_vertices p
  have l₁ := linearSchemeAverage_eq hP hL hm hn s _ _ d₁ (A := LieBondField.matrixValues a)
    (fun b hb => matrixValues_restrictToDoubleBlock a _
      (liesIn_of_endpoints (c := firstEdge p) (origin_mem_vertices p) (first_mem_vertices p)) hb)
  have l₂ := linearSchemeAverage_eq hP hL hm hn s _ _ d₂ (A := LieBondField.matrixValues a)
    (fun b hb => matrixValues_restrictToDoubleBlock a _
      (liesIn_of_endpoints (c := secondEdge p) (first_mem_vertices p) (far_mem_vertices p)) hb)
  have l₃ := linearSchemeAverage_eq hP hL hm hn s _ _ d₃ (A := LieBondField.matrixValues a)
    (fun b hb => matrixValues_restrictToDoubleBlock a _
      (liesIn_of_endpoints (c := thirdEdge p) (second_mem_vertices p) c₃) hb)
  have l₄ := linearSchemeAverage_eq hP hL hm hn s _ _ d₄ (A := LieBondField.matrixValues a)
    (fun b hb => matrixValues_restrictToDoubleBlock a _
      (liesIn_of_endpoints (c := fourthEdge p) (origin_mem_vertices p) (second_mem_vertices p)) hb)
  obtain ⟨hf, hcard⟩ := sitesInBlock_card hP hL hm hn p.origin
  have k₁ := crossingPathTotal_eq hP hL hm hn (LieBondField.matrixValues a) _ _ d₁ rfl hf
  have k₄ := crossingPathTotal_eq hP hL hm hn (LieBondField.matrixValues a) _ _ d₄ rfl hf
  have k₂ := crossingPathTotal_translated hP hL hm hn (LieBondField.matrixValues a) _
    (secondEdge p) _ _ d₁ d₂ rfl rfl hf
  have k₃ := crossingPathTotal_translated hP hL hm hn (LieBondField.matrixValues a) _
    (thirdEdge p) _ _ d₄ d₃ rfl rfl hf
  have hsum : plaquetteLinearAverage s a p = inverseFourthPowerWeight L •
      ∑ x ∈ hf.toFinset, ∑ i ∈ Finset.range L, ∑ k ∈ Finset.range L,
        bondFormSumAlong (LieBondField.matrixValues a) (Plaquette.boundaryBonds
          ⟨gridSite x p.firstAxis p.secondAxis i k, p.firstAxis, p.secondAxis,
            p.firstAxis_lt_secondAxis⟩) := by
    unfold plaquetteLinearAverage
    rw [l₁, l₂, l₃, l₄, e₂₃]
    have e₁₂ : (firstEdge p).target = (secondEdge p).source := rfl
    have e₃₄ : (thirdEdge p).source = (fourthEdge p).target := rfl
    have e₄₁ : (fourthEdge p).source = (firstEdge p).source := rfl
    rw [e₁₂, e₃₄, e₄₁, ← smul_add, ← smul_sub, ← smul_sub]
    congr 1
    have hcollect :
        blockContourTotal s (LieBondField.matrixValues a) (firstEdge p).source +
          crossingPathTotal (LieBondField.matrixValues a) (firstEdge p) -
          blockContourTotal s (LieBondField.matrixValues a) (secondEdge p).source +
        (blockContourTotal s (LieBondField.matrixValues a) (secondEdge p).source +
          crossingPathTotal (LieBondField.matrixValues a) (secondEdge p) -
          blockContourTotal s (LieBondField.matrixValues a) (thirdEdge p).target) -
        (blockContourTotal s (LieBondField.matrixValues a) (fourthEdge p).target +
          crossingPathTotal (LieBondField.matrixValues a) (thirdEdge p) -
          blockContourTotal s (LieBondField.matrixValues a) (thirdEdge p).target) -
        (blockContourTotal s (LieBondField.matrixValues a) (firstEdge p).source +
          crossingPathTotal (LieBondField.matrixValues a) (fourthEdge p) -
          blockContourTotal s (LieBondField.matrixValues a) (fourthEdge p).target) =
        crossingPathTotal (LieBondField.matrixValues a) (firstEdge p) +
          crossingPathTotal (LieBondField.matrixValues a) (secondEdge p) -
          crossingPathTotal (LieBondField.matrixValues a) (thirdEdge p) -
          crossingPathTotal (LieBondField.matrixValues a) (fourthEdge p) := by
      abel
    rw [hcollect, k₁, k₂, k₃, k₄,
      Finset.sum_congr rfl fun x _ =>
        (sum_around_square hAr x p.firstAxis p.secondAxis p.firstAxis_lt_secondAxis L).symm]
    simp only [blockTranslation, Finset.sum_sub_distrib, Finset.sum_add_distrib]
    rfl
  have hG : ∀ x ∈ hf.toFinset, ‖∑ i ∈ Finset.range L, ∑ k ∈ Finset.range L,
      bondFormSumAlong (LieBondField.matrixValues a) (Plaquette.boundaryBonds
        ⟨gridSite x p.firstAxis p.secondAxis i k, p.firstAxis, p.secondAxis,
          p.firstAxis_lt_secondAxis⟩)‖ ≤ (L : ℝ) ^ 2 * D := by
    intro x hx
    have hx' : x ∈ sitesInBlock (levelDepth K n) p.origin := hf.mem_toFinset.mp hx
    have hb := norm_sum_le_of_le (Finset.range L) (f := fun i => ∑ k ∈ Finset.range L,
        bondFormSumAlong (LieBondField.matrixValues a) (Plaquette.boundaryBonds
          ⟨gridSite x p.firstAxis p.secondAxis i k, p.firstAxis, p.secondAxis,
            p.firstAxis_lt_secondAxis⟩))
      (n := fun _ => (L : ℝ) * D) (fun i hi => by
        have hb' := norm_sum_le_of_le (Finset.range L) (f := fun k =>
            bondFormSumAlong (LieBondField.matrixValues a) (Plaquette.boundaryBonds
              ⟨gridSite x p.firstAxis p.secondAxis i k, p.firstAxis, p.secondAxis,
                p.firstAxis_lt_secondAxis⟩))
          (n := fun _ => D) (fun k hk => hD _
            (gridPlaquette_liesIn hP hL hm hn p hx' (Finset.mem_range.mp hi)
              (Finset.mem_range.mp hk)))
        simpa using hb')
    calc _ ≤ _ := hb
      _ = (L : ℝ) ^ 2 * D := by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        ring
  have hsumle := norm_sum_le_of_le hf.toFinset hG
  simp only [Finset.sum_const, hcard, nsmul_eq_mul] at hsumle
  have hw : ‖inverseFourthPowerWeight L‖ = ((L : ℝ) ^ 4)⁻¹ := by
    have hLpos : (0 : ℝ) ≤ (L : ℝ) ^ (-4 : ℤ) := by positivity
    rw [inverseFourthPowerWeight, Complex.norm_real, Real.norm_of_nonneg hLpos, zpow_neg]
    norm_cast
  change ‖plaquetteLinearAverage s a p‖ ≤ (L : ℝ) ^ 2 * D
  rw [hsum, norm_smul, hw]
  calc _ ≤ ((L : ℝ) ^ 4)⁻¹ * (((L ^ 4 : ℕ) : ℝ) * ((L : ℝ) ^ 2 * D)) :=
        mul_le_mul_of_nonneg_left hsumle (by positivity)
    _ = (L : ℝ) ^ 2 * D := by
      push_cast
      field_simp
end YangMills.Construction.PeriodicLattice
