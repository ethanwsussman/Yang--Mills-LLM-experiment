import YangMills.Construction.Lattice.AveragingMapContinuousOnEachCaseSetProof
import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Lattice.OneStepSchemes
import Mathlib
import YangMills.Construction.Lattice.PathsOfBlocksAndDoubleBlocks
import YangMills.Construction.Matrices.NormExpLogConjugation
set_option autoImplicit false

noncomputable section
namespace YangMills.Construction
namespace PeriodicLattice
open Matrices
variable {L m K n : ℕ}
def HolonomyGaugeLawOnDoubleBlock (h : SiteAtLevel L m K n → ComplexMatrix2)
    (W : BondAtLevel L m K n → ComplexMatrix2) (c : BondAtLevel L m K (n + 1)) : Prop :=
  ∀ (γ : List (BondAtLevel L m K n)) (z z' : SiteAtLevel L m K n), IsBondPathFromTo γ z z' →
    (z : FourTorus L m) ∈ bondDoubleBlock c →
    (∀ b ∈ γ, b ∈ (bondsInDoubleBlock c : Set (BondAtLevel L m K n))) →
      pathHolonomy (gaugeTransform h W) γ = h z * pathHolonomy W γ * (h z')⁻¹
structure CorneredSchemeGaugeLaw (h : SiteAtLevel L m K n → ComplexMatrix2)
    (W : BondAtLevel L m K n → ComplexMatrix2) (c : BondAtLevel L m K (n + 1)) : Prop where
  holonomy_law : HolonomyGaugeLawOnDoubleBlock h W c
  cornered_path : ∀ y ∈ ({c.source, c.target} : Set (SiteAtLevel L m K (n + 1))),
    ∀ x ∈ sitesInBlock (levelDepth K n) y,
      IsBondPathFromTo (coordinateComb (schemeBaseSite .cornered (levelDepth K n) y) x)
          (schemeBaseSite .cornered (levelDepth K n) y) x ∧
        ∀ b ∈ coordinateComb (schemeBaseSite .cornered (levelDepth K n) y) x,
          b ∈ (bondsInDoubleBlock c : Set (BondAtLevel L m K n))
  contourHolonomy_eq : ∀ y ∈ ({c.source, c.target} : Set (SiteAtLevel L m K (n + 1))),
    ∀ x ∈ sitesInBlock (levelDepth K n) y,
      contourHolonomy .cornered (gaugeTransform h W) y x =
        h (schemeBaseSite .cornered (levelDepth K n) y) * contourHolonomy .cornered W y x *
          (h x)⁻¹
  localDefect_eq : ∀ x ∈ sitesInBlock (levelDepth K n) c.source,
    localDefect .cornered (gaugeTransform h W) c x =
      h (schemeBaseSite .cornered (levelDepth K n) c.source) * localDefect .cornered W c x *
        (h (schemeBaseSite .cornered (levelDepth K n) c.source))⁻¹
def ExpLogConjugationCovariant (g : ComplexMatrix2) : Prop :=
  (∀ Z : ComplexMatrix2, ComplexMatrix2.matExp (g * Z * g⁻¹) = g * ComplexMatrix2.matExp Z * g⁻¹) ∧
    ∀ X ∈ ComplexMatrix2.logBall, g * X * g⁻¹ ∈ ComplexMatrix2.logBall →
      ComplexMatrix2.logSeries (g * X * g⁻¹) = g * ComplexMatrix2.logSeries X * g⁻¹
def CorneredSchemeGaugeLawAndConjugation : Prop :=
  (∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ m K n : ℕ, 0 < m → n < K →
    ∀ c : BondAtLevel L m K (n + 1), c.IsPositivelyOriented →
    ∀ (h : SiteAtLevel L m K n → ComplexMatrix2) (W : BondAtLevel L m K n → ComplexMatrix2),
      (∀ x : SiteAtLevel L m K n, (x : FourTorus L m) ∈ bondDoubleBlock c →
        h x ∈ compactGaugeGroup) →
      IsGaugeField complexGaugeGroup (bondsInDoubleBlock c) W → CorneredSchemeGaugeLaw h W c) ∧
  (∀ g : ComplexMatrix2, IsUnit g.det → ExpLogConjugationCovariant g) ∧
  ∀ g ∈ Matrix.unitaryGroup (Fin 2) ℂ, ∀ X ∈ ComplexMatrix2.logBall,
    g * X * g⁻¹ ∈ ComplexMatrix2.logBall
end PeriodicLattice
end YangMills.Construction
end

noncomputable section
namespace YangMills.Construction.PeriodicLattice
open YangMills.Construction.Matrices YangMills.Construction.Conventions
variable {L m K n : ℕ}
private theorem inv_mul_self_of_mem_compact {V : ComplexMatrix2} (hV : V ∈ compactGaugeGroup) :
    V⁻¹ * V = 1 :=
  Matrix.nonsing_inv_mul V (by rw [(Matrix.mem_specialUnitaryGroup_iff.1 hV).2]; exact isUnit_one)
abbrev _root_.YangMills.SharedProofs.p14555 := @inv_mul_self_of_mem_compact
private theorem mul_inv_self_of_mem_compact {V : ComplexMatrix2} (hV : V ∈ compactGaugeGroup) :
    V * V⁻¹ = 1 :=
  Matrix.mul_nonsing_inv V (by rw [(Matrix.mem_specialUnitaryGroup_iff.1 hV).2]; exact isUnit_one)
abbrev _root_.YangMills.SharedProofs.p16098 := @mul_inv_self_of_mem_compact
private theorem inv_inv_of_mem_compact {V : ComplexMatrix2} (hV : V ∈ compactGaugeGroup) :
    V⁻¹⁻¹ = V := by apply _root_.YangMills.Construction.PeriodicLattice.BlockAverageContinuity.inv_inv_of_mem_compactGaugeGroup <;> assumption
private theorem isBondPathFromTo_tail {j : ℤ} {b : Bond L m j} {Γ : List (Bond L m j)}
    {z z' : Site L m j} (hp : IsBondPathFromTo (b :: Γ) z z') :
    IsBondPathFromTo Γ b.target z' := by
  obtain ⟨hc, -, -, hl⟩ := hp
  cases Γ with
  | nil =>
    refine ⟨List.isChain_nil, fun _ => ?_, by simp, by simp⟩
    exact hl b (by simp)
  | cons b' Γ =>
    rw [IsBondPath, List.isChain_cons_cons] at hc
    refine ⟨hc.2, by simp, ?_, ?_⟩
    · intro b'' hb''
      simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hb''
      rw [← hb'']
      exact hc.1.symm
    · intro b'' hb''
      refine hl b'' ?_
      simpa [List.getLast?_cons_cons] using hb''
private theorem holonomyGaugeLaw_of_mem_compact (c : BondAtLevel L m K (n + 1))
    (h : SiteAtLevel L m K n → ComplexMatrix2) (W : BondAtLevel L m K n → ComplexMatrix2)
    (hh : ∀ x : SiteAtLevel L m K n, (x : FourTorus L m) ∈ bondDoubleBlock c →
      h x ∈ compactGaugeGroup) :
    HolonomyGaugeLawOnDoubleBlock h W c := by
  intro Γ
  induction Γ with
  | nil =>
    intro z z' hp hz _
    obtain rfl : z = z' := hp.2.1 rfl
    simp [pathHolonomy, mul_inv_self_of_mem_compact (hh z hz)]
  | cons b Γ ih =>
    intro z z' hp hz hb
    have hsrc : b.source = z := hp.2.2.1 b (by simp)
    have hb₀ : b ∈ (bondsInDoubleBlock c : Set (BondAtLevel L m K n)) := hb b (by simp)
    have htgt : (b.target : FourTorus L m) ∈ bondDoubleBlock c := hb₀.2
    have hrest := ih b.target z' (isBondPathFromTo_tail hp) htgt
      (fun b' hb' => hb b' (List.mem_cons_of_mem _ hb'))
    have hcancel : ∀ X : ComplexMatrix2, (h b.target)⁻¹ * (h b.target * X) = X := fun X => by
      rw [← mul_assoc, inv_mul_self_of_mem_compact (hh _ htgt), one_mul]
    have hcons : ∀ U : BondAtLevel L m K n → ComplexMatrix2,
        pathHolonomy U (b :: Γ) = U b * pathHolonomy U Γ := fun U => by simp [pathHolonomy]
    rw [hcons, hcons, hrest]
    simp only [gaugeTransform, hsrc, mul_assoc, hcancel]
private theorem conj_plaquette_product {g g' u v A B C D : ComplexMatrix2}
    (hu : u⁻¹ * u = 1) (hv : v⁻¹ * v = 1)
    (hv' : v⁻¹⁻¹ = v) (hg : g'⁻¹ * g' = 1) (hg' : g'⁻¹⁻¹ = g') :
    (g * A * u⁻¹) * (u * B * v⁻¹) * (g' * C * v⁻¹)⁻¹ * (g * D * g'⁻¹)⁻¹ =
      g * (A * B * C⁻¹ * D⁻¹) * g⁻¹ := by
  have e₁ : ∀ X : ComplexMatrix2, u⁻¹ * (u * X) = X := fun X => by rw [← mul_assoc, hu, one_mul]
  have e₂ : ∀ X : ComplexMatrix2, v⁻¹ * (v * X) = X := fun X => by rw [← mul_assoc, hv, one_mul]
  have e₃ : ∀ X : ComplexMatrix2, g'⁻¹ * (g' * X) = X := fun X => by
    rw [← mul_assoc, hg, one_mul]
  simp only [Matrix.mul_inv_rev, hv', hg', mul_assoc, e₁, e₂, e₃]
abbrev _root_.YangMills.SharedProofs.p47100 := @conj_plaquette_product
private theorem isBondPathFromTo_forwardFlow {j : ℤ} (μ : Fin 4) (k : ℕ) (x : Site L m j) :
    IsBondPathFromTo (forwardAxisPath x μ k) x (x + (k : ℤ) • unitStep L m j μ) := by
  induction k generalizing x with
  | zero =>
    exact ⟨List.isChain_nil, fun _ => by simp, by simp [forwardAxisPath], by simp [forwardAxisPath]⟩
  | succ k ih =>
    have hend : x + ((k + 1 : ℕ) : ℤ) • unitStep L m j μ =
        x + unitStep L m j μ + (k : ℤ) • unitStep L m j μ := by
      rw [Nat.cast_succ, add_smul, one_smul]
      abel
    have hrest := ih (x + unitStep L m j μ)
    rw [hend]
    cases k with
    | zero =>
      simp only [forwardAxisPath]
      refine ⟨List.isChain_singleton _, by simp, by simp [Bond.forwardFrom], ?_⟩
      simp [Bond.forwardFrom]
    | succ k =>
      simp only [forwardAxisPath] at hrest ⊢
      refine ⟨?_, by simp, by simp [Bond.forwardFrom], ?_⟩
      · rw [IsBondPath, List.isChain_cons_cons]
        exact ⟨by simp [Bond.forwardFrom], hrest.1⟩
      · intro b hb
        refine hrest.2.2.2 b ?_
        simpa [List.getLast?_cons_cons] using hb
abbrev _root_.YangMills.SharedProofs.p4940 := @isBondPathFromTo_forwardFlow
private theorem corneredSchemeGaugeLaw_of_blockPaths (hpaths : BlockPaths.Statement)
    (hL : IsAdmissibleBlockingFactor L) (hm : 0 < m) (hn : n < K)
    (c : BondAtLevel L m K (n + 1)) (hc : c.IsPositivelyOriented)
    (h : SiteAtLevel L m K n → ComplexMatrix2) (W : BondAtLevel L m K n → ComplexMatrix2)
    (hh : ∀ x : SiteAtLevel L m K n, (x : FourTorus L m) ∈ bondDoubleBlock c →
      h x ∈ compactGaugeGroup) :
    CorneredSchemeGaugeLaw h W c := by
  obtain ⟨μ, hμ⟩ := hc
  obtain ⟨hy, hb⟩ := hpaths L m K hL.1 hL.2 hm n hn
  obtain ⟨hcoord, hmono, htrans, hstraight, hin⟩ := hb c μ hμ
  have hlaw := holonomyGaugeLaw_of_mem_compact c h W hh
  have hsub : ∀ y ∈ ({c.source, c.target} : Set (SiteAtLevel L m K (n + 1))),
      unitBlock y ⊆ bondDoubleBlock c := by
    intro y hy' z hz
    rcases hy' with rfl | rfl
    · exact Or.inl hz
    · exact Or.inr hz
  have hbase : ∀ y : SiteAtLevel L m K (n + 1),
      (schemeBaseSite .cornered (levelDepth K n) y : SiteAtLevel L m K n) ∈
        sitesInBlock (levelDepth K n) y :=
    fun y => (hy y).1.2.2
  have hcomb : ∀ y ∈ ({c.source, c.target} : Set (SiteAtLevel L m K (n + 1))),
      ∀ x ∈ sitesInBlock (levelDepth K n) y,
        IsBondPathFromTo (coordinateComb (schemeBaseSite .cornered (levelDepth K n) y) x)
            (schemeBaseSite .cornered (levelDepth K n) y) x ∧
          ∀ b ∈ coordinateComb (schemeBaseSite .cornered (levelDepth K n) y) x,
            b ∈ (bondsInDoubleBlock c : Set (BondAtLevel L m K n)) := by
    intro y hy' x hx
    refine ⟨?_, ?_⟩
    · have hxb : (x : FourTorus L m) ∈ unitBlock y := hx
      rw [← (hy y).1.1.2] at hxb
      obtain ⟨p, hp, hpx⟩ := hxb
      have hsite : offsetSite (y.toSublattice (levelDepth K n)) p = x := Subtype.ext hpx
      have := ((hy y).2.2 p hp).2
      rw [hsite] at this
      exact this.2.2.1
    · exact (hin.1 y (by simpa using hy') x hx).2
  have hcontour : ∀ y ∈ ({c.source, c.target} : Set (SiteAtLevel L m K (n + 1))),
      ∀ x ∈ sitesInBlock (levelDepth K n) y,
        contourHolonomy .cornered (gaugeTransform h W) y x =
          h (schemeBaseSite .cornered (levelDepth K n) y) *
            contourHolonomy .cornered W y x * (h x)⁻¹ := by
    intro y hy' x hx
    obtain ⟨hp, hbonds⟩ := hcomb y hy' x hx
    exact hlaw _ _ _ hp (hsub y hy' (hbase y)) hbonds
  have hcross : ∀ x ∈ sitesInBlock (levelDepth K n) c.source,
      IsBondPathFromTo (crossingPath c x) x (shiftAcross c x) ∧
        ∀ b ∈ crossingPath c x, b ∈ (bondsInDoubleBlock c : Set (BondAtLevel L m K n)) := by
    intro x hx
    refine ⟨?_, hin.2 x hx⟩
    rw [(hstraight.1 x hx).2.1, hcoord.2.2.2.2.1 x hx]
    exact isBondPathFromTo_forwardFlow μ L x
  have hsrc : c.source ∈ ({c.source, c.target} : Set (SiteAtLevel L m K (n + 1))) := Or.inl rfl
  have htgt : c.target ∈ ({c.source, c.target} : Set (SiteAtLevel L m K (n + 1))) := Or.inr rfl
  have hshift : ∀ x ∈ sitesInBlock (levelDepth K n) c.source,
      shiftAcross c x ∈ sitesInBlock (levelDepth K n) c.target := by
    intro x hx
    rw [hcoord.2.2.2.2.1 x hx, ← hcoord.2.2.2.1]
    exact ⟨x, hx, rfl⟩
  have hbase_shift : shiftAcross c (schemeBaseSite .cornered (levelDepth K n) c.source) =
      schemeBaseSite .cornered (levelDepth K n) c.target := by
    rw [hcoord.2.2.2.2.1 _ (hbase c.source)]
    exact hcoord.2.1.symm
  have haxial : axialPath (schemeBaseSite .cornered (levelDepth K n) c.source)
      (schemeBaseSite .cornered (levelDepth K n) c.target) =
        crossingPath c (schemeBaseSite .cornered (levelDepth K n) c.source) :=
    hstraight.2.2
  refine ⟨hlaw, hcomb, hcontour, ?_⟩
  intro x hx
  set g := h (schemeBaseSite .cornered (levelDepth K n) c.source) with hg
  set g' := h (schemeBaseSite .cornered (levelDepth K n) c.target) with hg'
  have hx' := hshift x hx
  have hg'G : g' ∈ compactGaugeGroup := hh _ (hsub _ htgt (hbase c.target))
  have hxG : h x ∈ compactGaugeGroup := hh _ (hsub _ hsrc hx)
  have hx'G : h (shiftAcross c x) ∈ compactGaugeGroup := hh _ (hsub _ htgt hx')
  have hcross₁ := hcross x hx
  have hcross₂ := hcross _ (hbase c.source)
  rw [hbase_shift] at hcross₂
  have ht : baseTransport .cornered (gaugeTransform h W) c =
      g * baseTransport .cornered W c * g'⁻¹ := by
    unfold baseTransport
    rw [haxial]
    exact hlaw _ _ _ hcross₂.1 (hsub _ hsrc (hbase c.source)) hcross₂.2
  have hb₁ : pathHolonomy (gaugeTransform h W) (crossingPath c x) =
      h x * pathHolonomy W (crossingPath c x) * (h (shiftAcross c x))⁻¹ :=
    hlaw _ _ _ hcross₁.1 (hsub _ hsrc hx) hcross₁.2
  unfold localDefect
  rw [hcontour _ hsrc x hx, hcontour _ htgt _ hx', hb₁, ht]
  exact conj_plaquette_product (inv_mul_self_of_mem_compact hxG)
    (inv_mul_self_of_mem_compact hx'G) (inv_inv_of_mem_compact hx'G)
    (inv_mul_self_of_mem_compact hg'G) (inv_inv_of_mem_compact hg'G)
theorem corneredSchemeGaugeLawAndConjugation
    (hconj : ComplexMatrix2.NormExpLogConjugation)
    (hpaths : BlockPaths.Statement) :
    CorneredSchemeGaugeLawAndConjugation := by
  obtain ⟨-, -, -, -, -, hexp, hlog, hunit⟩ := hconj
  refine ⟨?_, ?_, ?_⟩
  · intro L hL m K n hm hn c hc h W hh _
    exact corneredSchemeGaugeLaw_of_blockPaths hpaths hL hm hn c hc h W hh
  · intro g hg
    have hg' : IsUnit g := (Matrix.isUnit_iff_isUnit_det g).2 hg
    exact ⟨fun Z => hexp g Z hg', fun X hX hX' => hlog g X hg' hX hX'⟩
  · intro g hg X hX
    exact hunit g X hg hX
end YangMills.Construction.PeriodicLattice
