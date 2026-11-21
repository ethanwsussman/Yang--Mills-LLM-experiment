import YangMills.Construction.ChessboardTori.ArithmeticOfMirrorGrids
import YangMills.Construction.ChessboardTori.GroupOfAGridAndCopies
import YangMills.Construction.ChessboardTori.TranslationsOfPeriodicGibbsStatesInTheGroupOfAGrid
import Mathlib
set_option autoImplicit false
open Set MeasureTheory
noncomputable section
namespace YangMills.Construction.ChessboardTori
open InfiniteLattice (AmbientSpace)
namespace PeriodicStatesAndGridTranslations
variable {D : ChessboardSetup}
theorem cell_injective (g : ReflectionGrid D) : Function.Injective g.cell := by apply _root_.YangMills.Construction.ChessboardTori.ReflectionGrid.cell_injective <;> assumption
theorem translate_image_baseCell (g : ReflectionGrid D) (k : Fin 4 → ℤ) :
    translate (g.cellOffsetVector k) '' g.baseCell = g.cell k := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [g.baseCell_eq] at hy
    intro i
    have hyi := hy i
    have heq : translate (g.cellOffsetVector k) y i - (g.origin i + g.cellSide * k i) =
        y i - g.origin i := by
      simp only [translate, ReflectionGrid.cellOffsetVector, Pi.add_apply]
      ring
    rw [heq]
    exact hyi
  · intro hx
    refine ⟨x - g.cellOffsetVector k, ?_, ?_⟩
    · rw [g.baseCell_eq]
      intro i
      have hxi := hx i
      have heq : (x - g.cellOffsetVector k) i - g.origin i =
          x i - (g.origin i + g.cellSide * k i) := by
        simp only [ReflectionGrid.cellOffsetVector, Pi.sub_apply]
        ring
      show (x - g.cellOffsetVector k) i - g.origin i ∈ Icc 0 g.cellSide
      rw [heq]
      exact hxi
    · simp [translate]
theorem exists_count_even_multiples (n : ℤ) (hn : 1 ≤ n) (q : ℕ) (hq : q ≠ 0) :
    ∃ c : ℕ, (∀ i : ℕ, i < c → 2 * (q : ℤ) * i ≤ n - 1) ∧ n ≤ 2 * (q : ℤ) * c := by
  have htwoq : 0 < 2 * (q : ℤ) := by omega
  refine ⟨((n - 1) / (2 * (q : ℤ))).toNat + 1, fun i hi => ?_, ?_⟩
  · have hnonneg : 0 ≤ (n - 1) / (2 * (q : ℤ)) := Int.ediv_nonneg (by omega) htwoq.le
    have hile : (i : ℤ) ≤ (n - 1) / (2 * (q : ℤ)) := by omega
    calc 2 * (q : ℤ) * i ≤ 2 * (q : ℤ) * ((n - 1) / (2 * (q : ℤ))) :=
          mul_le_mul_of_nonneg_left hile htwoq.le
      _ ≤ n - 1 := Int.mul_ediv_self_le htwoq.ne'
  · have hnonneg : 0 ≤ (n - 1) / (2 * (q : ℤ)) := Int.ediv_nonneg (by omega) htwoq.le
    have hcast : (((n - 1) / (2 * (q : ℤ))).toNat : ℤ) = (n - 1) / (2 * (q : ℤ)) :=
      Int.toNat_of_nonneg hnonneg
    have hlt := Int.lt_mul_ediv_self_add (x := n - 1) htwoq
    push_cast
    rw [hcast]
    nlinarith
end PeriodicStatesAndGridTranslations
open PeriodicStatesAndGridTranslations in
theorem PeriodicStatesAndGridTranslations.holds
    (hGroup : ReflectionGroupAndTransport.Statement) (hArith : ReflectionGridArithmetic.Statement) :
    PeriodicStatesAndGridTranslations.Statement := by
  intro D ν hν
  refine ⟨hν.2, ?_⟩
  intro Γ q hfin hq hinv g hg
  obtain ⟨-, hUnique, hSign, -⟩ := hGroup D g hg
  have hqne : q ≠ 0 := hq ▸ hfin.index_ne_zero
  have hmul : ∀ v : InfiniteLattice.LatticePoint D.mesh, q • v ∈ Γ := by
    intro v
    have : Finite (InfiniteLattice.LatticePoint D.mesh ⧸ Γ) :=
      AddSubgroup.finite_quotient_of_finiteIndex
    have hz := card_nsmul_eq_zero' (G := InfiniteLattice.LatticePoint D.mesh ⧸ Γ)
      (x := (v : InfiniteLattice.LatticePoint D.mesh ⧸ Γ))
    have hcard : Nat.card (InfiniteLattice.LatticePoint D.mesh ⧸ Γ) = q := hq
    rw [hcard, ← QuotientAddGroup.mk_nsmul] at hz
    exact (QuotientAddGroup.eq_zero_iff _).mp hz
  refine ⟨⟨hmul, fun v => hinv _ (hmul v)⟩, ?_, ?_, ?_⟩
  · intro k hk
    have heven : ∀ i, ∃ t : ℤ, k i = 2 * t := fun i => by
      obtain ⟨s, hs⟩ := hk i
      exact ⟨q * s, by rw [hs]; ring⟩
    choose t ht using heven
    obtain ⟨r, hr, hrt, hrs⟩ := hSign.2.2 t
    have hvec : (fun i => 2 * g.cellSide * t i) = g.cellOffsetVector k := by
      funext i
      simp only [ReflectionGrid.cellOffsetVector, ht i]
      push_cast
      ring
    rw [hvec] at hrt
    refine ⟨⟨r, hr⟩, hrt, hrs, fun r' => ?_⟩
    have hcarry : (⟨r, hr⟩ : g.reflectionGroup).1 '' g.baseCell = g.cell k := by
      show (r : AmbientSpace → AmbientSpace) '' g.baseCell = g.cell k
      rw [hrt]
      exact translate_image_baseCell g k
    obtain ⟨r₀, -, huniq⟩ := hUnique g.baseCell ⟨0, rfl⟩ (g.cell k) ⟨k, rfl⟩
    constructor
    · intro h
      rw [huniq r' h, huniq ⟨r, hr⟩ hcarry]
    · rintro rfl
      exact hcarry
  · intro k hk
    have hmem : g.cellOffsetPoint k ∈ Γ := by
      choose s hs using hk
      have heq : g.cellOffsetPoint k = q • g.cellOffsetPoint (fun i => 2 * s i) := by
        apply Subtype.ext
        funext i
        simp only [ReflectionGrid.cellOffsetPoint, ReflectionGrid.cellOffsetVector,
          AddSubgroup.coe_nsmul, Pi.smul_apply, hs i, nsmul_eq_mul]
        push_cast
        ring
      rw [heq]
      exact hmul _
    exact ⟨hmem, hinv _ hmem⟩
  · intro m' hm'
    set g' := g.withExponent m' with hg'
    obtain ⟨-, -, -, hgrid⟩ := hArith (D.withExponent m')
    obtain ⟨hTorus, hBlock⟩ := (hgrid g').2 hm'
    obtain ⟨-, hacross, -, hn2, -⟩ := hTorus
    obtain ⟨-, hcells, hcard⟩ := hBlock 0
    set n := g'.cellsPerTorusSide with hn
    have hsub : g'.sparseCells q ⊆ g'.cell '' g'.blockIndices 0 := by
      rintro _ ⟨k, ⟨hk, -⟩, rfl⟩
      refine ⟨k, fun i => ?_, rfl⟩
      have hreal : (k i : ℝ) ≤ (n : ℝ) - 1 := by
        have := (hk i).2
        rwa [hacross] at this
      have hint : k i ≤ n - 1 := by exact_mod_cast hreal
      show (0 : Fin 4 → ℤ) i ≤ k i ∧ k i ≤ (0 : Fin 4 → ℤ) i + n - 1
      simp only [Pi.zero_apply, zero_add]
      exact ⟨(hk i).1, hint⟩
    have hpos : (g'.cell '' g'.blockIndices 0).ncard ≠ 0 := by
      intro h0
      rw [h0] at hcard
      have : 0 < n ^ 4 := by positivity
      omega
    have hfinite : (g'.cell '' g'.blockIndices 0).Finite := finite_of_ncard_ne_zero hpos
    have hsparse : (g'.sparseCells q).Finite := hfinite.subset hsub
    refine ⟨?_, hsparse, ?_⟩
    · have : g'.cellsWithin g'.fundamentalBlock = g'.cell '' g'.blockIndices 0 := hcells
      rw [this]
      exact hsub
    · obtain ⟨c, hc1, hc2⟩ := exists_count_even_multiples n (by omega) q hqne
      let f : (Fin 4 → Fin c) → Set AmbientSpace :=
        fun u => g'.cell fun i => 2 * (q : ℤ) * (u i : ℕ)
      have hf : Function.Injective f := by
        intro u v huv
        have h := cell_injective g' huv
        funext i
        have hi := congrFun h i
        have hne : (2 * (q : ℤ)) ≠ 0 := by omega
        have hnat : ((u i : ℕ) : ℤ) = ((v i : ℕ) : ℤ) := mul_left_cancel₀ hne hi
        exact Fin.ext (by exact_mod_cast hnat)
      have hrange : range f ⊆ g'.sparseCells q := by
        rintro _ ⟨u, rfl⟩
        refine ⟨fun i => 2 * (q : ℤ) * (u i : ℕ), ⟨fun i => ⟨by positivity, ?_⟩, fun i => ?_⟩, rfl⟩
        · rw [hacross]
          exact_mod_cast hc1 _ (u i).2
        · exact Dvd.intro _ rfl
      have hle : (range f).ncard ≤ (g'.sparseCells q).ncard := ncard_le_ncard hrange hsparse
      have hcount : (range f).ncard = c ^ 4 := by
        rw [← image_univ, ncard_image_of_injective _ hf, ncard_univ]
        simp
      rw [hcount] at hle
      have htwoq : (0 : ℝ) < 2 * (q : ℝ) := by
        have : 0 < q := Nat.pos_of_ne_zero hqne
        positivity
      have hratio : g'.cellsAcross / (2 * q) ≤ c := by
        rw [hacross, div_le_iff₀ htwoq]
        have : (n : ℝ) ≤ 2 * (q : ℝ) * c := by exact_mod_cast hc2
        linarith
      have hnn : 0 ≤ g'.cellsAcross / (2 * (q : ℝ)) := by
        rw [hacross]
        have : (0 : ℝ) ≤ n := by exact_mod_cast (by omega : 0 ≤ n)
        positivity
      calc (g'.cellsAcross / (2 * q)) ^ 4 ≤ (c : ℝ) ^ 4 := pow_le_pow_left₀ hnn hratio 4
        _ ≤ ((g'.sparseCells q).ncard : ℝ) := by exact_mod_cast hle
end YangMills.Construction.ChessboardTori
end
