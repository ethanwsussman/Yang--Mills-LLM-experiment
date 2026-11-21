import YangMills.Construction.Lattice.BondsPathsAndAveragesOfADoubleBlock
import YangMills.Construction.Lattice.DoubleBlockContours
import YangMills.Construction.Lattice.LayerBondsCoarseSpacesAndAverages
import YangMills.Construction.Lattice.LengthsOfThePathsOfADoubleBlock
import YangMills.Construction.Lattice.PathsOfBlocksAndDoubleBlocks
import Mathlib
open Set
open scoped Matrix.Norms.L2Operator
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicLattice
namespace PathLengthBounds
variable {L m : ℕ} {j j' : ℤ}
theorem length_pathOfWord (z : Site L m j') (w : StepWord L m j') :
    (pathOfWord z w).length = w.length := by
  induction w generalizing z with
  | nil => rfl
  | cons s w ih => simp [pathOfWord, ih]
theorem norm_bondFormSumAlong_le {A : Bond L m j' → Matrices.ComplexMatrix2} {T : ℝ}
    (hA : ∀ b, ‖A b‖ ≤ T) (γ : List (Bond L m j')) :
    ‖bondFormSumAlong A γ‖ ≤ (γ.length : ℝ) * T := by
  induction γ with
  | nil => simp [bondFormSumAlong]
  | cons b γ ih =>
    have hcons : bondFormSumAlong A (b :: γ) = A b + bondFormSumAlong A γ := by
      simp [bondFormSumAlong]
    rw [hcons, List.length_cons]
    push_cast
    calc ‖A b + bondFormSumAlong A γ‖ ≤ ‖A b‖ + ‖bondFormSumAlong A γ‖ := norm_add_le _ _
      _ ≤ T + (γ.length : ℝ) * T := add_le_add (hA b) ih
      _ = ((γ.length : ℝ) + 1) * T := by ring
theorem norm_contourFormAverage_le {A : Bond L m j' → Matrices.ComplexMatrix2} {C : ℝ}
    (hC : 0 ≤ C) (y : Site L m j) (x : Site L m j')
    (h : ∀ σ : AxisOrdering y x, ‖bondFormSumAlong A (orderedContour y x σ)‖ ≤ C) :
    ‖contourFormAverage A y x‖ ≤ C := by
  unfold contourFormAverage
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hsum : ‖∑ σ : AxisOrdering y x, bondFormSumAlong A (orderedContour y x σ)‖ ≤
      (Fintype.card (AxisOrdering y x) : ℝ) * C := by
    calc ‖∑ σ : AxisOrdering y x, bondFormSumAlong A (orderedContour y x σ)‖
        ≤ ∑ σ : AxisOrdering y x, ‖bondFormSumAlong A (orderedContour y x σ)‖ :=
          norm_sum_le _ _
      _ ≤ ∑ _σ : AxisOrdering y x, C := Finset.sum_le_sum fun σ _ => h σ
      _ = (Fintype.card (AxisOrdering y x) : ℝ) * C := by
        simp [Finset.sum_const, nsmul_eq_mul]
  rcases Nat.eq_zero_or_pos (Fintype.card (AxisOrdering y x)) with h0 | hpos
  · simpa [h0] using hC
  · have hn : (0 : ℝ) < (Fintype.card (AxisOrdering y x) : ℝ) := by exact_mod_cast hpos
    calc ((Fintype.card (AxisOrdering y x) : ℝ))⁻¹ *
          ‖∑ σ : AxisOrdering y x, bondFormSumAlong A (orderedContour y x σ)‖
        ≤ ((Fintype.card (AxisOrdering y x) : ℝ))⁻¹ *
          ((Fintype.card (AxisOrdering y x) : ℝ) * C) :=
          mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = C := by field_simp
theorem norm_extendAntisymm_le {K k : ℕ} (hpos : 0 < L)
    (a : ChartIndex L m K k → Matrices.ComplexMatrix2) (b : BondAtLevel L m K k) :
    ‖extendAntisymm a b‖ ≤ Matrices.GroupLieProduct.supNorm a := by
  have hsite : Finite (SiteAtLevel L m K k) :=
    SeparatedSequences.BaseParameters.site_finite hpos _ _
  have hbond : Finite (BondAtLevel L m K k) :=
    Finite.of_injective (fun b : BondAtLevel L m K k => (b.source, b.target)) fun b b' hb =>
      Bond.ext (congrArg Prod.fst hb) (congrArg Prod.snd hb)
  have hbdd : BddAbove (range fun i : ChartIndex L m K k =>
      Matrices.ComplexMatrix2.operatorNorm (a i)) :=
    (finite_range _).bddAbove
  have hle : ∀ i : ChartIndex L m K k, ‖a i‖ ≤ Matrices.GroupLieProduct.supNorm a :=
    fun i => le_ciSup hbdd i
  have h0 : 0 ≤ Matrices.GroupLieProduct.supNorm a := Real.iSup_nonneg fun _ => norm_nonneg _
  unfold extendAntisymm
  split_ifs with h h'
  · exact hle _
  · rw [norm_neg]
    exact hle _
  · simpa using h0
end PathLengthBounds
open PathLengthBounds in
theorem doubleBlockPathLengths_holds
    (hContours : DoubleBlock.DoubleBlockContoursStatement)
    (hPaths : BlockPaths.Statement)
    (hDouble : DoubleBlockStructure.Statement) :
    DoubleBlockPathLengths := by
  intro L m K k hL hm hk
  have hodd : Odd L := hL.1
  have h13 : 13 ≤ L := hL.2
  have hpos : 0 < L := by omega
  have hcontour : ∀ (y : SiteAtLevel L m K (k + 1)) (x : SiteAtLevel L m K k),
      x ∈ sitesInBlock (levelDepth K k) y → ∀ σ : AxisOrdering y x,
        (orderedContour y x σ).length ≤ 2 * (L - 1) := by
    intro y x hx σ
    obtain ⟨-, hsite⟩ := (hContours L m K hodd h13 hm k hk (Bond.forwardFrom y 0)).1 y (Or.inl rfl)
    obtain ⟨⟨n, hn⟩, hall⟩ := hsite x hx
    obtain ⟨hsum, hpath, -⟩ := hall n hn
    obtain ⟨w, hlen, hst⟩ := hpath _ ⟨σ, rfl⟩
    rw [← hst, length_pathOfWord, hlen]
    have hcast : ((∑ μ, (n μ).natAbs : ℕ) : ℤ) = ∑ μ, |n μ| := by
      push_cast
      exact Finset.sum_congr rfl fun μ _ => rfl
    have hz : ((∑ μ, (n μ).natAbs : ℕ) : ℤ) ≤ 2 * ((L : ℤ) - 1) := by rw [hcast]; exact hsum
    omega
  have hcross : ∀ c : BondAtLevel L m K (k + 1), ∀ x ∈ sitesInBlock (levelDepth K k) c.source,
      (shiftAcross c x : FourTorus L m) ∈ unitBlock c.target ∧
        (crossingPath c x : List (BondAtLevel L m K k)).length = L := by
    intro c x hx
    have h := (hDouble L m K k hL hm hk c).2.2.1.1 x hx
    exact ⟨h.1, h.2.2.1⟩
  refine ⟨hcontour, fun c x hx => (hcross c x hx).2, ?_⟩
  intro a _ c
  have hT0 : 0 ≤ Matrices.GroupLieProduct.supNorm a := Real.iSup_nonneg fun _ => norm_nonneg _
  have hA := norm_extendAntisymm_le (m := m) (K := K) (k := k) hpos a
  have hL1 : (13 : ℝ) ≤ (L : ℝ) := by exact_mod_cast h13
  have hlenR : ∀ (y : SiteAtLevel L m K (k + 1)) (x : SiteAtLevel L m K k),
      x ∈ sitesInBlock (levelDepth K k) y →
        ‖contourFormAverage (extendAntisymm a) y x‖ ≤
          2 * ((L : ℝ) - 1) * Matrices.GroupLieProduct.supNorm a := by
    intro y x hx
    refine norm_contourFormAverage_le (mul_nonneg (by linarith) hT0) y x fun σ => ?_
    refine (norm_bondFormSumAlong_le hA _).trans (mul_le_mul_of_nonneg_right ?_ hT0)
    have h := hcontour y x hx σ
    have h' : (((orderedContour y x σ).length : ℕ) : ℝ) ≤ ((2 * (L - 1) : ℕ) : ℝ) := by
      exact_mod_cast h
    rw [Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ L)] at h'
    simpa using h'
  have hterm : ∀ x ∈ sitesInBlock (levelDepth K k) c.source,
      ‖contourFormAverage (extendAntisymm a) c.source x +
            bondFormSumAlong (extendAntisymm a) (crossingPath c x) -
          contourFormAverage (extendAntisymm a) c.target (shiftAcross c x)‖ ≤
        (5 * (L : ℝ) - 4) * Matrices.GroupLieProduct.supNorm a := by
    intro x hx
    obtain ⟨hx', hlen⟩ := hcross c x hx
    have h1 := hlenR c.source x hx
    have h2 := norm_bondFormSumAlong_le hA (crossingPath c x : List (BondAtLevel L m K k))
    have h3 := hlenR c.target (shiftAcross c x) hx'
    rw [hlen] at h2
    calc _ ≤ ‖contourFormAverage (extendAntisymm a) c.source x +
              bondFormSumAlong (extendAntisymm a) (crossingPath c x)‖ +
            ‖contourFormAverage (extendAntisymm a) c.target (shiftAcross c x)‖ :=
          norm_sub_le _ _
      _ ≤ ‖contourFormAverage (extendAntisymm a) c.source x‖ +
              ‖bondFormSumAlong (extendAntisymm a) (crossingPath c x)‖ +
            ‖contourFormAverage (extendAntisymm a) c.target (shiftAcross c x)‖ := by
          gcongr
          exact norm_add_le _ _
      _ ≤ _ := by linarith
  obtain ⟨⟨hco, hcard, -⟩, -⟩ := (hPaths L m K hodd h13 hm k hk).1 c.source
  have hsite : Finite (SiteAtLevel L m K k) :=
    SeparatedSequences.BaseParameters.site_finite hpos _ _
  have hfin : (sitesInBlock (levelDepth K k) c.source : Set (SiteAtLevel L m K k)).Finite :=
    Set.toFinite _
  have himage : (Subtype.val '' (sitesInBlock (levelDepth K k) c.source :
      Set (SiteAtLevel L m K k)) : Set (FourTorus L m)) = unitBlock c.source := by
    ext p
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro hp
      have hp' := hp
      rw [← hco.2] at hp'
      obtain ⟨q, -, hq⟩ := hp'
      refine ⟨offsetSite (c.source.toSublattice (levelDepth K k)) q, ?_, hq⟩
      show ((offsetSite (c.source.toSublattice (levelDepth K k)) q : SiteAtLevel L m K k) :
        FourTorus L m) ∈ unitBlock c.source
      have hq' : ((offsetSite (c.source.toSublattice (levelDepth K k)) q :
          SiteAtLevel L m K k) : FourTorus L m) = p := hq
      rw [hq']
      exact hp
  have hcount : (sitesInBlock (levelDepth K k) c.source : Set (SiteAtLevel L m K k)).ncard =
      L ^ 4 := by
    rw [← hcard, ← himage, Set.ncard_image_of_injective _ Subtype.val_injective]
  have hsum : ‖linearBlockSum (extendAntisymm a) c‖ ≤
      (L : ℝ) ^ 4 * ((5 * (L : ℝ) - 4) * Matrices.GroupLieProduct.supNorm a) := by
    unfold linearBlockSum
    rw [finsum_mem_eq_finite_toFinset_sum _ hfin]
    refine (norm_sum_le _ _).trans ?_
    refine (Finset.sum_le_sum fun x hx => hterm x (hfin.mem_toFinset.1 hx)).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul, ← Set.ncard_eq_toFinset_card _ hfin, hcount]
    push_cast
    exact le_rfl
  have hLpos : (0 : ℝ) < (L : ℝ) := by linarith
  have hzpow : (L : ℝ) ^ (-5 : ℤ) * (L : ℝ) ^ 4 = (L : ℝ)⁻¹ := by
    have : (L : ℝ) ^ (-5 : ℤ) = ((L : ℝ) ^ 5)⁻¹ := by
      rw [zpow_neg]
      norm_cast
    rw [this]
    field_simp
  constructor
  · unfold linearBlockAverage
    show ‖(((L : ℝ) ^ (-5 : ℤ) : ℝ) : ℂ) • linearBlockSum (extendAntisymm a) c‖ ≤ _
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc (L : ℝ) ^ (-5 : ℤ) * ‖linearBlockSum (extendAntisymm a) c‖
        ≤ (L : ℝ) ^ (-5 : ℤ) *
            ((L : ℝ) ^ 4 * ((5 * (L : ℝ) - 4) * Matrices.GroupLieProduct.supNorm a)) :=
          mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = _ := by ring
  · rw [hzpow]
    have hfrac : (L : ℝ)⁻¹ * (5 * (L : ℝ) - 4) ≤ 5 := by
      rw [inv_mul_le_iff₀ hLpos]
      linarith
    calc (L : ℝ)⁻¹ * (5 * (L : ℝ) - 4) * Matrices.GroupLieProduct.supNorm a
        ≤ 5 * Matrices.GroupLieProduct.supNorm a := mul_le_mul_of_nonneg_right hfrac hT0
end YangMills.Construction.PeriodicLattice
end
