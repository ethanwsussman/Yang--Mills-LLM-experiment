import YangMills.Construction.ColdStepAtMirrorFrames.SitesOfABlock
import YangMills.Construction.ColdStepAtMirrorFrames.SumOfADecayOnATorus
import YangMills.Construction.RunningCouplingSlope.CoefficientOfALocalDensityProof
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages
namespace YangMills.Construction.ColdStepAtMirrorFrames.DecaySum
theorem summable_pow_natAbs (q : ℝ) (hq₀ : 0 ≤ q) (hq₁ : q < 1) :
    Summable fun a : ℤ => q ^ a.natAbs := by apply _root_.YangMills.Construction.RunningCouplingSlope.LocalDensityCoefficient.summable_pow_natAbs <;> assumption
theorem sum_zmod_le_tsum_int (q : ℝ) (hq₀ : 0 ≤ q) (hq₁ : q < 1) (n : ℕ) [NeZero n] (u : ZMod n) :
    ∑ c : ZMod n, q ^ ((c - u).valMinAbs).natAbs ≤ ∑' a : ℤ, q ^ a.natAbs := by
  classical
  have hshift : ∑ c : ZMod n, q ^ ((c - u).valMinAbs).natAbs =
      ∑ c : ZMod n, q ^ (c.valMinAbs).natAbs :=
    Equiv.sum_comp (Equiv.subRight u) fun c : ZMod n => q ^ (c.valMinAbs).natAbs
  have hinj : Function.Injective (ZMod.valMinAbs : ZMod n → ℤ) := fun a b hab => by
    have := congrArg (Int.cast : ℤ → ZMod n) hab
    simpa using this
  have himage : ∑ c : ZMod n, q ^ (c.valMinAbs).natAbs =
      ∑ a ∈ Finset.univ.image (ZMod.valMinAbs : ZMod n → ℤ), q ^ a.natAbs :=
    (Finset.sum_image (f := fun a : ℤ => q ^ a.natAbs) fun a _ b _ hab => hinj hab).symm
  rw [hshift, himage]
  exact (summable_pow_natAbs q hq₀ hq₁).sum_le_tsum _ fun a _ => pow_nonneg hq₀ _
theorem exp_neg_le_prod_pow (s : ℝ) (hs : 0 < s) (a : Fin 4 → ℕ) (d : ℕ) (ha : ∀ i, a i ≤ d) :
    Real.exp (-(s * d)) ≤ ∏ i, Real.exp (-(s / 4)) ^ a i := by
  have h₀ : 0 ≤ Real.exp (-(s / 4)) := (Real.exp_pos _).le
  have h₁ : Real.exp (-(s / 4)) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have hpow : Real.exp (-(s * d)) = Real.exp (-(s / 4)) ^ (4 * d) := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [hpow, Finset.prod_pow_eq_pow_sum]
  refine pow_le_pow_of_le_one h₀ h₁ ?_
  calc ∑ i, a i ≤ ∑ _i : Fin 4, d := Finset.sum_le_sum fun i _ => ha i
    _ = 4 * d := by simp
theorem sum_exp_cellSupDist_le (s : ℝ) (hs : 0 < s) (F : BlockFrame) (hpos : ∀ i, 0 < F.extent i)
    (z : F.Cell) :
    ∑ z' ∈ finiteCells F, Real.exp (-(s * (cellSupDist z' z : ℝ))) ≤
      (∑' a : ℤ, Real.exp (-(s / 4)) ^ a.natAbs) ^ 4 := by
  classical
  have hne : ∀ i, NeZero (F.period F.top i) := fun i => ⟨by
    have : F.period F.top i = F.extent i := by simp [BlockFrame.period]
    rw [this]
    exact (hpos i).ne'⟩
  have hq₀ : 0 ≤ Real.exp (-(s / 4)) := (Real.exp_pos _).le
  have hq₁ : Real.exp (-(s / 4)) < 1 :=
    (Real.exp_lt_exp.2 (by linarith : -(s / 4) < 0)).trans_eq Real.exp_zero
  letI : ∀ i, Fintype (ZMod (F.period F.top i)) := fun i => by
    have := hne i
    exact ZMod.fintype _
  have hfin : Finite F.Cell := Pi.finite
  have hcells : finiteCells F =
      Fintype.piFinset fun i => (Finset.univ : Finset (ZMod (F.period F.top i))) := by
    ext y
    simp only [Fintype.mem_piFinset, Finset.mem_univ, implies_true, iff_true]
    unfold finiteCells
    rw [dif_pos hfin]
    exact @Finset.mem_univ _ (Fintype.ofFinite _) y
  have hterm : ∀ y : F.Cell, Real.exp (-(s * (cellSupDist y z : ℝ))) ≤
      ∏ i, Real.exp (-(s / 4)) ^ (((y i - z i).valMinAbs).natAbs) := fun y => by
    refine exp_neg_le_prod_pow s hs _ (cellSupDist y z) fun i => ?_
    unfold cellSupDist
    exact Finset.le_sup (f := fun i => ((y i - z i).valMinAbs).natAbs) (Finset.mem_univ i)
  calc ∑ z' ∈ finiteCells F, Real.exp (-(s * (cellSupDist z' z : ℝ)))
      ≤ ∑ y ∈ finiteCells F, ∏ i, Real.exp (-(s / 4)) ^ (((y i - z i).valMinAbs).natAbs) :=
        Finset.sum_le_sum fun y _ => hterm y
    _ = ∏ i, ∑ c : ZMod (F.period F.top i),
          Real.exp (-(s / 4)) ^ (((c - z i).valMinAbs).natAbs) := by
        rw [hcells, Finset.prod_univ_sum]
    _ ≤ ∏ _i : Fin 4, ∑' a : ℤ, Real.exp (-(s / 4)) ^ a.natAbs := by
        refine Finset.prod_le_prod (fun i _ => Finset.sum_nonneg fun _ _ => pow_nonneg hq₀ _)
          fun i _ => ?_
        have := hne i
        exact sum_zmod_le_tsum_int _ hq₀ hq₁ _ (z i)
    _ = _ := by simp
theorem sum_chordBonds_le (hS : SiteDecomposition) (F : BlockFrame) (hodd : Odd F.blockSide)
    (hs : ∀ i, 2 ≤ F.extent i) (g : F.Cell → ℝ) (hg : ∀ z, 0 ≤ g z) :
    ∑ b : ↥(chordBonds (finiteCells F)), g (enclosingCell b.1.1) ≤
      ((centredCube F.blockSide).card * 4 : ℝ) * ∑ z ∈ finiteCells F, g z := by
  classical
  have hpos : ∀ i, 0 < F.extent i := fun i => by have := hs i; omega
  have hmem : ∀ z : F.Cell, z ∈ finiteCells F := by
    have hne : ∀ i, NeZero (F.period F.top i) := fun i => ⟨by
      have : F.period F.top i = F.extent i := by simp [BlockFrame.period]
      rw [this]
      exact (hpos i).ne'⟩
    have hfin : Finite F.Cell := by
      have : ∀ i, Finite (ZMod (F.period F.top i)) := fun i => by
        have := hne i
        exact inferInstance
      exact Pi.finite
    intro z
    unfold finiteCells
    rw [dif_pos hfin]
    exact @Finset.mem_univ _ (Fintype.ofFinite _) z
  have hsite := (hS F hodd hs).2.1
  let φ : F.Site F.depth × Fin 4 → F.Cell × (Fin 4 → ℤ) × Fin 4 :=
    fun b => (enclosingCell b.1, cellOffset b.1, b.2)
  have hinj : Set.InjOn φ (chordBonds (finiteCells F) : Set (F.Site F.depth × Fin 4)) := by
    intro b _ b' _ hbb
    have hcell : enclosingCell b.1 = enclosingCell b'.1 := congrArg Prod.fst hbb
    have hoff : cellOffset b.1 = cellOffset b'.1 := congrArg (fun p => p.2.1) hbb
    have hdir : b.2 = b'.2 := congrArg (fun p => p.2.2) hbb
    refine Prod.ext ?_ hdir
    rw [← (hsite b.1).1, ← (hsite b'.1).1, hcell, hoff]
  calc ∑ b : ↥(chordBonds (finiteCells F)), g (enclosingCell b.1.1)
      = ∑ b ∈ chordBonds (finiteCells F), g (enclosingCell b.1) :=
        Finset.sum_coe_sort (chordBonds (finiteCells F)) fun b => g (enclosingCell b.1)
    _ = ∑ p ∈ (chordBonds (finiteCells F)).image φ, g p.1 :=
        (Finset.sum_image (f := fun p : F.Cell × (Fin 4 → ℤ) × Fin 4 => g p.1) hinj).symm
    _ ≤ ∑ p ∈ finiteCells F ×ˢ (centredCube F.blockSide ×ˢ (Finset.univ : Finset (Fin 4))), g p.1 := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun p _ _ => hg p.1
        intro p hp
        obtain ⟨b, _, rfl⟩ := Finset.mem_image.1 hp
        exact Finset.mem_product.2 ⟨hmem _, Finset.mem_product.2
          ⟨(hsite b.1).2, Finset.mem_univ _⟩⟩
    _ = ((centredCube F.blockSide).card * 4 : ℝ) * ∑ z ∈ finiteCells F, g z := by
        rw [Finset.sum_product, Finset.mul_sum]
        refine Finset.sum_congr rfl fun z _ => ?_
        simp
theorem decaySumOnTorusStatement_holds (hS : SiteDecomposition) : decaySumOnTorusStatement := by
  intro L s hodd hs
  have hq₀ : 0 ≤ Real.exp (-(s / 4)) := (Real.exp_pos _).le
  have hA : 0 ≤ ∑' a : ℤ, Real.exp (-(s / 4)) ^ a.natAbs :=
    tsum_nonneg fun a => pow_nonneg hq₀ _
  refine ⟨((centredCube L).card * 4 + 1 : ℝ) * (∑' a : ℤ, Real.exp (-(s / 4)) ^ a.natAbs) ^ 4, ?_⟩
  intro F n hL hn hside z
  subst hL
  have hs₂ : ∀ i, 2 ≤ F.extent i := fun i => by rw [hside i]; exact hn
  have hpos : ∀ i, 0 < F.extent i := fun i => by have := hs₂ i; omega
  have hcells := sum_exp_cellSupDist_le s hs F hpos z
  have hA₄ : 0 ≤ (∑' a : ℤ, Real.exp (-(s / 4)) ^ a.natAbs) ^ 4 := pow_nonneg hA 4
  have hN : (0 : ℝ) ≤ (centredCube F.blockSide).card * 4 := by positivity
  constructor
  · have hbonds := sum_chordBonds_le hS F hodd hs₂
      (fun z' => Real.exp (-(s * (cellSupDist z' z : ℝ)))) fun _ => (Real.exp_pos _).le
    calc _ ≤ _ := hbonds
      _ ≤ ((centredCube F.blockSide).card * 4 : ℝ) *
            (∑' a : ℤ, Real.exp (-(s / 4)) ^ a.natAbs) ^ 4 :=
        mul_le_mul_of_nonneg_left hcells hN
      _ ≤ _ := by nlinarith
  · calc _ ≤ _ := hcells
      _ ≤ _ := by nlinarith
end YangMills.Construction.ColdStepAtMirrorFrames.DecaySum
end
