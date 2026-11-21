import YangMills.Construction.HessianOfTheMainTerm.SumsOverTheSitesOfATorus
import YangMills.Construction.Lattice.CombGaugeOfABoxProof
import Mathlib
set_option autoImplicit false
open YangMills.Construction.PeriodicLattice
noncomputable section
namespace YangMills.Construction.HessianOfTheMainTerm
theorem coord_sum_zsmul_unitStep (L m : ℕ) (j : ℤ) (r : Fin 4 → ℤ) (ν : Fin 4) :
    ((∑ μ, r μ • unitStep L m j μ : Site L m j) : FourTorus L m) ν =
      (((r ν : ℝ) * meshSize L j : ℝ) : AddCircle (torusSide L m)) := by apply _root_.YangMills.Construction.PeriodicLattice.CombGaugeOnBox.coe_sum_zsmul_unitStep <;> assumption
theorem SiteSums.ballDoublingAndWeightBound_of_siteLengthFacts (hLen : SiteLengthFacts) :
    SiteSums.BallDoublingAndWeightBound := by
  refine ⟨?_, ?_⟩
  · intro L m j _ ℓ hL hmj hℓ hℓN _ _
    obtain ⟨-, -, -, -, -, -, -, -, -, hrep⟩ := hLen L m j hL hmj
    choose n hn hn' using hrep
    have hLpos : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
    have hmesh : 0 < meshSize L j := by unfold meshSize; exact zpow_pos hLpos _
    have hinj : Function.Injective n := by
      intro u v huv
      apply Subtype.ext
      funext μ
      rw [hn u μ, hn v μ, huv]
    have hupper : ((Finset.univ.filter fun u : Site L m j => supLengthInMesh u < (ℓ : ℝ)).card : ℝ) ≤
        (2 * (ℓ : ℝ)) ^ 4 := by
      set cube : Finset (Fin 4 → ℤ) :=
        Fintype.piFinset fun _ => Finset.Icc (-((ℓ : ℤ) - 1)) ((ℓ : ℤ) - 1) with hcube
      have hmaps : ∀ u ∈ (Finset.univ.filter fun u : Site L m j => supLengthInMesh u < (ℓ : ℝ)),
          n u ∈ cube := by
        intro u hu
        have hlt := (Finset.mem_filter.mp hu).2
        rw [hcube, Fintype.mem_piFinset]
        intro μ
        have h1 : |(n u μ : ℝ)| < ℓ := by
          refine lt_of_le_of_lt ?_ hlt
          rw [hn' u]
          exact Finset.le_sup' (fun μ => |(n u μ : ℝ)|) (Finset.mem_univ μ)
        have h2 : |n u μ| < (ℓ : ℤ) := by exact_mod_cast h1
        rw [abs_lt] at h2
        rw [Finset.mem_Icc]
        omega
      have hcard := Finset.card_le_card_of_injOn n hmaps (fun a _ b _ h => hinj h)
      have hcc : cube.card = (2 * ℓ - 1) ^ 4 := by
        rw [hcube, Fintype.card_piFinset]
        simp only [Int.card_Icc, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        congr 1
        omega
      rw [hcc] at hcard
      have h3 : ((2 * ℓ - 1 : ℕ) : ℝ) ≤ 2 * ℓ := by
        have : 2 * ℓ - 1 ≤ 2 * ℓ := by omega
        exact_mod_cast this
      calc ((Finset.univ.filter fun u : Site L m j => supLengthInMesh u < (ℓ : ℝ)).card : ℝ)
          ≤ (((2 * ℓ - 1) ^ 4 : ℕ) : ℝ) := by exact_mod_cast hcard
        _ = ((2 * ℓ - 1 : ℕ) : ℝ) ^ 4 := by push_cast; rfl
        _ ≤ (2 * (ℓ : ℝ)) ^ 4 := pow_le_pow_left₀ (by positivity) h3 4
    have hlower : (ℓ : ℝ) ^ 4 ≤
        ((Finset.univ.filter fun u : Site L m j => supLengthInMesh u ≤ (ℓ : ℝ) / 2).card : ℝ) := by
      set t : ℕ := ℓ / 2 with ht
      set cube : Finset (Fin 4 → ℤ) :=
        Fintype.piFinset fun _ => Finset.Icc (-(t : ℤ)) (t : ℤ) with hcube
      have hcc : cube.card = (2 * t + 1) ^ 4 := by
        rw [hcube, Fintype.card_piFinset]
        simp only [Int.card_Icc, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        congr 1
        omega
      have hmem : ∀ r ∈ cube, ∀ ν, |r ν| ≤ (t : ℤ) := by
        intro r hr ν
        rw [hcube, Fintype.mem_piFinset] at hr
        have := Finset.mem_Icc.mp (hr ν)
        exact abs_le.mpr this
      have hmaps : ∀ r ∈ cube, (∑ μ, r μ • unitStep L m j μ : Site L m j) ∈
          (Finset.univ.filter fun u : Site L m j => supLengthInMesh u ≤ (ℓ : ℝ) / 2) := by
        intro r hr
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
        have hlift : TorusMetric.torusSupNorm
            ((∑ μ, r μ • unitStep L m j μ : Site L m j) : FourTorus L m) ≤
            TorusMetric.supNormVec fun ν => (r ν : ℝ) * meshSize L j := by
          refine csInf_le ⟨0, ?_⟩ ⟨fun ν => (r ν : ℝ) * meshSize L j, ?_, rfl⟩
          · rintro _ ⟨v, -, rfl⟩
            exact le_trans (abs_nonneg (v 0))
              (Finset.le_sup' (fun μ => |v μ|) (Finset.mem_univ 0))
          · funext ν
            exact (coord_sum_zsmul_unitStep L m j r ν).symm
        have hsup : TorusMetric.supNormVec (fun ν => (r ν : ℝ) * meshSize L j) ≤
            (t : ℝ) * meshSize L j := by
          refine Finset.sup'_le _ _ fun ν _ => ?_
          rw [abs_mul, abs_of_pos hmesh]
          refine mul_le_mul_of_nonneg_right ?_ hmesh.le
          have := hmem r hr ν
          exact_mod_cast this
        rw [supLengthInMesh, div_le_iff₀ hmesh]
        refine hlift.trans (hsup.trans ?_)
        refine mul_le_mul_of_nonneg_right ?_ hmesh.le
        have h2 : 2 * t ≤ ℓ := by omega
        have h3 : (2 : ℝ) * t ≤ ℓ := by exact_mod_cast h2
        linarith
      have hinj2 : Set.InjOn (fun r : Fin 4 → ℤ => (∑ μ, r μ • unitStep L m j μ : Site L m j))
          (cube : Set (Fin 4 → ℤ)) := by
        intro r hr r' hr' hrr
        funext ν
        have hc : (((r ν : ℝ) * meshSize L j : ℝ) : AddCircle (torusSide L m)) =
            (((r' ν : ℝ) * meshSize L j : ℝ) : AddCircle (torusSide L m)) := by
          rw [← coord_sum_zsmul_unitStep, ← coord_sum_zsmul_unitStep]
          exact congrArg (fun s : Site L m j => (s : FourTorus L m) ν) hrr
        have h0 : ((((r ν : ℝ) - (r' ν : ℝ)) * meshSize L j : ℝ) : AddCircle (torusSide L m)) = 0 := by
          rw [sub_mul, AddCircle.coe_sub, hc, sub_self]
        obtain ⟨q, hq⟩ := (AddCircle.coe_eq_zero_iff _).mp h0
        have hN : (sitesPerSide L m j : ℝ) * meshSize L j = torusSide L m := by
          have e1 : (((m : ℤ) + j).toNat : ℤ) = (m : ℤ) + j := Int.toNat_of_nonneg hmj
          have e2 : (L : ℝ) ^ (((m : ℤ) + j).toNat) = (L : ℝ) ^ ((m : ℤ) + j) := by
            rw [← zpow_natCast, e1]
          simp only [sitesPerSide, torusSide, meshSize]
          push_cast
          rw [e2, mul_assoc, ← zpow_add₀ hLpos.ne']
          simp
        have h1 : (q : ℝ) * (sitesPerSide L m j : ℝ) = (r ν : ℝ) - (r' ν : ℝ) := by
          have : (q : ℝ) * torusSide L m = ((r ν : ℝ) - (r' ν : ℝ)) * meshSize L j := by
            simpa using hq
          rw [← hN, ← mul_assoc] at this
          exact mul_right_cancel₀ hmesh.ne' this
        have h2 : q * (sitesPerSide L m j : ℤ) = r ν - r' ν := by exact_mod_cast h1
        have hr1 := hmem r hr ν
        have hr2 := hmem r' hr' ν
        have hbound : |r ν - r' ν| < (sitesPerSide L m j : ℤ) := by
          have h3 : (2 * t : ℤ) ≤ ℓ := by
            have : 2 * t ≤ ℓ := by omega
            exact_mod_cast this
          have h4 : (ℓ : ℤ) < (sitesPerSide L m j : ℤ) := by exact_mod_cast hℓN
          have h5 := abs_sub (r ν) (r' ν)
          omega
        have hq0 : q = 0 := by
          by_contra hne
          have h6 : (sitesPerSide L m j : ℤ) ≤ |q * (sitesPerSide L m j : ℤ)| := by
            rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℤ) ≤ (sitesPerSide L m j : ℤ))]
            have : 1 ≤ |q| := Int.one_le_abs hne
            nlinarith [this, (by positivity : (0 : ℤ) ≤ (sitesPerSide L m j : ℤ))]
          rw [h2] at h6
          omega
        rw [hq0] at h2
        simp at h2
        omega
      have hcard := Finset.card_le_card_of_injOn _ hmaps hinj2
      rw [hcc] at hcard
      have h7 : ℓ ≤ 2 * t + 1 := by omega
      have h8 : (ℓ : ℝ) ≤ ((2 * t + 1 : ℕ) : ℝ) := by exact_mod_cast h7
      calc (ℓ : ℝ) ^ 4 ≤ ((2 * t + 1 : ℕ) : ℝ) ^ 4 := pow_le_pow_left₀ (by positivity) h8 4
        _ = (((2 * t + 1) ^ 4 : ℕ) : ℝ) := by push_cast; rfl
        _ ≤ _ := by exact_mod_cast hcard
    calc _ ≤ (2 * (ℓ : ℝ)) ^ 4 := hupper
      _ = 16 * (ℓ : ℝ) ^ 4 := by ring
      _ ≤ _ := by linarith
  · intro μ hμ
    set f : ℤ → ℝ := fun i => Real.exp (-(μ / 8) * |(i : ℝ)|) with hf
    have hf0 : ∀ i, 0 ≤ f i := fun i => (Real.exp_pos _).le
    have hgeo : Summable fun n : ℕ => Real.exp (-(μ / 8)) ^ n :=
      summable_geometric_of_lt_one (Real.exp_pos _).le
        (by rw [Real.exp_lt_one_iff]; linarith)
    have hs : Summable f := by
      refine Summable.of_nat_of_neg ?_ ?_
      · refine hgeo.congr fun n => ?_
        simp only [hf]
        rw [← Real.exp_nat_mul]
        congr 1
        simp
        ring
      · refine hgeo.congr fun n => ?_
        simp only [hf]
        rw [← Real.exp_nat_mul]
        congr 1
        simp
        ring
    set Z : ℝ := ∑' i, f i with hZ
    have hZ1 : 1 ≤ Z := by
      have h := hs.sum_le_tsum {(0 : ℤ)} (fun i _ => hf0 i)
      have h0 : f 0 = 1 := by simp [hf]
      rw [Finset.sum_singleton, h0] at h
      exact h
    set K : ℝ := 32 / μ ^ 2 * Real.exp (μ / 4) with hK
    have hKpos : 0 < K := by positivity
    refine ⟨K * Z ^ 4, by positivity, ?_⟩
    intro L m j _ hL hmj x
    obtain ⟨-, -, -, -, -, -, hpos, -, -, hrep⟩ := hLen L m j hL hmj
    choose n hn hn' using hrep
    have hinj : Function.Injective n := by
      intro u v huv
      apply Subtype.ext
      funext ν
      rw [hn u ν, hn v ν, huv]
    have hweight : ∀ u : Site L m j,
        (1 + supLengthInMesh u) ^ 2 * Real.exp (-μ * supLengthInMesh u) ≤ K * ∏ ν, f (n u ν) := by
      intro u
      set t := supLengthInMesh u with htdef
      have ht0 : 0 ≤ t := hpos u
      have hq : (1 + t) ^ 2 ≤ 32 / μ ^ 2 * Real.exp (μ / 4 * (1 + t)) := by
        have hx : 0 ≤ μ / 4 * (1 + t) := by positivity
        have h1 := Real.quadratic_le_exp_of_nonneg hx
        have h2 : (μ / 4 * (1 + t)) ^ 2 / 2 ≤ Real.exp (μ / 4 * (1 + t)) := by nlinarith
        rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
        nlinarith
      have hprod : Real.exp (-(μ / 2) * t) ≤ ∏ ν, f (n u ν) := by
        have e : ∏ ν, f (n u ν) = Real.exp (∑ ν, -(μ / 8) * |(n u ν : ℝ)|) := by
          rw [Real.exp_sum]
        rw [e]
        apply Real.exp_le_exp.mpr
        have hb : ∀ ν, |(n u ν : ℝ)| ≤ t := fun ν => by
          rw [htdef, hn' u]
          exact Finset.le_sup' (fun μ => |(n u μ : ℝ)|) (Finset.mem_univ ν)
        rw [← Finset.mul_sum]
        have hsum : ∑ ν, |(n u ν : ℝ)| ≤ 4 * t := by
          calc ∑ ν, |(n u ν : ℝ)| ≤ ∑ _ν : Fin 4, t := Finset.sum_le_sum fun ν _ => hb ν
            _ = 4 * t := by simp
        nlinarith
      calc (1 + t) ^ 2 * Real.exp (-μ * t)
          ≤ (32 / μ ^ 2 * Real.exp (μ / 4 * (1 + t))) * Real.exp (-μ * t) :=
            mul_le_mul_of_nonneg_right hq (Real.exp_pos _).le
        _ = K * Real.exp (-(3 * μ / 4) * t) := by
            rw [hK, mul_assoc, mul_assoc, ← Real.exp_add, ← Real.exp_add]
            congr 2
            ring
        _ ≤ K * Real.exp (-(μ / 2) * t) := by
            refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hKpos.le
            nlinarith
        _ ≤ K * ∏ ν, f (n u ν) := mul_le_mul_of_nonneg_left hprod hKpos.le
    have hshift : ∑ x' : Site L m j, (1 + supLengthInMesh (x' - x)) ^ 2 *
        Real.exp (-μ * supLengthInMesh (x' - x)) =
        ∑ u : Site L m j, (1 + supLengthInMesh u) ^ 2 * Real.exp (-μ * supLengthInMesh u) :=
      Fintype.sum_equiv (Equiv.subRight x) _ _ fun _ => rfl
    rw [hshift]
    refine (Finset.sum_le_sum fun u _ => hweight u).trans ?_
    rw [← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ hKpos.le
    classical
    set F : Finset (Fin 4 → ℤ) := Finset.univ.image n with hF
    have e1 : ∑ u : Site L m j, ∏ ν, f (n u ν) = ∑ p ∈ F, ∏ ν, f (p ν) := by
      rw [hF, Finset.sum_image (fun a _ b _ h => hinj h)]
    rw [e1]
    set proj : Fin 4 → Finset ℤ := fun ν => F.image fun p => p ν with hproj
    have hsub : F ⊆ Fintype.piFinset proj := by
      intro p hp
      rw [Fintype.mem_piFinset]
      intro ν
      exact Finset.mem_image.mpr ⟨p, hp, rfl⟩
    have h2 : ∑ p ∈ F, ∏ ν, f (p ν) ≤ ∑ p ∈ Fintype.piFinset proj, ∏ ν, f (p ν) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub
        fun p _ _ => Finset.prod_nonneg fun ν _ => hf0 _
    refine h2.trans ?_
    rw [← Finset.prod_univ_sum]
    calc ∏ ν, ∑ i ∈ proj ν, f i ≤ ∏ _ν : Fin 4, Z :=
          Finset.prod_le_prod (fun ν _ => Finset.sum_nonneg fun i _ => hf0 i)
            fun ν _ => hs.sum_le_tsum _ fun i _ => hf0 i
      _ = Z ^ 4 := by simp
end YangMills.Construction.HessianOfTheMainTerm
