import Mathlib

/-! Extract the finite-length induction from the archive's KummerTheory/LenOfCard
into the slightly more general direction needed for actual certificates:
finite length itself implies finite cardinality, with order p^length.
The archive exports only the converse setup assuming a finite module. -/

namespace Compaction.FiniteLengthCard

private theorem card_simple (p : ℕ) [Fact p.Prime] (M : Type) [AddCommGroup M]
    [Module ℤ_[p] M] [h : IsSimpleModule ℤ_[p] M] : Nat.card M = p := by
  obtain ⟨I, hI, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp h
  have hIm : I = IsLocalRing.maximalIdeal ℤ_[p] := IsLocalRing.eq_maximalIdeal hI
  subst hIm
  rw [Nat.card_congr e.toEquiv]
  have f := RingHom.quotientKerEquivOfSurjective (ZMod.ringHom_surjective (PadicInt.toZMod (p := p)))
  have g := Ideal.quotEquivOfEq (PadicInt.ker_toZMod (p := p))
  rw [← Nat.card_congr g.toEquiv, Nat.card_congr f.toEquiv, Nat.card_zmod]

private theorem finite_length (p : ℕ) [Fact p.Prime] (M : Type) [AddCommGroup M]
    [Module ℤ_[p] M] (h : IsFiniteLength ℤ_[p] M) :
    ∃ k : ℕ, Module.length ℤ_[p] M = k ∧ Nat.card M = p^k := by
  induction h with
  | of_subsingleton =>
    exact ⟨0, by rw [Module.length_eq_zero]; rfl,
      by rw [Nat.card_of_subsingleton (0 : _)]; simp⟩
  | @of_simple_quotient M _ _ N _ _ ih =>
    obtain ⟨k, hk, hc⟩ := ih
    refine ⟨k+1, ?_, ?_⟩
    · rw [Module.length_eq_add_of_exact N.subtype N.mkQ (Submodule.injective_subtype N)
        (Submodule.mkQ_surjective N) (LinearMap.exact_subtype_mkQ N), hk, Module.length_eq_one]
      rfl
    · rw [AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup N.toAddSubgroup]
      have h1 : Nat.card (M ⧸ N.toAddSubgroup) = p := card_simple p (M ⧸ N)
      have h2 : Nat.card N.toAddSubgroup = p^k := hc
      rw [h1, h2, pow_succ, mul_comm]

theorem card_eq_pow_length (p : ℕ) [Fact p.Prime] (M : Type) [AddCommGroup M]
    [Module ℤ_[p] M] (h : Module.length ℤ_[p] M ≠ ⊤) :
    Nat.card M = p^(Module.length ℤ_[p] M).toNat := by
  obtain ⟨k, hk, hc⟩ := finite_length p M (Module.length_ne_top_iff.mp h)
  simpa only [hk, ENat.toNat_natCast] using hc

theorem finite_of_length (p : ℕ) [Fact p.Prime] (M : Type) [AddCommGroup M]
    [Module ℤ_[p] M] (h : Module.length ℤ_[p] M ≠ ⊤) : Finite M := by
  apply Nat.finite_of_card_ne_zero
  rw [card_eq_pow_length p M h]
  exact pow_ne_zero _ (Fact.out : p.Prime).ne_zero

end Compaction.FiniteLengthCard

#print axioms Compaction.FiniteLengthCard.card_eq_pow_length
#print axioms Compaction.FiniteLengthCard.finite_of_length
