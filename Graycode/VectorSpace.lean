import Mathlib

@[ext]
structure BinaryNat where
  ofNat ::
    (toNat : ℕ)
deriving Inhabited, Repr


@[simp]
lemma BinaryNat.toNat_ofNat (x : ℕ) : (BinaryNat.ofNat x).toNat = x := rfl

instance : Zero BinaryNat where
  zero := BinaryNat.ofNat 0

@[simp]
lemma BinaryNat.toNat_zero : (0 : BinaryNat).toNat = 0 := rfl

instance : One BinaryNat where
  one := .ofNat 1

@[simp]
lemma BinaryNat.toNat_one : (1 : BinaryNat).toNat = 1 := rfl

instance : Nontrivial BinaryNat where
  exists_pair_ne := let ⟨x, y, h⟩ := (inferInstance :  Nontrivial ℕ).exists_pair_ne;
    ⟨.ofNat x, .ofNat y, by simp [h]⟩

instance : WellFoundedRelation BinaryNat where
  rel x y := WellFoundedRelation.rel x.toNat y.toNat
  wf := WellFounded.onFun (WellFoundedRelation.wf)

instance : LinearOrder BinaryNat where
  le x y := LE.le x.toNat y.toNat
  le_refl x := Preorder.le_refl x.toNat
  le_trans x y z := Preorder.le_trans x.toNat y.toNat z.toNat
  le_antisymm x y h h' := BinaryNat.ext (PartialOrder.le_antisymm x.toNat y.toNat h h')
  le_total x y := LinearOrder.le_total x.toNat y.toNat
  toDecidableLE x y := inferInstance

instance : Add BinaryNat where
  add x y := .ofNat (Nat.xor x.toNat y.toNat)

lemma BinaryNat.add_eq (x y : BinaryNat) : x + y =
  .ofNat (x.toNat ^^^ y.toNat) := rfl

instance : Mul BinaryNat where
  mul x y := .ofNat (Nat.land x.toNat y.toNat)

lemma BinaryNat.mul_eq (x y : BinaryNat) : x * y = .ofNat (x.toNat &&& y.toNat) := rfl

@[simp]
instance : Neg BinaryNat where
  neg := id

instance (n : Nat) : OfNat BinaryNat n where
  ofNat := .ofNat n

@[simp]
lemma BinaryNat.toNat_NatofNat (x : ℕ) : (OfNat.ofNat x : BinaryNat).toNat = x := by rfl

@[simp]
lemma BinaryNat.add_self (x : BinaryNat) : x + x = 0 := BinaryNat.ext (Nat.xor_self x.toNat)

@[reducible, simp]
def binaryNat_fast_nsmul (n : ℕ) (x : BinaryNat) := if Even n then 0 else x

@[reducible, simp]
def binaryNat_fast_zsmul (n : ℤ) (x : BinaryNat) := if Even n then 0 else x

@[simp]
def binaryNat_fast_zmodmul (n : ZMod 2) (x : BinaryNat) := if n == 0 then 0 else x

instance : AddCommGroup BinaryNat where
  add_assoc x y z := BinaryNat.ext (Nat.xor_assoc x.toNat y.toNat z.toNat)
  zero_add x := BinaryNat.ext (Nat.zero_xor x.toNat)
  add_zero x := BinaryNat.ext (Nat.xor_zero x.toNat)
  add_comm x y := BinaryNat.ext (Nat.xor_comm x.toNat y.toNat)
  neg_add_cancel x := BinaryNat.ext (Nat.xor_self x.toNat)
  nsmul := binaryNat_fast_nsmul
  zsmul := binaryNat_fast_zsmul
  nsmul_succ n x := by
    by_cases h : Even n
    · have : ¬Even (n + 1) := by grind
      simp [h, this]
      exact BinaryNat.ext (Nat.zero_xor x.toNat).symm
    have : Even (n+1) := by grind
    simp [h, this]
  zsmul_succ' n x := by
    by_cases h : Even n
    · have : ¬Even ((n : ℤ) + 1) := by grind
      simp [h, this]
      exact BinaryNat.ext (Nat.zero_xor x.toNat).symm
    have : Even ((n : ℤ) + 1) := by grind
    simp [h, this]
  zsmul_neg' n x := by
    rw [Int.negSucc_eq, binaryNat_fast_zsmul]
    have : ∀z : ℤ, Even (-z) ↔ Even z := by grind
    simp_rw [this ((n : ℤ) + 1)]
    rfl

instance : SMul (ZMod 2) BinaryNat where
  smul := binaryNat_fast_zmodmul

instance : Module (ZMod 2) BinaryNat where
  one_smul b := rfl
  mul_smul c d x := by fin_cases c, d <;> rfl
  smul_zero a := by fin_cases a <;> rfl
  smul_add c x y := by
    change binaryNat_fast_zmodmul c (x + y) =
      binaryNat_fast_zmodmul c x + binaryNat_fast_zmodmul c y
    fin_cases c <;> simp
  add_smul c d x := by
    change binaryNat_fast_zmodmul (c + d) x =
      binaryNat_fast_zmodmul c x + binaryNat_fast_zmodmul d x
    fin_cases c, d <;> simp [show (1 + 1 : ZMod 2) = 0 by rfl]
  zero_smul x := rfl

-- Alternative using ZMod 2
abbrev BitVector := ℕ →₀ (ZMod 2)

@[simp]
theorem Nat.bitIndices_getElem_iff_testBit (n : ℕ) (i : ℕ) :
    i ∈ Nat.bitIndices n ↔ Nat.testBit n i = true := by
  induction n using binaryRec generalizing i with
  | z => simp
  | f b n a =>
    by_cases h : i = 0
    · rcases b <;> simp [h]
    have : i = (i - 1).succ := by simp; grind
    rw [this]
    simp [Nat.testBit_bit_succ]
    rcases b <;> simp [a (i -1)]

def binaryNatToBitVector : BinaryNat → BitVector := fun n =>
  {
    support := (Nat.bitIndices n.toNat).toFinset
    toFun := fun i => if n.toNat.testBit i then 1 else 0
    mem_support_toFun := by
      intro i
      simp
  }

def bitVectorToBinaryNat : BitVector → BinaryNat := fun n =>
  .ofNat (Finset.equivBitIndices.invFun n.support)

@[simp]
lemma geomSum_testBit (s : Finset ℕ) (i : ℕ) :
    (∑ i ∈ s, 2 ^ i).testBit i = true ↔ i ∈ s := by
  set n := ∑ i ∈ s, 2^i with n_def
  have : s = n.bitIndices.toFinset := by
    simp [n_def] -- Colex combinatorics
  rw [this]
  simp

def binaryNat_bitVector_add_iso : BinaryNat ≃+ BitVector where
  toFun := binaryNatToBitVector
  invFun := bitVectorToBinaryNat
  left_inv := by
    intro n
    rw [bitVectorToBinaryNat, binaryNatToBitVector]
    simp [Finset.equivBitIndices]
  right_inv := by
    intro n
    rw [bitVectorToBinaryNat, binaryNatToBitVector]
    simp only [Finset.equivBitIndices, Equiv.invFun_as_coe, Equiv.coe_fn_symm_mk,
      Finset.toFinset_bitIndices_twoPowSum, geomSum_testBit, Finsupp.mem_support_iff, ne_eq,
      ite_not]
    ext i
    simp only [Finsupp.coe_mk]
    -- This feels incredibly stupid
    set m := n i
    have : ∀m : Fin 2, m = 0 ∨ m = 1 := by intro m; grind
    rcases (this m) <;> grind
  map_add' := by
    intro x y
    ext i
    simp [binaryNatToBitVector]
    rw [BinaryNat.add_eq, Nat.testBit_xor]
    rw [show Nat.testBit x.toNat i = x.toNat.testBit i by rfl]
    rw [show Nat.testBit y.toNat i = y.toNat.testBit i by rfl]
    grind


def binaryNat_bitVector_module_iso : BinaryNat ≃ₗ[ZMod 2] BitVector where
  toFun := binaryNatToBitVector
  invFun := bitVectorToBinaryNat
  left_inv := binaryNat_bitVector_add_iso.left_inv
  right_inv := binaryNat_bitVector_add_iso.right_inv
  map_add' := binaryNat_bitVector_add_iso.map_add'
  map_smul' := by
    intro c x
    ext i
    fin_cases c <;> simp [binaryNatToBitVector]

#synth Module (ZMod 2) BitVector
#synth Module (ZMod 2) BinaryNat

def test_bitvector : BitVector := List.toFinsupp [1]

def powerOfTwoBasis : Module.Basis ℕ (ZMod 2) BinaryNat where
  repr := binaryNat_bitVector_module_iso

#check Finsupp.sum

/--
a_n = 2^(n+1) - 1 form a basis of Nat.

They are independent, since ∑ c_i a_i = 0 implies that c_i = 0, since
(∑ i ∈ S, c_i a_i).testBit (max S) = 1.

Alternatively, we can construct an isomorphism as follows:

toFun 0 = fun i ↦ 0
toFun n = for i < n.log2, (1 - toFun (complement n)), for i = n.log2, 1
  otherwise 0.

invFun f = Finsupp.sum f (fun n b => (b • (2^(n+1) - 1)))
-/

def powerOfTwoMinusOne (i : ℕ) : BinaryNat := .ofNat (2^(i+1) - 1)

noncomputable def powerOfTwoMinusOneBasis : Module.Basis ℕ (ZMod 2) BinaryNat := Module.Basis.mk (v := powerOfTwoMinusOne)
  (by
    rw [linearIndependent_iff]
    intro v h
    contrapose! h
    -- First, we'll get the largest
    unfold Finsupp.linearCombination
    simp
    simp_rw [powerOfTwoMinusOne.eq_def]
    have : v.support.Nonempty := Finsupp.support_nonempty_iff.mpr h
    have : ∀f : _ → _ → BinaryNat, v.sum f = v.support.sum (fun i => f i 1) := by sorry
    rw [this]
    simp
    -- prove by induction on the size of v.support?



    have : Finsupp.basisSingleOne 1

  )
  (by sorry)

-- Noncomputable :(
--#eval (test_bitvector + test_bitvector) 3
