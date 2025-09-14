import Graycode.NatLemmas

def next_to (x y : ℕ) : Prop :=
  ∃ j, x.testBit j != y.testBit j ∧
    ∀k ≠ j, x.testBit k = y.testBit k

example : next_to 4 5 := by
  unfold next_to
  use 0
  refine ⟨by simp, ?_⟩
  intro k knot0
  rw [Nat.testBit_eq_inth, Nat.testBit_eq_inth]
  rw [show Nat.bits 4 = [false, false, true] by simp [Nat.bits, Nat.binaryRec]]
  rw [show Nat.bits 5 = [true, false, true] by simp [Nat.bits, Nat.binaryRec]]
  -- There still has to be  abetter way to do this kind of casework
  if k = 0 then
    contradiction
  else if h : k = 1 then
    simp [h]
  else if h' : k = 2 then
    simp [h']
  else
    have : 3 ≤ k := by grind
    rw [List.getI_eq_default [false, false, true] (by simp [this])]
    rw [List.getI_eq_default [true, false, true] (by simp [this])]

def Computable.next_to (x y : ℕ) : Bool :=
  let diff := x ^^^ y
  if diff = 0 then
    false
  else diff &&& (diff - 1) == 0

/--
info: true
-/
#guard_msgs in
#eval Computable.next_to 1 3

/--
info: true
-/
#guard_msgs in
#eval Computable.next_to 3 2

/--
info: true
-/
#guard_msgs in
#eval Computable.next_to 4 5

/--
Note that $2^k - 1 = 1 + \cdots + 2^{k-1}$. Thus $(2^k - 1)_i = 1$ for
all $i \le {k-1}$.

When $x = 2^k$, since $(x)_k = 1$ and all others are $0$, while
$(x - 1)_k = 1$ for all $i \le k-1$ and $0$ otherwise. Thus $x \& (x - 1) = 0$
and we return true.

If $x = 0$, then we return false correctly.

Suppose that $2^i < x < 2^{i+1}$, then $(x)_i = 1$ and $2^i \le (x - 1) < 2^{i-1}$,
so thus $(x-1)_i = 1$. Thus $x \& (x - 1) \neq 0$.

    $x$ is next to $y$ iff there is some $i$ alone where they are different.
    This occurs iff $(x \oplus y) = (x)_i \oplus (y)_i = 1$ only for $i$.
    $(x \oplus y)_i$ for only $i$ iff $(x \oplus y) = 2^i$.
-/
lemma next_to_xor_two_pow (x y : ℕ) : next_to x y ↔ (x ^^^ y).isPowerOfTwo := by
  rw [show next_to x y ↔ ∃ j, (x ^^^ y).testBit j ∧ ∀k ≠ j, ¬(x ^^^ y).testBit k by
    simp [next_to]]
  apply exists_congr
  intro i
  set z := x ^^^ y
  refine ⟨?_, by grind⟩
  intro h
  apply Nat.eq_of_testBit_eq
  intro j
  if h' : j = i then
    rw [<-h'] at h ⊢
    simp only [Nat.testBit_two_pow_self, h.1]
  else
    rw [show z.testBit j = false by simp [h.2 j h']]
    rw [Nat.testBit_two_pow_of_ne (by grind)]


lemma computable_next_to_correct (x y : ℕ) :
    next_to x y ↔ Computable.next_to x y := by
  unfold Computable.next_to
  rw [next_to_xor_two_pow]
  if h : x ^^^ y = 0 then
    simp [h, Nat.isPowerOfTwo]
    intro i; positivity
  else
    rw [<-bitwise_test_power_of_two _ h]
    rw [if_neg h]
    exact beq_iff_eq.symm

def IsUnitStepSeq {α : Type*} [AddMonoid α] [One α] (x : α → ℕ) : Prop :=
  ∀i, next_to (x i) (x (i + 1))

def IsGrayCode {α : Type*} [AddMonoid α] [One α] (x : α → ℕ) : Prop :=
  IsUnitStepSeq x ∧ Function.Bijective x

def list_gray_code : ℕ → List ℕ
| 0 => [0]
| .succ n => (list_gray_code n) ++ ((list_gray_code n).reverse.map (2^n ^^^ ·))

def is_list_gray_code (x : List ℕ) : Bool := Id.run do
  let mut is_good := true
  for i in List.range (x.length + 1) do
    is_good := is_good && Computable.next_to x[i % x.length]! x[(i + 1) % x.length]!
  return is_good

/--
info: [0, 1, 3, 2]
-/
#guard_msgs in
#eval list_gray_code 2

/--
info: true
-/
#guard_msgs in
#eval is_list_gray_code (list_gray_code 5)

@[simp, grind =]
lemma list_gray_code_length (n : ℕ) : (list_gray_code n).length = 2^n := by
  fun_induction list_gray_code n with
  | case1 => rfl
  | case2 n h => simp [h]; ring

@[simp]
lemma list_gray_code_zero (n : ℕ) : (list_gray_code n)[0] = 0 := by
  induction n with
  | zero => simp [list_gray_code]
  | succ n nh =>
    unfold list_gray_code
    simp [nh]

@[reducible]
def list_gray_code_i (i : ℕ) :=
  (list_gray_code (i.log2 + 1))[i]'(by
    rcases Nat.eq_zero_or_pos i with rfl | h
    · simp
    simp [Nat.lt_log2_self]
  )

def recursive_gray_code (n : ℕ) : ℕ :=
  binaryComplementRec
    (zero := 0) -- zero case
    (two_pow := fun i _ complement ↦ 2^(i.log2) ^^^ complement)
      -- do when you have the complement
    n

/--
info: true
-/
#guard_msgs in
#eval (List.range (2^5)).all (fun i ↦ recursive_gray_code i == (list_gray_code 5)[i]!)

def recursive_gray_code_eq {i : ℕ} (nezero : i ≠ 0) :
  recursive_gray_code i = 2^(i.log2) ^^^ recursive_gray_code ((2^(i.log2+1) - 1) ^^^ i) := by
  rw [recursive_gray_code, binaryComplementRec]
  simp_rw [dite_eq_ite, if_neg nezero]
  rw [<-recursive_gray_code]

@[simp]
lemma recursive_gray_code_zero : recursive_gray_code 0 = 0 := by
  simp [recursive_gray_code, binaryComplementRec]

def direct_gray_code (n : ℕ) : ℕ := n ^^^ (n >>> 1)

/--
info: true
-/
#guard_msgs in
#eval (List.range (2^5)).all (fun i ↦ direct_gray_code i == (list_gray_code 5)[i]!)

@[simp]
lemma direct_gray_code_zero : direct_gray_code 0 = 0 := by rfl

def recursive_inverse : ℕ → ℕ :=
  binaryBigEndianRec
    (zero := (0 : ℕ))
    (two_pow := fun i _ complement ↦ (2^(i.log2 + 1) - 1) ^^^ complement)

/--
info: true
-/
#guard_msgs in
#eval (List.range (2^5)).all (fun i ↦ recursive_inverse (recursive_gray_code i) == i)

/--
info: true
-/
#guard_msgs in
#eval (List.range (2^5)).all (fun i ↦ (recursive_gray_code (recursive_inverse i)) == i)

@[simp]
lemma recursive_inverse_zero : recursive_inverse 0 = 0 := by
  simp [recursive_inverse, binaryBigEndianRec]

lemma recursive_inverse_eq {n : ℕ} (nezero : n ≠ 0) :
    recursive_inverse n = (2^(n.log2 + 1) - 1) ^^^ recursive_inverse (n ^^^ 2^n.log2) := by
    rw [recursive_inverse, binaryBigEndianRec]
    rw [dite_eq_ite, if_neg nezero]
    rfl

def direct_inverse (n : ℕ) : ℕ :=
  if n = 0 then
    0
  else
    n ^^^ direct_inverse (n >>> 1)

/--
info: true
-/
#guard_msgs in
#eval (List.range (2^5)).all (fun i ↦ direct_inverse i == recursive_inverse i)

@[simp]
lemma direct_inverse_zero : direct_inverse 0 = 0 := by simp [direct_inverse]
