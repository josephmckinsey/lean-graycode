--import Mathlib
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Data.Nat.Bitwise
import Mathlib.Analysis.Normed.Ring.Lemmas  -- I have no idea why this is necessary

--#eval Nat.testBit 1 0

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


#check geom_sum_two

lemma geom_sum_pow_two (n : ℕ) : ∑ i ∈ Finset.range n, 2 ^ i = 2^n - 1 := by
  have := Nat.geomSum_eq (m := 2) Nat.AtLeastTwo.prop n
  simp [this]

#check Nat.testBit_two_pow_sub_one


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
lemma next_to_xor_two_pow (x y : ℕ) :
  next_to x y ↔ (x ^^^ y).isPowerOfTwo := by
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

lemma nat_is_zero_or_between_two_pow (i : ℕ) :
  i = 0 ∨ ∃n, 2^n ≤ i ∧ i < 2^(n+1) := by
  by_cases i = 0
  · left; assumption
  right
  use Nat.log2 i
  constructor
  · exact Nat.log2_self_le (by assumption)
  exact Nat.lt_log2_self

lemma nat_is_zero_two_pow_or_between_two_pow (i : ℕ) :
  i = 0 ∨ (∃n, i = 2^n) ∨  ∃n, 2^n < i ∧ i < 2^(n+1) := by
  rcases (nat_is_zero_or_between_two_pow i) with h | ⟨n, h⟩
  · left; assumption
  right
  rcases h.1.lt_or_eq with h' | rfl
  · right; exact ⟨n, h', h.2⟩
  left; use n

lemma order_two_pow_testBit_true (x n : ℕ) (h1 : 2 ^ n ≤ x) (h2 : x < 2 ^ (n + 1)) :
  x.testBit n = true := by
  have : x >>> n = 1 := by
    rw [Nat.shiftRight_eq_div_pow]
    apply Nat.div_eq_of_lt_le
    · simp [h1]
    rw [mul_comm, <-Nat.pow_add_one]
    exact h2
  unfold Nat.testBit
  simp [this]

lemma bitwise_test_power_of_two (x : ℕ) (nezero : x ≠ 0) :
  x &&& (x - 1) = 0 ↔ x.isPowerOfTwo := by
  rcases nat_is_zero_two_pow_or_between_two_pow x with _ | ⟨n, h⟩ | ⟨n, h⟩
  · contradiction
  · simp [Nat.isPowerOfTwo, h]
  have : ¬x.isPowerOfTwo := by
    rw [Nat.isPowerOfTwo, not_exists]
    intro i h'
    rw [h'] at h
    rw [Nat.pow_lt_pow_iff_right (a := 2) (n := n) (m := i) (h := by norm_num)] at h
    rw [Nat.pow_lt_pow_iff_right (a := 2) (h := by norm_num)] at h
    linarith
  simp only [this, iff_false, ne_eq]
  suffices (x &&& (x - 1)).testBit n = true by grind
  have h1 : x.testBit n = true :=
    order_two_pow_testBit_true x n h.1.le h.2
  have h2 : (x - 1).testBit n = true := by
    grind [order_two_pow_testBit_true]
  rw [Nat.testBit_and, h1, h2]
  rfl

def Computable.next_to (x y : ℕ) : Bool :=
  let diff := x ^^^ y
  if diff = 0 then
    false
  else diff &&& (diff - 1) == 0

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

def IsUnitStepSeq {α : Type*} [AddGroupWithOne α] (x : α → ℕ) : Prop :=
  ∀i, next_to (x i) (x (i + 1))

def IsGrayCode {α : Type*} [AddGroupWithOne α] (x : α → ℕ) : Prop :=
  IsUnitStepSeq x ∧ Function.Injective x

def list_gray_code : ℕ → List ℕ
| 0 => [0]
| .succ n => (list_gray_code n).append ((list_gray_code n).reverse.map (2^n ^^^ ·))


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

def hello := "world"
