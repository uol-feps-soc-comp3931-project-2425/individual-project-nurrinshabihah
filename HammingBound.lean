/-
Author: Nurrin Shabihah
-/
import Mathlib.InformationTheory.Hamming
import Mathlib.Data.Fintype.Basic


/-
# Hamming bound

The Hamming bound, also known as the sphere-packing bound, provides a limit on the number of
codewords a code can have while ensuring error correction within a given distance. It calculates the
maximum number of disjoint Hamming balls that can fit in the space of a finite Π-type, where each
ball corresponds to the set of elements differing from a codeword in at most a fixed number of
positions.

## Main definitions
* `hammingBall β r`: the set of elements in `Π i, β i` within a Hamming distance `r` from a fixed
center
* `hammingBound q n r`: the maximum number of disjoint Hamming balls of radius `r` that can fit in
in a space of length `n` over an alphabet of size `q`
* `hammingBound β`: a type of synonym for representing bounds on codes in the space `Π i, β i`
* `hammingBound.valid`: a property that verifies if a code satisfies the Hamming bound for its
parameters.
-/


/-- alphabet of size `q`-/
def alphabet (q : ℕ) := Fin q

-- ensure alphabet is finite
instance (q : ℕ) : Fintype (alphabet q) := Fin.fintype q

instance (q : ℕ) : DecidableEq (alphabet q) := by
  unfold alphabet
  infer_instance

/-- codeword of length `n` over an alphabet of size `q`-/
def codeword (q n : ℕ) := Fin n → alphabet q

-- ensure codewords are finite
instance (q n : ℕ) : Fintype (codeword q n) := Pi.instFintype

instance (q : ℕ) : DecidableEq (codeword q n) := by
  unfold codeword
  infer_instance

/--
Defines a Hamming ball of radius `r` centered at a codeword `x`.
It is the set of all codewords `y` such that the Hamming distance between `x`
and `y` is at most `r`.
-/
def hammingBall {q n : ℕ} (x : codeword q n) (r : ℕ) : Finset (codeword q n) :=
  Finset.filter (fun y => hammingDist x y ≤ r) Finset.univ

/--
Calculates the volume of a Hamming ball of radius `r` in a space of codewords of length `n` over an
alphabet of size `q`.
The volume is the number of codewords within the Hamming ball.
-/
def volumeHamming (q n r : ℕ) : ℚ :=
  ∑ i in Finset.range (r + 1), Nat.choose n i * (q - 1) ^ i

def minDistance {q n : ℕ} (C : Finset (codeword q n)) : Option ℕ :=
  if h : Finset.Nonempty (Finset.offDiag C) then
    some (Finset.inf' (Finset.offDiag C) h (fun ⟨x, y⟩ => hammingDist x y))
  else
    none


/--
The Hamming bound theorem states that for a code `C` of length `n`, size `q`, and minimum distance
`d`, the size of `C` is bounded by the volume of the space divided by the volume of a Hamming ball
of radius `t`, where `t` is the maximum number of errors that can be corrected.
-/
theorem hammingBound {q n d : ℕ} (C : Finset (codeword q n)) (hC : ∀ x ∈ C, ∀ y ∈ C,
x ≠ y → hammingDist x y ≥ d) (hd : d ≥ 1  ):
∀ v ∈ C, ∀ w ∈ C, v ≠ w → Disjoint (hammingBall v t) (hammingBall w t) := by
let t := (d-1)/2
-- assume contradiction that spheres overlap
intro v hv w hw hvw
rw [Finset.disjoint_iff_ne]
intro y hyv hyw
-- y is in the hamming ball of radius t centered at v and w
have hDist_v : hammingDist v y ≤ t := hyv
have hDist_w : hammingDist w y ≤ t := hyw

--C.card ≤ (q^n) / (volumeHamming q n ((d - 1) / 2)) :=
by
    sorry
#check Finset.disjoint_iff_ne
-- 1. each codeword in C can be the center of a Hamming ball of radius r
-- 2. the Hamming balls are disjoint because the minimum distance between codewords is d
-- 3. the total number of codewords in the space is q^n
-- 4. the volume of a Hamming ball of radius r is the sum of the volumes of the Hamming balls
-- centered at each codeword
-- 5. prove that the total number of codewords multiplied by the volume of a Hamming ball cannot
-- exceed q^n
