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
-- alphabet q is a set of symbols
def alphabet (q : ℕ) := Fin q

-- ensure alphabet is finite
instance (q : ℕ) : Fintype (alphabet q) := Fin.fintype q

-- to check equality between symbols
instance (q : ℕ) : DecidableEq (alphabet q) := by
  unfold alphabet
  infer_instance

/-- codeword of length `n` over an alphabet of size `q`-/
-- n length sequence over alphabet of size q
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
  -- filter elements from univ (all codewords)
  Finset.filter (fun y => hammingDist x y ≤ r) Finset.univ

/--
Calculates the volume of a Hamming ball of radius `r` in a space of codewords of length `n` over an
alphabet of size `q`.
The volume is the number of codewords within the Hamming ball.
-/
def volumeHamming (q n r : ℕ) : ℚ :=
  ∑ i in Finset.range (r + 1), Nat.choose n i * (q - 1) ^ i

/--
The Hamming bound theorem states that for a code `C` of length `n`, size `q`, and minimum distance
`d`, the size of `C` is bounded by the volume of the space divided by the volume of a Hamming ball
of radius `t`, where `t` is the maximum number of errors that can be corrected.

The proof follows by contradiction: if two distinct codewords have overlapping Hamming balls, then their Hamming distance would be less than `d`, contradicting the definition of a code.
-/
theorem hammingBound {q n d : ℕ} (C : Finset (codeword q n)) 
-- minimum distance between distinct codewords is at least d
(hC : ∀ x ∈ C, ∀ y ∈ C, x ≠ y → hammingDist x y ≥ d) 
-- distance parameter is at least 1 (two distinct codewords differ in one position )
(hd : d ≥ 1  )
-- to ensure Hamming balls cannot overlap
(ht : 2 * t < d):
-- Goal : Show that for any two distinct codewords v, w /in C, their Hamming balls do not overlap.
∀ v ∈ C, ∀ w ∈ C, v ≠ w → Disjoint (hammingBall v t) (hammingBall w t) := by

-- Assume for contradiction that there exist distinct `v, w ∈ C` whose Hamming balls overlap
intro v hv w hw hdiff
#check Finset.disjoint_iff_ne
rw [Finset.disjoint_iff_ne]

-- Let z exists in both balls
rintro z hzv c hzw rfl


#check Finset.mem_filter
-- how elements belong to a filtered Finset
 -- z ∈ Finset.univ ∧ hammingDist v z ≤ t
 -- extract the second condition
have hammingDist_v : hammingDist v z ≤ t := (Finset.mem_filter.mp hzv).2
have hammingDist_w : hammingDist w z ≤ t := (Finset.mem_filter.mp hzw).2

-- show the symmetry of hamming distance
have hammingDist_w_symm : hammingDist z w ≤ t := by
    rw [hammingDist_comm]  
    exact hammingDist_w

-- using the triangle inequality: d(v, w) ≤ d(v, z) + d(z, w)
have hamming_triangle : hammingDist v w ≤ hammingDist v z + hammingDist z w := 
  hammingDist_triangle v z w

-- upper bound the sum using `t`
have hamming_bound : hammingDist v z + hammingDist z w ≤ t + t := 
  -- hammingDist v z + hammingDist z w ≤ t + t
  add_le_add hammingDist_v hammingDist_w_symm
  -- note: we assumed d(v,w) ≤ 2t
have h_eq : t + t = 2 * t := by ring
have h_final : 2 * t < d := ht

-- contradiction: d(v, w) < d but should be ≥ d
have h_contra : hammingDist v w < d := 
  -- hammingDist v w < d
  lt_of_le_of_lt (le_trans hamming_triangle hamming_bound) (by rw [h_eq]; exact h_final)
have h_min_dist : hammingDist v w ≥ d := hC v hv w hw hdiff

-- arrive to conttradiction
have h_false : False := by
    linarith [h_contra, h_min_dist]  

contradiction
-- 1. each codeword in C can be the center of a Hamming ball of radius r
-- 2. the Hamming balls are disjoint because the minimum distance between codewords is d
-- 3. the total number of codewords in the space is q^n
-- 4. the volume of a Hamming ball of radius r is the sum of the volumes of the Hamming balls
-- centered at each codeword
-- 5. prove that the total number of codewords multiplied by the volume of a Hamming ball cannot
-- exceed q^n

#print hammingBound
