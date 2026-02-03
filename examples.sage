"""
Sage code to compute values associated to a list of coin denominations.
"""

from math import comb, perm, prod
from time import time

MAX_DEPTH = 7

def compute_gaps(coins):
	if len(coins) < 2:
		print(f"Error: must have at least two coin denominations. Given: {coins}.")
		return
	m,g,p = len(coins),coins[0],coins[0]
	for c in coins[1:]:
		g = gcd(g,c)
		p *= c
		if g == 1: break
	else:
		print(f"Error: must have gcd equal 1. Gcd found: {g}. Given denominations: {coins}.")
		return
	R.<t> = PowerSeriesRing(ZZ)
	a = prod((1+O(t^p))/(1-t^c+O(t^p)) for c in coins).padded_list(p)
	return [i for i in range(p) if a[i] == 0]

def compute_hilbert_num(coins, gaps):
	R.<t> = PolynomialRing(ZZ)
	p = prod(1-t^c for c in coins)
	return p//(1-t) - p*sum(t^g for g in gaps)

def compute_C(hnum):
	a = hnum.list()
	return lambda r: sum(-a[i]*i**r for i in range(1,len(a)))

def compute_K(coins,C):
	m = len(coins)
	return lambda p: C(m + p) / ((-1) ** m * prod(coins) * perm(m + p, m))

def T(n, inputs):
	_, p1, p2, _, p4, _, p6, _ = inputs # p0, p3, p5, p7 never used
	if n > 7:
		raise NotImplementedError
	values=[
		# n=0:
		1,
		# n=1:
		p1 / 2,
		# n=2:
		(3 * p1**2 + p2) / 12,
		# n=3:
		(p1**3 + p1 * p2) / 8,
		# n=4:
		(15 * p1**4 + 30 * p1**2 * p2 + 5 * p2**2 - 2 * p4) / 240,
		# n=5:
		(3 * p1**5 + 10 * p1**3 * p2 + 5 * p1 * p2**2 - 2 * p1 * p4) / 96,
		# n=6:
		(63 * p1**6
			+ 315 * p1**4 * p2
			+ 315 * p1**2 * p2**2
			- 126 * p1**2 * p4
			+ 35 * p2**3
			- 42 * p2 * p4
			+ 16 * p6) / 4032,
		# n=7:
		(9 * p1**7
			+ 63 * p1**5 * p2
			+ 105 * p1**3 * p2**2
			- 42 * p1**3 * p4
			+ 35 * p1 * p2**3
			- 42 * p1 * p2 * p4
			+ 16 * p1 * p6) / 1152]
	return values[n]

def compute(coins):
	print(f"Input: {coins}")
	gaps = compute_gaps(coins)
	print(f"Gaps: {gaps}")
	hnum = compute_hilbert_num(coins, gaps)
	print(f"Hilbert numerator: {hnum}")
	C = compute_C(hnum)
	K = compute_K(coins,C)
	G = lambda r: sum(g**r for g in gaps)
	sigma = lambda k: sum(d**k for d in coins)
	delta = lambda k: (sigma(k) - 1) / 2**k
	Tsigma = lambda n: T(n, [sigma(k) for k in range(MAX_DEPTH + 1)])
	Tdelta = lambda n: T(n, [delta(k) for k in range(MAX_DEPTH + 1)])
	def FelRHS(p):
		terms = [comb(p, r) * Tsigma(p - r) * G(r) for r in range(p + 1)]
		terms.append(2 ** (p + 1) / (p + 1) * Tdelta(p + 1))
		return sum(terms)
	for p in range(0, MAX_DEPTH):
		assert (Kp := K(p)) == FelRHS(p)
		print(f"K_{p} = {Kp}")
	print()

if __name__ == "__main__":
	start_time = time()
	compute([3,5])
	compute([4,5,6])
	compute([5,6,8,9])
	end_time = time()
	print(f"Time elapsed: {end_time-start_time} s.")
