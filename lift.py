

#!/usr/bin/python3
# -*- coding: utf-8 -*-
"""
Authors: ChairsDaily, p4r4xor, marcelgarus
References:
	YEAHHH I NEED TO DO THIS SOON
https://www.connellybarnes.com/documents/factoring.pdf
https://en.wikipedia.org/wiki/Integer_factorization
https://en.wikipedia.org/wiki/Fermat%27s_factorization_method
https://en.wikipedia.org/wiki/Wheel_factorization
https://en.wikipedia.org/wiki/Trial_division
https://en.wikipedia.org/wiki/Pollard%27s_rho_algorithm
"""

from __future__ import division
from itertools import chain, count
from random import randint
import math, sys

# collect small primes for faster
# primality test on small primes
# and witness testing for Miller
small_primes = [2, 3, 5, 7, 11, 13, 17, 19, 
23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 
71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 
113, 127, 131, 137, 139, 149, 151, 157, 163, 
167, 173, 179, 181, 191, 193, 197, 199, 211, 
223, 227, 229, 233, 239, 241, 251, 257, 263, 
269, 271, 277, 281, 283, 293, 307, 311, 313, 
317, 331, 337, 347, 349, 353, 359, 367, 373, 
379, 383, 389, 397, 401, 409, 419, 421, 431, 
433, 439, 443, 449, 457, 461, 463, 467, 479, 
487, 491, 499, 503, 509, 521, 523, 541, 547, 
557, 563, 569, 571, 577, 587, 593, 599, 601, 
607, 613, 617, 619, 631, 641, 643, 647, 653, 
659, 661, 673, 677, 683, 691, 701, 709, 719, 
727, 733, 739, 743, 751, 757, 761, 769, 773, 
787, 797, 809, 811, 821, 823, 827, 829, 839, 
853, 857, 859, 863, 877, 881, 883, 887, 907, 
911, 919, 929, 937, 941, 947, 953, 967, 971, 
977, 983, 991, 997]



def large_primes (n):
	"""
	Heavily modified sieve of eratosthenes, generate
	large primes quickly (for quick factorization
	of small composite numbers < 10^7)

	Arguments:
		n (:int) - upperbound for primes generation
	Returns:
		(generator) - all primes up to n non-inclusive
	Example:
		>>> tuple(large_primes(11))
		(2,3,5,7,)
	Author: ChairsDaily
	"""
	if n <= 2: return 
	if n & 1 != 1: n -= 1
	
	p = [0, 0] + ([1] * n)
	p[4:n:2] = [0] * ((n >> 1) - 1)
	
	if (n + 1) & 1 != 1:
		n += 1

	yield 2
	for j in range(3, n, 2):
		if p[j]:
			p[j*j::j] = [0] * len(p[j*j::j])
			yield j 


large_primes = large_primes(10**7)

"""
FROM HERE TO LINE 215 - PRIMALITY TESTING
"""
def bf_test (n):
	"""
	Bruteforce primality test using successive integers
	as trial factors. Includes some basic optimizations,
	works quite well for small n using a wheel mod 6 

	Arguments:
		n (:int) - the integer in question
	Returns:
		(:bool) - the primality
	Example:
		>>> bf_test(400)
		False
		>>> bf_test(5381)
		True
		>>> bf_test(201032122)
		False
	Authors: ChairsDaily
	"""
	if n < 2: return False 
	if n == 2 or n == 3: 
		return True 

	# wheel
	if not n % 2 or not n % 3:
		return False
	if n < 9: return True

	# trial divisor tests 
	d = 5
	while d < int(n**0.5):
		if not n % d: return False 
		d += 6
	return True


def aks_test (n):
	"""
	AKS primality test using (x-1)^n - (x^n - 1)
	to prove primality of n, or in other words
	the nth row of pascals triangle minus the leading
	and trailing 1s must be divisible by n.

	Arguments:
		n (:int) - the integer in question
	Returns:
		(:bool) - approximate primality of n 
	Example:
		>>> aks_test(23)
		True

		>>> aks_test(20)
		False
	Authors: ChairsDaily
	Notes: MUCH TOO SLOW FOR PRACTICAL USE
	"""
	if n == 2: return True

	# polynomial
	c = 1
	for i in range((n // 2) + 1):

		# expand each coefficient
		c = c * (n - i) // (i + 1)
		if c % n:
			return False 
	return True


def miller_rabin (n):
	"""
	Sufficient for very large numbers due to its
	witnessing optimizations for a probabilistic test.
	The more witnesses, the more accurate the claim
	of primality or compositeness.

	Arguments:
		n (:int) - the integer in question
	Returns:
		(:bool) - the primality of the number
	Example:
		>>> miller_rabin(5381)
		True
	Author: ChairsDaily
	"""

	# corner case
	if n <= 3: return n > 1
	primality = False 

	m = n - 1
	r = 0 # number of times 2 divides m
	
	# create a range of witnesses
	# upperbound taken from wikipedia
	# assume a natural logarithm
	logn = math.log(n)
	w = list()

	# when n is small, testing all a : a < 2(ln n)^2 is not 
	# absolutely required for accurate results 
	if n < 341550071728321: w = small_primes[:6]
	elif n < 3474749660383: w = small_primes[:5]
	elif n < 2152302898747: w = small_primes[:4]
	
	# deterministics
	elif n < 1122004669633: w = [2, 13, 23, 1662803]
	elif n < 4759123141: w = [2, 7, 61]
	elif n < 3215031751: small_primes[:3]
	elif n < 25326001: small_primes[:2] 
	elif n < 9080191: w = [31, 73]
	elif n < 1373653: w = small_primes[:1]
	elif n < 2047: w = small_primes[0] 
	else:
		w = range(2, 2 * int(
			logn * math.log(logn)/math.log(2))) 

	# remove all factors of 2 from m
	while m % 2 == 0:
		m //= 2
		r += 1

	for a in list(w):
		# select a witness w for 1,...,k
		# such that 2 < w < (n - 1) 
		x = pow(a, m, n) # the odd power
		neg = False 

		# keep squarring the odd power until we hit (n-1)st power
		for j in range(r + 1):
			if x == 1: primality = True; break  

			elif x == (n - 1):
				neg = True
		if primality:
			break 

		# closing case
		primality = neg
	return primality


def isprime (n):
	"""
	Combination of all above tests. Same argument
	and same return value.

	Arguments:
		n (:int) - the integer in question
	Returns:
		(:bool) - the primality of the number
	Example:
		>>> isprime(5381)
		True
	Author: ChairsDaily
	"""
	digits = math.log(n, 10) + 1

	# AKS is quite fast for very small n
	if digits < 2:
		return aks_test(n)
	else:
		# quickly check table of small primes 
		if n < 997:
			return n in small_primes
		
		# wheel mdo 6 functions well between 10^3 and 10^10
		elif digits < 10:
			return bf_test(n)
		else:

			# its too big, use millers formula
			return miller_rabin(n)

"""
FROM HERE TO LINE - FACTORIZATION CODE
"""
def table (n, primes):
	"""
	Use only members of a table of primes as trial divisors
	much faster with pre computed table, only works for 
	numbers < 10^7.

	Arguments:
		n (:int) - number to factor
		primes (:list/tuple) - iterable of primes not exceeding 10^7
	Returns:
		(generator) - prime factors of n
	Examples:
		>>> [p for p in table(20)]
		(2, 2, 5,)
	Author: ChairsDaily
	"""
	assert 2 <= n <= 10**7

	for p in tuple(primes)[:n]:
		while n % p == 0:
			yield p 
			n //= p 
			if n == 1: break


def bf_wheel (n):
	"""
	Bruteforce trial factorization with successive integers as
	candidate factors. uses a wheel mod 6 to speed things 
	up a lot. can be expanded to wheel mod 30 by adding to the
	prime basis, but takes extra steps in the trial phase. this seems
	to be the most optimized version I could put together.

	Arguments:
		n (:int) - the number to factor
	Returns:
		(generator) - prime factors of n
	Examples:
		>>> [p for p in bf_wheel(20)]
		(2, 2, 5,)
	Author: ChairsDaily
	"""
	if n <= 3: return n > 1
	while math.sqrt(n) == int(math.sqrt(n)):
		yield math.sqrt(n)
		n //= math.sqrt(n)
	if not n % 2 or not n % 3:
		while not n % 2: 
			yield 2
			n //= 2
		
		while not n % 3: 
			yield 3
			n //= 3

	# starting value for candidate
	# and improved upper bound
	d = 5
	upper = math.ceil(math.sqrt(n))

	while d < upper:
		while n % d == 0:
			n //= d
			yield d

		# correction case for wheel mod 6
		# we skipped the middle five digits essentially
		while n % (d + 2) == 0: 
			n //= (d + 2)
			yield (d + 2)

		if n == 1: break 
		d += 6
	if n > 1: yield n 


def fermats_composite (n):
	"""
	Use fermats sum of squares algorithm to quickly 
	derive a composite factor of n assuming n is 
	neither odd or prime. for the first condition,
	it may sometimes be necessary to run a certain amount
	of trial divisions and then ensure that n is now odd 
	before running a round of fermat.

	Arguments:
		n (:int) - the number to pull a composite from 
	Returns:
		(:int) - one composite that evenly divides n 
	Examples:
		>>> fermats_composite(932179818119999999999999999999)
		965510746754507

	NOTES: Domain error for 40 or more digits, also very slow
	for 30 digits or more. To fix, use a JIT decorator
	so that this function bypasses the byte-code compiler
	and runs directly as a C extension.

	Author: p4r4xor
	"""
	if not n % 2: return 

	x = math.ceil(math.sqrt(n))

	# this binomial seems to work the best
	# out of all the ones tested
	y = x*x - n 

	while not math.sqrt(y).is_integer():
		
		# add one to x and re evaluate the binomial
		# essentially moving up from the square root
		# of x until we find a valid factor
		# without testing divisibility because
		# of the sum of squares theory proved by fermat
		x += 1
		y = x*x - n

	return x + math.sqrt(y) # or x - sqrt(y)


def rhos_composite (n, r):
	"""
	In cases where there is a math domain error, Pollard Rho's
	algorithm can be used. It does less heavy lifting than
	fermat because of its use of gcd. for efficiency, however, 
	it would be best practice to divide and conquer n. do wheel 
	factorization a certain number of times until you have lets 
	say 3 or less factors, make sure your number is odd, 
	and then use fermat or rho depending on the size of n.

	NOTE: best used multiple times and to use wheel factorization on
	each result of rho f, n /f

	Arguments:
		n (:int) - the number to pull a composite from
	Returns:
		(:int) - one composite that evenly divides n
	Examples:
		>>> rho_composite(93893829381236799221918999100110000000111211212222222)
		286
	"""
	if not n % 2: return 
	if int(math.sqrt(n)) == math.sqrt(n): return 

	x = 2
	for cycle in count(1):
		y = x
		i = 1
		for j in range(2**cycle):
			i += 1
			# Pollard's modified fermat polynomial
			x = (x**18 + 2) % n 
			factor = math.gcd(x - y, n)

			if factor > r: return factor

			print('Cycle %d' % i)
'''
TRY THESE!!

2378273922111215
11111111111010191828112
777777777778738219391828228201111
92819321110999999991249
928193211109999999912499917882291842112111100000001101091101
237827392211121590191222999999999999999999999999999991010000000000092
9389382938123679922191899910011000000000000000000001191911
9281932111099999999124999178822918421121111000000011010911011209187761122222222211000010011101009761
251959084756578934940271832400483320277772844992687392807287776735971418347270261971824691165077613379859095700097330179742910064245869181719511874612151516869987549182911111111111111111111111111111111125195908475657893494027183240048332027777284499268739280728
'''

def factor (n):
	digits = math.log(n, 10) + 1
	factors = []

	if n < 10**7:

		# use a simple sieve 
		factors = list(table(n, large_primes))

	elif digits < 15:

		# just use a wheel factorizer
		factors = list(bf_wheel(n))

	elif digits >= 15:
		# could be handled quite quickly with 
		# a mod 30 wheel, but well divide and
		# conquer as proof of concept
		# first we check all primes up to 10^7
		# dont use table function it will
		# yield an assertion error
		for p in tuple(large_primes)[:n]: # only loop to n
			while n % p == 0:
				factors.append(p)
				n //= p
				if n == 1: break 

		# check to see if we can now jump
		# straight to wheel factorization
		new_digits = math.log(n, 10) + 1
		if new_digits < 20:
			factors += list(bf_wheel(n))

		# NOTE - if the sieve shrunk n enough, this will still run for numbers well over 30 digits ;)
		# but not always so we make another case for numbers exceeding 30 digits still at this point
		# this is most likely to happen with 70+ digit starting values 
		elif new_digits >= 20 and new_digits < 40:
			# at this point its best to just keep looping
			# fermat, but make sure it doesnt return None
			# if it does that means its either square
			# or even. we can assume at this point that n 
			# is not even, the sieve would have taken care
			# of all occurences of 2 in N so if we get
			# None that means N is currently square.
			# factor out the square and save the factorization
			# of that square as factors

			while math.log(n, 10) + 1 >= 20:

				C = None
				print('using sum of squares and incremental growth of X to find a composite factor...')
				C = fermats_composite(n)
				if C == None:
					print('was square...')
					# factor and divide square
					sq = int(math.sqrt(n))
					n //= sq 
					factors += list(bf_wheel(sq))
					continue # jump to next cycle where C might return a composite

				# here we know C is a valid composite
				# factor of n, so factor it out and 
				# add to factor list
				print('wheeling out the composite*...')
				n //= C
				factors += list(bf_wheel(C))

			# now n is less than 20 dgitis
			# wheel it out and add to factor list, we
			# are done here
			print('finishing off with wheel factorization...')
			factors += list(bf_wheel(n))


		elif new_digits >= 40:
			# this is big boy stuff. at this point
			# fermat WILL yield a domain error
			# so the fastest thing to do is start
			# looping pollard rho, which is
			# basically fermat but the composite
			# candidate grows much faster using
			# a polynomial of degree 2**k, where
			# is any multiple of 2
			# this is almost eliptic curve factorization

			while math.log(n, 10) + 1 >= 30:
				# if we can get it below 30, we can pass it on 
				# to another fermat loop ending again
				# with some wheel factorizations
				print('using polynomial growth of X to approach a composite factor...')
				C = rhos_composite(n, 1)

				if C == None:
					# factor out and divide square
					sq = int(math.sqrt(n))
					n //= sq
					factors += list(bf_wheel(sq)) # might want to consider a heavier wheel later on for 200+ digits
					# because your square will be quite large :)
					continue 

				# now we know C is a valid composite
				# divide and add to factor list
				print('wheeling out the composite...')
				n //= C 
				factors += list(bf_wheel(C))

			# now we known n is less than 30 digits
			# a goto would be nice right about now IM KIDDING
			while math.log(n, 10) + 1 >= 20:

				print('using sum of squares and incremental growth of X to find a composite factor...')
				C = fermats_composite(n)

				if C == None:
					print('was square')
					# factor and divide square
					sq = int(math.sqrt(n))
					n //= sq 
					factors += list(bf_wheel(sq))
					continue # jump to next cycle where C might return a composite

				# here we know C is a valid composite
				# factor of n, so factor it out and 
				# add to factor list
				print('wheeling out the composite...')
				n //= C
				factors += list(bf_wheel(C))

			# now n is less than 20 dgitis
			# wheel it out and add to factor list, we
			# are done here
			print('finishing off with wheel factorization...')
			factors += list(bf_wheel(n))

	print(factors)


if __name__ == '__main__':
	"""
	NOTICE: ANY NUMBER GREATER THAN 100 DIGITS,
	SCIENTIFIC NOTATION IS USED IN THE FACTORS
	SO PRIMALITY ASSERTION TESTS WILL YIELD
	FALSE NEGATIVES!
	"""
	n = 600851475143
	if n != None: factor(n)
	else:
		print('no value provided, set n')