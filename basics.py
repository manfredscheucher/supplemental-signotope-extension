from itertools import *
from ast import *
from sys import *

if 1^1 == 0: assert(int(version.split('.')[0]) >= 3) # use python 3.x or later
if 1^1 == 1: assert(int(version().split()[2].split('.')[0]) >= 9) # use sage 9.x or later

# def permutations(X,r): return itertools.permutations(X,int(r)) # sage 3.X bugfix


# also works with partial signotopes (not all entries needed)
def test_valid_signotope(X,elements,rank):
	for I in combinations(elements,rank+1):
		X_I = [X[J] for J in combinations(I,rank) if J in X] 
		s = 0
		for i in range(len(X_I)-1):
			if X_I[i] != X_I[i+1]: 
				s += 1
				if s > 1: return False
	return True 


def test_valid_signotope_after_flip(X,elements,rank,flipped_tuple):
	for x in set(elements)-set(flipped_tuple):
		I = list(sorted(flipped_tuple+(x,)))
		X_I = [X[J] for J in combinations(I,rank) if J in X] 
		s = 0
		for i in range(len(X_I)-1):
			if X_I[i] != X_I[i+1]: 
				s += 1
				if s > 1: return False
	return True 



def test_flipable(X,elements,rank,I):
	s = X[I]
	X[I] = -s
	result = test_valid_signotope_after_flip(X,elements,rank,I)
	X[I] = s
	return result

	
def string_to_signotope(X_str,elements,rank):
	X = {}
	i = 0
	for I in combinations(elements,rank):
		assert(X_str[i] in ["+","-"])
		s = +1 if X_str[i] == "+" else -1
		i += 1
		X[I] = s
	return X 



def line_to_signotope(line,elements,rank):
	if line == "\n": return

	X_str = line.split()[1] if ' ' in line else line
	if X_str[-1] == '\n': X_str = X_str[:-1]

	X = string_to_signotope(X_str,elements,rank)
	assert(test_valid_signotope(X,elements,rank))
	return X


def transpositions(I): 
	return sum(1 for (i,j) in combinations(I,2) if i>j)


def signotope_to_chirotope(X,N,rank):
	Y = {I:X[tuple(sorted(I))]*(-1)**transpositions(I) for I in permutations(N,rank)}
	for I in product(N,repeat=rank):
		if I not in Y: 
			Y[I] = 0
	return Y



def to_string(X,N,rank):
	return ''.join('+' if X[I] == +1 else '-' for I in combinations(N,rank))


def rotate(X,N,rank):
	max_element = max(N)
	assert(N == list(range(max_element+1)))

	X_rot = {}
	for I in combinations(N,rank):
		if I[-1] < max_element:
			X_rot[I] = X[tuple(x+1 for x in I)]
		else:
			X_rot[I] = -X[(0,)+tuple(x+1 for x in I[:-1])]
	assert(test_valid_signotope(X_rot,N,rank))

	return X_rot


