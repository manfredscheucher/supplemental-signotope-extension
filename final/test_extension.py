#!/usr/bin/python


from sys import *
from itertools import *
from copy import *
import pycosat

from basics import *

from multiprocessing import Pool,cpu_count



import argparse
parser = argparse.ArgumentParser()
parser.add_argument("rank",type=int,help="rank")
parser.add_argument("n",type=int,help="number of elements")
parser.add_argument("inputfile",help="inputfile")

parser.add_argument("--allevenodd","-AEO",action='store_true',help="all I even and J odd for must be non-extentable") 

parser.add_argument("--evenodd","-EO",action='store_true',help="only test I even and J odd for extension") 
parser.add_argument("--justone","-1",action='store_true',help="only test one pair of (I,J) for extension") 
parser.add_argument("--justoneI","-1I",action='store_true',help="only test pairs (I,J) with I minimal for extension") 

parser.add_argument("--debug","-D",action='store_true',help="pring debug output")
parser.add_argument("--parallel","-P",action='store_false',help="use flag to disable parallel computations (enabled by default)")
parser.add_argument("--solver", choices=['cadical', 'pycosat'], default='cadical', help="SAT solver")
args = parser.parse_args()

print("args",args)

if args.allevenodd: 
	args.evenodd = True
	assert(not args.justone)
	assert(not args.justoneeven)



rank = args.rank
n = args.n
N = list(range(n))

inputfile = open(args.inputfile)
outputfile = open(args.inputfile+".nonext","w")


def test_extension_with_fliples(X,N,rank,wanted_fliples):
	n = max(N)+1

	N_plus = N+[n] # add a new element
	CNF = []

	all_variables = []
	all_variables += [('orientation',I) for I in combinations(N_plus,rank)]

	all_variables_index = {}

	_num_vars = 0
	for v in all_variables:
		all_variables_index[v] = _num_vars
		_num_vars += 1

	def var(L):	return 1+all_variables_index[L]
	def var_orientation(*L): return var(('orientation',L))

	for I in combinations(N,rank):
		if X[I] == +1:
			CNF.append([+var_orientation(*I)])
		else:
			CNF.append([-var_orientation(*I)])

	#print "(1) Signotope Axioms",len(constraints)
	# signature functions: forbid invalid configuartions 

	for X in combinations(N_plus,rank+1):
		T = list(combinations(X,rank))

		for t1,t2,t3 in combinations(T,3): # lex. ord. r-tuples t1 < t2 < t3
			for s in [+1,-1]:
				CNF.append([s*var_orientation(*t1),-s*var_orientation(*t2),s*var_orientation(*t3)])

				if t1 in wanted_fliples:
					# if t1 is fliple, then t2 and t3 must coincide (?++ or ?--)
					CNF.append([-s*var_orientation(*t2),s*var_orientation(*t3)])

				if t2 in wanted_fliples:
					# if t2 is fliple, then t1 and t2 must differ (+?- or -?+)
					CNF.append([-s*var_orientation(*t1),-s*var_orientation(*t3)])

				if t3 in wanted_fliples:
					# if t3 is fliple, then t1 and t2 must coincide (++? or --?)
					CNF.append([-s*var_orientation(*t1),s*var_orientation(*t2)])

	if args.solver == "cadical":
		#print ("use pysat/Cadical")
		from pysat.solvers import Cadical	
		solver = Cadical()
		for c in CNF: solver.add_clause(c)
		solution_iterator = solver.enum_models()
	else:
		#print ("use pycosat")
		import pycosat
		solution_iterator = pycosat.itersolve(CNF)

	for sol in solution_iterator: return True

	return False



def test_extendable_IJ_parallel_routine(params):
	return test_extension_with_fliples(*params)


def test_extendable_IJ_parallel(params):
	# can give speedup of factor n=2r 
	(X,N,rank,I,J) = params
	Xk = deepcopy(X)
	Ik = deepcopy(I)
	Jk = deepcopy(J)
	inputs = []
	for k in N:
		Xk = rotate(Xk,N,rank)
		Ik = tuple(sorted(tuple((j-1)%n for j in Ik)))
		Jk = tuple(sorted(tuple((j-1)%n for j in Jk)))
		wanted_fliples = [Ik+(n,),Jk+(n,)]
		inputs.append((Xk,N,rank,wanted_fliples))

	result = Pool(cpu_count()).map(test_extendable_IJ_parallel_routine,inputs) # if args.parallel else map(test_extendable_IJ_parallel_routine,inputs)
	return True in result


def test_extendable_IJ(params):
	if args.parallel:
		return test_extendable_IJ_parallel(params)

	(X,N,rank,I,J) = params
	Xk = deepcopy(X)
	Ik = deepcopy(I)
	Jk = deepcopy(J)
	for k in N:
		Xk = rotate(Xk,N,rank)
		Ik = tuple(sorted(tuple((j-1)%n for j in Ik)))
		Jk = tuple(sorted(tuple((j-1)%n for j in Jk)))
		wanted_fliples = [Ik+(n,),Jk+(n,)]
		if test_extension_with_fliples(Xk,N,rank,wanted_fliples):
			return True
	return False


def test_extendable(X,N,rank):	
	if args.evenodd:
		I_tuples = list(combinations(range(0,n,2),rank-1)) # only even indices
		J_tuples = list(combinations(range(1,n,2),rank-1)) # only odd indices
	else:
		I_tuples = J_tuples = list(combinations(range(0,n),rank-1))

	if args.allevenodd:
		for I in I_tuples:
			for J in J_tuples:
				if not set(I) & set(J): 
					if not test_extendable_IJ((X,N,rank,I,J)): 
						if args.debug: print ("[D] not extendable",I,J)						
					else:
						if args.debug: print ("[D] extendable",I,J)
						return True
		return False

	else:
		for I in I_tuples:
			for J in J_tuples:
				if not args.evenodd and not I<J: continue
				if not set(I) & set(J): 
					if not test_extendable_IJ((X,N,rank,I,J)): 
						if args.debug: print ("[D] not extendable",I,J)
						return False
					else:
						if args.debug: print ("[D] extendable",I,J)
					if args.justone:
						return True
			if args.justoneI:
				return True
		return True


def routine(line0):
	line = line0.split(" ")[0]
	X = line_to_signotope(line,N,rank)
	if X and not test_extendable(X,N,rank): 
		print("found non-extendable:",line0)
		#exit()
		return line0


inputs = list(inputfile.readlines())
print ("read",len(inputs),"signotopes from file")

ct = 0
ext_ct = 0

for X in map(routine,inputs):
	ct += 1
	if X != None:
		if X[-1] == '\n': X=X[:-1] 
		outputfile.write(X+"\n")
		ext_ct += 1

	print ("so far non-extendable:",ext_ct,"of",ct)
	
print ("done")
print ("TOTAL: non-extendable:",ext_ct,"of",ct)
