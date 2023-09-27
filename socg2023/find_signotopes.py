#!/usr/bin/python
"""
	(c) 2022 by Manfred Scheucher and Helena Bergold
"""

from itertools import *
from sys import argv


from basics import *


import argparse
parser = argparse.ArgumentParser()
parser.add_argument("rank",type=int,help="rank")
parser.add_argument("n",type=int,help="number of elements")
parser.add_argument("-a","--all",action='store_true', help="enumerate all configurations")
parser.add_argument("--maxnumfliples","-m",type=int,help="maximum number of fliples")
parser.add_argument("--comparability","-c",action='store_true',help="assert comparability")
parser.add_argument("--loadsignotope","-l",type=str,help="load signotope from file")
parser.add_argument("--instance2file","-i2f",type=str,help="write instance to file")
parser.add_argument("--solutions2file","-s2f",type=str,help="write solutions to file")
parser.add_argument("--dontsolve",action='store_true',help="do not solve instance")
parser.add_argument("--assumptions",action='store_true',help="make assumptions as in the paper to restrict the search space")
parser.add_argument("--solver", choices=['cadical', 'pycosat'], default='cadical', help="SAT solver")
args = parser.parse_args()

print("args",args)

rank = args.rank
n = args.n
N = list(range(n))

m = args.maxnumfliples

even = list(range(0,n,2))
odd  = list(range(1,n,2))

rank_plus_one_types_all = [s for s in ["".join(s) for s in product('+-',repeat=rank+1)] if s.count('+-')+s.count('-+') <= 1]

print ("number of rank_plus_one_types_all:",len(set(rank_plus_one_types_all)))

def string_flip(t,i): return t[:i]+('+' if t[i] == '-' else '-')+t[i+1:]

# in the following types, index j is flipable
rank_plus_one_types_with_flipable_j = {j:[t for t in rank_plus_one_types_all if string_flip(t,j) in rank_plus_one_types_all] for j in range(rank+1)}

def type_to_vector(t): return [(+1 if x == '+' else -1) for x in t]


all_variables = []
all_variables += [('sign',I) for I in combinations(N,rank)]
all_variables += [('rank_plus_one_type',(I,t))   for I in combinations(N,rank+1) for t in rank_plus_one_types_all] # indicates whether (rank+1)-tuple is of type t
all_variables += [('flipable_j',(I,j)) for I in combinations(N,rank+1) for j in range(rank+1)] # indicates whether, in (rank+1)-tuple, index j is flipable
all_variables += [('flipable',I)  for I in combinations(N,rank)] # indicates whether (rank)-tuple is flipable
if args.maxnumfliples:
	all_variables += [('count',(I,k)) for I in combinations(N,rank) for k in range(m+1)]


if args.comparability:
	all_variables += [('sign_rot',(k,I)) for I in combinations(N,rank) for k in range(2*n)]
	VERTICES = list(combinations(N,rank-1))
	all_variables += [('edge',(k,u,v)) for u,v in permutations(VERTICES,2) for k in N]
	all_variables += [('reachable',(k,u,v,t)) for u in VERTICES for v in VERTICES for t in range(len(N)) for k in N] # u reaches v in t steps
	all_variables += [('reachable_via',(k,u,v,w,t)) for u in VERTICES for v in VERTICES for w in VERTICES for t in range(1,len(N)) for k in N] # u reaches v via w in t steps



all_variables_index = {}

_num_vars = 0
for v in all_variables:
	all_variables_index[v] = _num_vars
	_num_vars += 1

def var(L):	return 1+all_variables_index[L]

def var_sign(*L): return var(('sign',L))
def var_rank_plus_one_type(*L): return var(('rank_plus_one_type',L))
def var_flipable_j(*L): return var(('flipable_j',L))
def var_flipable(*L): return var(('flipable',L))
def var_count(*L): return var(('count',L))

def var_sign_rot(*L): return var(('sign_rot',L))

def var_vertex(*L): return var(('vertex',L))
def var_edge(*L): return var(('edge',L))
def var_reachable(*L): return var(('reachable',L))
def var_reachable_via(*L): return var(('reachable_via',L))


constraints = []

print ("(*) each (rank+1)-tuple has one type")
for I in combinations(N,rank+1):
	constraints.append([+var_rank_plus_one_type(I,t) for t in rank_plus_one_types_all])


def remove_jth(I,j): return I[:j]+I[j+1:]


print ("(*) assign rank_plus_one_type variables")
for I in combinations(N,rank+1):
	for t in rank_plus_one_types_all:
		tv = type_to_vector(t)
		for j in range(rank+1):
			constraints.append([-var_rank_plus_one_type(I,t),+tv[j]*var_sign(*remove_jth(I,rank-j))])
		constraints.append([+var_rank_plus_one_type(I,t)]+[-tv[j]*var_sign(*remove_jth(I,rank-j)) for j in range(rank+1)])


print ("(*) assign flipable_j variables")
for I in combinations(N,rank+1):
	for j in range(rank+1):
		constraints.append([-var_flipable_j(I,j)]+[+var_rank_plus_one_type(I,t) for t in rank_plus_one_types_with_flipable_j[j]])

		for t in rank_plus_one_types_with_flipable_j[j]: 
			constraints.append([+var_flipable_j(I,j),-var_rank_plus_one_type(I,t)])
	

print ("(*) assign flipable variables")
for I in combinations(N,rank):
	I_plus = (-1,)+I+(n,)
	I_extension_at_j = {j:[I[:j]+(x,)+I[j:] for x in range(I_plus[j]+1,I_plus[j+1])] for j in range(rank+1)}

	for j in range(rank+1):
		for J in I_extension_at_j[rank-j]: 
			constraints.append([-var_flipable(*I),+var_flipable_j(J,j)])

	constraints.append([+var_flipable(*I)]+[-var_flipable_j(J,j) for j in range(rank+1) for J in I_extension_at_j[rank-j]])


if args.maxnumfliples:
	print ("(*) counting variables")
	prevI = None
	for I in combinations(N,rank):

		# assert count 
		constraints.append([var_count(I,k) for k in range(m+1)])
		for k,l in combinations(range(m+1),2):
			constraints.append([-var_count(I,k),-var_count(I,l)])

		if prevI != None:
			constraints.append([-var_count(prevI,m),-var_flipable(*I)])
			for k in range(m):
				constraints.append([-var_count(prevI,k),-var_flipable(*I),+var_count(I,k+1)])

			for k in range(m+1):
				constraints.append([-var_count(prevI,k),+var_flipable(*I),+var_count(I,k)])
				
		else:
			constraints.append([+var_flipable(*I),+var_count(I,0)])
			if m > 0:
				constraints.append([-var_flipable(*I),+var_count(I,1)])
			else:
				constraints.append([-var_flipable(*I)])

		prevI = I


if args.assumptions:
	print ("(*) Levi: the even and odd indices form fliples")
	assert(n == 2*rank)
	constraints.append([+var_flipable(*even)]) 	
	constraints.append([+var_flipable(*odd )])


if args.assumptions:
	print ("(*) Levi: 1 -- (rank-1) assignments")
	for A in combinations(even,1):
		for B in combinations(odd,rank-1):
			I = tuple(sorted(A+B))
			iA0 = I.index(A[0])
			sign = +(-1)**iA0
			constraints.append([+var_sign(*I)*sign])

	for A in combinations(even,rank-1):
		for B in combinations(odd,1):
			I = tuple(sorted(A+B))
			iB0 = I.index(B[0])
			sign = -(-1)**iB0
			constraints.append([+var_sign(*I)*sign])


if args.assumptions and rank >= 4:
	# this is implied by the other conditions above
	print ("(*) Levi: 2 -- (rank-2) assignments")
	for A in combinations(even,2):
		for B in combinations(odd,rank-2):
			I = tuple(sorted(A+B))
			iA0 = I.index(A[0])
			iA1 = I.index(A[1])
			if (iA0 + iA1)%2 == 0: 
				sign = +(-1)**iA0
				constraints.append([+var_sign(*I)*sign])

	for A in combinations(even,rank-2):
		for B in combinations(odd,2):
			I = tuple(sorted(A+B))
			iB0 = I.index(B[0])
			iB1 = I.index(B[1])
			if (iB0 + iB1)%2 == 0: 
				sign = -(-1)**iB0
				constraints.append([+var_sign(*I)*sign])


if args.assumptions:
	print ("(*) assumption: fliples are either all odd, all even, or half-half")
	for I in combinations(N,rank):
		if len(set(I) & set(even)) not in {0,rank//2,rank}:
			constraints.append([-var_flipable(*I)])


if args.assumptions and rank >= 6:
	print ("(*) assumption for rank >= 6")
	O = odd[:rank//2]
	assert(min(O) == 1)
	max_o = max(O)
	J = [0]+O+[max_o+1,max_o+3]
	print ("J",J,[I for I in combinations(N,rank) if not set(J)-set(I)])
	constraints.append([+var_flipable(*I) for I in combinations(N,rank) if not set(J)-set(I)])


if args.assumptions and rank == 4:
	print ("(*) wlog even and odd map to plus")
	constraints.append([+var_sign(*odd)])
	constraints.append([+var_sign(*even)])


if args.assumptions:
	print ("(**) flipples have symmetry!")
	for I in combinations(N,rank):
		J = tuple(sorted([(i+4)%n for i in I]))
		constraints.append([-var_flipable(*I),+var_flipable(*J)])
		constraints.append([+var_flipable(*I),-var_flipable(*J)])


if args.loadsignotope:
	fp = args.loadsignotope
	print ("(****) fix and test solution from file:",fp)
	line = open(fp).readline()
	X_str = line.split()[1] if ' ' in line else line
	X = string_to_signotope(line,N,rank)
	for I in combinations(N,rank):
		constraints.append([var_sign(*I)*X[I]])


if args.comparability:
	print ("(*) assert rotations")
	for k in range(2*n):
		for I in combinations(N,rank):
			I_rot = tuple(sorted([(i-k)%n for i in I]))
			q = (-1)**len([i for i in I if i<k and i>=k-n])
			for s in [+1,-1]:
				constraints.append([-s*var_sign(*I_rot),+s*q*var_sign_rot(k,I)])


	print ("(*) assert edges")
	for k in N:
		for u,v in combinations(VERTICES,2):
			I = tuple(sorted(set(u+v)))
			if len(set(I)) == rank:
				for s in [+1,-1]:
					constraints.append([-s*var_sign_rot(k,I),+s*var_edge(k,u,v)])
					constraints.append([-s*var_sign_rot(k,I),-s*var_edge(k,v,u)])
			else:
				constraints.append([-var_edge(k,u,v)])
				constraints.append([-var_edge(k,v,u)])


	print ("(*) assert reachable variables / BFS")
	for k in N:
		for u in VERTICES:
			constraints.append([+var_reachable(k,u,u,0)])
			for v in VERTICES:
				if u != v:
					constraints.append([-var_reachable(k,u,v,0)])


		for t in range(1,len(N)):
			for u in VERTICES:
				for v in VERTICES:
					constraints.append([-var_reachable(k,u,v,t)]+[+var_reachable_via(k,u,v,w,t) for w in VERTICES])
					for w in VERTICES: constraints.append([+var_reachable(k,u,v,t),-var_reachable_via(k,u,v,w,t)])

					constraints.append([-var_reachable(k,u,v,t-1),+var_reachable_via(k,u,v,v,t)])
					constraints.append([+var_reachable(k,u,v,t-1),-var_reachable_via(k,u,v,v,t)])

					for w in VERTICES:
						if w != v:
							constraints.append([-var_reachable(k,u,w,t-1),-var_edge(k,w,v),+var_reachable_via(k,u,v,w,t)])
							constraints.append([+var_reachable(k,u,w,t-1),-var_reachable_via(k,u,v,w,t)])
							constraints.append([+var_edge(k,w,v),-var_reachable_via(k,u,v,w,t)])


	if 1:
		print("(**) assume not 2-extendable")
		even = tuple(range(0,2*rank-2,2))
		odd  = tuple(range(1,2*rank-2,2))
		print("even,odd",even,odd)

		for k in N:
			constraints.append([+var_reachable(k,even,odd,n-1),+var_reachable(k,odd,even,n-1)])


print ("Total number of constraints:",len(constraints))

if args.instance2file:
	fp = args.instance2file
	print ("write instance to file",fp)
	
	f = open(fp,"w")
	f.write("p cnf "+str(_num_vars)+" "+str(len(constraints))+"\n")
	for c in constraints:
		f.write(" ".join(str(v) for v in c)+" 0\n")
	f.close()

	print ("Created CNF-file:",fp)
	
	
if not args.dontsolve:
	print ("start solving")
	ct = 0

	if args.solutions2file:
		print ("write solutions to file",args.solutions2file)
		outfile = open(args.solutions2file,"w")
	else:
		outfile = None

	if args.solver == "cadical":
		print ("use pysat/Cadical")
		try:
			from pysat.solvers import Cadical	
			solver = Cadical()
		except ImportError:
			from pysat.solvers import Cadical153	
			solver = Cadical153()
		for c in constraints: solver.add_clause(c)
		solution_iterator = solver.enum_models()
	else:
		print ("use pycosat")
		import pycosat
		solution_iterator = pycosat.itersolve(constraints)

	for sol in solution_iterator: 
		sol = set(sol) # set allows more efficient queries 
		ct += 1
		s = "".join("+" if var_sign(*I) in sol else "-" for I in combinations(N,rank))
		
		if not args.comparability:
			print ("#sol"+str(ct)+":",s)

		else:
			print ("#sol"+str(ct)+":",s)
			for k in N:		
				s_rot = "".join("+" if var_sign_rot(k,I) in sol else "-" for I in combinations(N,rank))
				incomp_rot = [(a,b) for a,b in combinations(VERTICES,2) if var_reachable(k,a,b,n-1) not in sol and var_reachable(k,b,a,n-1) not in sol]
				print("rot",k,s_rot,incomp_rot)
			print("")
		
		if outfile: outfile.write(s+"\n")

		X = string_to_signotope(s,N,rank)
		if not args.all: break

	if ct == 0: print ("no solutions")
	if outfile: print ("wrote solutions to file:",args.solutions2file)
	
